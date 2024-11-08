#include <Havok.h>
#include <MathUtils.h>
#include <SimpleIni.h>
#include <Utilities.h>
#include <half.h>
#define max(a, b) (((a) > (b)) ? (a) : (b))
#define min(a, b) (((a) < (b)) ? (a) : (b))
using namespace RE;
using std::unordered_map;

const F4SE::TaskInterface* taskInterface;
PlayerCharacter* p;
PlayerCamera* pcam;
bhkPickData* pick;
REL::Relocation<uintptr_t> ptr_PCUpdateMainThread{ REL::ID(633524), 0x22D };
static CSimpleIniA ini(true, false, false);
static uintptr_t PCUpdateMainThreadOrig;
static uintptr_t AttachWeaponOrig;
static uintptr_t WeaponeDrawOrig;
static uintptr_t WeaponeSheatheOrig;
static std::deque<NiPoint3> sampledGunDirOffset;
static float lastRun;
static bool wasFP = false;
static bool wasSighted = false;

static float gunAimDiffThreshold1st = 0.209f;
static float gunAimDiffThreshold3rd = 0.75f;
static float laserMaxDistance = 1000.f;
static size_t sampleCount = 15;

float CalculateLaserLength(NiAVObject* tri)
{
	float laserLen = 759.f;
	BSGraphics::TriShape* triShape = *(BSGraphics::TriShape**)((uintptr_t)tri + 0x148);
	BSGraphics::VertexDesc* vertexDesc = (BSGraphics::VertexDesc*)((uintptr_t)tri + 0x150);
	int16_t vertexCount = *(int16_t*)((uintptr_t)tri + 0x164);
	uint32_t vertexSize = vertexDesc->GetSize();
	uint32_t posOffset = vertexDesc->GetAttributeOffset(BSGraphics::Vertex::VA_POSITION);
	float ymin = std::numeric_limits<float>::infinity();
	float ymax = -ymin;
	if (triShape && triShape->buffer08) {
		for (int v = 0; v < vertexCount; ++v) {
			uintptr_t posPtr = (uintptr_t)triShape->buffer08->rawVertexData + v * vertexSize + posOffset;
			NiPoint3 pos{ half_float::half_cast<float>(*(half_float::half*)(posPtr)), half_float::half_cast<float>(*(half_float::half*)(posPtr + 0x2)), half_float::half_cast<float>(*(half_float::half*)(posPtr + 0x4)) };
			ymin = min(ymin, pos.y);
			ymax = max(ymax, pos.y);
		}
		laserLen = ymax - ymin;
	}
	return laserLen;
}

bool TryFindingLaserSight(NiAVObject* root)
{
	bool found = false;
	/*NiAVObject* scanned = root->GetObjectByName("_Scanned");
	if (scanned)
		return false;*/

	bool marked = false;
	InterlockedIncrement((volatile long*)((uintptr_t)root + 0x138));
	NiNode* markingParent = root->IsNode();
	Visit(root, [&marked, &markingParent](NiAVObject* obj) {
		if ((obj->flags.flags & 0x1) == 0x1)
			return false;

		if (!markingParent && obj->IsNode()) {
			markingParent = obj->IsNode();
			return false;
		}

		if (!obj->IsTriShape())
			return false;

		int16_t vertexCount = *(int16_t*)((uintptr_t)obj + 0x164);
		BSShaderProperty* shaderProperty = *(BSShaderProperty**)((uintptr_t)obj + 0x138);
		if (vertexCount < 100 && shaderProperty && *(uintptr_t*)shaderProperty == REL::Relocation<uintptr_t>{ VTABLE::BSEffectShaderProperty[0] }.address() && obj->parent && *(uintptr_t*)obj->parent == REL::Relocation<uintptr_t>{ VTABLE::NiBillboardNode[0] }.address()) {
			std::string name{ obj->name.c_str() };
			for (auto& c : name) {
				c = tolower(c);
			}
			if (vertexCount > 40 && name.find("beam") != std::string::npos) {
				obj->name = "_LaserBeam";
			} else if (name.find("dot") != std::string::npos) {
				obj->name = "_LaserDot";
			} else {
				marked = true;
				//obj->name = "_Scanned";
			}
		}
		return false;
	});
	/*if (!marked) {
		marked = true;
		NiNode* node = CreateBone("_Scanned");
		markingParent->AttachChild(node, true);
		node->local.translate = NiPoint3();
		node->local.rotate.MakeIdentity();
	}*/
	InterlockedDecrement((volatile long*)((uintptr_t)root + 0x138));

	return found;
}

void AdjustLaserSight(Actor* a, NiNode* root, const NiPoint3& gunDir, const NiPoint3& laserPos, const NiPoint3& laserNormal, const NiPoint3& fpOffset)
{
	if (root) {
		float actorScale = GetActorScale(a);
		InterlockedIncrement((volatile long*)((uintptr_t)root + 0x138));
		Visit(root, [&](NiAVObject* obj) {
			if (obj->refCount == 0 || (obj->flags.flags & 0x1) == 0x1 || !obj->IsTriShape())
				return false;
			NiAVObject* laserBeam = nullptr;
			NiAVObject* laserDot = nullptr;
			if (obj->name == "_LaserBeam")
				laserBeam = obj;
			else if (obj->name == "_LaserDot")
				laserDot = obj;
			if (laserBeam) {
				if (laserBeam->parent) {
					NiPoint3 diff = laserPos - (laserBeam->parent->world.translate + fpOffset);
					diff = diff / actorScale;
					float dist = Length(diff);
					float laserLen = CalculateLaserLength(laserBeam);
					NiMatrix3 scale = GetScaleMatrix(1, dist / laserLen, 1);
					NiPoint3 targetDir = Normalize(diff);
					NiPoint3 axis = Normalize(laserBeam->parent->world.rotate * CrossProduct(targetDir, gunDir));
					float ang = acos(max(min(DotProduct(targetDir, gunDir), 1.f), -1.f));
					//_MESSAGE("beam axis %f %f %f", axis.x, axis.y, axis.z);
					//_MESSAGE("beam ang %f", ang);
					laserBeam->local.rotate = scale * GetRotationMatrix33(axis, ang);
					NiUpdateData ud;
					laserBeam->UpdateTransforms(ud);
				}
			}
			if (laserDot) {
				if (laserDot->parent) {
					NiPoint3 diff = laserPos - (laserDot->parent->world.translate + fpOffset);
					diff = diff / actorScale;
					NiPoint3 up = NiPoint3(0, 0, 1);
					NiPoint3 diffNorm = Normalize(diff);
					NiPoint3 rotAxis = Normalize(CrossProduct(up, laserNormal));
					float ang = acos(max(min(DotProduct(up, laserNormal), 1.f), -1.f));
					NiMatrix3 worldRot = GetRotationMatrix33(rotAxis, -ang);
					NiPoint3 worldRight = ToRightVector(worldRot);
					NiPoint3 gunRight = ToRightVector(laserDot->parent->world.rotate);
					NiPoint3 projGunRight = Normalize(gunRight - laserNormal * DotProduct(gunRight, laserNormal));
					float yawAng = acos(max(min(DotProduct(worldRight, projGunRight), 1.f), -1.f));
					if (DotProduct(ToUpVector(worldRot), gunRight) > 0) {
						yawAng *= -1.f;
					}
					laserDot->local.rotate = GetRotationMatrix33(rotAxis, -ang) * GetRotationMatrix33(laserNormal, yawAng) * Transpose(laserDot->parent->world.rotate);
					laserDot->local.translate = laserDot->parent->world.rotate * diff;
					NiUpdateData ud;
					laserDot->UpdateTransforms(ud);
				}
			}
			return false;
		});
		InterlockedDecrement((volatile long*)((uintptr_t)root + 0x138));
	}
}

bool ShouldNotAdjustLaser(Actor* a, float gunAimDiff, float gunAimDiffThreshold)
{
	return ((!AnimationSystemUtils::WillEventChangeState(*a, "attackStart") && !AnimationSystemUtils::WillEventChangeState(*a, "reloadStart")) || a->DoGetSprinting() || ((uint32_t)a->gunState >= 1 && (uint32_t)a->gunState <= 4) || gunAimDiff > gunAimDiffThreshold);
}

void AdjustPlayerBeam()
{
	if (pcam->currentState == pcam->cameraStates[CameraState::k3rdPerson] || pcam->currentState == pcam->cameraStates[CameraState::kFirstPerson] || pcam->currentState == pcam->cameraStates[CameraState::kFree]) {
		if (p->Get3D() && p->currentProcess && p->currentProcess->middleHigh) {
			BSTArray<EquippedItem>& equipped = p->currentProcess->middleHigh->equippedItems;
			if (equipped.size() != 0 && equipped[0].item.instanceData) {
				TESObjectWEAP::InstanceData* instance = (TESObjectWEAP::InstanceData*)equipped[0].item.instanceData.get();
				if (instance->type == WEAPON_TYPE::kGun && instance->ammo && p->weaponState != WEAPON_STATE::kSheathed) {
					BGSProjectile* projForm = instance->ammo->data.projectile;
					if (instance->rangedData->overrideProjectile) {
						projForm = instance->rangedData->overrideProjectile;
					}
					if (projForm) {
						NiNode* weapon = (NiNode*)p->Get3D()->GetObjectByName("Weapon");
						if (!weapon || (!weapon->GetObjectByName("_LaserBeam") && !weapon->GetObjectByName("_LaserDot"))) {
							return;
						}
						NiNode* projNode = (NiNode*)weapon->GetObjectByName("ProjectileNode");
						if (!projNode) {
							projNode = weapon;
						}
						bool firstPerson = p->Get3D(true) == p->Get3D();
						NiPoint3 fpOffset;
						NiPoint3 gunDir = Normalize(ToUpVector(projNode->world.rotate));
						NiPoint3 camDir = Normalize(ToUpVector(pcam->cameraRoot->world.rotate));
						NiPoint3 newPos = projNode->world.translate - gunDir * 25.f;
						NiPoint3 dir = Normalize(p->bulletAutoAim - newPos);
						float gunAimDiffThreshold = gunAimDiffThreshold3rd;
						if (firstPerson) {
							NiNode* camera = (NiNode*)p->Get3D()->GetObjectByName("Camera");
							fpOffset = pcam->cameraRoot->world.translate - *F4::ptr_k1stPersonCameraLocation;
							dir = camDir;
							newPos = pcam->cameraRoot->world.translate + dir * 25.f;
							gunAimDiffThreshold = gunAimDiffThreshold1st;
						} else if (pcam->currentState == pcam->cameraStates[CameraState::kFree]) {
							dir = gunDir;
							camDir = gunDir;
						}
						if (!wasFP && firstPerson) {
							sampledGunDirOffset.clear();
							wasFP = true;
						} else if (wasFP && !firstPerson) {
							sampledGunDirOffset.clear();
							wasFP = false;
						}

						if (!wasSighted && GetIsSighted(p)) {
							sampledGunDirOffset.clear();
							wasSighted = true;
						} else if (wasSighted && !GetIsSighted(p)) {
							sampledGunDirOffset.clear();
							wasSighted = false;
						}

						float camFovThreshold = 0.85f;
						float gunAimDiff = acos(DotProduct(camDir, gunDir));
						if (ShouldNotAdjustLaser(p, gunAimDiff, gunAimDiffThreshold)) {
							dir = gunDir;
							newPos = projNode->world.translate + fpOffset - gunDir * 25.f;
						} else {
							sampledGunDirOffset.push_back(dir - gunDir);
							if (sampledGunDirOffset.size() > sampleCount) {
								sampledGunDirOffset.pop_front();
							}

							NiPoint3 avgOffset;
							for (auto it = sampledGunDirOffset.begin(); it != sampledGunDirOffset.end(); ++it) {
								avgOffset = avgOffset + *it;
							}
							avgOffset = avgOffset / sampledGunDirOffset.size();

							dir = gunDir + avgOffset;
						}

						NiPoint3 laserNormal = dir * -1.f;
						NiPoint3 laserPos = NiPoint3();
						GetPickDataCELL(newPos, newPos + dir * laserMaxDistance, p, *pick);
						if (pick->HasHit()) {
							laserNormal = NiPoint3(*(float*)((uintptr_t)pick + 0x70), *(float*)((uintptr_t)pick + 0x74), *(float*)((uintptr_t)pick + 0x78));
							laserPos = NiPoint3(*(float*)((uintptr_t)pick + 0x60), *(float*)((uintptr_t)pick + 0x64), *(float*)((uintptr_t)pick + 0x68)) / *ptr_fBS2HkScale + laserNormal * 2.f;
						} else {
							laserPos = newPos + dir * laserMaxDistance + laserNormal * 2.f;
						}
						//_MESSAGE("autoaim %f %f %f", p->bulletAutoAim.x, p->bulletAutoAim.y, p->bulletAutoAim.z);
						//_MESSAGE("laserPos %f %f %f", laserPos.x, laserPos.y, laserPos.z);
						//_MESSAGE("laserNormal %f %f %f", laserNormal.x, laserNormal.y, laserNormal.z);
						AdjustLaserSight(p, weapon, gunDir, laserPos, laserNormal, fpOffset);
					}
				}
			}
		}
	}
}

void AdjustNPCBeam(Actor* a)
{
	if (a->currentProcess && a->currentProcess->middleHigh) {
		BSTArray<EquippedItem>& equipped = a->currentProcess->middleHigh->equippedItems;
		if (equipped.size() != 0 && equipped[0].item.instanceData) {
			TESObjectWEAP::InstanceData* instance = (TESObjectWEAP::InstanceData*)equipped[0].item.instanceData.get();
			if (instance->type == WEAPON_TYPE::kGun && instance->ammo && a->weaponState != WEAPON_STATE::kSheathed) {
				BGSProjectile* projForm = instance->ammo->data.projectile;
				if (instance->rangedData->overrideProjectile) {
					projForm = instance->rangedData->overrideProjectile;
				}
				if (projForm) {
					NiNode* weapon = (NiNode*)a->Get3D()->GetObjectByName("Weapon");
					if (!weapon || (!weapon->GetObjectByName("_LaserBeam") && !weapon->GetObjectByName("_LaserDot"))) {
						return;
					}
					NiNode* projNode = (NiNode*)weapon->GetObjectByName("ProjectileNode");
					if (!projNode) {
						projNode = weapon;
					}
					NiPoint3 newPos = projNode->world.translate;
					NiPoint3 dir;
					((ActorEx*)a)->GetAimVector(dir);
					NiPoint3 gunDir = Normalize(ToUpVector(projNode->world.rotate));
					float gunAimDiffThreshold = gunAimDiffThreshold3rd;

					float gunAimDiff = acos(DotProduct(dir, gunDir));
					if (ShouldNotAdjustLaser(a, gunAimDiff, gunAimDiffThreshold)) {
						dir = gunDir;
					}

					NiPoint3 laserNormal = dir * -1.f;
					NiPoint3 laserPos = NiPoint3();
					GetPickDataCELL(newPos, newPos + dir * laserMaxDistance, a, *pick);
					if (pick->HasHit()) {
						laserNormal = NiPoint3(*(float*)((uintptr_t)pick + 0x70), *(float*)((uintptr_t)pick + 0x74), *(float*)((uintptr_t)pick + 0x78));
						laserPos = NiPoint3(*(float*)((uintptr_t)pick + 0x60), *(float*)((uintptr_t)pick + 0x64), *(float*)((uintptr_t)pick + 0x68)) / *ptr_fBS2HkScale + laserNormal * 2.f;
					} else {
						laserPos = newPos + dir * laserMaxDistance + laserNormal * 2.f;
					}
					AdjustLaserSight(a, weapon, gunDir, laserPos, laserNormal, NiPoint3());
				}
			}
		}
	}
}

void HookedUpdate()
{
	BSTArray<ActorHandle>* highActorHandles = (BSTArray<ActorHandle>*)(F4::ptr_processLists.address() + 0x40);
	if (highActorHandles->size() > 0) {
		for (auto it = highActorHandles->begin(); it != highActorHandles->end(); ++it) {
			Actor* a = it->get().get();
			if (a && a->Get3D()) {
				if (a != p)
					AdjustNPCBeam(a);
			}
		}
	}
	AdjustPlayerBeam();
	lastRun = *F4::ptr_engineTime;
	typedef void (*FnUpdate)();
	FnUpdate fn = (FnUpdate)PCUpdateMainThreadOrig;
	if (fn)
		(*fn)();
}

void HookedAttachWeapon(Actor* a, const BGSObjectInstanceT<TESObjectWEAP>& instance, BGSEquipIndex idx)
{
	using func_t = decltype(&HookedAttachWeapon);
	((func_t)AttachWeaponOrig)(a, instance, idx);

	NiAVObject* root = a->Get3D(false);
	if (root) {
		TryFindingLaserSight(root);
		if (a == p) {
			TryFindingLaserSight(a->Get3D(true));
			sampledGunDirOffset.clear();
		}
	}
}

bool HookedWeaponDraw(void* handler, Actor* a, BSFixedString* str)
{
	using func_t = decltype(&HookedWeaponDraw);
	bool ret = ((func_t)WeaponeDrawOrig)(handler, a, str);

	NiAVObject* root = a->Get3D(false);
	if (root) {
		TryFindingLaserSight(root);
		if (a == p) {
			TryFindingLaserSight(a->Get3D(true));
			sampledGunDirOffset.clear();
		}
	}
	return ret;
}

bool HookedWeaponSheathe(void* handler, Actor* a, BSFixedString* str)
{
	NiAVObject* root = a->Get3D();
	if (root) {
		InterlockedIncrement((volatile long*)((uintptr_t)root + 0x138));
		Visit(root, [](NiAVObject* obj) {
			if (obj->refCount == 0 || (obj->flags.flags & 0x1) == 0x1 || !obj->IsTriShape() || obj->name.length() == 0)
				return false;
			NiAVObject* laserBeam = nullptr;
			NiAVObject* laserDot = nullptr;
			if (obj->name == "_LaserBeam")
				laserBeam = obj;
			else if (obj->name == "_LaserDot")
				laserDot = obj;
			if (laserBeam) {
				laserBeam->local.rotate.MakeIdentity();
			}
			if (laserDot) {
				laserDot->local.rotate = GetRotationMatrix33(1.57079633f, 0, 0);
				laserDot->local.translate = NiPoint3(0, 1000, 6);
			}
			return false;
		});
		InterlockedDecrement((volatile long*)((uintptr_t)root + 0x138));
	}
	using func_t = decltype(&HookedWeaponSheathe);
	return ((func_t)WeaponeSheatheOrig)(handler, a, str);
}

void LoadConfigs()
{
	std::string path = "Data\\MCM\\Config\\AutoBeam\\settings.ini";
	if (std::filesystem::exists("Data\\MCM\\Settings\\AutoBeam.ini")) {
		path = "Data\\MCM\\Settings\\AutoBeam.ini";
	}
	_MESSAGE("Loading config from %s", path.c_str());
	SI_Error result = ini.LoadFile(path.c_str());
	if (result >= 0) {
		gunAimDiffThreshold1st = std::stof(ini.GetValue("Main", "fGunAimDiffThreshold1st", "12.0")) * toRad;
		gunAimDiffThreshold3rd = std::stof(ini.GetValue("Main", "fGunAimDiffThreshold3rd", "47.0")) * toRad;
		laserMaxDistance = std::stof(ini.GetValue("Main", "fLaserMaxDistance", "2000.0"));
		sampleCount = std::stoi(ini.GetValue("Main", "iSampleCount", "15"));
	} else {
		_MESSAGE("Failed to load config.");
	}
}

class MenuWatcher : public BSTEventSink<MenuOpenCloseEvent>
{
	virtual BSEventNotifyControl ProcessEvent(const MenuOpenCloseEvent& evn, BSTEventSource<MenuOpenCloseEvent>* src) override
	{
		if (!evn.opening) {
			//_MESSAGE("Menu %s closing", evn.menuName.c_str());
			if (evn.menuName == BSFixedString("PauseMenu") || evn.menuName == BSFixedString("LoadingMenu")) {
				LoadConfigs();
			}
		}
		return BSEventNotifyControl::kContinue;
	}
};

void InitializePlugin()
{
	p = PlayerCharacter::GetSingleton();
	pcam = PlayerCamera::GetSingleton();
	pick = new bhkPickData();
	REL::Relocation<uintptr_t> actorVtbl{ VTABLE::Actor[0] };
	AttachWeaponOrig = actorVtbl.write_vfunc(0xA5, &HookedAttachWeapon);
	REL::Relocation<uintptr_t> PCVtbl{ VTABLE::PlayerCharacter[0] };
	PCVtbl.write_vfunc(0xA5, &HookedAttachWeapon);

	REL::Relocation<uintptr_t> drawVtbl{ VTABLE::WeaponDrawHandler[0] };
	WeaponeDrawOrig = drawVtbl.write_vfunc(0x1, &HookedWeaponDraw);

	REL::Relocation<uintptr_t> sheatheVtbl{ VTABLE::WeaponSheatheHandler[0] };
	WeaponeSheatheOrig = sheatheVtbl.write_vfunc(0x1, &HookedWeaponSheathe);

	MenuWatcher* mw = new MenuWatcher();
	UI::GetSingleton()->GetEventSource<MenuOpenCloseEvent>()->RegisterSink(mw);
}

extern "C" DLLEXPORT bool F4SEAPI F4SEPlugin_Query(const F4SE::QueryInterface* a_f4se, F4SE::PluginInfo* a_info)
{
#ifndef NDEBUG
	auto sink = std::make_shared<spdlog::sinks::msvc_sink_mt>();
#else
	auto path = logger::log_directory();
	if (!path) {
		return false;
	}

	*path /= fmt::format(FMT_STRING("{}.log"), Version::PROJECT);
	auto sink = std::make_shared<spdlog::sinks::basic_file_sink_mt>(path->string(), true);
#endif

	auto log = std::make_shared<spdlog::logger>("global log"s, std::move(sink));

#ifndef NDEBUG
	log->set_level(spdlog::level::trace);
#else
	log->set_level(spdlog::level::info);
	log->flush_on(spdlog::level::warn);
#endif

	spdlog::set_default_logger(std::move(log));
	spdlog::set_pattern("%g(%#): [%^%l%$] %v"s);

	logger::info(FMT_STRING("{} v{}"), Version::PROJECT, Version::NAME);

	a_info->infoVersion = F4SE::PluginInfo::kVersion;
	a_info->name = Version::PROJECT.data();
	a_info->version = Version::MAJOR;

	if (a_f4se->IsEditor()) {
		logger::critical(FMT_STRING("loaded in editor"));
		return false;
	}

	const auto ver = a_f4se->RuntimeVersion();
	if (ver < F4SE::RUNTIME_1_10_162) {
		logger::critical(FMT_STRING("unsupported runtime v{}"), ver.string());
		return false;
	}

	F4SE::AllocTrampoline(8 * 8);

	return true;
}

extern "C" DLLEXPORT bool F4SEAPI F4SEPlugin_Load(const F4SE::LoadInterface* a_f4se)
{
	F4SE::Init(a_f4se);

	F4SE::Trampoline& trampoline = F4SE::GetTrampoline();
	PCUpdateMainThreadOrig = trampoline.write_call<5>(ptr_PCUpdateMainThread.address(), &HookedUpdate);

	taskInterface = F4SE::GetTaskInterface();
	const F4SE::MessagingInterface* message = F4SE::GetMessagingInterface();
	message->RegisterListener([](F4SE::MessagingInterface::Message* msg) -> void {
		if (msg->type == F4SE::MessagingInterface::kGameDataReady) {
			InitializePlugin();
		}
	});

	return true;
}
