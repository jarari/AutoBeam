#include <Havok.h>
#include <MathUtils.h>
#include <Utilities.h>
#include <half.h>
#define max(a, b) (((a) > (b)) ? (a) : (b))
#define min(a, b) (((a) < (b)) ? (a) : (b))
using namespace RE;
using std::unordered_map;

const F4SE::TaskInterface* taskInterface;
PlayerCharacter* p;
PlayerCamera* pcam;
REL::Relocation<uintptr_t> ptr_PCUpdateMainThread{ REL::ID(633524), 0x22D };
uintptr_t PCUpdateMainThreadOrig;

const static float gunAimDiffThreshold1st = 0.209f;
const static float gunAimDiffThreshold3rd = 0.523f;

bhkNPCollisionObject* GetPickData(const NiPoint3& start, const NiPoint3& end, Actor* a, BGSProjectile* projForm, F4::bhkPickData& pick)
{
	if (!a->parentCell)
		return nullptr;
	bhkWorld* world = a->parentCell->GetbhkWorld();
	if (!world)
		return nullptr;
	hknpBSWorld* hkWorld = *(hknpBSWorld**)((uintptr_t)world + 0x60);
	if (!hkWorld)
		return nullptr;

	bhkNPCollisionObject* ret;
	pick.SetStartEnd(start, end);
	/*hknpAllHitsCollector collector = hknpAllHitsCollector();
	*(uintptr_t*)((uintptr_t)&pick + 0xD0) = (uintptr_t)&collector;
	*(uint32_t*)((uintptr_t)&pick + 0xD8) = 3;*/
	hknpClosestHitCollector collector = hknpClosestHitCollector();
	*(uintptr_t*)((uintptr_t)&pick + 0xD0) = (uintptr_t)&collector;
	if (projForm->data.collisionLayer) {
		uint32_t index = projForm->data.collisionLayer->collisionIdx;
		uint64_t filter = *(uint64_t*)((*REL::Relocation<uint64_t*>{ REL::ID(469495) }) + 0x1A0 + 0x8 * index) | 0x40000000;
		uint64_t flag = 0x1C15160;
		if (!((BGSProjectileEx*)projForm)->CollidesWithSmallTransparentLayer())
			flag = 0x15C15160;
		*(uint64_t*)((uintptr_t)&pick + 0xC8) = filter & ~flag;
	}
	*(uint32_t*)((uintptr_t)&pick + 0x0C) = ((((ActorEx*)a)->GetCurrentCollisionGroup() << 16) | 0x1);
	hkWorld->MarkForRead();
	ret = F4::CombatUtilities::CalculateProjectileLOS(a, projForm, pick);
	hkWorld->UnmarkForRead();
	return ret;
}

float CalculateLaserLength(NiAVObject* tri)
{
	float laserLen = 759.f;
	using namespace F4::BSGraphics;
	TriShape* triShape = *(TriShape**)((uintptr_t)tri + 0x148);
	VertexDesc* vertexDesc = (VertexDesc*)((uintptr_t)tri + 0x150);
	int16_t vertexCount = *(int16_t*)((uintptr_t)tri + 0x164);
	uint32_t vertexSize = vertexDesc->GetSize();
	uint32_t posOffset = vertexDesc->GetAttributeOffset(Vertex::VA_POSITION);
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
	NiAVObject* scanned = root->GetObjectByName("_Scanned");
	if (scanned)
		return false;

	bool marked = false;
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
				obj->name = "_Scanned";
			}
		}
		return false;
	});
	if (!marked) {
		marked = true;
		NiNode* node = CreateBone("_Scanned");
		markingParent->AttachChild(node, true);
		node->local.translate = NiPoint3();
		node->local.rotate.MakeIdentity();
	}

	return found;
}

void AdjustLaserSight(Actor* a, NiNode* root, const NiPoint3& gunDir, const NiPoint3& laserPos, const NiPoint3& laserNormal, const NiPoint3& fpOffset)
{
	if (root) {
		float actorScale = GetActorScale(a);
		InterlockedIncrement((volatile long*)((uintptr_t)a->Get3D() + 0x138));
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
					NiPoint3 targetDir = Normalize(laserPos - (laserBeam->parent->world.translate + fpOffset));
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
					NiPoint3 a = NiPoint3(0, 0, 1);
					NiPoint3 axis = Normalize(CrossProduct(a, laserNormal));
					float ang = acos(max(min(DotProduct(a, laserNormal), 1.f), -1.f));
					laserDot->local.rotate = GetRotationMatrix33(axis, -ang) * Inverse(laserDot->parent->world.rotate);
					laserDot->local.translate = laserDot->parent->world.rotate * diff;
					//_MESSAGE("dot axis %f %f %f", axis.x, axis.y, axis.z);
					//_MESSAGE("dot ang %f", ang);
					NiUpdateData ud;
					laserDot->UpdateTransforms(ud);
				}
			}
			return false;
		});
		InterlockedDecrement((volatile long*)((uintptr_t)a->Get3D() + 0x138));
	}
}

bool ShouldNotAdjustLaser(Actor* a, float gunAimDiff, float gunAimDiffThreshold)
{
	return ((!F4::AnimationSystemUtils::WillEventChangeState(*a, "attackStart") && !F4::AnimationSystemUtils::WillEventChangeState(*a, "reloadStart")) || a->DoGetSprinting() || (a->gunState >= 1 && a->gunState <= 4) || gunAimDiff > gunAimDiffThreshold);
}

void AdjustPlayerBeam()
{
	if (pcam->currentState == pcam->cameraStates[CameraState::k3rdPerson] || pcam->currentState == pcam->cameraStates[CameraState::kFirstPerson] || pcam->currentState == pcam->cameraStates[CameraState::kFree]) {
		if (p->Get3D() && p->currentProcess && p->currentProcess->middleHigh) {
			BSTArray<EquippedItem> equipped = p->currentProcess->middleHigh->equippedItems;
			if (equipped.size() != 0 && equipped[0].item.instanceData) {
				TESObjectWEAP::InstanceData* instance = (TESObjectWEAP::InstanceData*)equipped[0].item.instanceData.get();
				if (instance->type == 9 && instance->ammo && p->weaponState != WEAPON_STATE::kSheathed) {
					BGSProjectile* projForm = instance->ammo->data.projectile;
					if (instance->rangedData->overrideProjectile) {
						projForm = instance->rangedData->overrideProjectile;
					}
					if (projForm) {
						NiNode* weapon = (NiNode*)p->Get3D()->GetObjectByName("Weapon");
						if (!p->Get3D()->GetObjectByName("_LaserDot") && !p->Get3D()->GetObjectByName("_LaserBeam")) {
							if (weapon) {
								bool suspectedSightFound = TryFindingLaserSight(weapon);
								if (!suspectedSightFound)
									return;
							}
							return;
						}

						bool firstPerson = p->Get3D(true) == p->Get3D();
						NiPoint3 fpOffset;
						NiNode* projNode = (NiNode*)p->Get3D()->GetObjectByName("ProjectileNode");
						if (!projNode) {
							projNode = weapon;
						}
						NiPoint3 newPos = projNode->world.translate;
						NiPoint3 dir = Normalize(p->bulletAutoAim - newPos);
						NiPoint3 gunDir = Normalize(ToUpVector(projNode->world.rotate));
						NiPoint3 camDir = Normalize(ToUpVector(pcam->cameraRoot->world.rotate));
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

						float camFovThreshold = 0.85f;
						float gunAimDiff = acos(DotProduct(camDir, gunDir));
						if (ShouldNotAdjustLaser(p, gunAimDiff, gunAimDiffThreshold)) {
							dir = gunDir;
						}

						F4::bhkPickData pick = F4::bhkPickData();
						bhkNPCollisionObject* nodeHit = GetPickData(newPos, newPos + dir * 10000.f, p, projForm, pick);
						NiPoint3 laserNormal = dir * -1.f;
						NiPoint3 laserPos;
						if (pick.HasHit()) {
							/*hknpCollisionResult res;
							pick.GetAllCollectorRayHitAt(0, res);
							laserNormal = Normalize(res.normal);
							laserPos = res.position / *ptr_fBS2HkScale + laserNormal * 2.f;*/
							laserNormal = NiPoint3(*(float*)((uintptr_t)&pick + 0x70), *(float*)((uintptr_t)&pick + 0x74), *(float*)((uintptr_t)&pick + 0x78));
							laserPos = NiPoint3(*(float*)((uintptr_t)&pick + 0x60), *(float*)((uintptr_t)&pick + 0x64), *(float*)((uintptr_t)&pick + 0x68)) / *ptr_fBS2HkScale + laserNormal * 2.f;
						} else {
							laserPos = newPos + dir * 10000.f + laserNormal * 2.f;
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
		BSTArray<EquippedItem> equipped = a->currentProcess->middleHigh->equippedItems;
		if (equipped.size() != 0 && equipped[0].item.instanceData) {
			TESObjectWEAP::InstanceData* instance = (TESObjectWEAP::InstanceData*)equipped[0].item.instanceData.get();
			if (instance->type == 9 && instance->ammo && a->weaponState != WEAPON_STATE::kSheathed) {
				BGSProjectile* projForm = instance->ammo->data.projectile;
				if (instance->rangedData->overrideProjectile) {
					projForm = instance->rangedData->overrideProjectile;
				}
				if (projForm) {
					NiNode* weapon = (NiNode*)a->Get3D()->GetObjectByName("Weapon");
					if (!a->Get3D()->GetObjectByName("_LaserDot") && !a->Get3D()->GetObjectByName("_LaserBeam")) {
						if (weapon) {
							bool suspectedSightFound = TryFindingLaserSight(weapon);
							if (!suspectedSightFound)
								return;
						}
						return;
					}

					NiNode* projNode = (NiNode*)a->Get3D()->GetObjectByName("ProjectileNode");
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

					F4::bhkPickData pick = F4::bhkPickData();
					bhkNPCollisionObject* nodeHit = GetPickData(newPos, newPos + dir * 10000.f, a, projForm, pick);
					NiPoint3 laserNormal = dir * -1.f;
					NiPoint3 laserPos;
					if (pick.HasHit()) {
						/*hknpCollisionResult res;
						pick.GetAllCollectorRayHitAt(0, res);
						NiPoint3 laserNormal = res.normal;
						NiPoint3 laserPos = res.position / *ptr_fBS2HkScale + laserNormal * 2.f;*/
						laserNormal = NiPoint3(*(float*)((uintptr_t)&pick + 0x70), *(float*)((uintptr_t)&pick + 0x74), *(float*)((uintptr_t)&pick + 0x78));
						laserPos = NiPoint3(*(float*)((uintptr_t)&pick + 0x60), *(float*)((uintptr_t)&pick + 0x64), *(float*)((uintptr_t)&pick + 0x68)) / *ptr_fBS2HkScale + laserNormal * 2.f;
					} else {
						laserPos = newPos + dir * 10000.f + laserNormal * 2.f;
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

	typedef void (*FnUpdate)();
	FnUpdate fn = (FnUpdate)PCUpdateMainThreadOrig;
	if (fn)
		(*fn)();
}

void InitializePlugin()
{
	p = PlayerCharacter::GetSingleton();
	pcam = PlayerCamera::GetSingleton();
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
		logger::critical("loaded in editor"sv);
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
