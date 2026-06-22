import Lollipop.Concrete.EndToEnd.PairGeometry
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Similarity transport

The local polynomial family is constructed around the standard unit
lollipop.  Positive plane similarities transport it to any base lollipop and
preserve carriers, component counts, finite crossings, transversality, and
regions.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace Lower

open Set

structure PlaneSimilarity where
  scale : ℝ
  scale_pos : 0 < scale
  orthogonal : Point ≃ₗᵢ[ℝ] Point
  translation : Point

namespace PlaneSimilarity

def toFun (S : PlaneSimilarity) (x : Point) : Point :=
  S.translation + S.scale • S.orthogonal x

def invFun (S : PlaneSimilarity) (y : Point) : Point :=
  S.orthogonal.symm (S.scale⁻¹ • (y - S.translation))

@[simp] theorem left_inv (S : PlaneSimilarity) (x : Point) :
    S.invFun (S.toFun x) = x := by
  simp [toFun, invFun, smul_smul, S.scale_pos.ne']

@[simp] theorem right_inv (S : PlaneSimilarity) (y : Point) :
    S.toFun (S.invFun y) = y := by
  simp [toFun, invFun, smul_smul, S.scale_pos.ne']

/-- Underlying homeomorphism. -/
def homeomorph (S : PlaneSimilarity) : Point ≃ₜ Point where
  toFun := S.toFun
  invFun := S.invFun
  left_inv := S.left_inv
  right_inv := S.right_inv
  continuous_toFun := by unfold toFun; fun_prop
  continuous_invFun := by unfold invFun; fun_prop

@[simp] theorem sub_toFun (S : PlaneSimilarity) (x y : Point) :
    S.toFun x - S.toFun y = S.scale • S.orthogonal (x - y) := by
  simp [toFun, map_sub]

@[simp] theorem dist_toFun (S : PlaneSimilarity) (x y : Point) :
    dist (S.toFun x) (S.toFun y) = S.scale * dist x y := by
  rw [dist_eq_norm, S.sub_toFun, norm_smul, Real.norm_eq_abs,
    abs_of_pos S.scale_pos, S.orthogonal.norm_map, ← dist_eq_norm]

/-- Image lollipop. -/
def mapLollipop (S : PlaneSimilarity) (L : Lollipop) : Lollipop where
  center := S.toFun L.center
  radial := S.scale • S.orthogonal L.radial
  radial_ne_zero :=
    smul_ne_zero S.scale_pos.ne' (S.orthogonal.injective.ne L.radial_ne_zero)

@[simp] theorem map_radius (S : PlaneSimilarity) (L : Lollipop) :
    (S.mapLollipop L).radius = S.scale * L.radius := by
  simp [mapLollipop, Lollipop.radius, norm_smul, Real.norm_eq_abs,
    abs_of_pos S.scale_pos]

@[simp] theorem map_anchor (S : PlaneSimilarity) (L : Lollipop) :
    (S.mapLollipop L).anchor = S.toFun L.anchor := by
  simp [mapLollipop, Lollipop.anchor, toFun, map_add, add_assoc]

@[simp] theorem mem_map_circle_iff (S : PlaneSimilarity) (L : Lollipop)
    (x : Point) :
    S.toFun x ∈ (S.mapLollipop L).circle ↔ x ∈ L.circle := by
  simp [Lollipop.circle, S.dist_toFun, S.map_radius, S.scale_pos.ne']

@[simp] theorem mem_map_stem_iff (S : PlaneSimilarity) (L : Lollipop)
    (x : Point) :
    S.toFun x ∈ (S.mapLollipop L).stem ↔ x ∈ L.stem := by
  constructor
  · rintro ⟨t, ht, h⟩
    refine ⟨t, ht, ?_⟩
    apply S.homeomorph.injective
    simpa [mapLollipop, toFun, map_add, map_smul, smul_smul,
      add_assoc] using h.symm
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t, ht, ?_⟩
    simp [mapLollipop, toFun, map_add, map_smul, smul_smul, add_assoc]

@[simp] theorem mem_map_carrier_iff (S : PlaneSimilarity) (L : Lollipop)
    (x : Point) :
    S.toFun x ∈ (S.mapLollipop L).carrier ↔ x ∈ L.carrier := by
  simp [Lollipop.carrier]

/-- Carrier image identity. -/
theorem image_carrier (S : PlaneSimilarity) (L : Lollipop) :
    S.toFun '' L.carrier = (S.mapLollipop L).carrier := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (S.mem_map_carrier_iff L x).2 hx
  · intro hy
    refine ⟨S.invFun y, ?_, S.right_inv y⟩
    exact (S.mem_map_carrier_iff L (S.invFun y)).1 (by simpa using hy)

/-- Similarity invariance of finite pair crossing count. -/
theorem pairCrossingCount_map (S : PlaneSimilarity) (L M : Lollipop) :
    pairCrossingCount (S.mapLollipop L) (S.mapLollipop M) =
      pairCrossingCount L M := by
  unfold pairCrossingCount pairCrossingSet
  rw [← S.image_carrier L, ← S.image_carrier M,
    ← Set.image_inter S.homeomorph.injective]
  exact Set.ncard_image_of_injective S.homeomorph.injective

/-- Similarity invariance of robust pair excess. -/
theorem pairExcessNat_map (S : PlaneSimilarity) (L M : Lollipop) :
    pairExcessNat (S.mapLollipop L) (S.mapLollipop M) = pairExcessNat L M := by
  let hhat : Sphere2 ≃ₜ Sphere2 := OnePoint.mapHomeomorph S.homeomorph
  have hset : hhat '' hatPairIntersection L M =
      hatPairIntersection (S.mapLollipop L) (S.mapLollipop M) := by
    ext x
    cases x using OnePoint.rec with
    | infty => simp [hhat, hatPairIntersection]
    | coe p => simp [hhat, hatPairIntersection, S.mem_map_carrier_iff]
  unfold pairExcessNat componentCount
  exact congrArg (fun k : ℕ => k - 1)
    (Nat.card_congr (ConnectedComponents.equivOfHomeomorphOnImage hhat hset))

/-- Image arrangement. -/
def mapArrangement {n : ℕ} (S : PlaneSimilarity) (A : Arrangement n) :
    Arrangement n := fun i => S.mapLollipop (A i)

/-- Similarity preserves regions. -/
theorem regionCount_map {n : ℕ} (S : PlaneSimilarity) (A : Arrangement n) :
    regionCount (S.mapArrangement A) = regionCount A := by
  let e : FreeSpace A ≃ₜ FreeSpace (S.mapArrangement A) :=
    S.homeomorph.subtypeHomeomorph fun x => by
      simp [occupied, mapArrangement, S.image_carrier]
  unfold regionCount
  exact Nat.card_congr (ConnectedComponents.equivOfHomeomorph e).symm

end PlaneSimilarity

/-- Standard unit lollipop. -/
def standardLollipop : Lollipop where
  center := 0
  radial := fun i => if i = 0 then 1 else 0
  radial_ne_zero := by
    intro h
    have := congrFun h 0
    norm_num at this

/-- Rotation carrying the positive x-axis to a unit vector. -/
def rotationTo (u : Point) : Point →ₗ[ℝ] Point where
  toFun x := fun i =>
    if i = 0 then u 0 * x 0 - u 1 * x 1
    else u 1 * x 0 + u 0 * x 1
  map_add' := by intro x y; ext i; fin_cases i <;> simp <;> ring
  map_smul' := by intro a x; ext i; fin_cases i <;> simp <;> ring

/-- Unit-vector rotation as a linear isometry equivalence. -/
def rotationToIsometry (u : Point) (hu : ‖u‖ = 1) : Point ≃ₗᵢ[ℝ] Point := by
  exact LinearIsometryEquiv.rotationMatrix2 u hu

/-- Canonical positive similarity from the standard lollipop to `L`. -/
def similarityTo (L : Lollipop) : PlaneSimilarity where
  scale := L.radius
  scale_pos := L.radius_pos
  orthogonal := rotationToIsometry L.unitRadial L.norm_unitRadial
  translation := L.center

@[simp] theorem similarityTo_standard (L : Lollipop) :
    (similarityTo L).mapLollipop standardLollipop = L := by
  ext <;>
    simp [similarityTo, standardLollipop, rotationToIsometry,
      rotationTo, L.radial_eq_radius_smul_unitRadial]

end Lower
end EndToEnd
end Concrete
end Lollipop
