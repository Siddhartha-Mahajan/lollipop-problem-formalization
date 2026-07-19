import old_lean_folder.Concrete.EndToEnd.Support
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

theorem point_norm_sq_eq (x : Point) :
    ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  norm_num [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

theorem point_coord_sq_eq_one_of_norm_eq_one
    {u : Point} (hu : ‖u‖ = 1) :
    u 0 ^ 2 + u 1 ^ 2 = 1 := by
  have hsq : ‖u‖ ^ 2 = 1 := by rw [hu]; norm_num
  rwa [point_norm_sq_eq] at hsq

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
  simp [toFun, map_sub, smul_sub]

@[simp] theorem dist_toFun (S : PlaneSimilarity) (x y : Point) :
    dist (S.toFun x) (S.toFun y) = S.scale * dist x y := by
  rw [dist_eq_norm, S.sub_toFun, norm_smul, Real.norm_eq_abs,
    abs_of_pos S.scale_pos, S.orthogonal.norm_map, ← dist_eq_norm]

/-- Image lollipop. -/
def mapLollipop (S : PlaneSimilarity) (L : Lollipop) : Lollipop where
  center := S.toFun L.center
  radial := S.scale • S.orthogonal L.radial
  radial_ne_zero := by
    have horth : S.orthogonal L.radial ≠ 0 := by
      intro h
      have h' : S.orthogonal L.radial = S.orthogonal 0 := by
        simpa using h
      exact L.radial_ne_zero (S.orthogonal.injective h')
    exact smul_ne_zero S.scale_pos.ne' horth

@[simp] theorem map_radius (S : PlaneSimilarity) (L : Lollipop) :
    (S.mapLollipop L).radius = S.scale * L.radius := by
  simp [mapLollipop, Lollipop.radius, norm_smul, Real.norm_eq_abs,
    abs_of_pos S.scale_pos]

@[simp] theorem map_unitRadial (S : PlaneSimilarity) (L : Lollipop) :
    (S.mapLollipop L).unitRadial = S.orthogonal L.unitRadial := by
  rw [Lollipop.unitRadial, map_radius, mapLollipop, Lollipop.unitRadial]
  have hscale' : L.radius⁻¹ * S.scale⁻¹ * S.scale = L.radius⁻¹ := by
    field_simp [S.scale_pos.ne']
  ext i
  simp [smul_smul, hscale', map_smul]

@[simp] theorem map_anchor (S : PlaneSimilarity) (L : Lollipop) :
    (S.mapLollipop L).anchor = S.toFun L.anchor := by
  simp [mapLollipop, Lollipop.anchor, toFun, map_add, add_assoc]

@[simp] theorem mem_map_circle_iff (S : PlaneSimilarity) (L : Lollipop)
    (x : Point) :
    S.toFun x ∈ (S.mapLollipop L).circle ↔ x ∈ L.circle := by
  unfold Lollipop.circle
  change ‖S.toFun x - S.toFun L.center‖ = (S.mapLollipop L).radius ↔
    ‖x - L.center‖ = L.radius
  rw [S.sub_toFun x L.center, S.map_radius]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos S.scale_pos,
    S.orthogonal.norm_map]
  simp [S.scale_pos.ne']

@[simp] theorem mem_map_stem_iff (S : PlaneSimilarity) (L : Lollipop)
    (x : Point) :
    S.toFun x ∈ (S.mapLollipop L).stem ↔ x ∈ L.stem := by
  constructor
  · rintro ⟨t, ht, h⟩
    refine ⟨t, ht, ?_⟩
    have h' : S.toFun x = S.toFun (L.center + t • L.radial) := by
      simpa [mapLollipop, toFun, map_add, map_smul, smul_smul,
        mul_comm, add_assoc] using h
    exact S.homeomorph.injective h'
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t, ht, ?_⟩
    simp [mapLollipop, toFun, map_add, map_smul, smul_smul,
      mul_comm, add_assoc]

@[simp] theorem mem_map_carrier_iff (S : PlaneSimilarity) (L : Lollipop)
    (x : Point) :
    S.toFun x ∈ (S.mapLollipop L).carrier ↔ x ∈ L.carrier := by
  constructor
  · intro hx
    rcases hx with hx | hx
    · exact Or.inl ((S.mem_map_circle_iff L x).1 hx)
    · exact Or.inr ((S.mem_map_stem_iff L x).1 hx)
  · intro hx
    rcases hx with hx | hx
    · exact Or.inl ((S.mem_map_circle_iff L x).2 hx)
    · exact Or.inr ((S.mem_map_stem_iff L x).2 hx)

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
  rw [← S.image_carrier L, ← S.image_carrier M]
  rw [← Set.image_inter (f := S.toFun) S.homeomorph.injective]
  exact Set.ncard_image_of_injective (L.carrier ∩ M.carrier)
    S.homeomorph.injective

/-- Compactified carriers are preserved by a plane similarity. -/
theorem image_hatCarrier (S : PlaneSimilarity) (L : Lollipop) :
    (Homeomorph.onePointCongr S.homeomorph) '' hatCarrier L =
      hatCarrier (S.mapLollipop L) := by
  let hhat : Sphere2 ≃ₜ Sphere2 := Homeomorph.onePointCongr S.homeomorph
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    cases x using OnePoint.rec with
    | infty =>
        exact infinity_mem_hatCarrier (S.mapLollipop L)
    | coe p =>
        have hp : p ∈ L.carrier := by
          simpa [finitePoint] using
            (finitePoint_mem_hatCarrier_iff L p).1 hx
        change finitePoint (S.homeomorph p) ∈ hatCarrier (S.mapLollipop L)
        simpa [hhat, finitePoint, homeomorph] using
          (finitePoint_mem_hatCarrier_iff (S.mapLollipop L) (S.toFun p)).2
            ((S.mem_map_carrier_iff L p).2 hp)
  · intro hy
    cases y using OnePoint.rec with
    | infty =>
        exact ⟨infinity, infinity_mem_hatCarrier L, by simp [infinity]⟩
    | coe p =>
        have hp : p ∈ (S.mapLollipop L).carrier := by
          simpa [finitePoint] using
            (finitePoint_mem_hatCarrier_iff (S.mapLollipop L) p).1 hy
        refine ⟨finitePoint (S.invFun p), ?_, ?_⟩
        · exact (finitePoint_mem_hatCarrier_iff L (S.invFun p)).2
            ((S.mem_map_carrier_iff L (S.invFun p)).1
              (by simpa [S.right_inv p] using hp))
        · change finitePoint (S.homeomorph (S.invFun p)) = finitePoint p
          simp [finitePoint, homeomorph, S.right_inv]

/-- Similarity invariance of robust pair excess. -/
theorem pairExcessNat_map (S : PlaneSimilarity) (L M : Lollipop) :
    pairExcessNat (S.mapLollipop L) (S.mapLollipop M) = pairExcessNat L M := by
  let hhat : Sphere2 ≃ₜ Sphere2 := Homeomorph.onePointCongr S.homeomorph
  have hset : hhat '' hatPairIntersection L M =
      hatPairIntersection (S.mapLollipop L) (S.mapLollipop M) := by
    rw [hatPairIntersection, hatPairIntersection,
      Set.image_inter (f := hhat) hhat.injective,
      image_hatCarrier S L, image_hatCarrier S M]
  let eSet : hatPairIntersection L M ≃ₜ
      hatPairIntersection (S.mapLollipop L) (S.mapLollipop M) :=
    (hhat.image (hatPairIntersection L M)).trans (Homeomorph.setCongr hset)
  unfold pairExcessNat componentCount
  exact congrArg (fun k : ℕ => k - 1)
    (Nat.card_congr (connectedComponentsEquivOfHomeomorph eSet).symm)

/-- Image arrangement. -/
def mapArrangement {n : ℕ} (S : PlaneSimilarity) (A : Arrangement n) :
    Arrangement n := fun i => S.mapLollipop (A i)

/-- Similarities carry the occupied set of an arrangement to the occupied set
of the image arrangement. -/
theorem image_occupied {n : ℕ} (S : PlaneSimilarity) (A : Arrangement n) :
    S.toFun '' occupied A = occupied (S.mapArrangement A) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases mem_occupied_iff.1 hx with ⟨i, hxi⟩
    exact mem_occupied_iff.2
      ⟨i, (S.mem_map_carrier_iff (A i) x).2 hxi⟩
  · intro hy
    rcases mem_occupied_iff.1 hy with ⟨i, hyi⟩
    refine ⟨S.invFun y, ?_, S.right_inv y⟩
    exact mem_occupied_iff.2
      ⟨i, (S.mem_map_carrier_iff (A i) (S.invFun y)).1
        (by simpa [mapArrangement, S.right_inv y] using hyi)⟩

/-- Similarity preserves regions. -/
theorem regionCount_map {n : ℕ} (S : PlaneSimilarity) (A : Arrangement n) :
    regionCount (S.mapArrangement A) = regionCount A := by
  have hcompl :
      S.toFun '' ((occupied A)ᶜ : Set Point) =
        (occupied (S.mapArrangement A))ᶜ := by
    calc
      S.toFun '' ((occupied A)ᶜ : Set Point) =
          (S.toFun '' occupied A)ᶜ :=
        Set.image_compl_eq (f := S.toFun) S.homeomorph.bijective
      _ = (occupied (S.mapArrangement A))ᶜ := by
        rw [image_occupied]
  let e : FreeSpace A ≃ₜ FreeSpace (S.mapArrangement A) :=
    (S.homeomorph.image ((occupied A)ᶜ : Set Point)).trans
      (Homeomorph.setCongr hcompl)
  unfold regionCount
  exact Nat.card_congr (connectedComponentsEquivOfHomeomorph e).symm

end PlaneSimilarity

/-- Standard unit lollipop. -/
def standardLollipop : Lollipop where
  center := 0
  radial := R2.toPoint (fun i : Fin 2 => if i = 0 then 1 else 0)
  radial_ne_zero := by
    intro h
    have := congrFun (congrArg R2.ofPoint h) 0
    norm_num at this

/-- Rotation carrying the positive x-axis to a unit vector. -/
def rotationTo (u : Point) : Point →ₗ[ℝ] Point where
  toFun x := R2.toPoint fun i : Fin 2 =>
    if i = 0 then u 0 * x 0 - u 1 * x 1
    else u 1 * x 0 + u 0 * x 1
  map_add' := by
    intro x y
    ext i
    fin_cases i <;> simp [R2.toPoint] <;> ring_nf
  map_smul' := by
    intro a x
    ext i
    fin_cases i <;> simp [R2.toPoint] <;> ring_nf

theorem rotationTo_dotPoint {u : Point}
    (hu : u 0 ^ 2 + u 1 ^ 2 = 1) (x y : Point) :
    dotPoint (rotationTo u x) (rotationTo u y) = dotPoint x y := by
  unfold rotationTo dotPoint
  simp [R2.toPoint]
  calc
    (u 0 * x 0 - u 1 * x 1) * (u 0 * y 0 - u 1 * y 1) +
        (u 1 * x 0 + u 0 * x 1) * (u 1 * y 0 + u 0 * y 1) =
        (u 0 ^ 2 + u 1 ^ 2) * (x 0 * y 0 + x 1 * y 1) := by ring
    _ = x 0 * y 0 + x 1 * y 1 := by rw [hu]; ring

theorem rotationTo_detPoint {u : Point}
    (hu : u 0 ^ 2 + u 1 ^ 2 = 1) (x y : Point) :
    detPoint (rotationTo u x) (rotationTo u y) = detPoint x y := by
  unfold rotationTo detPoint
  simp [R2.toPoint]
  calc
    (u 0 * x 0 - u 1 * x 1) * (u 1 * y 0 + u 0 * y 1) -
        (u 1 * x 0 + u 0 * x 1) * (u 0 * y 0 - u 1 * y 1) =
        (u 0 ^ 2 + u 1 ^ 2) * (x 0 * y 1 - x 1 * y 0) := by ring
    _ = x 0 * y 1 - x 1 * y 0 := by rw [hu]; ring

/-- Unit-vector rotation as a linear isometry equivalence. -/
def rotationToIsometry (u : Point) (hu : ‖u‖ = 1) : Point ≃ₗᵢ[ℝ] Point := by
  let v : Point := R2.toPoint (fun i : Fin 2 => if i = 0 then u 0 else -u 1)
  have hsq : u 0 ^ 2 + u 1 ^ 2 = 1 :=
    point_coord_sq_eq_one_of_norm_eq_one hu
  exact
    { toFun := rotationTo u
      invFun := rotationTo v
      left_inv := by
        intro x
        ext i
        fin_cases i
        · simp [rotationTo, v, R2.toPoint]
          ring_nf
          calc
            u 0 ^ 2 * x 0 + x 0 * u 1 ^ 2 =
                (u 0 ^ 2 + u 1 ^ 2) * x 0 := by ring
            _ = x 0 := by rw [hsq]; ring
        · simp [rotationTo, v, R2.toPoint]
          ring_nf
          calc
            u 1 ^ 2 * x 1 + u 0 ^ 2 * x 1 =
                (u 0 ^ 2 + u 1 ^ 2) * x 1 := by ring
            _ = x 1 := by rw [hsq]; ring
      right_inv := by
        intro x
        ext i
        fin_cases i
        · simp [rotationTo, v, R2.toPoint]
          ring_nf
          calc
            u 0 ^ 2 * x 0 + x 0 * u 1 ^ 2 =
                (u 0 ^ 2 + u 1 ^ 2) * x 0 := by ring
            _ = x 0 := by rw [hsq]; ring
        · simp [rotationTo, v, R2.toPoint]
          ring_nf
          calc
            u 1 ^ 2 * x 1 + u 0 ^ 2 * x 1 =
                (u 0 ^ 2 + u 1 ^ 2) * x 1 := by ring
            _ = x 1 := by rw [hsq]; ring
      map_add' := (rotationTo u).map_add
      map_smul' := (rotationTo u).map_smul
      norm_map' := by
        intro x
        have hnormsq : ‖rotationTo u x‖ ^ 2 = ‖x‖ ^ 2 := by
          rw [point_norm_sq_eq, point_norm_sq_eq]
          simp [rotationTo, R2.toPoint]
          ring_nf
          nlinarith [hsq]
        exact (sq_eq_sq₀ (norm_nonneg (rotationTo u x)) (norm_nonneg x)).1 hnormsq }

/-- Canonical positive similarity from the standard lollipop to `L`. -/
def similarityTo (L : Lollipop) : PlaneSimilarity where
  scale := L.radius
  scale_pos := L.radius_pos
  orthogonal := rotationToIsometry L.unitRadial L.norm_unitRadial
  translation := L.center

@[simp] theorem similarityTo_standard (L : Lollipop) :
    (similarityTo L).mapLollipop standardLollipop = L := by
  apply Lollipop.ext
  · ext i
    simp [similarityTo, standardLollipop, rotationToIsometry,
      PlaneSimilarity.mapLollipop, PlaneSimilarity.toFun,
      rotationTo, R2.toPoint]
  · ext i
    fin_cases i <;>
      simp [similarityTo, standardLollipop, rotationToIsometry,
        PlaneSimilarity.mapLollipop, PlaneSimilarity.toFun,
        rotationTo, L.radial_eq_radius_smul_unitRadial, R2.toPoint]

end Lower
end EndToEnd
end Concrete
end Lollipop
