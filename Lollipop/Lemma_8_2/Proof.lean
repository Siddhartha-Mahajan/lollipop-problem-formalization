import Lollipop.Proposition_2_1.Proof
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
This is the substantive proof compilation unit for `Lemma_8_2`.
All project proof components used below are integrated here or imported
directly from another manuscript-numbered `Proof.lean` file.
-/

/-!
Proof component 1: `EndToEnd.Lower.Similarity`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

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

/-!
Proof component 2: `EndToEnd.Lower.PairChamber`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
# Strict pair chambers

The lower construction is controlled by a finite list of strict polynomial
inequalities.  They determine the exact number of primitive intersections of
two lollipops and are stable under a sufficiently small perturbation.

The key correction relative to the first manuscript draft is the `zero` mixed
code.  A ray--circle component is empty either because the supporting line has
negative discriminant, or because the mixed quadratic is positive at the
anchor and already increasing there, so every real supporting-line root lies
strictly behind the accepted ray.  The latter condition also correctly covers
a tangency behind the anchor.  The corrected polynomial family uses both
alternatives.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace Lower

open Set

/-- Topology inherited from center/radial coordinates.  This is used only for
openness and genericization; the nonzero proof field carries no data. -/
instance lollipopTopologicalSpace : TopologicalSpace Lollipop :=
  TopologicalSpace.induced (fun L : Lollipop => (L.center, L.radial)) inferInstance

/-- The coordinate map defining the topology. -/
def lollipopCoordinates (L : Lollipop) : Point × Point :=
  (L.center, L.radial)

@[continuity, fun_prop] theorem continuous_lollipopCoordinates :
    Continuous lollipopCoordinates :=
  continuous_induced_dom

@[continuity, fun_prop] theorem continuous_lollipop_center :
    Continuous (fun L : Lollipop => L.center) :=
  continuous_fst.comp continuous_lollipopCoordinates

@[continuity, fun_prop] theorem continuous_lollipop_radial :
    Continuous (fun L : Lollipop => L.radial) :=
  continuous_snd.comp continuous_lollipopCoordinates

@[continuity, fun_prop] theorem continuous_lollipop_radius :
    Continuous (fun L : Lollipop => L.radius) := by
  unfold Lollipop.radius
  fun_prop

@[continuity, fun_prop] theorem continuous_lollipop_unitRadial :
    Continuous (fun L : Lollipop => L.unitRadial) := by
  unfold Lollipop.unitRadial
  exact (continuous_lollipop_radius.inv₀ (fun L => L.radius_ne_zero)).smul
    continuous_lollipop_radial

@[continuity, fun_prop] theorem continuous_lollipop_center_comp
    {X : Type*} [TopologicalSpace X] {f : X → Lollipop}
    (hf : Continuous f) :
    Continuous (fun x => (f x).center) :=
  continuous_lollipop_center.comp hf

@[continuity, fun_prop] theorem continuous_lollipop_radial_comp
    {X : Type*} [TopologicalSpace X] {f : X → Lollipop}
    (hf : Continuous f) :
    Continuous (fun x => (f x).radial) :=
  continuous_lollipop_radial.comp hf

@[continuity, fun_prop] theorem continuous_lollipop_radius_comp
    {X : Type*} [TopologicalSpace X] {f : X → Lollipop}
    (hf : Continuous f) :
    Continuous (fun x => (f x).radius) :=
  continuous_lollipop_radius.comp hf

@[continuity, fun_prop] theorem continuous_lollipop_unitRadial_comp
    {X : Type*} [TopologicalSpace X] {f : X → Lollipop}
    (hf : Continuous f) :
    Continuous (fun x => (f x).unitRadial) :=
  continuous_lollipop_unitRadial.comp hf

/-- Squared Euclidean norm, written polynomially. -/
def normSqPoint (x : Point) : ℝ := dotPoint x x

/-- Center displacement from `L` to `M`. -/
def displacement (L M : Lollipop) : Point := M.center - L.center

/-- Squared center distance. -/
def centerDistanceSq (L M : Lollipop) : ℝ :=
  normSqPoint (displacement L M)

/-- Projection of the center displacement onto the unit stem direction of
`L`.  A supporting-line point is written `L.center + q • L.unitRadial`; it is
on the actual stem exactly when `L.radius ≤ q`. -/
def projectedCenterParameter (L M : Lollipop) : ℝ :=
  dotPoint (displacement L M) L.unitRadial

/-- Discriminant divided by four for the supporting line of `L` against the
circle of `M`. -/
def lineDiscriminant (L M : Lollipop) : ℝ :=
  M.radius ^ 2 -
    (centerDistanceSq L M - projectedCenterParameter L M ^ 2)

/-- Power of the anchor of `L` with respect to the circle of `M`. -/
def anchorPower (L M : Lollipop) : ℝ :=
  normSqPoint (L.anchor - M.center) - M.radius ^ 2

/-- Signed distance, in unit-speed stem coordinates, from the anchor of `L`
to the vertex of the mixed quadratic. -/
def vertexAhead (L M : Lollipop) : ℝ :=
  projectedCenterParameter L M - L.radius

/-- Strict inner and outer circle margins.  Both are positive exactly when the
two circles meet in two transverse points. -/
def circleOuterMargin (L M : Lollipop) : ℝ :=
  (L.radius + M.radius) ^ 2 - centerDistanceSq L M

def circleInnerMargin (L M : Lollipop) : ℝ :=
  centerDistanceSq L M - (L.radius - M.radius) ^ 2

/-- Determinant of the two actual unit stem directions. -/
def directionDet (L M : Lollipop) : ℝ :=
  detPoint L.unitRadial M.unitRadial

/-- Supporting-line parameters of the unique ray--ray intersection when the
directions are nonparallel. -/
def leftLineParameter (L M : Lollipop) : ℝ :=
  detPoint (displacement L M) M.unitRadial / directionDet L M

def rightLineParameter (L M : Lollipop) : ℝ :=
  detPoint (displacement L M) L.unitRadial / directionDet L M

private theorem continuous_detPoint_comp
    {X : Type*} [TopologicalSpace X] {u v : X → Point}
    (hu : Continuous u) (hv : Continuous v) :
    Continuous (fun x => detPoint (u x) (v x)) := by
  unfold detPoint
  fun_prop

private theorem continuous_dotPoint_comp
    {X : Type*} [TopologicalSpace X] {u v : X → Point}
    (hu : Continuous u) (hv : Continuous v) :
    Continuous (fun x => dotPoint (u x) (v x)) := by
  unfold dotPoint
  fun_prop

private theorem continuous_normSqPoint_comp
    {X : Type*} [TopologicalSpace X] {u : X → Point}
    (hu : Continuous u) :
    Continuous (fun x => normSqPoint (u x)) :=
  continuous_dotPoint_comp hu hu

private theorem continuous_displacement_pair :
    Continuous (fun p : Lollipop × Lollipop => displacement p.1 p.2) := by
  unfold displacement
  fun_prop

private theorem continuous_centerDistanceSq_pair :
    Continuous (fun p : Lollipop × Lollipop => centerDistanceSq p.1 p.2) := by
  unfold centerDistanceSq
  exact continuous_normSqPoint_comp continuous_displacement_pair

private theorem continuous_projectedCenterParameter_pair :
    Continuous (fun p : Lollipop × Lollipop =>
      projectedCenterParameter p.1 p.2) := by
  unfold projectedCenterParameter
  exact continuous_dotPoint_comp continuous_displacement_pair
    (continuous_lollipop_unitRadial.comp continuous_fst)

private theorem continuous_lineDiscriminant_pair :
    Continuous (fun p : Lollipop × Lollipop =>
      lineDiscriminant p.1 p.2) := by
  unfold lineDiscriminant
  exact ((continuous_lollipop_radius.comp continuous_snd).pow 2).sub
    (continuous_centerDistanceSq_pair.sub
      (continuous_projectedCenterParameter_pair.pow 2))

private theorem continuous_anchorPower_pair :
    Continuous (fun p : Lollipop × Lollipop => anchorPower p.1 p.2) := by
  unfold anchorPower
  have hanchor : Continuous (fun p : Lollipop × Lollipop => p.1.anchor) := by
    unfold Lollipop.anchor
    fun_prop
  exact (continuous_normSqPoint_comp
    (hanchor.sub (continuous_lollipop_center.comp continuous_snd))).sub
      ((continuous_lollipop_radius.comp continuous_snd).pow 2)

private theorem continuous_vertexAhead_pair :
    Continuous (fun p : Lollipop × Lollipop => vertexAhead p.1 p.2) := by
  unfold vertexAhead
  exact continuous_projectedCenterParameter_pair.sub
    (continuous_lollipop_radius.comp continuous_fst)

private theorem continuous_circleOuterMargin_pair :
    Continuous (fun p : Lollipop × Lollipop =>
      circleOuterMargin p.1 p.2) := by
  unfold circleOuterMargin
  exact (((continuous_lollipop_radius.comp continuous_fst).add
    (continuous_lollipop_radius.comp continuous_snd)).pow 2).sub
      continuous_centerDistanceSq_pair

private theorem continuous_circleInnerMargin_pair :
    Continuous (fun p : Lollipop × Lollipop =>
      circleInnerMargin p.1 p.2) := by
  unfold circleInnerMargin
  exact continuous_centerDistanceSq_pair.sub
    (((continuous_lollipop_radius.comp continuous_fst).sub
      (continuous_lollipop_radius.comp continuous_snd)).pow 2)

private theorem continuous_directionDet_pair :
    Continuous (fun p : Lollipop × Lollipop => directionDet p.1 p.2) := by
  unfold directionDet
  exact continuous_detPoint_comp
    (continuous_lollipop_unitRadial.comp continuous_fst)
    (continuous_lollipop_unitRadial.comp continuous_snd)

private theorem continuous_leftLineNumerator_pair :
    Continuous (fun p : Lollipop × Lollipop =>
      detPoint (displacement p.1 p.2) (p.2).unitRadial) :=
  continuous_detPoint_comp continuous_displacement_pair
    (continuous_lollipop_unitRadial.comp continuous_snd)

private theorem continuous_rightLineNumerator_pair :
    Continuous (fun p : Lollipop × Lollipop =>
      detPoint (displacement p.1 p.2) (p.1).unitRadial) :=
  continuous_detPoint_comp continuous_displacement_pair
    (continuous_lollipop_unitRadial.comp continuous_fst)

/-- The three strict possibilities for an oriented ray--circle primitive. -/
inductive MixedCode
  | zero
  | one
  | two
  deriving DecidableEq, Repr

namespace MixedCode

/-- Numerical contribution of a mixed primitive. -/
def crossings : MixedCode → ℕ
  | zero => 0
  | one  => 1
  | two  => 2

/-- Strict semialgebraic realization of an oriented mixed code.

For `zero`, the first branch is the disjoint-supporting-line alternative.  The
second branch says the line meets the circle twice, the anchor is outside, and
the vertex lies behind the anchor; hence both roots are rejected by the ray
constraint. -/
def Realized (code : MixedCode) (L M : Lollipop) : Prop :=
  match code with
  | zero =>
      lineDiscriminant L M < 0 ∨
        (0 < anchorPower L M ∧ vertexAhead L M < 0)
  | one =>
      0 < lineDiscriminant L M ∧ anchorPower L M < 0
  | two =>
      0 < lineDiscriminant L M ∧
        0 < anchorPower L M ∧ 0 < vertexAhead L M

end MixedCode

/-- A complete strict pair chamber.  Circle--circle contributes two crossings
in every chamber used by the Karlsson construction. -/
structure StrictPairCode where
  leftRayRightCircle : MixedCode
  rightRayLeftCircle : MixedCode
  rayRay : Bool
  deriving DecidableEq, Repr

namespace StrictPairCode

/-- Total finite crossing number encoded by a strict chamber. -/
def crossings (code : StrictPairCode) : ℕ :=
  2 + code.leftRayRightCircle.crossings +
    code.rightRayLeftCircle.crossings + (if code.rayRay then 1 else 0)

/-- Four-crossing chamber used inside one cluster. -/
def four : StrictPairCode :=
  ⟨.one, .zero, true⟩

/-- Five-crossing chamber used by the exceptional base pair `(0,1)`. -/
def five : StrictPairCode :=
  ⟨.two, .zero, true⟩

/-- Seven-crossing chamber used by the other five base pairs. -/
def seven : StrictPairCode :=
  ⟨.two, .two, true⟩

@[simp] theorem crossings_four : four.crossings = 4 := by decide
@[simp] theorem crossings_five : five.crossings = 5 := by decide
@[simp] theorem crossings_seven : seven.crossings = 7 := by decide

theorem crossings_pos (code : StrictPairCode) : 0 < code.crossings := by
  rcases code with ⟨left, right, rayRay⟩
  cases left <;> cases right <;> cases rayRay <;>
    norm_num [crossings, MixedCode.crossings]

end StrictPairCode

/-- Strict ray--ray realization.  The lower construction only uses the `true`
case.  The `false` case deliberately keeps `directionDet ≠ 0`: it describes
an open nonintersection chamber in which the unique supporting-line
intersection lies strictly behind at least one anchor.  Parallelism is a
boundary stratum, not part of a strict chamber. -/
def RayRayCodeRealized (b : Bool) (L M : Lollipop) : Prop :=
  if b then
    directionDet L M ≠ 0 ∧
      L.radius < leftLineParameter L M ∧
      M.radius < rightLineParameter L M
  else
    directionDet L M ≠ 0 ∧
      (leftLineParameter L M < L.radius ∨
        rightLineParameter L M < M.radius)

theorem directionDet_swap (L M : Lollipop) :
    directionDet M L = -directionDet L M := by
  unfold directionDet detPoint
  ring

theorem detPoint_neg_left (u v : Point) :
    detPoint (-u) v = -detPoint u v := by
  unfold detPoint
  simp
  ring

theorem displacement_swap (L M : Lollipop) :
    displacement M L = -displacement L M := by
  ext i
  simp [displacement, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

theorem leftLineParameter_swap (L M : Lollipop) :
    leftLineParameter M L = rightLineParameter L M := by
  unfold leftLineParameter rightLineParameter
  rw [displacement_swap, directionDet_swap, detPoint_neg_left]
  rw [neg_div_neg_eq]

theorem rightLineParameter_swap (L M : Lollipop) :
    rightLineParameter M L = leftLineParameter L M := by
  unfold leftLineParameter rightLineParameter
  rw [displacement_swap, directionDet_swap, detPoint_neg_left]
  rw [neg_div_neg_eq]

theorem rayRayCodeRealized_swap
    {b : Bool} {L M : Lollipop}
    (h : RayRayCodeRealized b L M) :
    RayRayCodeRealized b M L := by
  cases b
  · simp only [RayRayCodeRealized, if_false] at h ⊢
    refine ⟨?_, ?_⟩
    · rw [directionDet_swap]
      exact neg_ne_zero.2 h.1
    rcases h.2 with hleft | hright
    · exact Or.inr (by simpa [rightLineParameter_swap] using hleft)
    · exact Or.inl (by simpa [leftLineParameter_swap] using hright)
  · simp only [RayRayCodeRealized, if_true] at h ⊢
    refine ⟨?_, ?_, ?_⟩
    · rw [directionDet_swap]
      exact neg_ne_zero.2 h.1
    · rw [leftLineParameter_swap]
      exact h.2.2
    · rw [rightLineParameter_swap]
      exact h.2.1

private theorem isOpen_mixedCodeRealized (code : MixedCode) :
    IsOpen {p : Lollipop × Lollipop | code.Realized p.1 p.2} := by
  have hdisc := continuous_lineDiscriminant_pair
  have hpower := continuous_anchorPower_pair
  have hvertex := continuous_vertexAhead_pair
  cases code
  · dsimp [MixedCode.Realized]
    rw [Set.setOf_or, Set.setOf_and]
    exact (isOpen_lt hdisc continuous_const).union
      ((isOpen_lt continuous_const hpower).inter
        (isOpen_lt hvertex continuous_const))
  · dsimp [MixedCode.Realized]
    rw [Set.setOf_and]
    exact (isOpen_lt continuous_const hdisc).inter
      (isOpen_lt hpower continuous_const)
  · dsimp [MixedCode.Realized]
    rw [Set.setOf_and, Set.setOf_and]
    exact (isOpen_lt continuous_const hdisc).inter
      ((isOpen_lt continuous_const hpower).inter
        (isOpen_lt continuous_const hvertex))

private theorem isOpen_mixedCodeRealized_swap (code : MixedCode) :
    IsOpen {p : Lollipop × Lollipop | code.Realized p.2 p.1} := by
  simpa [Function.comp_def] using
    (isOpen_mixedCodeRealized code).preimage continuous_swap

private theorem isOpen_rayRayCodeRealized (b : Bool) :
    IsOpen {p : Lollipop × Lollipop | RayRayCodeRealized b p.1 p.2} := by
  let U : Set (Lollipop × Lollipop) :=
    {p | directionDet p.1 p.2 ≠ 0}
  have hdetCont := continuous_directionDet_pair
  have hU : IsOpen U := by
    dsimp [U]
    exact isOpen_ne_fun hdetCont continuous_const
  have hleft : ContinuousOn
      (fun p : Lollipop × Lollipop => leftLineParameter p.1 p.2) U := by
    unfold leftLineParameter
    exact continuous_leftLineNumerator_pair.continuousOn.div hdetCont.continuousOn
      (by intro p hp; exact hp)
  have hright : ContinuousOn
      (fun p : Lollipop × Lollipop => rightLineParameter p.1 p.2) U := by
    unfold rightLineParameter
    exact continuous_rightLineNumerator_pair.continuousOn.div hdetCont.continuousOn
      (by intro p hp; exact hp)
  have hLrad : ContinuousOn (fun p : Lollipop × Lollipop => p.1.radius) U :=
    (by fun_prop : Continuous (fun p : Lollipop × Lollipop => p.1.radius)).continuousOn
  have hMrad : ContinuousOn (fun p : Lollipop × Lollipop => p.2.radius) U :=
    (by fun_prop : Continuous (fun p : Lollipop × Lollipop => p.2.radius)).continuousOn
  have hleftForward :
      IsOpen (U ∩ {p : Lollipop × Lollipop |
        p.1.radius - leftLineParameter p.1 p.2 < 0}) := by
    simpa [Set.preimage] using
      (hLrad.sub hleft).isOpen_inter_preimage hU
        (isOpen_Iio : IsOpen (Set.Iio (0 : ℝ)))
  have hrightForward :
      IsOpen (U ∩ {p : Lollipop × Lollipop |
        p.2.radius - rightLineParameter p.1 p.2 < 0}) := by
    simpa [Set.preimage] using
      (hMrad.sub hright).isOpen_inter_preimage hU
        (isOpen_Iio : IsOpen (Set.Iio (0 : ℝ)))
  have hleftBehind :
      IsOpen (U ∩ {p : Lollipop × Lollipop |
        leftLineParameter p.1 p.2 - p.1.radius < 0}) := by
    simpa [Set.preimage] using
      (hleft.sub hLrad).isOpen_inter_preimage hU
        (isOpen_Iio : IsOpen (Set.Iio (0 : ℝ)))
  have hrightBehind :
      IsOpen (U ∩ {p : Lollipop × Lollipop |
        rightLineParameter p.1 p.2 - p.2.radius < 0}) := by
    simpa [Set.preimage] using
      (hright.sub hMrad).isOpen_inter_preimage hU
        (isOpen_Iio : IsOpen (Set.Iio (0 : ℝ)))
  cases b
  · dsimp [RayRayCodeRealized]
    simpa [U, Set.setOf_and, Set.setOf_or, sub_lt_zero, and_or_left] using
      hleftBehind.union hrightBehind
  · dsimp [RayRayCodeRealized]
    convert hleftForward.inter hrightForward using 1
    ext p
    simp [U, sub_lt_zero, and_assoc, and_left_comm, and_comm]

/-- Parameter-space set cut out by all strict inequalities belonging to a pair
code.  Keeping this as a set avoids expensive conversions between large
`setOf` predicates and finite intersections in the openness proofs. -/
def strictPairChamberSet (code : StrictPairCode) :
    Set (Lollipop × Lollipop) :=
  {p | 0 < circleOuterMargin p.1 p.2} ∩
    ({p | 0 < circleInnerMargin p.1 p.2} ∩
      ({p | code.leftRayRightCircle.Realized p.1 p.2} ∩
        ({p | code.rightRayLeftCircle.Realized p.2 p.1} ∩
          {p | RayRayCodeRealized code.rayRay p.1 p.2})))

/-- Realization of all strict inequalities belonging to a pair code. -/
def RealizesStrictPairCode
    (code : StrictPairCode) (L M : Lollipop) : Prop :=
  (L, M) ∈ strictPairChamberSet code

@[simp] theorem mem_strictPairChamberSet
    (code : StrictPairCode) (p : Lollipop × Lollipop) :
    p ∈ strictPairChamberSet code ↔
      0 < circleOuterMargin p.1 p.2 ∧
      0 < circleInnerMargin p.1 p.2 ∧
      code.leftRayRightCircle.Realized p.1 p.2 ∧
      code.rightRayLeftCircle.Realized p.2 p.1 ∧
      RayRayCodeRealized code.rayRay p.1 p.2 := by
  rfl

/-- Swapping the two lollipops swaps the two mixed codes. -/
def StrictPairCode.swap (code : StrictPairCode) : StrictPairCode :=
  ⟨code.rightRayLeftCircle, code.leftRayRightCircle, code.rayRay⟩

@[simp] theorem StrictPairCode.crossings_swap (code : StrictPairCode) :
    code.swap.crossings = code.crossings := by
  rcases code with ⟨left, right, rayRay⟩
  cases left <;> cases right <;> cases rayRay <;>
    decide

namespace PairChamberPort

/-!
The lemmas in this namespace are elementary coordinate proofs.  They are
written against the intended Mathlib polynomial/root APIs.  On a pinned
Mathlib version, the porting work is to replace the descriptive helper names
below by the exact local lemmas (or prove those helpers in this namespace).
No theorem in the public endpoint takes these statements as hypotheses.
-/

/-- Expansion of the mixed quadratic in unit-speed coordinates. -/
theorem mixed_quadratic_identity (L M : Lollipop) (q : ℝ) :
    normSqPoint (L.center + q • L.unitRadial - M.center) - M.radius ^ 2 =
      (q - projectedCenterParameter L M) ^ 2 - lineDiscriminant L M := by
  rw [show L.center + q • L.unitRadial - M.center =
      q • L.unitRadial - displacement L M by
    simp [displacement]; abel]
  have huSq : L.unitRadial 0 ^ 2 + L.unitRadial 1 ^ 2 = 1 :=
    point_coord_sq_eq_one_of_norm_eq_one L.norm_unitRadial
  simp only [normSqPoint, projectedCenterParameter, lineDiscriminant,
    centerDistanceSq, displacement, dotPoint, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, WithLp.ofLp_add, WithLp.ofLp_sub, WithLp.ofLp_smul]
  ring_nf
  nlinarith [huSq]

/-- The anchor-power diagnostic is the mixed quadratic at `q=L.radius`. -/
theorem anchorPower_eq_mixed_at_anchor (L M : Lollipop) :
    anchorPower L M =
      (L.radius - projectedCenterParameter L M) ^ 2 -
        lineDiscriminant L M := by
  rw [← mixed_quadratic_identity L M L.radius]
  simp [anchorPower, Lollipop.anchor,
    L.radial_eq_radius_smul_unitRadial, normSqPoint]

private theorem normSqPoint_eq_norm_sq (x : Point) :
    normSqPoint x = ‖x‖ ^ 2 := by
  rw [point_norm_sq_eq]
  simp [normSqPoint, dotPoint, sq]

private theorem centerDistanceSq_pos_of_circleInnerMargin_pos
    {L M : Lollipop} (hin : 0 < circleInnerMargin L M) :
    0 < centerDistanceSq L M := by
  unfold circleInnerMargin at hin
  have hsquare : 0 ≤ (L.radius - M.radius) ^ 2 := sq_nonneg _
  nlinarith

private theorem centers_ne_of_circleInnerMargin_pos
    {L M : Lollipop} (hin : 0 < circleInnerMargin L M) :
    L.center ≠ M.center := by
  intro hcenter
  have hpos := centerDistanceSq_pos_of_circleInnerMargin_pos hin
  have hzero : centerDistanceSq L M = 0 := by
    simp [centerDistanceSq, displacement, normSqPoint, dotPoint, hcenter]
  nlinarith

private def perpPoint (u : Point) : Point :=
  R2.toPoint fun i : Fin 2 => if i = 0 then -u 1 else u 0

private theorem dotPoint_perpPoint_self (u : Point) :
    dotPoint u (perpPoint u) = 0 := by
  simp [perpPoint, R2.toPoint, dotPoint]
  ring

private theorem dotPoint_self_perpPoint (u : Point) :
    dotPoint (perpPoint u) u = 0 := by
  rw [dotPoint_comm, dotPoint_perpPoint_self]

private theorem normSqPoint_perpPoint (u : Point) :
    normSqPoint (perpPoint u) = normSqPoint u := by
  simp [perpPoint, R2.toPoint, normSqPoint, dotPoint]
  ring

private theorem detPoint_self_perpPoint (u : Point) :
    detPoint u (perpPoint u) = normSqPoint u := by
  simp [perpPoint, R2.toPoint, detPoint, normSqPoint, dotPoint]

private theorem detPoint_self (u : Point) :
    detPoint u u = 0 := by
  simp [detPoint]
  ring

private theorem detPoint_smul_add_smul_perp
    (u : Point) (a b : ℝ) :
    detPoint u (a • u + b • perpPoint u) = b * normSqPoint u := by
  simp [perpPoint, R2.toPoint, detPoint, normSqPoint, dotPoint]
  ring

private theorem detPoint_smul_left (a : ℝ) (u v : Point) :
    detPoint (a • u) v = a * detPoint u v := by
  simp [detPoint]
  ring

private theorem detPoint_smul_right (a : ℝ) (u v : Point) :
    detPoint u (a • v) = a * detPoint u v := by
  simp [detPoint]
  ring

private theorem normSqPoint_smul (a : ℝ) (u : Point) :
    normSqPoint (a • u) = a ^ 2 * normSqPoint u := by
  simp [normSqPoint, dotPoint]
  ring

private theorem dotPoint_smul_left (a : ℝ) (u v : Point) :
    dotPoint (a • u) v = a * dotPoint u v := by
  simp [dotPoint]
  ring

private theorem dotPoint_smul_right (a : ℝ) (u v : Point) :
    dotPoint u (a • v) = a * dotPoint u v := by
  rw [dotPoint_comm, dotPoint_smul_left, dotPoint_comm v u]

private theorem normSqPoint_add_of_dot_zero
    {u v : Point} (h : dotPoint u v = 0) :
    normSqPoint (u + v) = normSqPoint u + normSqPoint v := by
  have hsym : dotPoint v u = 0 := by simpa [dotPoint_comm] using h
  simp [normSqPoint, dotPoint] at h hsym ⊢
  nlinarith

private theorem normSqPoint_sub_of_dot_zero
    {u v : Point} (h : dotPoint u v = 0) :
    normSqPoint (u - v) = normSqPoint u + normSqPoint v := by
  have hneg : dotPoint u (-v) = 0 := by
    have h' : u 0 * v 0 + u 1 * v 1 = 0 := by
      simpa [dotPoint] using h
    simp [dotPoint]
    nlinarith
  have hnorm_neg : normSqPoint (-v) = normSqPoint v := by
    simpa using normSqPoint_smul (-1) v
  rw [sub_eq_add_neg, normSqPoint_add_of_dot_zero hneg, hnorm_neg]

private theorem similarityTo_unit_sq (Q : Lollipop) :
    Q.unitRadial 0 ^ 2 + Q.unitRadial 1 ^ 2 = 1 :=
  point_coord_sq_eq_one_of_norm_eq_one Q.norm_unitRadial

theorem similarityTo_displacement (Q L M : Lollipop) :
    displacement ((similarityTo Q).mapLollipop L)
        ((similarityTo Q).mapLollipop M) =
      Q.radius • rotationTo Q.unitRadial (displacement L M) := by
  unfold displacement
  change (similarityTo Q).toFun M.center - (similarityTo Q).toFun L.center =
    Q.radius • rotationTo Q.unitRadial (M.center - L.center)
  rw [PlaneSimilarity.sub_toFun]
  simp [similarityTo, rotationToIsometry]

theorem similarityTo_map_unitRadial (Q L : Lollipop) :
    ((similarityTo Q).mapLollipop L).unitRadial =
      rotationTo Q.unitRadial L.unitRadial := by
  rw [PlaneSimilarity.map_unitRadial]
  simp [similarityTo, rotationToIsometry]

private theorem normSqPoint_similarityTo_rotation (Q : Lollipop) (x : Point) :
    normSqPoint (Q.radius • rotationTo Q.unitRadial x) =
      Q.radius ^ 2 * normSqPoint x := by
  rw [normSqPoint_smul]
  unfold normSqPoint
  rw [rotationTo_dotPoint (similarityTo_unit_sq Q)]

theorem centerDistanceSq_similarityTo (Q L M : Lollipop) :
    centerDistanceSq ((similarityTo Q).mapLollipop L)
        ((similarityTo Q).mapLollipop M) =
      Q.radius ^ 2 * centerDistanceSq L M := by
  unfold centerDistanceSq
  rw [similarityTo_displacement, normSqPoint_similarityTo_rotation]

theorem projectedCenterParameter_similarityTo (Q L M : Lollipop) :
    projectedCenterParameter ((similarityTo Q).mapLollipop L)
        ((similarityTo Q).mapLollipop M) =
      Q.radius * projectedCenterParameter L M := by
  unfold projectedCenterParameter
  rw [similarityTo_displacement, similarityTo_map_unitRadial]
  rw [dotPoint_smul_left, rotationTo_dotPoint (similarityTo_unit_sq Q)]

theorem circleOuterMargin_similarityTo (Q L M : Lollipop) :
    circleOuterMargin ((similarityTo Q).mapLollipop L)
        ((similarityTo Q).mapLollipop M) =
      Q.radius ^ 2 * circleOuterMargin L M := by
  unfold circleOuterMargin
  rw [PlaneSimilarity.map_radius, PlaneSimilarity.map_radius,
    centerDistanceSq_similarityTo]
  simp [similarityTo]
  ring_nf

theorem circleInnerMargin_similarityTo (Q L M : Lollipop) :
    circleInnerMargin ((similarityTo Q).mapLollipop L)
        ((similarityTo Q).mapLollipop M) =
      Q.radius ^ 2 * circleInnerMargin L M := by
  unfold circleInnerMargin
  rw [PlaneSimilarity.map_radius, PlaneSimilarity.map_radius,
    centerDistanceSq_similarityTo]
  simp [similarityTo]
  ring_nf

theorem lineDiscriminant_similarityTo (Q L M : Lollipop) :
    lineDiscriminant ((similarityTo Q).mapLollipop L)
        ((similarityTo Q).mapLollipop M) =
      Q.radius ^ 2 * lineDiscriminant L M := by
  unfold lineDiscriminant
  rw [PlaneSimilarity.map_radius, centerDistanceSq_similarityTo,
    projectedCenterParameter_similarityTo]
  simp [similarityTo]
  ring_nf

theorem anchorPower_similarityTo (Q L M : Lollipop) :
    anchorPower ((similarityTo Q).mapLollipop L)
        ((similarityTo Q).mapLollipop M) =
      Q.radius ^ 2 * anchorPower L M := by
  unfold anchorPower
  rw [PlaneSimilarity.map_anchor, PlaneSimilarity.map_radius]
  change normSqPoint
      ((similarityTo Q).toFun L.anchor - (similarityTo Q).toFun M.center) -
        (Q.radius * M.radius) ^ 2 =
      Q.radius ^ 2 * (normSqPoint (L.anchor - M.center) - M.radius ^ 2)
  rw [PlaneSimilarity.sub_toFun]
  change normSqPoint (Q.radius • rotationTo Q.unitRadial (L.anchor - M.center)) -
        (Q.radius * M.radius) ^ 2 =
      Q.radius ^ 2 * (normSqPoint (L.anchor - M.center) - M.radius ^ 2)
  rw [normSqPoint_similarityTo_rotation]
  ring

theorem vertexAhead_similarityTo (Q L M : Lollipop) :
    vertexAhead ((similarityTo Q).mapLollipop L)
        ((similarityTo Q).mapLollipop M) =
      Q.radius * vertexAhead L M := by
  unfold vertexAhead
  rw [projectedCenterParameter_similarityTo, PlaneSimilarity.map_radius]
  simp [similarityTo]
  ring_nf

theorem directionDet_similarityTo (Q L M : Lollipop) :
    directionDet ((similarityTo Q).mapLollipop L)
        ((similarityTo Q).mapLollipop M) =
      directionDet L M := by
  unfold directionDet
  rw [similarityTo_map_unitRadial, similarityTo_map_unitRadial]
  exact rotationTo_detPoint (similarityTo_unit_sq Q) L.unitRadial M.unitRadial

theorem leftLineParameter_similarityTo (Q L M : Lollipop) :
    leftLineParameter ((similarityTo Q).mapLollipop L)
        ((similarityTo Q).mapLollipop M) =
      Q.radius * leftLineParameter L M := by
  unfold leftLineParameter
  rw [similarityTo_displacement, similarityTo_map_unitRadial,
    directionDet_similarityTo]
  rw [detPoint_smul_left, rotationTo_detPoint (similarityTo_unit_sq Q)]
  ring

theorem rightLineParameter_similarityTo (Q L M : Lollipop) :
    rightLineParameter ((similarityTo Q).mapLollipop L)
        ((similarityTo Q).mapLollipop M) =
      Q.radius * rightLineParameter L M := by
  unfold rightLineParameter
  rw [similarityTo_displacement, similarityTo_map_unitRadial,
    directionDet_similarityTo]
  rw [detPoint_smul_left, rotationTo_detPoint (similarityTo_unit_sq Q)]
  ring

private theorem pos_mul_iff_of_pos_left' {a x : ℝ} (ha : 0 < a) :
    0 < a * x ↔ 0 < x :=
  mul_pos_iff_of_pos_left ha

private theorem mul_lt_zero_iff_of_pos_left' {a x : ℝ} (ha : 0 < a) :
    a * x < 0 ↔ x < 0 := by
  constructor
  · intro h
    exact neg_of_mul_neg_right h ha.le
  · intro hx
    simpa using mul_lt_mul_of_pos_left hx ha

private theorem mul_lt_mul_left_iff_of_pos' {a x y : ℝ} (ha : 0 < a) :
    a * x < a * y ↔ x < y := by
  constructor
  · intro h
    exact lt_of_mul_lt_mul_left h ha.le
  · intro h
    exact mul_lt_mul_of_pos_left h ha

theorem mixedCodeRealized_similarityTo_iff
    (Q : Lollipop) (code : MixedCode) (L M : Lollipop) :
    code.Realized ((similarityTo Q).mapLollipop L)
        ((similarityTo Q).mapLollipop M) ↔
      code.Realized L M := by
  have hscale : 0 < Q.radius := Q.radius_pos
  have hscaleSq : 0 < Q.radius ^ 2 := sq_pos_of_pos hscale
  cases code <;>
    simp [MixedCode.Realized, lineDiscriminant_similarityTo,
      anchorPower_similarityTo, vertexAhead_similarityTo,
      pos_mul_iff_of_pos_left' hscaleSq,
      mul_lt_zero_iff_of_pos_left' hscaleSq,
      pos_mul_iff_of_pos_left' hscale,
      mul_lt_zero_iff_of_pos_left' hscale]

theorem rayRayCodeRealized_similarityTo_iff
    (Q : Lollipop) (b : Bool) (L M : Lollipop) :
    RayRayCodeRealized b ((similarityTo Q).mapLollipop L)
        ((similarityTo Q).mapLollipop M) ↔
      RayRayCodeRealized b L M := by
  have hscale : 0 < Q.radius := Q.radius_pos
  cases b
  · simp only [RayRayCodeRealized, if_false]
    rw [directionDet_similarityTo, leftLineParameter_similarityTo,
      rightLineParameter_similarityTo, PlaneSimilarity.map_radius,
      PlaneSimilarity.map_radius]
    simp [similarityTo, mul_lt_mul_left_iff_of_pos' hscale]
  · simp only [RayRayCodeRealized, if_true]
    rw [directionDet_similarityTo, leftLineParameter_similarityTo,
      rightLineParameter_similarityTo, PlaneSimilarity.map_radius,
      PlaneSimilarity.map_radius]
    simp [similarityTo, mul_lt_mul_left_iff_of_pos' hscale]

/-- Canonical positive similarities preserve every strict pair chamber. -/
theorem realizes_similarityTo_iff
    (Q : Lollipop) (code : StrictPairCode) (L M : Lollipop) :
    RealizesStrictPairCode code ((similarityTo Q).mapLollipop L)
        ((similarityTo Q).mapLollipop M) ↔
      RealizesStrictPairCode code L M := by
  have hscaleSq : 0 < Q.radius ^ 2 := sq_pos_of_pos Q.radius_pos
  rcases code with ⟨left, right, ray⟩
  simp [RealizesStrictPairCode, strictPairChamberSet,
    circleOuterMargin_similarityTo, circleInnerMargin_similarityTo,
    mixedCodeRealized_similarityTo_iff,
    rayRayCodeRealized_similarityTo_iff,
    pos_mul_iff_of_pos_left' hscaleSq]

private def circleChordParameter (L M : Lollipop) : ℝ :=
  (centerDistanceSq L M + L.radius ^ 2 - M.radius ^ 2) /
    (2 * Real.sqrt (centerDistanceSq L M))

private def circleChordHeightSq (L M : Lollipop) : ℝ :=
  L.radius ^ 2 - circleChordParameter L M ^ 2

private def circleChordUnit (L M : Lollipop) : Point :=
  (Real.sqrt (centerDistanceSq L M))⁻¹ • displacement L M

private theorem circleChordUnit_normSq
    {L M : Lollipop} (hin : 0 < circleInnerMargin L M) :
    normSqPoint (circleChordUnit L M) = 1 := by
  have hd2_pos : 0 < centerDistanceSq L M :=
    centerDistanceSq_pos_of_circleInnerMargin_pos hin
  have hd_pos : 0 < Real.sqrt (centerDistanceSq L M) :=
    Real.sqrt_pos.2 hd2_pos
  have hd_sq :
      (Real.sqrt (centerDistanceSq L M)) ^ 2 =
        centerDistanceSq L M :=
    Real.sq_sqrt hd2_pos.le
  unfold circleChordUnit
  rw [normSqPoint_smul]
  change
    (Real.sqrt (centerDistanceSq L M))⁻¹ ^ 2 *
      centerDistanceSq L M = 1
  field_simp [hd_pos.ne']
  rw [hd_sq]

private theorem displacement_eq_sqrt_smul_circleChordUnit
    {L M : Lollipop} (hin : 0 < circleInnerMargin L M) :
    displacement L M =
      Real.sqrt (centerDistanceSq L M) • circleChordUnit L M := by
  have hd2_pos : 0 < centerDistanceSq L M :=
    centerDistanceSq_pos_of_circleInnerMargin_pos hin
  have hd_pos : 0 < Real.sqrt (centerDistanceSq L M) :=
    Real.sqrt_pos.2 hd2_pos
  unfold circleChordUnit
  rw [smul_smul]
  field_simp [hd_pos.ne']
  simp

private theorem normSqPoint_smul_add_smul_perp
    {u : Point} (hu : normSqPoint u = 1) (a b : ℝ) :
    normSqPoint (a • u + b • perpPoint u) = a ^ 2 + b ^ 2 := by
  have hdot : dotPoint (a • u) (b • perpPoint u) = 0 := by
    rw [dotPoint_smul_left, dotPoint_smul_right, dotPoint_perpPoint_self]
    ring
  rw [normSqPoint_add_of_dot_zero hdot]
  rw [normSqPoint_smul, normSqPoint_smul, normSqPoint_perpPoint, hu]
  ring

private theorem circleChordHeightSq_pos_of_strict_margins
    {L M : Lollipop}
    (hout : 0 < circleOuterMargin L M)
    (hin : 0 < circleInnerMargin L M) :
    0 < circleChordHeightSq L M := by
  have hd2_pos : 0 < centerDistanceSq L M :=
    centerDistanceSq_pos_of_circleInnerMargin_pos hin
  have hd_pos : 0 < Real.sqrt (centerDistanceSq L M) :=
    Real.sqrt_pos.2 hd2_pos
  have hd_sq :
      (Real.sqrt (centerDistanceSq L M)) ^ 2 =
        centerDistanceSq L M :=
    Real.sq_sqrt hd2_pos.le
  have houter :
      0 < (L.radius + M.radius) ^ 2 - centerDistanceSq L M := by
    simpa [circleOuterMargin] using hout
  have hinner :
      0 < centerDistanceSq L M - (L.radius - M.radius) ^ 2 := by
    simpa [circleInnerMargin] using hin
  have hnum_pos :
      0 <
        ((L.radius + M.radius) ^ 2 - centerDistanceSq L M) *
          (centerDistanceSq L M - (L.radius - M.radius) ^ 2) :=
    mul_pos houter hinner
  have hidentity :
      circleChordHeightSq L M =
        (((L.radius + M.radius) ^ 2 - centerDistanceSq L M) *
            (centerDistanceSq L M - (L.radius - M.radius) ^ 2)) /
          (4 * centerDistanceSq L M) := by
    unfold circleChordHeightSq circleChordParameter
    field_simp [hd_pos.ne', hd2_pos.ne']
    rw [hd_sq]
    ring_nf
  rw [hidentity]
  exact div_pos hnum_pos (mul_pos (by norm_num) hd2_pos)

private def circleCircleWitness (L M : Lollipop) (sign : ℝ) : Point :=
  L.center +
    (circleChordParameter L M • circleChordUnit L M +
      (sign * Real.sqrt (circleChordHeightSq L M)) •
        perpPoint (circleChordUnit L M))

private theorem circleCircleWitness_sub_left
    (L M : Lollipop) (sign : ℝ) :
    circleCircleWitness L M sign - L.center =
      circleChordParameter L M • circleChordUnit L M +
        (sign * Real.sqrt (circleChordHeightSq L M)) •
          perpPoint (circleChordUnit L M) := by
  ext i
  simp [circleCircleWitness]

private theorem circleCircleWitness_sub_right
    {L M : Lollipop} (hin : 0 < circleInnerMargin L M) (sign : ℝ) :
    circleCircleWitness L M sign - M.center =
      (circleChordParameter L M - Real.sqrt (centerDistanceSq L M)) •
          circleChordUnit L M +
        (sign * Real.sqrt (circleChordHeightSq L M)) •
          perpPoint (circleChordUnit L M) := by
  have hdisp := displacement_eq_sqrt_smul_circleChordUnit (L := L) (M := M) hin
  have hcenter : M.center = L.center + displacement L M := by
    ext i
    simp [displacement]
  ext i
  rw [hcenter, hdisp]
  simp [circleCircleWitness, sub_smul]
  ring

private theorem mem_circle_of_normSqPoint_sub_center_eq_radius_sq
    {L : Lollipop} {x : Point}
    (h : normSqPoint (x - L.center) = L.radius ^ 2) :
    x ∈ L.circle := by
  have hsq : ‖x - L.center‖ ^ 2 = L.radius ^ 2 := by
    rw [← normSqPoint_eq_norm_sq]
    exact h
  have hnorm :
      ‖x - L.center‖ = L.radius :=
    (sq_eq_sq₀ (norm_nonneg _) L.radius_pos.le).1 hsq
  simpa [Lollipop.circle] using hnorm

private theorem circleChordLeftNormAlgebra (L M : Lollipop) :
    circleChordParameter L M ^ 2 + circleChordHeightSq L M =
      L.radius ^ 2 := by
  unfold circleChordHeightSq
  ring

private theorem circleChordRightNormAlgebra
    {L M : Lollipop} (hin : 0 < circleInnerMargin L M) :
    (circleChordParameter L M - Real.sqrt (centerDistanceSq L M)) ^ 2 +
        circleChordHeightSq L M =
      M.radius ^ 2 := by
  have hd2_pos : 0 < centerDistanceSq L M :=
    centerDistanceSq_pos_of_circleInnerMargin_pos hin
  have hd_pos : 0 < Real.sqrt (centerDistanceSq L M) :=
    Real.sqrt_pos.2 hd2_pos
  have hd_sq :
      (Real.sqrt (centerDistanceSq L M)) ^ 2 =
        centerDistanceSq L M :=
    Real.sq_sqrt hd2_pos.le
  unfold circleChordHeightSq circleChordParameter
  field_simp [hd_pos.ne']
  rw [hd_sq]
  ring

private theorem circleCircleWitness_normSq_left
    {L M : Lollipop}
    (hout : 0 < circleOuterMargin L M)
    (hin : 0 < circleInnerMargin L M)
    {sign : ℝ} (hsign : sign ^ 2 = 1) :
    normSqPoint (circleCircleWitness L M sign - L.center) =
      L.radius ^ 2 := by
  have hu := circleChordUnit_normSq (L := L) (M := M) hin
  have hh_pos := circleChordHeightSq_pos_of_strict_margins
    (L := L) (M := M) hout hin
  have hsqrt_sq :
      (Real.sqrt (circleChordHeightSq L M)) ^ 2 =
        circleChordHeightSq L M :=
    Real.sq_sqrt hh_pos.le
  rw [circleCircleWitness_sub_left]
  rw [normSqPoint_smul_add_smul_perp hu]
  rw [mul_pow, hsign, one_mul, hsqrt_sq]
  exact circleChordLeftNormAlgebra L M

private theorem circleCircleWitness_normSq_right
    {L M : Lollipop}
    (hout : 0 < circleOuterMargin L M)
    (hin : 0 < circleInnerMargin L M)
    {sign : ℝ} (hsign : sign ^ 2 = 1) :
    normSqPoint (circleCircleWitness L M sign - M.center) =
      M.radius ^ 2 := by
  have hu := circleChordUnit_normSq (L := L) (M := M) hin
  have hh_pos := circleChordHeightSq_pos_of_strict_margins
    (L := L) (M := M) hout hin
  have hsqrt_sq :
      (Real.sqrt (circleChordHeightSq L M)) ^ 2 =
        circleChordHeightSq L M :=
    Real.sq_sqrt hh_pos.le
  rw [circleCircleWitness_sub_right hin]
  rw [normSqPoint_smul_add_smul_perp hu]
  rw [mul_pow, hsign, one_mul, hsqrt_sq]
  exact circleChordRightNormAlgebra hin

private theorem circleCircleWitness_mem_cc
    {L M : Lollipop}
    (hout : 0 < circleOuterMargin L M)
    (hin : 0 < circleInnerMargin L M)
    {sign : ℝ} (hsign : sign ^ 2 = 1) :
    circleCircleWitness L M sign ∈ cc L M := by
  refine ⟨?_, ?_⟩
  · exact mem_circle_of_normSqPoint_sub_center_eq_radius_sq
      (circleCircleWitness_normSq_left hout hin hsign)
  · exact mem_circle_of_normSqPoint_sub_center_eq_radius_sq
      (circleCircleWitness_normSq_right hout hin hsign)

private theorem circleCircleWitness_pos_ne_neg
    {L M : Lollipop}
    (hout : 0 < circleOuterMargin L M)
    (hin : 0 < circleInnerMargin L M) :
    circleCircleWitness L M 1 ≠ circleCircleWitness L M (-1) := by
  intro heq
  have hu := circleChordUnit_normSq (L := L) (M := M) hin
  have hh_pos := circleChordHeightSq_pos_of_strict_margins
    (L := L) (M := M) hout hin
  have hsqrt_pos :
      0 < Real.sqrt (circleChordHeightSq L M) :=
    Real.sqrt_pos.2 hh_pos
  have hdet := congrArg
    (fun x : Point =>
      detPoint (circleChordUnit L M) (x - L.center)) heq
  rw [circleCircleWitness_sub_left,
    circleCircleWitness_sub_left] at hdet
  rw [detPoint_smul_add_smul_perp,
    detPoint_smul_add_smul_perp, hu] at hdet
  norm_num at hdet
  nlinarith

/-- Strict circle margins classify the circle--circle primitive. -/
theorem circle_circle_ncard_eq_two
    {L M : Lollipop}
    (hout : 0 < circleOuterMargin L M)
    (hin : 0 < circleInnerMargin L M) :
    (cc L M).ncard = 2 := by
  let p : Point := circleCircleWitness L M 1
  let q : Point := circleCircleWitness L M (-1)
  have hp : p ∈ cc L M := by
    exact circleCircleWitness_mem_cc hout hin (by norm_num)
  have hq : q ∈ cc L M := by
    exact circleCircleWitness_mem_cc hout hin (by norm_num)
  have hpq : p ≠ q := by
    exact circleCircleWitness_pos_ne_neg hout hin
  have hsphere : concreteSphere L ≠ concreteSphere M := by
    intro hsphere
    exact centers_ne_of_circleInnerMargin_pos hin (by
      simpa [concreteSphere] using
        congrArg EuclideanGeometry.Sphere.center hsphere)
  have hfinite : (cc L M).Finite := by
    apply finite_of_forall_mem_eq_left_or_right
    intro a b x ha hb hx hab
    exact eq_or_eq_of_mem_cc_of_two_witnesses hsphere hab ha hb hx
  have hle : (cc L M).ncard ≤ 2 := by
    apply ncard_le_two_of_forall_mem_eq_left_or_right
    intro a b x ha hb hx hab
    exact eq_or_eq_of_mem_cc_of_two_witnesses hsphere hab ha hb hx
  have hlt : 1 < (cc L M).ncard := by
    rw [Set.one_lt_ncard_iff hfinite]
    exact ⟨p, q, hp, hq, hpq⟩
  omega

/-- The same strict margins imply transverse circle intersections. -/
theorem circle_circle_transverse
    {L M : Lollipop}
    (hout : 0 < circleOuterMargin L M)
    (hin : 0 < circleInnerMargin L M) :
    ∀ x, x ∈ cc L M → CircleCircleTransverseAt L M x := by
  intro x hx
  intro hdet
  let u : Point := x - L.center
  let v : Point := x - M.center
  have hu : normSqPoint u = L.radius ^ 2 := by
    have hxL : ‖x - L.center‖ = L.radius := by
      simpa [cc, Lollipop.circle] using hx.1
    rw [normSqPoint_eq_norm_sq, hxL]
  have hv : normSqPoint v = M.radius ^ 2 := by
    have hxM : ‖x - M.center‖ = M.radius := by
      simpa [cc, Lollipop.circle] using hx.2
    rw [normSqPoint_eq_norm_sq, hxM]
  have hdetuv : detPoint u v = 0 := by
    change detPoint (x - L.center) (x - M.center) = 0
    exact hdet
  have hpyth :
      dotPoint u v ^ 2 + detPoint u v ^ 2 =
        normSqPoint u * normSqPoint v := by
    simp only [dotPoint, detPoint, normSqPoint]
    ring_nf
  have hdot_sq : dotPoint u v ^ 2 = (L.radius * M.radius) ^ 2 := by
    rw [hdetuv] at hpyth
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] at hpyth
    rw [hu, hv] at hpyth
    nlinarith
  have hdot_cases :
      dotPoint u v = L.radius * M.radius ∨
        dotPoint u v = -(L.radius * M.radius) := by
    have hsq :
        dotPoint u v ^ 2 = (L.radius * M.radius) ^ 2 := hdot_sq
    exact (sq_eq_sq_iff_eq_or_eq_neg.mp hsq)
  have hdisp : displacement L M = u - v := by
    ext i
    simp [displacement, u, v]
  have hdist :
      centerDistanceSq L M =
        L.radius ^ 2 + M.radius ^ 2 - 2 * dotPoint u v := by
    have hnorm_sub :
        normSqPoint (u - v) =
          normSqPoint u + normSqPoint v - 2 * dotPoint u v := by
      simp only [normSqPoint, dotPoint, Pi.sub_apply, WithLp.ofLp_sub]
      ring_nf
    rw [centerDistanceSq, hdisp, hnorm_sub, hu, hv]
  rcases hdot_cases with hdot | hdot
  · have hinner_eq :
        centerDistanceSq L M = (L.radius - M.radius) ^ 2 := by
      rw [hdist, hdot]
      ring
    unfold circleInnerMargin at hin
    nlinarith
  · have houter_eq :
        centerDistanceSq L M = (L.radius + M.radius) ^ 2 := by
      rw [hdist, hdot]
      ring
    unfold circleOuterMargin at hout
    nlinarith

private def stemPoint (L : Lollipop) (q : ℝ) : Point :=
  L.center + q • L.unitRadial

private theorem stemPoint_injective (L : Lollipop) :
    Function.Injective (stemPoint L) := by
  intro q₁ q₂ h
  have hsmul : q₁ • L.unitRadial = q₂ • L.unitRadial := by
    have h' := congrArg (fun x : Point => x - L.center) h
    simpa [stemPoint, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h'
  have hvec : (q₁ - q₂) • L.unitRadial = 0 := by
    rw [sub_smul, hsmul, sub_self]
  have hnorm : ‖(q₁ - q₂) • L.unitRadial‖ = 0 := by
    rw [hvec, norm_zero]
  rw [norm_smul, L.norm_unitRadial, mul_one, Real.norm_eq_abs] at hnorm
  exact sub_eq_zero.1 (abs_eq_zero.1 hnorm)

private def acceptedQuadraticRoots (r p δ : ℝ) : Set ℝ :=
  {q | r ≤ q ∧ (q - p) ^ 2 - δ = 0}

private theorem quadratic_root_iff
    {q p δ : ℝ} (hδ : 0 ≤ δ) :
    (q - p) ^ 2 - δ = 0 ↔
      q = p - Real.sqrt δ ∨ q = p + Real.sqrt δ := by
  have hsqrt_sq : (Real.sqrt δ) ^ 2 = δ := Real.sq_sqrt hδ
  have hfac :
      (q - p) ^ 2 - δ =
        (q - (p + Real.sqrt δ)) * (q - (p - Real.sqrt δ)) := by
    conv_lhs => rw [← hsqrt_sq]
    ring
  constructor
  · intro h
    rw [hfac, mul_eq_zero] at h
    rcases h with h | h
    · right
      linarith
    · left
      linarith
  · rintro (rfl | rfl) <;>
      rw [hfac] <;> ring

private theorem acceptedQuadraticRoots_ncard_one
    {r p δ : ℝ}
    (hδ : 0 < δ)
    (hinside : (r - p) ^ 2 - δ < 0) :
    (acceptedQuadraticRoots r p δ).ncard = 1 := by
  have hsqrt_pos : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hsq_lt : (r - p) ^ 2 < (Real.sqrt δ) ^ 2 := by
    rw [Real.sq_sqrt hδ.le]
    linarith
  have hbounds :
      -Real.sqrt δ < r - p ∧ r - p < Real.sqrt δ :=
    abs_lt_of_sq_lt_sq' hsq_lt (Real.sqrt_nonneg δ)
  have hleft_rejected : p - Real.sqrt δ < r := by
    linarith [hbounds.1]
  have hright_accepted : r ≤ p + Real.sqrt δ := by
    linarith [hbounds.2]
  have hset : acceptedQuadraticRoots r p δ = {p + Real.sqrt δ} := by
    ext q
    constructor
    · rintro ⟨hrq, hroot⟩
      rcases (quadratic_root_iff hδ.le).1 hroot with hq | hq
      · exact False.elim (by linarith)
      · simpa [hq]
    · intro hq
      have hq' : q = p + Real.sqrt δ := by simpa using hq
      refine ⟨by simpa [hq'] using hright_accepted, ?_⟩
      exact (quadratic_root_iff hδ.le).2 (Or.inr hq')
  rw [hset]
  simp

private theorem acceptedQuadraticRoots_ncard_two
    {r p δ : ℝ}
    (hδ : 0 < δ)
    (houtside : 0 < (r - p) ^ 2 - δ)
    (hvertex : 0 < p - r) :
    (acceptedQuadraticRoots r p δ).ncard = 2 := by
  have hsqrt_pos : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hsq_lt : (Real.sqrt δ) ^ 2 < (p - r) ^ 2 := by
    rw [Real.sq_sqrt hδ.le]
    nlinarith
  have hsqrt_lt : Real.sqrt δ < p - r := by
    have habs := abs_lt_of_sq_lt_sq hsq_lt (le_of_lt hvertex)
    simpa [abs_of_nonneg (Real.sqrt_nonneg δ)] using habs
  have hleft_accepted : r ≤ p - Real.sqrt δ := by
    linarith
  have hright_accepted : r ≤ p + Real.sqrt δ := by
    linarith [hsqrt_pos]
  have hdistinct : p - Real.sqrt δ ≠ p + Real.sqrt δ := by
    linarith [hsqrt_pos]
  have hset :
      acceptedQuadraticRoots r p δ =
        {p - Real.sqrt δ, p + Real.sqrt δ} := by
    ext q
    constructor
    · rintro ⟨_hrq, hroot⟩
      rcases (quadratic_root_iff hδ.le).1 hroot with hq | hq
      · simp [hq]
      · simp [hq]
    · intro hq
      rcases (by simpa using hq :
          q = p - Real.sqrt δ ∨ q = p + Real.sqrt δ) with hq' | hq'
      · refine ⟨by simpa [hq'] using hleft_accepted, ?_⟩
        exact (quadratic_root_iff hδ.le).2 (Or.inl hq')
      · refine ⟨by simpa [hq'] using hright_accepted, ?_⟩
        exact (quadratic_root_iff hδ.le).2 (Or.inr hq')
  rw [hset]
  simpa [Set.ncard_eq_two, hdistinct]

/-- If the supporting stem line has negative circle discriminant, the accepted
ray--circle primitive is empty. -/
theorem ray_circle_ncard_eq_zero_of_negative_discriminant
    {L M : Lollipop}
    (hquad :
      ∀ q : ℝ,
        normSqPoint (L.center + q • L.unitRadial - M.center) -
            M.radius ^ 2 =
          (q - projectedCenterParameter L M) ^ 2 -
            lineDiscriminant L M)
    (hdisc : lineDiscriminant L M < 0) :
    (rc L M).ncard = 0 := by
  have hempty : rc L M = ∅ := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨hxStem, hxCircle⟩
      have hxStem' : x ∈ L.stemByDistance := by
        simpa using hxStem
      rcases hxStem' with ⟨q, _hq, hxq⟩
      have hzero :
          normSqPoint (L.center + q • L.unitRadial - M.center) -
              M.radius ^ 2 = 0 := by
        rw [← hxq]
        rw [normSqPoint_eq_norm_sq]
        have hcircle : ‖x - M.center‖ = M.radius := by
          simpa [Lollipop.circle] using hxCircle
        rw [hcircle]
        ring
      have hquadq := hquad q
      have hsq : 0 ≤ (q - projectedCenterParameter L M) ^ 2 :=
        sq_nonneg _
      nlinarith
    · intro hx
      simp at hx
  rw [hempty]
  simp

/-- If the anchor is already outside the circle and the quadratic vertex lies
strictly behind the anchor, the accepted ray sees no roots. -/
theorem ray_circle_ncard_eq_zero_of_anchor_positive_vertex_behind
    {L M : Lollipop}
    (hquad :
      ∀ q : ℝ,
        normSqPoint (L.center + q • L.unitRadial - M.center) -
            M.radius ^ 2 =
          (q - projectedCenterParameter L M) ^ 2 -
            lineDiscriminant L M)
    (hanchor :
      anchorPower L M =
        (L.radius - projectedCenterParameter L M) ^ 2 -
          lineDiscriminant L M)
    (hpower : 0 < anchorPower L M)
    (hvertex : vertexAhead L M < 0) :
    (rc L M).ncard = 0 := by
  have hanchor_pos :
      0 <
        (L.radius - projectedCenterParameter L M) ^ 2 -
          lineDiscriminant L M := by
    simpa [hanchor] using hpower
  have hvertex_pos :
      0 < L.radius - projectedCenterParameter L M := by
    simpa [vertexAhead] using neg_pos.2 hvertex
  have hempty : rc L M = ∅ := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨hxStem, hxCircle⟩
      have hxStem' : x ∈ L.stemByDistance := by
        simpa using hxStem
      rcases hxStem' with ⟨q, hq, hxq⟩
      have hzero :
          normSqPoint (L.center + q • L.unitRadial - M.center) -
              M.radius ^ 2 = 0 := by
        rw [← hxq]
        rw [normSqPoint_eq_norm_sq]
        have hcircle : ‖x - M.center‖ = M.radius := by
          simpa [Lollipop.circle] using hxCircle
        rw [hcircle]
        ring
      have hquadq := hquad q
      have hle :
          L.radius - projectedCenterParameter L M ≤
            q - projectedCenterParameter L M := by
        linarith
      have hq_nonneg :
          0 ≤ q - projectedCenterParameter L M :=
        le_trans hvertex_pos.le hle
      have hsqle :
          (L.radius - projectedCenterParameter L M) ^ 2 ≤
            (q - projectedCenterParameter L M) ^ 2 :=
        (sq_le_sq₀ hvertex_pos.le hq_nonneg).2 hle
      nlinarith
    · intro hx
      simp at hx
  rw [hempty]
  simp

private theorem rc_eq_stemPoint_image_acceptedQuadraticRoots
    {L M : Lollipop}
    (hquad :
      ∀ q : ℝ,
        normSqPoint (L.center + q • L.unitRadial - M.center) -
            M.radius ^ 2 =
          (q - projectedCenterParameter L M) ^ 2 -
            lineDiscriminant L M) :
    rc L M =
      stemPoint L ''
        acceptedQuadraticRoots L.radius
          (projectedCenterParameter L M) (lineDiscriminant L M) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxStem, hxCircle⟩
    have hxStem' : x ∈ L.stemByDistance := by
      simpa using hxStem
    rcases hxStem' with ⟨q, hq, hxq⟩
    have hzero :
        normSqPoint (L.center + q • L.unitRadial - M.center) -
            M.radius ^ 2 = 0 := by
      rw [← hxq]
      rw [normSqPoint_eq_norm_sq]
      have hcircle : ‖x - M.center‖ = M.radius := by
        simpa [Lollipop.circle] using hxCircle
      rw [hcircle]
      ring
    refine ⟨q, ⟨hq, ?_⟩, ?_⟩
    · nlinarith [hquad q, hzero]
    · simpa [stemPoint] using hxq.symm
  · rintro ⟨q, hq, rfl⟩
    rcases hq with ⟨hq, hroot⟩
    refine ⟨?_, ?_⟩
    · have hxStem : stemPoint L q ∈ L.stemByDistance :=
        ⟨q, hq, rfl⟩
      simpa [stemPoint] using hxStem
    · have hzero :
          normSqPoint (stemPoint L q - M.center) - M.radius ^ 2 = 0 := by
        have hquadq := hquad q
        simpa [stemPoint, hroot] using hquadq
      have hsq :
          ‖stemPoint L q - M.center‖ ^ 2 = M.radius ^ 2 := by
        rw [← normSqPoint_eq_norm_sq]
        linarith
      have hnorm :
          ‖stemPoint L q - M.center‖ = M.radius :=
        (sq_eq_sq₀ (norm_nonneg _) M.radius_pos.le).1 hsq
      simpa [Lollipop.circle, stemPoint] using hnorm

/-- If the anchor lies inside the circle and the supporting-line discriminant
is positive, exactly the forward root is accepted by the ray. -/
theorem ray_circle_ncard_eq_one_of_anchor_inside
    {L M : Lollipop}
    (hquad :
      ∀ q : ℝ,
        normSqPoint (L.center + q • L.unitRadial - M.center) -
            M.radius ^ 2 =
          (q - projectedCenterParameter L M) ^ 2 -
            lineDiscriminant L M)
    (hanchor :
      anchorPower L M =
        (L.radius - projectedCenterParameter L M) ^ 2 -
          lineDiscriminant L M)
    (hdisc : 0 < lineDiscriminant L M)
    (hpower : anchorPower L M < 0) :
    (rc L M).ncard = 1 := by
  have hinside :
      (L.radius - projectedCenterParameter L M) ^ 2 -
          lineDiscriminant L M < 0 := by
    simpa [hanchor] using hpower
  rw [rc_eq_stemPoint_image_acceptedQuadraticRoots hquad]
  have hinj : Set.InjOn (stemPoint L)
      (acceptedQuadraticRoots L.radius
        (projectedCenterParameter L M) (lineDiscriminant L M)) :=
    (stemPoint_injective L).injOn
  rw [hinj.ncard_image]
  exact acceptedQuadraticRoots_ncard_one hdisc hinside

/-- If the anchor is outside, the discriminant is positive, and the vertex is
strictly ahead of the anchor, both supporting-line roots are accepted. -/
theorem ray_circle_ncard_eq_two_of_anchor_outside_vertex_ahead
    {L M : Lollipop}
    (hquad :
      ∀ q : ℝ,
        normSqPoint (L.center + q • L.unitRadial - M.center) -
            M.radius ^ 2 =
          (q - projectedCenterParameter L M) ^ 2 -
            lineDiscriminant L M)
    (hanchor :
      anchorPower L M =
        (L.radius - projectedCenterParameter L M) ^ 2 -
          lineDiscriminant L M)
    (hdisc : 0 < lineDiscriminant L M)
    (hpower : 0 < anchorPower L M)
    (hvertex : 0 < vertexAhead L M) :
    (rc L M).ncard = 2 := by
  have houtside :
      0 <
        (L.radius - projectedCenterParameter L M) ^ 2 -
          lineDiscriminant L M := by
    simpa [hanchor] using hpower
  have hvertex' :
      0 < projectedCenterParameter L M - L.radius := by
    simpa [vertexAhead] using hvertex
  rw [rc_eq_stemPoint_image_acceptedQuadraticRoots hquad]
  have hinj : Set.InjOn (stemPoint L)
      (acceptedQuadraticRoots L.radius
        (projectedCenterParameter L M) (lineDiscriminant L M)) :=
    (stemPoint_injective L).injOn
  rw [hinj.ncard_image]
  exact acceptedQuadraticRoots_ncard_two hdisc houtside hvertex'

/-- Strict mixed diagnostics classify exactly the accepted roots of the ray
quadratic. -/
theorem mixed_ncard_eq
    (code : MixedCode) {L M : Lollipop}
    (h : code.Realized L M) :
    (rc L M).ncard = code.crossings := by
  cases code with
  | zero =>
      rcases h with hdisc | ⟨hpower, hvertex⟩
      · exact ray_circle_ncard_eq_zero_of_negative_discriminant
          (mixed_quadratic_identity L M) hdisc
      · exact ray_circle_ncard_eq_zero_of_anchor_positive_vertex_behind
          (mixed_quadratic_identity L M)
          (anchorPower_eq_mixed_at_anchor L M)
          hpower hvertex
  | one =>
      exact ray_circle_ncard_eq_one_of_anchor_inside
        (mixed_quadratic_identity L M)
        (anchorPower_eq_mixed_at_anchor L M) h.1 h.2
  | two =>
      exact ray_circle_ncard_eq_two_of_anchor_outside_vertex_ahead
        (mixed_quadratic_identity L M)
        (anchorPower_eq_mixed_at_anchor L M) h.1 h.2.1 h.2.2

/-- Dot product of the actual radial vector with a unit-speed stem parameter. -/
private theorem radial_dot_mixed_parameter
    (L M : Lollipop) (q : ℝ) :
    dotPoint L.radial
        (L.center + q • L.unitRadial - M.center) =
      L.radius * (q - projectedCenterParameter L M) := by
  have huSq : L.unitRadial 0 ^ 2 + L.unitRadial 1 ^ 2 = 1 :=
    point_coord_sq_eq_one_of_norm_eq_one L.norm_unitRadial
  rw [L.radial_eq_radius_smul_unitRadial]
  simp only [dotPoint, projectedCenterParameter, displacement,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, WithLp.ofLp_add,
    WithLp.ofLp_sub, WithLp.ofLp_smul]
  ring_nf
  linear_combination L.radius * q * huSq

/-- Every strict mixed root is transverse.  In the positive-discriminant
cases, a root cannot occur at the quadratic vertex.  In the zero cases, the
strict diagnostics make the primitive empty. -/
theorem ray_circle_transverse_of_strict_discriminant_and_anchor_code
    {code : MixedCode} {L M : Lollipop}
    (hquad :
      ∀ q : ℝ,
        normSqPoint (L.center + q • L.unitRadial - M.center) -
            M.radius ^ 2 =
          (q - projectedCenterParameter L M) ^ 2 -
            lineDiscriminant L M)
    (h : code.Realized L M)
    (x : Point) (hx : x ∈ rc L M) :
    StemCircleTransverseAt L M x := by
  cases code with
  | zero =>
      rcases h with hdisc | ⟨hpower, hvertex⟩
      · have hcard := ray_circle_ncard_eq_zero_of_negative_discriminant
          hquad hdisc
        have hpos : 0 < (rc L M).ncard :=
          (Set.ncard_pos (finite_ray_circle_intersection L M)).2 ⟨x, hx⟩
        rw [hcard] at hpos
        norm_num at hpos
      · have hcard := ray_circle_ncard_eq_zero_of_anchor_positive_vertex_behind
          hquad (anchorPower_eq_mixed_at_anchor L M) hpower hvertex
        have hpos : 0 < (rc L M).ncard :=
          (Set.ncard_pos (finite_ray_circle_intersection L M)).2 ⟨x, hx⟩
        rw [hcard] at hpos
        norm_num at hpos
  | one =>
      rcases hx with ⟨hxStem, hxCircle⟩
      have hxStem' : x ∈ L.stemByDistance := by
        simpa using hxStem
      rcases hxStem' with ⟨q, _hq, hxq⟩
      have hzero :
          normSqPoint (L.center + q • L.unitRadial - M.center) -
              M.radius ^ 2 = 0 := by
        rw [← hxq]
        rw [normSqPoint_eq_norm_sq]
        have hcircle : ‖x - M.center‖ = M.radius := by
          simpa [Lollipop.circle] using hxCircle
        rw [hcircle]
        ring
      have hquadq := hquad q
      have hqp_ne : q - projectedCenterParameter L M ≠ 0 := by
        intro hqp
        nlinarith [h.1]
      have hdot :
          dotPoint L.radial (x - M.center) =
            L.radius * (q - projectedCenterParameter L M) := by
        rw [hxq]
        exact radial_dot_mixed_parameter L M q
      rw [StemCircleTransverseAt, hdot]
      exact mul_ne_zero L.radius_ne_zero hqp_ne
  | two =>
      rcases hx with ⟨hxStem, hxCircle⟩
      have hxStem' : x ∈ L.stemByDistance := by
        simpa using hxStem
      rcases hxStem' with ⟨q, _hq, hxq⟩
      have hzero :
          normSqPoint (L.center + q • L.unitRadial - M.center) -
              M.radius ^ 2 = 0 := by
        rw [← hxq]
        rw [normSqPoint_eq_norm_sq]
        have hcircle : ‖x - M.center‖ = M.radius := by
          simpa [Lollipop.circle] using hxCircle
        rw [hcircle]
        ring
      have hquadq := hquad q
      have hqp_ne : q - projectedCenterParameter L M ≠ 0 := by
        intro hqp
        nlinarith [h.1]
      have hdot :
          dotPoint L.radial (x - M.center) =
            L.radius * (q - projectedCenterParameter L M) := by
        rw [hxq]
        exact radial_dot_mixed_parameter L M q
      rw [StemCircleTransverseAt, hdot]
      exact mul_ne_zero L.radius_ne_zero hqp_ne

/-- Every strict mixed root is transverse. -/
theorem mixed_transverse
    (code : MixedCode) {L M : Lollipop}
    (h : code.Realized L M) :
    ∀ x, x ∈ rc L M → StemCircleTransverseAt L M x := by
  intro x hx
  exact ray_circle_transverse_of_strict_discriminant_and_anchor_code
    (mixed_quadratic_identity L M) h x hx

/-- The true ray--ray chamber is transverse. -/
theorem ray_ray_transverse
    {L M : Lollipop}
    (h : RayRayCodeRealized true L M) : StemStemTransverse L M := by
  have hdir : directionDet L M ≠ 0 := by
    simpa [RayRayCodeRealized] using h.1
  have hscale :
      directionDet L M =
        (L.radius⁻¹ * M.radius⁻¹) * detPoint L.radial M.radial := by
    unfold directionDet Lollipop.unitRadial detPoint
    simp [WithLp.ofLp_smul]
    ring
  intro hzero
  apply hdir
  rw [hscale, hzero]
  ring

/-- Any common point of two nonparallel supporting stem lines has the
displayed Cramer-rule parameters. -/
private theorem line_parameters_of_mem_rr
    {L M : Lollipop} {x : Point}
    (hdet : directionDet L M ≠ 0)
    (hx : x ∈ rr L M) :
    ∃ qL qM : ℝ,
      L.radius ≤ qL ∧ M.radius ≤ qM ∧
      x = L.center + qL • L.unitRadial ∧
      x = M.center + qM • M.unitRadial ∧
      qL = leftLineParameter L M ∧
      qM = rightLineParameter L M := by
  rcases hx with ⟨hxL, hxM⟩
  have hxL' : x ∈ L.stemByDistance := by
    simpa using hxL
  have hxM' : x ∈ M.stemByDistance := by
    simpa using hxM
  rcases hxL' with ⟨qL, hqL, hxLq⟩
  rcases hxM' with ⟨qM, hqM, hxMq⟩
  have hcoord (i : Fin 2) :
      qL * L.unitRadial i - qM * M.unitRadial i =
        displacement L M i := by
    have hxi := congrArg (fun y : Point => y i) (hxLq.symm.trans hxMq)
    simp [displacement] at hxi ⊢
    linarith
  have hleft_num :
      detPoint (displacement L M) M.unitRadial =
        qL * directionDet L M := by
    unfold directionDet
    unfold detPoint
    rw [← hcoord 0, ← hcoord 1]
    ring_nf
  have hright_num :
      detPoint (displacement L M) L.unitRadial =
        qM * directionDet L M := by
    unfold directionDet
    unfold detPoint
    rw [← hcoord 0, ← hcoord 1]
    ring_nf
  refine ⟨qL, qM, hqL, hqM, hxLq, hxMq, ?_, ?_⟩
  · unfold leftLineParameter
    rw [hleft_num]
    field_simp [hdet]
  · unfold rightLineParameter
    rw [hright_num]
    field_simp [hdet]

/-- The false strict ray--ray chamber has no accepted stem--stem point. -/
theorem ray_ray_empty_of_false_strict_code
    {L M : Lollipop}
    (h : RayRayCodeRealized false L M) :
    rr L M = ∅ := by
  simp only [RayRayCodeRealized, if_false] at h
  ext x
  constructor
  · intro hx
    rcases line_parameters_of_mem_rr h.1 hx with
      ⟨qL, qM, hqL, hqM, _hxL, _hxM, hleft, hright⟩
    rcases h.2 with hbehind | hbehind
    · have : qL < L.radius := by simpa [hleft] using hbehind
      exact False.elim (not_lt_of_ge hqL this)
    · have : qM < M.radius := by simpa [hright] using hbehind
      exact False.elim (not_lt_of_ge hqM this)
  · intro hx
    simp at hx

/-- Cardinal form of the false ray--ray chamber. -/
theorem ray_ray_ncard_eq_zero_of_false_strict_code
    {L M : Lollipop}
    (h : RayRayCodeRealized false L M) :
    (rr L M).ncard = 0 := by
  rw [ray_ray_empty_of_false_strict_code h]
  simp

/-- Cramer's rule reconstructs the supporting-line intersection point from
the displayed parameters. -/
private theorem left_right_parameter_equation
    {L M : Lollipop}
    (hdet : directionDet L M ≠ 0) :
    leftLineParameter L M • L.unitRadial -
        rightLineParameter L M • M.unitRadial =
      displacement L M := by
  have hD :
      L.unitRadial 0 * M.unitRadial 1 -
          L.unitRadial 1 * M.unitRadial 0 ≠ 0 := by
    simpa [directionDet, detPoint] using hdet
  have hD' :
      M.unitRadial 1 * L.unitRadial 0 -
          M.unitRadial 0 * L.unitRadial 1 ≠ 0 := by
    convert hD using 1 <;> ring
  ext i <;> fin_cases i
  · simp [leftLineParameter, rightLineParameter, directionDet, detPoint]
    field_simp [hD']
    ring_nf
  · simp [leftLineParameter, rightLineParameter, directionDet, detPoint]
    field_simp [hD']
    ring_nf

/-- Nonparallel supporting lines whose Cramer parameters are both accepted by
the rays have exactly one stem--stem intersection. -/
theorem ray_ray_ncard_eq_one_of_nonparallel_parameters
    {L M : Lollipop}
    (hdet : directionDet L M ≠ 0)
    (hleft : L.radius < leftLineParameter L M)
    (hright : M.radius < rightLineParameter L M) :
    (rr L M).ncard = 1 := by
  let x : Point := L.center + leftLineParameter L M • L.unitRadial
  have hparam := left_right_parameter_equation (L := L) (M := M) hdet
  have hxM_eq :
      x = M.center + rightLineParameter L M • M.unitRadial := by
    ext i
    have hi := congrArg (fun y : Point => y i) hparam
    simp [x, displacement] at hi ⊢
    linarith
  have hx : x ∈ rr L M := by
    refine ⟨?_, ?_⟩
    · have hxL : x ∈ L.stemByDistance :=
        ⟨leftLineParameter L M, le_of_lt hleft, rfl⟩
      simpa using hxL
    · have hxM : x ∈ M.stemByDistance :=
        ⟨rightLineParameter L M, le_of_lt hright, hxM_eq⟩
      simpa using hxM
  have hsingleton : rr L M = {x} := by
    ext y
    constructor
    · intro hy
      rcases line_parameters_of_mem_rr hdet hy with
        ⟨qL, _qM, _hqL, _hqM, hyL, _hyM, hqL, _hqM⟩
      have hyx : y = x := by
        calc
          y = L.center + qL • L.unitRadial := hyL
          _ = L.center + leftLineParameter L M • L.unitRadial := by rw [hqL]
          _ = x := rfl
      simpa [hyx]
    · intro hy
      have hyx : y = x := by simpa using hy
      simpa [hyx] using hx
  rw [hsingleton]
  simp

/-- Nonparallel supporting lines with both parameters beyond the anchors have
exactly one ray--ray point. -/
theorem ray_ray_ncard_eq_one
    {L M : Lollipop}
    (h : RayRayCodeRealized true L M) :
    (rr L M).ncard = 1 := by
  simp only [RayRayCodeRealized, if_true] at h
  exact ray_ray_ncard_eq_one_of_nonparallel_parameters
    h.1 h.2.1 h.2.2

/-- Cardinality of four finite pairwise-disjoint sets.  The finiteness
hypothesis is essential for `Set.ncard`, which is zero on infinite sets. -/
private theorem ncard_union_four_of_pairwiseDisjoint
    {α : Type*} {s : Fin 4 → Set α}
    (hdisj : (Set.univ : Set (Fin 4)).PairwiseDisjoint s)
    (hfin : ∀ i, (s i).Finite) :
    (s 0 ∪ s 1 ∪ s 2 ∪ s 3).ncard =
      (s 0).ncard + (s 1).ncard + (s 2).ncard + (s 3).ncard := by
  have h01 : Disjoint (s 0) (s 1) :=
    hdisj (by simp) (by simp) (by decide)
  have h02 : Disjoint (s 0) (s 2) :=
    hdisj (by simp) (by simp) (by decide)
  have h03 : Disjoint (s 0) (s 3) :=
    hdisj (by simp) (by simp) (by decide)
  have h12 : Disjoint (s 1) (s 2) :=
    hdisj (by simp) (by simp) (by decide)
  have h13 : Disjoint (s 1) (s 3) :=
    hdisj (by simp) (by simp) (by decide)
  have h23 : Disjoint (s 2) (s 3) :=
    hdisj (by simp) (by simp) (by decide)
  have h01_2 : Disjoint (s 0 ∪ s 1) (s 2) := by
    rw [disjoint_left]
    intro x hx hx2
    rcases hx with hx0 | hx1
    · exact (disjoint_left.mp h02) hx0 hx2
    · exact (disjoint_left.mp h12) hx1 hx2
  have h012_3 : Disjoint (s 0 ∪ s 1 ∪ s 2) (s 3) := by
    rw [disjoint_left]
    intro x hx hx3
    rcases hx with hx01 | hx2
    · rcases hx01 with hx0 | hx1
      · exact (disjoint_left.mp h03) hx0 hx3
      · exact (disjoint_left.mp h13) hx1 hx3
    · exact (disjoint_left.mp h23) hx2 hx3
  rw [Set.ncard_union_eq h012_3 (((hfin 0).union (hfin 1)).union (hfin 2)) (hfin 3)]
  rw [Set.ncard_union_eq h01_2 ((hfin 0).union (hfin 1)) (hfin 2)]
  rw [Set.ncard_union_eq h01 (hfin 0) (hfin 1)]

private theorem eq_anchor_of_mem_circle_of_mem_stem
    {L : Lollipop} {x : Point}
    (hcircle : x ∈ L.circle) (hstem : x ∈ L.stem) :
    x = L.anchor := by
  rcases hstem with ⟨t, ht, rfl⟩
  have hnorm :
      ‖t • L.radial‖ = L.radius := by
    simpa [Lollipop.circle, Lollipop.anchor, sub_eq_add_neg,
      add_comm, add_left_comm, add_assoc] using hcircle
  rw [norm_smul, Real.norm_of_nonneg (le_trans zero_le_one ht),
    Lollipop.radius] at hnorm
  have hradial_pos : 0 < ‖L.radial‖ := by
    simpa [Lollipop.radius] using L.radius_pos
  have ht_eq : t = 1 := by
    nlinarith
  simp [Lollipop.anchor, ht_eq]

private theorem anchorPower_eq_zero_of_anchor_mem_circle
    {L M : Lollipop} (hcircle : L.anchor ∈ M.circle) :
    anchorPower L M = 0 := by
  have hnorm : ‖L.anchor - M.center‖ = M.radius := by
    simpa [Lollipop.circle] using hcircle
  unfold anchorPower
  rw [normSqPoint_eq_norm_sq, hnorm]
  ring

private theorem anchorPower_ne_zero_of_mixed_realized
    {code : MixedCode} {L M : Lollipop}
    (h : MixedCode.Realized code L M) :
    anchorPower L M ≠ 0 := by
  cases code
  · simp only [MixedCode.Realized] at h
    rcases h with hdisc | hpos
    · intro hzero
      have hquad := anchorPower_eq_mixed_at_anchor L M
      have hnonneg : 0 ≤ (L.radius - projectedCenterParameter L M) ^ 2 :=
        sq_nonneg _
      nlinarith
    · exact ne_of_gt hpos.1
  · simp only [MixedCode.Realized] at h
    exact ne_of_lt h.2
  · simp only [MixedCode.Realized] at h
    exact ne_of_gt h.2.1

private theorem not_anchor_mem_circle_of_mixed_realized
    {code : MixedCode} {L M : Lollipop}
    (h : MixedCode.Realized code L M) :
    L.anchor ∉ M.circle := by
  intro hcircle
  exact anchorPower_ne_zero_of_mixed_realized h
    (anchorPower_eq_zero_of_anchor_mem_circle hcircle)

private theorem anchor_eq_stemPoint_radius (L : Lollipop) :
    L.anchor = stemPoint L L.radius := by
  simp [stemPoint, Lollipop.anchor, L.radial_eq_radius_smul_unitRadial]

private theorem left_anchor_not_mem_rr_of_true
    {L M : Lollipop} (h : RayRayCodeRealized true L M) :
    L.anchor ∉ rr L M := by
  simp only [RayRayCodeRealized, if_true] at h
  intro hx
  rcases line_parameters_of_mem_rr h.1 hx with
    ⟨qL, _qM, _hqL, _hqM, hxL, _hxM, hqL, _hqM⟩
  have hq : qL = L.radius := by
    apply stemPoint_injective L
    rw [stemPoint, ← hxL, ← anchor_eq_stemPoint_radius L]
  nlinarith

private theorem right_anchor_not_mem_rr_of_true
    {L M : Lollipop} (h : RayRayCodeRealized true L M) :
    M.anchor ∉ rr L M := by
  simp only [RayRayCodeRealized, if_true] at h
  intro hx
  rcases line_parameters_of_mem_rr h.1 hx with
    ⟨_qL, qM, _hqL, _hqM, _hxL, hxM, _hqL', hqM⟩
  have hq : qM = M.radius := by
    apply stemPoint_injective M
    rw [stemPoint, ← hxM, ← anchor_eq_stemPoint_radius M]
  nlinarith

private theorem false_of_mem_cc_and_rc
    {code : MixedCode} {L M : Lollipop}
    (hrc : MixedCode.Realized code L M)
    {x : Point} (hcc : x ∈ cc L M) (hrc_mem : x ∈ rc L M) :
    False := by
  have hxanchor : x = L.anchor :=
    eq_anchor_of_mem_circle_of_mem_stem hcc.1 hrc_mem.1
  have hanchor_circle : L.anchor ∈ M.circle := by
    simpa [hxanchor] using hcc.2
  exact not_anchor_mem_circle_of_mixed_realized hrc hanchor_circle

private theorem false_of_mem_cc_and_cr
    {code : MixedCode} {L M : Lollipop}
    (hcr : MixedCode.Realized code M L)
    {x : Point} (hcc : x ∈ cc L M) (hcr_mem : x ∈ cr L M) :
    False := by
  have hxanchor : x = M.anchor :=
    eq_anchor_of_mem_circle_of_mem_stem hcc.2 hcr_mem.2
  have hanchor_circle : M.anchor ∈ L.circle := by
    simpa [hxanchor] using hcc.1
  exact not_anchor_mem_circle_of_mixed_realized hcr hanchor_circle

private theorem false_of_mem_cc_and_rr
    {b : Bool} {L M : Lollipop}
    (hrr : RayRayCodeRealized b L M)
    {x : Point} (hcc : x ∈ cc L M) (hrr_mem : x ∈ rr L M) :
    False := by
  cases b
  · have hempty := ray_ray_empty_of_false_strict_code hrr
    simpa [hempty] using hrr_mem
  · have hxanchor : x = L.anchor :=
      eq_anchor_of_mem_circle_of_mem_stem hcc.1 hrr_mem.1
    exact left_anchor_not_mem_rr_of_true hrr (by simpa [hxanchor] using hrr_mem)

private theorem false_of_mem_rc_and_cr
    {b : Bool} {L M : Lollipop}
    (hrr : RayRayCodeRealized b L M)
    {x : Point} (hrc_mem : x ∈ rc L M) (hcr_mem : x ∈ cr L M) :
    False := by
  have hrr_mem : x ∈ rr L M := ⟨hrc_mem.1, hcr_mem.2⟩
  cases b
  · have hempty := ray_ray_empty_of_false_strict_code hrr
    simpa [hempty] using hrr_mem
  · have hxanchor : x = L.anchor :=
      eq_anchor_of_mem_circle_of_mem_stem hcr_mem.1 hrc_mem.1
    exact left_anchor_not_mem_rr_of_true hrr (by simpa [hxanchor] using hrr_mem)

private theorem false_of_mem_rc_and_rr
    {b : Bool} {L M : Lollipop}
    (hrr : RayRayCodeRealized b L M)
    {x : Point} (hrc_mem : x ∈ rc L M) (hrr_mem : x ∈ rr L M) :
    False := by
  cases b
  · have hempty := ray_ray_empty_of_false_strict_code hrr
    simpa [hempty] using hrr_mem
  · have hxanchor : x = M.anchor :=
      eq_anchor_of_mem_circle_of_mem_stem hrc_mem.2 hrr_mem.2
    exact right_anchor_not_mem_rr_of_true hrr (by simpa [hxanchor] using hrr_mem)

private theorem false_of_mem_cr_and_rr
    {b : Bool} {L M : Lollipop}
    (hrr : RayRayCodeRealized b L M)
    {x : Point} (hcr_mem : x ∈ cr L M) (hrr_mem : x ∈ rr L M) :
    False := by
  cases b
  · have hempty := ray_ray_empty_of_false_strict_code hrr
    simpa [hempty] using hrr_mem
  · have hxanchor : x = L.anchor :=
      eq_anchor_of_mem_circle_of_mem_stem hcr_mem.1 hrr_mem.1
    exact left_anchor_not_mem_rr_of_true hrr (by simpa [hxanchor] using hrr_mem)

/-- Under strict pair diagnostics, the four primitive crossing sets are
pairwise disjoint.  Anchor coincidences and triple primitive coincidences would
force one of the strict inequalities to become an equality. -/
theorem primitive_pieces_pairwise_disjoint
    {code : StrictPairCode} {L M : Lollipop}
    (h : RealizesStrictPairCode code L M) :
    (Set.univ : Set (Fin 4)).PairwiseDisjoint (fun k : Fin 4 =>
      match k with
      | 0 => cc L M
      | 1 => rc L M
      | 2 => cr L M
      | 3 => rr L M) := by
  rcases h with ⟨_hout, _hin, hrc, hcr, hrr⟩
  rw [Set.pairwiseDisjoint_iff]
  intro i _hi j _hj hnonempty
  rcases hnonempty with ⟨x, hxi, hxj⟩
  fin_cases i <;> fin_cases j <;> simp at hxi hxj ⊢
  · exact false_of_mem_cc_and_rc hrc hxi hxj
  · exact false_of_mem_cc_and_cr hcr hxi hxj
  · exact false_of_mem_cc_and_rr hrr hxi hxj
  · exact false_of_mem_cc_and_rc hrc hxj hxi
  · exact false_of_mem_rc_and_cr hrr hxi hxj
  · exact false_of_mem_rc_and_rr hrr hxi hxj
  · exact false_of_mem_cc_and_cr hcr hxj hxi
  · exact false_of_mem_rc_and_cr hrr hxj hxi
  · exact false_of_mem_cr_and_rr hrr hxi hxj
  · exact false_of_mem_cc_and_rr hrr hxj hxi
  · exact false_of_mem_rc_and_rr hrr hxj hxi
  · exact false_of_mem_cr_and_rr hrr hxj hxi

/-- Exact finite pair crossing count in a strict chamber. -/
theorem pairCrossingCount_eq_code
    {code : StrictPairCode} {L M : Lollipop}
    (h : RealizesStrictPairCode code L M) :
    pairCrossingCount L M = code.crossings := by
  rcases h with ⟨hout, hin, hrc, hcr, hrr⟩
  have hccCard := circle_circle_ncard_eq_two hout hin
  have hrcCard := mixed_ncard_eq code.leftRayRightCircle hrc
  have hcrCard : (cr L M).ncard = code.rightRayLeftCircle.crossings := by
    simpa [cr, rc, inter_comm] using
      mixed_ncard_eq code.rightRayLeftCircle hcr
  have hrrCard : (rr L M).ncard = (if code.rayRay then 1 else 0) := by
    cases hcode : code.rayRay
    · simpa [hcode] using
        ray_ray_ncard_eq_zero_of_false_strict_code (by simpa [hcode] using hrr)
    · simpa [hcode] using
        ray_ray_ncard_eq_one (by simpa [hcode] using hrr)
  have hdisj := primitive_pieces_pairwise_disjoint
    (show RealizesStrictPairCode code L M from ⟨hout, hin, hrc, hcr, hrr⟩)
  have hccFin : (cc L M).Finite := by
    exact Set.finite_of_ncard_ne_zero (by rw [hccCard]; norm_num)
  have hrrFin : (rr L M).Finite := by
    cases hcode : code.rayRay
    · have hempty := ray_ray_empty_of_false_strict_code
        (by simpa [hcode] using hrr)
      rw [hempty]
      exact finite_empty
    · exact Set.finite_of_ncard_ne_zero (by rw [hrrCard]; simp [hcode])
  have hpieceFin : ∀ k : Fin 4,
      (match k with
      | 0 => cc L M
      | 1 => rc L M
      | 2 => cr L M
      | 3 => rr L M).Finite := by
    intro k
    fin_cases k
    · exact hccFin
    · exact finite_ray_circle_intersection L M
    · exact finite_circle_ray_intersection L M
    · exact hrrFin
  rw [pairCrossingCount, pairCrossingSet_decompose,
    ncard_union_four_of_pairwiseDisjoint hdisj hpieceFin,
    hccCard, hrcCard, hcrCard, hrrCard]
  rfl

/-- Primitive pairwise transversality in a strict chamber. -/
theorem pair_transverse
    {code : StrictPairCode} {L M : Lollipop}
    (h : RealizesStrictPairCode code L M) :
    PrimitivePairwiseTransverse L M := by
  rcases h with ⟨hout, hin, hrc, hcr, hrr⟩
  refine ⟨circle_circle_transverse hout hin, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : x ∈ rc M L := by
      simpa [cr, rc, inter_comm] using hx
    simpa [StemCircleTransverseAt] using
      mixed_transverse code.rightRayLeftCircle hcr x hx'
  · exact mixed_transverse code.leftRayRightCircle hrc
  · intro hnon
    cases hcode : code.rayRay
    · have hempty := ray_ray_empty_of_false_strict_code
        (by simpa [hcode] using hrr)
      rcases hnon with ⟨x, hx⟩
      exact False.elim (by simpa [hempty] using hx)
    · exact ray_ray_transverse (by simpa [hcode] using hrr)

end PairChamberPort

/-- Canonical positive similarities preserve every strict pair chamber. -/
theorem realizes_similarityTo_iff
    (Q : Lollipop) (code : StrictPairCode) (L M : Lollipop) :
    RealizesStrictPairCode code ((similarityTo Q).mapLollipop L)
        ((similarityTo Q).mapLollipop M) ↔
      RealizesStrictPairCode code L M :=
  PairChamberPort.realizes_similarityTo_iff Q code L M

/-- Swapping a strict pair chamber. -/
theorem realizes_swap_iff
    (code : StrictPairCode) (L M : Lollipop) :
    RealizesStrictPairCode code L M ↔
      RealizesStrictPairCode code.swap M L := by
  have houter : circleOuterMargin M L = circleOuterMargin L M := by
    unfold circleOuterMargin centerDistanceSq displacement normSqPoint dotPoint
    simp [sub_eq_neg_add, add_comm, add_left_comm, add_assoc]
    ring
  have hinner : circleInnerMargin M L = circleInnerMargin L M := by
    unfold circleInnerMargin centerDistanceSq displacement normSqPoint dotPoint
    simp [sub_eq_neg_add, add_comm, add_left_comm, add_assoc]
    ring
  constructor
  · rintro ⟨hout, hin, hrc, hcr, hrr⟩
    refine ⟨by simpa [houter] using hout, by simpa [hinner] using hin,
      hcr, hrc, ?_⟩
    exact rayRayCodeRealized_swap hrr
  · rintro ⟨hout, hin, hcr, hrc, hrr⟩
    refine ⟨by simpa [houter] using hout, by simpa [hinner] using hin,
      hrc, hcr, ?_⟩
    simpa [StrictPairCode.swap] using rayRayCodeRealized_swap hrr

/-- Exact crossing count exposed outside the port namespace. -/
theorem pairCrossingCount_eq_of_realizes
    {code : StrictPairCode} {L M : Lollipop}
    (h : RealizesStrictPairCode code L M) :
    pairCrossingCount L M = code.crossings :=
  PairChamberPort.pairCrossingCount_eq_code h

theorem pairCrossingSet_finite_of_realizes
    {code : StrictPairCode} {L M : Lollipop}
    (h : RealizesStrictPairCode code L M) :
    (pairCrossingSet L M).Finite := by
  have hcount := pairCrossingCount_eq_of_realizes h
  unfold pairCrossingCount at hcount
  exact Set.finite_of_ncard_ne_zero (by
    rw [hcount]
    exact Nat.ne_of_gt (StrictPairCode.crossings_pos code))

theorem left_anchor_not_mem_pairCrossingSet_of_realizes
    {code : StrictPairCode} {L M : Lollipop}
    (h : RealizesStrictPairCode code L M) :
    L.anchor ∉ pairCrossingSet L M := by
  intro hx
  have hdisj := PairChamberPort.primitive_pieces_pairwise_disjoint h
  rw [Set.pairwiseDisjoint_iff] at hdisj
  rcases hx with ⟨_hL, hM⟩
  rcases hM with hMcircle | hMstem
  · have hcc : L.anchor ∈ cc L M := ⟨L.anchor_mem_circle, hMcircle⟩
    have hrc : L.anchor ∈ rc L M := ⟨L.anchor_mem_stem, hMcircle⟩
    have hidx : (0 : Fin 4) = 1 :=
      hdisj (i := 0) (by simp) (j := 1) (by simp)
        ⟨L.anchor, hcc, hrc⟩
    exact (by decide : (0 : Fin 4) ≠ 1) hidx
  · have hcr : L.anchor ∈ cr L M := ⟨L.anchor_mem_circle, hMstem⟩
    have hrr : L.anchor ∈ rr L M := ⟨L.anchor_mem_stem, hMstem⟩
    have hidx : (2 : Fin 4) = 3 :=
      hdisj (i := 2) (by simp) (j := 3) (by simp)
        ⟨L.anchor, hcr, hrr⟩
    exact (by decide : (2 : Fin 4) ≠ 3) hidx

theorem right_anchor_not_mem_pairCrossingSet_of_realizes
    {code : StrictPairCode} {L M : Lollipop}
    (h : RealizesStrictPairCode code L M) :
    M.anchor ∉ pairCrossingSet L M := by
  intro hx
  have hdisj := PairChamberPort.primitive_pieces_pairwise_disjoint h
  rw [Set.pairwiseDisjoint_iff] at hdisj
  rcases hx with ⟨hL, _hM⟩
  rcases hL with hLcircle | hLstem
  · have hcc : M.anchor ∈ cc L M := ⟨hLcircle, M.anchor_mem_circle⟩
    have hcr : M.anchor ∈ cr L M := ⟨hLcircle, M.anchor_mem_stem⟩
    have hidx : (0 : Fin 4) = 2 :=
      hdisj (i := 0) (by simp) (j := 2) (by simp)
        ⟨M.anchor, hcc, hcr⟩
    exact (by decide : (0 : Fin 4) ≠ 2) hidx
  · have hrc : M.anchor ∈ rc L M := ⟨hLstem, M.anchor_mem_circle⟩
    have hrr : M.anchor ∈ rr L M := ⟨hLstem, M.anchor_mem_stem⟩
    have hidx : (1 : Fin 4) = 3 :=
      hdisj (i := 1) (by simp) (j := 3) (by simp)
        ⟨M.anchor, hrc, hrr⟩
    exact (by decide : (1 : Fin 4) ≠ 3) hidx

/-- Transversality exposed outside the port namespace. -/
theorem primitivePairwiseTransverse_of_realizes
    {code : StrictPairCode} {L M : Lollipop}
    (h : RealizesStrictPairCode code L M) :
    PrimitivePairwiseTransverse L M :=
  PairChamberPort.pair_transverse h

/-- A strict chamber is open in the product parameter space of pairs of
lollipops. -/
theorem isOpen_realizesStrictPairCode (code : StrictPairCode) :
    IsOpen (strictPairChamberSet code) := by
  have houter : IsOpen {p : Lollipop × Lollipop |
      0 < circleOuterMargin p.1 p.2} :=
    isOpen_lt continuous_const continuous_circleOuterMargin_pair
  have hinner : IsOpen {p : Lollipop × Lollipop |
      0 < circleInnerMargin p.1 p.2} :=
    isOpen_lt continuous_const continuous_circleInnerMargin_pair
  have hleft := isOpen_mixedCodeRealized code.leftRayRightCircle
  have hright := isOpen_mixedCodeRealized_swap code.rightRayLeftCircle
  have hrr := isOpen_rayRayCodeRealized code.rayRay
  exact houter.inter (hinner.inter (hleft.inter (hright.inter hrr)))

/-- Pointwise chamber stability in a convenient neighborhood form. -/
theorem exists_pair_chamber_neighborhood
    {code : StrictPairCode} {L M : Lollipop}
    (h : RealizesStrictPairCode code L M) :
    ∃ U V : Set Lollipop,
      IsOpen U ∧ IsOpen V ∧ L ∈ U ∧ M ∈ V ∧
      ∀ L' ∈ U, ∀ M' ∈ V, RealizesStrictPairCode code L' M' := by
  have hopen := isOpen_realizesStrictPairCode code
  have hp : (L, M) ∈ strictPairChamberSet code := h
  rcases isOpen_prod_iff.mp hopen L M hp with
    ⟨U, V, hU, hV, hLU, hMV, hsub⟩
  exact ⟨U, V, hU, hV, hLU, hMV, by
    intro L' hL' M' hM'
    exact hsub ⟨hL', hM'⟩⟩

end Lower
end EndToEnd
end Concrete
end Lollipop

/-!
The manuscript-facing proposition is repeated here as `CoreStatement` so
this proof module does not cyclically import its public statement module.
`Statement.lean` imports this file and exposes the same expression under the
public name `Statement`.
-/

/-!
Manuscript Lemma 8.2 (`lem:chamber`): a realized strict pair code persists on
an open product neighborhood.
-/

namespace Lollipop.Manuscript.Lemma_8_2

open Concrete Concrete.EndToEnd Concrete.EndToEnd.Lower

abbrev CoreStatement (code : StrictPairCode) (L M : Concrete.Lollipop) : Prop :=
  RealizesStrictPairCode code L M ->
    exists U V : Set Concrete.Lollipop,
      IsOpen U /\ IsOpen V /\ L ∈ U /\ M ∈ V /\
      ∀ L' ∈ U, ∀ M' ∈ V, RealizesStrictPairCode code L' M'

end Lollipop.Manuscript.Lemma_8_2

/-! The actual numbered proof. -/

namespace Lollipop.Manuscript.Lemma_8_2

open Concrete Concrete.EndToEnd Concrete.EndToEnd.Lower

theorem proof (code : StrictPairCode) (L M : Concrete.Lollipop) :
    CoreStatement code L M := by
  intro h
  exact exists_pair_chamber_neighborhood h

end Lollipop.Manuscript.Lemma_8_2
