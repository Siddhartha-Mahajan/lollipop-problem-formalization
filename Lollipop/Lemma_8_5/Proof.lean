import Lollipop.Lemma_8_4.Proof
import Lollipop.Proposition_2_1.Proof
import Lollipop.Theorem_4_1.Proof
import Mathlib.Data.Set.Card
import Mathlib.Tactic

/-!
This is the substantive proof compilation unit for `Lemma_8_5`.
All project proof components used below are integrated here or imported
directly from another manuscript-numbered `Proof.lean` file.
-/

/-!
Proof component 1: `Manuscript.PrimitiveGeometry.ComponentBounds`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Finite component bounds for primitive lollipop carrier intersections.

`SphereBridge` proves the geometric uniqueness facts: two circles have at most
two common points, a ray-supporting line and a circle have at most two common
points, and two noncoincident ray-supporting lines have at most one common
ray-ray point.  This file turns those set-level facts into reusable finite
cardinality bounds for carrier-intersection witnesses.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace PrimitiveGeometry

open TheoremOneEndToEnd.PaulsenLinearAlgebra

/-- A finite subset of a circle-circle component has at most two points when
the two lifted circles are distinct. -/
theorem finset_card_le_two_of_forall_mem_euclideanCircleCircleSet
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (S : Finset EuclideanR2)
    (hS : ∀ p ∈ S, p ∈ euclideanCircleCircleSet L M) :
    S.card ≤ 2 := by
  by_contra hle
  have hgt : 2 < S.card := Nat.lt_of_not_ge hle
  rcases Finset.two_lt_card.1 hgt with
    ⟨p₁, hp₁S, p₂, hp₂S, p, hpS, hp₁₂, hp₁p, hp₂p⟩
  rcases eq_or_eq_of_mem_euclideanCircleCircleSet_of_two_witnesses
      hLM hp₁₂ (hS p₁ hp₁S) (hS p₂ hp₂S) (hS p hpS) with hp_eq | hp_eq
  · exact hp₁p hp_eq.symm
  · exact hp₂p hp_eq.symm

/-- A finite subset of a circle-ray component has at most two points. -/
theorem finset_card_le_two_of_forall_mem_euclideanCircleRaySet
    {L M : EuclideanLollipop}
    (S : Finset EuclideanR2)
    (hS : ∀ p ∈ S, p ∈ euclideanCircleRaySet L M) :
    S.card ≤ 2 := by
  by_contra hle
  have hgt : 2 < S.card := Nat.lt_of_not_ge hle
  rcases Finset.two_lt_card.1 hgt with
    ⟨p₁, hp₁S, p₂, hp₂S, p, hpS, hp₁₂, hp₁p, hp₂p⟩
  rcases eq_or_eq_of_mem_euclideanCircleRaySet_of_two_witnesses
      hp₁₂ (hS p₁ hp₁S) (hS p₂ hp₂S) (hS p hpS) with hp_eq | hp_eq
  · exact hp₁p hp_eq.symm
  · exact hp₂p hp_eq.symm

/-- A finite subset of a ray-circle component has at most two points. -/
theorem finset_card_le_two_of_forall_mem_euclideanRayCircleSet
    {L M : EuclideanLollipop}
    (S : Finset EuclideanR2)
    (hS : ∀ p ∈ S, p ∈ euclideanRayCircleSet L M) :
    S.card ≤ 2 := by
  by_contra hle
  have hgt : 2 < S.card := Nat.lt_of_not_ge hle
  rcases Finset.two_lt_card.1 hgt with
    ⟨p₁, hp₁S, p₂, hp₂S, p, hpS, hp₁₂, hp₁p, hp₂p⟩
  rcases eq_or_eq_of_mem_euclideanRayCircleSet_of_two_witnesses
      hp₁₂ (hS p₁ hp₁S) (hS p₂ hp₂S) (hS p hpS) with hp_eq | hp_eq
  · exact hp₁p hp_eq.symm
  · exact hp₂p hp_eq.symm

/-- A finite subset of a ray-ray component has at most one point when the
supporting ray lines are distinct. -/
theorem finset_card_le_one_of_forall_mem_euclideanRayRaySet
    {L M : EuclideanLollipop}
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    (S : Finset EuclideanR2)
    (hS : ∀ p ∈ S, p ∈ euclideanRayRaySet L M) :
    S.card ≤ 1 := by
  rw [Finset.card_le_one]
  intro p₁ hp₁S p₂ hp₂S
  exact eq_of_mem_euclideanRayRaySet_of_rayLine_ne hline
    (hS p₁ hp₁S) (hS p₂ hp₂S)

/-- A finite subset of a lifted pair-intersection carrier has at most seven
points under the generic noncoincidence hypotheses for the two circles and
the two ray-supporting lines. -/
theorem finset_card_le_seven_of_forall_mem_euclideanPairIntersectionSet
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    (S : Finset EuclideanR2)
    (hS : ∀ p ∈ S, p ∈ euclideanPairIntersectionSet L M) :
    S.card ≤ 7 := by
  classical
  let cc : Finset EuclideanR2 :=
    S.filter fun p => p ∈ euclideanCircleCircleSet L M
  let cr : Finset EuclideanR2 :=
    S.filter fun p => p ∈ euclideanCircleRaySet L M
  let rc : Finset EuclideanR2 :=
    S.filter fun p => p ∈ euclideanRayCircleSet L M
  let rr : Finset EuclideanR2 :=
    S.filter fun p => p ∈ euclideanRayRaySet L M
  let u12 : Finset EuclideanR2 := cc ∪ cr
  let u123 : Finset EuclideanR2 := u12 ∪ rc
  let uall : Finset EuclideanR2 := u123 ∪ rr
  have hcover : S ⊆ uall := by
    intro p hpS
    rcases (mem_euclideanPairIntersectionSet_iff.1 (hS p hpS)) with
      hcc | hcr | hrc | hrr
    · simp [uall, u123, u12, cc, hpS, hcc]
    · simp [uall, u123, u12, cr, hpS, hcr]
    · simp [uall, u123, rc, hpS, hrc]
    · simp [uall, rr, hpS, hrr]
  have hccard : cc.card ≤ 2 :=
    finset_card_le_two_of_forall_mem_euclideanCircleCircleSet hLM cc
      (by
        intro p hp
        exact (Finset.mem_filter.1 hp).2)
  have hcrcard : cr.card ≤ 2 :=
    finset_card_le_two_of_forall_mem_euclideanCircleRaySet cr
      (by
        intro p hp
        exact (Finset.mem_filter.1 hp).2)
  have hrccard : rc.card ≤ 2 :=
    finset_card_le_two_of_forall_mem_euclideanRayCircleSet rc
      (by
        intro p hp
        exact (Finset.mem_filter.1 hp).2)
  have hrrcard : rr.card ≤ 1 :=
    finset_card_le_one_of_forall_mem_euclideanRayRaySet hline rr
      (by
        intro p hp
        exact (Finset.mem_filter.1 hp).2)
  have hSle : S.card ≤ uall.card := Finset.card_le_card hcover
  have huall : uall.card ≤ u123.card + rr.card :=
    Finset.card_union_le u123 rr
  have hu123 : u123.card ≤ u12.card + rc.card :=
    Finset.card_union_le u12 rc
  have hu12 : u12.card ≤ cc.card + cr.card :=
    Finset.card_union_le cc cr
  omega

/-- Lift a primitive finite crossing witness to the mathlib Euclidean plane. -/
noncomputable def liftedCrossingFinset (S : Finset R2) : Finset EuclideanR2 :=
  S.image toEuclideanR2

@[simp]
theorem liftedCrossingFinset_card (S : Finset R2) :
    (liftedCrossingFinset S).card = S.card := by
  classical
  exact Finset.card_image_of_injective S toEuclideanR2_injective

/-- The lifted finite carrier-crossing witness has at most seven points under
the generic noncoincidence hypotheses. -/
theorem pairwiseCarrierCrossingData_lifted_card_le_seven
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat}
    (D : PairwiseCarrierCrossingData A cross)
    {i j : Fin n} (hij : i < j)
    (hLM :
      euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
        euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      euclideanRayLine (A.lollipop i) ≠ euclideanRayLine (A.lollipop j)) :
    (liftedCrossingFinset (D.crossingPoints i j hij)).card ≤ 7 := by
  classical
  refine finset_card_le_seven_of_forall_mem_euclideanPairIntersectionSet
    hLM hline (liftedCrossingFinset (D.crossingPoints i j hij)) ?_
  intro p hp
  rcases Finset.mem_image.1 hp with ⟨x, hxS, rfl⟩
  have hx_pair : x ∈ A.pairIntersectionSet i j := by
    have hset := D.crossingPoints_spec i j hij
    have hx_finset : x ∈ ((D.crossingPoints i j hij : Finset R2) : Set R2) := by
      simpa using hxS
    simpa [hset] using hx_finset
  have hx_preimage :
      x ∈ {x : R2 |
        toEuclideanR2 x ∈
          euclideanPairIntersectionSet (A.lollipop i) (A.lollipop j)} := by
    have hx_pair' :
        x ∈ pairIntersectionSet (A.lollipop i) (A.lollipop j) := by
      simpa [EuclideanLollipopArrangement.pairIntersectionSet] using hx_pair
    have hpre :=
      pairIntersectionSet_eq_preimage_euclideanPairIntersectionSet
        (A.lollipop i) (A.lollipop j)
    simpa [hpre] using hx_pair'
  simpa using hx_preimage

/-- In the same generic noncoincident setting, the primitive finite
carrier-crossing table entry is at most seven. -/
theorem pairwiseCarrierCrossingData_cross_le_seven
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat}
    (D : PairwiseCarrierCrossingData A cross)
    {i j : Fin n} (hij : i < j)
    (hLM :
      euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
        euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      euclideanRayLine (A.lollipop i) ≠ euclideanRayLine (A.lollipop j)) :
    cross i j ≤ 7 := by
  have hcard :=
    pairwiseCarrierCrossingData_lifted_card_le_seven D hij hLM hline
  have hprimitive_card : (D.crossingPoints i j hij).card ≤ 7 := by
    simpa using hcard
  rw [D.cross_eq_card i j hij]
  exact_mod_cast hprimitive_card

/-- Local one-pair finite carrier-crossing witnesses have at most seven points
under the generic noncoincidence hypotheses. -/
theorem localPairCarrierCrossingData_lifted_card_le_seven
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
    (D : LocalPairCarrierCrossingData A cross i j hij)
    (hLM :
      euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
        euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      euclideanRayLine (A.lollipop i) ≠ euclideanRayLine (A.lollipop j)) :
    (liftedCrossingFinset D.crossingPoints).card ≤ 7 := by
  classical
  refine finset_card_le_seven_of_forall_mem_euclideanPairIntersectionSet
    hLM hline (liftedCrossingFinset D.crossingPoints) ?_
  intro p hp
  rcases Finset.mem_image.1 hp with ⟨x, hxS, rfl⟩
  have hx_pair : x ∈ A.pairIntersectionSet i j := by
    have hset := D.crossingPoints_spec
    have hx_finset : x ∈ ((D.crossingPoints : Finset R2) : Set R2) := by
      simpa using hxS
    simpa [hset] using hx_finset
  have hx_pair' :
      x ∈ pairIntersectionSet (A.lollipop i) (A.lollipop j) := by
    simpa [EuclideanLollipopArrangement.pairIntersectionSet] using hx_pair
  have hpre :=
    pairIntersectionSet_eq_preimage_euclideanPairIntersectionSet
      (A.lollipop i) (A.lollipop j)
  have hx_preimage :
      x ∈ {x : R2 |
        toEuclideanR2 x ∈
          euclideanPairIntersectionSet (A.lollipop i) (A.lollipop j)} := by
    simpa [hpre] using hx_pair'
  simpa using hx_preimage

/-- Local one-pair finite carrier-crossing witnesses imply the generic
`<= 7` rational crossing-table bound. -/
theorem localPairCarrierCrossingData_cross_le_seven
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
    (D : LocalPairCarrierCrossingData A cross i j hij)
    (hLM :
      euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
        euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      euclideanRayLine (A.lollipop i) ≠ euclideanRayLine (A.lollipop j)) :
    cross i j ≤ 7 := by
  have hcard :=
    localPairCarrierCrossingData_lifted_card_le_seven D hLM hline
  have hprimitive_card : D.crossingPoints.card ≤ 7 := by
    simpa using hcard
  rw [D.cross_eq_card]
  exact_mod_cast hprimitive_card

/-- Component-wise finite-cardinality savings for one pair of primitive
lollipops.  The four component caps are deliberately explicit: this is the
interface where a future Euclidean close/intriguing proof can say exactly
which circle/ray component loses crossings. -/
structure PairComponentSavings
    (L M : EuclideanLollipop) (bound : Nat) where
  circleCircleBound : Nat
  circleRayBound : Nat
  rayCircleBound : Nat
  rayRayBound : Nat
  total_le :
    circleCircleBound + circleRayBound + rayCircleBound + rayRayBound ≤ bound
  circleCircle_card_le :
    ∀ S : Finset EuclideanR2,
      (∀ p ∈ S, p ∈ euclideanCircleCircleSet L M) →
        S.card ≤ circleCircleBound
  circleRay_card_le :
    ∀ S : Finset EuclideanR2,
      (∀ p ∈ S, p ∈ euclideanCircleRaySet L M) →
        S.card ≤ circleRayBound
  rayCircle_card_le :
    ∀ S : Finset EuclideanR2,
      (∀ p ∈ S, p ∈ euclideanRayCircleSet L M) →
        S.card ≤ rayCircleBound
  rayRay_card_le :
    ∀ S : Finset EuclideanR2,
      (∀ p ∈ S, p ∈ euclideanRayRaySet L M) →
        S.card ≤ rayRayBound

/-- An empty component contributes no points to any finite witness. -/
theorem finset_card_le_zero_of_forall_mem_of_component_empty
    {s : Set EuclideanR2}
    (hempty : ∀ p : EuclideanR2, p ∉ s)
    (S : Finset EuclideanR2)
    (hS : ∀ p ∈ S, p ∈ s) :
    S.card ≤ 0 := by
  by_contra hle
  have hpos : 0 < S.card := Nat.lt_of_not_ge hle
  rcases Finset.card_pos.1 hpos with ⟨p, hp⟩
  exact hempty p (hS p hp)

/-- Build component savings from four component finite-cardinality caps. -/
def pairComponentSavingsOfComponentBounds
    {L M : EuclideanLollipop} {bound : Nat}
    (circleCircleBound circleRayBound rayCircleBound rayRayBound : Nat)
    (htotal :
      circleCircleBound + circleRayBound + rayCircleBound + rayRayBound ≤
        bound)
    (hcc :
      ∀ S : Finset EuclideanR2,
        (∀ p ∈ S, p ∈ euclideanCircleCircleSet L M) →
          S.card ≤ circleCircleBound)
    (hcr :
      ∀ S : Finset EuclideanR2,
        (∀ p ∈ S, p ∈ euclideanCircleRaySet L M) →
          S.card ≤ circleRayBound)
    (hrc :
      ∀ S : Finset EuclideanR2,
        (∀ p ∈ S, p ∈ euclideanRayCircleSet L M) →
          S.card ≤ rayCircleBound)
    (hrr :
      ∀ S : Finset EuclideanR2,
        (∀ p ∈ S, p ∈ euclideanRayRaySet L M) →
          S.card ≤ rayRayBound) :
    PairComponentSavings L M bound where
  circleCircleBound := circleCircleBound
  circleRayBound := circleRayBound
  rayCircleBound := rayCircleBound
  rayRayBound := rayRayBound
  total_le := htotal
  circleCircle_card_le := hcc
  circleRay_card_le := hcr
  rayCircle_card_le := hrc
  rayRay_card_le := hrr

/-- The generic component caps also form a `PairComponentSavings` witness with
bound `7`. -/
def pairComponentSavingsGenericSeven
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M) :
    PairComponentSavings L M 7 :=
  pairComponentSavingsOfComponentBounds
    2 2 2 1 (by norm_num)
    (finset_card_le_two_of_forall_mem_euclideanCircleCircleSet hLM)
    finset_card_le_two_of_forall_mem_euclideanCircleRaySet
    finset_card_le_two_of_forall_mem_euclideanRayCircleSet
    (finset_card_le_one_of_forall_mem_euclideanRayRaySet hline)

/-- If the circle-circle component is empty, the generic component caps improve
to a `<= 5` savings certificate. -/
def pairComponentSavingsFiveOfCircleCircleEmpty
    {L M : EuclideanLollipop}
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    (hcc_empty : ∀ p : EuclideanR2,
      p ∉ euclideanCircleCircleSet L M) :
    PairComponentSavings L M 5 :=
  pairComponentSavingsOfComponentBounds
    0 2 2 1 (by norm_num)
    (finset_card_le_zero_of_forall_mem_of_component_empty hcc_empty)
    finset_card_le_two_of_forall_mem_euclideanCircleRaySet
    finset_card_le_two_of_forall_mem_euclideanRayCircleSet
    (finset_card_le_one_of_forall_mem_euclideanRayRaySet hline)

/-- Far-apart circle centers give a `<= 5` savings certificate by making the
circle-circle component empty. -/
def pairComponentSavingsFiveOfCircleCircleFarApart
    {L M : EuclideanLollipop}
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    (hfar :
      L.radius + M.radius <
        dist (toEuclideanR2 L.center) (toEuclideanR2 M.center)) :
    PairComponentSavings L M 5 :=
  pairComponentSavingsFiveOfCircleCircleEmpty hline
    (euclideanCircleCircleSet_empty_of_radius_add_lt_dist hfar)

/-- Squared-coordinate far-apart criterion for the same `<= 5`
component-savings certificate. -/
def pairComponentSavingsFiveOfCircleCircleFarApartSq
    {L M : EuclideanLollipop}
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    (hfar :
      (L.radius + M.radius) ^ 2 < distSq2 L.center M.center) :
    PairComponentSavings L M 5 :=
  pairComponentSavingsFiveOfCircleCircleEmpty hline
    (euclideanCircleCircleSet_empty_of_radius_add_sq_lt_distSq2 hfar)

/-- Strict containment of one circle in the other gives a `<= 5` savings
certificate by making the circle-circle component empty. -/
def pairComponentSavingsFiveOfCircleCircleContainedLeft
    {L M : EuclideanLollipop}
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    (hcontained :
      dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) + L.radius <
        M.radius) :
    PairComponentSavings L M 5 :=
  pairComponentSavingsFiveOfCircleCircleEmpty hline
    (euclideanCircleCircleSet_empty_of_dist_add_left_radius_lt_right_radius
      hcontained)

/-- Symmetric strict-containment constructor for `<= 5` component savings. -/
def pairComponentSavingsFiveOfCircleCircleContainedRight
    {L M : EuclideanLollipop}
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    (hcontained :
      dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) + M.radius <
        L.radius) :
    PairComponentSavings L M 5 :=
  pairComponentSavingsFiveOfCircleCircleEmpty hline
    (euclideanCircleCircleSet_empty_of_dist_add_right_radius_lt_left_radius
      hcontained)

/-- Squared-coordinate strict-containment constructor with `L` inside `M`. -/
def pairComponentSavingsFiveOfCircleCircleContainedLeftSq
    {L M : EuclideanLollipop}
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    (hradius : L.radius < M.radius)
    (hcontained :
      distSq2 L.center M.center < (M.radius - L.radius) ^ 2) :
    PairComponentSavings L M 5 :=
  pairComponentSavingsFiveOfCircleCircleEmpty hline
    (euclideanCircleCircleSet_empty_of_distSq2_lt_right_sub_left_radius_sq
      hradius hcontained)

/-- Squared-coordinate strict-containment constructor with `M` inside `L`. -/
def pairComponentSavingsFiveOfCircleCircleContainedRightSq
    {L M : EuclideanLollipop}
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    (hradius : M.radius < L.radius)
    (hcontained :
      distSq2 L.center M.center < (L.radius - M.radius) ^ 2) :
    PairComponentSavings L M 5 :=
  pairComponentSavingsFiveOfCircleCircleEmpty hline
    (euclideanCircleCircleSet_empty_of_distSq2_lt_left_sub_right_radius_sq
      hradius hcontained)

/-- Any concrete no-meet certificate for the two circles gives a `<= 5`
component-savings certificate. -/
def pairComponentSavingsFiveOfCircleCircleNoMeet
    {L M : EuclideanLollipop}
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    (D : CircleCircleNoMeetData L M) :
    PairComponentSavings L M 5 :=
  pairComponentSavingsFiveOfCircleCircleEmpty hline D.empty

/-- If the circle-ray component is empty, the generic component caps improve
to a `<= 5` savings certificate. -/
def pairComponentSavingsFiveOfCircleRayEmpty
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    (hcr_empty : ∀ p : EuclideanR2,
      p ∉ euclideanCircleRaySet L M) :
    PairComponentSavings L M 5 :=
  pairComponentSavingsOfComponentBounds
    2 0 2 1 (by norm_num)
    (finset_card_le_two_of_forall_mem_euclideanCircleCircleSet hLM)
    (finset_card_le_zero_of_forall_mem_of_component_empty hcr_empty)
    finset_card_le_two_of_forall_mem_euclideanRayCircleSet
    (finset_card_le_one_of_forall_mem_euclideanRayRaySet hline)

/-- A line-separation certificate for an empty circle-ray component gives a
`<= 5` component-savings certificate. -/
def pairComponentSavingsFiveOfCircleRayNoMeet
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    (D : CircleRayNoMeetData L M) :
    PairComponentSavings L M 5 :=
  pairComponentSavingsFiveOfCircleRayEmpty hLM hline D.empty

/-- Projection-distance criterion for the empty circle-ray component. -/
noncomputable def pairComponentSavingsFiveOfCircleRayProjectionSeparated
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    (hsep :
      L.radius <
        dist (toEuclideanR2 L.center)
          (euclideanRayLineProjection M (toEuclideanR2 L.center))) :
    PairComponentSavings L M 5 :=
  pairComponentSavingsFiveOfCircleRayNoMeet hLM hline
    (CircleRayNoMeetData.of_rayLineProjection hsep)

/-- Determinant/Cauchy criterion for the empty circle-ray component. -/
def pairComponentSavingsFiveOfCircleRayDetSeparated
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    (hsep :
      L.radius ^ 2 * normSq2 M.rayDirection <
        det2 (M.anchor - L.center) M.rayDirection ^ 2) :
    PairComponentSavings L M 5 :=
  pairComponentSavingsFiveOfCircleRayEmpty hLM hline
    (euclideanCircleRaySet_empty_of_radius_sq_mul_normSq2_lt_det2_sq hsep)

/-- Half-line orientation criterion for the empty circle-ray component.  The
ray anchor starts outside the circle and the ray points weakly away from the
circle center. -/
def pairComponentSavingsFiveOfCircleRayOutward
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    (hanchor : L.radius ^ 2 < distSq2 M.anchor L.center)
    (hdot : 0 ≤ dot2 (M.anchor - L.center) M.rayDirection) :
    PairComponentSavings L M 5 :=
  pairComponentSavingsFiveOfCircleRayEmpty hLM hline
    (euclideanCircleRaySet_empty_of_radius_sq_lt_anchor_distSq2_of_dot_nonneg
      hanchor hdot)

/-- If the ray-circle component is empty, the generic component caps improve
to a `<= 5` savings certificate. -/
def pairComponentSavingsFiveOfRayCircleEmpty
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    (hrc_empty : ∀ p : EuclideanR2,
      p ∉ euclideanRayCircleSet L M) :
    PairComponentSavings L M 5 :=
  pairComponentSavingsOfComponentBounds
    2 2 0 1 (by norm_num)
    (finset_card_le_two_of_forall_mem_euclideanCircleCircleSet hLM)
    finset_card_le_two_of_forall_mem_euclideanCircleRaySet
    (finset_card_le_zero_of_forall_mem_of_component_empty hrc_empty)
    (finset_card_le_one_of_forall_mem_euclideanRayRaySet hline)

/-- A line-separation certificate for an empty ray-circle component gives a
`<= 5` component-savings certificate. -/
def pairComponentSavingsFiveOfRayCircleNoMeet
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    (D : RayCircleNoMeetData L M) :
    PairComponentSavings L M 5 :=
  pairComponentSavingsFiveOfRayCircleEmpty hLM hline D.empty

/-- Projection-distance criterion for the empty ray-circle component. -/
noncomputable def pairComponentSavingsFiveOfRayCircleProjectionSeparated
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    (hsep :
      M.radius <
        dist (toEuclideanR2 M.center)
          (euclideanRayLineProjection L (toEuclideanR2 M.center))) :
    PairComponentSavings L M 5 :=
  pairComponentSavingsFiveOfRayCircleNoMeet hLM hline
    (RayCircleNoMeetData.of_rayLineProjection hsep)

/-- Determinant/Cauchy criterion for the empty ray-circle component. -/
def pairComponentSavingsFiveOfRayCircleDetSeparated
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    (hsep :
      M.radius ^ 2 * normSq2 L.rayDirection <
        det2 (L.anchor - M.center) L.rayDirection ^ 2) :
    PairComponentSavings L M 5 :=
  pairComponentSavingsFiveOfRayCircleEmpty hLM hline
    (euclideanRayCircleSet_empty_of_radius_sq_mul_normSq2_lt_det2_sq hsep)

/-- Half-line orientation criterion for the empty ray-circle component. -/
def pairComponentSavingsFiveOfRayCircleOutward
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    (hanchor : M.radius ^ 2 < distSq2 L.anchor M.center)
    (hdot : 0 ≤ dot2 (L.anchor - M.center) L.rayDirection) :
    PairComponentSavings L M 5 :=
  pairComponentSavingsFiveOfRayCircleEmpty hLM hline
    (euclideanRayCircleSet_empty_of_radius_sq_lt_anchor_distSq2_of_dot_nonneg
      hanchor hdot)

/-- Empty circle-circle and ray-ray components give the `<= 4` savings needed
for pairs that are both close and intriguing. -/
def pairComponentSavingsFourOfCircleCircleAndRayRayEmpty
    {L M : EuclideanLollipop}
    (hcc_empty : ∀ p : EuclideanR2,
      p ∉ euclideanCircleCircleSet L M)
    (hrr_empty : ∀ p : EuclideanR2,
      p ∉ euclideanRayRaySet L M) :
    PairComponentSavings L M 4 :=
  pairComponentSavingsOfComponentBounds
    0 2 2 0 (by norm_num)
    (finset_card_le_zero_of_forall_mem_of_component_empty hcc_empty)
    finset_card_le_two_of_forall_mem_euclideanCircleRaySet
    finset_card_le_two_of_forall_mem_euclideanRayCircleSet
    (finset_card_le_zero_of_forall_mem_of_component_empty hrr_empty)

/-- Empty circle-circle component plus the determinant/parallel criterion for
an empty ray-ray component gives the `<= 4` branch. -/
def pairComponentSavingsFourOfCircleCircleEmptyAndRayRayDetSeparated
    {L M : EuclideanLollipop}
    (hcc_empty : ∀ p : EuclideanR2,
      p ∉ euclideanCircleCircleSet L M)
    (hparallel : det2 L.rayDirection M.rayDirection = 0)
    (hoffset : det2 (M.anchor - L.anchor) L.rayDirection ≠ 0) :
    PairComponentSavings L M 4 :=
  pairComponentSavingsFourOfCircleCircleAndRayRayEmpty hcc_empty
    (euclideanRayRaySet_empty_of_det2_directions_eq_zero_of_det2_anchor_sub_ne_zero
      hparallel hoffset)

/-- A circle no-meet certificate plus an empty ray-ray component gives the
`<= 4` component-savings branch. -/
def pairComponentSavingsFourOfCircleCircleNoMeetAndRayRayEmpty
    {L M : EuclideanLollipop}
    (D : CircleCircleNoMeetData L M)
    (hrr_empty : ∀ p : EuclideanR2,
      p ∉ euclideanRayRaySet L M) :
    PairComponentSavings L M 4 :=
  pairComponentSavingsFourOfCircleCircleAndRayRayEmpty D.empty hrr_empty

/-- Circle no-meet plus ray-ray no-meet certificates give the `<= 4`
component-savings branch. -/
def pairComponentSavingsFourOfCircleCircleNoMeetAndRayRayNoMeet
    {L M : EuclideanLollipop}
    (Dcc : CircleCircleNoMeetData L M)
    (Drr : RayRayNoMeetData L M) :
    PairComponentSavings L M 4 :=
  pairComponentSavingsFourOfCircleCircleNoMeetAndRayRayEmpty
    Dcc Drr.empty

/-- Circle no-meet plus the determinant/parallel criterion for an empty
ray-ray component gives the `<= 4` branch. -/
def pairComponentSavingsFourOfCircleCircleNoMeetAndRayRayDetSeparated
    {L M : EuclideanLollipop}
    (Dcc : CircleCircleNoMeetData L M)
    (hparallel : det2 L.rayDirection M.rayDirection = 0)
    (hoffset : det2 (M.anchor - L.anchor) L.rayDirection ≠ 0) :
    PairComponentSavings L M 4 :=
  pairComponentSavingsFourOfCircleCircleEmptyAndRayRayDetSeparated
    Dcc.empty hparallel hoffset

/-- Empty mixed circle-ray components give another reusable `<= 4` savings
certificate. -/
def pairComponentSavingsFourOfMixedRayComponentsEmpty
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    (hcr_empty : ∀ p : EuclideanR2,
      p ∉ euclideanCircleRaySet L M)
    (hrc_empty : ∀ p : EuclideanR2,
      p ∉ euclideanRayCircleSet L M) :
    PairComponentSavings L M 4 :=
  pairComponentSavingsOfComponentBounds
    2 0 0 1 (by norm_num)
    (finset_card_le_two_of_forall_mem_euclideanCircleCircleSet hLM)
    (finset_card_le_zero_of_forall_mem_of_component_empty hcr_empty)
    (finset_card_le_zero_of_forall_mem_of_component_empty hrc_empty)
    (finset_card_le_one_of_forall_mem_euclideanRayRaySet hline)

/-- Line-separation certificates for both mixed circle-ray components give a
`<= 4` component-savings certificate. -/
def pairComponentSavingsFourOfMixedRayComponentsNoMeet
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    (Dcr : CircleRayNoMeetData L M)
    (Drc : RayCircleNoMeetData L M) :
    PairComponentSavings L M 4 :=
  pairComponentSavingsFourOfMixedRayComponentsEmpty hLM hline
    Dcr.empty Drc.empty

/-- Projection-distance criteria for both mixed circle-ray components give a
`<= 4` component-savings certificate. -/
noncomputable def pairComponentSavingsFourOfMixedRayComponentsProjectionSeparated
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    (hsepLM :
      L.radius <
        dist (toEuclideanR2 L.center)
          (euclideanRayLineProjection M (toEuclideanR2 L.center)))
    (hsepML :
      M.radius <
        dist (toEuclideanR2 M.center)
          (euclideanRayLineProjection L (toEuclideanR2 M.center))) :
    PairComponentSavings L M 4 :=
  pairComponentSavingsFourOfMixedRayComponentsNoMeet hLM hline
    (CircleRayNoMeetData.of_rayLineProjection hsepLM)
    (RayCircleNoMeetData.of_rayLineProjection hsepML)

/-- Determinant/Cauchy criteria for both mixed components give a `<= 4`
component-savings certificate. -/
def pairComponentSavingsFourOfMixedRayComponentsDetSeparated
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    (hsepLM :
      L.radius ^ 2 * normSq2 M.rayDirection <
        det2 (M.anchor - L.center) M.rayDirection ^ 2)
    (hsepML :
      M.radius ^ 2 * normSq2 L.rayDirection <
        det2 (L.anchor - M.center) L.rayDirection ^ 2) :
    PairComponentSavings L M 4 :=
  pairComponentSavingsFourOfMixedRayComponentsEmpty hLM hline
    (euclideanCircleRaySet_empty_of_radius_sq_mul_normSq2_lt_det2_sq
      hsepLM)
    (euclideanRayCircleSet_empty_of_radius_sq_mul_normSq2_lt_det2_sq
      hsepML)

/-- Named first-principles routes for a `<= 5` pair-component savings
certificate.  This keeps the theorem-facing upper boundary from accepting an
unnamed `PairComponentSavings` object when one of the standard geometric
separation mechanisms is intended. -/
inductive PairComponentSavingsFiveRoute
    (L M : EuclideanLollipop) : Type where
  | circleCircleEmpty
      (hline : euclideanRayLine L ≠ euclideanRayLine M)
      (hcc_empty : ∀ p : EuclideanR2,
        p ∉ euclideanCircleCircleSet L M)
  | circleCircleFarApart
      (hline : euclideanRayLine L ≠ euclideanRayLine M)
      (hfar :
        L.radius + M.radius <
          dist (toEuclideanR2 L.center) (toEuclideanR2 M.center))
  | circleCircleFarApartSq
      (hline : euclideanRayLine L ≠ euclideanRayLine M)
      (hfar :
        (L.radius + M.radius) ^ 2 < distSq2 L.center M.center)
  | circleCircleContainedLeft
      (hline : euclideanRayLine L ≠ euclideanRayLine M)
      (hcontained :
        dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) +
          L.radius < M.radius)
  | circleCircleContainedRight
      (hline : euclideanRayLine L ≠ euclideanRayLine M)
      (hcontained :
        dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) +
          M.radius < L.radius)
  | circleCircleContainedLeftSq
      (hline : euclideanRayLine L ≠ euclideanRayLine M)
      (hradius : L.radius < M.radius)
      (hcontained :
        distSq2 L.center M.center < (M.radius - L.radius) ^ 2)
  | circleCircleContainedRightSq
      (hline : euclideanRayLine L ≠ euclideanRayLine M)
      (hradius : M.radius < L.radius)
      (hcontained :
        distSq2 L.center M.center < (L.radius - M.radius) ^ 2)
  | circleCircleNoMeet
      (hline : euclideanRayLine L ≠ euclideanRayLine M)
      (D : CircleCircleNoMeetData L M)
  | circleRayEmpty
      (hLM :
        euclideanSphere L.center L.radius ≠
          euclideanSphere M.center M.radius)
      (hline : euclideanRayLine L ≠ euclideanRayLine M)
      (hcr_empty : ∀ p : EuclideanR2,
        p ∉ euclideanCircleRaySet L M)
  | circleRayNoMeet
      (hLM :
        euclideanSphere L.center L.radius ≠
          euclideanSphere M.center M.radius)
      (hline : euclideanRayLine L ≠ euclideanRayLine M)
      (D : CircleRayNoMeetData L M)
  | circleRayProjectionSeparated
      (hLM :
        euclideanSphere L.center L.radius ≠
          euclideanSphere M.center M.radius)
      (hline : euclideanRayLine L ≠ euclideanRayLine M)
      (hsep :
        L.radius <
          dist (toEuclideanR2 L.center)
            (euclideanRayLineProjection M (toEuclideanR2 L.center)))
  | circleRayDetSeparated
      (hLM :
        euclideanSphere L.center L.radius ≠
          euclideanSphere M.center M.radius)
      (hline : euclideanRayLine L ≠ euclideanRayLine M)
      (hsep :
        L.radius ^ 2 * normSq2 M.rayDirection <
          det2 (M.anchor - L.center) M.rayDirection ^ 2)
  | circleRayOutward
      (hLM :
        euclideanSphere L.center L.radius ≠
          euclideanSphere M.center M.radius)
      (hline : euclideanRayLine L ≠ euclideanRayLine M)
      (hanchor : L.radius ^ 2 < distSq2 M.anchor L.center)
      (hdot : 0 ≤ dot2 (M.anchor - L.center) M.rayDirection)
  | rayCircleEmpty
      (hLM :
        euclideanSphere L.center L.radius ≠
          euclideanSphere M.center M.radius)
      (hline : euclideanRayLine L ≠ euclideanRayLine M)
      (hrc_empty : ∀ p : EuclideanR2,
        p ∉ euclideanRayCircleSet L M)
  | rayCircleNoMeet
      (hLM :
        euclideanSphere L.center L.radius ≠
          euclideanSphere M.center M.radius)
      (hline : euclideanRayLine L ≠ euclideanRayLine M)
      (D : RayCircleNoMeetData L M)
  | rayCircleProjectionSeparated
      (hLM :
        euclideanSphere L.center L.radius ≠
          euclideanSphere M.center M.radius)
      (hline : euclideanRayLine L ≠ euclideanRayLine M)
      (hsep :
        M.radius <
          dist (toEuclideanR2 M.center)
            (euclideanRayLineProjection L (toEuclideanR2 M.center)))
  | rayCircleDetSeparated
      (hLM :
        euclideanSphere L.center L.radius ≠
          euclideanSphere M.center M.radius)
      (hline : euclideanRayLine L ≠ euclideanRayLine M)
      (hsep :
        M.radius ^ 2 * normSq2 L.rayDirection <
          det2 (L.anchor - M.center) L.rayDirection ^ 2)
  | rayCircleOutward
      (hLM :
        euclideanSphere L.center L.radius ≠
          euclideanSphere M.center M.radius)
      (hline : euclideanRayLine L ≠ euclideanRayLine M)
      (hanchor : M.radius ^ 2 < distSq2 L.anchor M.center)
      (hdot : 0 ≤ dot2 (L.anchor - M.center) L.rayDirection)

namespace PairComponentSavingsFiveRoute

/-- Convert a named `<= 5` savings route into the component-savings object used
by the crossing-count theorem. -/
noncomputable def toPairComponentSavings
    {L M : EuclideanLollipop}
    (R : PairComponentSavingsFiveRoute L M) :
    PairComponentSavings L M 5 :=
  match R with
  | circleCircleEmpty hline hcc_empty =>
      pairComponentSavingsFiveOfCircleCircleEmpty hline hcc_empty
  | circleCircleFarApart hline hfar =>
      pairComponentSavingsFiveOfCircleCircleFarApart hline hfar
  | circleCircleFarApartSq hline hfar =>
      pairComponentSavingsFiveOfCircleCircleFarApartSq hline hfar
  | circleCircleContainedLeft hline hcontained =>
      pairComponentSavingsFiveOfCircleCircleContainedLeft hline hcontained
  | circleCircleContainedRight hline hcontained =>
      pairComponentSavingsFiveOfCircleCircleContainedRight hline hcontained
  | circleCircleContainedLeftSq hline hradius hcontained =>
      pairComponentSavingsFiveOfCircleCircleContainedLeftSq hline hradius
        hcontained
  | circleCircleContainedRightSq hline hradius hcontained =>
      pairComponentSavingsFiveOfCircleCircleContainedRightSq hline hradius
        hcontained
  | circleCircleNoMeet hline D =>
      pairComponentSavingsFiveOfCircleCircleNoMeet hline D
  | circleRayEmpty hLM hline hcr_empty =>
      pairComponentSavingsFiveOfCircleRayEmpty hLM hline hcr_empty
  | circleRayNoMeet hLM hline D =>
      pairComponentSavingsFiveOfCircleRayNoMeet hLM hline D
  | circleRayProjectionSeparated hLM hline hsep =>
      pairComponentSavingsFiveOfCircleRayProjectionSeparated hLM hline hsep
  | circleRayDetSeparated hLM hline hsep =>
      pairComponentSavingsFiveOfCircleRayDetSeparated hLM hline hsep
  | circleRayOutward hLM hline hanchor hdot =>
      pairComponentSavingsFiveOfCircleRayOutward hLM hline hanchor hdot
  | rayCircleEmpty hLM hline hrc_empty =>
      pairComponentSavingsFiveOfRayCircleEmpty hLM hline hrc_empty
  | rayCircleNoMeet hLM hline D =>
      pairComponentSavingsFiveOfRayCircleNoMeet hLM hline D
  | rayCircleProjectionSeparated hLM hline hsep =>
      pairComponentSavingsFiveOfRayCircleProjectionSeparated hLM hline hsep
  | rayCircleDetSeparated hLM hline hsep =>
      pairComponentSavingsFiveOfRayCircleDetSeparated hLM hline hsep
  | rayCircleOutward hLM hline hanchor hdot =>
      pairComponentSavingsFiveOfRayCircleOutward hLM hline hanchor hdot

end PairComponentSavingsFiveRoute

/-- Named first-principles routes for a `<= 4` pair-component savings
certificate. -/
inductive PairComponentSavingsFourRoute
    (L M : EuclideanLollipop) : Type where
  | circleCircleAndRayRayEmpty
      (hcc_empty : ∀ p : EuclideanR2,
        p ∉ euclideanCircleCircleSet L M)
      (hrr_empty : ∀ p : EuclideanR2,
        p ∉ euclideanRayRaySet L M)
  | circleCircleEmptyAndRayRayDetSeparated
      (hcc_empty : ∀ p : EuclideanR2,
        p ∉ euclideanCircleCircleSet L M)
      (hparallel : det2 L.rayDirection M.rayDirection = 0)
      (hoffset : det2 (M.anchor - L.anchor) L.rayDirection ≠ 0)
  | circleCircleNoMeetAndRayRayEmpty
      (D : CircleCircleNoMeetData L M)
      (hrr_empty : ∀ p : EuclideanR2,
        p ∉ euclideanRayRaySet L M)
  | circleCircleNoMeetAndRayRayNoMeet
      (Dcc : CircleCircleNoMeetData L M)
      (Drr : RayRayNoMeetData L M)
  | circleCircleNoMeetAndRayRayDetSeparated
      (Dcc : CircleCircleNoMeetData L M)
      (hparallel : det2 L.rayDirection M.rayDirection = 0)
      (hoffset : det2 (M.anchor - L.anchor) L.rayDirection ≠ 0)
  | mixedRayComponentsEmpty
      (hLM :
        euclideanSphere L.center L.radius ≠
          euclideanSphere M.center M.radius)
      (hline : euclideanRayLine L ≠ euclideanRayLine M)
      (hcr_empty : ∀ p : EuclideanR2,
        p ∉ euclideanCircleRaySet L M)
      (hrc_empty : ∀ p : EuclideanR2,
        p ∉ euclideanRayCircleSet L M)
  | mixedRayComponentsNoMeet
      (hLM :
        euclideanSphere L.center L.radius ≠
          euclideanSphere M.center M.radius)
      (hline : euclideanRayLine L ≠ euclideanRayLine M)
      (Dcr : CircleRayNoMeetData L M)
      (Drc : RayCircleNoMeetData L M)
  | mixedRayComponentsProjectionSeparated
      (hLM :
        euclideanSphere L.center L.radius ≠
          euclideanSphere M.center M.radius)
      (hline : euclideanRayLine L ≠ euclideanRayLine M)
      (hsepLM :
        L.radius <
          dist (toEuclideanR2 L.center)
            (euclideanRayLineProjection M (toEuclideanR2 L.center)))
      (hsepML :
        M.radius <
          dist (toEuclideanR2 M.center)
            (euclideanRayLineProjection L (toEuclideanR2 M.center)))
  | mixedRayComponentsDetSeparated
      (hLM :
        euclideanSphere L.center L.radius ≠
          euclideanSphere M.center M.radius)
      (hline : euclideanRayLine L ≠ euclideanRayLine M)
      (hsepLM :
        L.radius ^ 2 * normSq2 M.rayDirection <
          det2 (M.anchor - L.center) M.rayDirection ^ 2)
      (hsepML :
        M.radius ^ 2 * normSq2 L.rayDirection <
          det2 (L.anchor - M.center) L.rayDirection ^ 2)

namespace PairComponentSavingsFourRoute

/-- Convert a named `<= 4` savings route into the component-savings object used
by the crossing-count theorem. -/
noncomputable def toPairComponentSavings
    {L M : EuclideanLollipop}
    (R : PairComponentSavingsFourRoute L M) :
    PairComponentSavings L M 4 :=
  match R with
  | circleCircleAndRayRayEmpty hcc_empty hrr_empty =>
      pairComponentSavingsFourOfCircleCircleAndRayRayEmpty
        hcc_empty hrr_empty
  | circleCircleEmptyAndRayRayDetSeparated hcc_empty hparallel hoffset =>
      pairComponentSavingsFourOfCircleCircleEmptyAndRayRayDetSeparated
        hcc_empty hparallel hoffset
  | circleCircleNoMeetAndRayRayEmpty D hrr_empty =>
      pairComponentSavingsFourOfCircleCircleNoMeetAndRayRayEmpty D hrr_empty
  | circleCircleNoMeetAndRayRayNoMeet Dcc Drr =>
      pairComponentSavingsFourOfCircleCircleNoMeetAndRayRayNoMeet Dcc Drr
  | circleCircleNoMeetAndRayRayDetSeparated Dcc hparallel hoffset =>
      pairComponentSavingsFourOfCircleCircleNoMeetAndRayRayDetSeparated
        Dcc hparallel hoffset
  | mixedRayComponentsEmpty hLM hline hcr_empty hrc_empty =>
      pairComponentSavingsFourOfMixedRayComponentsEmpty hLM hline
        hcr_empty hrc_empty
  | mixedRayComponentsNoMeet hLM hline Dcr Drc =>
      pairComponentSavingsFourOfMixedRayComponentsNoMeet hLM hline Dcr Drc
  | mixedRayComponentsProjectionSeparated hLM hline hsepLM hsepML =>
      pairComponentSavingsFourOfMixedRayComponentsProjectionSeparated hLM hline
        hsepLM hsepML
  | mixedRayComponentsDetSeparated hLM hline hsepLM hsepML =>
      pairComponentSavingsFourOfMixedRayComponentsDetSeparated hLM hline
        hsepLM hsepML

end PairComponentSavingsFourRoute

/-- Component-wise savings imply the corresponding total finite carrier bound. -/
theorem finset_card_le_of_pairComponentSavings
    {L M : EuclideanLollipop} {bound : Nat}
    (B : PairComponentSavings L M bound)
    (S : Finset EuclideanR2)
    (hS : ∀ p ∈ S, p ∈ euclideanPairIntersectionSet L M) :
    S.card ≤ bound := by
  classical
  let cc : Finset EuclideanR2 :=
    S.filter fun p => p ∈ euclideanCircleCircleSet L M
  let cr : Finset EuclideanR2 :=
    S.filter fun p => p ∈ euclideanCircleRaySet L M
  let rc : Finset EuclideanR2 :=
    S.filter fun p => p ∈ euclideanRayCircleSet L M
  let rr : Finset EuclideanR2 :=
    S.filter fun p => p ∈ euclideanRayRaySet L M
  let u12 : Finset EuclideanR2 := cc ∪ cr
  let u123 : Finset EuclideanR2 := u12 ∪ rc
  let uall : Finset EuclideanR2 := u123 ∪ rr
  have hcover : S ⊆ uall := by
    intro p hpS
    rcases (mem_euclideanPairIntersectionSet_iff.1 (hS p hpS)) with
      hcc | hcr | hrc | hrr
    · simp [uall, u123, u12, cc, hpS, hcc]
    · simp [uall, u123, u12, cr, hpS, hcr]
    · simp [uall, u123, rc, hpS, hrc]
    · simp [uall, rr, hpS, hrr]
  have hccard : cc.card ≤ B.circleCircleBound :=
    B.circleCircle_card_le cc
      (by
        intro p hp
        exact (Finset.mem_filter.1 hp).2)
  have hcrcard : cr.card ≤ B.circleRayBound :=
    B.circleRay_card_le cr
      (by
        intro p hp
        exact (Finset.mem_filter.1 hp).2)
  have hrccard : rc.card ≤ B.rayCircleBound :=
    B.rayCircle_card_le rc
      (by
        intro p hp
        exact (Finset.mem_filter.1 hp).2)
  have hrrcard : rr.card ≤ B.rayRayBound :=
    B.rayRay_card_le rr
      (by
        intro p hp
        exact (Finset.mem_filter.1 hp).2)
  have hSle : S.card ≤ uall.card := Finset.card_le_card hcover
  have huall : uall.card ≤ u123.card + rr.card :=
    Finset.card_union_le u123 rr
  have hu123 : u123.card ≤ u12.card + rc.card :=
    Finset.card_union_le u12 rc
  have hu12 : u12.card ≤ cc.card + cr.card :=
    Finset.card_union_le cc cr
  have htotal :
      B.circleCircleBound + B.circleRayBound + B.rayCircleBound +
        B.rayRayBound ≤ bound :=
    B.total_le
  omega

/-- A primitive finite crossing witness inherits any component-wise savings
after lifting to mathlib's Euclidean plane. -/
theorem pairwiseCarrierCrossingData_lifted_card_le_of_pairComponentSavings
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat}
    (D : PairwiseCarrierCrossingData A cross)
    {i j : Fin n} (hij : i < j) {bound : Nat}
    (B : PairComponentSavings (A.lollipop i) (A.lollipop j) bound) :
    (liftedCrossingFinset (D.crossingPoints i j hij)).card ≤ bound := by
  classical
  refine finset_card_le_of_pairComponentSavings
    B (liftedCrossingFinset (D.crossingPoints i j hij)) ?_
  intro p hp
  rcases Finset.mem_image.1 hp with ⟨x, hxS, rfl⟩
  have hx_pair : x ∈ A.pairIntersectionSet i j := by
    have hset := D.crossingPoints_spec i j hij
    have hx_finset : x ∈ ((D.crossingPoints i j hij : Finset R2) : Set R2) := by
      simpa using hxS
    simpa [hset] using hx_finset
  have hx_pair' :
      x ∈ pairIntersectionSet (A.lollipop i) (A.lollipop j) := by
    simpa [EuclideanLollipopArrangement.pairIntersectionSet] using hx_pair
  have hpre :=
    pairIntersectionSet_eq_preimage_euclideanPairIntersectionSet
      (A.lollipop i) (A.lollipop j)
  have hx_preimage :
      x ∈ {x : R2 |
        toEuclideanR2 x ∈
          euclideanPairIntersectionSet (A.lollipop i) (A.lollipop j)} := by
    simpa [hpre] using hx_pair'
  simpa using hx_preimage

/-- Component-wise savings imply the matching rational crossing-table bound. -/
theorem pairwiseCarrierCrossingData_cross_le_of_pairComponentSavings
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat}
    (D : PairwiseCarrierCrossingData A cross)
    {i j : Fin n} (hij : i < j) {bound : Nat}
    (B : PairComponentSavings (A.lollipop i) (A.lollipop j) bound) :
    cross i j ≤ (bound : Rat) := by
  have hcard :=
    pairwiseCarrierCrossingData_lifted_card_le_of_pairComponentSavings
      D hij B
  have hprimitive_card : (D.crossingPoints i j hij).card ≤ bound := by
    simpa using hcard
  rw [D.cross_eq_card i j hij]
  exact_mod_cast hprimitive_card

/-- Local one-pair finite crossing witnesses inherit component-wise savings
after lifting to mathlib's Euclidean plane. -/
theorem localPairCarrierCrossingData_lifted_card_le_of_pairComponentSavings
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
    (D : LocalPairCarrierCrossingData A cross i j hij) {bound : Nat}
    (B : PairComponentSavings (A.lollipop i) (A.lollipop j) bound) :
    (liftedCrossingFinset D.crossingPoints).card ≤ bound := by
  classical
  refine finset_card_le_of_pairComponentSavings
    B (liftedCrossingFinset D.crossingPoints) ?_
  intro p hp
  rcases Finset.mem_image.1 hp with ⟨x, hxS, rfl⟩
  have hx_pair : x ∈ A.pairIntersectionSet i j := by
    have hset := D.crossingPoints_spec
    have hx_finset : x ∈ ((D.crossingPoints : Finset R2) : Set R2) := by
      simpa using hxS
    simpa [hset] using hx_finset
  have hx_pair' :
      x ∈ pairIntersectionSet (A.lollipop i) (A.lollipop j) := by
    simpa [EuclideanLollipopArrangement.pairIntersectionSet] using hx_pair
  have hpre :=
    pairIntersectionSet_eq_preimage_euclideanPairIntersectionSet
      (A.lollipop i) (A.lollipop j)
  have hx_preimage :
      x ∈ {x : R2 |
        toEuclideanR2 x ∈
          euclideanPairIntersectionSet (A.lollipop i) (A.lollipop j)} := by
    simpa [hpre] using hx_pair'
  simpa using hx_preimage

/-- Component-wise savings imply the matching rational crossing-table bound
directly from a local one-pair finite crossing witness. -/
theorem localPairCarrierCrossingData_cross_le_of_pairComponentSavings
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
    (D : LocalPairCarrierCrossingData A cross i j hij) {bound : Nat}
    (B : PairComponentSavings (A.lollipop i) (A.lollipop j) bound) :
    cross i j ≤ (bound : Rat) := by
  have hcard :=
    localPairCarrierCrossingData_lifted_card_le_of_pairComponentSavings
      D B
  have hprimitive_card : D.crossingPoints.card ≤ bound := by
    simpa using hcard
  rw [D.cross_eq_card]
  exact_mod_cast hprimitive_card

/-- Primitive one-pair local upper data with named route certificates for the
close/intriguing savings branches.  This is lower-level than the
first-principles theorem boundary: it talks only about one concrete primitive
arrangement and one ordered pair `i < j`. -/
structure PrimitiveRoutedLocalPairData
    {n : Nat} (A : EuclideanLollipopArrangement n)
    (cross : Fin n → Fin n → Rat) (i j : Fin n) (hij : i < j) where
  carrier_crossing :
    LocalPairCarrierCrossingData A cross i j hij
  spheres_distinct :
    euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
      euclideanSphere (A.lollipop j).center (A.lollipop j).radius
  rayLines_distinct :
    euclideanRayLine (A.lollipop i) ≠
      euclideanRayLine (A.lollipop j)
  close_savings_route :
    TheoremOneEndToEnd.CloseDirection.cyclicClose
      (fun k => A.normalizedDirection k) i j →
      PairComponentSavingsFiveRoute (A.lollipop i) (A.lollipop j)
  intriguing_savings_route :
    TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
      (fun k => A.center k) (fun k => A.radius k) i j →
      PairComponentSavingsFiveRoute (A.lollipop i) (A.lollipop j)
  close_intriguing_savings_route :
    TheoremOneEndToEnd.CloseDirection.cyclicClose
      (fun k => A.normalizedDirection k) i j →
    TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
      (fun k => A.center k) (fun k => A.radius k) i j →
      PairComponentSavingsFourRoute (A.lollipop i) (A.lollipop j)

namespace PrimitiveRoutedLocalPairData

/-- The routed local primitive pair data prove the generic `<= 7` bound. -/
theorem generic_cross_le_seven
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
    (D : PrimitiveRoutedLocalPairData A cross i j hij) :
    cross i j ≤ 7 :=
  localPairCarrierCrossingData_cross_le_seven
    D.carrier_crossing D.spheres_distinct D.rayLines_distinct

/-- The routed local primitive pair data prove the close-pair `<= 5` bound. -/
theorem close_cross_le_five
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
    (D : PrimitiveRoutedLocalPairData A cross i j hij)
    (hclose :
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => A.normalizedDirection k) i j) :
    cross i j ≤ 5 :=
  localPairCarrierCrossingData_cross_le_of_pairComponentSavings
    D.carrier_crossing (D.close_savings_route hclose).toPairComponentSavings

/-- The routed local primitive pair data prove the intriguing-pair `<= 5`
bound. -/
theorem intriguing_cross_le_five
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
    (D : PrimitiveRoutedLocalPairData A cross i j hij)
    (hintriguing :
      TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
        (fun k => A.center k) (fun k => A.radius k) i j) :
    cross i j ≤ 5 :=
  localPairCarrierCrossingData_cross_le_of_pairComponentSavings
    D.carrier_crossing
      (D.intriguing_savings_route hintriguing).toPairComponentSavings

/-- The routed local primitive pair data prove the close-and-intriguing
`<= 4` bound. -/
theorem close_intriguing_cross_le_four
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
    (D : PrimitiveRoutedLocalPairData A cross i j hij)
    (hclose :
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => A.normalizedDirection k) i j)
    (hintriguing :
      TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
        (fun k => A.center k) (fun k => A.radius k) i j) :
    cross i j ≤ 4 :=
  localPairCarrierCrossingData_cross_le_of_pairComponentSavings
    D.carrier_crossing
      (D.close_intriguing_savings_route hclose hintriguing).toPairComponentSavings

end PrimitiveRoutedLocalPairData

/-- Stronger primitive carrier upper data where close/intriguing savings are
also supplied component-wise rather than as final numeric crossing bounds. -/
structure PrimitiveCarrierComponentSavingsUpperGeometryData
    (P : TheoremOne.ProblemFamily.{u}) where
  arrangement :
    ∀ n : Nat, P.Arrangement n → EuclideanLollipopArrangement n
  cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  pairwise_crossings :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      PairwiseCarrierCrossingData (arrangement n A) (cross n A)
  spheres_distinct :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      euclideanSphere ((arrangement n A).lollipop i).center
          ((arrangement n A).lollipop i).radius ≠
        euclideanSphere ((arrangement n A).lollipop j).center
          ((arrangement n A).lollipop j).radius
  rayLines_distinct :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      euclideanRayLine ((arrangement n A).lollipop i) ≠
        euclideanRayLine ((arrangement n A).lollipop j)
  close_savings :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => (arrangement n A).normalizedDirection k) i j →
        PairComponentSavings ((arrangement n A).lollipop i)
          ((arrangement n A).lollipop j) 5
  intriguing_savings :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      circleIntriguing
        (fun k => (arrangement n A).center k)
        (fun k => (arrangement n A).radius k) i j →
        PairComponentSavings ((arrangement n A).lollipop i)
          ((arrangement n A).lollipop j) 5
  close_intriguing_savings :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => (arrangement n A).normalizedDirection k) i j →
      circleIntriguing
        (fun k => (arrangement n A).center k)
        (fun k => (arrangement n A).radius k) i j →
        PairComponentSavings ((arrangement n A).lollipop i)
          ((arrangement n A).lollipop j) 4
  region_increment :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      OrderedIncrementalPairRegionData n (P.region n A) (cross n A)

namespace PrimitiveCarrierComponentSavingsUpperGeometryData

/-- Component-savings upper data imply the existing carrier-certified exact
upper interface.  The generic branch uses the proved `≤ 7` component count;
the close/intriguing branches use the supplied component-wise savings. -/
noncomputable def toPrimitiveCarrierCertifiedExactUpperGeometryData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveCarrierComponentSavingsUpperGeometryData P) :
    PrimitiveCarrierCertifiedExactUpperGeometryData P where
  arrangement := h.arrangement
  cross := h.cross
  pairwise_crossings := h.pairwise_crossings
  cross_le_case := by
    intro n A i j hij
    by_cases hc :
        TheoremOneEndToEnd.CloseDirection.cyclicClose
          (fun k => (h.arrangement n A).normalizedDirection k) i j
    · by_cases hi :
          circleIntriguing
            (fun k => (h.arrangement n A).center k)
            (fun k => (h.arrangement n A).radius k) i j
      · have h4 :=
          pairwiseCarrierCrossingData_cross_le_of_pairComponentSavings
            (h.pairwise_crossings n A) hij
            (h.close_intriguing_savings n A i j hij hc hi)
        simpa [TheoremOneEndToEnd.canonicalCrossingCaseBound, hc, hi] using h4
      · have h5 :=
          pairwiseCarrierCrossingData_cross_le_of_pairComponentSavings
            (h.pairwise_crossings n A) hij (h.close_savings n A i j hij hc)
        simpa [TheoremOneEndToEnd.canonicalCrossingCaseBound, hc, hi] using h5
    · by_cases hi :
          circleIntriguing
            (fun k => (h.arrangement n A).center k)
            (fun k => (h.arrangement n A).radius k) i j
      · have h5 :=
          pairwiseCarrierCrossingData_cross_le_of_pairComponentSavings
            (h.pairwise_crossings n A) hij
            (h.intriguing_savings n A i j hij hi)
        simpa [TheoremOneEndToEnd.canonicalCrossingCaseBound, hc, hi] using h5
      · have h7 :=
          pairwiseCarrierCrossingData_cross_le_seven
            (h.pairwise_crossings n A) hij
            (h.spheres_distinct n A i j hij)
            (h.rayLines_distinct n A i j hij)
        simpa [TheoremOneEndToEnd.canonicalCrossingCaseBound, hc, hi] using h7
  region_increment := h.region_increment

end PrimitiveCarrierComponentSavingsUpperGeometryData

/-- Primitive carrier upper data whose close/intriguing savings are supplied
by named geometric route constructors.  This is the theorem-stack version of
the route-based first-principles boundary: Lean converts each route to the
component-savings object used by the existing crossing-count theorem. -/
structure PrimitiveCarrierRoutedComponentSavingsUpperGeometryData
    (P : TheoremOne.ProblemFamily.{u}) where
  arrangement :
    ∀ n : Nat, P.Arrangement n → EuclideanLollipopArrangement n
  cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  pairwise_crossings :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      PairwiseCarrierCrossingData (arrangement n A) (cross n A)
  spheres_distinct :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      euclideanSphere ((arrangement n A).lollipop i).center
          ((arrangement n A).lollipop i).radius ≠
        euclideanSphere ((arrangement n A).lollipop j).center
          ((arrangement n A).lollipop j).radius
  rayLines_distinct :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      euclideanRayLine ((arrangement n A).lollipop i) ≠
        euclideanRayLine ((arrangement n A).lollipop j)
  close_savings_route :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => (arrangement n A).normalizedDirection k) i j →
        PairComponentSavingsFiveRoute ((arrangement n A).lollipop i)
          ((arrangement n A).lollipop j)
  intriguing_savings_route :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      circleIntriguing
        (fun k => (arrangement n A).center k)
        (fun k => (arrangement n A).radius k) i j →
        PairComponentSavingsFiveRoute ((arrangement n A).lollipop i)
          ((arrangement n A).lollipop j)
  close_intriguing_savings_route :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => (arrangement n A).normalizedDirection k) i j →
      circleIntriguing
        (fun k => (arrangement n A).center k)
        (fun k => (arrangement n A).radius k) i j →
        PairComponentSavingsFourRoute ((arrangement n A).lollipop i)
          ((arrangement n A).lollipop j)
  region_increment :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      OrderedIncrementalPairRegionData n (P.region n A) (cross n A)

namespace PrimitiveCarrierRoutedComponentSavingsUpperGeometryData

/-- Convert routed upper data to the component-savings upper package used by
the existing theorem stack. -/
noncomputable def toComponentSavingsUpperGeometryData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveCarrierRoutedComponentSavingsUpperGeometryData P) :
    PrimitiveCarrierComponentSavingsUpperGeometryData P where
  arrangement := h.arrangement
  cross := h.cross
  pairwise_crossings := h.pairwise_crossings
  spheres_distinct := h.spheres_distinct
  rayLines_distinct := h.rayLines_distinct
  close_savings := by
    intro n A i j hij hclose
    exact (h.close_savings_route n A i j hij hclose).toPairComponentSavings
  intriguing_savings := by
    intro n A i j hij hintriguing
    exact
      (h.intriguing_savings_route n A i j hij hintriguing).toPairComponentSavings
  close_intriguing_savings := by
    intro n A i j hij hclose hintriguing
    exact
      (h.close_intriguing_savings_route n A i j hij hclose
        hintriguing).toPairComponentSavings
  region_increment := h.region_increment

end PrimitiveCarrierRoutedComponentSavingsUpperGeometryData

/-- Radial version of component-savings primitive upper data.

The base component-savings package is enough for the generic theorem stack,
because the carrier sets and crossing witnesses are already explicit.  This
strengthened package additionally records the manuscript condition that every
stem ray is radial outward from its circle center. -/
structure PrimitiveRadialCarrierComponentSavingsUpperGeometryData
    (P : TheoremOne.ProblemFamily.{u})
    extends PrimitiveCarrierComponentSavingsUpperGeometryData P where
  radial_outward :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i : Fin n,
      ((arrangement n A).lollipop i).IsRadialOutward

namespace PrimitiveRadialCarrierComponentSavingsUpperGeometryData

/-- Forget the radial-outward field after it has been recorded at the
theorem-facing boundary. -/
noncomputable def toComponentSavingsUpperGeometryData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveRadialCarrierComponentSavingsUpperGeometryData P) :
    PrimitiveCarrierComponentSavingsUpperGeometryData P :=
  h.toPrimitiveCarrierComponentSavingsUpperGeometryData

end PrimitiveRadialCarrierComponentSavingsUpperGeometryData

/-- Radial version of routed component-savings primitive upper data. -/
structure PrimitiveRadialCarrierRoutedComponentSavingsUpperGeometryData
    (P : TheoremOne.ProblemFamily.{u})
    extends PrimitiveCarrierRoutedComponentSavingsUpperGeometryData P where
  radial_outward :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i : Fin n,
      ((arrangement n A).lollipop i).IsRadialOutward

namespace PrimitiveRadialCarrierRoutedComponentSavingsUpperGeometryData

/-- Forget only the radial-outward field from routed radial upper data. -/
noncomputable def toRoutedComponentSavingsUpperGeometryData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveRadialCarrierRoutedComponentSavingsUpperGeometryData P) :
    PrimitiveCarrierRoutedComponentSavingsUpperGeometryData P :=
  h.toPrimitiveCarrierRoutedComponentSavingsUpperGeometryData

/-- Convert routed radial upper data into the radial component-savings package
used by the current manuscript dependency graph. -/
noncomputable def toRadialComponentSavingsUpperGeometryData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveRadialCarrierRoutedComponentSavingsUpperGeometryData P) :
    PrimitiveRadialCarrierComponentSavingsUpperGeometryData P where
  toPrimitiveCarrierComponentSavingsUpperGeometryData :=
    h.toRoutedComponentSavingsUpperGeometryData.toComponentSavingsUpperGeometryData
  radial_outward := h.radial_outward

end PrimitiveRadialCarrierRoutedComponentSavingsUpperGeometryData

/-- Primitive carrier-certified upper data where Lean derives the baseline
`≤ 7` crossing bound from component cardinalities and generic noncoincidence.
The close/intriguing `≤ 5/4` savings remain explicit fields, because those
are the manuscript-specific Euclidean angle arguments. -/
structure PrimitiveCarrierComponentBoundUpperGeometryData
    (P : TheoremOne.ProblemFamily.{u}) where
  arrangement :
    ∀ n : Nat, P.Arrangement n → EuclideanLollipopArrangement n
  cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  pairwise_crossings :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      PairwiseCarrierCrossingData (arrangement n A) (cross n A)
  spheres_distinct :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      euclideanSphere ((arrangement n A).lollipop i).center
          ((arrangement n A).lollipop i).radius ≠
        euclideanSphere ((arrangement n A).lollipop j).center
          ((arrangement n A).lollipop j).radius
  rayLines_distinct :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      euclideanRayLine ((arrangement n A).lollipop i) ≠
        euclideanRayLine ((arrangement n A).lollipop j)
  cross_le_close :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => (arrangement n A).normalizedDirection k) i j →
        cross n A i j ≤ 5
  cross_le_intriguing :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      circleIntriguing
        (fun k => (arrangement n A).center k)
        (fun k => (arrangement n A).radius k) i j →
        cross n A i j ≤ 5
  cross_le_close_intriguing :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => (arrangement n A).normalizedDirection k) i j →
      circleIntriguing
        (fun k => (arrangement n A).center k)
        (fun k => (arrangement n A).radius k) i j →
        cross n A i j ≤ 4
  region_increment :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      OrderedIncrementalPairRegionData n (P.region n A) (cross n A)

namespace PrimitiveCarrierComponentBoundUpperGeometryData

/-- Convert component-bound primitive carrier data into the existing carrier
certified exact upper interface.  The general branch of the canonical
crossing table is supplied by `pairwiseCarrierCrossingData_cross_le_seven`. -/
noncomputable def toPrimitiveCarrierCertifiedExactUpperGeometryData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveCarrierComponentBoundUpperGeometryData P) :
    PrimitiveCarrierCertifiedExactUpperGeometryData P where
  arrangement := h.arrangement
  cross := h.cross
  pairwise_crossings := h.pairwise_crossings
  cross_le_case := by
    intro n A i j hij
    by_cases hc :
        TheoremOneEndToEnd.CloseDirection.cyclicClose
          (fun k => (h.arrangement n A).normalizedDirection k) i j
    · by_cases hi :
          circleIntriguing
            (fun k => (h.arrangement n A).center k)
            (fun k => (h.arrangement n A).radius k) i j
      · have h4 := h.cross_le_close_intriguing n A i j hij hc hi
        simpa [TheoremOneEndToEnd.canonicalCrossingCaseBound, hc, hi] using h4
      · have h5 := h.cross_le_close n A i j hij hc
        simpa [TheoremOneEndToEnd.canonicalCrossingCaseBound, hc, hi] using h5
    · by_cases hi :
          circleIntriguing
            (fun k => (h.arrangement n A).center k)
            (fun k => (h.arrangement n A).radius k) i j
      · have h5 := h.cross_le_intriguing n A i j hij hi
        simpa [TheoremOneEndToEnd.canonicalCrossingCaseBound, hc, hi] using h5
      · have h7 :=
          pairwiseCarrierCrossingData_cross_le_seven
            (h.pairwise_crossings n A) hij
            (h.spheres_distinct n A i j hij)
            (h.rayLines_distinct n A i j hij)
        simpa [TheoremOneEndToEnd.canonicalCrossingCaseBound, hc, hi] using h7
  region_increment := h.region_increment

end PrimitiveCarrierComponentBoundUpperGeometryData

end PrimitiveGeometry
end TheoremOneManuscript
end Lollipop

/-!
Proof component 2: `Manuscript.CompleteFormalization.FiniteCarrier`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Finite carrier witnesses from the proved component bounds.

The primitive geometry layer proves that every finite subset of the lifted
circle/ray components has the expected cardinality bound.  This file converts
those bounds into actual `Set.Finite` and `Finset` witnesses.  It is kept in the
`CompleteFormalization` folder so it refines the theorem boundary without
changing the older proof stack.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace CompleteFormalization

open PrimitiveGeometry

namespace FiniteCarrier

noncomputable section

/-- If every finite subset of a set has bounded cardinality, then the set is
finite.  Mathlib supplies the contrapositive direction via
`Set.Infinite.exists_subset_card_eq`. -/
theorem finite_of_forall_finset_subset_card_le
    {α : Type*} {s : Set α} {N : Nat}
    (h : ∀ T : Finset α, (T : Set α) ⊆ s → T.card ≤ N) :
    s.Finite := by
  by_contra hfinite
  have hinfinite : s.Infinite := hfinite
  rcases hinfinite.exists_subset_card_eq (N + 1) with ⟨T, hTsub, hTcard⟩
  have hle : T.card ≤ N := h T hTsub
  omega

/-- A lifted circle-circle component is finite when the two lifted circles are
distinct. -/
theorem euclideanCircleCircleSet_finite
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius) :
    (euclideanCircleCircleSet L M).Finite := by
  refine finite_of_forall_finset_subset_card_le (N := 2) ?_
  intro S hS
  exact finset_card_le_two_of_forall_mem_euclideanCircleCircleSet hLM S
    (by
      intro p hp
      exact hS hp)

/-- A lifted circle-ray component is finite. -/
theorem euclideanCircleRaySet_finite
    (L M : EuclideanLollipop) :
    (euclideanCircleRaySet L M).Finite := by
  refine finite_of_forall_finset_subset_card_le (N := 2) ?_
  intro S hS
  exact finset_card_le_two_of_forall_mem_euclideanCircleRaySet S
    (by
      intro p hp
      exact hS hp)

/-- A lifted ray-circle component is finite. -/
theorem euclideanRayCircleSet_finite
    (L M : EuclideanLollipop) :
    (euclideanRayCircleSet L M).Finite := by
  refine finite_of_forall_finset_subset_card_le (N := 2) ?_
  intro S hS
  exact finset_card_le_two_of_forall_mem_euclideanRayCircleSet S
    (by
      intro p hp
      exact hS hp)

/-- A lifted ray-ray component is finite when the supporting ray lines are
distinct. -/
theorem euclideanRayRaySet_finite
    {L M : EuclideanLollipop}
    (hline : euclideanRayLine L ≠ euclideanRayLine M) :
    (euclideanRayRaySet L M).Finite := by
  refine finite_of_forall_finset_subset_card_le (N := 1) ?_
  intro S hS
  exact finset_card_le_one_of_forall_mem_euclideanRayRaySet hline S
    (by
      intro p hp
      exact hS hp)

/-- The whole lifted carrier intersection is finite under the two generic
noncoincidence hypotheses used throughout the upper-bound proof. -/
theorem euclideanPairIntersectionSet_finite
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M) :
    (euclideanPairIntersectionSet L M).Finite := by
  let U : Set EuclideanR2 :=
    euclideanCircleCircleSet L M ∪ euclideanCircleRaySet L M ∪
      euclideanRayCircleSet L M ∪ euclideanRayRaySet L M
  have hUfinite : U.Finite := by
    dsimp [U]
    exact (((euclideanCircleCircleSet_finite hLM).union
      (euclideanCircleRaySet_finite L M)).union
      (euclideanRayCircleSet_finite L M)).union
      (euclideanRayRaySet_finite hline)
  refine hUfinite.subset ?_
  intro p hp
  rcases mem_euclideanPairIntersectionSet_iff.1 hp with hcc | hcr | hrc | hrr
  · exact Or.inl (Or.inl (Or.inl hcc))
  · exact Or.inl (Or.inl (Or.inr hcr))
  · exact Or.inl (Or.inr hrc)
  · exact Or.inr hrr

/-- The primitive carrier intersection is finite under the generic
noncoincidence hypotheses. -/
theorem pairIntersectionSet_finite
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M) :
    (pairIntersectionSet L M).Finite := by
  have hE : (euclideanPairIntersectionSet L M).Finite :=
    euclideanPairIntersectionSet_finite hLM hline
  have hpre :
      ({p : R2 | toEuclideanR2 p ∈ euclideanPairIntersectionSet L M}).Finite := by
    exact hE.preimage
      (by
        intro x _hx y _hy hxy
        exact toEuclideanR2_injective hxy)
  simpa [pairIntersectionSet_eq_preimage_euclideanPairIntersectionSet] using hpre

/-- The finite primitive carrier-intersection witness produced from the generic
noncoincidence hypotheses. -/
noncomputable def pairIntersectionFinset
    (L M : EuclideanLollipop)
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M) : Finset R2 :=
  (pairIntersectionSet_finite hLM hline).toFinset

/-- The automatically produced finite witness is exactly the primitive carrier
intersection. -/
theorem pairIntersectionFinset_spec
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M) :
    (pairIntersectionFinset L M hLM hline : Set R2) =
      pairIntersectionSet L M := by
  exact (pairIntersectionSet_finite hLM hline).coe_toFinset

/-- Any primitive finite subset of a generic carrier intersection has at most
seven points. -/
theorem finset_card_le_seven_of_forall_mem_pairIntersectionSet
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    (S : Finset R2)
    (hS : ∀ p ∈ S, p ∈ pairIntersectionSet L M) :
    S.card ≤ 7 := by
  have hlift :
      (liftedCrossingFinset S).card ≤ 7 := by
    refine finset_card_le_seven_of_forall_mem_euclideanPairIntersectionSet
      hLM hline (liftedCrossingFinset S) ?_
    intro p hp
    rcases Finset.mem_image.1 hp with ⟨x, hxS, rfl⟩
    have hx : x ∈ pairIntersectionSet L M := hS x hxS
    have hxpre :
        x ∈ {x : R2 | toEuclideanR2 x ∈
          euclideanPairIntersectionSet L M} := by
      simpa [pairIntersectionSet_eq_preimage_euclideanPairIntersectionSet]
        using hx
    simpa using hxpre
  simpa using hlift

/-- The automatically produced finite witness has at most seven points. -/
theorem pairIntersectionFinset_card_le_seven
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M) :
    (pairIntersectionFinset L M hLM hline).card ≤ 7 := by
  refine finset_card_le_seven_of_forall_mem_pairIntersectionSet
    hLM hline (pairIntersectionFinset L M hLM hline) ?_
  intro p hp
  have hp_set :
      p ∈ ((pairIntersectionFinset L M hLM hline : Finset R2) : Set R2) := by
    simpa using hp
  simpa [pairIntersectionFinset_spec hLM hline] using hp_set

/-- If a seven-point finite set lies inside a generic carrier intersection,
then the automatic finite carrier witness has cardinality at least seven. -/
theorem seven_le_pairIntersectionFinset_card_of_subset
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    (S : Finset R2)
    (hScard : S.card = 7)
    (hS : ∀ p ∈ S, p ∈ pairIntersectionSet L M) :
    7 ≤ (pairIntersectionFinset L M hLM hline).card := by
  have hsubset :
      S ⊆ pairIntersectionFinset L M hLM hline := by
    intro p hp
    have hp_set :
        p ∈ pairIntersectionSet L M := hS p hp
    have hp_auto :
        p ∈ ((pairIntersectionFinset L M hLM hline : Finset R2) :
          Set R2) := by
      simpa [pairIntersectionFinset_spec hLM hline] using hp_set
    simpa using hp_auto
  rw [← hScard]
  exact Finset.card_le_card hsubset

/-- A seven-point finite subset of a generic carrier intersection pins the
automatic finite carrier witness down to exactly seven points. -/
theorem pairIntersectionFinset_card_eq_seven_of_subset
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    (S : Finset R2)
    (hScard : S.card = 7)
    (hS : ∀ p ∈ S, p ∈ pairIntersectionSet L M) :
    (pairIntersectionFinset L M hLM hline).card = 7 := by
  exact Nat.le_antisymm
    (pairIntersectionFinset_card_le_seven hLM hline)
    (seven_le_pairIntersectionFinset_card_of_subset hLM hline S hScard hS)

/-- Local arrangement-indexed finite witness for one unordered pair. -/
noncomputable def arrangementPairIntersectionFinset
    {n : Nat} (A : EuclideanLollipopArrangement n)
    {i j : Fin n} (_hij : i < j)
    (hLM :
      euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
        euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      euclideanRayLine (A.lollipop i) ≠ euclideanRayLine (A.lollipop j)) :
    Finset R2 :=
  pairIntersectionFinset (A.lollipop i) (A.lollipop j) hLM hline

/-- The arrangement-indexed finite witness is exactly that pair's primitive
carrier intersection. -/
theorem arrangementPairIntersectionFinset_spec
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n} {hij : i < j}
    (hLM :
      euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
        euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      euclideanRayLine (A.lollipop i) ≠ euclideanRayLine (A.lollipop j)) :
    (arrangementPairIntersectionFinset A hij hLM hline : Set R2) =
      A.pairIntersectionSet i j := by
  simpa [arrangementPairIntersectionFinset,
    EuclideanLollipopArrangement.pairIntersectionSet] using
    pairIntersectionFinset_spec hLM hline

/-- The arrangement-indexed finite witness has at most seven points. -/
theorem arrangementPairIntersectionFinset_card_le_seven
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n} {hij : i < j}
    (hLM :
      euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
        euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      euclideanRayLine (A.lollipop i) ≠ euclideanRayLine (A.lollipop j)) :
    (arrangementPairIntersectionFinset A hij hLM hline).card ≤ 7 :=
  pairIntersectionFinset_card_le_seven hLM hline

/-- A seven-point finite subset of one arrangement pair's carrier
intersection pins the automatic arrangement-indexed witness down to exactly
seven points. -/
theorem arrangementPairIntersectionFinset_card_eq_seven_of_subset
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n} {hij : i < j}
    (hLM :
      euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
        euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      euclideanRayLine (A.lollipop i) ≠ euclideanRayLine (A.lollipop j))
    (S : Finset R2)
    (hScard : S.card = 7)
    (hS : ∀ p ∈ S, p ∈ A.pairIntersectionSet i j) :
    (arrangementPairIntersectionFinset A hij hLM hline).card = 7 := by
  refine pairIntersectionFinset_card_eq_seven_of_subset
    hLM hline S hScard ?_
  intro p hp
  simpa [EuclideanLollipopArrangement.pairIntersectionSet] using hS p hp

/-- If a crossing table is defined as the cardinality of the automatic finite
witness for one pair, that pair has a local carrier-crossing certificate. -/
noncomputable def localPairCarrierCrossingDataOfFiniteCarrier
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n} (hij : i < j)
    (hLM :
      euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
        euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      euclideanRayLine (A.lollipop i) ≠ euclideanRayLine (A.lollipop j)) :
    LocalPairCarrierCrossingData A
      (fun a b =>
        if _h : a = i ∧ b = j then
          ((arrangementPairIntersectionFinset A hij hLM hline).card : Rat)
        else 0)
      i j hij where
  crossingPoints := arrangementPairIntersectionFinset A hij hLM hline
  crossingPoints_spec := arrangementPairIntersectionFinset_spec hLM hline
  cross_eq_card := by
    simp

/-- A more flexible local certificate constructor: any crossing table whose
selected entry is the cardinality of the automatic finite witness gets a local
carrier-crossing certificate for that pair. -/
noncomputable def localPairCarrierCrossingDataOfFiniteCarrierEq
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat}
    {i j : Fin n} (hij : i < j)
    (hLM :
      euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
        euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      euclideanRayLine (A.lollipop i) ≠ euclideanRayLine (A.lollipop j))
    (hcross :
      cross i j =
        ((arrangementPairIntersectionFinset A hij hLM hline).card : Rat)) :
    LocalPairCarrierCrossingData A cross i j hij where
  crossingPoints := arrangementPairIntersectionFinset A hij hLM hline
  crossingPoints_spec := arrangementPairIntersectionFinset_spec hLM hline
  cross_eq_card := hcross

/-- The automatic pairwise crossing table obtained by counting each finite
carrier intersection.  Unordered pairs `i < j` get their exact finite-witness
cardinality; other entries are set to zero because the formal upper pipeline
only consumes increasing pairs. -/
noncomputable def automaticCarrierCrossingTable
    {n : Nat} (A : EuclideanLollipopArrangement n)
    (hLM :
      ∀ i j : Fin n, i < j →
        euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
          euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      ∀ i j : Fin n, i < j →
        euclideanRayLine (A.lollipop i) ≠
          euclideanRayLine (A.lollipop j)) :
    Fin n → Fin n → Rat :=
  fun i j =>
    if hij : i < j then
      ((arrangementPairIntersectionFinset A hij (hLM i j hij)
        (hline i j hij)).card : Rat)
    else
      0

/-- Each increasing entry of the automatic crossing table is the cardinality of
the corresponding automatic finite witness. -/
theorem automaticCarrierCrossingTable_eq_card
    {n : Nat} {A : EuclideanLollipopArrangement n}
    (hLM :
      ∀ i j : Fin n, i < j →
        euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
          euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      ∀ i j : Fin n, i < j →
        euclideanRayLine (A.lollipop i) ≠
          euclideanRayLine (A.lollipop j))
    {i j : Fin n} (hij : i < j) :
    automaticCarrierCrossingTable A hLM hline i j =
      ((arrangementPairIntersectionFinset A hij (hLM i j hij)
        (hline i j hij)).card : Rat) := by
  simp [automaticCarrierCrossingTable, hij]

/-- The automatic crossing table has a bundled pairwise carrier-crossing
certificate. -/
noncomputable def pairwiseCarrierCrossingDataOfFiniteCarrier
    {n : Nat} (A : EuclideanLollipopArrangement n)
    (hLM :
      ∀ i j : Fin n, i < j →
        euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
          euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      ∀ i j : Fin n, i < j →
        euclideanRayLine (A.lollipop i) ≠
          euclideanRayLine (A.lollipop j)) :
    PairwiseCarrierCrossingData A
      (automaticCarrierCrossingTable A hLM hline) where
  crossingPoints := fun i j hij =>
    arrangementPairIntersectionFinset A hij (hLM i j hij) (hline i j hij)
  crossingPoints_spec := by
    intro i j hij
    exact arrangementPairIntersectionFinset_spec (hLM i j hij) (hline i j hij)
  cross_eq_card := by
    intro i j hij
    exact automaticCarrierCrossingTable_eq_card hLM hline hij

/-- Every increasing entry of the automatic crossing table is at most seven. -/
theorem automaticCarrierCrossingTable_le_seven
    {n : Nat} {A : EuclideanLollipopArrangement n}
    (hLM :
      ∀ i j : Fin n, i < j →
        euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
          euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      ∀ i j : Fin n, i < j →
        euclideanRayLine (A.lollipop i) ≠
          euclideanRayLine (A.lollipop j))
    {i j : Fin n} (hij : i < j) :
    automaticCarrierCrossingTable A hLM hline i j ≤ 7 := by
  rw [automaticCarrierCrossingTable_eq_card hLM hline hij]
  exact_mod_cast arrangementPairIntersectionFinset_card_le_seven
    (hLM i j hij) (hline i j hij)

end

end FiniteCarrier
end CompleteFormalization
end TheoremOneManuscript
end Lollipop

/-!
Proof component 3: `Manuscript.ExplicitInputs.Lower`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Explicit lower-construction inputs for the manuscript version of Theorem 1.

The older sorted Karlsson interfaces only ask for an arrangement realizing
each sorted quadruple.  This file exposes the more construction-shaped
interface used in the manuscript: for every sorted quadruple, a named
Karlsson blow-up arrangement is produced, its crossing count is the lower
quadruple count, and its region equation is either supplied directly or
derived from incremental insertion data.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace ExplicitInputs

universe u

/-- A named sorted Karlsson blow-up construction for every sorted quadruple,
with the lower region equation supplied directly. -/
structure KarlssonBlowUpLowerData
    (P : TheoremOne.ProblemFamily.{u}) where
  crossings : (n : Nat) → P.Arrangement n → Rat
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  crossings_eq_lower :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      crossings n (arrangement n q hq) = lowerCrossingsOfQuad q
  regions_eq :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      P.region n (arrangement n q hq) =
        crossings n (arrangement n q hq) + (n : Rat) + 1

namespace KarlssonBlowUpLowerData

/-- A named Karlsson blow-up construction implies the older existential
sorted lower-realization interface. -/
def toSortedKarlssonLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonBlowUpLowerData P) :
    SortedKarlssonLowerData P where
  crossings := h.crossings
  realizations := by
    intro n q hq
    exact ⟨h.arrangement n q hq, h.crossings_eq_lower n q hq,
      h.regions_eq n q hq⟩

end KarlssonBlowUpLowerData

/-- A named sorted Karlsson blow-up construction where the lower region
equation is proved from incremental insertion data. -/
structure KarlssonBlowUpIncrementalLowerData
    (P : TheoremOne.ProblemFamily.{u}) where
  crossings : (n : Nat) → P.Arrangement n → Rat
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  crossings_eq_lower :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      crossings n (arrangement n q hq) = lowerCrossingsOfQuad q
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      IncrementalRegionData n
        (P.region n (arrangement n q hq))
        (crossings n (arrangement n q hq))

namespace KarlssonBlowUpIncrementalLowerData

/-- Forget the step-by-step lower construction after deriving the direct
lower region equation. -/
def toKarlssonBlowUpLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonBlowUpIncrementalLowerData P) :
    KarlssonBlowUpLowerData P where
  crossings := h.crossings
  arrangement := h.arrangement
  crossings_eq_lower := h.crossings_eq_lower
  regions_eq := by
    intro n q hq
    exact (h.region_increment n q hq).target_eq_totalCrossings_add

/-- A named incremental Karlsson blow-up construction implies the older
existential incremental sorted lower-realization interface. -/
def toSortedKarlssonIncrementalLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonBlowUpIncrementalLowerData P) :
    SortedKarlssonIncrementalLowerData P where
  crossings := h.crossings
  realizations := by
    intro n q hq
    exact ⟨h.arrangement n q hq, h.region_increment n q hq,
      h.crossings_eq_lower n q hq⟩

/-- A named incremental Karlsson blow-up construction also implies the direct
sorted lower-realization interface. -/
def toSortedKarlssonLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonBlowUpIncrementalLowerData P) :
    SortedKarlssonLowerData P :=
  h.toKarlssonBlowUpLowerData.toSortedKarlssonLowerData

end KarlssonBlowUpIncrementalLowerData

/-- Direct named Karlsson blow-up data give lower attainment of the
Theorem 1 candidate. -/
theorem lower_attainment_of_karlssonBlowUpLowerData_choose
    (P : TheoremOne.ProblemFamily.{u})
    (h : KarlssonBlowUpLowerData P) :
    ∀ n : Nat, ∃ A : P.Arrangement n,
      P.region n A = candidateRegionsChoose n := by
  exact
    lower_attainment_of_sortedLowerCrossingRealizations_choose
      P (crossings := h.crossings) h.toSortedKarlssonLowerData.realizations

/-- Incremental named Karlsson blow-up data give lower attainment of the
Theorem 1 candidate. -/
theorem lower_attainment_of_karlssonBlowUpIncrementalLowerData_choose
    (P : TheoremOne.ProblemFamily.{u})
    (h : KarlssonBlowUpIncrementalLowerData P) :
    ∀ n : Nat, ∃ A : P.Arrangement n,
      P.region n A = candidateRegionsChoose n := by
  exact
    lower_attainment_of_sortedLowerIncrementalCrossingRealizations_choose
      P (crossings := h.crossings)
      h.toSortedKarlssonIncrementalLowerData.realizations

end ExplicitInputs
end TheoremOneManuscript
end Lollipop

/-!
Proof component 4: `Manuscript.ExplicitInputs.LowerTable`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Table-shaped Karlsson lower construction data.

`ExplicitInputs/Lower.lean` asks the lower construction to prove directly
that its crossing count is `lowerCrossingsOfQuad q`.  This file splits that
obligation into the manuscript's four-cluster crossing table: intra-cluster
pairs contribute `4`, the exceptional inter-cluster pair `(0,1)` contributes
`5`, and the other five inter-cluster pairs contribute `7`.  Lean proves that
the finite table sum is exactly the old `lowerCrossingsOfQuad` formula.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace ExplicitInputs

universe u

/-- The inter-cluster part of Karlsson's four-cluster lower crossing table.
This function is intended for ordered pairs `i < j`; on that support the only
exceptional pair is `(0,1)`. -/
def karlssonInterClusterCrossing (i j : Fin 4) : Rat :=
  if (i : Nat) = 0 ∧ (j : Nat) = 1 then 5 else 7

/-- Karlsson's four-cluster crossing count as a finite table sum over the
four cluster sizes. -/
def karlssonClusterTableCrossingsQ (m : Fin 4 → Rat) : Rat :=
  (∑ i : Fin 4, 4 * binomTwoQ (m i)) +
    karlssonInterClusterCrossing 0 1 * m 0 * m 1 +
    karlssonInterClusterCrossing 0 2 * m 0 * m 2 +
    karlssonInterClusterCrossing 0 3 * m 0 * m 3 +
    karlssonInterClusterCrossing 1 2 * m 1 * m 2 +
    karlssonInterClusterCrossing 1 3 * m 1 * m 3 +
    karlssonInterClusterCrossing 2 3 * m 2 * m 3

/-- The finite table-sum form is exactly the lower crossing polynomial used
throughout the theorem stack. -/
theorem karlssonClusterTableCrossingsQ_eq_lowerCrossingsQ
    (m : Fin 4 → Rat) :
    karlssonClusterTableCrossingsQ m =
      lowerCrossingsQ (m 0) (m 1) (m 2) (m 3) := by
  unfold karlssonClusterTableCrossingsQ lowerCrossingsQ
    karlssonInterClusterCrossing binomTwoQ
  norm_num [Fin.sum_univ_four]
  ring

/-- Karlsson's four-cluster table count for a bounded integer quadruple. -/
def karlssonClusterTableCrossingsOfQuad {n : Nat} (q : QuadVec n) : Rat :=
  karlssonClusterTableCrossingsQ (fun i => quadEntry q i)

/-- The table count attached to a quadruple is the existing lower crossing
count attached to that quadruple. -/
theorem karlssonClusterTableCrossingsOfQuad_eq_lowerCrossingsOfQuad
    {n : Nat} (q : QuadVec n) :
    karlssonClusterTableCrossingsOfQuad q = lowerCrossingsOfQuad q := by
  unfold karlssonClusterTableCrossingsOfQuad lowerCrossingsOfQuad
  exact karlssonClusterTableCrossingsQ_eq_lowerCrossingsQ
    (fun i => quadEntry q i)

/-- Named sorted Karlsson blow-up construction whose crossing count is
certified by the four-cluster table sum. -/
structure KarlssonTableBlowUpLowerData
    (P : TheoremOne.ProblemFamily.{u}) where
  crossings : (n : Nat) → P.Arrangement n → Rat
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  crossings_eq_table :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      crossings n (arrangement n q hq) =
        karlssonClusterTableCrossingsOfQuad q
  regions_eq :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      P.region n (arrangement n q hq) =
        crossings n (arrangement n q hq) + (n : Rat) + 1

namespace KarlssonTableBlowUpLowerData

/-- Forget the table presentation after Lean has rewritten it to
`lowerCrossingsOfQuad`. -/
def toKarlssonBlowUpLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonTableBlowUpLowerData P) :
    KarlssonBlowUpLowerData P where
  crossings := h.crossings
  arrangement := h.arrangement
  crossings_eq_lower := by
    intro n q hq
    rw [h.crossings_eq_table n q hq,
      karlssonClusterTableCrossingsOfQuad_eq_lowerCrossingsOfQuad]
  regions_eq := h.regions_eq

/-- Table-shaped lower data imply the sorted lower-realization package. -/
def toSortedKarlssonLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonTableBlowUpLowerData P) :
    SortedKarlssonLowerData P :=
  h.toKarlssonBlowUpLowerData.toSortedKarlssonLowerData

end KarlssonTableBlowUpLowerData

/-- Named sorted Karlsson blow-up construction with the lower region equation
proved from incremental insertion data and the crossing count certified by
the four-cluster table sum. -/
structure KarlssonTableBlowUpIncrementalLowerData
    (P : TheoremOne.ProblemFamily.{u}) where
  crossings : (n : Nat) → P.Arrangement n → Rat
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  crossings_eq_table :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      crossings n (arrangement n q hq) =
        karlssonClusterTableCrossingsOfQuad q
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      IncrementalRegionData n
        (P.region n (arrangement n q hq))
        (crossings n (arrangement n q hq))

namespace KarlssonTableBlowUpIncrementalLowerData

/-- Forget the incremental region proof after deriving the direct region
equation, retaining the table-shaped crossing certification. -/
def toKarlssonTableBlowUpLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonTableBlowUpIncrementalLowerData P) :
    KarlssonTableBlowUpLowerData P where
  crossings := h.crossings
  arrangement := h.arrangement
  crossings_eq_table := h.crossings_eq_table
  regions_eq := by
    intro n q hq
    exact (h.region_increment n q hq).target_eq_totalCrossings_add

/-- Convert the table-shaped incremental lower construction to the existing
named blow-up construction interface. -/
def toKarlssonBlowUpIncrementalLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonTableBlowUpIncrementalLowerData P) :
    KarlssonBlowUpIncrementalLowerData P where
  crossings := h.crossings
  arrangement := h.arrangement
  crossings_eq_lower := by
    intro n q hq
    rw [h.crossings_eq_table n q hq,
      karlssonClusterTableCrossingsOfQuad_eq_lowerCrossingsOfQuad]
  region_increment := h.region_increment

/-- Table-shaped incremental lower data imply the existing incremental sorted
lower-realization package. -/
def toSortedKarlssonIncrementalLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonTableBlowUpIncrementalLowerData P) :
    SortedKarlssonIncrementalLowerData P :=
  h.toKarlssonBlowUpIncrementalLowerData.toSortedKarlssonIncrementalLowerData

end KarlssonTableBlowUpIncrementalLowerData

end ExplicitInputs
end TheoremOneManuscript
end Lollipop

/-!
Proof component 5: `Manuscript.ExplicitInputs.ClusteredLower`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Clustered Karlsson lower construction data.

`LowerTable.lean` certifies a lower arrangement by the four cluster sizes
alone.  This file exposes one more layer of the blow-up construction: the
constructed `n` lollipops carry a cluster map into the four Karlsson base
lollipops, individual unordered lollipop pairs are counted by the corresponding
same-cluster/inter-cluster table value, and the individual-pair sum collapses
to the four-cluster table count.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace ExplicitInputs

universe u

/-- Symmetric pair contribution determined by two cluster labels in the
Karlsson blow-up: copies in the same cluster contribute `4`; the two
exceptional clusters `0` and `1` contribute `5`; all other inter-cluster pairs
contribute `7`. -/
def karlssonClusterPairCrossing (a b : Fin 4) : Rat :=
  if a = b then
    4
  else if ((a : Nat) = 0 ∧ (b : Nat) = 1) ∨
      ((a : Nat) = 1 ∧ (b : Nat) = 0) then
    5
  else
    7

/-- Nat-valued version of the same `4/5/7` cluster table.  This is useful for
finite lower witnesses, whose sizes are natural numbers. -/
def karlssonClusterPairCrossingNat (a b : Fin 4) : Nat :=
  if a = b then
    4
  else if ((a : Nat) = 0 ∧ (b : Nat) = 1) ∨
      ((a : Nat) = 1 ∧ (b : Nat) = 0) then
    5
  else
    7

/-- The Nat-valued cluster table coerces to the rational cluster table. -/
theorem karlssonClusterPairCrossing_eq_nat (a b : Fin 4) :
    karlssonClusterPairCrossing a b =
      (karlssonClusterPairCrossingNat a b : Rat) := by
  unfold karlssonClusterPairCrossing karlssonClusterPairCrossingNat
  by_cases hab : a = b
  · simp [hab]
  · by_cases hex :
        ((a : Nat) = 0 ∧ (b : Nat) = 1) ∨
        ((a : Nat) = 1 ∧ (b : Nat) = 0)
    · simp [hab]
    · simp [hab]

theorem karlssonClusterPairCrossing_same (a : Fin 4) :
    karlssonClusterPairCrossing a a = 4 := by
  simp [karlssonClusterPairCrossing]

theorem karlssonClusterPairCrossing_symm (a b : Fin 4) :
    karlssonClusterPairCrossing a b =
      karlssonClusterPairCrossing b a := by
  unfold karlssonClusterPairCrossing
  by_cases hab : a = b
  · subst b
    simp
  · have hba : b ≠ a := by
      intro h
      exact hab h.symm
    simp [hab, hba, and_comm, or_comm]

/-- Individual-pair Karlsson table sum for a chosen cluster map on the `n`
lollipops. -/
def clusteredKarlssonPairTableCrossings
    {n : Nat} (cluster : Fin n → Fin 4) : Rat :=
  pairSum n (fun i j => karlssonClusterPairCrossing (cluster i) (cluster j))

/-- A cluster map whose fibers have the desired quadruple sizes and whose
individual-pair table sum collapses to the four-cluster Karlsson table. -/
structure ClusteredKarlssonTableWitness {n : Nat} (q : QuadVec n) where
  cluster : Fin n → Fin 4
  cluster_card_eq :
    ∀ r : Fin 4,
      (((Finset.univ : Finset (Fin n)).filter
        (fun i => cluster i = r)).card : Rat) = quadEntry q r
  pairSum_eq_table :
    clusteredKarlssonPairTableCrossings cluster =
      karlssonClusterTableCrossingsOfQuad q

/-- Named sorted Karlsson blow-up construction whose crossing count is
certified by a cluster map on the produced lollipops. -/
structure ClusteredKarlssonBlowUpLowerData
    (P : TheoremOne.ProblemFamily.{u}) where
  crossings : (n : Nat) → P.Arrangement n → Rat
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  cluster_witness :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      ClusteredKarlssonTableWitness q
  crossings_eq_clustered_pair_sum :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      crossings n (arrangement n q hq) =
        clusteredKarlssonPairTableCrossings
          ((cluster_witness n q hq).cluster)
  regions_eq :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      P.region n (arrangement n q hq) =
        crossings n (arrangement n q hq) + (n : Rat) + 1

namespace ClusteredKarlssonBlowUpLowerData

/-- Forget the individual cluster map after Lean collapses the pair sum to
the four-cluster table. -/
def toKarlssonTableBlowUpLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ClusteredKarlssonBlowUpLowerData P) :
    KarlssonTableBlowUpLowerData P where
  crossings := h.crossings
  arrangement := h.arrangement
  crossings_eq_table := by
    intro n q hq
    rw [h.crossings_eq_clustered_pair_sum n q hq,
      (h.cluster_witness n q hq).pairSum_eq_table]
  regions_eq := h.regions_eq

end ClusteredKarlssonBlowUpLowerData

/-- Named sorted Karlsson blow-up construction with incremental lower region
data and a cluster map on the produced lollipops. -/
structure ClusteredKarlssonBlowUpIncrementalLowerData
    (P : TheoremOne.ProblemFamily.{u}) where
  crossings : (n : Nat) → P.Arrangement n → Rat
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  cluster_witness :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      ClusteredKarlssonTableWitness q
  crossings_eq_clustered_pair_sum :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      crossings n (arrangement n q hq) =
        clusteredKarlssonPairTableCrossings
          ((cluster_witness n q hq).cluster)
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      IncrementalRegionData n
        (P.region n (arrangement n q hq))
        (crossings n (arrangement n q hq))

namespace ClusteredKarlssonBlowUpIncrementalLowerData

/-- Forget incremental region data after deriving the direct region equation. -/
def toClusteredKarlssonBlowUpLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ClusteredKarlssonBlowUpIncrementalLowerData P) :
    ClusteredKarlssonBlowUpLowerData P where
  crossings := h.crossings
  arrangement := h.arrangement
  cluster_witness := h.cluster_witness
  crossings_eq_clustered_pair_sum := h.crossings_eq_clustered_pair_sum
  regions_eq := by
    intro n q hq
    exact (h.region_increment n q hq).target_eq_totalCrossings_add

/-- Convert clustered incremental lower data to the four-cluster table lower
interface. -/
def toKarlssonTableBlowUpIncrementalLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ClusteredKarlssonBlowUpIncrementalLowerData P) :
    KarlssonTableBlowUpIncrementalLowerData P where
  crossings := h.crossings
  arrangement := h.arrangement
  crossings_eq_table := by
    intro n q hq
    rw [h.crossings_eq_clustered_pair_sum n q hq,
      (h.cluster_witness n q hq).pairSum_eq_table]
  region_increment := h.region_increment

end ClusteredKarlssonBlowUpIncrementalLowerData

end ExplicitInputs
end TheoremOneManuscript
end Lollipop

/-!
Proof component 6: `Manuscript.ExplicitInputs.PairCountedClusteredLower`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Pair-counted clustered Karlsson lower construction data.

`ClusteredLower.lean` exposes the individual cluster map, but its witness still
contains the collapsed equality from the individual-pair sum to the
four-cluster Karlsson table.  This module splits that equality into finite
pair-count facts.  Lean proves:

* the individual pair sum is the sum over oriented cluster-label pair counts;
* the oriented count table collapses to Karlsson's six unordered inter-cluster
  terms plus the four same-cluster terms;
* the resulting table is the already-checked lower polynomial.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace ExplicitInputs

universe u

open BigOperators

/-- Fiber of a cluster map over one Karlsson base cluster. -/
def clusterFiber {n : Nat} (cluster : Fin n → Fin 4) (r : Fin 4) :
    Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun i => cluster i = r)

/-- The `pairFinset` pairs whose two endpoints lie in a subset `s` are counted
by `#s choose 2`.  This is the subset version of `pairFinset_card`. -/
theorem pairFinset_filter_mem_card
    {n : Nat} (s : Finset (Fin n)) :
    ((pairFinset n).filter (fun p : Fin n × Fin n => p.1 ∈ s ∧ p.2 ∈ s)).card =
      s.card.choose 2 := by
  classical
  have hfilter :
      (pairFinset n).filter (fun p : Fin n × Fin n => p.1 ∈ s ∧ p.2 ∈ s) =
        s.offDiag.filter (fun p : Fin n × Fin n => p.1 < p.2) := by
    ext p
    by_cases hlt : p.1 < p.2
    · simp [pairFinset, Finset.mem_offDiag, hlt, ne_of_lt hlt,
        and_comm]
    · simp [pairFinset, Finset.mem_offDiag, hlt]
  rw [hfilter]
  have hsum :=
    Finset.sum_sym2_filter_not_isDiag (s := s) (p := fun _ => (1 : Nat))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  have hsumNat :
      (s.sym2.filter fun a : Sym2 (Fin n) => ¬a.IsDiag).card =
        (s.offDiag.filter fun p : Fin n × Fin n => p.1 < p.2).card := by
    exact_mod_cast hsum
  rw [← hsumNat, Finset.sym2_eq_image, Sym2.filter_image_mk_not_isDiag]
  exact Sym2.card_image_offDiag s

/-- For two disjoint subsets, the two canonical orientations of inter-set
pairs in `pairFinset` add up to the product of the subset cardinalities. -/
theorem pairFinset_filter_inter_card
    {n : Nat} (s t : Finset (Fin n)) (hst : Disjoint s t) :
    ((pairFinset n).filter
        (fun p : Fin n × Fin n => p.1 ∈ s ∧ p.2 ∈ t)).card +
      ((pairFinset n).filter
        (fun p : Fin n × Fin n => p.1 ∈ t ∧ p.2 ∈ s)).card =
        s.card * t.card := by
  classical
  let stLT : Finset (Fin n × Fin n) :=
    (s ×ˢ t).filter (fun p : Fin n × Fin n => p.1 < p.2)
  let stGT : Finset (Fin n × Fin n) :=
    (s ×ˢ t).filter (fun p : Fin n × Fin n => p.2 < p.1)
  have hfirst :
      stLT =
        (pairFinset n).filter
          (fun p : Fin n × Fin n => p.1 ∈ s ∧ p.2 ∈ t) := by
    ext p
    simp [stLT, pairFinset, and_comm]
  let swapEmbedding : Fin n × Fin n ↪ Fin n × Fin n :=
    { toFun := fun p => (p.2, p.1)
      inj' := by
        intro p q h
        cases p
        cases q
        simp at h
        simp [h.1, h.2] }
  have hmap :
      stGT.map swapEmbedding =
        (pairFinset n).filter
          (fun p : Fin n × Fin n => p.1 ∈ t ∧ p.2 ∈ s) := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_map.mp hp with ⟨q, hq, hqp⟩
      simp [stGT] at hq
      rw [← hqp]
      simp [swapEmbedding, pairFinset, hq.1.1, hq.1.2, hq.2]
    · intro hp
      simp [pairFinset] at hp
      refine Finset.mem_map.mpr ⟨(p.2, p.1), ?_, ?_⟩
      · simp [stGT, hp.2.2, hp.2.1, hp.1]
      · simp [swapEmbedding]
  have hsecond :
      stGT.card =
        ((pairFinset n).filter
          (fun p : Fin n × Fin n => p.1 ∈ t ∧ p.2 ∈ s)).card := by
    rw [← hmap, Finset.card_map]
  have hsplit : s ×ˢ t = stLT ∪ stGT := by
    ext p
    constructor
    · intro hp
      have hps : p.1 ∈ s := (Finset.mem_product.mp hp).1
      have hpt : p.2 ∈ t := (Finset.mem_product.mp hp).2
      have hne : p.1 ≠ p.2 := by
        intro hp_eq
        have hp2s : p.2 ∈ s := by simpa [hp_eq] using hps
        exact (Finset.disjoint_left.mp hst) hp2s hpt
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Finset.mem_union.mpr (Or.inl (by simp [stLT, hp, hlt]))
      · exact Finset.mem_union.mpr (Or.inr (by simp [stGT, hp, hgt]))
    · intro hp
      rcases Finset.mem_union.mp hp with hp | hp
      · exact (Finset.mem_filter.mp hp).1
      · exact (Finset.mem_filter.mp hp).1
  have hdisj : Disjoint stLT stGT := by
    rw [Finset.disjoint_left]
    intro p hpLT hpGT
    have hlt : p.1 < p.2 := (Finset.mem_filter.mp hpLT).2
    have hgt : p.2 < p.1 := (Finset.mem_filter.mp hpGT).2
    exact (not_lt_of_gt hgt) hlt
  have hcard :
      (s ×ˢ t).card = stLT.card + stGT.card := by
    rw [hsplit, Finset.card_union_of_disjoint hdisj]
  rw [← hfirst, ← hsecond]
  rw [← Finset.card_product]
  exact hcard.symm

/-- Number of unordered lollipop pairs, represented by `pairFinset n`, whose
first representative lies in cluster `a` and second representative lies in
cluster `b`.  The orientation is only the canonical `i < j` orientation of the
underlying unordered pair; later inter-cluster hypotheses add both directions. -/
def orientedClusterPairCountQ
    {n : Nat} (cluster : Fin n → Fin 4) (a b : Fin 4) : Rat :=
  (((pairFinset n).filter
    (fun p : Fin n × Fin n => cluster p.1 = a ∧ cluster p.2 = b)).card : Rat)

/-- Karlsson's individual-pair sum regrouped by oriented cluster labels. -/
def orientedKarlssonPairCountedCrossings
    {n : Nat} (cluster : Fin n → Fin 4) : Rat :=
  ∑ a : Fin 4, ∑ b : Fin 4,
    karlssonClusterPairCrossing a b *
      orientedClusterPairCountQ cluster a b

theorem orientedClusterPairCountQ_eq_indicator_sum
    {n : Nat} (cluster : Fin n → Fin 4) (a b : Fin 4) :
    orientedClusterPairCountQ cluster a b =
      ∑ p ∈ pairFinset n,
        if cluster p.1 = a ∧ cluster p.2 = b then (1 : Rat) else 0 := by
  unfold orientedClusterPairCountQ
  rw [Finset.card_eq_sum_ones]
  simp

/-- Same-cluster oriented pair counts are determined by the cluster fiber
cardinality. -/
theorem orientedClusterPairCountQ_same_eq_fiber_choose
    {n : Nat} (cluster : Fin n → Fin 4) (r : Fin 4) :
    orientedClusterPairCountQ cluster r r =
      (((clusterFiber cluster r).card.choose 2 : Nat) : Rat) := by
  let s := clusterFiber cluster r
  have hnat := pairFinset_filter_mem_card (n := n) s
  have hrat :
      (((pairFinset n).filter
        (fun p : Fin n × Fin n => p.1 ∈ s ∧ p.2 ∈ s)).card : Rat) =
        ((s.card.choose 2 : Nat) : Rat) := by
    exact_mod_cast hnat
  simpa [orientedClusterPairCountQ, clusterFiber, s] using hrat

/-- If a cluster fiber has rational size `m`, its same-cluster pair count is
`m choose 2`. -/
theorem orientedClusterPairCountQ_same_eq_binomTwoQ_of_card
    {n : Nat} {q : QuadVec n} {cluster : Fin n → Fin 4}
    (hcard :
      ∀ r : Fin 4,
        (((clusterFiber cluster r).card : Nat) : Rat) = quadEntry q r)
    (r : Fin 4) :
    orientedClusterPairCountQ cluster r r =
      binomTwoQ (quadEntry q r) := by
  rw [orientedClusterPairCountQ_same_eq_fiber_choose]
  unfold binomTwoQ
  rw [← hcard r]
  rw [Nat.cast_choose_two]

/-- Inter-cluster oriented pair counts are determined by the two cluster fiber
cardinalities. -/
theorem orientedClusterPairCountQ_inter_add_eq_fiber_mul
    {n : Nat} (cluster : Fin n → Fin 4) {a b : Fin 4}
    (hab : a ≠ b) :
    orientedClusterPairCountQ cluster a b +
      orientedClusterPairCountQ cluster b a =
        (((clusterFiber cluster a).card *
          (clusterFiber cluster b).card : Nat) : Rat) := by
  let s := clusterFiber cluster a
  let t := clusterFiber cluster b
  have hdisj : Disjoint s t := by
    rw [Finset.disjoint_left]
    intro i his hit
    have hia : cluster i = a := by
      simpa [s, clusterFiber] using his
    have hib : cluster i = b := by
      simpa [t, clusterFiber] using hit
    exact hab (hia.symm.trans hib)
  have hnat := pairFinset_filter_inter_card (n := n) s t hdisj
  have hrat :
      (((pairFinset n).filter
          (fun p : Fin n × Fin n => p.1 ∈ s ∧ p.2 ∈ t)).card : Rat) +
        (((pairFinset n).filter
          (fun p : Fin n × Fin n => p.1 ∈ t ∧ p.2 ∈ s)).card : Rat) =
          (((s.card * t.card : Nat)) : Rat) := by
    exact_mod_cast hnat
  simpa [orientedClusterPairCountQ, clusterFiber, s, t] using hrat

/-- If two cluster fibers have rational sizes `m_a` and `m_b`, their unordered
inter-cluster pair count is `m_a * m_b`. -/
theorem orientedClusterPairCountQ_inter_add_eq_mul_of_card
    {n : Nat} {q : QuadVec n} {cluster : Fin n → Fin 4}
    (hcard :
      ∀ r : Fin 4,
        (((clusterFiber cluster r).card : Nat) : Rat) = quadEntry q r)
    {a b : Fin 4} (hab : a ≠ b) :
    orientedClusterPairCountQ cluster a b +
      orientedClusterPairCountQ cluster b a =
        quadEntry q a * quadEntry q b := by
  rw [orientedClusterPairCountQ_inter_add_eq_fiber_mul cluster hab]
  rw [Nat.cast_mul, hcard a, hcard b]

theorem clusteredKarlssonPairTableCrossings_eq_orientedPairCounted
    {n : Nat} (cluster : Fin n → Fin 4) :
    clusteredKarlssonPairTableCrossings cluster =
      orientedKarlssonPairCountedCrossings cluster := by
  unfold clusteredKarlssonPairTableCrossings pairSum
  unfold orientedKarlssonPairCountedCrossings
  simp_rw [orientedClusterPairCountQ_eq_indicator_sum]
  simp_rw [Finset.mul_sum]
  symm
  calc
    (∑ a : Fin 4, ∑ b : Fin 4, ∑ p ∈ pairFinset n,
        karlssonClusterPairCrossing a b *
          (if cluster p.1 = a ∧ cluster p.2 = b then (1 : Rat) else 0))
        =
      ∑ a : Fin 4, ∑ p ∈ pairFinset n, ∑ b : Fin 4,
        karlssonClusterPairCrossing a b *
          (if cluster p.1 = a ∧ cluster p.2 = b then (1 : Rat) else 0) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm]
    _ =
      ∑ p ∈ pairFinset n, ∑ a : Fin 4, ∑ b : Fin 4,
        karlssonClusterPairCrossing a b *
          (if cluster p.1 = a ∧ cluster p.2 = b then (1 : Rat) else 0) := by
        rw [Finset.sum_comm]
    _ =
      ∑ p ∈ pairFinset n,
        karlssonClusterPairCrossing (cluster p.1) (cluster p.2) := by
        apply Finset.sum_congr rfl
        intro p _
        rw [Fintype.sum_eq_single (cluster p.1)]
        · rw [Fintype.sum_eq_single (cluster p.2)]
          · simp
          · intro b hb
            simp [hb.symm]
        · intro a ha
          rw [Fintype.sum_eq_zero]
          intro b
          simp [ha.symm]

/-- Pair-counted cluster witness.  Same-cluster counts are supplied directly;
for distinct cluster labels the two possible orientations in `pairFinset n`
are supplied as one unordered count. -/
structure PairCountedClusteredKarlssonTableWitness
    {n : Nat} (q : QuadVec n) where
  cluster : Fin n → Fin 4
  cluster_card_eq :
    ∀ r : Fin 4,
      (((Finset.univ : Finset (Fin n)).filter
        (fun i => cluster i = r)).card : Rat) = quadEntry q r
  same_pair_count_eq :
    ∀ r : Fin 4,
      orientedClusterPairCountQ cluster r r =
        binomTwoQ (quadEntry q r)
  inter_pair_count_eq_zero_one :
    orientedClusterPairCountQ cluster 0 1 +
      orientedClusterPairCountQ cluster 1 0 =
        quadEntry q 0 * quadEntry q 1
  inter_pair_count_eq_zero_two :
    orientedClusterPairCountQ cluster 0 2 +
      orientedClusterPairCountQ cluster 2 0 =
        quadEntry q 0 * quadEntry q 2
  inter_pair_count_eq_zero_three :
    orientedClusterPairCountQ cluster 0 3 +
      orientedClusterPairCountQ cluster 3 0 =
        quadEntry q 0 * quadEntry q 3
  inter_pair_count_eq_one_two :
    orientedClusterPairCountQ cluster 1 2 +
      orientedClusterPairCountQ cluster 2 1 =
        quadEntry q 1 * quadEntry q 2
  inter_pair_count_eq_one_three :
    orientedClusterPairCountQ cluster 1 3 +
      orientedClusterPairCountQ cluster 3 1 =
        quadEntry q 1 * quadEntry q 3
  inter_pair_count_eq_two_three :
    orientedClusterPairCountQ cluster 2 3 +
      orientedClusterPairCountQ cluster 3 2 =
        quadEntry q 2 * quadEntry q 3

namespace PairCountedClusteredKarlssonTableWitness

theorem orientedPairCounted_eq_table
    {n : Nat} {q : QuadVec n}
    (w : PairCountedClusteredKarlssonTableWitness q) :
    orientedKarlssonPairCountedCrossings w.cluster =
      karlssonClusterTableCrossingsOfQuad q := by
  unfold orientedKarlssonPairCountedCrossings
    karlssonClusterTableCrossingsOfQuad karlssonClusterTableCrossingsQ
    karlssonClusterPairCrossing karlssonInterClusterCrossing
  simp [Fin.sum_univ_four, w.same_pair_count_eq 0, w.same_pair_count_eq 1,
    w.same_pair_count_eq 2, w.same_pair_count_eq 3]
  nlinarith [w.inter_pair_count_eq_zero_one,
    w.inter_pair_count_eq_zero_two,
    w.inter_pair_count_eq_zero_three,
    w.inter_pair_count_eq_one_two,
    w.inter_pair_count_eq_one_three,
    w.inter_pair_count_eq_two_three]

theorem pairSum_eq_table
    {n : Nat} {q : QuadVec n}
    (w : PairCountedClusteredKarlssonTableWitness q) :
    clusteredKarlssonPairTableCrossings w.cluster =
      karlssonClusterTableCrossingsOfQuad q := by
  rw [clusteredKarlssonPairTableCrossings_eq_orientedPairCounted]
  exact w.orientedPairCounted_eq_table

/-- Forget the explicit pair-count equations after Lean has collapsed them to
the older clustered witness interface. -/
def toClusteredKarlssonTableWitness
    {n : Nat} {q : QuadVec n}
    (w : PairCountedClusteredKarlssonTableWitness q) :
    ClusteredKarlssonTableWitness q where
  cluster := w.cluster
  cluster_card_eq := w.cluster_card_eq
  pairSum_eq_table := w.pairSum_eq_table

end PairCountedClusteredKarlssonTableWitness

/-- A lighter cluster witness: same-cluster pair counts are not fields, because
Lean derives them from the fiber cardinalities.  The six inter-cluster counts
remain explicit finite counting obligations. -/
structure FiberCountedClusteredKarlssonTableWitness
    {n : Nat} (q : QuadVec n) where
  cluster : Fin n → Fin 4
  cluster_card_eq :
    ∀ r : Fin 4,
      (((clusterFiber cluster r).card : Nat) : Rat) = quadEntry q r
  inter_pair_count_eq_zero_one :
    orientedClusterPairCountQ cluster 0 1 +
      orientedClusterPairCountQ cluster 1 0 =
        quadEntry q 0 * quadEntry q 1
  inter_pair_count_eq_zero_two :
    orientedClusterPairCountQ cluster 0 2 +
      orientedClusterPairCountQ cluster 2 0 =
        quadEntry q 0 * quadEntry q 2
  inter_pair_count_eq_zero_three :
    orientedClusterPairCountQ cluster 0 3 +
      orientedClusterPairCountQ cluster 3 0 =
        quadEntry q 0 * quadEntry q 3
  inter_pair_count_eq_one_two :
    orientedClusterPairCountQ cluster 1 2 +
      orientedClusterPairCountQ cluster 2 1 =
        quadEntry q 1 * quadEntry q 2
  inter_pair_count_eq_one_three :
    orientedClusterPairCountQ cluster 1 3 +
      orientedClusterPairCountQ cluster 3 1 =
        quadEntry q 1 * quadEntry q 3
  inter_pair_count_eq_two_three :
    orientedClusterPairCountQ cluster 2 3 +
      orientedClusterPairCountQ cluster 3 2 =
        quadEntry q 2 * quadEntry q 3

namespace FiberCountedClusteredKarlssonTableWitness

/-- Add the derived same-cluster pair-count equations, obtaining the stronger
pair-counted witness interface. -/
def toPairCountedClusteredKarlssonTableWitness
    {n : Nat} {q : QuadVec n}
    (w : FiberCountedClusteredKarlssonTableWitness q) :
    PairCountedClusteredKarlssonTableWitness q where
  cluster := w.cluster
  cluster_card_eq := by
    intro r
    simpa [clusterFiber] using w.cluster_card_eq r
  same_pair_count_eq := by
    intro r
    exact orientedClusterPairCountQ_same_eq_binomTwoQ_of_card
      w.cluster_card_eq r
  inter_pair_count_eq_zero_one := w.inter_pair_count_eq_zero_one
  inter_pair_count_eq_zero_two := w.inter_pair_count_eq_zero_two
  inter_pair_count_eq_zero_three := w.inter_pair_count_eq_zero_three
  inter_pair_count_eq_one_two := w.inter_pair_count_eq_one_two
  inter_pair_count_eq_one_three := w.inter_pair_count_eq_one_three
  inter_pair_count_eq_two_three := w.inter_pair_count_eq_two_three

theorem pairSum_eq_table
    {n : Nat} {q : QuadVec n}
    (w : FiberCountedClusteredKarlssonTableWitness q) :
    clusteredKarlssonPairTableCrossings w.cluster =
      karlssonClusterTableCrossingsOfQuad q :=
  w.toPairCountedClusteredKarlssonTableWitness.pairSum_eq_table

end FiberCountedClusteredKarlssonTableWitness

/-- Strongest finite-counting cluster witness in this file.  It supplies only
a cluster map whose four fibers have the desired cardinalities.  Lean derives
all four same-cluster counts and all six inter-cluster counts. -/
structure CardinalityClusteredKarlssonTableWitness
    {n : Nat} (q : QuadVec n) where
  cluster : Fin n → Fin 4
  cluster_card_eq :
    ∀ r : Fin 4,
      (((clusterFiber cluster r).card : Nat) : Rat) = quadEntry q r

namespace CardinalityClusteredKarlssonTableWitness

def toFiberCountedClusteredKarlssonTableWitness
    {n : Nat} {q : QuadVec n}
    (w : CardinalityClusteredKarlssonTableWitness q) :
    FiberCountedClusteredKarlssonTableWitness q where
  cluster := w.cluster
  cluster_card_eq := w.cluster_card_eq
  inter_pair_count_eq_zero_one :=
    orientedClusterPairCountQ_inter_add_eq_mul_of_card
      w.cluster_card_eq (by decide)
  inter_pair_count_eq_zero_two :=
    orientedClusterPairCountQ_inter_add_eq_mul_of_card
      w.cluster_card_eq (by decide)
  inter_pair_count_eq_zero_three :=
    orientedClusterPairCountQ_inter_add_eq_mul_of_card
      w.cluster_card_eq (by decide)
  inter_pair_count_eq_one_two :=
    orientedClusterPairCountQ_inter_add_eq_mul_of_card
      w.cluster_card_eq (by decide)
  inter_pair_count_eq_one_three :=
    orientedClusterPairCountQ_inter_add_eq_mul_of_card
      w.cluster_card_eq (by decide)
  inter_pair_count_eq_two_three :=
    orientedClusterPairCountQ_inter_add_eq_mul_of_card
      w.cluster_card_eq (by decide)

def toPairCountedClusteredKarlssonTableWitness
    {n : Nat} {q : QuadVec n}
    (w : CardinalityClusteredKarlssonTableWitness q) :
    PairCountedClusteredKarlssonTableWitness q :=
  w.toFiberCountedClusteredKarlssonTableWitness.toPairCountedClusteredKarlssonTableWitness

theorem pairSum_eq_table
    {n : Nat} {q : QuadVec n}
    (w : CardinalityClusteredKarlssonTableWitness q) :
    clusteredKarlssonPairTableCrossings w.cluster =
      karlssonClusterTableCrossingsOfQuad q :=
  w.toFiberCountedClusteredKarlssonTableWitness.pairSum_eq_table

end CardinalityClusteredKarlssonTableWitness

/-- The finite type containing one element for each intended lollipop in each
of the four clusters of a quadruple. -/
abbrev quadClusterIndex {n : Nat} (q : QuadVec n) : Type :=
  Σ r : Fin 4, Fin ((q r : Nat))

theorem quadClusterIndex_card {n : Nat} {q : QuadVec n}
    (hq : q ∈ quadVecs n) :
    Fintype.card (quadClusterIndex q) = n := by
  rw [quadVecs, Finset.mem_filter] at hq
  have hsum : (∑ r : Fin 4, (q r : Nat)) = n := by
    simpa [quadVecSum] using hq.2
  simp [quadClusterIndex, hsum]

/-- Noncomputably identify `Fin n` with the disjoint union of four finite
cluster fibers having sizes prescribed by `q`. -/
noncomputable def quadClusterEquiv {n : Nat} (q : QuadVec n)
    (hq : q ∈ quadVecs n) :
    Fin n ≃ quadClusterIndex q :=
  (Fintype.equivFinOfCardEq (quadClusterIndex_card (q := q) hq)).symm

/-- Canonical cluster map obtained from the first coordinate of the finite
equivalence with the disjoint union of four fibers. -/
noncomputable def canonicalQuadCluster {n : Nat} (q : QuadVec n)
    (hq : q ∈ quadVecs n) :
    Fin n → Fin 4 :=
  fun i => (quadClusterEquiv q hq i).1

/-- The subtype of the sigma cluster index over one fixed cluster is exactly
that cluster's finite fiber. -/
def quadClusterIndexFiberEquiv {n : Nat} (q : QuadVec n) (r : Fin 4) :
    {x : quadClusterIndex q // x.1 = r} ≃ Fin ((q r : Nat)) where
  toFun x :=
    Fin.cast (by
      exact congrArg (fun s : Fin 4 => (q s : Nat)) x.2) x.1.2
  invFun y := ⟨⟨r, y⟩, rfl⟩
  left_inv := by
    intro x
    rcases x with ⟨⟨s, y⟩, hsr⟩
    subst hsr
    simp
  right_inv := by
    intro y
    simp

theorem canonicalQuadCluster_card_eq
    {n : Nat} (q : QuadVec n) (hq : q ∈ quadVecs n) (r : Fin 4) :
    (((clusterFiber (canonicalQuadCluster q hq) r).card : Nat) : Rat) =
      quadEntry q r := by
  let e := quadClusterEquiv q hq
  let cluster := canonicalQuadCluster q hq
  have hmem :
      ∀ i : Fin n, i ∈ clusterFiber cluster r ↔ cluster i = r := by
    intro i
    simp [clusterFiber]
  let memEquiv :
      {i : Fin n // i ∈ clusterFiber cluster r} ≃
        {i : Fin n // cluster i = r} :=
    Equiv.subtypeEquivRight hmem
  have hsub :
      ∀ i : Fin n, cluster i = r ↔ (e i).1 = r := by
    intro i
    rfl
  let imageEquiv :
      {i : Fin n // cluster i = r} ≃
        {x : quadClusterIndex q // x.1 = r} :=
    e.subtypeEquiv hsub
  let fiberEquiv :
      {i : Fin n // i ∈ clusterFiber cluster r} ≃ Fin ((q r : Nat)) :=
    memEquiv.trans (imageEquiv.trans (quadClusterIndexFiberEquiv q r))
  have hcard :
      (clusterFiber cluster r).card = (q r : Nat) := by
    calc
      (clusterFiber cluster r).card =
          Fintype.card {i : Fin n // i ∈ clusterFiber cluster r} := by
            exact (Fintype.card_coe (clusterFiber cluster r)).symm
      _ = Fintype.card (Fin ((q r : Nat))) := Fintype.card_congr fiberEquiv
      _ = (q r : Nat) := Fintype.card_fin ((q r : Nat))
  rw [hcard]
  rfl

/-- Every admissible quadruple has a cardinality-clustered witness; all finite
same/inter-cluster pair counts are then derived internally. -/
noncomputable def cardinalityClusteredKarlssonTableWitnessOfQuad
    {n : Nat} (q : QuadVec n) (hq : q ∈ quadVecs n) :
    CardinalityClusteredKarlssonTableWitness q where
  cluster := canonicalQuadCluster q hq
  cluster_card_eq := canonicalQuadCluster_card_eq q hq

/-- A sorted quadruple has the canonical cardinality-clustered witness. -/
noncomputable def cardinalityClusteredKarlssonTableWitnessOfSortedQuad
    {n : Nat} (q : QuadVec n) (hq : q ∈ sortedQuadVecs n) :
    CardinalityClusteredKarlssonTableWitness q :=
  cardinalityClusteredKarlssonTableWitnessOfQuad q (by
    rw [sortedQuadVecs, Finset.mem_filter] at hq
    exact hq.1)

/-- Named sorted Karlsson blow-up construction whose lower crossing count is
certified by finite same/inter-cluster pair counts. -/
structure PairCountedClusteredKarlssonBlowUpLowerData
    (P : TheoremOne.ProblemFamily.{u}) where
  crossings : (n : Nat) → P.Arrangement n → Rat
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  cluster_witness :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      PairCountedClusteredKarlssonTableWitness q
  crossings_eq_clustered_pair_sum :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      crossings n (arrangement n q hq) =
        clusteredKarlssonPairTableCrossings
          ((cluster_witness n q hq).cluster)
  regions_eq :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      P.region n (arrangement n q hq) =
        crossings n (arrangement n q hq) + (n : Rat) + 1

namespace PairCountedClusteredKarlssonBlowUpLowerData

def toClusteredKarlssonBlowUpLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PairCountedClusteredKarlssonBlowUpLowerData P) :
    ClusteredKarlssonBlowUpLowerData P where
  crossings := h.crossings
  arrangement := h.arrangement
  cluster_witness := by
    intro n q hq
    exact (h.cluster_witness n q hq).toClusteredKarlssonTableWitness
  crossings_eq_clustered_pair_sum := h.crossings_eq_clustered_pair_sum
  regions_eq := h.regions_eq

def toKarlssonTableBlowUpLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PairCountedClusteredKarlssonBlowUpLowerData P) :
    KarlssonTableBlowUpLowerData P :=
  h.toClusteredKarlssonBlowUpLowerData.toKarlssonTableBlowUpLowerData

end PairCountedClusteredKarlssonBlowUpLowerData

/-- Incremental lower construction with pair-counted clustered table data. -/
structure PairCountedClusteredKarlssonBlowUpIncrementalLowerData
    (P : TheoremOne.ProblemFamily.{u}) where
  crossings : (n : Nat) → P.Arrangement n → Rat
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  cluster_witness :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      PairCountedClusteredKarlssonTableWitness q
  crossings_eq_clustered_pair_sum :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      crossings n (arrangement n q hq) =
        clusteredKarlssonPairTableCrossings
          ((cluster_witness n q hq).cluster)
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      IncrementalRegionData n
        (P.region n (arrangement n q hq))
        (crossings n (arrangement n q hq))

namespace PairCountedClusteredKarlssonBlowUpIncrementalLowerData

def toPairCountedClusteredKarlssonBlowUpLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PairCountedClusteredKarlssonBlowUpIncrementalLowerData P) :
    PairCountedClusteredKarlssonBlowUpLowerData P where
  crossings := h.crossings
  arrangement := h.arrangement
  cluster_witness := h.cluster_witness
  crossings_eq_clustered_pair_sum := h.crossings_eq_clustered_pair_sum
  regions_eq := by
    intro n q hq
    exact (h.region_increment n q hq).target_eq_totalCrossings_add

def toClusteredKarlssonBlowUpIncrementalLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PairCountedClusteredKarlssonBlowUpIncrementalLowerData P) :
    ClusteredKarlssonBlowUpIncrementalLowerData P where
  crossings := h.crossings
  arrangement := h.arrangement
  cluster_witness := by
    intro n q hq
    exact (h.cluster_witness n q hq).toClusteredKarlssonTableWitness
  crossings_eq_clustered_pair_sum := h.crossings_eq_clustered_pair_sum
  region_increment := h.region_increment

def toKarlssonTableBlowUpIncrementalLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PairCountedClusteredKarlssonBlowUpIncrementalLowerData P) :
    KarlssonTableBlowUpIncrementalLowerData P :=
  h.toClusteredKarlssonBlowUpIncrementalLowerData.toKarlssonTableBlowUpIncrementalLowerData

end PairCountedClusteredKarlssonBlowUpIncrementalLowerData

/-- Named sorted Karlsson blow-up construction whose same-cluster pair counts
are derived from cluster fiber cardinalities, with only the six inter-cluster
counts supplied explicitly. -/
structure FiberCountedClusteredKarlssonBlowUpLowerData
    (P : TheoremOne.ProblemFamily.{u}) where
  crossings : (n : Nat) → P.Arrangement n → Rat
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  cluster_witness :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      FiberCountedClusteredKarlssonTableWitness q
  crossings_eq_clustered_pair_sum :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      crossings n (arrangement n q hq) =
        clusteredKarlssonPairTableCrossings
          ((cluster_witness n q hq).cluster)
  regions_eq :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      P.region n (arrangement n q hq) =
        crossings n (arrangement n q hq) + (n : Rat) + 1

namespace FiberCountedClusteredKarlssonBlowUpLowerData

def toPairCountedClusteredKarlssonBlowUpLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : FiberCountedClusteredKarlssonBlowUpLowerData P) :
    PairCountedClusteredKarlssonBlowUpLowerData P where
  crossings := h.crossings
  arrangement := h.arrangement
  cluster_witness := by
    intro n q hq
    exact
      (h.cluster_witness n q hq).toPairCountedClusteredKarlssonTableWitness
  crossings_eq_clustered_pair_sum := h.crossings_eq_clustered_pair_sum
  regions_eq := h.regions_eq

def toClusteredKarlssonBlowUpLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : FiberCountedClusteredKarlssonBlowUpLowerData P) :
    ClusteredKarlssonBlowUpLowerData P :=
  h.toPairCountedClusteredKarlssonBlowUpLowerData.toClusteredKarlssonBlowUpLowerData

end FiberCountedClusteredKarlssonBlowUpLowerData

/-- Incremental lower construction with same-cluster pair counts derived from
cluster fiber cardinalities and explicit inter-cluster counts. -/
structure FiberCountedClusteredKarlssonBlowUpIncrementalLowerData
    (P : TheoremOne.ProblemFamily.{u}) where
  crossings : (n : Nat) → P.Arrangement n → Rat
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  cluster_witness :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      FiberCountedClusteredKarlssonTableWitness q
  crossings_eq_clustered_pair_sum :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      crossings n (arrangement n q hq) =
        clusteredKarlssonPairTableCrossings
          ((cluster_witness n q hq).cluster)
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      IncrementalRegionData n
        (P.region n (arrangement n q hq))
        (crossings n (arrangement n q hq))

namespace FiberCountedClusteredKarlssonBlowUpIncrementalLowerData

def toFiberCountedClusteredKarlssonBlowUpLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : FiberCountedClusteredKarlssonBlowUpIncrementalLowerData P) :
    FiberCountedClusteredKarlssonBlowUpLowerData P where
  crossings := h.crossings
  arrangement := h.arrangement
  cluster_witness := h.cluster_witness
  crossings_eq_clustered_pair_sum := h.crossings_eq_clustered_pair_sum
  regions_eq := by
    intro n q hq
    exact (h.region_increment n q hq).target_eq_totalCrossings_add

def toPairCountedClusteredKarlssonBlowUpIncrementalLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : FiberCountedClusteredKarlssonBlowUpIncrementalLowerData P) :
    PairCountedClusteredKarlssonBlowUpIncrementalLowerData P where
  crossings := h.crossings
  arrangement := h.arrangement
  cluster_witness := by
    intro n q hq
    exact
      (h.cluster_witness n q hq).toPairCountedClusteredKarlssonTableWitness
  crossings_eq_clustered_pair_sum := h.crossings_eq_clustered_pair_sum
  region_increment := h.region_increment

def toClusteredKarlssonBlowUpIncrementalLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : FiberCountedClusteredKarlssonBlowUpIncrementalLowerData P) :
    ClusteredKarlssonBlowUpIncrementalLowerData P :=
  h.toPairCountedClusteredKarlssonBlowUpIncrementalLowerData.toClusteredKarlssonBlowUpIncrementalLowerData

end FiberCountedClusteredKarlssonBlowUpIncrementalLowerData

/-- Named sorted Karlsson blow-up construction whose finite counting input is
only a cluster map with the required four fiber cardinalities. -/
structure CardinalityClusteredKarlssonBlowUpLowerData
    (P : TheoremOne.ProblemFamily.{u}) where
  crossings : (n : Nat) → P.Arrangement n → Rat
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  cluster_witness :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      CardinalityClusteredKarlssonTableWitness q
  crossings_eq_clustered_pair_sum :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      crossings n (arrangement n q hq) =
        clusteredKarlssonPairTableCrossings
          ((cluster_witness n q hq).cluster)
  regions_eq :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      P.region n (arrangement n q hq) =
        crossings n (arrangement n q hq) + (n : Rat) + 1

namespace CardinalityClusteredKarlssonBlowUpLowerData

def toFiberCountedClusteredKarlssonBlowUpLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CardinalityClusteredKarlssonBlowUpLowerData P) :
    FiberCountedClusteredKarlssonBlowUpLowerData P where
  crossings := h.crossings
  arrangement := h.arrangement
  cluster_witness := by
    intro n q hq
    exact
      (h.cluster_witness n q hq).toFiberCountedClusteredKarlssonTableWitness
  crossings_eq_clustered_pair_sum := h.crossings_eq_clustered_pair_sum
  regions_eq := h.regions_eq

def toPairCountedClusteredKarlssonBlowUpLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CardinalityClusteredKarlssonBlowUpLowerData P) :
    PairCountedClusteredKarlssonBlowUpLowerData P :=
  h.toFiberCountedClusteredKarlssonBlowUpLowerData.toPairCountedClusteredKarlssonBlowUpLowerData

def toClusteredKarlssonBlowUpLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CardinalityClusteredKarlssonBlowUpLowerData P) :
    ClusteredKarlssonBlowUpLowerData P :=
  h.toFiberCountedClusteredKarlssonBlowUpLowerData.toClusteredKarlssonBlowUpLowerData

end CardinalityClusteredKarlssonBlowUpLowerData

/-- Incremental lower construction whose finite counting input is only the
cluster map and its four fiber cardinalities. -/
structure CardinalityClusteredKarlssonBlowUpIncrementalLowerData
    (P : TheoremOne.ProblemFamily.{u}) where
  crossings : (n : Nat) → P.Arrangement n → Rat
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  cluster_witness :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      CardinalityClusteredKarlssonTableWitness q
  crossings_eq_clustered_pair_sum :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      crossings n (arrangement n q hq) =
        clusteredKarlssonPairTableCrossings
          ((cluster_witness n q hq).cluster)
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      IncrementalRegionData n
        (P.region n (arrangement n q hq))
        (crossings n (arrangement n q hq))

namespace CardinalityClusteredKarlssonBlowUpIncrementalLowerData

def toCardinalityClusteredKarlssonBlowUpLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CardinalityClusteredKarlssonBlowUpIncrementalLowerData P) :
    CardinalityClusteredKarlssonBlowUpLowerData P where
  crossings := h.crossings
  arrangement := h.arrangement
  cluster_witness := h.cluster_witness
  crossings_eq_clustered_pair_sum := h.crossings_eq_clustered_pair_sum
  regions_eq := by
    intro n q hq
    exact (h.region_increment n q hq).target_eq_totalCrossings_add

def toFiberCountedClusteredKarlssonBlowUpIncrementalLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CardinalityClusteredKarlssonBlowUpIncrementalLowerData P) :
    FiberCountedClusteredKarlssonBlowUpIncrementalLowerData P where
  crossings := h.crossings
  arrangement := h.arrangement
  cluster_witness := by
    intro n q hq
    exact
      (h.cluster_witness n q hq).toFiberCountedClusteredKarlssonTableWitness
  crossings_eq_clustered_pair_sum := h.crossings_eq_clustered_pair_sum
  region_increment := h.region_increment

def toPairCountedClusteredKarlssonBlowUpIncrementalLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CardinalityClusteredKarlssonBlowUpIncrementalLowerData P) :
    PairCountedClusteredKarlssonBlowUpIncrementalLowerData P :=
  h.toFiberCountedClusteredKarlssonBlowUpIncrementalLowerData.toPairCountedClusteredKarlssonBlowUpIncrementalLowerData

def toClusteredKarlssonBlowUpIncrementalLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CardinalityClusteredKarlssonBlowUpIncrementalLowerData P) :
    ClusteredKarlssonBlowUpIncrementalLowerData P :=
  h.toFiberCountedClusteredKarlssonBlowUpIncrementalLowerData.toClusteredKarlssonBlowUpIncrementalLowerData

end CardinalityClusteredKarlssonBlowUpIncrementalLowerData

/- A direct named Karlsson blow-up lower construction can be upgraded to the
cardinality-clustered interface: Lean supplies the canonical four-fiber cluster
map and proves its pair table is the closed lower crossing formula.  This is a
numeric counting refinement of the older interface. -/
namespace KarlssonBlowUpLowerData

noncomputable def toCardinalityClusteredKarlssonBlowUpLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonBlowUpLowerData P) :
    CardinalityClusteredKarlssonBlowUpLowerData P where
  crossings := h.crossings
  arrangement := h.arrangement
  cluster_witness := by
    intro n q hq
    exact cardinalityClusteredKarlssonTableWitnessOfSortedQuad q hq
  crossings_eq_clustered_pair_sum := by
    intro n q hq
    let w := cardinalityClusteredKarlssonTableWitnessOfSortedQuad q hq
    rw [h.crossings_eq_lower n q hq]
    exact (w.pairSum_eq_table.trans
      (karlssonClusterTableCrossingsOfQuad_eq_lowerCrossingsOfQuad q)).symm
  regions_eq := h.regions_eq

end KarlssonBlowUpLowerData

/- Incremental named Karlsson blow-up lower data have the same canonical
cardinality-clustered finite counting refinement. -/
namespace KarlssonBlowUpIncrementalLowerData

noncomputable def toCardinalityClusteredKarlssonBlowUpIncrementalLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonBlowUpIncrementalLowerData P) :
    CardinalityClusteredKarlssonBlowUpIncrementalLowerData P where
  crossings := h.crossings
  arrangement := h.arrangement
  cluster_witness := by
    intro n q hq
    exact cardinalityClusteredKarlssonTableWitnessOfSortedQuad q hq
  crossings_eq_clustered_pair_sum := by
    intro n q hq
    let w := cardinalityClusteredKarlssonTableWitnessOfSortedQuad q hq
    rw [h.crossings_eq_lower n q hq]
    exact (w.pairSum_eq_table.trans
      (karlssonClusterTableCrossingsOfQuad_eq_lowerCrossingsOfQuad q)).symm
  region_increment := h.region_increment

end KarlssonBlowUpIncrementalLowerData

end ExplicitInputs
end TheoremOneManuscript
end Lollipop

/-!
Proof component 7: `Manuscript.ExplicitInputs.PairwiseLower`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Pairwise Karlsson lower construction data.

The clustered lower interfaces still let the construction supply an aggregate
crossing equality.  This file moves that boundary one step closer to the
geometry: the construction supplies a pairwise crossing table for the produced
arrangement, proves each unordered pair has the Karlsson cluster-table value,
and supplies ordered insertion-region data for that pair table.  Lean then
derives the aggregate Karlsson crossing total and the region equation.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace ExplicitInputs

universe u

/-- One local monotone lower copy-pair certificate: the produced pair
crossing value is at least the corresponding Karlsson cluster-table value.
This is the lower-bound analogue of the exact local copy-pair equality
certificate in `KarlssonBase.lean`. -/
structure LocalClusterPairLowerBoundData
    {n : Nat} (cluster : Fin n → Fin 4)
    (pairCross : Fin n → Fin n → Rat)
    (i j : Fin n) (_hij : i < j) where
  pair_cross_ge_cluster :
    karlssonClusterPairCrossing (cluster i) (cluster j) ≤
      pairCross i j

/-- Local monotone copy-pair lower certificates assemble into the universal
pairwise lower-bound statement used by the monotone lower construction
interface. -/
theorem pair_cross_ge_cluster_from_local
    {n : Nat} {cluster : Fin n → Fin 4}
    {pairCross : Fin n → Fin n → Rat}
    (loc :
      ∀ i j : Fin n, ∀ hij : i < j,
        LocalClusterPairLowerBoundData cluster pairCross i j hij) :
    ∀ i j : Fin n, ∀ _hij : i < j,
      karlssonClusterPairCrossing (cluster i) (cluster j) ≤
        pairCross i j := by
  intro i j hij
  exact (loc i j hij).pair_cross_ge_cluster

/-- Pairwise lower construction with only cardinality-clustered finite counting
data.  The aggregate crossing count is no longer an input: it is defined as
the pair sum of the supplied pairwise crossing table. -/
structure PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerData
    (P : TheoremOne.ProblemFamily.{u}) where
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  cluster_witness :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      CardinalityClusteredKarlssonTableWitness q
  pair_cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  pair_cross_eq_cluster :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        pair_cross n (arrangement n q hq) i j =
          karlssonClusterPairCrossing
            ((cluster_witness n q hq).cluster i)
            ((cluster_witness n q hq).cluster j)
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      OrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

namespace PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerData

/-- The aggregate crossing count induced by a pairwise lower table. -/
def crossings
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerData P)
    (n : Nat) (A : P.Arrangement n) : Rat :=
  pairSum n (h.pair_cross n A)

/-- Pairwise Karlsson data imply the previous cardinality-clustered
incremental lower interface: Lean sums the pairwise table to the clustered
Karlsson pair sum and converts ordered insertion data to the ordinary
incremental region package. -/
noncomputable def toCardinalityClusteredKarlssonBlowUpIncrementalLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerData P) :
    CardinalityClusteredKarlssonBlowUpIncrementalLowerData P where
  crossings := h.crossings
  arrangement := h.arrangement
  cluster_witness := h.cluster_witness
  crossings_eq_clustered_pair_sum := by
    intro n q hq
    unfold crossings clusteredKarlssonPairTableCrossings pairSum
    apply Finset.sum_congr rfl
    intro p hp
    have hp_lt : p.1 < p.2 := by
      rw [pairFinset, Finset.mem_filter] at hp
      exact hp.2
    exact h.pair_cross_eq_cluster n q hq p.1 p.2 hp_lt
  region_increment := by
    intro n q hq
    exact (h.region_increment n q hq).toIncrementalPairRegionData

/-- Pairwise lower data also imply the named Karlsson blow-up lower interface
used by older theorem endpoints. -/
noncomputable def toKarlssonBlowUpIncrementalLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerData P) :
    KarlssonBlowUpIncrementalLowerData P :=
  h.toCardinalityClusteredKarlssonBlowUpIncrementalLowerData
    |>.toClusteredKarlssonBlowUpIncrementalLowerData
    |>.toKarlssonTableBlowUpIncrementalLowerData
    |>.toKarlssonBlowUpIncrementalLowerData

end PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerData

/-- Monotone pairwise lower construction.  The construction supplies a
pairwise crossing table and only proves that each unordered pair has at least
the corresponding Karlsson cluster-table value.  This is enough for the lower
bound side once the ordered region recurrence is supplied. -/
structure PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData
    (P : TheoremOne.ProblemFamily.{u}) where
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  cluster_witness :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      CardinalityClusteredKarlssonTableWitness q
  pair_cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  pair_cross_ge_cluster :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        karlssonClusterPairCrossing
            ((cluster_witness n q hq).cluster i)
            ((cluster_witness n q hq).cluster j) ≤
          pair_cross n (arrangement n q hq) i j
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      OrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

namespace PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData

/-- Aggregate crossing count induced by a monotone pairwise lower table. -/
def crossings
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData P)
    (n : Nat) (A : P.Arrangement n) : Rat :=
  pairSum n (h.pair_cross n A)

/-- The monotone pairwise table has aggregate crossing count at least the
clustered Karlsson table sum. -/
theorem clustered_pair_sum_le_crossings
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData P)
    (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n) :
    clusteredKarlssonPairTableCrossings
        ((h.cluster_witness n q hq).cluster) ≤
      h.crossings n (h.arrangement n q hq) := by
  unfold clusteredKarlssonPairTableCrossings crossings pairSum
  apply Finset.sum_le_sum
  intro p hp
  have hp_lt : p.1 < p.2 := by
    rw [pairFinset, Finset.mem_filter] at hp
    exact hp.2
  exact h.pair_cross_ge_cluster n q hq p.1 p.2 hp_lt

/-- Monotone pairwise lower data imply the monotone sorted lower-realization
interface.  The proof uses finite-sum monotonicity instead of exact pair-value
classification. -/
noncomputable def toSortedLowerCrossingBoundRealizations
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData P) :
    SortedLowerCrossingBoundRealizations P h.crossings := by
  intro n q hq
  refine ⟨h.arrangement n q hq, ?_, ?_⟩
  · have hw :=
      (h.cluster_witness n q hq).pairSum_eq_table
    have htable :
        karlssonClusterTableCrossingsOfQuad q =
          lowerCrossingsOfQuad q :=
      karlssonClusterTableCrossingsOfQuad_eq_lowerCrossingsOfQuad q
    have hcluster :
        lowerCrossingsOfQuad q ≤ h.crossings n (h.arrangement n q hq) := by
      rw [← htable, ← hw]
      exact h.clustered_pair_sum_le_crossings n q hq
    exact hcluster
  · exact (h.region_increment n q hq).target_eq_pairSum_add

/-- Monotone pairwise lower data give lower attainment as an inequality in
the displayed candidate form. -/
theorem lower_bound_attainment_choose
    (P : TheoremOne.ProblemFamily.{u})
    (h : PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData P) :
    ∀ n : Nat, ∃ A : P.Arrangement n,
      candidateRegionsChoose n ≤ P.region n A :=
  lower_bound_attainment_of_sortedLowerCrossingBoundRealizations_choose
    P h.toSortedLowerCrossingBoundRealizations

end PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData

end ExplicitInputs
end TheoremOneManuscript
end Lollipop

/-!
Proof component 8: `Manuscript.PrimitiveGeometry.LowerWitness`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Finite lower witnesses for primitive carrier intersections.

The monotone lower construction only needs to prove that each copy pair has at
least the Karlsson cluster-table value.  This file records the local geometric
certificate that supplies such an inequality: a finite set of distinct points
inside one pair carrier, together with the fact that the pair-crossing table
counts at least those points.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace PrimitiveGeometry

/-- Any finite subset of a locally certified carrier intersection has
cardinality at most the corresponding pair-crossing table entry. -/
theorem finset_card_le_pair_cross_of_localCarrierCrossing
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {pairCross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
    (C : LocalPairCarrierCrossingData A pairCross i j hij)
    (S : Finset R2)
    (hS : ∀ p ∈ S, p ∈ A.pairIntersectionSet i j) :
    (S.card : Rat) ≤ pairCross i j := by
  have hsubset : S ⊆ C.crossingPoints := by
    intro p hp
    have hp_pair : p ∈ A.pairIntersectionSet i j := hS p hp
    have hp_set : p ∈ ((C.crossingPoints : Finset R2) : Set R2) := by
      simpa [C.crossingPoints_spec] using hp_pair
    simpa using hp_set
  rw [C.cross_eq_card]
  exact_mod_cast Finset.card_le_card hsubset

/-- A local lower subset for one primitive carrier pair.  This is the purely
geometric part of a lower witness: a finite set of distinct carrier
intersection points whose size reaches the desired bound.  If the pair also
has a local carrier-crossing certificate, Lean can turn this subset into a
full lower witness by cardinality monotonicity. -/
structure LocalPairCarrierLowerSubsetData
    {n : Nat} (A : EuclideanLollipopArrangement n)
    (i j : Fin n) (_hij : i < j) (bound : Nat) where
  lowerPoints : Finset R2
  lowerPoints_subset :
    ∀ p ∈ lowerPoints, p ∈ A.pairIntersectionSet i j
  bound_le_card : bound ≤ lowerPoints.card

/-- A local lower witness for one primitive carrier pair.  The finite set
`lowerPoints` is not required to classify the whole carrier intersection; it
only has to lie inside it and have enough distinct points. -/
structure LocalPairCarrierLowerWitnessData
    {n : Nat} (A : EuclideanLollipopArrangement n)
    (pairCross : Fin n → Fin n → Rat)
    (i j : Fin n) (_hij : i < j) (bound : Nat) where
  lowerPoints : Finset R2
  lowerPoints_subset :
    ∀ p ∈ lowerPoints, p ∈ A.pairIntersectionSet i j
  bound_le_card : bound ≤ lowerPoints.card
  card_le_pair_cross : (lowerPoints.card : Rat) ≤ pairCross i j

namespace LocalPairCarrierLowerSubsetData

/-- A local carrier-crossing certificate upgrades a lower subset to a lower
witness whose cardinality is bounded by the pair-crossing table entry. -/
def toLocalPairCarrierLowerWitnessData
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {pairCross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
    {bound : Nat}
    (D : LocalPairCarrierLowerSubsetData A i j hij bound)
    (C : LocalPairCarrierCrossingData A pairCross i j hij) :
    LocalPairCarrierLowerWitnessData A pairCross i j hij bound where
  lowerPoints := D.lowerPoints
  lowerPoints_subset := D.lowerPoints_subset
  bound_le_card := D.bound_le_card
  card_le_pair_cross :=
    finset_card_le_pair_cross_of_localCarrierCrossing C D.lowerPoints
      D.lowerPoints_subset

/-- A lower subset plus a local carrier-crossing certificate gives the
corresponding rational lower bound on the pair-crossing table entry. -/
theorem bound_le_pair_cross
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {pairCross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
    {bound : Nat}
    (D : LocalPairCarrierLowerSubsetData A i j hij bound)
    (C : LocalPairCarrierCrossingData A pairCross i j hij) :
    (bound : Rat) ≤ pairCross i j := by
  have hcard : (bound : Rat) ≤ (D.lowerPoints.card : Rat) := by
    exact_mod_cast D.bound_le_card
  exact le_trans hcard
    (finset_card_le_pair_cross_of_localCarrierCrossing C D.lowerPoints
      D.lowerPoints_subset)

/-- A lower subset plus a local carrier-crossing certificate supplies the
local monotone copy-pair lower certificate once its size dominates the
Karlsson cluster-table value. -/
def toLocalClusterPairLowerBoundData
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {pairCross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
    {bound : Nat} {cluster : Fin n → Fin 4}
    (D : LocalPairCarrierLowerSubsetData A i j hij bound)
    (C : LocalPairCarrierCrossingData A pairCross i j hij)
    (hcluster :
      ExplicitInputs.karlssonClusterPairCrossing (cluster i) (cluster j) ≤
        (bound : Rat)) :
    ExplicitInputs.LocalClusterPairLowerBoundData
      cluster pairCross i j hij :=
  { pair_cross_ge_cluster := le_trans hcluster (D.bound_le_pair_cross C) }

end LocalPairCarrierLowerSubsetData

namespace LocalPairCarrierLowerWitnessData

/-- A finite lower witness gives the corresponding rational lower bound on
the pair-crossing table entry. -/
theorem bound_le_pair_cross
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {pairCross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
    {bound : Nat}
    (D : LocalPairCarrierLowerWitnessData A pairCross i j hij bound) :
    (bound : Rat) ≤ pairCross i j := by
  have hcard : (bound : Rat) ≤ (D.lowerPoints.card : Rat) := by
    exact_mod_cast D.bound_le_card
  exact le_trans hcard D.card_le_pair_cross

/-- If the requested Karlsson cluster value is at most the finite witness
size, then the witness supplies the local monotone lower copy-pair
certificate used by the lower-bound construction interface. -/
def toLocalClusterPairLowerBoundData
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {pairCross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
    {bound : Nat} {cluster : Fin n → Fin 4}
    (D : LocalPairCarrierLowerWitnessData A pairCross i j hij bound)
    (hcluster :
      ExplicitInputs.karlssonClusterPairCrossing (cluster i) (cluster j) ≤
        (bound : Rat)) :
    ExplicitInputs.LocalClusterPairLowerBoundData
      cluster pairCross i j hij where
  pair_cross_ge_cluster := le_trans hcluster D.bound_le_pair_cross

end LocalPairCarrierLowerWitnessData

/-- Four distinct component witnesses give a four-point lower subset of one
primitive carrier intersection.

This is the local shape needed for an intra-cluster Karlsson blow-up pair:
one certified point in each of the circle-circle, circle-ray, ray-circle, and
ray-ray components. -/
noncomputable def four_component_lower_subset
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n} (hij : i < j)
    {pcc pcr prc prr : R2}
    (hcc :
      pcc ∈ circleSet (A.lollipop i).center (A.lollipop i).radius ∧
        pcc ∈ circleSet (A.lollipop j).center (A.lollipop j).radius)
    (hcr :
      pcr ∈ circleSet (A.lollipop i).center (A.lollipop i).radius ∧
        pcr ∈ raySet (A.lollipop j).anchor (A.lollipop j).rayDirection)
    (hrc :
      prc ∈ raySet (A.lollipop i).anchor (A.lollipop i).rayDirection ∧
        prc ∈ circleSet (A.lollipop j).center (A.lollipop j).radius)
    (hrr :
      prr ∈ raySet (A.lollipop i).anchor (A.lollipop i).rayDirection ∧
        prr ∈ raySet (A.lollipop j).anchor (A.lollipop j).rayDirection)
    (hcc_cr : pcc ≠ pcr)
    (hcc_rc : pcc ≠ prc)
    (hcc_rr : pcc ≠ prr)
    (hcr_rc : pcr ≠ prc)
    (hcr_rr : pcr ≠ prr)
    (hrc_rr : prc ≠ prr) :
    LocalPairCarrierLowerSubsetData A i j hij 4 := by
  classical
  refine
    { lowerPoints := {pcc, pcr, prc, prr}
      lowerPoints_subset := ?_
      bound_le_card := ?_ }
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl
    · simpa [EuclideanLollipopArrangement.pairIntersectionSet] using
        mem_pairIntersectionSet_of_mem_circleSets
          (L := A.lollipop i) (M := A.lollipop j) hcc.1 hcc.2
    · simpa [EuclideanLollipopArrangement.pairIntersectionSet] using
        mem_pairIntersectionSet_of_mem_circleSet_of_mem_raySet
          (L := A.lollipop i) (M := A.lollipop j) hcr.1 hcr.2
    · simpa [EuclideanLollipopArrangement.pairIntersectionSet] using
        mem_pairIntersectionSet_of_mem_raySet_of_mem_circleSet
          (L := A.lollipop i) (M := A.lollipop j) hrc.1 hrc.2
    · simpa [EuclideanLollipopArrangement.pairIntersectionSet] using
        mem_pairIntersectionSet_of_mem_raySets
          (L := A.lollipop i) (M := A.lollipop j) hrr.1 hrr.2
  · have hcard : ({pcc, pcr, prc, prr} : Finset R2).card = 4 := by
      rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_insert_of_notMem]
          · simp
          · simp [hrc_rr]
        · simp [hcr_rc, hcr_rr]
      · simp [hcc_cr, hcc_rc, hcc_rr]
    exact le_of_eq hcard.symm

/-- Four distinct component witnesses plus a local finite-carrier certificate
force the local crossing table to count at least four points. -/
theorem four_le_pair_cross_of_component_witnesses
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {pairCross : Fin n → Fin n → Rat} {i j : Fin n}
    (hij : i < j)
    {pcc pcr prc prr : R2}
    (hcc :
      pcc ∈ circleSet (A.lollipop i).center (A.lollipop i).radius ∧
        pcc ∈ circleSet (A.lollipop j).center (A.lollipop j).radius)
    (hcr :
      pcr ∈ circleSet (A.lollipop i).center (A.lollipop i).radius ∧
        pcr ∈ raySet (A.lollipop j).anchor (A.lollipop j).rayDirection)
    (hrc :
      prc ∈ raySet (A.lollipop i).anchor (A.lollipop i).rayDirection ∧
        prc ∈ circleSet (A.lollipop j).center (A.lollipop j).radius)
    (hrr :
      prr ∈ raySet (A.lollipop i).anchor (A.lollipop i).rayDirection ∧
        prr ∈ raySet (A.lollipop j).anchor (A.lollipop j).rayDirection)
    (hcc_cr : pcc ≠ pcr)
    (hcc_rc : pcc ≠ prc)
    (hcc_rr : pcc ≠ prr)
    (hcr_rc : pcr ≠ prc)
    (hcr_rr : pcr ≠ prr)
    (hrc_rr : prc ≠ prr)
    (C : LocalPairCarrierCrossingData A pairCross i j hij) :
    (4 : Rat) ≤ pairCross i j :=
  (four_component_lower_subset
      hij hcc hcr hrc hrr hcc_cr hcc_rc hcc_rr hcr_rc hcr_rr hrc_rr)
    |>.bound_le_pair_cross C

/-- Same-cluster local Karlsson lower certificate from four distinct component
witnesses.

For same-cluster pairs the Karlsson table value is `4`, so the four-component
local witness is exactly the geometric input needed by the pairwise monotone
lower pipeline. -/
def localClusterPairLowerBoundData_of_four_component_same_cluster
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {pairCross : Fin n → Fin n → Rat} {cluster : Fin n → Fin 4}
    {i j : Fin n} (hij : i < j)
    (hsame : cluster i = cluster j)
    {pcc pcr prc prr : R2}
    (hcc :
      pcc ∈ circleSet (A.lollipop i).center (A.lollipop i).radius ∧
        pcc ∈ circleSet (A.lollipop j).center (A.lollipop j).radius)
    (hcr :
      pcr ∈ circleSet (A.lollipop i).center (A.lollipop i).radius ∧
        pcr ∈ raySet (A.lollipop j).anchor (A.lollipop j).rayDirection)
    (hrc :
      prc ∈ raySet (A.lollipop i).anchor (A.lollipop i).rayDirection ∧
        prc ∈ circleSet (A.lollipop j).center (A.lollipop j).radius)
    (hrr :
      prr ∈ raySet (A.lollipop i).anchor (A.lollipop i).rayDirection ∧
        prr ∈ raySet (A.lollipop j).anchor (A.lollipop j).rayDirection)
    (hcc_cr : pcc ≠ pcr)
    (hcc_rc : pcc ≠ prc)
    (hcc_rr : pcc ≠ prr)
    (hcr_rc : pcr ≠ prc)
    (hcr_rr : pcr ≠ prr)
    (hrc_rr : prc ≠ prr)
    (C : LocalPairCarrierCrossingData A pairCross i j hij) :
    ExplicitInputs.LocalClusterPairLowerBoundData
      cluster pairCross i j hij where
  pair_cross_ge_cluster := by
    have h4 :
        (4 : Rat) ≤ pairCross i j :=
      four_le_pair_cross_of_component_witnesses
        hij hcc hcr hrc hrr hcc_cr hcc_rc hcc_rr hcr_rc hcr_rr hrc_rr C
    simpa [hsame, ExplicitInputs.karlssonClusterPairCrossing_same] using h4

end PrimitiveGeometry
end TheoremOneManuscript
end Lollipop

/-!
Proof component 9: `Manuscript.Construction.IndexedLowerWitness`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Indexed finite lower witnesses.

Future coordinate blow-up proofs should be able to provide explicit carrier
points in the most convenient form.  This module records the reusable bridge
from an injective indexed family of `k` primitive carrier-intersection points
to the finite lower-subset certificates used by the monotone lower pipeline.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace ConstructionFormalization

open PrimitiveGeometry

noncomputable section

/-- An injective indexed family of `bound` carrier-intersection points gives a
finite lower subset of cardinality at least `bound`. -/
def indexed_lower_subset_of_mem_pairIntersectionSet
    {n bound : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n} (hij : i < j)
    (points : Fin bound → R2)
    (hinj : Function.Injective points)
    (hmem : ∀ k : Fin bound, points k ∈ A.pairIntersectionSet i j) :
    LocalPairCarrierLowerSubsetData A i j hij bound := by
  classical
  refine
    { lowerPoints := Finset.univ.image points
      lowerPoints_subset := ?_
      bound_le_card := ?_ }
  · intro p hp
    rcases Finset.mem_image.mp hp with ⟨k, _hk, rfl⟩
    exact hmem k
  · have hcard :
        (Finset.univ.image points).card = bound := by
      rw [Finset.card_image_of_injective _ hinj]
      exact Finset.card_fin bound
    exact le_of_eq hcard.symm

/-- An injective indexed family of carrier-intersection points plus a local
finite-carrier certificate gives the corresponding finite lower witness. -/
def indexed_lower_witness_of_mem_pairIntersectionSet
    {n bound : Nat} {A : EuclideanLollipopArrangement n}
    {pairCross : Fin n → Fin n → Rat} {i j : Fin n}
    (hij : i < j)
    (points : Fin bound → R2)
    (hinj : Function.Injective points)
    (hmem : ∀ k : Fin bound, points k ∈ A.pairIntersectionSet i j)
    (C : LocalPairCarrierCrossingData A pairCross i j hij) :
    LocalPairCarrierLowerWitnessData A pairCross i j hij bound :=
  (indexed_lower_subset_of_mem_pairIntersectionSet
      hij points hinj hmem)
    |>.toLocalPairCarrierLowerWitnessData C

/-- Indexed explicit carrier points prove a rational lower bound on the local
pair-crossing table once the full local carrier finset is certified. -/
theorem bound_le_pair_cross_of_indexed_mem_pairIntersectionSet
    {n bound : Nat} {A : EuclideanLollipopArrangement n}
    {pairCross : Fin n → Fin n → Rat} {i j : Fin n}
    (hij : i < j)
    (points : Fin bound → R2)
    (hinj : Function.Injective points)
    (hmem : ∀ k : Fin bound, points k ∈ A.pairIntersectionSet i j)
    (C : LocalPairCarrierCrossingData A pairCross i j hij) :
    (bound : Rat) ≤ pairCross i j :=
  (indexed_lower_subset_of_mem_pairIntersectionSet
      hij points hinj hmem).bound_le_pair_cross C

/-- Indexed carrier-intersection points of exactly the Karlsson local table
size give the local monotone cluster-pair lower certificate.

This is the intended direct interface for perturbation/blow-up geometry:
construct `4`, `5`, or `7` distinct points in the pair carrier according to
the two cluster labels, and combine them with the finite carrier-count
certificate for the same pair. -/
def localClusterPairLowerBoundData_of_indexed_karlsson_points
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {pairCross : Fin n → Fin n → Rat}
    {cluster : Fin n → Fin 4} {i j : Fin n}
    (hij : i < j)
    (points :
      Fin (ExplicitInputs.karlssonClusterPairCrossingNat
        (cluster i) (cluster j)) → R2)
    (hinj : Function.Injective points)
    (hmem :
      ∀ k : Fin (ExplicitInputs.karlssonClusterPairCrossingNat
        (cluster i) (cluster j)),
        points k ∈ A.pairIntersectionSet i j)
    (C : LocalPairCarrierCrossingData A pairCross i j hij) :
    ExplicitInputs.LocalClusterPairLowerBoundData
      cluster pairCross i j hij :=
  (indexed_lower_subset_of_mem_pairIntersectionSet
      hij points hinj hmem)
    |>.toLocalClusterPairLowerBoundData C
      (by
        rw [ExplicitInputs.karlssonClusterPairCrossing_eq_nat])

end

end ConstructionFormalization
end TheoremOneManuscript
end Lollipop

/-!
Proof component 10: `Manuscript.Construction.IndexedCarrier`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Indexed exact carrier certificates.

Concrete coordinate proofs often enumerate a pair carrier by an indexed family
`Fin k -> R2`.  The theorem stack, however, consumes `Finset` carrier
certificates.  This module records the reusable conversion from an injective
indexed enumeration whose image is exactly the primitive carrier intersection
to the local and pairwise carrier-crossing certificates used elsewhere.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace ConstructionFormalization

open PrimitiveGeometry

noncomputable section

/-- The finite set underlying an indexed carrier enumeration. -/
def indexedCarrierFinset
    {bound : Nat} (points : Fin bound → R2) : Finset R2 :=
  Finset.univ.image points

/-- An injective indexed carrier enumeration has the expected cardinality. -/
theorem indexedCarrierFinset_card
    {bound : Nat} (points : Fin bound → R2)
    (hinj : Function.Injective points) :
    (indexedCarrierFinset points).card = bound := by
  dsimp [indexedCarrierFinset]
  rw [Finset.card_image_of_injective _ hinj]
  exact Finset.card_fin bound

/-- An indexed carrier image is exactly a target pair carrier once every
indexed point lies in the carrier and every carrier point is covered by some
index. -/
theorem indexedCarrierFinset_spec_of_mem_and_cover
    {n bound : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n}
    (points : Fin bound → R2)
    (hmem : ∀ k : Fin bound, points k ∈ A.pairIntersectionSet i j)
    (hcover :
      ∀ p : R2, p ∈ A.pairIntersectionSet i j →
        ∃ k : Fin bound, points k = p) :
    ((indexedCarrierFinset points : Finset R2) : Set R2) =
      A.pairIntersectionSet i j := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨k, _hk, rfl⟩
    exact hmem k
  · intro hp
    rcases hcover p hp with ⟨k, hk⟩
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hk⟩

/-- A component-wise coverage proof is enough to identify an indexed carrier
image with the whole primitive pair carrier. -/
theorem indexedCarrierFinset_spec_of_component_covers
    {n bound : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n}
    (points : Fin bound → R2)
    (hmem : ∀ k : Fin bound, points k ∈ A.pairIntersectionSet i j)
    (hcc :
      ∀ p : R2,
        p ∈ circleSet (A.lollipop i).center (A.lollipop i).radius →
        p ∈ circleSet (A.lollipop j).center (A.lollipop j).radius →
        ∃ k : Fin bound, points k = p)
    (hcr :
      ∀ p : R2,
        p ∈ circleSet (A.lollipop i).center (A.lollipop i).radius →
        p ∈ raySet (A.lollipop j).anchor (A.lollipop j).rayDirection →
        ∃ k : Fin bound, points k = p)
    (hrc :
      ∀ p : R2,
        p ∈ raySet (A.lollipop i).anchor (A.lollipop i).rayDirection →
        p ∈ circleSet (A.lollipop j).center (A.lollipop j).radius →
        ∃ k : Fin bound, points k = p)
    (hrr :
      ∀ p : R2,
        p ∈ raySet (A.lollipop i).anchor (A.lollipop i).rayDirection →
        p ∈ raySet (A.lollipop j).anchor (A.lollipop j).rayDirection →
        ∃ k : Fin bound, points k = p) :
    ((indexedCarrierFinset points : Finset R2) : Set R2) =
      A.pairIntersectionSet i j := by
  refine indexedCarrierFinset_spec_of_mem_and_cover points hmem ?_
  intro p hp
  rcases (EuclideanLollipopArrangement.mem_pairIntersectionSet_iff
      A (i := i) (j := j) (p := p)).1 hp with hccp | hcrp | hrcp | hrrp
  · exact hcc p hccp.1 hccp.2
  · exact hcr p hcrp.1 hcrp.2
  · exact hrc p hrcp.1 hrcp.2
  · exact hrr p hrrp.1 hrrp.2

/-- A finite carrier set is exactly a target pair carrier once every point in
the finite set lies in the carrier and every carrier point is covered by the
finite set. -/
theorem carrierFinset_spec_of_mem_and_cover
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n}
    (carrier : Finset R2)
    (hmem : ∀ p : R2, p ∈ carrier → p ∈ A.pairIntersectionSet i j)
    (hcover :
      ∀ p : R2, p ∈ A.pairIntersectionSet i j → p ∈ carrier) :
    ((carrier : Finset R2) : Set R2) = A.pairIntersectionSet i j := by
  ext p
  constructor
  · intro hp
    exact hmem p (by simpa using hp)
  · intro hp
    simpa using hcover p hp

/-- The finite carrier set assembled from the four primitive circle/ray
components of one pair. -/
def componentCarrierFinset
    (circleCircle circleRay rayCircle rayRay : Finset R2) : Finset R2 :=
  circleCircle ∪ circleRay ∪ rayCircle ∪ rayRay

/-- If each component finset contains only points in its named component, then
their union contains only points in the primitive pair carrier. -/
theorem componentCarrierFinset_mem_pairIntersectionSet
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n}
    (circleCircle circleRay rayCircle rayRay : Finset R2)
    (hcc :
      ∀ p : R2, p ∈ circleCircle →
        p ∈ circleSet (A.lollipop i).center (A.lollipop i).radius ∧
        p ∈ circleSet (A.lollipop j).center (A.lollipop j).radius)
    (hcr :
      ∀ p : R2, p ∈ circleRay →
        p ∈ circleSet (A.lollipop i).center (A.lollipop i).radius ∧
        p ∈ raySet (A.lollipop j).anchor (A.lollipop j).rayDirection)
    (hrc :
      ∀ p : R2, p ∈ rayCircle →
        p ∈ raySet (A.lollipop i).anchor (A.lollipop i).rayDirection ∧
        p ∈ circleSet (A.lollipop j).center (A.lollipop j).radius)
    (hrr :
      ∀ p : R2, p ∈ rayRay →
        p ∈ raySet (A.lollipop i).anchor (A.lollipop i).rayDirection ∧
        p ∈ raySet (A.lollipop j).anchor (A.lollipop j).rayDirection) :
    ∀ p : R2, p ∈ componentCarrierFinset
        circleCircle circleRay rayCircle rayRay →
      p ∈ A.pairIntersectionSet i j := by
  classical
  intro p hp
  simp [componentCarrierFinset] at hp
  rcases hp with hpcc | hpcr | hprc | hprr
  · exact
      (EuclideanLollipopArrangement.mem_pairIntersectionSet_iff
        A (i := i) (j := j) (p := p)).2
        (Or.inl (hcc p hpcc))
  · exact
      (EuclideanLollipopArrangement.mem_pairIntersectionSet_iff
        A (i := i) (j := j) (p := p)).2
        (Or.inr (Or.inl (hcr p hpcr)))
  · exact
      (EuclideanLollipopArrangement.mem_pairIntersectionSet_iff
        A (i := i) (j := j) (p := p)).2
        (Or.inr (Or.inr (Or.inl (hrc p hprc))))
  · exact
      (EuclideanLollipopArrangement.mem_pairIntersectionSet_iff
        A (i := i) (j := j) (p := p)).2
        (Or.inr (Or.inr (Or.inr (hrr p hprr))))

/-- Component finsets identify the whole primitive pair carrier once they
contain only points of their component and cover every point in that
component. -/
theorem componentCarrierFinset_spec_of_component_covers
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n}
    (circleCircle circleRay rayCircle rayRay : Finset R2)
    (hcc_mem :
      ∀ p : R2, p ∈ circleCircle →
        p ∈ circleSet (A.lollipop i).center (A.lollipop i).radius ∧
        p ∈ circleSet (A.lollipop j).center (A.lollipop j).radius)
    (hcr_mem :
      ∀ p : R2, p ∈ circleRay →
        p ∈ circleSet (A.lollipop i).center (A.lollipop i).radius ∧
        p ∈ raySet (A.lollipop j).anchor (A.lollipop j).rayDirection)
    (hrc_mem :
      ∀ p : R2, p ∈ rayCircle →
        p ∈ raySet (A.lollipop i).anchor (A.lollipop i).rayDirection ∧
        p ∈ circleSet (A.lollipop j).center (A.lollipop j).radius)
    (hrr_mem :
      ∀ p : R2, p ∈ rayRay →
        p ∈ raySet (A.lollipop i).anchor (A.lollipop i).rayDirection ∧
        p ∈ raySet (A.lollipop j).anchor (A.lollipop j).rayDirection)
    (hcc_cover :
      ∀ p : R2,
        p ∈ circleSet (A.lollipop i).center (A.lollipop i).radius →
        p ∈ circleSet (A.lollipop j).center (A.lollipop j).radius →
        p ∈ circleCircle)
    (hcr_cover :
      ∀ p : R2,
        p ∈ circleSet (A.lollipop i).center (A.lollipop i).radius →
        p ∈ raySet (A.lollipop j).anchor (A.lollipop j).rayDirection →
        p ∈ circleRay)
    (hrc_cover :
      ∀ p : R2,
        p ∈ raySet (A.lollipop i).anchor (A.lollipop i).rayDirection →
        p ∈ circleSet (A.lollipop j).center (A.lollipop j).radius →
        p ∈ rayCircle)
    (hrr_cover :
      ∀ p : R2,
        p ∈ raySet (A.lollipop i).anchor (A.lollipop i).rayDirection →
        p ∈ raySet (A.lollipop j).anchor (A.lollipop j).rayDirection →
        p ∈ rayRay) :
    ((componentCarrierFinset
      circleCircle circleRay rayCircle rayRay : Finset R2) : Set R2) =
      A.pairIntersectionSet i j := by
  refine carrierFinset_spec_of_mem_and_cover
    (componentCarrierFinset circleCircle circleRay rayCircle rayRay)
    (componentCarrierFinset_mem_pairIntersectionSet
      circleCircle circleRay rayCircle rayRay
      hcc_mem hcr_mem hrc_mem hrr_mem)
    ?_
  intro p hp
  rcases (EuclideanLollipopArrangement.mem_pairIntersectionSet_iff
      A (i := i) (j := j) (p := p)).1 hp with hccp | hcrp | hrcp | hrrp
  · simp [componentCarrierFinset, hcc_cover p hccp.1 hccp.2]
  · simp [componentCarrierFinset, hcr_cover p hcrp.1 hcrp.2]
  · simp [componentCarrierFinset, hrc_cover p hrcp.1 hrcp.2]
  · simp [componentCarrierFinset, hrr_cover p hrrp.1 hrrp.2]

/-- If the four component finsets are pairwise disjoint and have prescribed
cardinalities, then their carrier union has the sum of those cardinalities. -/
theorem componentCarrierFinset_card_eq_of_disjoint
    (circleCircle circleRay rayCircle rayRay : Finset R2)
    {cc cr rc rr : Nat}
    (hcc_cr : Disjoint circleCircle circleRay)
    (hcc_rc : Disjoint circleCircle rayCircle)
    (hcc_rr : Disjoint circleCircle rayRay)
    (hcr_rc : Disjoint circleRay rayCircle)
    (hcr_rr : Disjoint circleRay rayRay)
    (hrc_rr : Disjoint rayCircle rayRay)
    (hcc_card : circleCircle.card = cc)
    (hcr_card : circleRay.card = cr)
    (hrc_card : rayCircle.card = rc)
    (hrr_card : rayRay.card = rr) :
    (componentCarrierFinset
      circleCircle circleRay rayCircle rayRay).card = cc + cr + rc + rr := by
  classical
  have hcccr_rc : Disjoint (circleCircle ∪ circleRay) rayCircle := by
    rw [Finset.disjoint_left]
    intro p hp hprc
    rw [Finset.mem_union] at hp
    rcases hp with hpcc | hpcr
    · exact (Finset.disjoint_left.mp hcc_rc) hpcc hprc
    · exact (Finset.disjoint_left.mp hcr_rc) hpcr hprc
  have hcccrrc_rr : Disjoint (circleCircle ∪ circleRay ∪ rayCircle) rayRay := by
    rw [Finset.disjoint_left]
    intro p hp hprr
    rw [Finset.mem_union] at hp
    rcases hp with hpcccr | hprc
    · rw [Finset.mem_union] at hpcccr
      rcases hpcccr with hpcc | hpcr
      · exact (Finset.disjoint_left.mp hcc_rr) hpcc hprr
      · exact (Finset.disjoint_left.mp hcr_rr) hpcr hprr
    · exact (Finset.disjoint_left.mp hrc_rr) hprc hprr
  calc
    (componentCarrierFinset
        circleCircle circleRay rayCircle rayRay).card =
        (circleCircle ∪ circleRay ∪ rayCircle).card + rayRay.card := by
      rw [componentCarrierFinset]
      exact Finset.card_union_of_disjoint hcccrrc_rr
    _ = (circleCircle ∪ circleRay).card + rayCircle.card + rayRay.card := by
      rw [Finset.card_union_of_disjoint hcccr_rc]
    _ = circleCircle.card + circleRay.card + rayCircle.card + rayRay.card := by
      rw [Finset.card_union_of_disjoint hcc_cr]
    _ = cc + cr + rc + rr := by
      omega

/-- Four component-indexed point families give a local lower subset once
their indexed images are pairwise disjoint and their component sizes add to
the target bound.  Coverage of the whole carrier is not needed for this
lower-bound direction. -/
noncomputable def component_indexed_lower_subset
    {n cc cr rc rr bound : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n} (hij : i < j)
    (circleCirclePoints : Fin cc → R2)
    (circleRayPoints : Fin cr → R2)
    (rayCirclePoints : Fin rc → R2)
    (rayRayPoints : Fin rr → R2)
    (circleCircleInjective : Function.Injective circleCirclePoints)
    (circleRayInjective : Function.Injective circleRayPoints)
    (rayCircleInjective : Function.Injective rayCirclePoints)
    (rayRayInjective : Function.Injective rayRayPoints)
    (circleCircleMem :
      ∀ k : Fin cc,
        circleCirclePoints k ∈
            circleSet (A.lollipop i).center (A.lollipop i).radius ∧
          circleCirclePoints k ∈
            circleSet (A.lollipop j).center (A.lollipop j).radius)
    (circleRayMem :
      ∀ k : Fin cr,
        circleRayPoints k ∈
            circleSet (A.lollipop i).center (A.lollipop i).radius ∧
          circleRayPoints k ∈
            raySet (A.lollipop j).anchor (A.lollipop j).rayDirection)
    (rayCircleMem :
      ∀ k : Fin rc,
        rayCirclePoints k ∈
            raySet (A.lollipop i).anchor (A.lollipop i).rayDirection ∧
          rayCirclePoints k ∈
            circleSet (A.lollipop j).center (A.lollipop j).radius)
    (rayRayMem :
      ∀ k : Fin rr,
        rayRayPoints k ∈
            raySet (A.lollipop i).anchor (A.lollipop i).rayDirection ∧
          rayRayPoints k ∈
            raySet (A.lollipop j).anchor (A.lollipop j).rayDirection)
    (hcc_cr :
      Disjoint (indexedCarrierFinset circleCirclePoints)
        (indexedCarrierFinset circleRayPoints))
    (hcc_rc :
      Disjoint (indexedCarrierFinset circleCirclePoints)
        (indexedCarrierFinset rayCirclePoints))
    (hcc_rr :
      Disjoint (indexedCarrierFinset circleCirclePoints)
        (indexedCarrierFinset rayRayPoints))
    (hcr_rc :
      Disjoint (indexedCarrierFinset circleRayPoints)
        (indexedCarrierFinset rayCirclePoints))
    (hcr_rr :
      Disjoint (indexedCarrierFinset circleRayPoints)
        (indexedCarrierFinset rayRayPoints))
    (hrc_rr :
      Disjoint (indexedCarrierFinset rayCirclePoints)
        (indexedCarrierFinset rayRayPoints))
    (hsum : cc + cr + rc + rr = bound) :
    LocalPairCarrierLowerSubsetData A i j hij bound := by
  classical
  refine
    { lowerPoints :=
        componentCarrierFinset
          (indexedCarrierFinset circleCirclePoints)
          (indexedCarrierFinset circleRayPoints)
          (indexedCarrierFinset rayCirclePoints)
          (indexedCarrierFinset rayRayPoints)
      lowerPoints_subset := ?_
      bound_le_card := ?_ }
  · exact
      componentCarrierFinset_mem_pairIntersectionSet
        (A := A) (i := i) (j := j)
        (indexedCarrierFinset circleCirclePoints)
        (indexedCarrierFinset circleRayPoints)
        (indexedCarrierFinset rayCirclePoints)
        (indexedCarrierFinset rayRayPoints)
        (by
          intro p hp
          rcases
              (by
                simpa [indexedCarrierFinset] using hp :
                ∃ k : Fin cc, circleCirclePoints k = p) with
            ⟨k, rfl⟩
          exact circleCircleMem k)
        (by
          intro p hp
          rcases
              (by
                simpa [indexedCarrierFinset] using hp :
                ∃ k : Fin cr, circleRayPoints k = p) with
            ⟨k, rfl⟩
          exact circleRayMem k)
        (by
          intro p hp
          rcases
              (by
                simpa [indexedCarrierFinset] using hp :
                ∃ k : Fin rc, rayCirclePoints k = p) with
            ⟨k, rfl⟩
          exact rayCircleMem k)
        (by
          intro p hp
          rcases
              (by
                simpa [indexedCarrierFinset] using hp :
                ∃ k : Fin rr, rayRayPoints k = p) with
            ⟨k, rfl⟩
          exact rayRayMem k)
  · have hcard :
        (componentCarrierFinset
          (indexedCarrierFinset circleCirclePoints)
          (indexedCarrierFinset circleRayPoints)
          (indexedCarrierFinset rayCirclePoints)
          (indexedCarrierFinset rayRayPoints)).card = bound := by
      calc
        (componentCarrierFinset
          (indexedCarrierFinset circleCirclePoints)
          (indexedCarrierFinset circleRayPoints)
          (indexedCarrierFinset rayCirclePoints)
          (indexedCarrierFinset rayRayPoints)).card = cc + cr + rc + rr := by
          exact
            componentCarrierFinset_card_eq_of_disjoint
              (indexedCarrierFinset circleCirclePoints)
              (indexedCarrierFinset circleRayPoints)
              (indexedCarrierFinset rayCirclePoints)
              (indexedCarrierFinset rayRayPoints)
              hcc_cr hcc_rc hcc_rr hcr_rc hcr_rr hrc_rr
              (indexedCarrierFinset_card circleCirclePoints
                circleCircleInjective)
              (indexedCarrierFinset_card circleRayPoints
                circleRayInjective)
              (indexedCarrierFinset_card rayCirclePoints
                rayCircleInjective)
              (indexedCarrierFinset_card rayRayPoints rayRayInjective)
        _ = bound := hsum
    exact le_of_eq hcard.symm

/-- Component-indexed points whose component sizes add to the Karlsson local
table value give the local monotone cluster-pair lower certificate. -/
noncomputable def
    localClusterPairLowerBoundData_of_component_indexed_karlsson_points
    {n cc cr rc rr : Nat} {A : EuclideanLollipopArrangement n}
    {pairCross : Fin n → Fin n → Rat}
    {cluster : Fin n → Fin 4} {i j : Fin n}
    (hij : i < j)
    (circleCirclePoints : Fin cc → R2)
    (circleRayPoints : Fin cr → R2)
    (rayCirclePoints : Fin rc → R2)
    (rayRayPoints : Fin rr → R2)
    (circleCircleInjective : Function.Injective circleCirclePoints)
    (circleRayInjective : Function.Injective circleRayPoints)
    (rayCircleInjective : Function.Injective rayCirclePoints)
    (rayRayInjective : Function.Injective rayRayPoints)
    (circleCircleMem :
      ∀ k : Fin cc,
        circleCirclePoints k ∈
            circleSet (A.lollipop i).center (A.lollipop i).radius ∧
          circleCirclePoints k ∈
            circleSet (A.lollipop j).center (A.lollipop j).radius)
    (circleRayMem :
      ∀ k : Fin cr,
        circleRayPoints k ∈
            circleSet (A.lollipop i).center (A.lollipop i).radius ∧
          circleRayPoints k ∈
            raySet (A.lollipop j).anchor (A.lollipop j).rayDirection)
    (rayCircleMem :
      ∀ k : Fin rc,
        rayCirclePoints k ∈
            raySet (A.lollipop i).anchor (A.lollipop i).rayDirection ∧
          rayCirclePoints k ∈
            circleSet (A.lollipop j).center (A.lollipop j).radius)
    (rayRayMem :
      ∀ k : Fin rr,
        rayRayPoints k ∈
            raySet (A.lollipop i).anchor (A.lollipop i).rayDirection ∧
          rayRayPoints k ∈
            raySet (A.lollipop j).anchor (A.lollipop j).rayDirection)
    (hcc_cr :
      Disjoint (indexedCarrierFinset circleCirclePoints)
        (indexedCarrierFinset circleRayPoints))
    (hcc_rc :
      Disjoint (indexedCarrierFinset circleCirclePoints)
        (indexedCarrierFinset rayCirclePoints))
    (hcc_rr :
      Disjoint (indexedCarrierFinset circleCirclePoints)
        (indexedCarrierFinset rayRayPoints))
    (hcr_rc :
      Disjoint (indexedCarrierFinset circleRayPoints)
        (indexedCarrierFinset rayCirclePoints))
    (hcr_rr :
      Disjoint (indexedCarrierFinset circleRayPoints)
        (indexedCarrierFinset rayRayPoints))
    (hrc_rr :
      Disjoint (indexedCarrierFinset rayCirclePoints)
        (indexedCarrierFinset rayRayPoints))
    (hsum :
      cc + cr + rc + rr =
        ExplicitInputs.karlssonClusterPairCrossingNat
          (cluster i) (cluster j))
    (C : LocalPairCarrierCrossingData A pairCross i j hij) :
    ExplicitInputs.LocalClusterPairLowerBoundData
      cluster pairCross i j hij :=
  (component_indexed_lower_subset
      hij circleCirclePoints circleRayPoints rayCirclePoints rayRayPoints
      circleCircleInjective circleRayInjective rayCircleInjective
      rayRayInjective circleCircleMem circleRayMem rayCircleMem rayRayMem
      hcc_cr hcc_rc hcc_rr hcr_rc hcr_rr hrc_rr hsum)
    |>.toLocalClusterPairLowerBoundData C
      (by
        rw [ExplicitInputs.karlssonClusterPairCrossing_eq_nat])

/-- Component-wise coverage proves that a finite carrier set is the whole
primitive pair carrier. -/
theorem carrierFinset_spec_of_component_covers
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n}
    (carrier : Finset R2)
    (hmem : ∀ p : R2, p ∈ carrier → p ∈ A.pairIntersectionSet i j)
    (hcc :
      ∀ p : R2,
        p ∈ circleSet (A.lollipop i).center (A.lollipop i).radius →
        p ∈ circleSet (A.lollipop j).center (A.lollipop j).radius →
        p ∈ carrier)
    (hcr :
      ∀ p : R2,
        p ∈ circleSet (A.lollipop i).center (A.lollipop i).radius →
        p ∈ raySet (A.lollipop j).anchor (A.lollipop j).rayDirection →
        p ∈ carrier)
    (hrc :
      ∀ p : R2,
        p ∈ raySet (A.lollipop i).anchor (A.lollipop i).rayDirection →
        p ∈ circleSet (A.lollipop j).center (A.lollipop j).radius →
        p ∈ carrier)
    (hrr :
      ∀ p : R2,
        p ∈ raySet (A.lollipop i).anchor (A.lollipop i).rayDirection →
        p ∈ raySet (A.lollipop j).anchor (A.lollipop j).rayDirection →
        p ∈ carrier) :
    ((carrier : Finset R2) : Set R2) = A.pairIntersectionSet i j := by
  refine carrierFinset_spec_of_mem_and_cover carrier hmem ?_
  intro p hp
  rcases (EuclideanLollipopArrangement.mem_pairIntersectionSet_iff
      A (i := i) (j := j) (p := p)).1 hp with hccp | hcrp | hrcp | hrrp
  · exact hcc p hccp.1 hccp.2
  · exact hcr p hcrp.1 hcrp.2
  · exact hrc p hrcp.1 hrcp.2
  · exact hrr p hrrp.1 hrrp.2

/-- If a finite carrier set is exactly the primitive pair carrier, then every
point of that finite set is a primitive carrier-intersection point. -/
theorem carrierFinset_mem_pairIntersectionSet_of_spec
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n}
    (carrier : Finset R2)
    (hspec : ((carrier : Finset R2) : Set R2) =
        A.pairIntersectionSet i j)
    {p : R2} (hp : p ∈ carrier) :
    p ∈ A.pairIntersectionSet i j := by
  have hpSet : p ∈ ((carrier : Finset R2) : Set R2) := by
    simpa using hp
  simpa [hspec] using hpSet

/-- If the indexed carrier image is exactly the primitive pair carrier, then
each indexed point is a primitive carrier-intersection point. -/
theorem indexedCarrier_mem_pairIntersectionSet_of_spec
    {n bound : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n}
    (points : Fin bound → R2)
    (hspec :
      ((indexedCarrierFinset points : Finset R2) : Set R2) =
        A.pairIntersectionSet i j)
    (k : Fin bound) :
    points k ∈ A.pairIntersectionSet i j := by
  have hp : points k ∈ indexedCarrierFinset points := by
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩
  have hpSet :
      points k ∈ ((indexedCarrierFinset points : Finset R2) : Set R2) := by
    simpa using hp
  simpa [hspec] using hpSet

/-- An exact indexed carrier enumeration gives the local carrier-crossing
certificate for one pair. -/
def localPairCarrierCrossingDataOfIndexedCarrier
    {n bound : Nat} {A : EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat} {i j : Fin n}
    (hij : i < j)
    (points : Fin bound → R2)
    (hinj : Function.Injective points)
    (hspec :
      ((indexedCarrierFinset points : Finset R2) : Set R2) =
        A.pairIntersectionSet i j)
    (hcross : cross i j = (bound : Rat)) :
    LocalPairCarrierCrossingData A cross i j hij where
  crossingPoints := indexedCarrierFinset points
  crossingPoints_spec := hspec
  cross_eq_card := by
    rw [indexedCarrierFinset_card points hinj]
    exact hcross

/-- Membership and coverage data for an indexed carrier enumeration give the
local carrier-crossing certificate for one pair. -/
def localPairCarrierCrossingDataOfIndexedCarrierFromMemCover
    {n bound : Nat} {A : EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat} {i j : Fin n}
    (hij : i < j)
    (points : Fin bound → R2)
    (hinj : Function.Injective points)
    (hmem : ∀ k : Fin bound, points k ∈ A.pairIntersectionSet i j)
    (hcover :
      ∀ p : R2, p ∈ A.pairIntersectionSet i j →
        ∃ k : Fin bound, points k = p)
    (hcross : cross i j = (bound : Rat)) :
    LocalPairCarrierCrossingData A cross i j hij :=
  localPairCarrierCrossingDataOfIndexedCarrier
    hij points hinj
    (indexedCarrierFinset_spec_of_mem_and_cover points hmem hcover)
    hcross

/-- An exact indexed carrier enumeration gives the lower subset of the same
size without needing a separate membership proof for each point. -/
def indexed_lower_subset_of_exact_carrier
    {n bound : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n} (hij : i < j)
    (points : Fin bound → R2)
    (hinj : Function.Injective points)
    (hspec :
      ((indexedCarrierFinset points : Finset R2) : Set R2) =
        A.pairIntersectionSet i j) :
    LocalPairCarrierLowerSubsetData A i j hij bound :=
  indexed_lower_subset_of_mem_pairIntersectionSet
    hij points hinj
    (indexedCarrier_mem_pairIntersectionSet_of_spec points hspec)

/-- Membership data for an indexed carrier enumeration give the lower subset
of the same size.  Coverage is not needed for the lower subset, but this
wrapper matches the fields used by the exact-carrier constructor above. -/
def indexed_lower_subset_of_mem_cover
    {n bound : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n} (hij : i < j)
    (points : Fin bound → R2)
    (hinj : Function.Injective points)
    (hmem : ∀ k : Fin bound, points k ∈ A.pairIntersectionSet i j)
    (_hcover :
      ∀ p : R2, p ∈ A.pairIntersectionSet i j →
        ∃ k : Fin bound, points k = p) :
    LocalPairCarrierLowerSubsetData A i j hij bound :=
  indexed_lower_subset_of_mem_pairIntersectionSet hij points hinj hmem

/-- An exact indexed carrier enumeration gives the local lower witness for
the same pair-crossing table entry. -/
def indexed_lower_witness_of_exact_carrier
    {n bound : Nat} {A : EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat} {i j : Fin n}
    (hij : i < j)
    (points : Fin bound → R2)
    (hinj : Function.Injective points)
    (hspec :
      ((indexedCarrierFinset points : Finset R2) : Set R2) =
        A.pairIntersectionSet i j)
    (hcross : cross i j = (bound : Rat)) :
    LocalPairCarrierLowerWitnessData A cross i j hij bound :=
  (indexed_lower_subset_of_exact_carrier hij points hinj hspec)
    |>.toLocalPairCarrierLowerWitnessData
      (localPairCarrierCrossingDataOfIndexedCarrier
        hij points hinj hspec hcross)

/-- Membership and coverage data for an indexed carrier enumeration give the
local lower witness for the same pair-crossing table entry. -/
def indexed_lower_witness_of_mem_cover
    {n bound : Nat} {A : EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat} {i j : Fin n}
    (hij : i < j)
    (points : Fin bound → R2)
    (hinj : Function.Injective points)
    (hmem : ∀ k : Fin bound, points k ∈ A.pairIntersectionSet i j)
    (hcover :
      ∀ p : R2, p ∈ A.pairIntersectionSet i j →
        ∃ k : Fin bound, points k = p)
    (hcross : cross i j = (bound : Rat)) :
    LocalPairCarrierLowerWitnessData A cross i j hij bound :=
  (indexed_lower_subset_of_mem_cover hij points hinj hmem hcover)
    |>.toLocalPairCarrierLowerWitnessData
      (localPairCarrierCrossingDataOfIndexedCarrierFromMemCover
        hij points hinj hmem hcover hcross)

/-- An exact indexed carrier enumeration identifies the automatic finite
carrier witness with the indexed finset. -/
theorem arrangementPairIntersectionFinset_eq_indexedCarrierFinset_of_exact_carrier
    {n bound : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n} {hij : i < j}
    (hLM :
      euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
        euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      euclideanRayLine (A.lollipop i) ≠ euclideanRayLine (A.lollipop j))
    (points : Fin bound → R2)
    (hspec :
      ((indexedCarrierFinset points : Finset R2) : Set R2) =
        A.pairIntersectionSet i j) :
    CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
        A hij hLM hline =
      indexedCarrierFinset points := by
  classical
  let auto :
      Finset R2 :=
    CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
      A hij hLM hline
  have hauto :
      ((auto : Finset R2) : Set R2) = A.pairIntersectionSet i j := by
    simpa [auto] using
      CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset_spec
        (A := A) (i := i) (j := j) (hij := hij) hLM hline
  have hsets :
      ((auto : Finset R2) : Set R2) =
        ((indexedCarrierFinset points : Finset R2) : Set R2) := by
    rw [hauto, ← hspec]
  change auto = indexedCarrierFinset points
  apply Finset.ext
  intro p
  constructor
  · intro hp
    have hpSet : p ∈ ((auto : Finset R2) : Set R2) := by
      simpa using hp
    have hpIndexed :
        p ∈ ((indexedCarrierFinset points : Finset R2) : Set R2) := by
      simpa [hsets] using hpSet
    simpa using hpIndexed
  · intro hp
    have hpIndexed :
        p ∈ ((indexedCarrierFinset points : Finset R2) : Set R2) := by
      simpa using hp
    have hpSet : p ∈ ((auto : Finset R2) : Set R2) := by
      simpa [hsets] using hpIndexed
    simpa using hpSet

/-- An exact finite carrier set identifies the automatic finite carrier
witness with that finite set. -/
theorem arrangementPairIntersectionFinset_eq_carrierFinset_of_exact_carrier
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n} {hij : i < j}
    (hLM :
      euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
        euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      euclideanRayLine (A.lollipop i) ≠ euclideanRayLine (A.lollipop j))
    (carrier : Finset R2)
    (hspec :
      ((carrier : Finset R2) : Set R2) =
        A.pairIntersectionSet i j) :
    CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
        A hij hLM hline =
      carrier := by
  classical
  let auto :
      Finset R2 :=
    CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
      A hij hLM hline
  have hauto :
      ((auto : Finset R2) : Set R2) = A.pairIntersectionSet i j := by
    simpa [auto] using
      CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset_spec
        (A := A) (i := i) (j := j) (hij := hij) hLM hline
  have hsets :
      ((auto : Finset R2) : Set R2) =
        ((carrier : Finset R2) : Set R2) := by
    rw [hauto, ← hspec]
  change auto = carrier
  apply Finset.ext
  intro p
  constructor
  · intro hp
    have hpSet : p ∈ ((auto : Finset R2) : Set R2) := by
      simpa using hp
    have hpCarrier :
        p ∈ ((carrier : Finset R2) : Set R2) := by
      simpa [hsets] using hpSet
    simpa using hpCarrier
  · intro hp
    have hpCarrier : p ∈ ((carrier : Finset R2) : Set R2) := by
      simpa using hp
    have hpSet : p ∈ ((auto : Finset R2) : Set R2) := by
      simpa [hsets] using hpCarrier
    simpa using hpSet

/-- An exact injective indexed carrier enumeration computes the cardinality
of the automatic finite carrier witness. -/
theorem arrangementPairIntersectionFinset_card_eq_of_indexedCarrier
    {n bound : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n} {hij : i < j}
    (hLM :
      euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
        euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      euclideanRayLine (A.lollipop i) ≠ euclideanRayLine (A.lollipop j))
    (points : Fin bound → R2)
    (hinj : Function.Injective points)
    (hspec :
      ((indexedCarrierFinset points : Finset R2) : Set R2) =
        A.pairIntersectionSet i j) :
    (CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
        A hij hLM hline).card = bound := by
  rw [arrangementPairIntersectionFinset_eq_indexedCarrierFinset_of_exact_carrier
    hLM hline points hspec]
  exact indexedCarrierFinset_card points hinj

/-- An exact finite carrier set computes the cardinality of the automatic
finite carrier witness. -/
theorem arrangementPairIntersectionFinset_card_eq_of_carrierFinset
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n} {hij : i < j}
    (hLM :
      euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
        euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      euclideanRayLine (A.lollipop i) ≠ euclideanRayLine (A.lollipop j))
    (carrier : Finset R2)
    (hspec :
      ((carrier : Finset R2) : Set R2) =
        A.pairIntersectionSet i j) :
    (CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
        A hij hLM hline).card = carrier.card := by
  rw [arrangementPairIntersectionFinset_eq_carrierFinset_of_exact_carrier
    hLM hline carrier hspec]

/-- An exact injective indexed carrier enumeration computes the automatic
carrier crossing-table entry. -/
theorem automaticCarrierCrossingTable_eq_of_indexedCarrier
    {n bound : Nat} {A : EuclideanLollipopArrangement n}
    (hLM :
      ∀ i j : Fin n, i < j →
        euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
          euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      ∀ i j : Fin n, i < j →
        euclideanRayLine (A.lollipop i) ≠
          euclideanRayLine (A.lollipop j))
    {i j : Fin n} (hij : i < j)
    (points : Fin bound → R2)
    (hinj : Function.Injective points)
    (hspec :
      ((indexedCarrierFinset points : Finset R2) : Set R2) =
        A.pairIntersectionSet i j) :
    CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable
        A hLM hline i j = (bound : Rat) := by
  rw [CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable_eq_card
    hLM hline hij]
  exact_mod_cast
    arrangementPairIntersectionFinset_card_eq_of_indexedCarrier
      (hLM i j hij) (hline i j hij) points hinj hspec

/-- An exact finite carrier set computes the automatic carrier crossing-table
entry. -/
theorem automaticCarrierCrossingTable_eq_card_of_carrierFinset
    {n : Nat} {A : EuclideanLollipopArrangement n}
    (hLM :
      ∀ i j : Fin n, i < j →
        euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
          euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      ∀ i j : Fin n, i < j →
        euclideanRayLine (A.lollipop i) ≠
          euclideanRayLine (A.lollipop j))
    {i j : Fin n} (hij : i < j)
    (carrier : Finset R2)
    (hspec :
      ((carrier : Finset R2) : Set R2) =
        A.pairIntersectionSet i j) :
    CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable
        A hLM hline i j = (carrier.card : Rat) := by
  rw [CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable_eq_card
    hLM hline hij]
  exact_mod_cast
    arrangementPairIntersectionFinset_card_eq_of_carrierFinset
      (hLM i j hij) (hline i j hij) carrier hspec

/-- Exact indexed carriers assemble into the global pairwise carrier-crossing
certificate. -/
def pairwiseCarrierCrossingDataOfIndexedCarriers
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat}
    (bound : ∀ i j : Fin n, i < j → Nat)
    (points :
      ∀ i j : Fin n, ∀ hij : i < j,
        Fin (bound i j hij) → R2)
    (hinj :
      ∀ i j : Fin n, ∀ hij : i < j,
        Function.Injective (points i j hij))
    (hspec :
      ∀ i j : Fin n, ∀ hij : i < j,
        ((indexedCarrierFinset (points i j hij) : Finset R2) : Set R2) =
          A.pairIntersectionSet i j)
    (hcross :
      ∀ i j : Fin n, ∀ hij : i < j,
        cross i j = (bound i j hij : Rat)) :
    PairwiseCarrierCrossingData A cross :=
  PairwiseCarrierCrossingData.ofLocal fun i j hij =>
    localPairCarrierCrossingDataOfIndexedCarrier
      hij (points i j hij) (hinj i j hij)
      (hspec i j hij) (hcross i j hij)

end

end ConstructionFormalization
end TheoremOneManuscript
end Lollipop

/-!
Proof component 11: `Manuscript.Construction.LowerAnchorWitness`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Concrete lower witnesses from shared anchors.

This module records a first construction-side primitive fact: if two
lollipops share their anchor, that common anchor is an actual point of the
primitive carrier intersection.  Consequently it gives a one-point finite
lower subset, and any local finite-carrier certificate turns that subset into
a rational lower bound on the pair-crossing table.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace ConstructionFormalization

open PrimitiveGeometry

/-- If two primitive lollipops share their anchor, the left anchor lies in
their primitive carrier intersection. -/
theorem left_anchor_mem_pairIntersectionSet_of_common_anchor
    {L M : EuclideanLollipop}
    (hanchor : L.anchor = M.anchor) :
    L.anchor ∈ pairIntersectionSet L M := by
  constructor
  · exact L.anchor_mem_carrier
  · simpa [hanchor] using M.anchor_mem_carrier

/-- If two primitive lollipops share their anchor, the right anchor lies in
their primitive carrier intersection. -/
theorem right_anchor_mem_pairIntersectionSet_of_common_anchor
    {L M : EuclideanLollipop}
    (hanchor : L.anchor = M.anchor) :
    M.anchor ∈ pairIntersectionSet L M := by
  simpa [hanchor] using
    left_anchor_mem_pairIntersectionSet_of_common_anchor
      (L := L) (M := M) hanchor

/-- Arrangement-indexed form of the shared-anchor primitive intersection
point. -/
theorem arrangement_left_anchor_mem_pairIntersectionSet_of_common_anchor
    {n : Nat} (A : EuclideanLollipopArrangement n)
    {i j : Fin n}
    (hanchor : (A.lollipop i).anchor = (A.lollipop j).anchor) :
    (A.lollipop i).anchor ∈ A.pairIntersectionSet i j := by
  simpa [EuclideanLollipopArrangement.pairIntersectionSet] using
    left_anchor_mem_pairIntersectionSet_of_common_anchor
      (L := A.lollipop i) (M := A.lollipop j) hanchor

/-- A single certified primitive carrier-intersection point is a one-point
finite lower subset. -/
def singleton_lower_subset_of_mem_pairIntersectionSet
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n} (hij : i < j) {p : R2}
    (hp : p ∈ A.pairIntersectionSet i j) :
    LocalPairCarrierLowerSubsetData A i j hij 1 where
  lowerPoints := {p}
  lowerPoints_subset := by
    intro q hq
    rw [Finset.mem_singleton] at hq
    subst q
    exact hp
  bound_le_card := by
    simp

/-- A shared anchor gives a one-point finite lower subset for that arranged
pair. -/
def common_anchor_lower_subset_one
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n} (hij : i < j)
    (hanchor : (A.lollipop i).anchor = (A.lollipop j).anchor) :
    LocalPairCarrierLowerSubsetData A i j hij 1 :=
  singleton_lower_subset_of_mem_pairIntersectionSet hij
    (arrangement_left_anchor_mem_pairIntersectionSet_of_common_anchor
      A hanchor)

/-- A shared anchor plus a local finite-carrier certificate gives a one-point
local lower witness. -/
def common_anchor_lower_witness_one
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {pairCross : Fin n → Fin n → Rat} {i j : Fin n}
    (hij : i < j)
    (hanchor : (A.lollipop i).anchor = (A.lollipop j).anchor)
    (C : LocalPairCarrierCrossingData A pairCross i j hij) :
    LocalPairCarrierLowerWitnessData A pairCross i j hij 1 :=
  (common_anchor_lower_subset_one hij hanchor)
    |>.toLocalPairCarrierLowerWitnessData C

/-- A shared anchor plus a local finite-carrier certificate forces the
pair-crossing table to count at least one primitive carrier point. -/
theorem one_le_pair_cross_of_common_anchor
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {pairCross : Fin n → Fin n → Rat} {i j : Fin n}
    (hij : i < j)
    (hanchor : (A.lollipop i).anchor = (A.lollipop j).anchor)
    (C : LocalPairCarrierCrossingData A pairCross i j hij) :
    (1 : Rat) ≤ pairCross i j :=
  (common_anchor_lower_subset_one hij hanchor).bound_le_pair_cross C

end ConstructionFormalization
end TheoremOneManuscript
end Lollipop

/-!
Proof component 12: `Manuscript.GeometricInputs`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Manuscript-style geometric inputs for Theorem 1.

`ConcreteModel.lean` exposes a strong coordinate/canonical endpoint.  This
file also exposes the more literal interface used in the manuscript: for every
arrangement, provide close and intriguing predicates, the pairwise crossing
table bounds, and the four-subset and five-subset close/intriguing facts.  Lean then
constructs the colored graph and runs the already proved Zykov, weighted
Turan, blocker, matrix, and lower-attainment stacks.
-/

namespace Lollipop
namespace TheoremOneManuscript

universe u

/-- The manuscript's pair score
`1_{not close} + 1_{not intriguing} + 1_{not close and not intriguing}`. -/
noncomputable def manuscriptPairScore
    {V : Type*} (close intriguing : V → V → Prop) (i j : V) : Rat := by
  classical
  exact
    (if close i j then 0 else 1) +
    (if intriguing i j then 0 else 1) +
    (if close i j ∨ intriguing i j then 0 else 1)

/-- Global paper-style geometric upper data for every arrangement.  This is
the manuscript's geometric input written as extractor functions: close and
intriguing predicates, an exact pairwise crossing table, the four pointwise
crossing bounds including the baseline `<= 7` case, the close-pair-in-four and
intriguing-pair-in-five facts, and the total crossing/region equation. -/
structure ManuscriptGeometricUpperData
    (P : TheoremOne.ProblemFamily.{u}) where
  crossings : ∀ n : Nat, P.Arrangement n → Rat
  close : ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Prop
  intriguing : ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Prop
  close_decidable :
    ∀ n : Nat, ∀ A : P.Arrangement n, DecidableRel (close n A)
  intriguing_decidable :
    ∀ n : Nat, ∀ A : P.Arrangement n, DecidableRel (intriguing n A)
  close_symm :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n,
      close n A i j ↔ close n A j i
  intriguing_symm :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n,
      intriguing n A i j ↔ intriguing n A j i
  cross : ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  crossings_le_pairSum :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      crossings n A ≤ pairSum n (cross n A)
  cross_le_general :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      cross n A i j ≤ 7
  cross_le_close :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      close n A i j → cross n A i j ≤ 5
  cross_le_intriguing :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      intriguing n A i j → cross n A i j ≤ 5
  cross_le_close_intriguing :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      close n A i j → intriguing n A i j → cross n A i j ≤ 4
  close_pair_in_every_four :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ t : Finset (Fin n), t.card = 4 →
      ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ close n A i j
  intriguing_pair_in_every_five :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ t : Finset (Fin n), t.card = 5 →
      ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ intriguing n A i j
  regions_eq :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A = crossings n A + (n : Rat) + 1

namespace ManuscriptGeometricUpperData

/-- The four pointwise geometric crossing bounds imply the manuscript's
displayed estimate
`c_ij <= 4 + 1_D + 1_E + 1_{D cap E}`. -/
theorem pair_crossing_le_four_plus_score
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ManuscriptGeometricUpperData P)
    (n : Nat) (A : P.Arrangement n) :
    ∀ i j : Fin n, i < j →
      h.cross n A i j ≤
        4 + manuscriptPairScore (h.close n A) (h.intriguing n A) i j := by
  intro i j hij
  unfold manuscriptPairScore
  by_cases hc : h.close n A i j
  · by_cases hi : h.intriguing n A i j
    · have hcross := h.cross_le_close_intriguing n A i j hij hc hi
      simp [hc, hi] at hcross ⊢
      linarith
    · have hcross := h.cross_le_close n A i j hij hc
      simp [hc, hi] at hcross ⊢
      linarith
  · by_cases hi : h.intriguing n A i j
    · have hcross := h.cross_le_intriguing n A i j hij hi
      simp [hc, hi] at hcross ⊢
      linarith
    · have hcross := h.cross_le_general n A i j hij
      simp [hc, hi] at hcross ⊢
      linarith

/-- Convert global paper-style geometric extractors into the upper
certificates used by the geometric reduction. -/
noncomputable def toPairwiseGeometricUpperCertificates
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ManuscriptGeometricUpperData P) :
    TheoremOneEndToEnd.PairwiseGeometricUpperCertificates P := by
  intro n A
  exact
    ⟨{ nNat := n
       crossings := h.crossings n A
       regions := P.region n A
       close := h.close n A
       intriguing := h.intriguing n A
       close_decidable := h.close_decidable n A
       intriguing_decidable := h.intriguing_decidable n A
       close_symm := h.close_symm n A
       intriguing_symm := h.intriguing_symm n A
       cross := h.cross n A
       crossings_le_pairSum := h.crossings_le_pairSum n A
       cross_le_general := h.cross_le_general n A
       cross_le_close := h.cross_le_close n A
       cross_le_intriguing := h.cross_le_intriguing n A
       cross_le_close_intriguing := h.cross_le_close_intriguing n A
       close_pair_in_every_four := h.close_pair_in_every_four n A
       intriguing_pair_in_every_five := h.intriguing_pair_in_every_five n A
       regions_eq := h.regions_eq n A },
      rfl, rfl⟩

end ManuscriptGeometricUpperData

/-- Paper-style geometric upper data where the region equation is derived from
incremental insertion data rather than assumed directly. -/
structure ManuscriptGeometricIncrementalUpperData
    (P : TheoremOne.ProblemFamily.{u}) where
  crossings : ∀ n : Nat, P.Arrangement n → Rat
  close : ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Prop
  intriguing : ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Prop
  close_decidable :
    ∀ n : Nat, ∀ A : P.Arrangement n, DecidableRel (close n A)
  intriguing_decidable :
    ∀ n : Nat, ∀ A : P.Arrangement n, DecidableRel (intriguing n A)
  close_symm :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n,
      close n A i j ↔ close n A j i
  intriguing_symm :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n,
      intriguing n A i j ↔ intriguing n A j i
  cross : ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  crossings_le_pairSum :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      crossings n A ≤ pairSum n (cross n A)
  cross_le_general :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      cross n A i j ≤ 7
  cross_le_close :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      close n A i j → cross n A i j ≤ 5
  cross_le_intriguing :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      intriguing n A i j → cross n A i j ≤ 5
  cross_le_close_intriguing :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      close n A i j → intriguing n A i j → cross n A i j ≤ 4
  close_pair_in_every_four :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ t : Finset (Fin n), t.card = 4 →
      ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ close n A i j
  intriguing_pair_in_every_five :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ t : Finset (Fin n), t.card = 5 →
      ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ intriguing n A i j
  region_increment :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      IncrementalRegionData n (P.region n A) (crossings n A)

namespace ManuscriptGeometricIncrementalUpperData

/-- Derive the direct region-equation upper data from incremental insertion
data. -/
def toManuscriptGeometricUpperData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ManuscriptGeometricIncrementalUpperData P) :
    ManuscriptGeometricUpperData P where
  crossings := h.crossings
  close := h.close
  intriguing := h.intriguing
  close_decidable := h.close_decidable
  intriguing_decidable := h.intriguing_decidable
  close_symm := h.close_symm
  intriguing_symm := h.intriguing_symm
  cross := h.cross
  crossings_le_pairSum := h.crossings_le_pairSum
  cross_le_general := h.cross_le_general
  cross_le_close := h.cross_le_close
  cross_le_intriguing := h.cross_le_intriguing
  cross_le_close_intriguing := h.cross_le_close_intriguing
  close_pair_in_every_four := h.close_pair_in_every_four
  intriguing_pair_in_every_five := h.intriguing_pair_in_every_five
  regions_eq := by
    intro n A
    exact (h.region_increment n A).target_eq_totalCrossings_add

/-- The incremental upper-data variant also implies the manuscript's displayed
pointwise pair estimate. -/
theorem pair_crossing_le_four_plus_score
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ManuscriptGeometricIncrementalUpperData P)
    (n : Nat) (A : P.Arrangement n) :
    ∀ i j : Fin n, i < j →
      h.cross n A i j ≤
        4 + manuscriptPairScore (h.close n A) (h.intriguing n A) i j := by
  exact h.toManuscriptGeometricUpperData.pair_crossing_le_four_plus_score n A

/-- Convert incremental global paper-style geometric data into the upper
certificates used by the geometric reduction. -/
noncomputable def toPairwiseGeometricUpperCertificates
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ManuscriptGeometricIncrementalUpperData P) :
    TheoremOneEndToEnd.PairwiseGeometricUpperCertificates P :=
  h.toManuscriptGeometricUpperData.toPairwiseGeometricUpperCertificates

end ManuscriptGeometricIncrementalUpperData

/-- Manuscript-style subtheorems: the upper input is exactly the abstract
close/intriguing geometric package, and the lower input is sorted Karlsson
crossing-count realization data. -/
structure ManuscriptGeometricModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : TheoremOneEndToEnd.PairwiseGeometricUpperCertificates P
  lower_karlsson : SortedKarlssonLowerData P

/-- Manuscript-style subtheorems with the lower region equation supplied by
incremental insertion data. -/
structure ManuscriptGeometricIncrementalModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : TheoremOneEndToEnd.PairwiseGeometricUpperCertificates P
  lower_karlsson : SortedKarlssonIncrementalLowerData P

/-- Global-data version of the paper-style geometric subtheorems. -/
structure ManuscriptGeometricDataSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : ManuscriptGeometricUpperData P
  lower_karlsson : SortedKarlssonLowerData P

/-- Global-data version where both upper and lower region equations are
derived from incremental insertion data. -/
structure ManuscriptGeometricFullyIncrementalDataSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : ManuscriptGeometricIncrementalUpperData P
  lower_karlsson : SortedKarlssonIncrementalLowerData P

namespace ManuscriptGeometricIncrementalModelSubtheorems

/-- Forget lower incremental proof details after Lean derives
`regions = crossings + n + 1`. -/
def toManuscriptGeometricModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ManuscriptGeometricIncrementalModelSubtheorems P) :
    ManuscriptGeometricModelSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson := h.lower_karlsson.toSortedKarlssonLowerData

end ManuscriptGeometricIncrementalModelSubtheorems

namespace ManuscriptGeometricDataSubtheorems

/-- Convert global paper-style geometric data to the certificate-style
manuscript package. -/
noncomputable def toManuscriptGeometricModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ManuscriptGeometricDataSubtheorems P) :
    ManuscriptGeometricModelSubtheorems P where
  upper_geometry := h.upper_geometry.toPairwiseGeometricUpperCertificates
  lower_karlsson := h.lower_karlsson

end ManuscriptGeometricDataSubtheorems

namespace ManuscriptGeometricFullyIncrementalDataSubtheorems

/-- Convert fully incremental global paper-style geometric data to the
incremental certificate-style manuscript package. -/
noncomputable def toManuscriptGeometricIncrementalModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ManuscriptGeometricFullyIncrementalDataSubtheorems P) :
    ManuscriptGeometricIncrementalModelSubtheorems P where
  upper_geometry := h.upper_geometry.toPairwiseGeometricUpperCertificates
  lower_karlsson := h.lower_karlsson

end ManuscriptGeometricFullyIncrementalDataSubtheorems

/-- Upper bound from the manuscript's abstract close/intriguing geometric
package. -/
theorem upper_bound_proven_from_manuscript_geometric_model
    (P : TheoremOne.ProblemFamily.{u})
    (h : ManuscriptGeometricModelSubtheorems P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact
    TheoremOneEndToEnd.upper_bound_of_pairwise_geometric_certificates
      P h.upper_geometry

/-- Maximum-form Theorem 1 from manuscript-style geometric upper data and
sorted Karlsson lower data. -/
theorem theorem_one_statement_proven_from_manuscript_geometric_model
    (P : TheoremOne.ProblemFamily.{u})
    (h : ManuscriptGeometricModelSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact
    TheoremOneFormal.maximumStatement_of_choose_upper_bound_and_lower_attainment
      P
      (upper_bound_proven_from_manuscript_geometric_model P h)
      (lower_attainment_of_sortedLowerCrossingRealizations_choose
        P (crossings := h.lower_karlsson.crossings) h.lower_karlsson.realizations)

/-- Maximum-form Theorem 1 from manuscript-style geometric upper data and
incremental sorted Karlsson lower data. -/
theorem theorem_one_statement_proven_from_manuscript_geometric_incremental_model
    (P : TheoremOne.ProblemFamily.{u})
    (h : ManuscriptGeometricIncrementalModelSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_manuscript_geometric_model
    P h.toManuscriptGeometricModelSubtheorems

/-- Maximum-form Theorem 1 from global paper-style geometric upper data and
sorted Karlsson lower data. -/
theorem theorem_one_statement_proven_from_manuscript_geometric_data
    (P : TheoremOne.ProblemFamily.{u})
    (h : ManuscriptGeometricDataSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_manuscript_geometric_model
    P h.toManuscriptGeometricModelSubtheorems

/-- Maximum-form Theorem 1 from fully incremental global paper-style
geometric data. -/
theorem theorem_one_statement_proven_from_manuscript_geometric_fully_incremental_data
    (P : TheoremOne.ProblemFamily.{u})
    (h : ManuscriptGeometricFullyIncrementalDataSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_manuscript_geometric_incremental_model
    P h.toManuscriptGeometricIncrementalModelSubtheorems

/-- Manuscript-style geometric obligations for a family with a named maximum
count function. -/
def MaxManuscriptGeometricModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ManuscriptGeometricModelSubtheorems P.toProblemFamily

/-- Incremental manuscript-style geometric obligations for a family with a
named maximum count function. -/
def MaxManuscriptGeometricIncrementalModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ManuscriptGeometricIncrementalModelSubtheorems P.toProblemFamily

/-- Global paper-style geometric obligations for a family with a named maximum
count function. -/
def MaxManuscriptGeometricDataSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ManuscriptGeometricDataSubtheorems P.toProblemFamily

/-- Fully incremental global paper-style geometric obligations for a family
with a named maximum count function. -/
def MaxManuscriptGeometricFullyIncrementalDataSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ManuscriptGeometricFullyIncrementalDataSubtheorems P.toProblemFamily

/-- Formula-form Theorem 1 with the manuscript's sorted `S(n)`, from the
paper-style close/intriguing geometric input and sorted Karlsson lower data. -/
theorem theorem_one_formula_statement_proven_from_manuscript_geometric_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  intro n
  have hmax :
      TheoremOne.MaximumStatement P.toProblemFamily :=
    theorem_one_statement_proven_from_manuscript_geometric_model
      P.toProblemFamily h
  have hformula := TheoremOne.formulaStatement_of_maximumStatement P hmax n
  rw [hformula]
  unfold candidateRegionsChoose
  rw [← manuscriptS_eq_concreteS n]

/-- Formula-form Theorem 1 with the manuscript's sorted `S(n)`, from the
paper-style close/intriguing geometric input and incremental sorted Karlsson
lower data. -/
theorem theorem_one_formula_statement_proven_from_manuscript_geometric_incremental_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricIncrementalModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_manuscript_geometric_model
    P h.toManuscriptGeometricModelSubtheorems

/-- Formula-form Theorem 1 from global paper-style geometric upper data and
sorted Karlsson lower data. -/
theorem theorem_one_formula_statement_proven_from_manuscript_geometric_data
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricDataSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_manuscript_geometric_model
    P h.toManuscriptGeometricModelSubtheorems

/-- Formula-form Theorem 1 from fully incremental global paper-style
geometric data. -/
theorem theorem_one_formula_statement_proven_from_manuscript_geometric_fully_incremental_data
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricFullyIncrementalDataSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_manuscript_geometric_incremental_model
    P h.toManuscriptGeometricIncrementalModelSubtheorems

/-- Single-size displayed formula from paper-style close/intriguing
geometric input and sorted Karlsson lower data. -/
theorem theorem_one_formula_at_proven_from_manuscript_geometric_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_manuscript_geometric_model P h n

/-- Single-size displayed formula from paper-style close/intriguing
geometric input and incremental sorted Karlsson lower data. -/
theorem theorem_one_formula_at_proven_from_manuscript_geometric_incremental_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricIncrementalModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_manuscript_geometric_incremental_model P h n

/-- Single-size displayed formula from global paper-style geometric upper data
and sorted Karlsson lower data. -/
theorem theorem_one_formula_at_proven_from_manuscript_geometric_data
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricDataSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_manuscript_geometric_data P h n

/-- Single-size displayed formula from fully incremental global paper-style
geometric data. -/
theorem theorem_one_formula_at_proven_from_manuscript_geometric_fully_incremental_data
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricFullyIncrementalDataSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_manuscript_geometric_fully_incremental_data P h n

end TheoremOneManuscript
end Lollipop

/-!
Proof component 13: `Manuscript.ExplicitInputs.EndToEnd`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
End-to-end manuscript endpoints from explicit lower-construction data.

This module is deliberately separate from the earlier manuscript files.  It
keeps the previously checked interfaces unchanged and adds stronger final
packages whose lower side is a named Karlsson blow-up construction for every
sorted quadruple, not merely an existential realization relation.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace ExplicitInputs

universe u

/-- Fully incremental concrete model data with a named Karlsson blow-up lower
construction. -/
structure ConcreteFullyIncrementalBlowUpModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : CanonicalExactUpperGeometryIncrementalData P
  lower_karlsson : KarlssonBlowUpIncrementalLowerData P

namespace ConcreteFullyIncrementalBlowUpModelSubtheorems

/-- Convert the stronger named-blow-up package to the existing fully
incremental concrete package. -/
def toConcreteFullyIncrementalModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ConcreteFullyIncrementalBlowUpModelSubtheorems P) :
    ConcreteFullyIncrementalModelSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson := h.lower_karlsson.toSortedKarlssonIncrementalLowerData

end ConcreteFullyIncrementalBlowUpModelSubtheorems

/-- Paper-style global geometric data with a named Karlsson blow-up lower
construction. -/
structure ManuscriptGeometricBlowUpDataSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : ManuscriptGeometricIncrementalUpperData P
  lower_karlsson : KarlssonBlowUpIncrementalLowerData P

namespace ManuscriptGeometricBlowUpDataSubtheorems

/-- Convert the stronger named-blow-up package to the existing fully
incremental paper-style geometric package. -/
noncomputable def toManuscriptGeometricFullyIncrementalDataSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ManuscriptGeometricBlowUpDataSubtheorems P) :
    ManuscriptGeometricFullyIncrementalDataSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson := h.lower_karlsson.toSortedKarlssonIncrementalLowerData

end ManuscriptGeometricBlowUpDataSubtheorems

/-- Fully incremental concrete model data whose lower construction is
certified by the explicit four-cluster Karlsson table. -/
structure ConcreteFullyIncrementalTableBlowUpModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : CanonicalExactUpperGeometryIncrementalData P
  lower_karlsson : KarlssonTableBlowUpIncrementalLowerData P

namespace ConcreteFullyIncrementalTableBlowUpModelSubtheorems

/-- Convert table-shaped lower data to the named-blow-up package after Lean
derives `lowerCrossingsOfQuad` from the table sum. -/
def toConcreteFullyIncrementalBlowUpModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ConcreteFullyIncrementalTableBlowUpModelSubtheorems P) :
    ConcreteFullyIncrementalBlowUpModelSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson := h.lower_karlsson.toKarlssonBlowUpIncrementalLowerData

end ConcreteFullyIncrementalTableBlowUpModelSubtheorems

/-- Paper-style global geometric data whose lower construction is certified
by the explicit four-cluster Karlsson table. -/
structure ManuscriptGeometricTableBlowUpDataSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : ManuscriptGeometricIncrementalUpperData P
  lower_karlsson : KarlssonTableBlowUpIncrementalLowerData P

namespace ManuscriptGeometricTableBlowUpDataSubtheorems

/-- Convert table-shaped lower data to the named-blow-up paper-style package
after Lean derives `lowerCrossingsOfQuad` from the table sum. -/
def toManuscriptGeometricBlowUpDataSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ManuscriptGeometricTableBlowUpDataSubtheorems P) :
    ManuscriptGeometricBlowUpDataSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson := h.lower_karlsson.toKarlssonBlowUpIncrementalLowerData

end ManuscriptGeometricTableBlowUpDataSubtheorems

/-- Fully incremental concrete model data whose lower construction carries an
individual cluster map on the produced lollipops. -/
structure ConcreteFullyIncrementalClusteredBlowUpModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : CanonicalExactUpperGeometryIncrementalData P
  lower_karlsson : ClusteredKarlssonBlowUpIncrementalLowerData P

namespace ConcreteFullyIncrementalClusteredBlowUpModelSubtheorems

/-- Convert clustered lower data to table-certified lower data after Lean
collapses the individual pair table to the four-cluster table. -/
def toConcreteFullyIncrementalTableBlowUpModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ConcreteFullyIncrementalClusteredBlowUpModelSubtheorems P) :
    ConcreteFullyIncrementalTableBlowUpModelSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson := h.lower_karlsson.toKarlssonTableBlowUpIncrementalLowerData

end ConcreteFullyIncrementalClusteredBlowUpModelSubtheorems

/-- Paper-style global geometric data whose lower construction carries an
individual cluster map on the produced lollipops. -/
structure ManuscriptGeometricClusteredBlowUpDataSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : ManuscriptGeometricIncrementalUpperData P
  lower_karlsson : ClusteredKarlssonBlowUpIncrementalLowerData P

namespace ManuscriptGeometricClusteredBlowUpDataSubtheorems

/-- Convert clustered lower data to table-certified paper-style lower data. -/
def toManuscriptGeometricTableBlowUpDataSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ManuscriptGeometricClusteredBlowUpDataSubtheorems P) :
    ManuscriptGeometricTableBlowUpDataSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson := h.lower_karlsson.toKarlssonTableBlowUpIncrementalLowerData

end ManuscriptGeometricClusteredBlowUpDataSubtheorems

/-- Maximum-form Theorem 1 from concrete upper data and a named Karlsson
blow-up lower construction. -/
theorem theorem_one_statement_proven_from_concrete_blowup_model
    (P : TheoremOne.ProblemFamily.{u})
    (h : ConcreteFullyIncrementalBlowUpModelSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_fully_incremental_concrete_model
    P h.toConcreteFullyIncrementalModelSubtheorems

/-- Maximum-form Theorem 1 from paper-style geometric upper data and a named
Karlsson blow-up lower construction. -/
theorem theorem_one_statement_proven_from_geometric_data_and_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : ManuscriptGeometricBlowUpDataSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_manuscript_geometric_fully_incremental_data
    P h.toManuscriptGeometricFullyIncrementalDataSubtheorems

/-- Maximum-form Theorem 1 from concrete upper data and a table-certified
Karlsson blow-up lower construction. -/
theorem theorem_one_statement_proven_from_concrete_table_blowup_model
    (P : TheoremOne.ProblemFamily.{u})
    (h : ConcreteFullyIncrementalTableBlowUpModelSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_concrete_blowup_model
    P h.toConcreteFullyIncrementalBlowUpModelSubtheorems

/-- Maximum-form Theorem 1 from paper-style geometric upper data and a
table-certified Karlsson blow-up lower construction. -/
theorem theorem_one_statement_proven_from_geometric_data_and_table_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : ManuscriptGeometricTableBlowUpDataSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_geometric_data_and_blowup
    P h.toManuscriptGeometricBlowUpDataSubtheorems

/-- Maximum-form Theorem 1 from concrete upper data and a clustered Karlsson
blow-up lower construction. -/
theorem theorem_one_statement_proven_from_concrete_clustered_blowup_model
    (P : TheoremOne.ProblemFamily.{u})
    (h : ConcreteFullyIncrementalClusteredBlowUpModelSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_concrete_table_blowup_model
    P h.toConcreteFullyIncrementalTableBlowUpModelSubtheorems

/-- Maximum-form Theorem 1 from paper-style geometric upper data and a
clustered Karlsson blow-up lower construction. -/
theorem theorem_one_statement_proven_from_geometric_data_and_clustered_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : ManuscriptGeometricClusteredBlowUpDataSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_geometric_data_and_table_blowup
    P h.toManuscriptGeometricTableBlowUpDataSubtheorems

/-- Concrete named-blow-up obligations for a family with a named maximum
count function. -/
def MaxConcreteFullyIncrementalBlowUpModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ConcreteFullyIncrementalBlowUpModelSubtheorems P.toProblemFamily

/-- Paper-style geometric named-blow-up obligations for a family with a named
maximum count function. -/
def MaxManuscriptGeometricBlowUpDataSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ManuscriptGeometricBlowUpDataSubtheorems P.toProblemFamily

/-- Concrete table-certified named-blow-up obligations for a family with a
named maximum count function. -/
def MaxConcreteFullyIncrementalTableBlowUpModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ConcreteFullyIncrementalTableBlowUpModelSubtheorems P.toProblemFamily

/-- Paper-style geometric table-certified named-blow-up obligations for a
family with a named maximum count function. -/
def MaxManuscriptGeometricTableBlowUpDataSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ManuscriptGeometricTableBlowUpDataSubtheorems P.toProblemFamily

/-- Concrete clustered named-blow-up obligations for a family with a named
maximum count function. -/
def MaxConcreteFullyIncrementalClusteredBlowUpModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ConcreteFullyIncrementalClusteredBlowUpModelSubtheorems P.toProblemFamily

/-- Paper-style geometric clustered named-blow-up obligations for a family
with a named maximum count function. -/
def MaxManuscriptGeometricClusteredBlowUpDataSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ManuscriptGeometricClusteredBlowUpDataSubtheorems P.toProblemFamily

/-- Formula-form Theorem 1 from concrete upper data and a named Karlsson
blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_concrete_blowup_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteFullyIncrementalBlowUpModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_fully_incremental_concrete_model
    P h.toConcreteFullyIncrementalModelSubtheorems

/-- Formula-form Theorem 1 from paper-style geometric upper data and a named
Karlsson blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_geometric_data_and_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricBlowUpDataSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_manuscript_geometric_fully_incremental_data
    P h.toManuscriptGeometricFullyIncrementalDataSubtheorems

/-- Formula-form Theorem 1 from concrete upper data and a table-certified
Karlsson blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_concrete_table_blowup_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteFullyIncrementalTableBlowUpModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_concrete_blowup_model
    P h.toConcreteFullyIncrementalBlowUpModelSubtheorems

/-- Formula-form Theorem 1 from paper-style geometric upper data and a
table-certified Karlsson blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_geometric_data_and_table_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricTableBlowUpDataSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_geometric_data_and_blowup
    P h.toManuscriptGeometricBlowUpDataSubtheorems

/-- Formula-form Theorem 1 from concrete upper data and a clustered Karlsson
blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_concrete_clustered_blowup_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteFullyIncrementalClusteredBlowUpModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_concrete_table_blowup_model
    P h.toConcreteFullyIncrementalTableBlowUpModelSubtheorems

/-- Formula-form Theorem 1 from paper-style geometric upper data and a
clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_geometric_data_and_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricClusteredBlowUpDataSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_geometric_data_and_table_blowup
    P h.toManuscriptGeometricTableBlowUpDataSubtheorems

/-- Single-size displayed formula from concrete upper data and a named
Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_concrete_blowup_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteFullyIncrementalBlowUpModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_concrete_blowup_model P h n

/-- Single-size displayed formula from paper-style geometric upper data and a
named Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_geometric_data_and_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricBlowUpDataSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_geometric_data_and_blowup P h n

/-- Single-size displayed formula from concrete upper data and a
table-certified Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_concrete_table_blowup_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteFullyIncrementalTableBlowUpModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_concrete_table_blowup_model P h n

/-- Single-size displayed formula from paper-style geometric upper data and a
table-certified Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_geometric_data_and_table_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricTableBlowUpDataSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_geometric_data_and_table_blowup P h n

/-- Single-size displayed formula from concrete upper data and a clustered
Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_concrete_clustered_blowup_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteFullyIncrementalClusteredBlowUpModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_concrete_clustered_blowup_model P h n

/-- Single-size displayed formula from paper-style geometric upper data and a
clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_geometric_data_and_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricClusteredBlowUpDataSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_geometric_data_and_clustered_blowup P h n

end ExplicitInputs
end TheoremOneManuscript
end Lollipop

/-!
Proof component 14: `Manuscript.ExplicitInputs.PairCountedEndToEnd`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Theorem 1 endpoints from pair-counted clustered lower data.

This module is a non-disruptive strengthening of `ExplicitInputs.EndToEnd`.
The lower side no longer supplies the final collapse from individual
cluster-pair crossings to the four-cluster table directly.  It supplies finite
same/inter-cluster pair counts; `PairCountedClusteredLower.lean` proves the
collapse and then this file reuses the existing theorem stack.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace ExplicitInputs

universe u

/-- Fully incremental concrete model data whose lower construction is
certified by explicit finite same/inter-cluster pair counts. -/
structure ConcreteFullyIncrementalPairCountedClusteredBlowUpModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : CanonicalExactUpperGeometryIncrementalData P
  lower_karlsson : PairCountedClusteredKarlssonBlowUpIncrementalLowerData P

namespace ConcreteFullyIncrementalPairCountedClusteredBlowUpModelSubtheorems

def toConcreteFullyIncrementalClusteredBlowUpModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ConcreteFullyIncrementalPairCountedClusteredBlowUpModelSubtheorems P) :
    ConcreteFullyIncrementalClusteredBlowUpModelSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson := h.lower_karlsson.toClusteredKarlssonBlowUpIncrementalLowerData

end ConcreteFullyIncrementalPairCountedClusteredBlowUpModelSubtheorems

/-- Paper-style global geometric data whose lower construction is certified by
explicit finite same/inter-cluster pair counts. -/
structure ManuscriptGeometricPairCountedClusteredBlowUpDataSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : ManuscriptGeometricIncrementalUpperData P
  lower_karlsson : PairCountedClusteredKarlssonBlowUpIncrementalLowerData P

namespace ManuscriptGeometricPairCountedClusteredBlowUpDataSubtheorems

def toManuscriptGeometricClusteredBlowUpDataSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ManuscriptGeometricPairCountedClusteredBlowUpDataSubtheorems P) :
    ManuscriptGeometricClusteredBlowUpDataSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson := h.lower_karlsson.toClusteredKarlssonBlowUpIncrementalLowerData

end ManuscriptGeometricPairCountedClusteredBlowUpDataSubtheorems

/-- Fully incremental concrete model data whose lower construction supplies
cluster fiber cardinalities and the six inter-cluster pair counts; same-cluster
pair counts are derived in Lean. -/
structure ConcreteFullyIncrementalFiberCountedClusteredBlowUpModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : CanonicalExactUpperGeometryIncrementalData P
  lower_karlsson : FiberCountedClusteredKarlssonBlowUpIncrementalLowerData P

namespace ConcreteFullyIncrementalFiberCountedClusteredBlowUpModelSubtheorems

def toConcreteFullyIncrementalPairCountedClusteredBlowUpModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ConcreteFullyIncrementalFiberCountedClusteredBlowUpModelSubtheorems P) :
    ConcreteFullyIncrementalPairCountedClusteredBlowUpModelSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson :=
    h.lower_karlsson.toPairCountedClusteredKarlssonBlowUpIncrementalLowerData

end ConcreteFullyIncrementalFiberCountedClusteredBlowUpModelSubtheorems

/-- Paper-style global geometric data whose lower construction supplies
cluster fiber cardinalities and the six inter-cluster pair counts. -/
structure ManuscriptGeometricFiberCountedClusteredBlowUpDataSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : ManuscriptGeometricIncrementalUpperData P
  lower_karlsson : FiberCountedClusteredKarlssonBlowUpIncrementalLowerData P

namespace ManuscriptGeometricFiberCountedClusteredBlowUpDataSubtheorems

def toManuscriptGeometricPairCountedClusteredBlowUpDataSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ManuscriptGeometricFiberCountedClusteredBlowUpDataSubtheorems P) :
    ManuscriptGeometricPairCountedClusteredBlowUpDataSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson :=
    h.lower_karlsson.toPairCountedClusteredKarlssonBlowUpIncrementalLowerData

end ManuscriptGeometricFiberCountedClusteredBlowUpDataSubtheorems

/-- Fully incremental concrete model data whose lower construction supplies
only cluster fiber cardinalities for the finite counting part. -/
structure ConcreteFullyIncrementalCardinalityClusteredBlowUpModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : CanonicalExactUpperGeometryIncrementalData P
  lower_karlsson : CardinalityClusteredKarlssonBlowUpIncrementalLowerData P

namespace ConcreteFullyIncrementalCardinalityClusteredBlowUpModelSubtheorems

def toConcreteFullyIncrementalFiberCountedClusteredBlowUpModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ConcreteFullyIncrementalCardinalityClusteredBlowUpModelSubtheorems P) :
    ConcreteFullyIncrementalFiberCountedClusteredBlowUpModelSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson :=
    h.lower_karlsson.toFiberCountedClusteredKarlssonBlowUpIncrementalLowerData

end ConcreteFullyIncrementalCardinalityClusteredBlowUpModelSubtheorems

/-- Paper-style global geometric data whose lower construction supplies only
cluster fiber cardinalities for the finite counting part. -/
structure ManuscriptGeometricCardinalityClusteredBlowUpDataSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : ManuscriptGeometricIncrementalUpperData P
  lower_karlsson : CardinalityClusteredKarlssonBlowUpIncrementalLowerData P

namespace ManuscriptGeometricCardinalityClusteredBlowUpDataSubtheorems

def toManuscriptGeometricFiberCountedClusteredBlowUpDataSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ManuscriptGeometricCardinalityClusteredBlowUpDataSubtheorems P) :
    ManuscriptGeometricFiberCountedClusteredBlowUpDataSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson :=
    h.lower_karlsson.toFiberCountedClusteredKarlssonBlowUpIncrementalLowerData

end ManuscriptGeometricCardinalityClusteredBlowUpDataSubtheorems

namespace ConcreteFullyIncrementalBlowUpModelSubtheorems

/-- Upgrade the older named-blow-up package to the cardinality-clustered
finite-counting package using the canonical four-fiber cluster witness. -/
noncomputable def toConcreteFullyIncrementalCardinalityClusteredBlowUpModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ConcreteFullyIncrementalBlowUpModelSubtheorems P) :
    ConcreteFullyIncrementalCardinalityClusteredBlowUpModelSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson :=
    h.lower_karlsson.toCardinalityClusteredKarlssonBlowUpIncrementalLowerData

end ConcreteFullyIncrementalBlowUpModelSubtheorems

namespace ManuscriptGeometricBlowUpDataSubtheorems

/-- Upgrade the older paper-style named-blow-up package to the
cardinality-clustered finite-counting package using the canonical four-fiber
cluster witness. -/
noncomputable def toManuscriptGeometricCardinalityClusteredBlowUpDataSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ManuscriptGeometricBlowUpDataSubtheorems P) :
    ManuscriptGeometricCardinalityClusteredBlowUpDataSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson :=
    h.lower_karlsson.toCardinalityClusteredKarlssonBlowUpIncrementalLowerData

end ManuscriptGeometricBlowUpDataSubtheorems

/-- Pair-counted lower obligations for a family with a named maximum count
function, in the concrete upper-data version. -/
def MaxConcreteFullyIncrementalPairCountedClusteredBlowUpModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ConcreteFullyIncrementalPairCountedClusteredBlowUpModelSubtheorems
    P.toProblemFamily

/-- Pair-counted lower obligations for a family with a named maximum count
function, in the paper-style geometric upper-data version. -/
def MaxManuscriptGeometricPairCountedClusteredBlowUpDataSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ManuscriptGeometricPairCountedClusteredBlowUpDataSubtheorems
    P.toProblemFamily

/-- Fiber-counted lower obligations for a family with a named maximum count
function, in the concrete upper-data version. -/
def MaxConcreteFullyIncrementalFiberCountedClusteredBlowUpModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ConcreteFullyIncrementalFiberCountedClusteredBlowUpModelSubtheorems
    P.toProblemFamily

/-- Fiber-counted lower obligations for a family with a named maximum count
function, in the paper-style geometric upper-data version. -/
def MaxManuscriptGeometricFiberCountedClusteredBlowUpDataSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ManuscriptGeometricFiberCountedClusteredBlowUpDataSubtheorems
    P.toProblemFamily

/-- Cardinality-only finite-counting lower obligations for a family with a
named maximum count function, in the concrete upper-data version. -/
def MaxConcreteFullyIncrementalCardinalityClusteredBlowUpModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ConcreteFullyIncrementalCardinalityClusteredBlowUpModelSubtheorems
    P.toProblemFamily

/-- Cardinality-only finite-counting lower obligations for a family with a
named maximum count function, in the paper-style geometric upper-data version. -/
def MaxManuscriptGeometricCardinalityClusteredBlowUpDataSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ManuscriptGeometricCardinalityClusteredBlowUpDataSubtheorems
    P.toProblemFamily

/-- Maximum-form Theorem 1 from concrete upper data and a pair-counted
clustered Karlsson blow-up lower construction. -/
theorem theorem_one_statement_proven_from_concrete_pair_counted_clustered_blowup_model
    (P : TheoremOne.ProblemFamily.{u})
    (h : ConcreteFullyIncrementalPairCountedClusteredBlowUpModelSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_concrete_clustered_blowup_model
    P h.toConcreteFullyIncrementalClusteredBlowUpModelSubtheorems

/-- Maximum-form Theorem 1 from paper-style geometric upper data and a
pair-counted clustered Karlsson blow-up lower construction. -/
theorem theorem_one_statement_proven_from_geometric_data_and_pair_counted_clustered_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : ManuscriptGeometricPairCountedClusteredBlowUpDataSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_geometric_data_and_clustered_blowup
    P h.toManuscriptGeometricClusteredBlowUpDataSubtheorems

/-- Formula-form Theorem 1 from concrete upper data and a pair-counted
clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_concrete_pair_counted_clustered_blowup_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteFullyIncrementalPairCountedClusteredBlowUpModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_concrete_clustered_blowup_model
    P h.toConcreteFullyIncrementalClusteredBlowUpModelSubtheorems

/-- Formula-form Theorem 1 from paper-style geometric upper data and a
pair-counted clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_geometric_data_and_pair_counted_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricPairCountedClusteredBlowUpDataSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_geometric_data_and_clustered_blowup
    P h.toManuscriptGeometricClusteredBlowUpDataSubtheorems

/-- Single-size displayed formula from concrete upper data and a pair-counted
clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_concrete_pair_counted_clustered_blowup_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteFullyIncrementalPairCountedClusteredBlowUpModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_concrete_pair_counted_clustered_blowup_model
    P h n

/-- Single-size displayed formula from paper-style geometric upper data and a
pair-counted clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_geometric_data_and_pair_counted_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricPairCountedClusteredBlowUpDataSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_geometric_data_and_pair_counted_clustered_blowup
    P h n

/-- Maximum-form Theorem 1 from concrete upper data and a fiber-counted
clustered Karlsson blow-up lower construction. -/
theorem theorem_one_statement_proven_from_concrete_fiber_counted_clustered_blowup_model
    (P : TheoremOne.ProblemFamily.{u})
    (h : ConcreteFullyIncrementalFiberCountedClusteredBlowUpModelSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_concrete_pair_counted_clustered_blowup_model
    P h.toConcreteFullyIncrementalPairCountedClusteredBlowUpModelSubtheorems

/-- Maximum-form Theorem 1 from paper-style geometric upper data and a
fiber-counted clustered Karlsson blow-up lower construction. -/
theorem theorem_one_statement_proven_from_geometric_data_and_fiber_counted_clustered_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : ManuscriptGeometricFiberCountedClusteredBlowUpDataSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_geometric_data_and_pair_counted_clustered_blowup
    P h.toManuscriptGeometricPairCountedClusteredBlowUpDataSubtheorems

/-- Formula-form Theorem 1 from concrete upper data and a fiber-counted
clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_concrete_fiber_counted_clustered_blowup_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteFullyIncrementalFiberCountedClusteredBlowUpModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_concrete_pair_counted_clustered_blowup_model
    P h.toConcreteFullyIncrementalPairCountedClusteredBlowUpModelSubtheorems

/-- Formula-form Theorem 1 from paper-style geometric upper data and a
fiber-counted clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_geometric_data_and_fiber_counted_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricFiberCountedClusteredBlowUpDataSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_geometric_data_and_pair_counted_clustered_blowup
    P h.toManuscriptGeometricPairCountedClusteredBlowUpDataSubtheorems

/-- Single-size displayed formula from concrete upper data and a fiber-counted
clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_concrete_fiber_counted_clustered_blowup_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteFullyIncrementalFiberCountedClusteredBlowUpModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_concrete_fiber_counted_clustered_blowup_model
    P h n

/-- Single-size displayed formula from paper-style geometric upper data and a
fiber-counted clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_geometric_data_and_fiber_counted_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricFiberCountedClusteredBlowUpDataSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_geometric_data_and_fiber_counted_clustered_blowup
    P h n

/-- Maximum-form Theorem 1 from concrete upper data and a cardinality-only
clustered Karlsson blow-up lower construction. -/
theorem theorem_one_statement_proven_from_concrete_cardinality_clustered_blowup_model
    (P : TheoremOne.ProblemFamily.{u})
    (h : ConcreteFullyIncrementalCardinalityClusteredBlowUpModelSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_concrete_fiber_counted_clustered_blowup_model
    P h.toConcreteFullyIncrementalFiberCountedClusteredBlowUpModelSubtheorems

/-- Maximum-form Theorem 1 from paper-style geometric upper data and a
cardinality-only clustered Karlsson blow-up lower construction. -/
theorem theorem_one_statement_proven_from_geometric_data_and_cardinality_clustered_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : ManuscriptGeometricCardinalityClusteredBlowUpDataSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_geometric_data_and_fiber_counted_clustered_blowup
    P h.toManuscriptGeometricFiberCountedClusteredBlowUpDataSubtheorems

/-- Formula-form Theorem 1 from concrete upper data and a cardinality-only
clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_concrete_cardinality_clustered_blowup_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteFullyIncrementalCardinalityClusteredBlowUpModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_concrete_fiber_counted_clustered_blowup_model
    P h.toConcreteFullyIncrementalFiberCountedClusteredBlowUpModelSubtheorems

/-- Formula-form Theorem 1 from paper-style geometric upper data and a
cardinality-only clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_geometric_data_and_cardinality_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricCardinalityClusteredBlowUpDataSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_geometric_data_and_fiber_counted_clustered_blowup
    P h.toManuscriptGeometricFiberCountedClusteredBlowUpDataSubtheorems

/-- Single-size displayed formula from concrete upper data and a
cardinality-only clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_concrete_cardinality_clustered_blowup_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteFullyIncrementalCardinalityClusteredBlowUpModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_concrete_cardinality_clustered_blowup_model
    P h n

/-- Single-size displayed formula from paper-style geometric upper data and a
cardinality-only clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_geometric_data_and_cardinality_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricCardinalityClusteredBlowUpDataSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_geometric_data_and_cardinality_clustered_blowup
    P h n

end ExplicitInputs
end TheoremOneManuscript
end Lollipop

/-!
Proof component 15: `Manuscript.PrimitiveGeometry.EndToEnd`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Theorem 1 endpoints from primitive coordinate lollipop records.

The upper side here names actual lollipop point sets, but still takes the
hard Euclidean crossing-count table and incremental region data as
certificates.  The lower side uses the named Karlsson blow-up construction
data from `ExplicitInputs`.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace PrimitiveGeometry

universe u

/-- Primitive coordinate upper data plus a named Karlsson blow-up lower
construction. -/
structure PrimitiveGeometryAndBlowUpSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : PrimitiveExactUpperGeometryData P
  lower_karlsson : ExplicitInputs.KarlssonBlowUpIncrementalLowerData P

namespace PrimitiveGeometryAndBlowUpSubtheorems

/-- Convert primitive coordinate lollipop records into the explicit concrete
blow-up package used by the proved theorem stack. -/
def toConcreteFullyIncrementalBlowUpModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveGeometryAndBlowUpSubtheorems P) :
    ExplicitInputs.ConcreteFullyIncrementalBlowUpModelSubtheorems P where
  upper_geometry := h.upper_geometry.toCanonicalExactUpperGeometryIncrementalData
  lower_karlsson := h.lower_karlsson

end PrimitiveGeometryAndBlowUpSubtheorems

/-- Carrier-certified primitive coordinate upper data plus a named Karlsson
blow-up lower construction. -/
structure PrimitiveCarrierGeometryAndBlowUpSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : PrimitiveCarrierCertifiedExactUpperGeometryData P
  lower_karlsson : ExplicitInputs.KarlssonBlowUpIncrementalLowerData P

namespace PrimitiveCarrierGeometryAndBlowUpSubtheorems

/-- Forget the finite carrier-intersection witnesses after converting them to
the primitive exact upper package. -/
def toPrimitiveGeometryAndBlowUpSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveCarrierGeometryAndBlowUpSubtheorems P) :
    PrimitiveGeometryAndBlowUpSubtheorems P where
  upper_geometry := h.upper_geometry.toPrimitiveExactUpperGeometryData
  lower_karlsson := h.lower_karlsson

end PrimitiveCarrierGeometryAndBlowUpSubtheorems

/-- Primitive coordinate upper data plus a four-cluster-table-certified
Karlsson blow-up lower construction. -/
structure PrimitiveGeometryAndTableBlowUpSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : PrimitiveExactUpperGeometryData P
  lower_karlsson : ExplicitInputs.KarlssonTableBlowUpIncrementalLowerData P

namespace PrimitiveGeometryAndTableBlowUpSubtheorems

/-- Convert table-certified lower data to the named-blow-up primitive package
after Lean derives the lower crossing polynomial from the table sum. -/
def toPrimitiveGeometryAndBlowUpSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveGeometryAndTableBlowUpSubtheorems P) :
    PrimitiveGeometryAndBlowUpSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson := h.lower_karlsson.toKarlssonBlowUpIncrementalLowerData

end PrimitiveGeometryAndTableBlowUpSubtheorems

/-- Carrier-certified primitive coordinate upper data plus a
four-cluster-table-certified Karlsson blow-up lower construction. -/
structure PrimitiveCarrierGeometryAndTableBlowUpSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : PrimitiveCarrierCertifiedExactUpperGeometryData P
  lower_karlsson : ExplicitInputs.KarlssonTableBlowUpIncrementalLowerData P

namespace PrimitiveCarrierGeometryAndTableBlowUpSubtheorems

/-- Forget carrier-intersection witnesses and convert table-certified lower
data to the named-blow-up primitive package. -/
def toPrimitiveCarrierGeometryAndBlowUpSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveCarrierGeometryAndTableBlowUpSubtheorems P) :
    PrimitiveCarrierGeometryAndBlowUpSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson := h.lower_karlsson.toKarlssonBlowUpIncrementalLowerData

end PrimitiveCarrierGeometryAndTableBlowUpSubtheorems

/-- Primitive coordinate upper data plus a clustered Karlsson blow-up lower
construction. -/
structure PrimitiveGeometryAndClusteredBlowUpSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : PrimitiveExactUpperGeometryData P
  lower_karlsson : ExplicitInputs.ClusteredKarlssonBlowUpIncrementalLowerData P

namespace PrimitiveGeometryAndClusteredBlowUpSubtheorems

/-- Convert clustered lower data to the table-certified primitive package. -/
def toPrimitiveGeometryAndTableBlowUpSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveGeometryAndClusteredBlowUpSubtheorems P) :
    PrimitiveGeometryAndTableBlowUpSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson := h.lower_karlsson.toKarlssonTableBlowUpIncrementalLowerData

end PrimitiveGeometryAndClusteredBlowUpSubtheorems

/-- Carrier-certified primitive coordinate upper data plus a clustered
Karlsson blow-up lower construction. -/
structure PrimitiveCarrierGeometryAndClusteredBlowUpSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : PrimitiveCarrierCertifiedExactUpperGeometryData P
  lower_karlsson : ExplicitInputs.ClusteredKarlssonBlowUpIncrementalLowerData P

namespace PrimitiveCarrierGeometryAndClusteredBlowUpSubtheorems

/-- Convert clustered lower data to the table-certified primitive carrier
package. -/
def toPrimitiveCarrierGeometryAndTableBlowUpSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveCarrierGeometryAndClusteredBlowUpSubtheorems P) :
    PrimitiveCarrierGeometryAndTableBlowUpSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson := h.lower_karlsson.toKarlssonTableBlowUpIncrementalLowerData

end PrimitiveCarrierGeometryAndClusteredBlowUpSubtheorems

/-- Maximum-form Theorem 1 from primitive coordinate lollipop records and a
named Karlsson blow-up lower construction. -/
theorem theorem_one_statement_proven_from_primitive_geometry_and_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : PrimitiveGeometryAndBlowUpSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact
    ExplicitInputs.theorem_one_statement_proven_from_concrete_blowup_model
      P h.toConcreteFullyIncrementalBlowUpModelSubtheorems

/-- Maximum-form Theorem 1 from carrier-certified primitive coordinate
lollipop records and a named Karlsson blow-up lower construction. -/
theorem theorem_one_statement_proven_from_primitive_carrier_geometry_and_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : PrimitiveCarrierGeometryAndBlowUpSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_primitive_geometry_and_blowup
    P h.toPrimitiveGeometryAndBlowUpSubtheorems

/-- Maximum-form Theorem 1 from primitive coordinate lollipop records and a
four-cluster-table-certified Karlsson blow-up lower construction. -/
theorem theorem_one_statement_proven_from_primitive_geometry_and_table_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : PrimitiveGeometryAndTableBlowUpSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_primitive_geometry_and_blowup
    P h.toPrimitiveGeometryAndBlowUpSubtheorems

/-- Maximum-form Theorem 1 from carrier-certified primitive coordinate
lollipop records and a four-cluster-table-certified Karlsson blow-up lower
construction. -/
theorem theorem_one_statement_proven_from_primitive_carrier_geometry_and_table_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : PrimitiveCarrierGeometryAndTableBlowUpSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_primitive_carrier_geometry_and_blowup
    P h.toPrimitiveCarrierGeometryAndBlowUpSubtheorems

/-- Maximum-form Theorem 1 from primitive coordinate lollipop records and a
clustered Karlsson blow-up lower construction. -/
theorem theorem_one_statement_proven_from_primitive_geometry_and_clustered_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : PrimitiveGeometryAndClusteredBlowUpSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_primitive_geometry_and_table_blowup
    P h.toPrimitiveGeometryAndTableBlowUpSubtheorems

/-- Maximum-form Theorem 1 from carrier-certified primitive coordinate
lollipop records and a clustered Karlsson blow-up lower construction. -/
theorem theorem_one_statement_proven_from_primitive_carrier_geometry_and_clustered_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : PrimitiveCarrierGeometryAndClusteredBlowUpSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_primitive_carrier_geometry_and_table_blowup
    P h.toPrimitiveCarrierGeometryAndTableBlowUpSubtheorems

/-- Primitive coordinate lollipop and named-blow-up obligations for a family
with a named maximum count function. -/
def MaxPrimitiveGeometryAndBlowUpSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  PrimitiveGeometryAndBlowUpSubtheorems P.toProblemFamily

/-- Carrier-certified primitive coordinate lollipop and named-blow-up
obligations for a family with a named maximum count function. -/
def MaxPrimitiveCarrierGeometryAndBlowUpSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  PrimitiveCarrierGeometryAndBlowUpSubtheorems P.toProblemFamily

/-- Primitive coordinate lollipop and table-certified named-blow-up
obligations for a family with a named maximum count function. -/
def MaxPrimitiveGeometryAndTableBlowUpSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  PrimitiveGeometryAndTableBlowUpSubtheorems P.toProblemFamily

/-- Carrier-certified primitive coordinate lollipop and table-certified
named-blow-up obligations for a family with a named maximum count function. -/
def MaxPrimitiveCarrierGeometryAndTableBlowUpSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  PrimitiveCarrierGeometryAndTableBlowUpSubtheorems P.toProblemFamily

/-- Primitive coordinate lollipop and clustered named-blow-up obligations for
a family with a named maximum count function. -/
def MaxPrimitiveGeometryAndClusteredBlowUpSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  PrimitiveGeometryAndClusteredBlowUpSubtheorems P.toProblemFamily

/-- Carrier-certified primitive coordinate lollipop and clustered named-blow-up
obligations for a family with a named maximum count function. -/
def MaxPrimitiveCarrierGeometryAndClusteredBlowUpSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  PrimitiveCarrierGeometryAndClusteredBlowUpSubtheorems P.toProblemFamily

/-- Formula-form Theorem 1 from primitive coordinate lollipop records and a
named Karlsson blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_primitive_geometry_and_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveGeometryAndBlowUpSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact
    ExplicitInputs.theorem_one_formula_statement_proven_from_concrete_blowup_model
      P h.toConcreteFullyIncrementalBlowUpModelSubtheorems

/-- Formula-form Theorem 1 from carrier-certified primitive coordinate
lollipop records and a named Karlsson blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveCarrierGeometryAndBlowUpSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_primitive_geometry_and_blowup
    P h.toPrimitiveGeometryAndBlowUpSubtheorems

/-- Formula-form Theorem 1 from primitive coordinate lollipop records and a
four-cluster-table-certified Karlsson blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_primitive_geometry_and_table_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveGeometryAndTableBlowUpSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_primitive_geometry_and_blowup
    P h.toPrimitiveGeometryAndBlowUpSubtheorems

/-- Formula-form Theorem 1 from carrier-certified primitive coordinate
lollipop records and a four-cluster-table-certified Karlsson blow-up lower
construction. -/
theorem theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_table_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveCarrierGeometryAndTableBlowUpSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_blowup
    P h.toPrimitiveCarrierGeometryAndBlowUpSubtheorems

/-- Formula-form Theorem 1 from primitive coordinate lollipop records and a
clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_primitive_geometry_and_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveGeometryAndClusteredBlowUpSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_primitive_geometry_and_table_blowup
    P h.toPrimitiveGeometryAndTableBlowUpSubtheorems

/-- Formula-form Theorem 1 from carrier-certified primitive coordinate
lollipop records and a clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveCarrierGeometryAndClusteredBlowUpSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_table_blowup
    P h.toPrimitiveCarrierGeometryAndTableBlowUpSubtheorems

/-- Single-size displayed formula from primitive coordinate lollipop records
and a named Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_primitive_geometry_and_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveGeometryAndBlowUpSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_primitive_geometry_and_blowup P h n

/-- Single-size displayed formula from carrier-certified primitive coordinate
lollipop records and a named Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_primitive_carrier_geometry_and_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveCarrierGeometryAndBlowUpSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_blowup P h n

/-- Single-size displayed formula from primitive coordinate lollipop records
and a four-cluster-table-certified Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_primitive_geometry_and_table_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveGeometryAndTableBlowUpSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_primitive_geometry_and_table_blowup P h n

/-- Single-size displayed formula from carrier-certified primitive coordinate
lollipop records and a four-cluster-table-certified Karlsson blow-up lower
construction. -/
theorem theorem_one_formula_at_proven_from_primitive_carrier_geometry_and_table_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveCarrierGeometryAndTableBlowUpSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_table_blowup P h n

/-- Single-size displayed formula from primitive coordinate lollipop records
and a clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_primitive_geometry_and_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveGeometryAndClusteredBlowUpSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_primitive_geometry_and_clustered_blowup P h n

/-- Single-size displayed formula from carrier-certified primitive coordinate
lollipop records and a clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_primitive_carrier_geometry_and_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveCarrierGeometryAndClusteredBlowUpSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_clustered_blowup P h n

end PrimitiveGeometry
end TheoremOneManuscript
end Lollipop

/-!
Proof component 16: `Manuscript.PrimitiveGeometry.PairCountedEndToEnd`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Primitive-geometry Theorem 1 endpoints with pair-counted clustered lower data.

This keeps the primitive coordinate upper packages separate from the new lower
pair-count layer.  The proof is by conversion to the already checked clustered
primitive endpoints.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace PrimitiveGeometry

universe u

/-- Primitive coordinate upper data plus a pair-counted clustered Karlsson
blow-up lower construction. -/
structure PrimitiveGeometryAndPairCountedClusteredBlowUpSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : PrimitiveExactUpperGeometryData P
  lower_karlsson :
    ExplicitInputs.PairCountedClusteredKarlssonBlowUpIncrementalLowerData P

namespace PrimitiveGeometryAndPairCountedClusteredBlowUpSubtheorems

def toPrimitiveGeometryAndClusteredBlowUpSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveGeometryAndPairCountedClusteredBlowUpSubtheorems P) :
    PrimitiveGeometryAndClusteredBlowUpSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson :=
    h.lower_karlsson.toClusteredKarlssonBlowUpIncrementalLowerData

end PrimitiveGeometryAndPairCountedClusteredBlowUpSubtheorems

/-- Carrier-certified primitive coordinate upper data plus a pair-counted
clustered Karlsson blow-up lower construction. -/
structure PrimitiveCarrierGeometryAndPairCountedClusteredBlowUpSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : PrimitiveCarrierCertifiedExactUpperGeometryData P
  lower_karlsson :
    ExplicitInputs.PairCountedClusteredKarlssonBlowUpIncrementalLowerData P

namespace PrimitiveCarrierGeometryAndPairCountedClusteredBlowUpSubtheorems

def toPrimitiveCarrierGeometryAndClusteredBlowUpSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveCarrierGeometryAndPairCountedClusteredBlowUpSubtheorems P) :
    PrimitiveCarrierGeometryAndClusteredBlowUpSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson :=
    h.lower_karlsson.toClusteredKarlssonBlowUpIncrementalLowerData

end PrimitiveCarrierGeometryAndPairCountedClusteredBlowUpSubtheorems

/-- Primitive coordinate upper data plus a fiber-counted clustered Karlsson
blow-up lower construction. -/
structure PrimitiveGeometryAndFiberCountedClusteredBlowUpSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : PrimitiveExactUpperGeometryData P
  lower_karlsson :
    ExplicitInputs.FiberCountedClusteredKarlssonBlowUpIncrementalLowerData P

namespace PrimitiveGeometryAndFiberCountedClusteredBlowUpSubtheorems

def toPrimitiveGeometryAndPairCountedClusteredBlowUpSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveGeometryAndFiberCountedClusteredBlowUpSubtheorems P) :
    PrimitiveGeometryAndPairCountedClusteredBlowUpSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson :=
    h.lower_karlsson.toPairCountedClusteredKarlssonBlowUpIncrementalLowerData

end PrimitiveGeometryAndFiberCountedClusteredBlowUpSubtheorems

/-- Carrier-certified primitive coordinate upper data plus a fiber-counted
clustered Karlsson blow-up lower construction. -/
structure PrimitiveCarrierGeometryAndFiberCountedClusteredBlowUpSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : PrimitiveCarrierCertifiedExactUpperGeometryData P
  lower_karlsson :
    ExplicitInputs.FiberCountedClusteredKarlssonBlowUpIncrementalLowerData P

namespace PrimitiveCarrierGeometryAndFiberCountedClusteredBlowUpSubtheorems

def toPrimitiveCarrierGeometryAndPairCountedClusteredBlowUpSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveCarrierGeometryAndFiberCountedClusteredBlowUpSubtheorems P) :
    PrimitiveCarrierGeometryAndPairCountedClusteredBlowUpSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson :=
    h.lower_karlsson.toPairCountedClusteredKarlssonBlowUpIncrementalLowerData

end PrimitiveCarrierGeometryAndFiberCountedClusteredBlowUpSubtheorems

/-- Primitive coordinate upper data plus a cardinality-only clustered
Karlsson blow-up lower construction. -/
structure PrimitiveGeometryAndCardinalityClusteredBlowUpSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : PrimitiveExactUpperGeometryData P
  lower_karlsson :
    ExplicitInputs.CardinalityClusteredKarlssonBlowUpIncrementalLowerData P

namespace PrimitiveGeometryAndCardinalityClusteredBlowUpSubtheorems

def toPrimitiveGeometryAndFiberCountedClusteredBlowUpSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveGeometryAndCardinalityClusteredBlowUpSubtheorems P) :
    PrimitiveGeometryAndFiberCountedClusteredBlowUpSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson :=
    h.lower_karlsson.toFiberCountedClusteredKarlssonBlowUpIncrementalLowerData

end PrimitiveGeometryAndCardinalityClusteredBlowUpSubtheorems

/-- Carrier-certified primitive coordinate upper data plus a cardinality-only
clustered Karlsson blow-up lower construction. -/
structure PrimitiveCarrierGeometryAndCardinalityClusteredBlowUpSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : PrimitiveCarrierCertifiedExactUpperGeometryData P
  lower_karlsson :
    ExplicitInputs.CardinalityClusteredKarlssonBlowUpIncrementalLowerData P

namespace PrimitiveCarrierGeometryAndCardinalityClusteredBlowUpSubtheorems

def toPrimitiveCarrierGeometryAndFiberCountedClusteredBlowUpSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveCarrierGeometryAndCardinalityClusteredBlowUpSubtheorems P) :
    PrimitiveCarrierGeometryAndFiberCountedClusteredBlowUpSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson :=
    h.lower_karlsson.toFiberCountedClusteredKarlssonBlowUpIncrementalLowerData

end PrimitiveCarrierGeometryAndCardinalityClusteredBlowUpSubtheorems

namespace PrimitiveGeometryAndBlowUpSubtheorems

/-- Upgrade primitive coordinate upper data plus ordinary named lower blow-up
data to the cardinality-clustered finite-counting package. -/
noncomputable def toPrimitiveGeometryAndCardinalityClusteredBlowUpSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveGeometryAndBlowUpSubtheorems P) :
    PrimitiveGeometryAndCardinalityClusteredBlowUpSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson :=
    h.lower_karlsson.toCardinalityClusteredKarlssonBlowUpIncrementalLowerData

end PrimitiveGeometryAndBlowUpSubtheorems

namespace PrimitiveCarrierGeometryAndBlowUpSubtheorems

/-- Upgrade carrier-certified primitive coordinate upper data plus ordinary
named lower blow-up data to the cardinality-clustered finite-counting package. -/
noncomputable def toPrimitiveCarrierGeometryAndCardinalityClusteredBlowUpSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveCarrierGeometryAndBlowUpSubtheorems P) :
    PrimitiveCarrierGeometryAndCardinalityClusteredBlowUpSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson :=
    h.lower_karlsson.toCardinalityClusteredKarlssonBlowUpIncrementalLowerData

end PrimitiveCarrierGeometryAndBlowUpSubtheorems

/-- Primitive coordinate and pair-counted lower obligations for a family with
a named maximum count function. -/
def MaxPrimitiveGeometryAndPairCountedClusteredBlowUpSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  PrimitiveGeometryAndPairCountedClusteredBlowUpSubtheorems P.toProblemFamily

/-- Carrier-certified primitive coordinate and pair-counted lower obligations
for a family with a named maximum count function. -/
def MaxPrimitiveCarrierGeometryAndPairCountedClusteredBlowUpSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  PrimitiveCarrierGeometryAndPairCountedClusteredBlowUpSubtheorems
    P.toProblemFamily

/-- Primitive coordinate and fiber-counted lower obligations for a family with
a named maximum count function. -/
def MaxPrimitiveGeometryAndFiberCountedClusteredBlowUpSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  PrimitiveGeometryAndFiberCountedClusteredBlowUpSubtheorems P.toProblemFamily

/-- Carrier-certified primitive coordinate and fiber-counted lower obligations
for a family with a named maximum count function. -/
def MaxPrimitiveCarrierGeometryAndFiberCountedClusteredBlowUpSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  PrimitiveCarrierGeometryAndFiberCountedClusteredBlowUpSubtheorems
    P.toProblemFamily

/-- Primitive coordinate and cardinality-only lower obligations for a family
with a named maximum count function. -/
def MaxPrimitiveGeometryAndCardinalityClusteredBlowUpSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  PrimitiveGeometryAndCardinalityClusteredBlowUpSubtheorems P.toProblemFamily

/-- Carrier-certified primitive coordinate and cardinality-only lower
obligations for a family with a named maximum count function. -/
def MaxPrimitiveCarrierGeometryAndCardinalityClusteredBlowUpSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  PrimitiveCarrierGeometryAndCardinalityClusteredBlowUpSubtheorems
    P.toProblemFamily

/-- Maximum-form Theorem 1 from primitive coordinate lollipop records and a
pair-counted clustered Karlsson blow-up lower construction. -/
theorem theorem_one_statement_proven_from_primitive_geometry_and_pair_counted_clustered_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : PrimitiveGeometryAndPairCountedClusteredBlowUpSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_primitive_geometry_and_clustered_blowup
    P h.toPrimitiveGeometryAndClusteredBlowUpSubtheorems

/-- Maximum-form Theorem 1 from carrier-certified primitive coordinate
lollipop records and a pair-counted clustered Karlsson blow-up lower
construction. -/
theorem theorem_one_statement_proven_from_primitive_carrier_geometry_and_pair_counted_clustered_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : PrimitiveCarrierGeometryAndPairCountedClusteredBlowUpSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_primitive_carrier_geometry_and_clustered_blowup
    P h.toPrimitiveCarrierGeometryAndClusteredBlowUpSubtheorems

/-- Formula-form Theorem 1 from primitive coordinate lollipop records and a
pair-counted clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_primitive_geometry_and_pair_counted_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveGeometryAndPairCountedClusteredBlowUpSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_primitive_geometry_and_clustered_blowup
    P h.toPrimitiveGeometryAndClusteredBlowUpSubtheorems

/-- Formula-form Theorem 1 from carrier-certified primitive coordinate
lollipop records and a pair-counted clustered Karlsson blow-up lower
construction. -/
theorem theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_pair_counted_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveCarrierGeometryAndPairCountedClusteredBlowUpSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_clustered_blowup
    P h.toPrimitiveCarrierGeometryAndClusteredBlowUpSubtheorems

/-- Single-size displayed formula from primitive coordinate lollipop records
and a pair-counted clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_primitive_geometry_and_pair_counted_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveGeometryAndPairCountedClusteredBlowUpSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_primitive_geometry_and_pair_counted_clustered_blowup
    P h n

/-- Single-size displayed formula from carrier-certified primitive coordinate
lollipop records and a pair-counted clustered Karlsson blow-up lower
construction. -/
theorem theorem_one_formula_at_proven_from_primitive_carrier_geometry_and_pair_counted_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveCarrierGeometryAndPairCountedClusteredBlowUpSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_pair_counted_clustered_blowup
    P h n

/-- Maximum-form Theorem 1 from primitive coordinate lollipop records and a
fiber-counted clustered Karlsson blow-up lower construction. -/
theorem theorem_one_statement_proven_from_primitive_geometry_and_fiber_counted_clustered_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : PrimitiveGeometryAndFiberCountedClusteredBlowUpSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_primitive_geometry_and_pair_counted_clustered_blowup
    P h.toPrimitiveGeometryAndPairCountedClusteredBlowUpSubtheorems

/-- Maximum-form Theorem 1 from carrier-certified primitive coordinate
lollipop records and a fiber-counted clustered Karlsson blow-up lower
construction. -/
theorem theorem_one_statement_proven_from_primitive_carrier_geometry_and_fiber_counted_clustered_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : PrimitiveCarrierGeometryAndFiberCountedClusteredBlowUpSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_primitive_carrier_geometry_and_pair_counted_clustered_blowup
    P h.toPrimitiveCarrierGeometryAndPairCountedClusteredBlowUpSubtheorems

/-- Formula-form Theorem 1 from primitive coordinate lollipop records and a
fiber-counted clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_primitive_geometry_and_fiber_counted_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveGeometryAndFiberCountedClusteredBlowUpSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_primitive_geometry_and_pair_counted_clustered_blowup
    P h.toPrimitiveGeometryAndPairCountedClusteredBlowUpSubtheorems

/-- Formula-form Theorem 1 from carrier-certified primitive coordinate
lollipop records and a fiber-counted clustered Karlsson blow-up lower
construction. -/
theorem theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_fiber_counted_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveCarrierGeometryAndFiberCountedClusteredBlowUpSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_pair_counted_clustered_blowup
    P h.toPrimitiveCarrierGeometryAndPairCountedClusteredBlowUpSubtheorems

/-- Single-size displayed formula from primitive coordinate lollipop records
and a fiber-counted clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_primitive_geometry_and_fiber_counted_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveGeometryAndFiberCountedClusteredBlowUpSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_primitive_geometry_and_fiber_counted_clustered_blowup
    P h n

/-- Single-size displayed formula from carrier-certified primitive coordinate
lollipop records and a fiber-counted clustered Karlsson blow-up lower
construction. -/
theorem theorem_one_formula_at_proven_from_primitive_carrier_geometry_and_fiber_counted_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveCarrierGeometryAndFiberCountedClusteredBlowUpSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_fiber_counted_clustered_blowup
    P h n

/-- Maximum-form Theorem 1 from primitive coordinate lollipop records and a
cardinality-only clustered Karlsson blow-up lower construction. -/
theorem theorem_one_statement_proven_from_primitive_geometry_and_cardinality_clustered_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : PrimitiveGeometryAndCardinalityClusteredBlowUpSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_primitive_geometry_and_fiber_counted_clustered_blowup
    P h.toPrimitiveGeometryAndFiberCountedClusteredBlowUpSubtheorems

/-- Maximum-form Theorem 1 from carrier-certified primitive coordinate
lollipop records and a cardinality-only clustered Karlsson blow-up lower
construction. -/
theorem theorem_one_statement_proven_from_primitive_carrier_geometry_and_cardinality_clustered_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : PrimitiveCarrierGeometryAndCardinalityClusteredBlowUpSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_primitive_carrier_geometry_and_fiber_counted_clustered_blowup
    P h.toPrimitiveCarrierGeometryAndFiberCountedClusteredBlowUpSubtheorems

/-- Formula-form Theorem 1 from primitive coordinate lollipop records and a
cardinality-only clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_statement_proven_from_primitive_geometry_and_cardinality_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveGeometryAndCardinalityClusteredBlowUpSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_primitive_geometry_and_fiber_counted_clustered_blowup
    P h.toPrimitiveGeometryAndFiberCountedClusteredBlowUpSubtheorems

/-- Formula-form Theorem 1 from carrier-certified primitive coordinate
lollipop records and a cardinality-only clustered Karlsson blow-up lower
construction. -/
theorem theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_cardinality_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveCarrierGeometryAndCardinalityClusteredBlowUpSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_fiber_counted_clustered_blowup
    P h.toPrimitiveCarrierGeometryAndFiberCountedClusteredBlowUpSubtheorems

/-- Single-size displayed formula from primitive coordinate lollipop records
and a cardinality-only clustered Karlsson blow-up lower construction. -/
theorem theorem_one_formula_at_proven_from_primitive_geometry_and_cardinality_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveGeometryAndCardinalityClusteredBlowUpSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_primitive_geometry_and_cardinality_clustered_blowup
    P h n

/-- Single-size displayed formula from carrier-certified primitive coordinate
lollipop records and a cardinality-only clustered Karlsson blow-up lower
construction. -/
theorem theorem_one_formula_at_proven_from_primitive_carrier_geometry_and_cardinality_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPrimitiveCarrierGeometryAndCardinalityClusteredBlowUpSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_cardinality_clustered_blowup
    P h n

end PrimitiveGeometry
end TheoremOneManuscript
end Lollipop

/-!
Proof component 17: `Manuscript.Proof`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Final manuscript-facing Theorem 1 entry points.

The files in this folder expose the paper's displayed formula using the sorted
finite extremum `manuscriptS`.  This file gives short theorem names for the
strongest current concrete endpoint: exact canonical upper geometry with the
upper region equation proved from the previous-pair insertion recurrence, and
sorted Karlsson lower data with the lower region equation proved from
incremental insertion data.
-/

namespace Lollipop
namespace TheoremOneManuscript

universe u

/-- Manuscript Theorem 1 in maximum form, from fully incremental concrete
upper/lower model subtheorems. -/
theorem theorem_one_maximum
    (P : TheoremOne.ProblemFamily.{u})
    (h : ConcreteFullyIncrementalModelSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_fully_incremental_concrete_model P h

/-- Manuscript Theorem 1 in the displayed formula form, using the sorted
definition of `S(n)`. -/
theorem theorem_one
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteFullyIncrementalModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_fully_incremental_concrete_model P h

/-- Single-size form of the manuscript's displayed Theorem 1 formula. -/
theorem theorem_one_at
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteFullyIncrementalModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one P h n

/-- Manuscript Theorem 1 in maximum form from the paper-style
close/intriguing geometric input and incremental sorted Karlsson lower data. -/
theorem theorem_one_maximum_from_geometric_inputs
    (P : TheoremOne.ProblemFamily.{u})
    (h : ManuscriptGeometricIncrementalModelSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_manuscript_geometric_incremental_model P h

/-- Manuscript Theorem 1 in displayed formula form from the paper-style
close/intriguing geometric input and incremental sorted Karlsson lower data. -/
theorem theorem_one_from_geometric_inputs
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricIncrementalModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_manuscript_geometric_incremental_model P h

/-- Single-size displayed formula from the paper-style close/intriguing
geometric input and incremental sorted Karlsson lower data. -/
theorem theorem_one_at_from_geometric_inputs
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricIncrementalModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_geometric_inputs P h n

/-- Manuscript Theorem 1 in maximum form from fully incremental global
paper-style geometric extractor data. -/
theorem theorem_one_maximum_from_geometric_data
    (P : TheoremOne.ProblemFamily.{u})
    (h : ManuscriptGeometricFullyIncrementalDataSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_manuscript_geometric_fully_incremental_data P h

/-- Manuscript Theorem 1 in displayed formula form from fully incremental
global paper-style geometric extractor data. -/
theorem theorem_one_from_geometric_data
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricFullyIncrementalDataSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_manuscript_geometric_fully_incremental_data P h

/-- Single-size displayed formula from fully incremental global paper-style
geometric extractor data. -/
theorem theorem_one_at_from_geometric_data
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricFullyIncrementalDataSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_geometric_data P h n

/-- Manuscript Theorem 1 in maximum form from concrete upper data and a named
Karlsson blow-up lower construction. -/
theorem theorem_one_maximum_from_explicit_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : ExplicitInputs.ConcreteFullyIncrementalBlowUpModelSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact ExplicitInputs.theorem_one_statement_proven_from_concrete_blowup_model P h

/-- Manuscript Theorem 1 in displayed formula form from concrete upper data
and a named Karlsson blow-up lower construction. -/
theorem theorem_one_from_explicit_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ExplicitInputs.MaxConcreteFullyIncrementalBlowUpModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact ExplicitInputs.theorem_one_formula_statement_proven_from_concrete_blowup_model P h

/-- Single-size displayed formula from concrete upper data and a named
Karlsson blow-up lower construction. -/
theorem theorem_one_at_from_explicit_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ExplicitInputs.MaxConcreteFullyIncrementalBlowUpModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_explicit_blowup P h n

/-- Manuscript Theorem 1 in maximum form from paper-style geometric upper
data and a named Karlsson blow-up lower construction. -/
theorem theorem_one_maximum_from_geometric_data_and_explicit_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : ExplicitInputs.ManuscriptGeometricBlowUpDataSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact ExplicitInputs.theorem_one_statement_proven_from_geometric_data_and_blowup P h

/-- Manuscript Theorem 1 in displayed formula form from paper-style
geometric upper data and a named Karlsson blow-up lower construction. -/
theorem theorem_one_from_geometric_data_and_explicit_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ExplicitInputs.MaxManuscriptGeometricBlowUpDataSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact ExplicitInputs.theorem_one_formula_statement_proven_from_geometric_data_and_blowup P h

/-- Single-size displayed formula from paper-style geometric upper data and a
named Karlsson blow-up lower construction. -/
theorem theorem_one_at_from_geometric_data_and_explicit_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ExplicitInputs.MaxManuscriptGeometricBlowUpDataSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_geometric_data_and_explicit_blowup P h n

/-- Manuscript Theorem 1 in maximum form from concrete upper data and a
four-cluster-table-certified Karlsson blow-up lower construction. -/
theorem theorem_one_maximum_from_table_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : ExplicitInputs.ConcreteFullyIncrementalTableBlowUpModelSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact ExplicitInputs.theorem_one_statement_proven_from_concrete_table_blowup_model P h

/-- Manuscript Theorem 1 in displayed formula form from concrete upper data
and a four-cluster-table-certified Karlsson blow-up lower construction. -/
theorem theorem_one_from_table_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ExplicitInputs.MaxConcreteFullyIncrementalTableBlowUpModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact ExplicitInputs.theorem_one_formula_statement_proven_from_concrete_table_blowup_model P h

/-- Single-size displayed formula from concrete upper data and a
four-cluster-table-certified Karlsson blow-up lower construction. -/
theorem theorem_one_at_from_table_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ExplicitInputs.MaxConcreteFullyIncrementalTableBlowUpModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_table_blowup P h n

/-- Manuscript Theorem 1 in maximum form from paper-style geometric upper
data and a four-cluster-table-certified Karlsson blow-up lower construction. -/
theorem theorem_one_maximum_from_geometric_data_and_table_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : ExplicitInputs.ManuscriptGeometricTableBlowUpDataSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact ExplicitInputs.theorem_one_statement_proven_from_geometric_data_and_table_blowup P h

/-- Manuscript Theorem 1 in displayed formula form from paper-style
geometric upper data and a four-cluster-table-certified Karlsson blow-up lower
construction. -/
theorem theorem_one_from_geometric_data_and_table_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ExplicitInputs.MaxManuscriptGeometricTableBlowUpDataSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact ExplicitInputs.theorem_one_formula_statement_proven_from_geometric_data_and_table_blowup P h

/-- Single-size displayed formula from paper-style geometric upper data and a
four-cluster-table-certified Karlsson blow-up lower construction. -/
theorem theorem_one_at_from_geometric_data_and_table_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ExplicitInputs.MaxManuscriptGeometricTableBlowUpDataSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_geometric_data_and_table_blowup P h n

/-- Manuscript Theorem 1 in maximum form from primitive coordinate lollipop
records and a named Karlsson blow-up lower construction. -/
theorem theorem_one_maximum_from_primitive_geometry_and_explicit_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : PrimitiveGeometry.PrimitiveGeometryAndBlowUpSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact
    PrimitiveGeometry.theorem_one_statement_proven_from_primitive_geometry_and_blowup
      P h

/-- Manuscript Theorem 1 in displayed formula form from primitive coordinate
lollipop records and a named Karlsson blow-up lower construction. -/
theorem theorem_one_from_primitive_geometry_and_explicit_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveGeometry.MaxPrimitiveGeometryAndBlowUpSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact
    PrimitiveGeometry.theorem_one_formula_statement_proven_from_primitive_geometry_and_blowup
      P h

/-- Single-size displayed formula from primitive coordinate lollipop records
and a named Karlsson blow-up lower construction. -/
theorem theorem_one_at_from_primitive_geometry_and_explicit_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveGeometry.MaxPrimitiveGeometryAndBlowUpSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_primitive_geometry_and_explicit_blowup P h n

/-- Manuscript Theorem 1 in maximum form from carrier-certified primitive
coordinate lollipop records and a named Karlsson blow-up lower construction. -/
theorem theorem_one_maximum_from_primitive_carrier_geometry_and_explicit_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : PrimitiveGeometry.PrimitiveCarrierGeometryAndBlowUpSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact
    PrimitiveGeometry.theorem_one_statement_proven_from_primitive_carrier_geometry_and_blowup
      P h

/-- Manuscript Theorem 1 in displayed formula form from carrier-certified
primitive coordinate lollipop records and a named Karlsson blow-up lower
construction. -/
theorem theorem_one_from_primitive_carrier_geometry_and_explicit_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveGeometry.MaxPrimitiveCarrierGeometryAndBlowUpSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact
    PrimitiveGeometry.theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_blowup
      P h

/-- Single-size displayed formula from carrier-certified primitive coordinate
lollipop records and a named Karlsson blow-up lower construction. -/
theorem theorem_one_at_from_primitive_carrier_geometry_and_explicit_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveGeometry.MaxPrimitiveCarrierGeometryAndBlowUpSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_primitive_carrier_geometry_and_explicit_blowup P h n

/-- Manuscript Theorem 1 in maximum form from primitive coordinate lollipop
records and a four-cluster-table-certified Karlsson blow-up lower
construction. -/
theorem theorem_one_maximum_from_primitive_geometry_and_table_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : PrimitiveGeometry.PrimitiveGeometryAndTableBlowUpSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact
    PrimitiveGeometry.theorem_one_statement_proven_from_primitive_geometry_and_table_blowup
      P h

/-- Manuscript Theorem 1 in displayed formula form from primitive coordinate
lollipop records and a four-cluster-table-certified Karlsson blow-up lower
construction. -/
theorem theorem_one_from_primitive_geometry_and_table_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveGeometry.MaxPrimitiveGeometryAndTableBlowUpSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact
    PrimitiveGeometry.theorem_one_formula_statement_proven_from_primitive_geometry_and_table_blowup
      P h

/-- Single-size displayed formula from primitive coordinate lollipop records
and a four-cluster-table-certified Karlsson blow-up lower construction. -/
theorem theorem_one_at_from_primitive_geometry_and_table_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveGeometry.MaxPrimitiveGeometryAndTableBlowUpSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_primitive_geometry_and_table_blowup P h n

/-- Manuscript Theorem 1 in maximum form from carrier-certified primitive
coordinate lollipop records and a four-cluster-table-certified Karlsson
blow-up lower construction. -/
theorem theorem_one_maximum_from_primitive_carrier_geometry_and_table_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : PrimitiveGeometry.PrimitiveCarrierGeometryAndTableBlowUpSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact
    PrimitiveGeometry.theorem_one_statement_proven_from_primitive_carrier_geometry_and_table_blowup
      P h

/-- Manuscript Theorem 1 in displayed formula form from carrier-certified
primitive coordinate lollipop records and a four-cluster-table-certified
Karlsson blow-up lower construction. -/
theorem theorem_one_from_primitive_carrier_geometry_and_table_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveGeometry.MaxPrimitiveCarrierGeometryAndTableBlowUpSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact
    PrimitiveGeometry.theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_table_blowup
      P h

/-- Single-size displayed formula from carrier-certified primitive coordinate
lollipop records and a four-cluster-table-certified Karlsson blow-up lower
construction. -/
theorem theorem_one_at_from_primitive_carrier_geometry_and_table_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveGeometry.MaxPrimitiveCarrierGeometryAndTableBlowUpSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_primitive_carrier_geometry_and_table_blowup P h n

/-- Manuscript Theorem 1 in maximum form from concrete upper data and a
clustered Karlsson blow-up lower construction. -/
theorem theorem_one_maximum_from_clustered_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : ExplicitInputs.ConcreteFullyIncrementalClusteredBlowUpModelSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact ExplicitInputs.theorem_one_statement_proven_from_concrete_clustered_blowup_model P h

/-- Manuscript Theorem 1 in displayed formula form from concrete upper data
and a clustered Karlsson blow-up lower construction. -/
theorem theorem_one_from_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ExplicitInputs.MaxConcreteFullyIncrementalClusteredBlowUpModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact ExplicitInputs.theorem_one_formula_statement_proven_from_concrete_clustered_blowup_model P h

/-- Single-size displayed formula from concrete upper data and a clustered
Karlsson blow-up lower construction. -/
theorem theorem_one_at_from_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ExplicitInputs.MaxConcreteFullyIncrementalClusteredBlowUpModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_clustered_blowup P h n

/-- Manuscript Theorem 1 in maximum form from paper-style geometric upper
data and a clustered Karlsson blow-up lower construction. -/
theorem theorem_one_maximum_from_geometric_data_and_clustered_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : ExplicitInputs.ManuscriptGeometricClusteredBlowUpDataSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact ExplicitInputs.theorem_one_statement_proven_from_geometric_data_and_clustered_blowup P h

/-- Manuscript Theorem 1 in displayed formula form from paper-style geometric
upper data and a clustered Karlsson blow-up lower construction. -/
theorem theorem_one_from_geometric_data_and_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ExplicitInputs.MaxManuscriptGeometricClusteredBlowUpDataSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact ExplicitInputs.theorem_one_formula_statement_proven_from_geometric_data_and_clustered_blowup P h

/-- Single-size displayed formula from paper-style geometric upper data and a
clustered Karlsson blow-up lower construction. -/
theorem theorem_one_at_from_geometric_data_and_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ExplicitInputs.MaxManuscriptGeometricClusteredBlowUpDataSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_geometric_data_and_clustered_blowup P h n

/-- Manuscript Theorem 1 in maximum form from primitive coordinate lollipop
records and a clustered Karlsson blow-up lower construction. -/
theorem theorem_one_maximum_from_primitive_geometry_and_clustered_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : PrimitiveGeometry.PrimitiveGeometryAndClusteredBlowUpSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact
    PrimitiveGeometry.theorem_one_statement_proven_from_primitive_geometry_and_clustered_blowup
      P h

/-- Manuscript Theorem 1 in displayed formula form from primitive coordinate
lollipop records and a clustered Karlsson blow-up lower construction. -/
theorem theorem_one_from_primitive_geometry_and_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveGeometry.MaxPrimitiveGeometryAndClusteredBlowUpSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact
    PrimitiveGeometry.theorem_one_formula_statement_proven_from_primitive_geometry_and_clustered_blowup
      P h

/-- Single-size displayed formula from primitive coordinate lollipop records
and a clustered Karlsson blow-up lower construction. -/
theorem theorem_one_at_from_primitive_geometry_and_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveGeometry.MaxPrimitiveGeometryAndClusteredBlowUpSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_primitive_geometry_and_clustered_blowup P h n

/-- Manuscript Theorem 1 in maximum form from carrier-certified primitive
coordinate lollipop records and a clustered Karlsson blow-up lower
construction. -/
theorem theorem_one_maximum_from_primitive_carrier_geometry_and_clustered_blowup
    (P : TheoremOne.ProblemFamily.{u})
    (h : PrimitiveGeometry.PrimitiveCarrierGeometryAndClusteredBlowUpSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact
    PrimitiveGeometry.theorem_one_statement_proven_from_primitive_carrier_geometry_and_clustered_blowup
      P h

/-- Manuscript Theorem 1 in displayed formula form from carrier-certified
primitive coordinate lollipop records and a clustered Karlsson blow-up lower
construction. -/
theorem theorem_one_from_primitive_carrier_geometry_and_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveGeometry.MaxPrimitiveCarrierGeometryAndClusteredBlowUpSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact
    PrimitiveGeometry.theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_clustered_blowup
      P h

/-- Single-size displayed formula from carrier-certified primitive coordinate
lollipop records and a clustered Karlsson blow-up lower construction. -/
theorem theorem_one_at_from_primitive_carrier_geometry_and_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveGeometry.MaxPrimitiveCarrierGeometryAndClusteredBlowUpSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_primitive_carrier_geometry_and_clustered_blowup P h n

end TheoremOneManuscript
end Lollipop

/-!
Proof component 18: `Manuscript.Formalization.CardinalityClusteredBridge`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Minimal theorem bridge for the final manuscript formalization.

The lower-bound stack used by the final theorem routes through the
cardinality-clustered Karlsson blow-up construction.  This file exposes only
that bridge, avoiding the older collection of theorem-one wrapper variants.
-/

namespace Lollipop
namespace TheoremOneManuscript

universe u

/-- Manuscript Theorem 1 in displayed formula form from concrete upper data
and a cardinality-only clustered Karlsson blow-up lower construction. -/
theorem theorem_one_from_cardinality_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h :
      ExplicitInputs.MaxConcreteFullyIncrementalCardinalityClusteredBlowUpModelSubtheorems
        P) :
    TheoremOneFormulaStatement P := by
  exact
    ExplicitInputs.theorem_one_formula_statement_proven_from_concrete_cardinality_clustered_blowup_model
      P h

/-- Manuscript Theorem 1 in displayed formula form from paper-style geometric
upper data and a cardinality-only clustered Karlsson blow-up lower
construction. -/
theorem theorem_one_from_geometric_data_and_cardinality_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h :
      ExplicitInputs.MaxManuscriptGeometricCardinalityClusteredBlowUpDataSubtheorems
        P) :
    TheoremOneFormulaStatement P := by
  exact
    ExplicitInputs.theorem_one_formula_statement_proven_from_geometric_data_and_cardinality_clustered_blowup
      P h

/-- Manuscript Theorem 1 in displayed formula form from primitive coordinate
lollipop records and a cardinality-only clustered Karlsson blow-up lower
construction. -/
theorem theorem_one_from_primitive_geometry_and_cardinality_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveGeometry.MaxPrimitiveGeometryAndCardinalityClusteredBlowUpSubtheorems
      P) :
    TheoremOneFormulaStatement P := by
  exact
    PrimitiveGeometry.theorem_one_formula_statement_proven_from_primitive_geometry_and_cardinality_clustered_blowup
      P h

/-- Manuscript Theorem 1 in displayed formula form from carrier-certified
primitive coordinate lollipop records and a cardinality-only clustered
Karlsson blow-up lower construction. -/
theorem theorem_one_from_primitive_carrier_geometry_and_cardinality_clustered_blowup
    (P : TheoremOne.MaxProblemFamily.{u})
    (h :
      PrimitiveGeometry.MaxPrimitiveCarrierGeometryAndCardinalityClusteredBlowUpSubtheorems
        P) :
    TheoremOneFormulaStatement P := by
  exact
    PrimitiveGeometry.theorem_one_formula_statement_proven_from_primitive_carrier_geometry_and_cardinality_clustered_blowup
      P h

end TheoremOneManuscript
end Lollipop

/-!
Proof component 19: `Manuscript.Formalization.FromSubtheorems`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Manuscript Theorem 1 as a statement proved from named subtheorem packages.

This file is intentionally small and theorem-facing.  The finite lower
counting step routes through the cardinality-clustered formalization: for each
sorted quadruple Lean builds the canonical four-fiber cluster map, proves the
same/inter-cluster pair counts from finite cardinalities, collapses the pair
sum to Karlsson's table, and then invokes the existing upper/lower theorem
stack.
-/

namespace Lollipop
namespace TheoremOneManuscript

universe u

/-- Theorem 1 in the manuscript's displayed formula form. -/
abbrev TheoremOneStatement (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  TheoremOneFormulaStatement P

/-- The concrete subtheorem package: exact incremental upper geometry plus
named incremental Karlsson blow-up lower data. -/
abbrev ConcreteTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ExplicitInputs.MaxConcreteFullyIncrementalBlowUpModelSubtheorems P

/-- The paper-style geometric subtheorem package: global upper geometry plus
named incremental Karlsson blow-up lower data. -/
abbrev GeometricTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ExplicitInputs.MaxManuscriptGeometricBlowUpDataSubtheorems P

/-- The primitive-coordinate subtheorem package. -/
abbrev PrimitiveTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  PrimitiveGeometry.MaxPrimitiveGeometryAndBlowUpSubtheorems P

/-- The carrier-certified primitive-coordinate subtheorem package. -/
abbrev PrimitiveCarrierTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  PrimitiveGeometry.MaxPrimitiveCarrierGeometryAndBlowUpSubtheorems P

/-- Theorem 1 from the concrete named subtheorems, with finite lower counting
proved via the canonical cardinality-clustered layer. -/
theorem theorem_one_from_concrete_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ConcreteTheoremOneSubtheorems P) :
    TheoremOneStatement P := by
  exact theorem_one_from_cardinality_clustered_blowup P
    h.toConcreteFullyIncrementalCardinalityClusteredBlowUpModelSubtheorems

/-- Single-size form of Theorem 1 from the concrete named subtheorems. -/
theorem theorem_one_at_from_concrete_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ConcreteTheoremOneSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_concrete_subtheorems P h n

/-- Theorem 1 from the paper-style geometric named subtheorems, with finite
lower counting proved via the canonical cardinality-clustered layer. -/
theorem theorem_one_from_geometric_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : GeometricTheoremOneSubtheorems P) :
    TheoremOneStatement P := by
  exact theorem_one_from_geometric_data_and_cardinality_clustered_blowup P
    h.toManuscriptGeometricCardinalityClusteredBlowUpDataSubtheorems

/-- Single-size form of Theorem 1 from the paper-style geometric named
subtheorems. -/
theorem theorem_one_at_from_geometric_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : GeometricTheoremOneSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_geometric_subtheorems P h n

/-- Theorem 1 from primitive-coordinate subtheorems, with finite lower
counting proved via the canonical cardinality-clustered layer. -/
theorem theorem_one_from_primitive_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveTheoremOneSubtheorems P) :
    TheoremOneStatement P := by
  exact theorem_one_from_primitive_geometry_and_cardinality_clustered_blowup P
    h.toPrimitiveGeometryAndCardinalityClusteredBlowUpSubtheorems

/-- Single-size form of Theorem 1 from primitive-coordinate subtheorems. -/
theorem theorem_one_at_from_primitive_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveTheoremOneSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_primitive_subtheorems P h n

/-- Theorem 1 from carrier-certified primitive-coordinate subtheorems, with
finite lower counting proved via the canonical cardinality-clustered layer. -/
theorem theorem_one_from_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveCarrierTheoremOneSubtheorems P) :
    TheoremOneStatement P := by
  exact
    theorem_one_from_primitive_carrier_geometry_and_cardinality_clustered_blowup
      P h.toPrimitiveCarrierGeometryAndCardinalityClusteredBlowUpSubtheorems

/-- Single-size form of Theorem 1 from carrier-certified primitive-coordinate
subtheorems. -/
theorem theorem_one_at_from_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PrimitiveCarrierTheoremOneSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_primitive_carrier_subtheorems P h n

end TheoremOneManuscript
end Lollipop

/-!
Proof component 20: `Manuscript.ExplicitInputs.KarlssonBase`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Karlsson four-base lower construction data.

The OEIS/Karlsson construction starts from four lollipops whose unordered
pair crossing table is

* one exceptional pair with `5` crossings;
* the other five inter-base pairs with `7` crossings.

This file makes that base table explicit and separates it from the later
local blow-up/perturbation certificate.  Lean proves that a construction whose
copies inherit this four-base table supplies the pairwise lower interface, and
hence the already-proved Karlsson lower polynomial.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace ExplicitInputs

universe u

open BigOperators

/-- The exact pair table for the four Karlsson base lollipops.  It is the
same symmetric table later used by the cluster blow-up: same-cluster pairs
have value `4`, the exceptional base pair `(0,1)` has value `5`, and the
remaining inter-base pairs have value `7`. -/
def karlssonBasePairCrossing (a b : Fin 4) : Rat :=
  karlssonClusterPairCrossing a b

theorem karlssonBasePairCrossing_symm (a b : Fin 4) :
    karlssonBasePairCrossing a b =
      karlssonBasePairCrossing b a :=
  karlssonClusterPairCrossing_symm a b

@[simp] theorem karlssonBasePairCrossing_same (a : Fin 4) :
    karlssonBasePairCrossing a a = 4 := by
  simp [karlssonBasePairCrossing, karlssonClusterPairCrossing]

@[simp] theorem karlssonBasePairCrossing_zero_one :
    karlssonBasePairCrossing (0 : Fin 4) (1 : Fin 4) = 5 := by
  norm_num [karlssonBasePairCrossing, karlssonClusterPairCrossing]

@[simp] theorem karlssonBasePairCrossing_zero_two :
    karlssonBasePairCrossing (0 : Fin 4) (2 : Fin 4) = 7 := by
  decide

@[simp] theorem karlssonBasePairCrossing_zero_three :
    karlssonBasePairCrossing (0 : Fin 4) (3 : Fin 4) = 7 := by
  decide

@[simp] theorem karlssonBasePairCrossing_one_two :
    karlssonBasePairCrossing (1 : Fin 4) (2 : Fin 4) = 7 := by
  decide

@[simp] theorem karlssonBasePairCrossing_one_three :
    karlssonBasePairCrossing (1 : Fin 4) (3 : Fin 4) = 7 := by
  decide

@[simp] theorem karlssonBasePairCrossing_two_three :
    karlssonBasePairCrossing (2 : Fin 4) (3 : Fin 4) = 7 := by
  decide

/-- The visible six-entry Karlsson base table sums to `40`. -/
theorem karlssonBasePairCrossing_six_pair_sum_eq_forty :
    karlssonBasePairCrossing (0 : Fin 4) (1 : Fin 4) +
      karlssonBasePairCrossing (0 : Fin 4) (2 : Fin 4) +
      karlssonBasePairCrossing (0 : Fin 4) (3 : Fin 4) +
      karlssonBasePairCrossing (1 : Fin 4) (2 : Fin 4) +
      karlssonBasePairCrossing (1 : Fin 4) (3 : Fin 4) +
      karlssonBasePairCrossing (2 : Fin 4) (3 : Fin 4) = 40 := by
  norm_num

/-- A concrete four-base pair table certified by the six visible unordered
Karlsson values plus symmetry.  This is closer to the manuscript table than
the theorem-facing universal `∀ a b, a ≠ b` field. -/
structure KarlssonBaseSixPairTableCertificate
    (baseCross : Fin 4 → Fin 4 → Rat) where
  symm : ∀ a b : Fin 4, baseCross a b = baseCross b a
  zero_one : baseCross (0 : Fin 4) (1 : Fin 4) = 5
  zero_two : baseCross (0 : Fin 4) (2 : Fin 4) = 7
  zero_three : baseCross (0 : Fin 4) (3 : Fin 4) = 7
  one_two : baseCross (1 : Fin 4) (2 : Fin 4) = 7
  one_three : baseCross (1 : Fin 4) (3 : Fin 4) = 7
  two_three : baseCross (2 : Fin 4) (3 : Fin 4) = 7

namespace KarlssonBaseSixPairTableCertificate

/-- The six-entry symmetric table certificate expands to the universal
distinct-label table agreement used by the lower-bound theorem stack. -/
theorem base_pair_cross_eq_karlsson
    {baseCross : Fin 4 → Fin 4 → Rat}
    (h : KarlssonBaseSixPairTableCertificate baseCross) :
    ∀ a b : Fin 4, a ≠ b →
      baseCross a b = karlssonBasePairCrossing a b := by
  intro a b hab
  fin_cases a <;> fin_cases b
  · contradiction
  · simpa [karlssonBasePairCrossing, karlssonClusterPairCrossing]
      using h.zero_one
  · simpa [karlssonBasePairCrossing, karlssonClusterPairCrossing]
      using h.zero_two
  · simpa [karlssonBasePairCrossing, karlssonClusterPairCrossing]
      using h.zero_three
  · rw [h.symm]
    simpa [karlssonBasePairCrossing, karlssonClusterPairCrossing]
      using h.zero_one
  · contradiction
  · simpa [karlssonBasePairCrossing, karlssonClusterPairCrossing]
      using h.one_two
  · simpa [karlssonBasePairCrossing, karlssonClusterPairCrossing]
      using h.one_three
  · rw [h.symm]
    simpa [karlssonBasePairCrossing, karlssonClusterPairCrossing]
      using h.zero_two
  · rw [h.symm]
    simpa [karlssonBasePairCrossing, karlssonClusterPairCrossing]
      using h.one_two
  · contradiction
  · simpa [karlssonBasePairCrossing, karlssonClusterPairCrossing]
      using h.two_three
  · rw [h.symm]
    simpa [karlssonBasePairCrossing, karlssonClusterPairCrossing]
      using h.zero_three
  · rw [h.symm]
    simpa [karlssonBasePairCrossing, karlssonClusterPairCrossing]
      using h.one_three
  · rw [h.symm]
    simpa [karlssonBasePairCrossing, karlssonClusterPairCrossing]
      using h.two_three
  · contradiction

end KarlssonBaseSixPairTableCertificate

/-- The displayed Karlsson base table itself satisfies the six-pair symmetric
table certificate. -/
def karlssonBasePairCrossing_sixPairTableCertificate :
    KarlssonBaseSixPairTableCertificate karlssonBasePairCrossing where
  symm := karlssonBasePairCrossing_symm
  zero_one := karlssonBasePairCrossing_zero_one
  zero_two := karlssonBasePairCrossing_zero_two
  zero_three := karlssonBasePairCrossing_zero_three
  one_two := karlssonBasePairCrossing_one_two
  one_three := karlssonBasePairCrossing_one_three
  two_three := karlssonBasePairCrossing_two_three

/-- The unordered-pair finite sum over the four base lollipops is `40`. -/
theorem pairSum_four_karlssonBasePairCrossing_eq_forty :
    pairSum 4 karlssonBasePairCrossing = 40 := by
  have hpair : pairFinset 4 =
      {((0 : Fin 4), (1 : Fin 4)), ((0 : Fin 4), (2 : Fin 4)),
        ((0 : Fin 4), (3 : Fin 4)), ((1 : Fin 4), (2 : Fin 4)),
        ((1 : Fin 4), (3 : Fin 4)), ((2 : Fin 4), (3 : Fin 4))} := by
    ext p
    rcases p with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [pairFinset]
  unfold pairSum
  rw [hpair]
  simp [karlssonBasePairCrossing_zero_one, karlssonBasePairCrossing_zero_two,
    karlssonBasePairCrossing_zero_three, karlssonBasePairCrossing_one_two,
    karlssonBasePairCrossing_one_three, karlssonBasePairCrossing_two_three]
  norm_num

/-- Any concrete four-base crossing table agreeing with Karlsson's table on
distinct base pairs has unordered-pair sum `40`. -/
theorem pairSum_four_eq_forty_of_base_pair_crossing_eq
    {baseCross : Fin 4 → Fin 4 → Rat}
    (hbase :
      ∀ a b : Fin 4, a ≠ b →
        baseCross a b = karlssonBasePairCrossing a b) :
    pairSum 4 baseCross = 40 := by
  rw [show pairSum 4 baseCross = pairSum 4 karlssonBasePairCrossing by
    unfold pairSum
    apply Finset.sum_congr rfl
    intro p hp
    have hp_lt : p.1 < p.2 := by
      rw [pairFinset, Finset.mem_filter] at hp
      exact hp.2
    exact hbase p.1 p.2 (ne_of_lt hp_lt)]
  exact pairSum_four_karlssonBasePairCrossing_eq_forty

/-- Pair value for two blown-up copies as inherited from a four-base table. -/
def karlssonBaseCopyPairCrossing
    (baseCross : Fin 4 → Fin 4 → Rat)
    {n : Nat} (cluster : Fin n → Fin 4) (i j : Fin n) : Rat :=
  if cluster i = cluster j then 4 else baseCross (cluster i) (cluster j)

/-- One local lower copy-pair certificate: the produced pair crossing value is
the value inherited from either the same-cluster case or the relevant
Karlsson base pair. -/
structure LocalKarlssonBaseCopyPairCrossingData
    (baseCross : Fin 4 → Fin 4 → Rat)
    {n : Nat} (cluster : Fin n → Fin 4)
    (pairCross : Fin n → Fin n → Rat)
    (i j : Fin n) (_hij : i < j) where
  pair_cross_eq :
    pairCross i j =
      karlssonBaseCopyPairCrossing baseCross cluster i j

/-- Local lower copy-pair certificates assemble into the universal pair-value
statement used by the lower-bound theorem stack. -/
theorem pair_cross_eq_base_copy_from_local
    {baseCross : Fin 4 → Fin 4 → Rat}
    {n : Nat} {cluster : Fin n → Fin 4}
    {pairCross : Fin n → Fin n → Rat}
    (loc :
      ∀ i j : Fin n, ∀ hij : i < j,
        LocalKarlssonBaseCopyPairCrossingData
          baseCross cluster pairCross i j hij) :
    ∀ i j : Fin n, ∀ _hij : i < j,
      pairCross i j =
        karlssonBaseCopyPairCrossing baseCross cluster i j := by
  intro i j hij
  exact (loc i j hij).pair_cross_eq

/-- If the four-base table is Karlsson's table on distinct base labels, then
the inherited copy-pair table is exactly the cluster table used in the lower
polynomial. -/
theorem karlssonBaseCopyPairCrossing_eq_clusterPairCrossing
    {baseCross : Fin 4 → Fin 4 → Rat}
    (hbase :
      ∀ a b : Fin 4, a ≠ b →
        baseCross a b = karlssonBasePairCrossing a b)
    {n : Nat} (cluster : Fin n → Fin 4) (i j : Fin n) :
    karlssonBaseCopyPairCrossing baseCross cluster i j =
      karlssonClusterPairCrossing (cluster i) (cluster j) := by
  unfold karlssonBaseCopyPairCrossing
  by_cases hsame : cluster i = cluster j
  · rw [hsame]
    simp [karlssonClusterPairCrossing]
  · simp [hsame, hbase (cluster i) (cluster j) hsame,
      karlssonBasePairCrossing]

/-- A lower construction certificate with the four-base Karlsson table named
separately from the local blow-up/insertion data.  The still model-specific
fields are exactly:

* the four-base arrangement and its pair table;
* the ordered incremental region certificate for the base;
* for every sorted quadruple, the locally perturbed blow-up arrangement;
* proof that every copy pair inherits either same-cluster value `4` or the
  corresponding four-base pair value;
* ordered insertion-region data for the produced arrangement.
-/
structure KarlssonBaseBlowUpIncrementalLowerData
    (P : TheoremOne.ProblemFamily.{u}) where
  base_arrangement : P.Arrangement 4
  base_pair_cross : Fin 4 → Fin 4 → Rat
  base_pair_cross_eq_karlsson :
    ∀ a b : Fin 4, a ≠ b →
      base_pair_cross a b = karlssonBasePairCrossing a b
  base_region_increment :
    OrderedIncrementalPairRegionData 4
      (P.region 4 base_arrangement) base_pair_cross
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  cluster_witness :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      CardinalityClusteredKarlssonTableWitness q
  pair_cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  pair_cross_eq_base_copy :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        pair_cross n (arrangement n q hq) i j =
          karlssonBaseCopyPairCrossing base_pair_cross
            ((cluster_witness n q hq).cluster) i j
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      OrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

/-- The same four-base/local-blow-up lower certificate, but with the base
table supplied by the six displayed unordered inter-base values plus symmetry.
Lean expands those six fields to the universal base-table agreement. -/
structure KarlssonBaseSixPairBlowUpIncrementalLowerData
    (P : TheoremOne.ProblemFamily.{u}) where
  base_arrangement : P.Arrangement 4
  base_pair_cross : Fin 4 → Fin 4 → Rat
  base_pair_table :
    KarlssonBaseSixPairTableCertificate base_pair_cross
  base_region_increment :
    OrderedIncrementalPairRegionData 4
      (P.region 4 base_arrangement) base_pair_cross
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  cluster_witness :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      CardinalityClusteredKarlssonTableWitness q
  pair_cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  pair_cross_eq_base_copy :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        pair_cross n (arrangement n q hq) i j =
          karlssonBaseCopyPairCrossing base_pair_cross
            ((cluster_witness n q hq).cluster) i j
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      OrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

/-- Four-base/local-blow-up lower data where each produced copy pair carries a
local certificate of its inherited base value. -/
structure KarlssonBaseSixPairLocalBlowUpIncrementalLowerData
    (P : TheoremOne.ProblemFamily.{u}) where
  base_arrangement : P.Arrangement 4
  base_pair_cross : Fin 4 → Fin 4 → Rat
  base_pair_table :
    KarlssonBaseSixPairTableCertificate base_pair_cross
  base_region_increment :
    OrderedIncrementalPairRegionData 4
      (P.region 4 base_arrangement) base_pair_cross
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  cluster_witness :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      CardinalityClusteredKarlssonTableWitness q
  pair_cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  local_pair_cross_eq_base_copy :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        LocalKarlssonBaseCopyPairCrossingData base_pair_cross
          ((cluster_witness n q hq).cluster)
          (pair_cross n (arrangement n q hq)) i j hij
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      OrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

namespace KarlssonBaseSixPairLocalBlowUpIncrementalLowerData

/-- Assemble local copy-pair lower certificates into the existing six-pair
four-base/local-blow-up lower package. -/
noncomputable def toKarlssonBaseSixPairBlowUpIncrementalLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonBaseSixPairLocalBlowUpIncrementalLowerData P) :
    KarlssonBaseSixPairBlowUpIncrementalLowerData P where
  base_arrangement := h.base_arrangement
  base_pair_cross := h.base_pair_cross
  base_pair_table := h.base_pair_table
  base_region_increment := h.base_region_increment
  arrangement := h.arrangement
  cluster_witness := h.cluster_witness
  pair_cross := h.pair_cross
  pair_cross_eq_base_copy := by
    intro n q hq i j hij
    exact pair_cross_eq_base_copy_from_local
      (h.local_pair_cross_eq_base_copy n q hq) i j hij
  region_increment := h.region_increment

/-- Convert directly to the theorem-facing lower construction package. -/
noncomputable def toKarlssonBaseBlowUpIncrementalLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonBaseSixPairLocalBlowUpIncrementalLowerData P) :
    KarlssonBaseBlowUpIncrementalLowerData P where
  base_arrangement := h.base_arrangement
  base_pair_cross := h.base_pair_cross
  base_pair_cross_eq_karlsson :=
    h.base_pair_table.base_pair_cross_eq_karlsson
  base_region_increment := h.base_region_increment
  arrangement := h.arrangement
  cluster_witness := h.cluster_witness
  pair_cross := h.pair_cross
  pair_cross_eq_base_copy := by
    intro n q hq i j hij
    exact pair_cross_eq_base_copy_from_local
      (h.local_pair_cross_eq_base_copy n q hq) i j hij
  region_increment := h.region_increment

end KarlssonBaseSixPairLocalBlowUpIncrementalLowerData

namespace KarlssonBaseSixPairBlowUpIncrementalLowerData

/-- Expand the six-pair base table into the existing theorem-facing lower
certificate. -/
noncomputable def toKarlssonBaseBlowUpIncrementalLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonBaseSixPairBlowUpIncrementalLowerData P) :
    KarlssonBaseBlowUpIncrementalLowerData P where
  base_arrangement := h.base_arrangement
  base_pair_cross := h.base_pair_cross
  base_pair_cross_eq_karlsson :=
    h.base_pair_table.base_pair_cross_eq_karlsson
  base_region_increment := h.base_region_increment
  arrangement := h.arrangement
  cluster_witness := h.cluster_witness
  pair_cross := h.pair_cross
  pair_cross_eq_base_copy := h.pair_cross_eq_base_copy
  region_increment := h.region_increment

end KarlssonBaseSixPairBlowUpIncrementalLowerData

namespace KarlssonBaseBlowUpIncrementalLowerData

/-- The named four-base construction has `45` regions, since its pair table
sums to `40` and the incremental equation adds `4 + 1`. -/
theorem base_region_eq_forty_five
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonBaseBlowUpIncrementalLowerData P) :
    P.region 4 h.base_arrangement = 45 := by
  rw [h.base_region_increment.target_eq_pairSum_add]
  rw [pairSum_four_eq_forty_of_base_pair_crossing_eq
    h.base_pair_cross_eq_karlsson]
  norm_num

/-- A four-base-plus-local-blow-up certificate implies the pairwise lower
interface.  Lean uses the base table agreement to prove every copy-pair value
is the Karlsson cluster value, then the existing pairwise layer performs the
finite summation and derives the lower polynomial. -/
noncomputable def toPairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonBaseBlowUpIncrementalLowerData P) :
    PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerData P where
  arrangement := h.arrangement
  cluster_witness := h.cluster_witness
  pair_cross := h.pair_cross
  pair_cross_eq_cluster := by
    intro n q hq i j hij
    rw [h.pair_cross_eq_base_copy n q hq i j hij]
    exact
      karlssonBaseCopyPairCrossing_eq_clusterPairCrossing
        h.base_pair_cross_eq_karlsson
        ((h.cluster_witness n q hq).cluster) i j
  region_increment := h.region_increment

/-- Forget the four-base/local-blow-up presentation after converting it to the
older named Karlsson incremental lower interface. -/
noncomputable def toKarlssonBlowUpIncrementalLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonBaseBlowUpIncrementalLowerData P) :
    KarlssonBlowUpIncrementalLowerData P :=
  h.toPairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerData
    |>.toKarlssonBlowUpIncrementalLowerData

end KarlssonBaseBlowUpIncrementalLowerData

end ExplicitInputs
end TheoremOneManuscript
end Lollipop

/-!
Proof component 21: `Manuscript.PrimitiveGeometry.CarrierSavings`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Direct finite-carrier savings.

`PairComponentSavings` is useful when a route proof lowers independent caps on
the four components `circle-circle`, `circle-ray`, `ray-circle`, and
`ray-ray`.  Some geometric arguments, especially close-pair radial arguments,
can be inherently coupled across components.  This file records the weaker
direct interface: every finite subset of the whole lifted carrier
intersection has bounded cardinality.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace PrimitiveGeometry

open TheoremOneEndToEnd.PaulsenLinearAlgebra

/-- Direct finite-cardinality savings for the whole lifted carrier
intersection of one lollipop pair. -/
structure PairCarrierSavings
    (L M : EuclideanLollipop) (bound : Nat) where
  carrier_card_le :
    ∀ S : Finset EuclideanR2,
      (∀ p ∈ S, p ∈ euclideanPairIntersectionSet L M) →
        S.card ≤ bound

namespace PairCarrierSavings

/-- Apply a direct carrier-savings certificate to a finite witness. -/
theorem card_le
    {L M : EuclideanLollipop} {bound : Nat}
    (B : PairCarrierSavings L M bound)
    (S : Finset EuclideanR2)
    (hS : ∀ p ∈ S, p ∈ euclideanPairIntersectionSet L M) :
    S.card ≤ bound :=
  B.carrier_card_le S hS

/-- A stronger direct whole-carrier savings bound can be weakened to any
larger bound. -/
def mono
    {L M : EuclideanLollipop} {bound bound' : Nat}
    (B : PairCarrierSavings L M bound)
    (hle : bound ≤ bound') :
    PairCarrierSavings L M bound' where
  carrier_card_le := by
    intro S hS
    exact le_trans (B.card_le S hS) hle

/-- A direct `<= 4` whole-carrier savings certificate can be reused wherever
the upper proof asks only for `<= 5`. -/
def fourToFive
    {L M : EuclideanLollipop}
    (B : PairCarrierSavings L M 4) :
    PairCarrierSavings L M 5 :=
  B.mono (by decide)

/-- Direct whole-carrier savings are symmetric in the two lollipops. -/
def symm
    {L M : EuclideanLollipop} {bound : Nat}
    (B : PairCarrierSavings L M bound) :
    PairCarrierSavings M L bound where
  carrier_card_le := by
    intro S hS
    exact B.card_le S (by
      intro p hp
      have hpML : p ∈ euclideanPairIntersectionSet M L := hS p hp
      rwa [euclideanPairIntersectionSet_symm L M])

end PairCarrierSavings

namespace PairComponentSavings

/-- Independent component caps imply the direct whole-carrier savings
interface. -/
def toPairCarrierSavings
    {L M : EuclideanLollipop} {bound : Nat}
    (B : PairComponentSavings L M bound) :
    PairCarrierSavings L M bound where
  carrier_card_le := finset_card_le_of_pairComponentSavings B

end PairComponentSavings

/-- Generic noncoincidence gives a direct whole-carrier `<= 7` savings
certificate. -/
def pairCarrierSavingsGenericSeven
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M) :
    PairCarrierSavings L M 7 :=
  (pairComponentSavingsGenericSeven hLM hline).toPairCarrierSavings

/-- If the two primitive circles are disjoint, and the ray supporting lines
are not the same line, the existing component-count proof gives the direct
whole-carrier `<= 5` savings interface. -/
def pairCarrierSavingsFiveOfCircleCircleNoMeetData
    {L M : EuclideanLollipop}
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    (D : CircleCircleNoMeetData L M) :
    PairCarrierSavings L M 5 :=
  (pairComponentSavingsFiveOfCircleCircleNoMeet hline D).toPairCarrierSavings

/-- A circle-ray no-meet certificate gives direct whole-carrier `<= 5`
savings under the standard noncoincidence assumptions. -/
def pairCarrierSavingsFiveOfCircleRayNoMeetData
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    (D : CircleRayNoMeetData L M) :
    PairCarrierSavings L M 5 :=
  (pairComponentSavingsFiveOfCircleRayNoMeet hLM hline D).toPairCarrierSavings

/-- A ray-circle no-meet certificate gives direct whole-carrier `<= 5`
savings under the standard noncoincidence assumptions. -/
def pairCarrierSavingsFiveOfRayCircleNoMeetData
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    (D : RayCircleNoMeetData L M) :
    PairCarrierSavings L M 5 :=
  (pairComponentSavingsFiveOfRayCircleNoMeet hLM hline D).toPairCarrierSavings

/-- Simultaneous circle-circle and ray-ray no-meet certificates give the
direct whole-carrier `<= 4` savings interface. -/
def pairCarrierSavingsFourOfCircleCircleNoMeetAndRayRayNoMeetData
    {L M : EuclideanLollipop}
    (Dcc : CircleCircleNoMeetData L M)
    (Drr : RayRayNoMeetData L M) :
    PairCarrierSavings L M 4 :=
  (pairComponentSavingsFourOfCircleCircleNoMeetAndRayRayNoMeet Dcc Drr)
    |>.toPairCarrierSavings

/-- Simultaneous mixed circle-ray and ray-circle no-meet certificates give the
direct whole-carrier `<= 4` savings interface under the standard
noncoincidence assumptions. -/
def pairCarrierSavingsFourOfMixedRayComponentsNoMeetData
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    (Dcr : CircleRayNoMeetData L M)
    (Drc : RayCircleNoMeetData L M) :
    PairCarrierSavings L M 4 :=
  (pairComponentSavingsFourOfMixedRayComponentsNoMeet hLM hline Dcr Drc)
    |>.toPairCarrierSavings

/-- A named five-route supplies a direct whole-carrier `<= 5` savings
certificate. -/
noncomputable def PairComponentSavingsFiveRoute.toPairCarrierSavings
    {L M : EuclideanLollipop}
    (R : PairComponentSavingsFiveRoute L M) :
    PairCarrierSavings L M 5 :=
  R.toPairComponentSavings.toPairCarrierSavings

/-- A named four-route supplies a direct whole-carrier `<= 4` savings
certificate. -/
noncomputable def PairComponentSavingsFourRoute.toPairCarrierSavings
    {L M : EuclideanLollipop}
    (R : PairComponentSavingsFourRoute L M) :
    PairCarrierSavings L M 4 :=
  R.toPairComponentSavings.toPairCarrierSavings

/-- Direct carrier savings imply the matching rational crossing-table bound
from global pairwise carrier-crossing data. -/
theorem pairwiseCarrierCrossingData_cross_le_of_pairCarrierSavings
    {n : Nat} {A : EuclideanLollipopArrangement n}
  {cross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
  (D : PairwiseCarrierCrossingData A cross)
  {bound : Nat}
  (B : PairCarrierSavings (A.lollipop i) (A.lollipop j) bound) :
    cross i j ≤ (bound : Rat) := by
  let S : Finset EuclideanR2 :=
    liftedCrossingFinset (D.crossingPoints i j hij)
  have hS :
      ∀ p ∈ S,
        p ∈ euclideanPairIntersectionSet (A.lollipop i) (A.lollipop j) := by
    intro p hp
    rcases Finset.mem_image.1 hp with ⟨x, hx, rfl⟩
    exact
      by
        have hx_pair : x ∈ A.pairIntersectionSet i j := by
          have hset := D.crossingPoints_spec i j hij
          have hx_finset :
              x ∈ ((D.crossingPoints i j hij : Finset R2) : Set R2) := by
            simpa using hx
          simpa [hset] using hx_finset
        have hx_pair' :
            x ∈ pairIntersectionSet (A.lollipop i) (A.lollipop j) := by
          simpa [EuclideanLollipopArrangement.pairIntersectionSet] using
            hx_pair
        have hpre :=
          pairIntersectionSet_eq_preimage_euclideanPairIntersectionSet
            (A.lollipop i) (A.lollipop j)
        have hx_preimage :
            x ∈ {x : R2 |
              toEuclideanR2 x ∈
                euclideanPairIntersectionSet (A.lollipop i)
                  (A.lollipop j)} := by
          simpa [hpre] using hx_pair'
        simpa using hx_preimage
  have hcard_lifted : S.card ≤ bound := B.card_le S hS
  have hcard :
      (D.crossingPoints i j hij).card ≤ bound := by
    simpa [S] using hcard_lifted
  rw [D.cross_eq_card i j hij]
  exact_mod_cast hcard

/-- Direct carrier savings imply the matching rational crossing-table bound
from one local carrier-crossing witness. -/
theorem localPairCarrierCrossingData_cross_le_of_pairCarrierSavings
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
  (D : LocalPairCarrierCrossingData A cross i j hij)
  {bound : Nat}
  (B : PairCarrierSavings (A.lollipop i) (A.lollipop j) bound) :
    cross i j ≤ (bound : Rat) := by
  let S : Finset EuclideanR2 :=
    liftedCrossingFinset D.crossingPoints
  have hS :
      ∀ p ∈ S,
        p ∈ euclideanPairIntersectionSet (A.lollipop i) (A.lollipop j) := by
    intro p hp
    rcases Finset.mem_image.1 hp with ⟨x, hx, rfl⟩
    exact
      by
        have hx_pair : x ∈ A.pairIntersectionSet i j := by
          have hset := D.crossingPoints_spec
          have hx_finset :
              x ∈ ((D.crossingPoints : Finset R2) : Set R2) := by
            simpa using hx
          simpa [hset] using hx_finset
        have hx_pair' :
            x ∈ pairIntersectionSet (A.lollipop i) (A.lollipop j) := by
          simpa [EuclideanLollipopArrangement.pairIntersectionSet] using
            hx_pair
        have hpre :=
          pairIntersectionSet_eq_preimage_euclideanPairIntersectionSet
            (A.lollipop i) (A.lollipop j)
        have hx_preimage :
            x ∈ {x : R2 |
              toEuclideanR2 x ∈
                euclideanPairIntersectionSet (A.lollipop i)
                  (A.lollipop j)} := by
          simpa [hpre] using hx_pair'
        simpa using hx_preimage
  have hcard_lifted : S.card ≤ bound := B.card_le S hS
  have hcard : D.crossingPoints.card ≤ bound := by
    simpa [S] using hcard_lifted
  rw [D.cross_eq_card]
  exact_mod_cast hcard

/-- Primitive carrier upper data where close/intriguing savings are supplied
as direct whole-carrier finite-cardinality bounds.  This package is intended
for coupled component-count proofs that cannot naturally be expressed as four
independent component caps. -/
structure PrimitiveCarrierDirectSavingsUpperGeometryData
    (P : TheoremOne.ProblemFamily.{u}) where
  arrangement :
    ∀ n : Nat, P.Arrangement n → EuclideanLollipopArrangement n
  cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  pairwise_crossings :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      PairwiseCarrierCrossingData (arrangement n A) (cross n A)
  spheres_distinct :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      euclideanSphere ((arrangement n A).lollipop i).center
          ((arrangement n A).lollipop i).radius ≠
        euclideanSphere ((arrangement n A).lollipop j).center
          ((arrangement n A).lollipop j).radius
  rayLines_distinct :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      euclideanRayLine ((arrangement n A).lollipop i) ≠
        euclideanRayLine ((arrangement n A).lollipop j)
  close_savings :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => (arrangement n A).normalizedDirection k) i j →
        PairCarrierSavings ((arrangement n A).lollipop i)
          ((arrangement n A).lollipop j) 5
  intriguing_savings :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      circleIntriguing
        (fun k => (arrangement n A).center k)
        (fun k => (arrangement n A).radius k) i j →
        PairCarrierSavings ((arrangement n A).lollipop i)
          ((arrangement n A).lollipop j) 5
  close_intriguing_savings :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => (arrangement n A).normalizedDirection k) i j →
      circleIntriguing
        (fun k => (arrangement n A).center k)
        (fun k => (arrangement n A).radius k) i j →
        PairCarrierSavings ((arrangement n A).lollipop i)
          ((arrangement n A).lollipop j) 4
  region_increment :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      OrderedIncrementalPairRegionData n (P.region n A) (cross n A)

namespace PrimitiveCarrierDirectSavingsUpperGeometryData

/-- Direct whole-carrier savings imply the existing carrier-certified exact
upper interface.  The generic branch still comes from the component-count
`<= 7` theorem under noncoincident spheres and ray-supporting lines. -/
noncomputable def toPrimitiveCarrierCertifiedExactUpperGeometryData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveCarrierDirectSavingsUpperGeometryData P) :
    PrimitiveCarrierCertifiedExactUpperGeometryData P where
  arrangement := h.arrangement
  cross := h.cross
  pairwise_crossings := h.pairwise_crossings
  cross_le_case := by
    intro n A i j hij
    by_cases hc :
        TheoremOneEndToEnd.CloseDirection.cyclicClose
          (fun k => (h.arrangement n A).normalizedDirection k) i j
    · by_cases hi :
          circleIntriguing
            (fun k => (h.arrangement n A).center k)
            (fun k => (h.arrangement n A).radius k) i j
      · have h4 :=
          pairwiseCarrierCrossingData_cross_le_of_pairCarrierSavings
            (h.pairwise_crossings n A) (hij := hij)
            (h.close_intriguing_savings n A i j hij hc hi)
        simpa [TheoremOneEndToEnd.canonicalCrossingCaseBound, hc, hi] using h4
      · have h5 :=
          pairwiseCarrierCrossingData_cross_le_of_pairCarrierSavings
            (h.pairwise_crossings n A) (hij := hij)
            (h.close_savings n A i j hij hc)
        simpa [TheoremOneEndToEnd.canonicalCrossingCaseBound, hc, hi] using h5
    · by_cases hi :
          circleIntriguing
            (fun k => (h.arrangement n A).center k)
            (fun k => (h.arrangement n A).radius k) i j
      · have h5 :=
          pairwiseCarrierCrossingData_cross_le_of_pairCarrierSavings
            (h.pairwise_crossings n A) (hij := hij)
            (h.intriguing_savings n A i j hij hi)
        simpa [TheoremOneEndToEnd.canonicalCrossingCaseBound, hc, hi] using h5
      · have h7 :=
          pairwiseCarrierCrossingData_cross_le_seven
            (h.pairwise_crossings n A) hij
            (h.spheres_distinct n A i j hij)
            (h.rayLines_distinct n A i j hij)
        simpa [TheoremOneEndToEnd.canonicalCrossingCaseBound, hc, hi] using h7
  region_increment := h.region_increment

end PrimitiveCarrierDirectSavingsUpperGeometryData

namespace PrimitiveCarrierComponentSavingsUpperGeometryData

/-- Component-wise savings are a special case of direct whole-carrier savings. -/
noncomputable def toDirectSavingsUpperGeometryData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveCarrierComponentSavingsUpperGeometryData P) :
    PrimitiveCarrierDirectSavingsUpperGeometryData P where
  arrangement := h.arrangement
  cross := h.cross
  pairwise_crossings := h.pairwise_crossings
  spheres_distinct := h.spheres_distinct
  rayLines_distinct := h.rayLines_distinct
  close_savings := by
    intro n A i j hij hclose
    exact (h.close_savings n A i j hij hclose).toPairCarrierSavings
  intriguing_savings := by
    intro n A i j hij hintriguing
    exact (h.intriguing_savings n A i j hij hintriguing).toPairCarrierSavings
  close_intriguing_savings := by
    intro n A i j hij hclose hintriguing
    exact
      (h.close_intriguing_savings n A i j hij hclose
        hintriguing).toPairCarrierSavings
  region_increment := h.region_increment

end PrimitiveCarrierComponentSavingsUpperGeometryData

/-- Radial version of direct whole-carrier savings upper data. -/
structure PrimitiveRadialCarrierDirectSavingsUpperGeometryData
    (P : TheoremOne.ProblemFamily.{u})
    extends PrimitiveCarrierDirectSavingsUpperGeometryData P where
  radial_outward :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i : Fin n,
      ((arrangement n A).lollipop i).IsRadialOutward

namespace PrimitiveRadialCarrierDirectSavingsUpperGeometryData

/-- Forget the radial-outward field after it has been recorded. -/
noncomputable def toDirectSavingsUpperGeometryData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveRadialCarrierDirectSavingsUpperGeometryData P) :
    PrimitiveCarrierDirectSavingsUpperGeometryData P :=
  h.toPrimitiveCarrierDirectSavingsUpperGeometryData

end PrimitiveRadialCarrierDirectSavingsUpperGeometryData

end PrimitiveGeometry
end TheoremOneManuscript
end Lollipop

/-!
Proof component 22: `Manuscript.Formalization.FromComponentBounds`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Theorem 1 from primitive carrier component bounds.

This theorem-facing file is one step closer to the manuscript's geometric
Lemma 2 than `FromSubtheorems`: the baseline `≤ 7` pair-crossing
case is not assumed as a table entry.  It is proved from finite
carrier-intersection witnesses plus the generic noncoincidence of the two
circles and two ray-supporting lines.  The strongest endpoint in this file
also makes the close/intriguing `≤ 5/4` savings component-wise finite
cardinality obligations rather than final numeric crossing inequalities.
-/

namespace Lollipop
namespace TheoremOneManuscript

universe u

/-- Component-bound primitive carrier subtheorems for Theorem 1: the upper
side derives the generic `≤ 7` crossing case from carrier components, and the
lower side is the named incremental Karlsson blow-up construction. -/
structure ComponentBoundPrimitiveCarrierTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) where
  upper_geometry :
    PrimitiveGeometry.PrimitiveCarrierComponentBoundUpperGeometryData
      P.toProblemFamily
  lower_karlsson :
    ExplicitInputs.KarlssonBlowUpIncrementalLowerData P.toProblemFamily

namespace ComponentBoundPrimitiveCarrierTheoremOneSubtheorems

/-- Forget the proof of the generic `≤ 7` case after converting it to the
existing primitive carrier-certified theorem-one package. -/
noncomputable def toPrimitiveCarrierTheoremOneSubtheorems
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : ComponentBoundPrimitiveCarrierTheoremOneSubtheorems P) :
    PrimitiveCarrierTheoremOneSubtheorems P where
  upper_geometry :=
    h.upper_geometry.toPrimitiveCarrierCertifiedExactUpperGeometryData
  lower_karlsson := h.lower_karlsson

end ComponentBoundPrimitiveCarrierTheoremOneSubtheorems

/-- Theorem 1 from primitive carrier component bounds and named Karlsson
blow-up data. -/
theorem theorem_one_from_component_bound_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ComponentBoundPrimitiveCarrierTheoremOneSubtheorems P) :
    TheoremOneStatement P := by
  exact theorem_one_from_primitive_carrier_subtheorems P
    h.toPrimitiveCarrierTheoremOneSubtheorems

/-- Single-size Theorem 1 formula from primitive carrier component bounds and
named Karlsson blow-up data. -/
theorem theorem_one_at_from_component_bound_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ComponentBoundPrimitiveCarrierTheoremOneSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_component_bound_primitive_carrier_subtheorems P h n

/-- Component-savings primitive carrier subtheorems for Theorem 1: the upper
side derives the generic `≤ 7` case and derives the close/intriguing `≤ 5/4`
cases from component-wise finite-cardinality savings. -/
structure ComponentSavingsPrimitiveCarrierTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) where
  upper_geometry :
    PrimitiveGeometry.PrimitiveCarrierComponentSavingsUpperGeometryData
      P.toProblemFamily
  lower_karlsson :
    ExplicitInputs.KarlssonBlowUpIncrementalLowerData P.toProblemFamily

namespace ComponentSavingsPrimitiveCarrierTheoremOneSubtheorems

/-- Forget the component-wise proof details after converting them to the
existing primitive carrier-certified theorem-one package. -/
noncomputable def toPrimitiveCarrierTheoremOneSubtheorems
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : ComponentSavingsPrimitiveCarrierTheoremOneSubtheorems P) :
    PrimitiveCarrierTheoremOneSubtheorems P where
  upper_geometry :=
    h.upper_geometry.toPrimitiveCarrierCertifiedExactUpperGeometryData
  lower_karlsson := h.lower_karlsson

end ComponentSavingsPrimitiveCarrierTheoremOneSubtheorems

/-- Theorem 1 from primitive carrier component savings and named Karlsson
blow-up data. -/
theorem theorem_one_from_component_savings_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ComponentSavingsPrimitiveCarrierTheoremOneSubtheorems P) :
    TheoremOneStatement P := by
  exact theorem_one_from_primitive_carrier_subtheorems P
    h.toPrimitiveCarrierTheoremOneSubtheorems

/-- Single-size Theorem 1 formula from primitive carrier component savings
and named Karlsson blow-up data. -/
theorem theorem_one_at_from_component_savings_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ComponentSavingsPrimitiveCarrierTheoremOneSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_component_savings_primitive_carrier_subtheorems P h n

/-- Direct-savings primitive carrier subtheorems for Theorem 1: the upper
side derives the generic `≤ 7` case and derives the close/intriguing `≤ 5/4`
cases from whole-carrier finite-cardinality savings. -/
structure DirectSavingsPrimitiveCarrierTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) where
  upper_geometry :
    PrimitiveGeometry.PrimitiveCarrierDirectSavingsUpperGeometryData
      P.toProblemFamily
  lower_karlsson :
    ExplicitInputs.KarlssonBlowUpIncrementalLowerData P.toProblemFamily

namespace DirectSavingsPrimitiveCarrierTheoremOneSubtheorems

/-- Forget direct whole-carrier proof details after converting them to the
existing primitive carrier-certified theorem-one package. -/
noncomputable def toPrimitiveCarrierTheoremOneSubtheorems
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : DirectSavingsPrimitiveCarrierTheoremOneSubtheorems P) :
    PrimitiveCarrierTheoremOneSubtheorems P where
  upper_geometry :=
    h.upper_geometry.toPrimitiveCarrierCertifiedExactUpperGeometryData
  lower_karlsson := h.lower_karlsson

end DirectSavingsPrimitiveCarrierTheoremOneSubtheorems

/-- Theorem 1 from primitive carrier direct savings and named Karlsson
blow-up data. -/
theorem theorem_one_from_direct_savings_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : DirectSavingsPrimitiveCarrierTheoremOneSubtheorems P) :
    TheoremOneStatement P := by
  exact theorem_one_from_primitive_carrier_subtheorems P
    h.toPrimitiveCarrierTheoremOneSubtheorems

/-- Single-size formula from primitive carrier direct savings and named
Karlsson blow-up data. -/
theorem theorem_one_at_from_direct_savings_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : DirectSavingsPrimitiveCarrierTheoremOneSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_from_direct_savings_primitive_carrier_subtheorems P h n

/-- Stronger lower-bound endpoint: the lower construction supplies pairwise
crossing values and ordered insertion-region data.  Lean sums those pairwise
values to the Karlsson lower polynomial before invoking the theorem stack. -/
structure ComponentSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) where
  upper_geometry :
    PrimitiveGeometry.PrimitiveCarrierComponentSavingsUpperGeometryData
      P.toProblemFamily
  lower_pairwise :
    ExplicitInputs.PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerData
      P.toProblemFamily

namespace ComponentSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems

/-- Convert the pairwise lower package to the older component-savings theorem
package after Lean has derived the aggregate Karlsson lower data. -/
noncomputable def toComponentSavingsPrimitiveCarrierTheoremOneSubtheorems
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : ComponentSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems P) :
    ComponentSavingsPrimitiveCarrierTheoremOneSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson := h.lower_pairwise.toKarlssonBlowUpIncrementalLowerData

end ComponentSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems

/-- Theorem 1 from primitive carrier component savings and pairwise Karlsson
lower construction data. -/
theorem theorem_one_from_component_savings_pairwise_lower_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ComponentSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems P) :
    TheoremOneStatement P := by
  exact theorem_one_from_component_savings_primitive_carrier_subtheorems P
    h.toComponentSavingsPrimitiveCarrierTheoremOneSubtheorems

/-- Single-size formula from primitive carrier component savings and pairwise
Karlsson lower construction data. -/
theorem theorem_one_at_from_component_savings_pairwise_lower_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ComponentSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact
    theorem_one_from_component_savings_pairwise_lower_primitive_carrier_subtheorems
      P h n

/-- Direct-savings endpoint with pairwise Karlsson lower construction data. -/
structure DirectSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) where
  upper_geometry :
    PrimitiveGeometry.PrimitiveCarrierDirectSavingsUpperGeometryData
      P.toProblemFamily
  lower_pairwise :
    ExplicitInputs.PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerData
      P.toProblemFamily

namespace DirectSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems

/-- Convert the pairwise lower package to the older direct-savings theorem
package after Lean has derived the aggregate Karlsson lower data. -/
noncomputable def toDirectSavingsPrimitiveCarrierTheoremOneSubtheorems
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : DirectSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems P) :
    DirectSavingsPrimitiveCarrierTheoremOneSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson := h.lower_pairwise.toKarlssonBlowUpIncrementalLowerData

end DirectSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems

/-- Theorem 1 from primitive carrier direct savings and pairwise Karlsson
lower construction data. -/
theorem theorem_one_from_direct_savings_pairwise_lower_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : DirectSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems P) :
    TheoremOneStatement P := by
  exact theorem_one_from_direct_savings_primitive_carrier_subtheorems P
    h.toDirectSavingsPrimitiveCarrierTheoremOneSubtheorems

/-- Single-size formula from primitive carrier direct savings and pairwise
Karlsson lower construction data. -/
theorem theorem_one_at_from_direct_savings_pairwise_lower_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : DirectSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact
    theorem_one_from_direct_savings_pairwise_lower_primitive_carrier_subtheorems
      P h n

/-- Monotone lower-bound endpoint: the upper side is component-savings
primitive carrier geometry, while the lower construction only proves each
copy pair has at least the corresponding Karlsson cluster-table value. -/
structure ComponentSavingsMonotonePairwiseLowerPrimitiveCarrierTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) where
  upper_geometry :
    PrimitiveGeometry.PrimitiveCarrierComponentSavingsUpperGeometryData
      P.toProblemFamily
  lower_pairwise_bound :
    ExplicitInputs.PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData
      P.toProblemFamily

namespace ComponentSavingsMonotonePairwiseLowerPrimitiveCarrierTheoremOneSubtheorems

/-- Convert component-savings upper data plus monotone pairwise lower data to
the statement-layer monotone theorem package. -/
noncomputable def toMaxCanonicalExactCoordinateGeometricCrossingModelBoundSubtheorems
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h :
      ComponentSavingsMonotonePairwiseLowerPrimitiveCarrierTheoremOneSubtheorems
        P) :
    MaxCanonicalExactCoordinateGeometricCrossingModelBoundSubtheorems P where
  upper_certificates :=
    h.upper_geometry
      |>.toPrimitiveCarrierCertifiedExactUpperGeometryData
      |>.toCanonicalExactUpperGeometryIncrementalData
      |>.toUpperCertificates
  lower_sorted_crossing_bound_realizations :=
    ⟨h.lower_pairwise_bound.crossings,
      h.lower_pairwise_bound.toSortedLowerCrossingBoundRealizations⟩

end ComponentSavingsMonotonePairwiseLowerPrimitiveCarrierTheoremOneSubtheorems

/-- Theorem 1 from component-savings primitive carrier upper data and
monotone pairwise Karlsson lower data. -/
theorem theorem_one_from_component_savings_monotone_pairwise_lower_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ComponentSavingsMonotonePairwiseLowerPrimitiveCarrierTheoremOneSubtheorems
      P) :
    TheoremOneStatement P := by
  exact
    theorem_one_formula_statement_proven_from_manuscript_canonical_exact_coordinate_geometric_crossing_bound_certificates
      P h.toMaxCanonicalExactCoordinateGeometricCrossingModelBoundSubtheorems

/-- Single-size formula from component-savings primitive carrier upper data
and monotone pairwise Karlsson lower data. -/
theorem theorem_one_at_from_component_savings_monotone_pairwise_lower_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ComponentSavingsMonotonePairwiseLowerPrimitiveCarrierTheoremOneSubtheorems
      P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact
    theorem_one_from_component_savings_monotone_pairwise_lower_primitive_carrier_subtheorems
      P h n

/-- Direct-savings version of the monotone pairwise lower endpoint. -/
structure DirectSavingsMonotonePairwiseLowerPrimitiveCarrierTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) where
  upper_geometry :
    PrimitiveGeometry.PrimitiveCarrierDirectSavingsUpperGeometryData
      P.toProblemFamily
  lower_pairwise_bound :
    ExplicitInputs.PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData
      P.toProblemFamily

namespace DirectSavingsMonotonePairwiseLowerPrimitiveCarrierTheoremOneSubtheorems

/-- Convert direct whole-carrier upper data plus monotone pairwise lower data
to the statement-layer monotone theorem package. -/
noncomputable def toMaxCanonicalExactCoordinateGeometricCrossingModelBoundSubtheorems
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h :
      DirectSavingsMonotonePairwiseLowerPrimitiveCarrierTheoremOneSubtheorems
        P) :
    MaxCanonicalExactCoordinateGeometricCrossingModelBoundSubtheorems P where
  upper_certificates :=
    h.upper_geometry
      |>.toPrimitiveCarrierCertifiedExactUpperGeometryData
      |>.toCanonicalExactUpperGeometryIncrementalData
      |>.toUpperCertificates
  lower_sorted_crossing_bound_realizations :=
    ⟨h.lower_pairwise_bound.crossings,
      h.lower_pairwise_bound.toSortedLowerCrossingBoundRealizations⟩

end DirectSavingsMonotonePairwiseLowerPrimitiveCarrierTheoremOneSubtheorems

/-- Theorem 1 from direct whole-carrier primitive upper data and monotone
pairwise Karlsson lower data. -/
theorem theorem_one_from_direct_savings_monotone_pairwise_lower_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h :
      DirectSavingsMonotonePairwiseLowerPrimitiveCarrierTheoremOneSubtheorems
        P) :
    TheoremOneStatement P := by
  exact
    theorem_one_formula_statement_proven_from_manuscript_canonical_exact_coordinate_geometric_crossing_bound_certificates
      P h.toMaxCanonicalExactCoordinateGeometricCrossingModelBoundSubtheorems

/-- Single-size formula from direct whole-carrier primitive upper data and
monotone pairwise Karlsson lower data. -/
theorem theorem_one_at_from_direct_savings_monotone_pairwise_lower_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h :
      DirectSavingsMonotonePairwiseLowerPrimitiveCarrierTheoremOneSubtheorems
        P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact
    theorem_one_from_direct_savings_monotone_pairwise_lower_primitive_carrier_subtheorems
      P h n

/-- Strongest lower-bound endpoint in this file: the lower construction names
Karlsson's four-base table and supplies local blow-up/insertion certificates.
Lean converts that data to the pairwise lower interface, then sums the
pairwise table to the lower polynomial. -/
structure ComponentSavingsKarlssonBaseLowerPrimitiveCarrierTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) where
  upper_geometry :
    PrimitiveGeometry.PrimitiveCarrierComponentSavingsUpperGeometryData
      P.toProblemFamily
  lower_karlsson_base :
    ExplicitInputs.KarlssonBaseBlowUpIncrementalLowerData P.toProblemFamily

namespace ComponentSavingsKarlssonBaseLowerPrimitiveCarrierTheoremOneSubtheorems

/-- Convert the four-base/local-blow-up lower package to the pairwise lower
theorem package. -/
noncomputable def toComponentSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : ComponentSavingsKarlssonBaseLowerPrimitiveCarrierTheoremOneSubtheorems P) :
    ComponentSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_pairwise :=
    h.lower_karlsson_base
      |>.toPairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerData

end ComponentSavingsKarlssonBaseLowerPrimitiveCarrierTheoremOneSubtheorems

/-- Theorem 1 from primitive carrier component savings plus Karlsson
four-base/local-blow-up lower construction data. -/
theorem theorem_one_from_component_savings_karlsson_base_lower_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ComponentSavingsKarlssonBaseLowerPrimitiveCarrierTheoremOneSubtheorems P) :
    TheoremOneStatement P := by
  exact theorem_one_from_component_savings_pairwise_lower_primitive_carrier_subtheorems
    P h.toComponentSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems

/-- Single-size formula from primitive carrier component savings plus
Karlsson four-base/local-blow-up lower construction data. -/
theorem theorem_one_at_from_component_savings_karlsson_base_lower_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ComponentSavingsKarlssonBaseLowerPrimitiveCarrierTheoremOneSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact
    theorem_one_from_component_savings_karlsson_base_lower_primitive_carrier_subtheorems
      P h n

/-- Direct-savings endpoint with Karlsson four-base/local-blow-up lower
construction data. -/
structure DirectSavingsKarlssonBaseLowerPrimitiveCarrierTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) where
  upper_geometry :
    PrimitiveGeometry.PrimitiveCarrierDirectSavingsUpperGeometryData
      P.toProblemFamily
  lower_karlsson_base :
    ExplicitInputs.KarlssonBaseBlowUpIncrementalLowerData P.toProblemFamily

namespace DirectSavingsKarlssonBaseLowerPrimitiveCarrierTheoremOneSubtheorems

/-- Convert the four-base/local-blow-up lower package to the pairwise lower
direct-savings theorem package. -/
noncomputable def toDirectSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : DirectSavingsKarlssonBaseLowerPrimitiveCarrierTheoremOneSubtheorems P) :
    DirectSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_pairwise :=
    h.lower_karlsson_base
      |>.toPairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerData

end DirectSavingsKarlssonBaseLowerPrimitiveCarrierTheoremOneSubtheorems

/-- Theorem 1 from primitive carrier direct savings plus Karlsson
four-base/local-blow-up lower construction data. -/
theorem theorem_one_from_direct_savings_karlsson_base_lower_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : DirectSavingsKarlssonBaseLowerPrimitiveCarrierTheoremOneSubtheorems P) :
    TheoremOneStatement P := by
  exact theorem_one_from_direct_savings_pairwise_lower_primitive_carrier_subtheorems
    P h.toDirectSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems

/-- Single-size formula from primitive carrier direct savings plus Karlsson
four-base/local-blow-up lower construction data. -/
theorem theorem_one_at_from_direct_savings_karlsson_base_lower_primitive_carrier_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : DirectSavingsKarlssonBaseLowerPrimitiveCarrierTheoremOneSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact
    theorem_one_from_direct_savings_karlsson_base_lower_primitive_carrier_subtheorems
      P h n

end TheoremOneManuscript
end Lollipop

/-!
Proof component 23: `Manuscript.FormalizedProof.Statements`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Manuscript-shaped statement layer for Theorem 1.

This folder is intentionally separate from the existing development.  It
presents the final theorem target and the strongest currently formalized
subtheorem package in the order used by the manuscript, while reusing the
proved modules underneath.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace FormalizedProof

universe u

/-- The displayed Theorem 1 statement in the paper's `S(n)` notation. -/
abbrev FinalTheoremOneStatement
    (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  TheoremOneStatement P

/-- The single-size displayed formula from Theorem 1. -/
abbrev FinalTheoremOneAtStatement
    (P : TheoremOne.MaxProblemFamily.{u}) (n : Nat) : Prop :=
  P.aLop n =
    4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1

/-- Unfolded form of the final theorem statement. -/
theorem finalTheoremOneStatement_iff
    (P : TheoremOne.MaxProblemFamily.{u}) :
    FinalTheoremOneStatement P ↔
      ∀ n : Nat, FinalTheoremOneAtStatement P n := by
  rfl

/-- The strongest currently exposed manuscript subtheorem package: primitive
carrier geometry with the generic `<= 7` case proved from component counts,
close/intriguing cases reduced to component-wise savings, and named
incremental Karlsson lower data. -/
abbrev StrongestKnownTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ComponentSavingsPrimitiveCarrierTheoremOneSubtheorems P

/-- Direct whole-carrier savings package: primitive carrier geometry with the
generic `<= 7` case proved from component counts, close/intriguing cases
reduced to finite-cardinality bounds on the whole carrier intersection, and
named incremental Karlsson lower data.  This is the preferred upper boundary
for coupled close-pair arguments. -/
abbrev DirectSavingsTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  DirectSavingsPrimitiveCarrierTheoremOneSubtheorems P

/-- Stronger lower-bound-facing package: the upper bound is still the
component-savings primitive carrier package, while the lower construction is
specified pairwise.  The aggregate Karlsson lower polynomial is then derived
inside Lean by summing the certified pair contributions. -/
abbrev PairwiseLowerTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ComponentSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems P

/-- Direct-savings version with pairwise Karlsson lower data. -/
abbrev DirectSavingsPairwiseLowerTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  DirectSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems P

/-- Monotone pairwise lower package: lower copy-pair data are inequalities
`cluster value <= actual pair value`, which is enough for the lower-bound
half of Theorem 1. -/
abbrev MonotonePairwiseLowerTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ComponentSavingsMonotonePairwiseLowerPrimitiveCarrierTheoremOneSubtheorems P

/-- Direct-savings version with monotone pairwise Karlsson lower data. -/
abbrev DirectSavingsMonotonePairwiseLowerTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  DirectSavingsMonotonePairwiseLowerPrimitiveCarrierTheoremOneSubtheorems P

/-- Lower-bound-facing package closest to Karlsson's manuscript construction:
the lower side names the four-base table and supplies local blow-up/insertion
certificates before Lean converts it to the pairwise lower interface. -/
abbrev KarlssonBaseLowerTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ComponentSavingsKarlssonBaseLowerPrimitiveCarrierTheoremOneSubtheorems P

/-- Direct-savings version closest to Karlsson's manuscript lower
construction: whole-carrier close/intriguing savings on the upper side and
four-base/local-blow-up data on the lower side. -/
abbrev DirectSavingsKarlssonBaseLowerTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  DirectSavingsKarlssonBaseLowerPrimitiveCarrierTheoremOneSubtheorems P

/-- A weaker but useful package where the close/intriguing savings have
already been converted to final numeric pair-crossing inequalities. -/
abbrev ComponentBoundTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ComponentBoundPrimitiveCarrierTheoremOneSubtheorems P

end FormalizedProof
end TheoremOneManuscript
end Lollipop

/-!
Proof component 24: `Manuscript.ExplicitInputs.KarlssonOEIS`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
The OEIS/Karlsson four-lollipop coordinate base.

This file records the coordinate data from the OEIS note:

* `Q0 = Qoppa.from_anchor(0, 0, 200, 0)`;
* `Q1 = Qoppa.from_center(0.45, 0.4, 0.55, -0.01)`;
* `Q2 = Qoppa.from_anchor(1.15, 0.65, 100, -(pi/2 + pi/7.5))`;
* `Q3 = Qoppa.from_anchor(1.0488116827495215, -0.05, 100,
    pi/2 + pi/30)`.

The file does not assert the difficult intersection calculation for free:
`KarlssonOEISBaseCoordinateCrossingCertificate` is the finite
carrier-intersection certificate type for these exact four coordinate
lollipops.  The complete formalization folder constructs this certificate
from six local pair certificates.  This file proves the finite
region-insertion arithmetic for the certified `5,7,7,7,7,7` base table.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace ExplicitInputs

open PrimitiveGeometry
open TheoremOneEndToEnd.PaulsenLinearAlgebra

/-- Normalized direction for the OEIS `-0.01` bearing. -/
noncomputable def normalizedMinusPoint01 : ℝ :=
  1 - (1 / 100 : ℝ) / (2 * Real.pi)

theorem normalizedMinusPoint01_nonneg :
    0 ≤ normalizedMinusPoint01 := by
  unfold normalizedMinusPoint01
  have hden : 0 < 2 * Real.pi := by positivity
  have hfrac : (1 / 100 : ℝ) / (2 * Real.pi) ≤ 1 := by
    rw [div_le_iff₀ hden]
    nlinarith [Real.pi_gt_three]
  linarith

theorem normalizedMinusPoint01_lt_one :
    normalizedMinusPoint01 < 1 := by
  unfold normalizedMinusPoint01
  have hfrac : 0 < (1 / 100 : ℝ) / (2 * Real.pi) := by positivity
  linarith

/-- `Q0` from the OEIS/Karlsson coordinate note. -/
noncomputable def karlssonOEISQ0 : EuclideanLollipop :=
  EuclideanLollipop.fromAnchor
    (point2 0 0) 200 0 0
    (by norm_num) (by norm_num) (by norm_num)

theorem karlssonOEISQ0_isRadialOutward :
    karlssonOEISQ0.IsRadialOutward := by
  simpa [karlssonOEISQ0] using
    EuclideanLollipop.fromAnchor_isRadialOutward
      (point2 0 0) 200 0 0
      (by norm_num) (by norm_num) (by norm_num)

/-- The recorded normalized direction of `Q0` agrees with its ray vector. -/
theorem karlssonOEISQ0_hasNormalizedBearing :
    karlssonOEISQ0.HasNormalizedBearing := by
  unfold karlssonOEISQ0
  exact EuclideanLollipop.fromAnchor_hasNormalizedBearing (by ring)

/-- `Q1` from the OEIS/Karlsson coordinate note. -/
noncomputable def karlssonOEISQ1 : EuclideanLollipop :=
  EuclideanLollipop.fromCenter
    (point2 (45 / 100) (4 / 10)) (55 / 100) (-(1 / 100))
    normalizedMinusPoint01
    (by norm_num) normalizedMinusPoint01_nonneg
    normalizedMinusPoint01_lt_one

theorem karlssonOEISQ1_isRadialOutward :
    karlssonOEISQ1.IsRadialOutward := by
  simpa [karlssonOEISQ1] using
    EuclideanLollipop.fromCenter_isRadialOutward
      (point2 (45 / 100) (4 / 10)) (55 / 100) (-(1 / 100))
      normalizedMinusPoint01
      (by norm_num) normalizedMinusPoint01_nonneg
      normalizedMinusPoint01_lt_one

/-- The recorded normalized direction of `Q1` agrees with its ray vector. -/
theorem karlssonOEISQ1_hasNormalizedBearing :
    karlssonOEISQ1.HasNormalizedBearing := by
  unfold karlssonOEISQ1
  exact EuclideanLollipop.fromCenter_hasNormalizedBearing_of_eq_sub_two_pi
    (by
      unfold normalizedMinusPoint01
      have hden : (2 * Real.pi : ℝ) ≠ 0 := by positivity
      field_simp [hden]
      ring)

/-- The OEIS angle `-(pi/2 + pi/7.5)`, written without decimal division. -/
noncomputable def karlssonOEISQ2Theta : ℝ :=
  -(Real.pi / 2 + 2 * Real.pi / 15)

/-- `Q2` from the OEIS/Karlsson coordinate note. -/
noncomputable def karlssonOEISQ2 : EuclideanLollipop :=
  EuclideanLollipop.fromAnchor
    (point2 (115 / 100) (65 / 100)) 100 karlssonOEISQ2Theta
    (41 / 60)
    (by norm_num) (by norm_num) (by norm_num)

theorem karlssonOEISQ2_isRadialOutward :
    karlssonOEISQ2.IsRadialOutward := by
  simpa [karlssonOEISQ2] using
    EuclideanLollipop.fromAnchor_isRadialOutward
      (point2 (115 / 100) (65 / 100)) 100 karlssonOEISQ2Theta
      (41 / 60)
      (by norm_num) (by norm_num) (by norm_num)

/-- The recorded normalized direction of `Q2` agrees with its ray vector. -/
theorem karlssonOEISQ2_hasNormalizedBearing :
    karlssonOEISQ2.HasNormalizedBearing := by
  unfold karlssonOEISQ2
  exact EuclideanLollipop.fromAnchor_hasNormalizedBearing_of_eq_sub_two_pi
    (by
      unfold karlssonOEISQ2Theta
      ring)

/-- The OEIS angle `pi/2 + pi/30`. -/
noncomputable def karlssonOEISQ3Theta : ℝ :=
  Real.pi / 2 + Real.pi / 30

/-- The decimal `1.0488116827495215` from the OEIS coordinate note, recorded
as an exact rational. -/
noncomputable def karlssonOEISQ3AnchorX : ℝ :=
  (10488116827495215 : ℝ) / 10000000000000000

/-- `Q3` from the OEIS/Karlsson coordinate note. -/
noncomputable def karlssonOEISQ3 : EuclideanLollipop :=
  EuclideanLollipop.fromAnchor
    (point2 karlssonOEISQ3AnchorX (-(5 / 100))) 100
    karlssonOEISQ3Theta (4 / 15)
    (by norm_num) (by norm_num) (by norm_num)

theorem karlssonOEISQ3_isRadialOutward :
    karlssonOEISQ3.IsRadialOutward := by
  simpa [karlssonOEISQ3] using
    EuclideanLollipop.fromAnchor_isRadialOutward
      (point2 karlssonOEISQ3AnchorX (-(5 / 100))) 100
      karlssonOEISQ3Theta (4 / 15)
      (by norm_num) (by norm_num) (by norm_num)

/-- The recorded normalized direction of `Q3` agrees with its ray vector. -/
theorem karlssonOEISQ3_hasNormalizedBearing :
    karlssonOEISQ3.HasNormalizedBearing := by
  unfold karlssonOEISQ3
  exact EuclideanLollipop.fromAnchor_hasNormalizedBearing
    (by
      unfold karlssonOEISQ3Theta
      ring)

/-- The four exact coordinate lollipops in the OEIS/Karlsson base
arrangement. -/
noncomputable def karlssonOEISBaseArrangement :
    EuclideanLollipopArrangement 4 where
  lollipop
    | 0 => karlssonOEISQ0
    | 1 => karlssonOEISQ1
    | 2 => karlssonOEISQ2
    | 3 => karlssonOEISQ3

@[simp] theorem karlssonOEISBaseArrangement_zero :
    karlssonOEISBaseArrangement.lollipop 0 = karlssonOEISQ0 := rfl

@[simp] theorem karlssonOEISBaseArrangement_one :
    karlssonOEISBaseArrangement.lollipop 1 = karlssonOEISQ1 := rfl

@[simp] theorem karlssonOEISBaseArrangement_two :
    karlssonOEISBaseArrangement.lollipop 2 = karlssonOEISQ2 := rfl

@[simp] theorem karlssonOEISBaseArrangement_three :
    karlssonOEISBaseArrangement.lollipop 3 = karlssonOEISQ3 := rfl

/-- Every stem in the exact OEIS/Karlsson base arrangement satisfies the
manuscript's radial-outward condition. -/
theorem karlssonOEISBaseArrangement_isRadialOutward
    (i : Fin 4) :
    (karlssonOEISBaseArrangement.lollipop i).IsRadialOutward := by
  fin_cases i <;> simp
    [karlssonOEISQ0_isRadialOutward, karlssonOEISQ1_isRadialOutward,
      karlssonOEISQ2_isRadialOutward, karlssonOEISQ3_isRadialOutward]

/-- Every stem in the exact OEIS/Karlsson base arrangement has
normalized-bearing compatibility. -/
theorem karlssonOEISBaseArrangement_hasNormalizedBearings :
    karlssonOEISBaseArrangement.HasNormalizedBearings := by
  intro i
  fin_cases i <;> simp
    [karlssonOEISQ0_hasNormalizedBearing,
      karlssonOEISQ1_hasNormalizedBearing,
      karlssonOEISQ2_hasNormalizedBearing,
      karlssonOEISQ3_hasNormalizedBearing]

/-- The partial region counts obtained by inserting the OEIS/Karlsson base
lollipops in order against the certified table. -/
def karlssonOEISBasePartialRegions : Nat → Rat
  | 0 => 1
  | 1 => 2
  | 2 => 8
  | 3 => 23
  | _ => 45

/-- Ordered insertion-region data for the base table:
`1 -> 2 -> 8 -> 23 -> 45`. -/
def karlssonOEISBaseOrderedRegionData :
    OrderedIncrementalPairRegionData 4 45 karlssonBasePairCrossing where
  partialRegions := karlssonOEISBasePartialRegions
  partialRegions_zero := rfl
  partialRegions_step := by
    intro k hk
    interval_cases k <;>
      simp [karlssonOEISBasePartialRegions, previousPairAdded, previousPairSum,
        Fin.sum_univ_four] <;>
      norm_num
  partialRegions_final := rfl

/-- Stepwise ordered insertion-region data for the base table, splitting the
same arithmetic into the four local insertion steps
`1 -> 2 -> 8 -> 23 -> 45`. -/
def karlssonOEISBaseStepwiseOrderedRegionData :
    StepwiseOrderedIncrementalPairRegionData 4 45 karlssonBasePairCrossing where
  partialRegions := karlssonOEISBasePartialRegions
  partialRegions_zero := rfl
  step := by
    intro k hk
    refine ⟨?_⟩
    interval_cases k <;>
      simp [karlssonOEISBasePartialRegions, previousPairAdded, previousPairSum,
        Fin.sum_univ_four] <;>
      norm_num
  partialRegions_final := rfl

/-- The ordered insertion arithmetic for the OEIS/Karlsson base table gives
`45` regions. -/
theorem karlssonOEISBaseOrderedRegionData_target :
    (45 : Rat) = pairSum 4 karlssonBasePairCrossing + (4 : Rat) + 1 :=
  karlssonOEISBaseOrderedRegionData.target_eq_pairSum_add

/-- The stepwise local insertion arithmetic for the OEIS/Karlsson base table
also gives `45` regions. -/
theorem karlssonOEISBaseStepwiseOrderedRegionData_target :
    (45 : Rat) = pairSum 4 karlssonBasePairCrossing + (4 : Rat) + 1 :=
  karlssonOEISBaseStepwiseOrderedRegionData.target_eq_pairSum_add

/-- First-principles certificate for the exact OEIS/Karlsson coordinate base:
the finite carrier intersections of the four coordinate lollipops are exactly
the Karlsson base table. -/
structure KarlssonOEISBaseCoordinateCrossingCertificate where
  pairwise_crossings :
    PrimitiveGeometry.PairwiseCarrierCrossingData
      karlssonOEISBaseArrangement karlssonBasePairCrossing

/-- One pair of the exact OEIS/Karlsson base-coordinate crossing certificate. -/
structure KarlssonOEISBasePairCoordinateCrossingCertificate
    (i j : Fin 4) (hij : i < j) where
  crossingPoints : Finset PrimitiveGeometry.R2
  crossingPoints_spec :
    (crossingPoints : Set PrimitiveGeometry.R2) =
      karlssonOEISBaseArrangement.pairIntersectionSet i j
  cross_eq_card :
    karlssonBasePairCrossing i j = (crossingPoints.card : Rat)

namespace KarlssonOEISBasePairCoordinateCrossingCertificate

/-- Each exact OEIS/Karlsson pair certificate is an instance of the generic
local primitive carrier-crossing certificate. -/
def toLocalPairCarrierCrossingData
    {i j : Fin 4} {hij : i < j}
    (C : KarlssonOEISBasePairCoordinateCrossingCertificate i j hij) :
    PrimitiveGeometry.LocalPairCarrierCrossingData
      karlssonOEISBaseArrangement karlssonBasePairCrossing i j hij where
  crossingPoints := C.crossingPoints
  crossingPoints_spec := C.crossingPoints_spec
  cross_eq_card := C.cross_eq_card

end KarlssonOEISBasePairCoordinateCrossingCertificate

/-- Six independent pair certificates for the exact OEIS/Karlsson base
arrangement.  This is a more modular replacement boundary for the all-at-once
`PairwiseCarrierCrossingData` certificate above. -/
structure KarlssonOEISBaseSixPairCoordinateCrossingCertificate where
  pair01 :
    KarlssonOEISBasePairCoordinateCrossingCertificate
      (0 : Fin 4) (1 : Fin 4) (by decide)
  pair02 :
    KarlssonOEISBasePairCoordinateCrossingCertificate
      (0 : Fin 4) (2 : Fin 4) (by decide)
  pair03 :
    KarlssonOEISBasePairCoordinateCrossingCertificate
      (0 : Fin 4) (3 : Fin 4) (by decide)
  pair12 :
    KarlssonOEISBasePairCoordinateCrossingCertificate
      (1 : Fin 4) (2 : Fin 4) (by decide)
  pair13 :
    KarlssonOEISBasePairCoordinateCrossingCertificate
      (1 : Fin 4) (3 : Fin 4) (by decide)
  pair23 :
    KarlssonOEISBasePairCoordinateCrossingCertificate
      (2 : Fin 4) (3 : Fin 4) (by decide)

namespace KarlssonOEISBaseSixPairCoordinateCrossingCertificate

/-- The finite crossing-point set selected from the six explicit pair
certificates.  It is only used with proofs `i < j`; the final `empty` branch is
for impossible or unordered pairs. -/
noncomputable def crossingPoints
    (C : KarlssonOEISBaseSixPairCoordinateCrossingCertificate)
    (i j : Fin 4) : Finset PrimitiveGeometry.R2 :=
  if i = (0 : Fin 4) ∧ j = (1 : Fin 4) then
    C.pair01.crossingPoints
  else if i = (0 : Fin 4) ∧ j = (2 : Fin 4) then
    C.pair02.crossingPoints
  else if i = (0 : Fin 4) ∧ j = (3 : Fin 4) then
    C.pair03.crossingPoints
  else if i = (1 : Fin 4) ∧ j = (2 : Fin 4) then
    C.pair12.crossingPoints
  else if i = (1 : Fin 4) ∧ j = (3 : Fin 4) then
    C.pair13.crossingPoints
  else if i = (2 : Fin 4) ∧ j = (3 : Fin 4) then
    C.pair23.crossingPoints
  else
    ∅

/-- Select the corresponding generic local carrier-intersection certificate
from the six exact OEIS/Karlsson pair certificates. -/
noncomputable def localPairCarrierCrossingData
    (C : KarlssonOEISBaseSixPairCoordinateCrossingCertificate)
    (i j : Fin 4) (hij : i < j) :
    PrimitiveGeometry.LocalPairCarrierCrossingData
      karlssonOEISBaseArrangement karlssonBasePairCrossing i j hij where
  crossingPoints := C.crossingPoints i j
  crossingPoints_spec := by
    fin_cases i <;> fin_cases j <;>
      simp [crossingPoints] at hij ⊢
    · exact C.pair01.crossingPoints_spec
    · exact C.pair02.crossingPoints_spec
    · exact C.pair03.crossingPoints_spec
    · exact C.pair12.crossingPoints_spec
    · exact C.pair13.crossingPoints_spec
    · exact C.pair23.crossingPoints_spec
  cross_eq_card := by
    fin_cases i <;> fin_cases j <;>
      simp [crossingPoints] at hij ⊢
    · exact C.pair01.cross_eq_card
    · exact C.pair02.cross_eq_card
    · exact C.pair03.cross_eq_card
    · exact C.pair12.cross_eq_card
    · exact C.pair13.cross_eq_card
    · exact C.pair23.cross_eq_card

/-- Six pair certificates assemble into the original all-pairs OEIS/Karlsson
base-coordinate certificate. -/
noncomputable def toCoordinateCrossingCertificate
    (C : KarlssonOEISBaseSixPairCoordinateCrossingCertificate) :
    KarlssonOEISBaseCoordinateCrossingCertificate where
  pairwise_crossings :=
    PrimitiveGeometry.PairwiseCarrierCrossingData.ofLocal
      (C.localPairCarrierCrossingData)

end KarlssonOEISBaseSixPairCoordinateCrossingCertificate

end ExplicitInputs
end TheoremOneManuscript
end Lollipop

/-!
Proof component 25: `Manuscript.ExplicitInputs.KarlssonOEISGeometry`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Geometry-facing consequences of the exact OEIS/Karlsson base certificate.

`KarlssonOEIS.lean` records the four coordinate lollipops and names the finite
carrier-intersection certificate type.  This file unwraps that certificate
into the six concrete cardinality obligations for the displayed
`5,7,7,7,7,7` base table, and records easy noncoincidence facts that follow
from the visible radii.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace ExplicitInputs

open PrimitiveGeometry
open TheoremOneEndToEnd.PaulsenLinearAlgebra

/-- Determinant of two bearing direction vectors. -/
theorem det2_angleDirection (theta phi : ℝ) :
    det2 (angleDirection theta) (angleDirection phi) =
      Real.sin (phi - theta) := by
  unfold det2 angleDirection point2
  rw [Real.sin_sub]
  ring

/-- The recorded normalized OEIS directions make the exceptional base pair
`(Q0,Q1)` a close pair in the cyclic direction relation. -/
theorem karlssonOEISBase_zero_one_cyclicClose :
    TheoremOneEndToEnd.CloseDirection.cyclicClose
      (fun i : Fin 4 => karlssonOEISBaseArrangement.normalizedDirection i)
      (0 : Fin 4) (1 : Fin 4) := by
  unfold TheoremOneEndToEnd.CloseDirection.cyclicClose
    TheoremOneEndToEnd.CloseDirection.cyclicClosePair
  right
  let eps : ℝ := (1 / 100 : ℝ) / (2 * Real.pi)
  have heps_le_quarter : eps ≤ 1 / 4 := by
    dsimp [eps]
    have hden : 0 < 2 * Real.pi := by positivity
    rw [div_le_iff₀ hden]
    nlinarith [Real.pi_gt_three]
  have hdiff :
      karlssonOEISBaseArrangement.normalizedDirection (0 : Fin 4) -
        karlssonOEISBaseArrangement.normalizedDirection (1 : Fin 4) =
      -(1 - eps) := by
    dsimp [eps]
    simp [EuclideanLollipopArrangement.normalizedDirection,
      karlssonOEISBaseArrangement, karlssonOEISQ0, karlssonOEISQ1,
      EuclideanLollipop.fromAnchor, EuclideanLollipop.fromCenter,
      normalizedMinusPoint01]
  rw [hdiff, abs_neg]
  have hnonneg : 0 ≤ 1 - eps := by linarith
  rw [abs_of_nonneg hnonneg]
  linarith

/-- The OEIS base pair `(Q0,Q2)` is not close by its recorded normalized
directions. -/
theorem karlssonOEISBase_zero_two_not_cyclicClose :
    ¬ TheoremOneEndToEnd.CloseDirection.cyclicClose
      (fun i : Fin 4 => karlssonOEISBaseArrangement.normalizedDirection i)
      (0 : Fin 4) (2 : Fin 4) := by
  apply TheoremOneEndToEnd.CloseDirection.not_cyclicClose_of_abs_between
  · norm_num [EuclideanLollipopArrangement.normalizedDirection,
      karlssonOEISBaseArrangement, karlssonOEISQ0, karlssonOEISQ2,
      EuclideanLollipop.fromAnchor]
  · norm_num [EuclideanLollipopArrangement.normalizedDirection,
      karlssonOEISBaseArrangement, karlssonOEISQ0, karlssonOEISQ2,
      EuclideanLollipop.fromAnchor]

/-- The OEIS base pair `(Q0,Q3)` is not close by its recorded normalized
directions. -/
theorem karlssonOEISBase_zero_three_not_cyclicClose :
    ¬ TheoremOneEndToEnd.CloseDirection.cyclicClose
      (fun i : Fin 4 => karlssonOEISBaseArrangement.normalizedDirection i)
      (0 : Fin 4) (3 : Fin 4) := by
  apply TheoremOneEndToEnd.CloseDirection.not_cyclicClose_of_abs_between
  · norm_num [EuclideanLollipopArrangement.normalizedDirection,
      karlssonOEISBaseArrangement, karlssonOEISQ0, karlssonOEISQ3,
      EuclideanLollipop.fromAnchor]
  · norm_num [EuclideanLollipopArrangement.normalizedDirection,
      karlssonOEISBaseArrangement, karlssonOEISQ0, karlssonOEISQ3,
      EuclideanLollipop.fromAnchor]

/-- The OEIS base pair `(Q2,Q3)` is not close by its recorded normalized
directions. -/
theorem karlssonOEISBase_two_three_not_cyclicClose :
    ¬ TheoremOneEndToEnd.CloseDirection.cyclicClose
      (fun i : Fin 4 => karlssonOEISBaseArrangement.normalizedDirection i)
      (2 : Fin 4) (3 : Fin 4) := by
  apply TheoremOneEndToEnd.CloseDirection.not_cyclicClose_of_abs_between
  · norm_num [EuclideanLollipopArrangement.normalizedDirection,
      karlssonOEISBaseArrangement, karlssonOEISQ2, karlssonOEISQ3,
      EuclideanLollipop.fromAnchor]
  · norm_num [EuclideanLollipopArrangement.normalizedDirection,
      karlssonOEISBaseArrangement, karlssonOEISQ2, karlssonOEISQ3,
      EuclideanLollipop.fromAnchor]

/-- The small negative-direction normalization error in `Q1` is below
`1/15`, which is enough for the remaining OEIS non-close direction checks. -/
private theorem karlssonOEISBase_q1_epsilon_lt_one_fifteenth :
    (1 / 100 : ℝ) / (2 * Real.pi) < 1 / 15 := by
  have hden : 0 < 2 * Real.pi := by positivity
  rw [div_lt_iff₀ hden]
  nlinarith [Real.pi_gt_three]

/-- The OEIS base pair `(Q1,Q2)` is not close by its recorded normalized
directions. -/
theorem karlssonOEISBase_one_two_not_cyclicClose :
    ¬ TheoremOneEndToEnd.CloseDirection.cyclicClose
      (fun i : Fin 4 => karlssonOEISBaseArrangement.normalizedDirection i)
      (1 : Fin 4) (2 : Fin 4) := by
  let eps : ℝ := (1 / 100 : ℝ) / (2 * Real.pi)
  have heps_lt : eps < 1 / 15 := by
    simpa [eps] using karlssonOEISBase_q1_epsilon_lt_one_fifteenth
  have heps_pos : 0 < eps := by positivity
  have hdiff :
      karlssonOEISBaseArrangement.normalizedDirection (1 : Fin 4) -
        karlssonOEISBaseArrangement.normalizedDirection (2 : Fin 4) =
      19 / 60 - eps := by
    dsimp [eps]
    simp [EuclideanLollipopArrangement.normalizedDirection,
      karlssonOEISBaseArrangement, karlssonOEISQ1, karlssonOEISQ2,
      EuclideanLollipop.fromCenter, EuclideanLollipop.fromAnchor,
      normalizedMinusPoint01]
    ring
  have habs :
      |karlssonOEISBaseArrangement.normalizedDirection (1 : Fin 4) -
        karlssonOEISBaseArrangement.normalizedDirection (2 : Fin 4)| =
      19 / 60 - eps := by
    rw [hdiff]
    rw [abs_of_nonneg]
    linarith
  apply TheoremOneEndToEnd.CloseDirection.not_cyclicClose_of_abs_between
  · rw [habs]
    linarith
  · rw [habs]
    linarith

/-- The OEIS base pair `(Q1,Q3)` is not close by its recorded normalized
directions. -/
theorem karlssonOEISBase_one_three_not_cyclicClose :
    ¬ TheoremOneEndToEnd.CloseDirection.cyclicClose
      (fun i : Fin 4 => karlssonOEISBaseArrangement.normalizedDirection i)
      (1 : Fin 4) (3 : Fin 4) := by
  let eps : ℝ := (1 / 100 : ℝ) / (2 * Real.pi)
  have heps_lt : eps < 1 / 15 := by
    simpa [eps] using karlssonOEISBase_q1_epsilon_lt_one_fifteenth
  have heps_pos : 0 < eps := by positivity
  have hdiff :
      karlssonOEISBaseArrangement.normalizedDirection (1 : Fin 4) -
        karlssonOEISBaseArrangement.normalizedDirection (3 : Fin 4) =
      11 / 15 - eps := by
    dsimp [eps]
    simp [EuclideanLollipopArrangement.normalizedDirection,
      karlssonOEISBaseArrangement, karlssonOEISQ1, karlssonOEISQ3,
      EuclideanLollipop.fromCenter, EuclideanLollipop.fromAnchor,
      normalizedMinusPoint01]
    ring
  have habs :
      |karlssonOEISBaseArrangement.normalizedDirection (1 : Fin 4) -
        karlssonOEISBaseArrangement.normalizedDirection (3 : Fin 4)| =
      11 / 15 - eps := by
    rw [hdiff]
    rw [abs_of_nonneg]
    linarith
  apply TheoremOneEndToEnd.CloseDirection.not_cyclicClose_of_abs_between
  · rw [habs]
    linarith
  · rw [habs]
    linarith

/-- The same exceptional OEIS base pair is not intriguing: its two circles
satisfy Paulsen's strict obtuse-intersection distance condition. -/
theorem karlssonOEISQ0_Q1_circleObtuseCondition :
    circleObtuseCondition karlssonOEISQ0.radius karlssonOEISQ1.radius
      karlssonOEISQ0.center karlssonOEISQ1.center := by
  unfold circleObtuseCondition distSq2 normSq2 dot2
  norm_num [karlssonOEISQ0, karlssonOEISQ1,
    EuclideanLollipop.fromAnchor, EuclideanLollipop.fromCenter,
    angleDirection, point2]

/-- Pair-level form: `(Q0,Q1)` is not intriguing. -/
theorem karlssonOEISQ0_Q1_not_circleIntriguingPair :
    ¬ circleIntriguingPair karlssonOEISQ0.radius karlssonOEISQ1.radius
      karlssonOEISQ0.center karlssonOEISQ1.center := by
  classical
  exact not_not.mpr karlssonOEISQ0_Q1_circleObtuseCondition

/-- Arrangement-level form: the exact OEIS base pair `(0,1)` is not
intriguing for the canonical circle relation. -/
theorem karlssonOEISBase_zero_one_not_circleIntriguing :
    ¬ circleIntriguing
      (fun i : Fin 4 => karlssonOEISBaseArrangement.center i)
      (fun i : Fin 4 => karlssonOEISBaseArrangement.radius i)
      (0 : Fin 4) (1 : Fin 4) := by
  simpa [circleIntriguing, EuclideanLollipopArrangement.center,
    EuclideanLollipopArrangement.radius] using
    karlssonOEISQ0_Q1_not_circleIntriguingPair

/-- The finite carrier-intersection certificate identifies every certified
pair's finite set cardinality with the Karlsson base table. -/
theorem KarlssonOEISBaseCoordinateCrossingCertificate.crossingPoints_card_eq_base
    (C : KarlssonOEISBaseCoordinateCrossingCertificate)
    {i j : Fin 4} (hij : i < j) :
    ((C.pairwise_crossings.crossingPoints i j hij).card : Rat) =
      karlssonBasePairCrossing i j := by
  exact (C.pairwise_crossings.cross_eq_card i j hij).symm

/-- The exceptional base pair has exactly five certified carrier-intersection
points. -/
theorem KarlssonOEISBaseCoordinateCrossingCertificate.card_zero_one
    (C : KarlssonOEISBaseCoordinateCrossingCertificate) :
    (C.pairwise_crossings.crossingPoints (0 : Fin 4) (1 : Fin 4)
      (by decide)).card = 5 := by
  have h :=
    C.crossingPoints_card_eq_base
      (i := (0 : Fin 4)) (j := (1 : Fin 4)) (by decide)
  norm_num at h
  exact_mod_cast h

/-- The `(0,2)` base pair has exactly seven certified carrier-intersection
points. -/
theorem KarlssonOEISBaseCoordinateCrossingCertificate.card_zero_two
    (C : KarlssonOEISBaseCoordinateCrossingCertificate) :
    (C.pairwise_crossings.crossingPoints (0 : Fin 4) (2 : Fin 4)
      (by decide)).card = 7 := by
  have h :=
    C.crossingPoints_card_eq_base
      (i := (0 : Fin 4)) (j := (2 : Fin 4)) (by decide)
  norm_num at h
  exact_mod_cast h

/-- The `(0,3)` base pair has exactly seven certified carrier-intersection
points. -/
theorem KarlssonOEISBaseCoordinateCrossingCertificate.card_zero_three
    (C : KarlssonOEISBaseCoordinateCrossingCertificate) :
    (C.pairwise_crossings.crossingPoints (0 : Fin 4) (3 : Fin 4)
      (by decide)).card = 7 := by
  have h :=
    C.crossingPoints_card_eq_base
      (i := (0 : Fin 4)) (j := (3 : Fin 4)) (by decide)
  norm_num at h
  exact_mod_cast h

/-- The `(1,2)` base pair has exactly seven certified carrier-intersection
points. -/
theorem KarlssonOEISBaseCoordinateCrossingCertificate.card_one_two
    (C : KarlssonOEISBaseCoordinateCrossingCertificate) :
    (C.pairwise_crossings.crossingPoints (1 : Fin 4) (2 : Fin 4)
      (by decide)).card = 7 := by
  have h :=
    C.crossingPoints_card_eq_base
      (i := (1 : Fin 4)) (j := (2 : Fin 4)) (by decide)
  norm_num at h
  exact_mod_cast h

/-- The `(1,3)` base pair has exactly seven certified carrier-intersection
points. -/
theorem KarlssonOEISBaseCoordinateCrossingCertificate.card_one_three
    (C : KarlssonOEISBaseCoordinateCrossingCertificate) :
    (C.pairwise_crossings.crossingPoints (1 : Fin 4) (3 : Fin 4)
      (by decide)).card = 7 := by
  have h :=
    C.crossingPoints_card_eq_base
      (i := (1 : Fin 4)) (j := (3 : Fin 4)) (by decide)
  norm_num at h
  exact_mod_cast h

/-- The `(2,3)` base pair has exactly seven certified carrier-intersection
points. -/
theorem KarlssonOEISBaseCoordinateCrossingCertificate.card_two_three
    (C : KarlssonOEISBaseCoordinateCrossingCertificate) :
    (C.pairwise_crossings.crossingPoints (2 : Fin 4) (3 : Fin 4)
      (by decide)).card = 7 := by
  have h :=
    C.crossingPoints_card_eq_base
      (i := (2 : Fin 4)) (j := (3 : Fin 4)) (by decide)
  norm_num at h
  exact_mod_cast h

/-- Proposition bundling the six displayed OEIS/Karlsson base-coordinate
finite carrier-intersection cardinalities. -/
def KarlssonOEISBaseCoordinateCrossingCertificate.SixPairCardinalities
    (C : KarlssonOEISBaseCoordinateCrossingCertificate) : Prop :=
  (C.pairwise_crossings.crossingPoints (0 : Fin 4) (1 : Fin 4)
    (by decide)).card = 5 ∧
  (C.pairwise_crossings.crossingPoints (0 : Fin 4) (2 : Fin 4)
    (by decide)).card = 7 ∧
  (C.pairwise_crossings.crossingPoints (0 : Fin 4) (3 : Fin 4)
    (by decide)).card = 7 ∧
  (C.pairwise_crossings.crossingPoints (1 : Fin 4) (2 : Fin 4)
    (by decide)).card = 7 ∧
  (C.pairwise_crossings.crossingPoints (1 : Fin 4) (3 : Fin 4)
    (by decide)).card = 7 ∧
  (C.pairwise_crossings.crossingPoints (2 : Fin 4) (3 : Fin 4)
    (by decide)).card = 7

/-- The exact OEIS/Karlsson base-coordinate certificate is equivalent, at
the six displayed unordered pairs, to the visible `5,7,7,7,7,7` finite
carrier-intersection cardinalities. -/
theorem KarlssonOEISBaseCoordinateCrossingCertificate.six_pair_cardinalities
    (C : KarlssonOEISBaseCoordinateCrossingCertificate) :
    C.SixPairCardinalities := by
  exact ⟨C.card_zero_one, C.card_zero_two, C.card_zero_three,
    C.card_one_two, C.card_one_three, C.card_two_three⟩

/-- Six independent pair certificates imply the bundled six displayed
OEIS/Karlsson cardinalities after assembly into the all-pairs certificate. -/
theorem KarlssonOEISBaseSixPairCoordinateCrossingCertificate.six_pair_cardinalities
    (C : KarlssonOEISBaseSixPairCoordinateCrossingCertificate) :
    C.toCoordinateCrossingCertificate.SixPairCardinalities :=
  C.toCoordinateCrossingCertificate.six_pair_cardinalities

/-- The OEIS `Q0` and `Q1` lifted circles are different, already because
their radii are different. -/
theorem karlssonOEISQ0_Q1_spheres_distinct :
    euclideanSphere karlssonOEISQ0.center karlssonOEISQ0.radius ≠
      euclideanSphere karlssonOEISQ1.center karlssonOEISQ1.radius := by
  apply euclideanSphere_ne_of_radius_ne
  norm_num [karlssonOEISQ0, karlssonOEISQ1,
    EuclideanLollipop.fromAnchor, EuclideanLollipop.fromCenter]

/-- The OEIS `Q0` and `Q2` lifted circles are different, already because
their radii are different. -/
theorem karlssonOEISQ0_Q2_spheres_distinct :
    euclideanSphere karlssonOEISQ0.center karlssonOEISQ0.radius ≠
      euclideanSphere karlssonOEISQ2.center karlssonOEISQ2.radius := by
  apply euclideanSphere_ne_of_radius_ne
  norm_num [karlssonOEISQ0, karlssonOEISQ2,
    EuclideanLollipop.fromAnchor]

/-- The OEIS `Q0` and `Q3` lifted circles are different, already because
their radii are different. -/
theorem karlssonOEISQ0_Q3_spheres_distinct :
    euclideanSphere karlssonOEISQ0.center karlssonOEISQ0.radius ≠
      euclideanSphere karlssonOEISQ3.center karlssonOEISQ3.radius := by
  apply euclideanSphere_ne_of_radius_ne
  norm_num [karlssonOEISQ0, karlssonOEISQ3,
    EuclideanLollipop.fromAnchor]

/-- The OEIS `Q1` and `Q2` lifted circles are different, already because
their radii are different. -/
theorem karlssonOEISQ1_Q2_spheres_distinct :
    euclideanSphere karlssonOEISQ1.center karlssonOEISQ1.radius ≠
      euclideanSphere karlssonOEISQ2.center karlssonOEISQ2.radius := by
  apply euclideanSphere_ne_of_radius_ne
  norm_num [karlssonOEISQ1, karlssonOEISQ2,
    EuclideanLollipop.fromCenter, EuclideanLollipop.fromAnchor]

/-- The OEIS `Q1` and `Q3` lifted circles are different, already because
their radii are different. -/
theorem karlssonOEISQ1_Q3_spheres_distinct :
    euclideanSphere karlssonOEISQ1.center karlssonOEISQ1.radius ≠
      euclideanSphere karlssonOEISQ3.center karlssonOEISQ3.radius := by
  apply euclideanSphere_ne_of_radius_ne
  norm_num [karlssonOEISQ1, karlssonOEISQ3,
    EuclideanLollipop.fromCenter, EuclideanLollipop.fromAnchor]

/-- The `y`-coordinate of the OEIS `Q2` circle center is positive. -/
theorem karlssonOEISQ2_center_y_pos :
    0 < karlssonOEISQ2.center 1 := by
  have hcos : 0 < Real.cos (2 * Real.pi / 15) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_pos]
  have hsin :
      Real.sin karlssonOEISQ2Theta =
        -Real.cos (2 * Real.pi / 15) := by
    rw [karlssonOEISQ2Theta, Real.sin_neg]
    rw [show Real.pi / 2 + 2 * Real.pi / 15 =
      2 * Real.pi / 15 + Real.pi / 2 by ring]
    rw [Real.sin_add_pi_div_two]
  simp [karlssonOEISQ2, EuclideanLollipop.fromAnchor,
    angleDirection, point2, hsin]
  nlinarith

/-- The `y`-coordinate of the OEIS `Q3` circle center is negative. -/
theorem karlssonOEISQ3_center_y_neg :
    karlssonOEISQ3.center 1 < 0 := by
  have hcos : 0 < Real.cos (Real.pi / 30) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_pos]
  have hsin :
      Real.sin karlssonOEISQ3Theta =
        Real.cos (Real.pi / 30) := by
    rw [karlssonOEISQ3Theta]
    rw [show Real.pi / 2 + Real.pi / 30 =
      Real.pi / 30 + Real.pi / 2 by ring]
    rw [Real.sin_add_pi_div_two]
  simp [karlssonOEISQ3, EuclideanLollipop.fromAnchor,
    angleDirection, point2, hsin]
  nlinarith

/-- The OEIS `Q2` and `Q3` lifted circles are different.  They have the same
radius, so this proof uses the signs of their center `y`-coordinates. -/
theorem karlssonOEISQ2_Q3_spheres_distinct :
    euclideanSphere karlssonOEISQ2.center karlssonOEISQ2.radius ≠
      euclideanSphere karlssonOEISQ3.center karlssonOEISQ3.radius := by
  apply euclideanSphere_ne_of_center_ne
  intro hcenter
  have hy : karlssonOEISQ2.center 1 = karlssonOEISQ3.center 1 :=
    congr_fun hcenter 1
  have hq3_pos : 0 < karlssonOEISQ3.center 1 := by
    simpa [hy] using karlssonOEISQ2_center_y_pos
  exact (not_lt_of_ge hq3_pos.le) karlssonOEISQ3_center_y_neg

/-- The OEIS `Q0` and `Q1` ray-supporting lines are different. -/
theorem karlssonOEISQ0_Q1_rayLines_distinct :
    euclideanRayLine karlssonOEISQ0 ≠ euclideanRayLine karlssonOEISQ1 := by
  apply euclideanRayLine_ne_of_det2_rayDirection_ne_zero
  have hsin_pos : 0 < Real.sin ((1 : ℝ) / 100) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · norm_num
    · nlinarith [Real.pi_gt_three]
  have hdet :
      det2 karlssonOEISQ0.rayDirection karlssonOEISQ1.rayDirection =
        -Real.sin ((1 : ℝ) / 100) := by
    simp [karlssonOEISQ0, karlssonOEISQ1,
      EuclideanLollipop.fromAnchor, EuclideanLollipop.fromCenter,
      angleDirection, det2, point2, Real.sin_neg]
  rw [hdet]
  exact neg_ne_zero.mpr hsin_pos.ne'

/-- In the exceptional OEIS base pair, the `Q1` ray anchor is strictly
outside the `Q0` circle. -/
theorem karlssonOEISQ0_Q1_circleRay_anchor_distSq_gt_radius_sq :
    karlssonOEISQ0.radius ^ 2 <
      distSq2 karlssonOEISQ1.anchor karlssonOEISQ0.center := by
  have hcos_pos : 0 < Real.cos ((1 / 100 : ℝ)) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_gt_three]
  let x : ℝ := 200 + 45 / 100 + 55 / 100 * Real.cos ((1 / 100 : ℝ))
  let y : ℝ := 4 / 10 - 55 / 100 * Real.sin ((1 / 100 : ℝ))
  have hx_gt : (200 : ℝ) < x := by
    dsimp [x]
    nlinarith
  have hx_sq_gt : (200 : ℝ) ^ 2 < x ^ 2 :=
    (sq_lt_sq₀ (by norm_num) (by nlinarith)).2 hx_gt
  have hy_sq_nonneg : 0 ≤ y ^ 2 := sq_nonneg y
  dsimp [x, y] at hx_sq_gt hy_sq_nonneg
  unfold distSq2 normSq2 dot2
  simp [karlssonOEISQ0, karlssonOEISQ1,
    EuclideanLollipop.fromAnchor, EuclideanLollipop.fromCenter,
    angleDirection, point2, Real.cos_neg, Real.sin_neg]
  nlinarith

/-- In the exceptional OEIS base pair, the `Q1` ray points weakly away from
the `Q0` center. -/
theorem karlssonOEISQ0_Q1_circleRay_anchor_dot_nonneg :
    0 ≤
      dot2 (karlssonOEISQ1.anchor - karlssonOEISQ0.center)
        karlssonOEISQ1.rayDirection := by
  have hcos_pos : 0 < Real.cos ((1 / 100 : ℝ)) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_gt_three]
  have hsin_le_one : Real.sin ((1 / 100 : ℝ)) ≤ 1 :=
    Real.sin_le_one ((1 / 100 : ℝ))
  have htrig := Real.cos_sq_add_sin_sq ((1 / 100 : ℝ))
  unfold dot2
  simp [karlssonOEISQ0, karlssonOEISQ1,
    EuclideanLollipop.fromAnchor, EuclideanLollipop.fromCenter,
    angleDirection, point2, Real.cos_neg, Real.sin_neg]
  nlinarith

/-- Therefore the `circle(Q0) ∩ ray(Q1)` component is empty. -/
theorem karlssonOEISQ0_Q1_circleRaySet_empty :
    ∀ p : EuclideanR2,
      p ∉ euclideanCircleRaySet karlssonOEISQ0 karlssonOEISQ1 :=
  euclideanCircleRaySet_empty_of_radius_sq_lt_anchor_distSq2_of_dot_nonneg
    karlssonOEISQ0_Q1_circleRay_anchor_distSq_gt_radius_sq
    karlssonOEISQ0_Q1_circleRay_anchor_dot_nonneg

/-- For the exceptional OEIS base pair, the `Q1` ray starts outside the `Q0`
circle and points weakly away from the `Q0` center.  Hence the
circle-ray component `circle(Q0) ∩ ray(Q1)` is empty, giving a concrete
named `<= 5` savings route for the close pair. -/
noncomputable def karlssonOEISQ0_Q1_circleRayOutward_savings_route :
    PairComponentSavingsFiveRoute karlssonOEISQ0 karlssonOEISQ1 :=
  PairComponentSavingsFiveRoute.circleRayOutward
    karlssonOEISQ0_Q1_spheres_distinct
    karlssonOEISQ0_Q1_rayLines_distinct
    karlssonOEISQ0_Q1_circleRay_anchor_distSq_gt_radius_sq
    karlssonOEISQ0_Q1_circleRay_anchor_dot_nonneg

/-- The OEIS `Q0` and `Q2` ray-supporting lines are different. -/
theorem karlssonOEISQ0_Q2_rayLines_distinct :
    euclideanRayLine karlssonOEISQ0 ≠ euclideanRayLine karlssonOEISQ2 := by
  apply euclideanRayLine_ne_of_det2_rayDirection_ne_zero
  have hsin_pos : 0 < Real.sin (Real.pi / 2 + 2 * Real.pi / 15) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  intro hzero
  have hzero' :
      Real.sin (-(2 * Real.pi / 15) + -(Real.pi / 2)) = 0 := by
    simpa [karlssonOEISQ0, karlssonOEISQ2,
      EuclideanLollipop.fromAnchor, angleDirection, det2, point2,
      karlssonOEISQ2Theta] using hzero
  have hangle :
      -(2 * Real.pi / 15) + -(Real.pi / 2) =
        -(Real.pi / 2 + 2 * Real.pi / 15) := by
    ring
  rw [hangle, Real.sin_neg] at hzero'
  exact hsin_pos.ne' (neg_eq_zero.mp hzero')

/-- The OEIS `Q0` and `Q3` ray-supporting lines are different. -/
theorem karlssonOEISQ0_Q3_rayLines_distinct :
    euclideanRayLine karlssonOEISQ0 ≠ euclideanRayLine karlssonOEISQ3 := by
  apply euclideanRayLine_ne_of_det2_rayDirection_ne_zero
  have hsin_pos : 0 < Real.sin (Real.pi / 2 + Real.pi / 30) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  have hdet :
      det2 karlssonOEISQ0.rayDirection karlssonOEISQ3.rayDirection =
        Real.sin (Real.pi / 2 + Real.pi / 30) := by
    simp [karlssonOEISQ0, karlssonOEISQ3,
      EuclideanLollipop.fromAnchor, angleDirection, det2, point2,
      karlssonOEISQ3Theta]
  rw [hdet]
  exact hsin_pos.ne'

/-- The OEIS `Q1` and `Q2` ray-supporting lines are different. -/
theorem karlssonOEISQ1_Q2_rayLines_distinct :
    euclideanRayLine karlssonOEISQ1 ≠ euclideanRayLine karlssonOEISQ2 := by
  apply euclideanRayLine_ne_of_det2_rayDirection_ne_zero
  intro hzero
  let x : ℝ := (1 : ℝ) / 100 - (Real.pi / 2 + 2 * Real.pi / 15)
  have hsin_neg : Real.sin x < 0 := by
    apply Real.sin_neg_of_neg_of_neg_pi_lt
    · dsimp [x]
      nlinarith [Real.pi_gt_three]
    · dsimp [x]
      nlinarith [Real.pi_pos]
  have hzero' : Real.sin x = 0 := by
    have hraw :
        Real.sin (karlssonOEISQ2Theta - (-(1 / 100 : ℝ))) = 0 := by
      simpa [karlssonOEISQ1, karlssonOEISQ2,
        EuclideanLollipop.fromCenter, EuclideanLollipop.fromAnchor,
        det2_angleDirection] using hzero
    have hangle :
        karlssonOEISQ2Theta - (-(1 / 100 : ℝ)) = x := by
      dsimp [x, karlssonOEISQ2Theta]
      ring
    rwa [hangle] at hraw
  exact hsin_neg.ne hzero'

/-- The OEIS `Q1` and `Q3` ray-supporting lines are different. -/
theorem karlssonOEISQ1_Q3_rayLines_distinct :
    euclideanRayLine karlssonOEISQ1 ≠ euclideanRayLine karlssonOEISQ3 := by
  apply euclideanRayLine_ne_of_det2_rayDirection_ne_zero
  let x : ℝ := Real.pi / 2 + Real.pi / 30 + (1 : ℝ) / 100
  have hsin_pos : 0 < Real.sin x := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · dsimp [x]
      nlinarith [Real.pi_pos]
    · dsimp [x]
      nlinarith [Real.pi_gt_three]
  intro hzero
  have hzero' : Real.sin x = 0 := by
    have hraw :
        Real.sin (karlssonOEISQ3Theta - (-(1 / 100 : ℝ))) = 0 := by
      simpa [karlssonOEISQ1, karlssonOEISQ3,
        EuclideanLollipop.fromCenter, EuclideanLollipop.fromAnchor,
        det2_angleDirection] using hzero
    have hangle :
        karlssonOEISQ3Theta - (-(1 / 100 : ℝ)) = x := by
      dsimp [x, karlssonOEISQ3Theta]
      ring
    rwa [hangle] at hraw
  exact hsin_pos.ne' hzero'

/-- The OEIS `Q2` and `Q3` ray-supporting lines are different. -/
theorem karlssonOEISQ2_Q3_rayLines_distinct :
    euclideanRayLine karlssonOEISQ2 ≠ euclideanRayLine karlssonOEISQ3 := by
  apply euclideanRayLine_ne_of_det2_rayDirection_ne_zero
  intro hzero
  have hsin_pos : 0 < Real.sin (Real.pi / 6) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  have hzero' : -Real.sin (Real.pi / 6) = 0 := by
    have hraw :
        Real.sin (karlssonOEISQ3Theta - karlssonOEISQ2Theta) = 0 := by
      simpa [karlssonOEISQ2, karlssonOEISQ3,
        EuclideanLollipop.fromAnchor, det2_angleDirection] using hzero
    have hangle :
        karlssonOEISQ3Theta - karlssonOEISQ2Theta =
          Real.pi / 6 + Real.pi := by
      dsimp [karlssonOEISQ2Theta, karlssonOEISQ3Theta]
      ring
    rw [hangle, Real.sin_add_pi] at hraw
    exact hraw
  exact hsin_pos.ne' (neg_eq_zero.mp hzero')

/-- Uniform lifted-circle noncoincidence theorem for all six unordered pairs
of the OEIS/Karlsson base arrangement. -/
theorem karlssonOEISBase_spheres_distinct
    {i j : Fin 4} (hij : i < j) :
    euclideanSphere (karlssonOEISBaseArrangement.lollipop i).center
        (karlssonOEISBaseArrangement.lollipop i).radius ≠
      euclideanSphere (karlssonOEISBaseArrangement.lollipop j).center
        (karlssonOEISBaseArrangement.lollipop j).radius := by
  fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
    first
    | exact karlssonOEISQ0_Q1_spheres_distinct
    | exact karlssonOEISQ0_Q2_spheres_distinct
    | exact karlssonOEISQ0_Q3_spheres_distinct
    | exact karlssonOEISQ1_Q2_spheres_distinct
    | exact karlssonOEISQ1_Q3_spheres_distinct
    | exact karlssonOEISQ2_Q3_spheres_distinct

/-- Uniform ray-supporting-line noncoincidence theorem for all six unordered
pairs of the OEIS/Karlsson base arrangement. -/
theorem karlssonOEISBase_rayLines_distinct
    {i j : Fin 4} (hij : i < j) :
    euclideanRayLine (karlssonOEISBaseArrangement.lollipop i) ≠
      euclideanRayLine (karlssonOEISBaseArrangement.lollipop j) := by
  fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
    first
    | exact karlssonOEISQ0_Q1_rayLines_distinct
    | exact karlssonOEISQ0_Q2_rayLines_distinct
    | exact karlssonOEISQ0_Q3_rayLines_distinct
    | exact karlssonOEISQ1_Q2_rayLines_distinct
    | exact karlssonOEISQ1_Q3_rayLines_distinct
    | exact karlssonOEISQ2_Q3_rayLines_distinct

/-- Once the exact OEIS/Karlsson base carrier-intersection certificate is
supplied, the generic component-count theorem recovers the universal
`<= 7` crossing bound for every base pair from the checked noncoincidence
facts above. -/
theorem KarlssonOEISBaseCoordinateCrossingCertificate.cross_le_seven
    (C : KarlssonOEISBaseCoordinateCrossingCertificate)
    {i j : Fin 4} (hij : i < j) :
    karlssonBasePairCrossing i j ≤ 7 :=
  pairwiseCarrierCrossingData_cross_le_seven
    C.pairwise_crossings hij
    (karlssonOEISBase_spheres_distinct hij)
    (karlssonOEISBase_rayLines_distinct hij)

/-- Six independent pair certificates imply the generic `<= 7` crossing bound
for every exact OEIS/Karlsson base pair after assembly. -/
theorem KarlssonOEISBaseSixPairCoordinateCrossingCertificate.cross_le_seven
    (C : KarlssonOEISBaseSixPairCoordinateCrossingCertificate)
    {i j : Fin 4} (hij : i < j) :
    karlssonBasePairCrossing i j ≤ 7 :=
  C.toCoordinateCrossingCertificate.cross_le_seven hij

/-- The exact OEIS `(Q0,Q1)` pair forms a complete primitive routed local
pair-data object once the six-pair local finite carrier witness is supplied.
The close branch uses the concrete half-line-outward route; the intriguing
branches are impossible because the pair is not intriguing. -/
noncomputable def KarlssonOEISBaseSixPairCoordinateCrossingCertificate.zero_one_primitiveRoutedLocalPairData
    (C : KarlssonOEISBaseSixPairCoordinateCrossingCertificate) :
    PrimitiveRoutedLocalPairData
      karlssonOEISBaseArrangement karlssonBasePairCrossing
      (0 : Fin 4) (1 : Fin 4) (by decide) where
  carrier_crossing :=
    C.localPairCarrierCrossingData (0 : Fin 4) (1 : Fin 4) (by decide)
  spheres_distinct := by
    simpa using karlssonOEISQ0_Q1_spheres_distinct
  rayLines_distinct := by
    simpa using karlssonOEISQ0_Q1_rayLines_distinct
  close_savings_route := by
    intro _hclose
    simpa using karlssonOEISQ0_Q1_circleRayOutward_savings_route
  intriguing_savings_route := by
    intro hintriguing
    exact False.elim (karlssonOEISBase_zero_one_not_circleIntriguing hintriguing)
  close_intriguing_savings_route := by
    intro _hclose hintriguing
    exact False.elim (karlssonOEISBase_zero_one_not_circleIntriguing hintriguing)

/-- For the exceptional OEIS base pair `(Q0,Q1)`, the concrete
circle-ray-outward route and the local finite pair certificate already prove
the sharp `<= 5` crossing bound. -/
theorem KarlssonOEISBaseSixPairCoordinateCrossingCertificate.zero_one_cross_le_five
    (C : KarlssonOEISBaseSixPairCoordinateCrossingCertificate) :
    karlssonBasePairCrossing (0 : Fin 4) (1 : Fin 4) ≤ 5 := by
  have h :=
    localPairCarrierCrossingData_cross_le_of_pairComponentSavings
      (C.localPairCarrierCrossingData (0 : Fin 4) (1 : Fin 4) (by decide))
      karlssonOEISQ0_Q1_circleRayOutward_savings_route.toPairComponentSavings
  exact h

/-- Cardinality form of the concrete `(Q0,Q1)` route: the finite witness set
for the exceptional OEIS base pair has at most five points. -/
theorem KarlssonOEISBaseSixPairCoordinateCrossingCertificate.zero_one_card_le_five
    (C : KarlssonOEISBaseSixPairCoordinateCrossingCertificate) :
    C.pair01.crossingPoints.card ≤ 5 := by
  have h :=
    localPairCarrierCrossingData_lifted_card_le_of_pairComponentSavings
      (C.localPairCarrierCrossingData (0 : Fin 4) (1 : Fin 4) (by decide))
      karlssonOEISQ0_Q1_circleRayOutward_savings_route.toPairComponentSavings
  simpa [KarlssonOEISBaseSixPairCoordinateCrossingCertificate.crossingPoints,
    KarlssonOEISBaseSixPairCoordinateCrossingCertificate.localPairCarrierCrossingData]
    using h

/-- Cardinality form of the same generic `<= 7` bound for the finite
carrier-intersection witnesses in the exact OEIS/Karlsson base certificate. -/
theorem KarlssonOEISBaseCoordinateCrossingCertificate.crossingPoints_card_le_seven
    (C : KarlssonOEISBaseCoordinateCrossingCertificate)
    {i j : Fin 4} (hij : i < j) :
    (C.pairwise_crossings.crossingPoints i j hij).card ≤ 7 := by
  have hcard_rat :
      (((C.pairwise_crossings.crossingPoints i j hij).card : Nat) : Rat) ≤
        (7 : Rat) := by
    rw [C.crossingPoints_card_eq_base hij]
    exact C.cross_le_seven hij
  exact_mod_cast hcard_rat

end ExplicitInputs
end TheoremOneManuscript
end Lollipop

/-!
Proof component 26: `Manuscript.PrimitiveGeometry.OverlapSavings`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Direct savings from component overlap.

The generic component count gives `2 + 2 + 2 + 1 = 7`.  For direct
whole-carrier savings, overlap between components can be exploited without
forcing any one component to be empty.  This file proves the strongest simple
overlap case needed for shared-anchor audits: if one point lies in all four
circle/ray components, the whole carrier intersection has at most four
points under the usual noncoincidence assumptions.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace PrimitiveGeometry

/-- If a component already contains a point `q` outside a finite witness,
then inserting `q` improves the component-cardinality estimate by one. -/
theorem finset_card_add_one_le_of_forall_mem_of_mem_of_not_mem
    {α : Type*} [DecidableEq α] {component : Set α}
    {q : α} {bound : Nat} {S : Finset α}
    (hq_component : q ∈ component)
    (hqS : q ∉ S)
    (hS : ∀ p ∈ S, p ∈ component)
    (hbound :
      ∀ T : Finset α,
        (∀ p ∈ T, p ∈ component) → T.card ≤ bound) :
    S.card + 1 ≤ bound := by
  have hinsert :=
    hbound (insert q S)
      (by
        intro p hp
        rcases Finset.mem_insert.1 hp with rfl | hpS
        · exact hq_component
        · exact hS p hpS)
  simpa [Finset.card_insert_of_notMem hqS] using hinsert

/-- Abstract finite-set overlap saving.  If a point belongs to three of four
components, then deleting it improves three component-cardinality estimates by
one. -/
theorem finset_card_le_of_common_three_components
    {α : Type*} [DecidableEq α] {C₀ C₁ C₂ C₃ : Set α}
    {q : α} {b₀ b₁ b₂ b₃ : Nat} {S : Finset α}
    (hq₀ : q ∈ C₀)
    (hq₁ : q ∈ C₁)
    (hq₂ : q ∈ C₂)
    (hS : ∀ p ∈ S, p ∈ C₀ ∨ p ∈ C₁ ∨ p ∈ C₂ ∨ p ∈ C₃)
    (hbound₀ :
      ∀ T : Finset α, (∀ p ∈ T, p ∈ C₀) → T.card ≤ b₀)
    (hbound₁ :
      ∀ T : Finset α, (∀ p ∈ T, p ∈ C₁) → T.card ≤ b₁)
    (hbound₂ :
      ∀ T : Finset α, (∀ p ∈ T, p ∈ C₂) → T.card ≤ b₂)
    (hbound₃ :
      ∀ T : Finset α, (∀ p ∈ T, p ∈ C₃) → T.card ≤ b₃) :
    S.card ≤ b₀ + b₁ + b₂ + b₃ - 2 := by
  classical
  let S' : Finset α := S.erase q
  let F₀ : Finset α := S'.filter fun p => p ∈ C₀
  let F₁ : Finset α := S'.filter fun p => p ∈ C₁
  let F₂ : Finset α := S'.filter fun p => p ∈ C₂
  let F₃ : Finset α := S'.filter fun p => p ∈ C₃
  let U₀₁ : Finset α := F₀ ∪ F₁
  let U₀₁₂ : Finset α := U₀₁ ∪ F₂
  let Uall : Finset α := U₀₁₂ ∪ F₃
  have hcover : S' ⊆ Uall := by
    intro p hpS'
    have hpS : p ∈ S := (Finset.mem_erase.1 hpS').2
    rcases hS p hpS with hp₀ | hp₁ | hp₂ | hp₃
    · simp [Uall, U₀₁₂, U₀₁, F₀, hpS', hp₀]
    · simp [Uall, U₀₁₂, U₀₁, F₁, hpS', hp₁]
    · simp [Uall, U₀₁₂, F₂, hpS', hp₂]
    · simp [Uall, F₃, hpS', hp₃]
  have hqS' : q ∉ S' := by
    simp [S']
  have hcard₀ : F₀.card + 1 ≤ b₀ :=
    finset_card_add_one_le_of_forall_mem_of_mem_of_not_mem
      (component := C₀) hq₀
      (by
        intro hqF
        exact hqS' ((Finset.mem_filter.1 hqF).1))
      (by
        intro p hp
        exact (Finset.mem_filter.1 hp).2)
      hbound₀
  have hcard₁ : F₁.card + 1 ≤ b₁ :=
    finset_card_add_one_le_of_forall_mem_of_mem_of_not_mem
      (component := C₁) hq₁
      (by
        intro hqF
        exact hqS' ((Finset.mem_filter.1 hqF).1))
      (by
        intro p hp
        exact (Finset.mem_filter.1 hp).2)
      hbound₁
  have hcard₂ : F₂.card + 1 ≤ b₂ :=
    finset_card_add_one_le_of_forall_mem_of_mem_of_not_mem
      (component := C₂) hq₂
      (by
        intro hqF
        exact hqS' ((Finset.mem_filter.1 hqF).1))
      (by
        intro p hp
        exact (Finset.mem_filter.1 hp).2)
      hbound₂
  have hcard₃ : F₃.card ≤ b₃ :=
    hbound₃ F₃ (by
      intro p hp
      exact (Finset.mem_filter.1 hp).2)
  have hSle : S'.card ≤ Uall.card := Finset.card_le_card hcover
  have hUall : Uall.card ≤ U₀₁₂.card + F₃.card :=
    Finset.card_union_le U₀₁₂ F₃
  have hU₀₁₂ : U₀₁₂.card ≤ U₀₁.card + F₂.card :=
    Finset.card_union_le U₀₁ F₂
  have hU₀₁ : U₀₁.card ≤ F₀.card + F₁.card :=
    Finset.card_union_le F₀ F₁
  have hS'le : S'.card ≤ b₀ + b₁ + b₂ + b₃ - 3 := by
    omega
  by_cases hqS : q ∈ S
  · have hcard : S'.card + 1 = S.card := by
      simpa [S'] using Finset.card_erase_add_one hqS
    omega
  · have hcard : S'.card = S.card := by
      simp [S', Finset.erase_eq_of_notMem hqS]
    omega

/-- Abstract finite-set overlap saving from two overlap witnesses.  The first
witness belongs to the first two components and the second witness belongs to
the last two components, improving all four component estimates by one after
deleting the witnesses.  The two witnesses need not be distinct; if they
coincide, this is the weaker form of the all-four-overlap saving. -/
theorem finset_card_le_of_two_double_component_overlaps
    {α : Type*} [DecidableEq α] {C₀ C₁ C₂ C₃ : Set α}
    {q r : α} {b₀ b₁ b₂ b₃ : Nat} {S : Finset α}
    (hq₀ : q ∈ C₀)
    (hq₁ : q ∈ C₁)
    (hr₂ : r ∈ C₂)
    (hr₃ : r ∈ C₃)
    (hS : ∀ p ∈ S, p ∈ C₀ ∨ p ∈ C₁ ∨ p ∈ C₂ ∨ p ∈ C₃)
    (hbound₀ :
      ∀ T : Finset α, (∀ p ∈ T, p ∈ C₀) → T.card ≤ b₀)
    (hbound₁ :
      ∀ T : Finset α, (∀ p ∈ T, p ∈ C₁) → T.card ≤ b₁)
    (hbound₂ :
      ∀ T : Finset α, (∀ p ∈ T, p ∈ C₂) → T.card ≤ b₂)
    (hbound₃ :
      ∀ T : Finset α, (∀ p ∈ T, p ∈ C₃) → T.card ≤ b₃) :
    S.card ≤ b₀ + b₁ + b₂ + b₃ - 2 := by
  classical
  let S₁ : Finset α := S.erase q
  let S' : Finset α := S₁.erase r
  let F₀ : Finset α := S'.filter fun p => p ∈ C₀
  let F₁ : Finset α := S'.filter fun p => p ∈ C₁
  let F₂ : Finset α := S'.filter fun p => p ∈ C₂
  let F₃ : Finset α := S'.filter fun p => p ∈ C₃
  let U₀₁ : Finset α := F₀ ∪ F₁
  let U₀₁₂ : Finset α := U₀₁ ∪ F₂
  let Uall : Finset α := U₀₁₂ ∪ F₃
  have hcover : S' ⊆ Uall := by
    intro p hpS'
    have hpS₁ : p ∈ S₁ := (Finset.mem_erase.1 hpS').2
    have hpS : p ∈ S := (Finset.mem_erase.1 hpS₁).2
    rcases hS p hpS with hp₀ | hp₁ | hp₂ | hp₃
    · simp [Uall, U₀₁₂, U₀₁, F₀, hpS', hp₀]
    · simp [Uall, U₀₁₂, U₀₁, F₁, hpS', hp₁]
    · simp [Uall, U₀₁₂, F₂, hpS', hp₂]
    · simp [Uall, F₃, hpS', hp₃]
  have hqS' : q ∉ S' := by
    intro hqS'
    have hqS₁ : q ∈ S₁ := (Finset.mem_erase.1 hqS').2
    exact (Finset.mem_erase.1 hqS₁).1 rfl
  have hrS' : r ∉ S' := by
    simp [S']
  have hcard₀ : F₀.card + 1 ≤ b₀ :=
    finset_card_add_one_le_of_forall_mem_of_mem_of_not_mem
      (component := C₀) hq₀
      (by
        intro hqF
        exact hqS' ((Finset.mem_filter.1 hqF).1))
      (by
        intro p hp
        exact (Finset.mem_filter.1 hp).2)
      hbound₀
  have hcard₁ : F₁.card + 1 ≤ b₁ :=
    finset_card_add_one_le_of_forall_mem_of_mem_of_not_mem
      (component := C₁) hq₁
      (by
        intro hqF
        exact hqS' ((Finset.mem_filter.1 hqF).1))
      (by
        intro p hp
        exact (Finset.mem_filter.1 hp).2)
      hbound₁
  have hcard₂ : F₂.card + 1 ≤ b₂ :=
    finset_card_add_one_le_of_forall_mem_of_mem_of_not_mem
      (component := C₂) hr₂
      (by
        intro hrF
        exact hrS' ((Finset.mem_filter.1 hrF).1))
      (by
        intro p hp
        exact (Finset.mem_filter.1 hp).2)
      hbound₂
  have hcard₃ : F₃.card + 1 ≤ b₃ :=
    finset_card_add_one_le_of_forall_mem_of_mem_of_not_mem
      (component := C₃) hr₃
      (by
        intro hrF
        exact hrS' ((Finset.mem_filter.1 hrF).1))
      (by
        intro p hp
        exact (Finset.mem_filter.1 hp).2)
      hbound₃
  have hSle : S'.card ≤ Uall.card := Finset.card_le_card hcover
  have hUall : Uall.card ≤ U₀₁₂.card + F₃.card :=
    Finset.card_union_le U₀₁₂ F₃
  have hU₀₁₂ : U₀₁₂.card ≤ U₀₁.card + F₂.card :=
    Finset.card_union_le U₀₁ F₂
  have hU₀₁ : U₀₁.card ≤ F₀.card + F₁.card :=
    Finset.card_union_le F₀ F₁
  have hS'le : S'.card ≤ b₀ + b₁ + b₂ + b₃ - 4 := by
    omega
  have hS₁le : S.card ≤ S₁.card + 1 := by
    by_cases hqS : q ∈ S
    · have hcard : S₁.card + 1 = S.card := by
        simpa [S₁] using Finset.card_erase_add_one hqS
      omega
    · have hcard : S₁.card = S.card := by
        simp [S₁, Finset.erase_eq_of_notMem hqS]
      omega
  have hS'card_step : S₁.card ≤ S'.card + 1 := by
    by_cases hrS₁ : r ∈ S₁
    · have hcard : S'.card + 1 = S₁.card := by
        simpa [S'] using Finset.card_erase_add_one hrS₁
      omega
    · have hcard : S'.card = S₁.card := by
        simp [S', Finset.erase_eq_of_notMem hrS₁]
      omega
  omega

/-- If the four circle/ray components share one common point, the generic
`2,2,2,1` component bounds collapse to a direct whole-carrier `<= 4` bound. -/
theorem finset_card_le_four_of_common_all_components
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    {q : EuclideanR2}
    (hqcc : q ∈ euclideanCircleCircleSet L M)
    (hqcr : q ∈ euclideanCircleRaySet L M)
    (hqrc : q ∈ euclideanRayCircleSet L M)
    (hqrr : q ∈ euclideanRayRaySet L M)
    (S : Finset EuclideanR2)
    (hS : ∀ p ∈ S, p ∈ euclideanPairIntersectionSet L M) :
    S.card ≤ 4 := by
  classical
  let S' : Finset EuclideanR2 := S.erase q
  let cc : Finset EuclideanR2 :=
    S'.filter fun p => p ∈ euclideanCircleCircleSet L M
  let cr : Finset EuclideanR2 :=
    S'.filter fun p => p ∈ euclideanCircleRaySet L M
  let rc : Finset EuclideanR2 :=
    S'.filter fun p => p ∈ euclideanRayCircleSet L M
  let rr : Finset EuclideanR2 :=
    S'.filter fun p => p ∈ euclideanRayRaySet L M
  let u12 : Finset EuclideanR2 := cc ∪ cr
  let u123 : Finset EuclideanR2 := u12 ∪ rc
  let uall : Finset EuclideanR2 := u123 ∪ rr
  have hcover : S' ⊆ uall := by
    intro p hpS'
    have hpS : p ∈ S := (Finset.mem_erase.1 hpS').2
    rcases (mem_euclideanPairIntersectionSet_iff.1 (hS p hpS)) with
      hcc | hcr | hrc | hrr
    · simp [uall, u123, u12, cc, hpS', hcc]
    · simp [uall, u123, u12, cr, hpS', hcr]
    · simp [uall, u123, rc, hpS', hrc]
    · simp [uall, rr, hpS', hrr]
  have hqS' : q ∉ S' := by
    simp [S']
  have hccard : cc.card + 1 ≤ 2 :=
    finset_card_add_one_le_of_forall_mem_of_mem_of_not_mem
      (component := euclideanCircleCircleSet L M) hqcc
      (by
        intro hqcc_filter
        exact hqS' ((Finset.mem_filter.1 hqcc_filter).1))
      (by
        intro p hp
        exact (Finset.mem_filter.1 hp).2)
      (finset_card_le_two_of_forall_mem_euclideanCircleCircleSet hLM)
  have hcrcard : cr.card + 1 ≤ 2 :=
    finset_card_add_one_le_of_forall_mem_of_mem_of_not_mem
      (component := euclideanCircleRaySet L M) hqcr
      (by
        intro hqcr_filter
        exact hqS' ((Finset.mem_filter.1 hqcr_filter).1))
      (by
        intro p hp
        exact (Finset.mem_filter.1 hp).2)
      finset_card_le_two_of_forall_mem_euclideanCircleRaySet
  have hrccard : rc.card + 1 ≤ 2 :=
    finset_card_add_one_le_of_forall_mem_of_mem_of_not_mem
      (component := euclideanRayCircleSet L M) hqrc
      (by
        intro hqrc_filter
        exact hqS' ((Finset.mem_filter.1 hqrc_filter).1))
      (by
        intro p hp
        exact (Finset.mem_filter.1 hp).2)
      finset_card_le_two_of_forall_mem_euclideanRayCircleSet
  have hrrcard : rr.card + 1 ≤ 1 :=
    finset_card_add_one_le_of_forall_mem_of_mem_of_not_mem
      (component := euclideanRayRaySet L M) hqrr
      (by
        intro hqrr_filter
        exact hqS' ((Finset.mem_filter.1 hqrr_filter).1))
      (by
        intro p hp
        exact (Finset.mem_filter.1 hp).2)
      (finset_card_le_one_of_forall_mem_euclideanRayRaySet hline)
  have hSle : S'.card ≤ uall.card := Finset.card_le_card hcover
  have huall : uall.card ≤ u123.card + rr.card :=
    Finset.card_union_le u123 rr
  have hu123 : u123.card ≤ u12.card + rc.card :=
    Finset.card_union_le u12 rc
  have hu12 : u12.card ≤ cc.card + cr.card :=
    Finset.card_union_le cc cr
  have hS'le : S'.card ≤ 3 := by
    omega
  by_cases hqS : q ∈ S
  · have hcard : S'.card + 1 = S.card := by
      simpa [S'] using Finset.card_erase_add_one hqS
    omega
  · have hcard : S'.card = S.card := by
      simp [S', Finset.erase_eq_of_notMem hqS]
    omega

/-- Direct whole-carrier savings from one point common to all four
circle/ray components. -/
def pairCarrierSavingsFourOfCommonAllComponents
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    {q : EuclideanR2}
    (hqcc : q ∈ euclideanCircleCircleSet L M)
    (hqcr : q ∈ euclideanCircleRaySet L M)
    (hqrc : q ∈ euclideanRayCircleSet L M)
    (hqrr : q ∈ euclideanRayRaySet L M) :
    PairCarrierSavings L M 4 where
  carrier_card_le :=
    finset_card_le_four_of_common_all_components
      hLM hline hqcc hqcr hqrc hqrr

/-- A witness that one point lies in at least three of the four circle/ray
components of the carrier intersection. -/
inductive PairComponentTripleOverlap
    (L M : EuclideanLollipop) (q : EuclideanR2) : Prop where
  | withoutCircleCircle
      (hqcr : q ∈ euclideanCircleRaySet L M)
      (hqrc : q ∈ euclideanRayCircleSet L M)
      (hqrr : q ∈ euclideanRayRaySet L M)
  | withoutCircleRay
      (hqcc : q ∈ euclideanCircleCircleSet L M)
      (hqrc : q ∈ euclideanRayCircleSet L M)
      (hqrr : q ∈ euclideanRayRaySet L M)
  | withoutRayCircle
      (hqcc : q ∈ euclideanCircleCircleSet L M)
      (hqcr : q ∈ euclideanCircleRaySet L M)
      (hqrr : q ∈ euclideanRayRaySet L M)
  | withoutRayRay
      (hqcc : q ∈ euclideanCircleCircleSet L M)
      (hqcr : q ∈ euclideanCircleRaySet L M)
      (hqrc : q ∈ euclideanRayCircleSet L M)

/-- For these four product-type components, a single point in any three
components automatically lies in the fourth component too. -/
theorem pairComponentTripleOverlap_all_four
    {L M : EuclideanLollipop} {q : EuclideanR2}
    (H : PairComponentTripleOverlap L M q) :
    q ∈ euclideanCircleCircleSet L M ∧
      q ∈ euclideanCircleRaySet L M ∧
        q ∈ euclideanRayCircleSet L M ∧
          q ∈ euclideanRayRaySet L M := by
  cases H with
  | withoutCircleCircle hqcr hqrc hqrr =>
      exact ⟨⟨hqcr.1, hqrc.2⟩, hqcr, hqrc, hqrr⟩
  | withoutCircleRay hqcc hqrc hqrr =>
      exact ⟨hqcc, ⟨hqcc.1, hqrr.2⟩, hqrc, hqrr⟩
  | withoutRayCircle hqcc hqcr hqrr =>
      exact ⟨hqcc, hqcr, ⟨hqrr.1, hqcc.2⟩, hqrr⟩
  | withoutRayRay hqcc hqcr hqrc =>
      exact ⟨hqcc, hqcr, hqrc, ⟨hqrc.1, hqcr.2⟩⟩

/-- If one point lies in any three of the four circle/ray components, it
actually gives the stronger direct whole-carrier `<= 4` bound. -/
theorem finset_card_le_four_of_triple_component_overlap
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    {q : EuclideanR2}
    (H : PairComponentTripleOverlap L M q)
    (S : Finset EuclideanR2)
    (hS : ∀ p ∈ S, p ∈ euclideanPairIntersectionSet L M) :
    S.card ≤ 4 := by
  rcases pairComponentTripleOverlap_all_four H with
    ⟨hqcc, hqcr, hqrc, hqrr⟩
  exact
    finset_card_le_four_of_common_all_components
      hLM hline hqcc hqcr hqrc hqrr S hS

/-- Direct whole-carrier `<= 4` savings from a point common to any three
circle/ray components. -/
def pairCarrierSavingsFourOfTripleComponentOverlap
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    {q : EuclideanR2}
    (H : PairComponentTripleOverlap L M q) :
    PairCarrierSavings L M 4 where
  carrier_card_le :=
    finset_card_le_four_of_triple_component_overlap hLM hline H

/-- If one point lies in any three of the four circle/ray components, the
generic component bounds collapse to a direct whole-carrier `<= 5` bound. -/
theorem finset_card_le_five_of_triple_component_overlap
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    {q : EuclideanR2}
    (H : PairComponentTripleOverlap L M q)
    (S : Finset EuclideanR2)
    (hS : ∀ p ∈ S, p ∈ euclideanPairIntersectionSet L M) :
    S.card ≤ 5 := by
  have hcover₀ :
      ∀ p ∈ S,
        p ∈ euclideanCircleCircleSet L M ∨
        p ∈ euclideanCircleRaySet L M ∨
        p ∈ euclideanRayCircleSet L M ∨
        p ∈ euclideanRayRaySet L M := by
    intro p hp
    exact mem_euclideanPairIntersectionSet_iff.1 (hS p hp)
  cases H with
  | withoutCircleCircle hqcr hqrc hqrr =>
    have hcover :
        ∀ p ∈ S,
          p ∈ euclideanCircleRaySet L M ∨
          p ∈ euclideanRayCircleSet L M ∨
          p ∈ euclideanRayRaySet L M ∨
          p ∈ euclideanCircleCircleSet L M := by
      intro p hp
      rcases hcover₀ p hp with hcc | hcr | hrc | hrr
      · exact Or.inr (Or.inr (Or.inr hcc))
      · exact Or.inl hcr
      · exact Or.inr (Or.inl hrc)
      · exact Or.inr (Or.inr (Or.inl hrr))
    have h :=
      finset_card_le_of_common_three_components
        (C₀ := euclideanCircleRaySet L M)
        (C₁ := euclideanRayCircleSet L M)
        (C₂ := euclideanRayRaySet L M)
        (C₃ := euclideanCircleCircleSet L M)
        hqcr hqrc hqrr hcover
        finset_card_le_two_of_forall_mem_euclideanCircleRaySet
        finset_card_le_two_of_forall_mem_euclideanRayCircleSet
        (finset_card_le_one_of_forall_mem_euclideanRayRaySet hline)
        (finset_card_le_two_of_forall_mem_euclideanCircleCircleSet hLM)
    norm_num at h
    exact h
  | withoutCircleRay hqcc hqrc hqrr =>
    have hcover :
        ∀ p ∈ S,
          p ∈ euclideanCircleCircleSet L M ∨
          p ∈ euclideanRayCircleSet L M ∨
          p ∈ euclideanRayRaySet L M ∨
          p ∈ euclideanCircleRaySet L M := by
      intro p hp
      rcases hcover₀ p hp with hcc | hcr | hrc | hrr
      · exact Or.inl hcc
      · exact Or.inr (Or.inr (Or.inr hcr))
      · exact Or.inr (Or.inl hrc)
      · exact Or.inr (Or.inr (Or.inl hrr))
    have h :=
      finset_card_le_of_common_three_components
        (C₀ := euclideanCircleCircleSet L M)
        (C₁ := euclideanRayCircleSet L M)
        (C₂ := euclideanRayRaySet L M)
        (C₃ := euclideanCircleRaySet L M)
        hqcc hqrc hqrr hcover
        (finset_card_le_two_of_forall_mem_euclideanCircleCircleSet hLM)
        finset_card_le_two_of_forall_mem_euclideanRayCircleSet
        (finset_card_le_one_of_forall_mem_euclideanRayRaySet hline)
        finset_card_le_two_of_forall_mem_euclideanCircleRaySet
    norm_num at h
    exact h
  | withoutRayCircle hqcc hqcr hqrr =>
    have hcover :
        ∀ p ∈ S,
          p ∈ euclideanCircleCircleSet L M ∨
          p ∈ euclideanCircleRaySet L M ∨
          p ∈ euclideanRayRaySet L M ∨
          p ∈ euclideanRayCircleSet L M := by
      intro p hp
      rcases hcover₀ p hp with hcc | hcr | hrc | hrr
      · exact Or.inl hcc
      · exact Or.inr (Or.inl hcr)
      · exact Or.inr (Or.inr (Or.inr hrc))
      · exact Or.inr (Or.inr (Or.inl hrr))
    have h :=
      finset_card_le_of_common_three_components
        (C₀ := euclideanCircleCircleSet L M)
        (C₁ := euclideanCircleRaySet L M)
        (C₂ := euclideanRayRaySet L M)
        (C₃ := euclideanRayCircleSet L M)
        hqcc hqcr hqrr hcover
        (finset_card_le_two_of_forall_mem_euclideanCircleCircleSet hLM)
        finset_card_le_two_of_forall_mem_euclideanCircleRaySet
        (finset_card_le_one_of_forall_mem_euclideanRayRaySet hline)
        finset_card_le_two_of_forall_mem_euclideanRayCircleSet
    norm_num at h
    exact h
  | withoutRayRay hqcc hqcr hqrc =>
    have hcover :
        ∀ p ∈ S,
          p ∈ euclideanCircleCircleSet L M ∨
          p ∈ euclideanCircleRaySet L M ∨
          p ∈ euclideanRayCircleSet L M ∨
          p ∈ euclideanRayRaySet L M := by
      exact hcover₀
    have h :=
      finset_card_le_of_common_three_components
        (C₀ := euclideanCircleCircleSet L M)
        (C₁ := euclideanCircleRaySet L M)
        (C₂ := euclideanRayCircleSet L M)
        (C₃ := euclideanRayRaySet L M)
        hqcc hqcr hqrc hcover
        (finset_card_le_two_of_forall_mem_euclideanCircleCircleSet hLM)
        finset_card_le_two_of_forall_mem_euclideanCircleRaySet
        finset_card_le_two_of_forall_mem_euclideanRayCircleSet
        (finset_card_le_one_of_forall_mem_euclideanRayRaySet hline)
    norm_num at h
    exact h

/-- Direct whole-carrier savings from a point common to any three circle/ray
components. -/
def pairCarrierSavingsFiveOfTripleComponentOverlap
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    {q : EuclideanR2}
    (H : PairComponentTripleOverlap L M q) :
    PairCarrierSavings L M 5 where
  carrier_card_le :=
    finset_card_le_five_of_triple_component_overlap hLM hline H

/-- Two overlap witnesses that together improve all four component estimates.
The witnesses may coincide. -/
inductive PairComponentTwoDoubleOverlap
    (L M : EuclideanLollipop) (q r : EuclideanR2) : Prop where
  | circleCircle_circleRay__rayCircle_rayRay
      (hqcc : q ∈ euclideanCircleCircleSet L M)
      (hqcr : q ∈ euclideanCircleRaySet L M)
      (hrrc : r ∈ euclideanRayCircleSet L M)
      (hrrr : r ∈ euclideanRayRaySet L M)
  | circleCircle_rayCircle__circleRay_rayRay
      (hqcc : q ∈ euclideanCircleCircleSet L M)
      (hqrc : q ∈ euclideanRayCircleSet L M)
      (hrcr : r ∈ euclideanCircleRaySet L M)
      (hrrr : r ∈ euclideanRayRaySet L M)
  | circleCircle_rayRay__circleRay_rayCircle
      (hqcc : q ∈ euclideanCircleCircleSet L M)
      (hqrr : q ∈ euclideanRayRaySet L M)
      (hrcr : r ∈ euclideanCircleRaySet L M)
      (hrrc : r ∈ euclideanRayCircleSet L M)

/-- If the two witnesses in a two-double overlap coincide, the data actually
give a point lying in all four circle/ray components. -/
theorem pairComponentTwoDoubleOverlap_all_four_of_same_point
    {L M : EuclideanLollipop} {q : EuclideanR2}
    (H : PairComponentTwoDoubleOverlap L M q q) :
    q ∈ euclideanCircleCircleSet L M ∧
      q ∈ euclideanCircleRaySet L M ∧
        q ∈ euclideanRayCircleSet L M ∧
          q ∈ euclideanRayRaySet L M := by
  cases H with
  | circleCircle_circleRay__rayCircle_rayRay hqcc hqcr hqrc hqrr =>
      exact ⟨hqcc, hqcr, hqrc, hqrr⟩
  | circleCircle_rayCircle__circleRay_rayRay hqcc hqrc hqcr hqrr =>
      exact ⟨hqcc, hqcr, hqrc, hqrr⟩
  | circleCircle_rayRay__circleRay_rayCircle hqcc hqrr hqcr hqrc =>
      exact ⟨hqcc, hqcr, hqrc, hqrr⟩

/-- Coincident two-double overlap witnesses give the stronger direct
whole-carrier `<= 4` bound. -/
theorem finset_card_le_four_of_two_double_component_overlap_same_point
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    {q : EuclideanR2}
    (H : PairComponentTwoDoubleOverlap L M q q)
    (S : Finset EuclideanR2)
    (hS : ∀ p ∈ S, p ∈ euclideanPairIntersectionSet L M) :
    S.card ≤ 4 := by
  rcases pairComponentTwoDoubleOverlap_all_four_of_same_point H with
    ⟨hqcc, hqcr, hqrc, hqrr⟩
  exact
    finset_card_le_four_of_common_all_components
      hLM hline hqcc hqcr hqrc hqrr S hS

/-- Direct whole-carrier `<= 4` savings from coincident two-double overlap
witnesses. -/
def pairCarrierSavingsFourOfTwoDoubleComponentOverlapSamePoint
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    {q : EuclideanR2}
    (H : PairComponentTwoDoubleOverlap L M q q) :
    PairCarrierSavings L M 4 where
  carrier_card_le :=
    finset_card_le_four_of_two_double_component_overlap_same_point
      hLM hline H

/-- If two overlap witnesses together improve all four circle/ray component
estimates, the whole carrier intersection has at most five points. -/
theorem finset_card_le_five_of_two_double_component_overlap
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    {q r : EuclideanR2}
    (H : PairComponentTwoDoubleOverlap L M q r)
    (S : Finset EuclideanR2)
    (hS : ∀ p ∈ S, p ∈ euclideanPairIntersectionSet L M) :
    S.card ≤ 5 := by
  have hcover₀ :
      ∀ p ∈ S,
        p ∈ euclideanCircleCircleSet L M ∨
        p ∈ euclideanCircleRaySet L M ∨
        p ∈ euclideanRayCircleSet L M ∨
        p ∈ euclideanRayRaySet L M := by
    intro p hp
    exact mem_euclideanPairIntersectionSet_iff.1 (hS p hp)
  cases H with
  | circleCircle_circleRay__rayCircle_rayRay hqcc hqcr hrrc hrrr =>
    have h :=
      finset_card_le_of_two_double_component_overlaps
        (C₀ := euclideanCircleCircleSet L M)
        (C₁ := euclideanCircleRaySet L M)
        (C₂ := euclideanRayCircleSet L M)
        (C₃ := euclideanRayRaySet L M)
        hqcc hqcr hrrc hrrr hcover₀
        (finset_card_le_two_of_forall_mem_euclideanCircleCircleSet hLM)
        finset_card_le_two_of_forall_mem_euclideanCircleRaySet
        finset_card_le_two_of_forall_mem_euclideanRayCircleSet
        (finset_card_le_one_of_forall_mem_euclideanRayRaySet hline)
    norm_num at h
    exact h
  | circleCircle_rayCircle__circleRay_rayRay hqcc hqrc hrcr hrrr =>
    have hcover :
        ∀ p ∈ S,
          p ∈ euclideanCircleCircleSet L M ∨
          p ∈ euclideanRayCircleSet L M ∨
          p ∈ euclideanCircleRaySet L M ∨
          p ∈ euclideanRayRaySet L M := by
      intro p hp
      rcases hcover₀ p hp with hcc | hcr | hrc | hrr
      · exact Or.inl hcc
      · exact Or.inr (Or.inr (Or.inl hcr))
      · exact Or.inr (Or.inl hrc)
      · exact Or.inr (Or.inr (Or.inr hrr))
    have h :=
      finset_card_le_of_two_double_component_overlaps
        (C₀ := euclideanCircleCircleSet L M)
        (C₁ := euclideanRayCircleSet L M)
        (C₂ := euclideanCircleRaySet L M)
        (C₃ := euclideanRayRaySet L M)
        hqcc hqrc hrcr hrrr hcover
        (finset_card_le_two_of_forall_mem_euclideanCircleCircleSet hLM)
        finset_card_le_two_of_forall_mem_euclideanRayCircleSet
        finset_card_le_two_of_forall_mem_euclideanCircleRaySet
        (finset_card_le_one_of_forall_mem_euclideanRayRaySet hline)
    norm_num at h
    exact h
  | circleCircle_rayRay__circleRay_rayCircle hqcc hqrr hrcr hrrc =>
    have hcover :
        ∀ p ∈ S,
          p ∈ euclideanCircleCircleSet L M ∨
          p ∈ euclideanRayRaySet L M ∨
          p ∈ euclideanCircleRaySet L M ∨
          p ∈ euclideanRayCircleSet L M := by
      intro p hp
      rcases hcover₀ p hp with hcc | hcr | hrc | hrr
      · exact Or.inl hcc
      · exact Or.inr (Or.inr (Or.inl hcr))
      · exact Or.inr (Or.inr (Or.inr hrc))
      · exact Or.inr (Or.inl hrr)
    have h :=
      finset_card_le_of_two_double_component_overlaps
        (C₀ := euclideanCircleCircleSet L M)
        (C₁ := euclideanRayRaySet L M)
        (C₂ := euclideanCircleRaySet L M)
        (C₃ := euclideanRayCircleSet L M)
        hqcc hqrr hrcr hrrc hcover
        (finset_card_le_two_of_forall_mem_euclideanCircleCircleSet hLM)
        (finset_card_le_one_of_forall_mem_euclideanRayRaySet hline)
        finset_card_le_two_of_forall_mem_euclideanCircleRaySet
        finset_card_le_two_of_forall_mem_euclideanRayCircleSet
    norm_num at h
    exact h

/-- Direct whole-carrier savings from two overlap witnesses that together
improve all four component estimates. -/
def pairCarrierSavingsFiveOfTwoDoubleComponentOverlap
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    {q r : EuclideanR2}
    (H : PairComponentTwoDoubleOverlap L M q r) :
    PairCarrierSavings L M 5 where
  carrier_card_le :=
    finset_card_le_five_of_two_double_component_overlap hLM hline H

end PrimitiveGeometry
end TheoremOneManuscript
end Lollipop

/-!
Proof component 27: `Manuscript.PrimitiveGeometry.CloseRouteAudit`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Audit examples for the close-pair route boundary.

The close-pair route theorem cannot be discharged merely by proving that one
of the two mixed circle-ray components is always empty.  This file gives a
small exact radial, normalized-bearing, cyclic-close pair where both mixed
components are nonempty.  The example is not a counterexample to the
`<= 5` close-pair bound; it only rules out an overly strong intermediate
claim.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace PrimitiveGeometry

open TheoremOneEndToEnd

/-- Unit lollipop anchored at `(1,0)` and pointing right. -/
noncomputable def closeRouteAuditRight : EuclideanLollipop :=
  EuclideanLollipop.fromAnchor
    (point2 1 0) 1 0 0
    (by norm_num) (by norm_num) (by norm_num)

/-- Unit lollipop with the same anchor and pointing down. -/
noncomputable def closeRouteAuditDown : EuclideanLollipop :=
  EuclideanLollipop.fromAnchor
    (point2 1 0) 1 (-(Real.pi / 2)) (3 / 4)
    (by norm_num) (by norm_num) (by norm_num)

theorem closeRouteAuditRight_isRadialOutward :
    closeRouteAuditRight.IsRadialOutward := by
  simpa [closeRouteAuditRight] using
    EuclideanLollipop.fromAnchor_isRadialOutward
      (point2 1 0) 1 0 0
      (by norm_num) (by norm_num) (by norm_num)

theorem closeRouteAuditDown_isRadialOutward :
    closeRouteAuditDown.IsRadialOutward := by
  simpa [closeRouteAuditDown] using
    EuclideanLollipop.fromAnchor_isRadialOutward
      (point2 1 0) 1 (-(Real.pi / 2)) (3 / 4)
      (by norm_num) (by norm_num) (by norm_num)

theorem closeRouteAuditRight_hasNormalizedBearing :
    closeRouteAuditRight.HasNormalizedBearing := by
  unfold closeRouteAuditRight
  exact EuclideanLollipop.fromAnchor_hasNormalizedBearing (by ring)

theorem closeRouteAuditDown_hasNormalizedBearing :
    closeRouteAuditDown.HasNormalizedBearing := by
  unfold closeRouteAuditDown
  exact EuclideanLollipop.fromAnchor_hasNormalizedBearing_of_eq_sub_two_pi
    (by ring)

theorem closeRouteAudit_cyclicClosePair :
    CloseDirection.cyclicClosePair
      closeRouteAuditRight.normalizedDirection
      closeRouteAuditDown.normalizedDirection := by
  unfold closeRouteAuditRight closeRouteAuditDown
  simp [EuclideanLollipop.fromAnchor, CloseDirection.cyclicClosePair]
  right
  norm_num

/-- The shared anchor belongs to both mixed components. -/
theorem closeRouteAudit_mixed_components_nonempty :
    ∃ p : EuclideanR2,
      p ∈ euclideanCircleRaySet closeRouteAuditRight closeRouteAuditDown ∧
      p ∈ euclideanRayCircleSet closeRouteAuditRight closeRouteAuditDown := by
  refine ⟨toEuclideanR2 (point2 1 0), ?_, ?_⟩
  · exact
      mem_euclideanCircleRaySet_of_mem_circleSet_of_mem_raySet
        (L := closeRouteAuditRight) (M := closeRouteAuditDown)
        (p := point2 1 0)
        (by
          simpa [closeRouteAuditRight, EuclideanLollipop.fromAnchor] using
            closeRouteAuditRight.anchor_on_circle)
        (by
          simpa [closeRouteAuditDown, EuclideanLollipop.fromAnchor] using
            anchor_mem_raySet (point2 1 0)
              closeRouteAuditDown.rayDirection)
  · exact
      mem_euclideanRayCircleSet_of_mem_raySet_of_mem_circleSet
        (L := closeRouteAuditRight) (M := closeRouteAuditDown)
        (p := point2 1 0)
        (by
          simpa [closeRouteAuditRight, EuclideanLollipop.fromAnchor] using
            anchor_mem_raySet (point2 1 0)
              closeRouteAuditRight.rayDirection)
        (by
          simpa [closeRouteAuditDown, EuclideanLollipop.fromAnchor] using
            closeRouteAuditDown.anchor_on_circle)

theorem closeRouteAudit_circleRay_not_empty :
    ¬ (∀ p : EuclideanR2,
      p ∉ euclideanCircleRaySet closeRouteAuditRight closeRouteAuditDown) := by
  intro hempty
  rcases closeRouteAudit_mixed_components_nonempty with ⟨p, hp, _⟩
  exact hempty p hp

theorem closeRouteAudit_rayCircle_not_empty :
    ¬ (∀ p : EuclideanR2,
      p ∉ euclideanRayCircleSet closeRouteAuditRight closeRouteAuditDown) := by
  intro hempty
  rcases closeRouteAudit_mixed_components_nonempty with ⟨p, _, hp⟩
  exact hempty p hp

theorem closeRouteAudit_spheres_distinct :
    euclideanSphere closeRouteAuditRight.center closeRouteAuditRight.radius ≠
      euclideanSphere closeRouteAuditDown.center closeRouteAuditDown.radius := by
  apply euclideanSphere_ne_of_center_ne
  intro hcenter
  have hx := congr_fun hcenter 0
  simp [closeRouteAuditRight, closeRouteAuditDown,
    EuclideanLollipop.fromAnchor, angleDirection, point2,
    Real.cos_neg, Real.cos_pi_div_two] at hx

theorem closeRouteAudit_rayLines_distinct :
    euclideanRayLine closeRouteAuditRight ≠
      euclideanRayLine closeRouteAuditDown := by
  apply euclideanRayLine_ne_of_det2_rayDirection_ne_zero
  have hdet :
      det2 closeRouteAuditRight.rayDirection
        closeRouteAuditDown.rayDirection = -1 := by
    simp [closeRouteAuditRight, closeRouteAuditDown,
      EuclideanLollipop.fromAnchor, angleDirection, det2, point2,
      Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
  rw [hdet]
  norm_num

theorem closeRouteAudit_common_all_components :
    ∃ p : EuclideanR2,
      p ∈ euclideanCircleCircleSet closeRouteAuditRight closeRouteAuditDown ∧
      p ∈ euclideanCircleRaySet closeRouteAuditRight closeRouteAuditDown ∧
      p ∈ euclideanRayCircleSet closeRouteAuditRight closeRouteAuditDown ∧
      p ∈ euclideanRayRaySet closeRouteAuditRight closeRouteAuditDown := by
  refine ⟨toEuclideanR2 (point2 1 0), ?_, ?_, ?_, ?_⟩
  · exact
      mem_euclideanCircleCircleSet_of_mem_circleSets
        (L := closeRouteAuditRight) (M := closeRouteAuditDown)
        (p := point2 1 0)
        (by
          simpa [closeRouteAuditRight, EuclideanLollipop.fromAnchor] using
            closeRouteAuditRight.anchor_on_circle)
        (by
          simpa [closeRouteAuditDown, EuclideanLollipop.fromAnchor] using
            closeRouteAuditDown.anchor_on_circle)
  · exact
      mem_euclideanCircleRaySet_of_mem_circleSet_of_mem_raySet
        (L := closeRouteAuditRight) (M := closeRouteAuditDown)
        (p := point2 1 0)
        (by
          simpa [closeRouteAuditRight, EuclideanLollipop.fromAnchor] using
            closeRouteAuditRight.anchor_on_circle)
        (by
          simpa [closeRouteAuditDown, EuclideanLollipop.fromAnchor] using
            anchor_mem_raySet (point2 1 0)
              closeRouteAuditDown.rayDirection)
  · exact
      mem_euclideanRayCircleSet_of_mem_raySet_of_mem_circleSet
        (L := closeRouteAuditRight) (M := closeRouteAuditDown)
        (p := point2 1 0)
        (by
          simpa [closeRouteAuditRight, EuclideanLollipop.fromAnchor] using
            anchor_mem_raySet (point2 1 0)
              closeRouteAuditRight.rayDirection)
        (by
          simpa [closeRouteAuditDown, EuclideanLollipop.fromAnchor] using
            closeRouteAuditDown.anchor_on_circle)
  · exact
      mem_euclideanRayRaySet_of_mem_raySets
        (L := closeRouteAuditRight) (M := closeRouteAuditDown)
        (p := point2 1 0)
        (by
          simpa [closeRouteAuditRight, EuclideanLollipop.fromAnchor] using
            anchor_mem_raySet (point2 1 0)
              closeRouteAuditRight.rayDirection)
        (by
          simpa [closeRouteAuditDown, EuclideanLollipop.fromAnchor] using
            anchor_mem_raySet (point2 1 0)
              closeRouteAuditDown.rayDirection)

theorem closeRouteAudit_direct_savings_four :
    PairCarrierSavings closeRouteAuditRight closeRouteAuditDown 4 := by
  rcases closeRouteAudit_common_all_components with
    ⟨p, hcc, hcr, hrc, hrr⟩
  exact
    pairCarrierSavingsFourOfCommonAllComponents
      closeRouteAudit_spheres_distinct
      closeRouteAudit_rayLines_distinct
      (q := p) hcc hcr hrc hrr

theorem closeRouteAudit_carrier_card_le_four
    (S : Finset EuclideanR2)
    (hS : ∀ p ∈ S,
      p ∈ euclideanPairIntersectionSet
        closeRouteAuditRight closeRouteAuditDown) :
    S.card ≤ 4 :=
  closeRouteAudit_direct_savings_four.carrier_card_le S hS

end PrimitiveGeometry
end TheoremOneManuscript
end Lollipop

/-!
Proof component 28: `Manuscript.FormalizedProof.ManuscriptLemmas`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Named Lean endpoints for the manuscript lemmas used in Theorem 1.

The statements here are wrappers around the detailed formalization.  They make
the proof DAG visible at manuscript scale: region equation, forced close and
intriguing pairs, generic carrier-component counting, component savings,
colored Turan, and the Section 5 matrix theorem.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace FormalizedProof

universe u

open TheoremOneEndToEnd

/-- The incremental insertion argument proves the usual
`regions = crossings + n + 1` formula when crossings are counted by previous
pairs. -/
theorem region_equation_from_ordered_increment
    {n : Nat} {target : Rat} {cross : Fin n → Fin n → Rat}
    (D : OrderedIncrementalPairRegionData n target cross) :
    target = pairSum n cross + (n : Rat) + 1 :=
  D.target_eq_pairSum_add

/-- Local per-insertion region-step certificates assemble into the ordered
region recurrence used by the theorem stack. -/
def ordered_increment_from_stepwise_region_steps
    {n : Nat} {target : Rat} {cross : Fin n → Fin n → Rat}
    (D : StepwiseOrderedIncrementalPairRegionData n target cross) :
    OrderedIncrementalPairRegionData n target cross :=
  D.toOrderedIncrementalPairRegionData

/-- The stepwise region-increment form also proves
`regions = crossings + n + 1`. -/
theorem region_equation_from_stepwise_ordered_increment
    {n : Nat} {target : Rat} {cross : Fin n → Fin n → Rat}
    (D : StepwiseOrderedIncrementalPairRegionData n target cross) :
    target = pairSum n cross + (n : Rat) + 1 :=
  D.target_eq_pairSum_add

/-- Karlsson's four-base crossing table has visible inter-base entries
`5, 7, 7, 7, 7, 7`, whose sum is `40`. -/
theorem karlsson_base_six_pair_table_sum :
    ExplicitInputs.karlssonBasePairCrossing (0 : Fin 4) (1 : Fin 4) +
      ExplicitInputs.karlssonBasePairCrossing (0 : Fin 4) (2 : Fin 4) +
      ExplicitInputs.karlssonBasePairCrossing (0 : Fin 4) (3 : Fin 4) +
      ExplicitInputs.karlssonBasePairCrossing (1 : Fin 4) (2 : Fin 4) +
      ExplicitInputs.karlssonBasePairCrossing (1 : Fin 4) (3 : Fin 4) +
      ExplicitInputs.karlssonBasePairCrossing (2 : Fin 4) (3 : Fin 4) = 40 :=
  ExplicitInputs.karlssonBasePairCrossing_six_pair_sum_eq_forty

/-- The same four-base table, summed over `pairFinset 4`, has crossing total
`40`. -/
theorem karlsson_base_pairFinset_table_sum :
    pairSum 4 ExplicitInputs.karlssonBasePairCrossing = 40 :=
  ExplicitInputs.pairSum_four_karlssonBasePairCrossing_eq_forty

/-- A six-entry symmetric base table certificate expands to the universal
distinct-label Karlsson base table agreement. -/
theorem karlsson_base_table_agreement_from_six_pairs
    {baseCross : Fin 4 → Fin 4 → Rat}
    (C : ExplicitInputs.KarlssonBaseSixPairTableCertificate baseCross) :
    ∀ a b : Fin 4, a ≠ b →
      baseCross a b = ExplicitInputs.karlssonBasePairCrossing a b :=
  C.base_pair_cross_eq_karlsson

/-- The displayed Karlsson base table itself is certified by its six unordered
inter-base entries plus symmetry. -/
def karlsson_base_six_pair_table_certificate :
    ExplicitInputs.KarlssonBaseSixPairTableCertificate
      ExplicitInputs.karlssonBasePairCrossing :=
  ExplicitInputs.karlssonBasePairCrossing_sixPairTableCertificate

/-- The exact four-coordinate OEIS/Karlsson base arrangement recorded in
Lean. -/
noncomputable def karlsson_oeis_base_coordinate_arrangement :
    PrimitiveGeometry.EuclideanLollipopArrangement 4 :=
  ExplicitInputs.karlssonOEISBaseArrangement

/-- Exact OEIS base fact: every stem in the four-coordinate base arrangement is
radial outward. -/
theorem karlsson_oeis_base_radial_outward
    (i : Fin 4) :
    (ExplicitInputs.karlssonOEISBaseArrangement.lollipop i).IsRadialOutward :=
  ExplicitInputs.karlssonOEISBaseArrangement_isRadialOutward i

/-- Exact OEIS base fact: the exceptional base pair `(Q0,Q1)` is close in
the canonical cyclic normalized-direction relation. -/
theorem karlsson_oeis_base_zero_one_close :
    TheoremOneEndToEnd.CloseDirection.cyclicClose
      (fun i : Fin 4 =>
        ExplicitInputs.karlssonOEISBaseArrangement.normalizedDirection i)
      (0 : Fin 4) (1 : Fin 4) :=
  ExplicitInputs.karlssonOEISBase_zero_one_cyclicClose

/-- Exact OEIS base fact: the exceptional base pair `(Q0,Q1)` satisfies
Paulsen's strict obtuse-intersection distance condition. -/
theorem karlsson_oeis_base_zero_one_circle_obtuse :
    TheoremOneEndToEnd.PaulsenLinearAlgebra.circleObtuseCondition
      ExplicitInputs.karlssonOEISQ0.radius
      ExplicitInputs.karlssonOEISQ1.radius
      ExplicitInputs.karlssonOEISQ0.center
      ExplicitInputs.karlssonOEISQ1.center :=
  ExplicitInputs.karlssonOEISQ0_Q1_circleObtuseCondition

/-- Exact OEIS base fact: the exceptional base pair `(Q0,Q1)` is not
intriguing for the canonical Paulsen circle relation. -/
theorem karlsson_oeis_base_zero_one_not_intriguing :
    ¬ TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
      (fun i : Fin 4 => ExplicitInputs.karlssonOEISBaseArrangement.center i)
      (fun i : Fin 4 => ExplicitInputs.karlssonOEISBaseArrangement.radius i)
      (0 : Fin 4) (1 : Fin 4) :=
  ExplicitInputs.karlssonOEISBase_zero_one_not_circleIntriguing

/-- Exact OEIS base fact: the `Q1` ray anchor is outside the `Q0` circle. -/
theorem karlsson_oeis_base_zero_one_circleRay_anchor_outside :
    ExplicitInputs.karlssonOEISQ0.radius ^ 2 <
      TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
        ExplicitInputs.karlssonOEISQ1.anchor
        ExplicitInputs.karlssonOEISQ0.center :=
  ExplicitInputs.karlssonOEISQ0_Q1_circleRay_anchor_distSq_gt_radius_sq

/-- Exact OEIS base fact: the `Q1` ray points weakly away from the `Q0`
center. -/
theorem karlsson_oeis_base_zero_one_circleRay_dot_nonneg :
    0 ≤
      TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2
        (ExplicitInputs.karlssonOEISQ1.anchor -
          ExplicitInputs.karlssonOEISQ0.center)
        ExplicitInputs.karlssonOEISQ1.rayDirection :=
  ExplicitInputs.karlssonOEISQ0_Q1_circleRay_anchor_dot_nonneg

/-- Exact OEIS base fact: the `circle(Q0) ∩ ray(Q1)` component is empty. -/
theorem karlsson_oeis_base_zero_one_circleRay_empty :
    ∀ p : PrimitiveGeometry.EuclideanR2,
      p ∉ PrimitiveGeometry.euclideanCircleRaySet
        ExplicitInputs.karlssonOEISQ0 ExplicitInputs.karlssonOEISQ1 :=
  ExplicitInputs.karlssonOEISQ0_Q1_circleRaySet_empty

/-- Exact OEIS base fact: the exceptional pair `(Q0,Q1)` has a named
circle-ray-outward route proving the `<= 5` component-savings branch. -/
noncomputable def karlsson_oeis_base_zero_one_close_savings_route :
    PrimitiveGeometry.PairComponentSavingsFiveRoute
      ExplicitInputs.karlssonOEISQ0 ExplicitInputs.karlssonOEISQ1 :=
  ExplicitInputs.karlssonOEISQ0_Q1_circleRayOutward_savings_route

/-- The named `(Q0,Q1)` route converts to the component-savings certificate
used by the crossing-count theorem. -/
noncomputable def karlsson_oeis_base_zero_one_close_component_savings :
    PrimitiveGeometry.PairComponentSavings
      ExplicitInputs.karlssonOEISQ0 ExplicitInputs.karlssonOEISQ1 5 :=
  karlsson_oeis_base_zero_one_close_savings_route.toPairComponentSavings

/-- The OEIS/Karlsson base table has checked ordered insertion arithmetic:
the certified table gives `45 = 40 + 4 + 1`. -/
theorem karlsson_oeis_base_ordered_region_arithmetic :
    (45 : Rat) =
      pairSum 4 ExplicitInputs.karlssonBasePairCrossing + (4 : Rat) + 1 :=
  ExplicitInputs.karlssonOEISBaseOrderedRegionData_target

/-- The OEIS/Karlsson base table also has local per-insertion certificates for
the four ordered region steps `1 -> 2 -> 8 -> 23 -> 45`. -/
def karlsson_oeis_base_stepwise_ordered_region_data :
    StepwiseOrderedIncrementalPairRegionData 4 45
      ExplicitInputs.karlssonBasePairCrossing :=
  ExplicitInputs.karlssonOEISBaseStepwiseOrderedRegionData

/-- The stepwise local insertion certificates for the OEIS/Karlsson base table
give the same `45 = 40 + 4 + 1` arithmetic. -/
theorem karlsson_oeis_base_stepwise_ordered_region_arithmetic :
    (45 : Rat) =
      pairSum 4 ExplicitInputs.karlssonBasePairCrossing + (4 : Rat) + 1 :=
  ExplicitInputs.karlssonOEISBaseStepwiseOrderedRegionData_target

/-- The first-principles base-coordinate certificate is the finite
carrier-intersection proof for the exact OEIS four-lollipop arrangement. -/
abbrev KarlssonOEISBaseCoordinateCrossingCertificate : Type :=
  ExplicitInputs.KarlssonOEISBaseCoordinateCrossingCertificate

/-- Modular six-pair form of the exact OEIS/Karlsson base-coordinate
certificate. -/
abbrev KarlssonOEISBaseSixPairCoordinateCrossingCertificate : Type :=
  ExplicitInputs.KarlssonOEISBaseSixPairCoordinateCrossingCertificate

/-- Six independent exact OEIS/Karlsson pair certificates assemble into the
original all-pairs base-coordinate crossing certificate. -/
noncomputable def karlsson_oeis_base_coordinate_certificate_from_six_pairs
    (C : KarlssonOEISBaseSixPairCoordinateCrossingCertificate) :
    KarlssonOEISBaseCoordinateCrossingCertificate :=
  C.toCoordinateCrossingCertificate

/-- The six-pair exact OEIS/Karlsson certificate supplies a generic local
carrier-intersection certificate for any base pair `i < j`. -/
noncomputable def karlsson_oeis_base_local_pair_certificate
    (C : KarlssonOEISBaseSixPairCoordinateCrossingCertificate)
    (i j : Fin 4) (hij : i < j) :
    PrimitiveGeometry.LocalPairCarrierCrossingData
      ExplicitInputs.karlssonOEISBaseArrangement
      ExplicitInputs.karlssonBasePairCrossing i j hij :=
  C.localPairCarrierCrossingData i j hij

/-- The six-pair OEIS/Karlsson certificate route implies the bundled displayed
cardinalities after Lean assembles it into the all-pairs certificate. -/
theorem karlsson_oeis_base_six_pair_certificate_cardinalities
    (C : KarlssonOEISBaseSixPairCoordinateCrossingCertificate) :
    C.toCoordinateCrossingCertificate.SixPairCardinalities :=
  C.six_pair_cardinalities

/-- The six-pair OEIS/Karlsson certificate route also implies the generic
`<= 7` bound for every exact base pair. -/
theorem karlsson_oeis_base_six_pair_certificate_cross_le_seven
    (C : KarlssonOEISBaseSixPairCoordinateCrossingCertificate)
    {i j : Fin 4} (hij : i < j) :
    ExplicitInputs.karlssonBasePairCrossing i j ≤ 7 :=
  C.cross_le_seven hij

/-- The six-pair exact OEIS/Karlsson certificate supplies a full primitive
routed local pair-data object for the exceptional `(Q0,Q1)` pair. -/
noncomputable def karlsson_oeis_base_zero_one_primitive_routed_local_pair_data
    (C : KarlssonOEISBaseSixPairCoordinateCrossingCertificate) :
    PrimitiveGeometry.PrimitiveRoutedLocalPairData
      ExplicitInputs.karlssonOEISBaseArrangement
      ExplicitInputs.karlssonBasePairCrossing
      (0 : Fin 4) (1 : Fin 4) (by decide) :=
  C.zero_one_primitiveRoutedLocalPairData

/-- For the exceptional OEIS base pair `(Q0,Q1)`, the concrete
circle-ray-outward route and the local finite pair certificate imply the sharp
`<= 5` crossing bound. -/
theorem karlsson_oeis_base_six_pair_zero_one_cross_le_five
    (C : KarlssonOEISBaseSixPairCoordinateCrossingCertificate) :
    ExplicitInputs.karlssonBasePairCrossing (0 : Fin 4) (1 : Fin 4) ≤ 5 :=
  C.zero_one_cross_le_five

/-- Cardinality form of the concrete `(Q0,Q1)` OEIS route: the local finite
pair witness has at most five points. -/
theorem karlsson_oeis_base_six_pair_zero_one_card_le_five
    (C : KarlssonOEISBaseSixPairCoordinateCrossingCertificate) :
    C.pair01.crossingPoints.card ≤ 5 :=
  C.zero_one_card_le_five

/-- Unwrapped form of the exact OEIS/Karlsson base-coordinate certificate:
the six finite carrier-intersection sets have cardinalities
`5, 7, 7, 7, 7, 7`. -/
theorem karlsson_oeis_base_coordinate_six_pair_cardinalities
    (C : KarlssonOEISBaseCoordinateCrossingCertificate) :
    C.SixPairCardinalities :=
  ExplicitInputs.KarlssonOEISBaseCoordinateCrossingCertificate.six_pair_cardinalities C

/-- Nonzero determinant of primitive ray directions proves that their lifted
supporting lines are distinct. -/
theorem ray_lines_distinct_from_direction_det_ne_zero
    {L M : PrimitiveGeometry.EuclideanLollipop}
    (hdet : PrimitiveGeometry.det2 L.rayDirection M.rayDirection ≠ 0) :
    PrimitiveGeometry.euclideanRayLine L ≠
      PrimitiveGeometry.euclideanRayLine M :=
  PrimitiveGeometry.euclideanRayLine_ne_of_det2_rayDirection_ne_zero hdet

/-- Exact OEIS base fact: `Q0` and `Q1` have distinct lifted circles. -/
theorem karlsson_oeis_q0_q1_spheres_distinct :
    PrimitiveGeometry.euclideanSphere ExplicitInputs.karlssonOEISQ0.center
        ExplicitInputs.karlssonOEISQ0.radius ≠
      PrimitiveGeometry.euclideanSphere ExplicitInputs.karlssonOEISQ1.center
        ExplicitInputs.karlssonOEISQ1.radius :=
  ExplicitInputs.karlssonOEISQ0_Q1_spheres_distinct

/-- Exact OEIS base fact: `Q0` and `Q2` have distinct lifted circles. -/
theorem karlsson_oeis_q0_q2_spheres_distinct :
    PrimitiveGeometry.euclideanSphere ExplicitInputs.karlssonOEISQ0.center
        ExplicitInputs.karlssonOEISQ0.radius ≠
      PrimitiveGeometry.euclideanSphere ExplicitInputs.karlssonOEISQ2.center
        ExplicitInputs.karlssonOEISQ2.radius :=
  ExplicitInputs.karlssonOEISQ0_Q2_spheres_distinct

/-- Exact OEIS base fact: `Q0` and `Q3` have distinct lifted circles. -/
theorem karlsson_oeis_q0_q3_spheres_distinct :
    PrimitiveGeometry.euclideanSphere ExplicitInputs.karlssonOEISQ0.center
        ExplicitInputs.karlssonOEISQ0.radius ≠
      PrimitiveGeometry.euclideanSphere ExplicitInputs.karlssonOEISQ3.center
        ExplicitInputs.karlssonOEISQ3.radius :=
  ExplicitInputs.karlssonOEISQ0_Q3_spheres_distinct

/-- Exact OEIS base fact: `Q1` and `Q2` have distinct lifted circles. -/
theorem karlsson_oeis_q1_q2_spheres_distinct :
    PrimitiveGeometry.euclideanSphere ExplicitInputs.karlssonOEISQ1.center
        ExplicitInputs.karlssonOEISQ1.radius ≠
      PrimitiveGeometry.euclideanSphere ExplicitInputs.karlssonOEISQ2.center
        ExplicitInputs.karlssonOEISQ2.radius :=
  ExplicitInputs.karlssonOEISQ1_Q2_spheres_distinct

/-- Exact OEIS base fact: `Q1` and `Q3` have distinct lifted circles. -/
theorem karlsson_oeis_q1_q3_spheres_distinct :
    PrimitiveGeometry.euclideanSphere ExplicitInputs.karlssonOEISQ1.center
        ExplicitInputs.karlssonOEISQ1.radius ≠
      PrimitiveGeometry.euclideanSphere ExplicitInputs.karlssonOEISQ3.center
        ExplicitInputs.karlssonOEISQ3.radius :=
  ExplicitInputs.karlssonOEISQ1_Q3_spheres_distinct

/-- Exact OEIS base fact: `Q2` and `Q3` have distinct lifted circles. -/
theorem karlsson_oeis_q2_q3_spheres_distinct :
    PrimitiveGeometry.euclideanSphere ExplicitInputs.karlssonOEISQ2.center
        ExplicitInputs.karlssonOEISQ2.radius ≠
      PrimitiveGeometry.euclideanSphere ExplicitInputs.karlssonOEISQ3.center
        ExplicitInputs.karlssonOEISQ3.radius :=
  ExplicitInputs.karlssonOEISQ2_Q3_spheres_distinct

/-- Uniform exact OEIS base fact: every unordered base pair has distinct
lifted circles. -/
theorem karlsson_oeis_base_spheres_distinct
    {i j : Fin 4} (hij : i < j) :
    PrimitiveGeometry.euclideanSphere
        (ExplicitInputs.karlssonOEISBaseArrangement.lollipop i).center
        (ExplicitInputs.karlssonOEISBaseArrangement.lollipop i).radius ≠
      PrimitiveGeometry.euclideanSphere
        (ExplicitInputs.karlssonOEISBaseArrangement.lollipop j).center
        (ExplicitInputs.karlssonOEISBaseArrangement.lollipop j).radius :=
  ExplicitInputs.karlssonOEISBase_spheres_distinct hij

/-- Exact OEIS base fact: `Q0` and `Q1` have distinct ray-supporting lines. -/
theorem karlsson_oeis_q0_q1_ray_lines_distinct :
    PrimitiveGeometry.euclideanRayLine ExplicitInputs.karlssonOEISQ0 ≠
      PrimitiveGeometry.euclideanRayLine ExplicitInputs.karlssonOEISQ1 :=
  ExplicitInputs.karlssonOEISQ0_Q1_rayLines_distinct

/-- Exact OEIS base fact: `Q0` and `Q2` have distinct ray-supporting lines. -/
theorem karlsson_oeis_q0_q2_ray_lines_distinct :
    PrimitiveGeometry.euclideanRayLine ExplicitInputs.karlssonOEISQ0 ≠
      PrimitiveGeometry.euclideanRayLine ExplicitInputs.karlssonOEISQ2 :=
  ExplicitInputs.karlssonOEISQ0_Q2_rayLines_distinct

/-- Exact OEIS base fact: `Q0` and `Q3` have distinct ray-supporting lines. -/
theorem karlsson_oeis_q0_q3_ray_lines_distinct :
    PrimitiveGeometry.euclideanRayLine ExplicitInputs.karlssonOEISQ0 ≠
      PrimitiveGeometry.euclideanRayLine ExplicitInputs.karlssonOEISQ3 :=
  ExplicitInputs.karlssonOEISQ0_Q3_rayLines_distinct

/-- Exact OEIS base fact: `Q1` and `Q2` have distinct ray-supporting lines. -/
theorem karlsson_oeis_q1_q2_ray_lines_distinct :
    PrimitiveGeometry.euclideanRayLine ExplicitInputs.karlssonOEISQ1 ≠
      PrimitiveGeometry.euclideanRayLine ExplicitInputs.karlssonOEISQ2 :=
  ExplicitInputs.karlssonOEISQ1_Q2_rayLines_distinct

/-- Exact OEIS base fact: `Q1` and `Q3` have distinct ray-supporting lines. -/
theorem karlsson_oeis_q1_q3_ray_lines_distinct :
    PrimitiveGeometry.euclideanRayLine ExplicitInputs.karlssonOEISQ1 ≠
      PrimitiveGeometry.euclideanRayLine ExplicitInputs.karlssonOEISQ3 :=
  ExplicitInputs.karlssonOEISQ1_Q3_rayLines_distinct

/-- Exact OEIS base fact: `Q2` and `Q3` have distinct ray-supporting lines. -/
theorem karlsson_oeis_q2_q3_ray_lines_distinct :
    PrimitiveGeometry.euclideanRayLine ExplicitInputs.karlssonOEISQ2 ≠
      PrimitiveGeometry.euclideanRayLine ExplicitInputs.karlssonOEISQ3 :=
  ExplicitInputs.karlssonOEISQ2_Q3_rayLines_distinct

/-- Uniform exact OEIS base fact: every unordered base pair has distinct
ray-supporting lines. -/
theorem karlsson_oeis_base_ray_lines_distinct
    {i j : Fin 4} (hij : i < j) :
    PrimitiveGeometry.euclideanRayLine
        (ExplicitInputs.karlssonOEISBaseArrangement.lollipop i) ≠
      PrimitiveGeometry.euclideanRayLine
        (ExplicitInputs.karlssonOEISBaseArrangement.lollipop j) :=
  ExplicitInputs.karlssonOEISBase_rayLines_distinct hij

/-- The checked OEIS base noncoincidence package plus any exact base
carrier-intersection certificate imply the generic `<= 7` crossing bound for
every unordered base pair. -/
theorem karlsson_oeis_base_certificate_cross_le_seven
    (C : KarlssonOEISBaseCoordinateCrossingCertificate)
    {i j : Fin 4} (hij : i < j) :
    ExplicitInputs.karlssonBasePairCrossing i j ≤ 7 :=
  C.cross_le_seven hij

/-- Cardinality version of the generic `<= 7` bound for the finite crossing
sets in an exact OEIS base-coordinate certificate. -/
theorem karlsson_oeis_base_certificate_crossingPoints_card_le_seven
    (C : KarlssonOEISBaseCoordinateCrossingCertificate)
    {i j : Fin 4} (hij : i < j) :
    (C.pairwise_crossings.crossingPoints i j hij).card ≤ 7 :=
  C.crossingPoints_card_le_seven hij

/-- The named Karlsson four-base lower certificate gives the `n = 4` region
count `45`. -/
theorem karlsson_base_incremental_region_count
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ExplicitInputs.KarlssonBaseBlowUpIncrementalLowerData P) :
    P.region 4 h.base_arrangement = 45 :=
  h.base_region_eq_forty_five

/-- Four-base/local-blow-up lower data convert to the pairwise lower package
used by the final Theorem 1 endpoint. -/
noncomputable def pairwise_lower_data_from_karlsson_base_blowup
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ExplicitInputs.KarlssonBaseBlowUpIncrementalLowerData P) :
    ExplicitInputs.PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerData P :=
  h.toPairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerData

/-- Local copy-pair lower certificates assemble into the universal copy-pair
value statement used by the Karlsson lower interface. -/
theorem karlsson_base_copy_pair_values_from_local
    {baseCross : Fin 4 → Fin 4 → Rat}
    {n : Nat} {cluster : Fin n → Fin 4}
    {pairCross : Fin n → Fin n → Rat}
    (loc :
      ∀ i j : Fin n, ∀ hij : i < j,
        ExplicitInputs.LocalKarlssonBaseCopyPairCrossingData
          baseCross cluster pairCross i j hij) :
    ∀ i j : Fin n, ∀ _hij : i < j,
      pairCross i j =
        ExplicitInputs.karlssonBaseCopyPairCrossing baseCross cluster i j :=
  ExplicitInputs.pair_cross_eq_base_copy_from_local loc

/-- Six-pair base data plus local copy-pair lower certificates assemble into
the theorem-facing Karlsson lower construction package. -/
noncomputable def karlsson_base_blowup_from_local_copy_pairs
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ExplicitInputs.KarlssonBaseSixPairLocalBlowUpIncrementalLowerData P) :
    ExplicitInputs.KarlssonBaseBlowUpIncrementalLowerData P :=
  h.toKarlssonBaseBlowUpIncrementalLowerData

/-- Local copy-pair lower data convert all the way to the pairwise lower
package where Lean performs the cluster summation. -/
noncomputable def pairwise_lower_data_from_local_karlsson_base_blowup
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ExplicitInputs.KarlssonBaseSixPairLocalBlowUpIncrementalLowerData P) :
    ExplicitInputs.PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerData P :=
  h.toKarlssonBaseBlowUpIncrementalLowerData
    |>.toPairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerData

/-- Monotone pairwise lower data, where each copy pair only has to realize at
least the Karlsson table value, imply lower attainment as an inequality.  This
is often the right target for concrete geometric lower constructions: exact
classification of all extra intersections is unnecessary for the lower bound. -/
theorem lower_bound_attainment_from_monotone_pairwise_lower_data
    (P : TheoremOne.ProblemFamily.{u})
    (h :
      ExplicitInputs.PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData
        P) :
    ∀ n : Nat, ∃ A : P.Arrangement n,
      candidateRegionsChoose n ≤ P.region n A :=
  h.lower_bound_attainment_choose P

/-- Any finite subset of a locally certified primitive carrier intersection
has cardinality at most the corresponding pair-crossing table value. -/
theorem finite_lower_subset_card_le_pair_cross_from_local_carrier
    {n : Nat} {A : PrimitiveGeometry.EuclideanLollipopArrangement n}
    {pairCross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
    (C : PrimitiveGeometry.LocalPairCarrierCrossingData A pairCross i j hij)
    (S : Finset PrimitiveGeometry.R2)
    (hS : ∀ p ∈ S, p ∈ A.pairIntersectionSet i j) :
    (S.card : Rat) ≤ pairCross i j :=
  PrimitiveGeometry.finset_card_le_pair_cross_of_localCarrierCrossing C S hS

/-- A finite primitive carrier lower witness gives a rational lower bound on
the corresponding pair-crossing table entry. -/
theorem pair_cross_lower_bound_from_finite_lower_witness
    {n : Nat} {A : PrimitiveGeometry.EuclideanLollipopArrangement n}
    {pairCross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
    {bound : Nat}
    (D :
      PrimitiveGeometry.LocalPairCarrierLowerWitnessData
        A pairCross i j hij bound) :
    (bound : Rat) ≤ pairCross i j :=
  D.bound_le_pair_cross

/-- A finite primitive carrier lower subset plus a local carrier-crossing
certificate gives a rational lower bound on the corresponding pair-crossing
table entry. -/
theorem pair_cross_lower_bound_from_finite_lower_subset
    {n : Nat} {A : PrimitiveGeometry.EuclideanLollipopArrangement n}
    {pairCross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
    {bound : Nat}
    (D :
      PrimitiveGeometry.LocalPairCarrierLowerSubsetData A i j hij bound)
    (C : PrimitiveGeometry.LocalPairCarrierCrossingData A pairCross i j hij) :
    (bound : Rat) ≤ pairCross i j :=
  D.bound_le_pair_cross C

/-- A finite primitive carrier lower witness supplies the local monotone
copy-pair lower certificate once its size dominates the Karlsson cluster-table
value. -/
def local_cluster_lower_bound_from_finite_lower_witness
    {n : Nat} {A : PrimitiveGeometry.EuclideanLollipopArrangement n}
    {pairCross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
    {bound : Nat} {cluster : Fin n → Fin 4}
    (D :
      PrimitiveGeometry.LocalPairCarrierLowerWitnessData
        A pairCross i j hij bound)
    (hcluster :
      ExplicitInputs.karlssonClusterPairCrossing (cluster i) (cluster j) ≤
        (bound : Rat)) :
    ExplicitInputs.LocalClusterPairLowerBoundData
      cluster pairCross i j hij :=
  D.toLocalClusterPairLowerBoundData hcluster

/-- A finite primitive carrier lower subset plus a local carrier-crossing
certificate supplies the local monotone copy-pair lower certificate once its
size dominates the Karlsson cluster-table value. -/
def local_cluster_lower_bound_from_finite_lower_subset
    {n : Nat} {A : PrimitiveGeometry.EuclideanLollipopArrangement n}
    {pairCross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
    {bound : Nat} {cluster : Fin n → Fin 4}
    (D :
      PrimitiveGeometry.LocalPairCarrierLowerSubsetData A i j hij bound)
    (C : PrimitiveGeometry.LocalPairCarrierCrossingData A pairCross i j hij)
    (hcluster :
      ExplicitInputs.karlssonClusterPairCrossing (cluster i) (cluster j) ≤
        (bound : Rat)) :
    ExplicitInputs.LocalClusterPairLowerBoundData
      cluster pairCross i j hij :=
  D.toLocalClusterPairLowerBoundData C hcluster

/-- Four normalized directions contain a close pair.  The sorting step is
internal: callers only supply the normalized direction bounds on the four-set. -/
theorem close_pair_in_every_four_from_normalized_directions
    {V : Type u} [DecidableEq V]
    (theta : V → ℝ) {t : Finset V} (ht : t.card = 4)
    (htheta_nonneg : ∀ x ∈ t, 0 ≤ theta x)
    (htheta_lt_one : ∀ x ∈ t, theta x < 1) :
    ∃ x ∈ t, ∃ y ∈ t, x ≠ y ∧
      CloseDirection.cyclicClose theta x y :=
  CloseDirection.exists_cyclicClose_pair_of_card_four
    theta ht htheta_nonneg htheta_lt_one

/-- Paulsen's five-vector obstruction proves that every five-set contains an
intriguing pair once the corresponding Paulsen witnesses have been supplied. -/
theorem intriguing_pair_in_every_five_from_paulsen_data
    {V : Type u} [DecidableEq V]
    (intriguing : V → V → Prop)
    (hdata : ∀ t : Finset V, t.card = 5 →
      PaulsenLinearAlgebra.FiveSetPaulsenData intriguing t) :
    ∀ t : Finset V, t.card = 5 →
      ∃ x ∈ t, ∃ y ∈ t, x ≠ y ∧ intriguing x y :=
  PaulsenLinearAlgebra.intriguing_pair_in_every_five_of_paulsen_data
    intriguing hdata

/-- In Paulsen's appendix, a nontrivial linear relation among the five vectors
cannot have all coefficients with the same sign, because every first coordinate
is positive. -/
theorem paulsen_relation_has_pos_and_neg_coefficients
    (v : Fin 5 → PaulsenLinearAlgebra.R4)
    (hfirst : ∀ i : Fin 5, 0 < v i 0)
    (c : Fin 5 → ℝ)
    (hrel : ∑ i : Fin 5, c i • v i = 0)
    (hnonzero : ∃ i : Fin 5, c i ≠ 0) :
    (∃ i : Fin 5, 0 < c i) ∧ (∃ i : Fin 5, c i < 0) :=
  PaulsenLinearAlgebra.relation_has_pos_and_neg_coefficients
    v hfirst c hrel hnonzero

/-- Formal split of Paulsen's nontrivial relation into the positive and negative
coefficient supports. -/
theorem paulsen_relation_split
    (v : Fin 5 → PaulsenLinearAlgebra.R4) (c : Fin 5 → ℝ)
    (hrel : ∑ i : Fin 5, c i • v i = 0) :
    let P : Finset (Fin 5) := Finset.univ.filter (fun i => 0 < c i)
    let N : Finset (Fin 5) := Finset.univ.filter (fun i => c i < 0)
    Disjoint P N ∧
      (∑ i ∈ P, c i • v i) = ∑ j ∈ N, (-c j) • v j :=
  PaulsenLinearAlgebra.relation_split v c hrel

/-- The abstract five-vector contradiction at the end of Paulsen's appendix:
five vectors with positive first coordinates, unit diagonal Gram values, and
off-diagonal Gram values in `(-1,0)` cannot exist. -/
theorem paulsen_no_five_gram_vectors
    (v : Fin 5 → PaulsenLinearAlgebra.R4)
    (hfirst : ∀ i : Fin 5, 0 < v i 0)
    (hself :
      ∀ i : Fin 5,
        PaulsenLinearAlgebra.lorentzForm (v i) (v i) = 1)
    (hneg :
      ∀ i j : Fin 5, i ≠ j →
        PaulsenLinearAlgebra.lorentzForm (v i) (v j) < 0)
    (hgt_neg_one :
      ∀ i j : Fin 5, i ≠ j →
        -1 < PaulsenLinearAlgebra.lorentzForm (v i) (v j)) :
    False :=
  PaulsenLinearAlgebra.no_paulsen_gram_five
    v hfirst hself hneg hgt_neg_one

/-- The checked no-meet branch of the manuscript's intriguing-circle
definition. -/
theorem circle_intriguing_from_no_meet_certificate
    {L M : PrimitiveGeometry.EuclideanLollipop}
    (D : PrimitiveGeometry.CircleCircleNoMeetData L M) :
    PaulsenLinearAlgebra.circleIntriguingPair
      L.radius M.radius L.center M.center :=
  D.circleIntriguingPair

/-- Algebraic case split for the manuscript's formal intriguing-circle
relation: an intriguing pair lies on one of the two closed sides of the strict
obtuse-distance interval. -/
theorem circle_intriguing_distance_cases
    (r s : ℝ) (x y : PaulsenLinearAlgebra.R2) :
    PaulsenLinearAlgebra.circleIntriguingPair r s x y ↔
      PaulsenLinearAlgebra.distSq2 x y ≤ r ^ 2 + s ^ 2 ∨
        (r + s) ^ 2 ≤ PaulsenLinearAlgebra.distSq2 x y :=
  PaulsenLinearAlgebra.circleIntriguingPair_iff_distSq2_le_or_radius_add_sq_le
    r s x y

/-- Local one-pair primitive carrier-intersection certificates assemble into the
global pairwise carrier-crossing certificate used by the upper-bound stack. -/
noncomputable def pairwise_carrier_crossing_data_from_local
    {n : Nat}
    {A : PrimitiveGeometry.EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat}
    (loc :
      ∀ i j : Fin n, ∀ hij : i < j,
        PrimitiveGeometry.LocalPairCarrierCrossingData A cross i j hij) :
    PrimitiveGeometry.PairwiseCarrierCrossingData A cross :=
  PrimitiveGeometry.PairwiseCarrierCrossingData.ofLocal loc

/-- Generic primitive carrier intersections have at most seven crossing
points when the two circles and the two ray-supporting lines are distinct. -/
theorem generic_carrier_pair_crossing_bound
    {n : Nat}
    {A : PrimitiveGeometry.EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat}
    (D : PrimitiveGeometry.PairwiseCarrierCrossingData A cross)
    {i j : Fin n} (hij : i < j)
    (hspheres :
      PrimitiveGeometry.euclideanSphere (A.lollipop i).center
          (A.lollipop i).radius ≠
        PrimitiveGeometry.euclideanSphere (A.lollipop j).center
          (A.lollipop j).radius)
    (hlines :
      PrimitiveGeometry.euclideanRayLine (A.lollipop i) ≠
        PrimitiveGeometry.euclideanRayLine (A.lollipop j)) :
    cross i j ≤ 7 :=
  PrimitiveGeometry.pairwiseCarrierCrossingData_cross_le_seven
    D hij hspheres hlines

/-- Local one-pair primitive carrier intersections have at most seven crossing
points when the two circles and the two ray-supporting lines are distinct. -/
theorem local_generic_carrier_pair_crossing_bound
    {n : Nat}
    {A : PrimitiveGeometry.EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat}
    {i j : Fin n} {hij : i < j}
    (D : PrimitiveGeometry.LocalPairCarrierCrossingData A cross i j hij)
    (hspheres :
      PrimitiveGeometry.euclideanSphere (A.lollipop i).center
          (A.lollipop i).radius ≠
        PrimitiveGeometry.euclideanSphere (A.lollipop j).center
          (A.lollipop j).radius)
    (hlines :
      PrimitiveGeometry.euclideanRayLine (A.lollipop i) ≠
        PrimitiveGeometry.euclideanRayLine (A.lollipop j)) :
    cross i j ≤ 7 :=
  PrimitiveGeometry.localPairCarrierCrossingData_cross_le_seven
    D hspheres hlines

/-- Component-wise savings for one primitive carrier pair imply the
corresponding rational pair-crossing bound. -/
theorem carrier_pair_crossing_bound_from_component_savings
    {n : Nat}
    {A : PrimitiveGeometry.EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat}
    (D : PrimitiveGeometry.PairwiseCarrierCrossingData A cross)
    {i j : Fin n} (hij : i < j) {bound : Nat}
    (B : PrimitiveGeometry.PairComponentSavings
      (A.lollipop i) (A.lollipop j) bound) :
    cross i j ≤ (bound : Rat) :=
  PrimitiveGeometry.pairwiseCarrierCrossingData_cross_le_of_pairComponentSavings
    D hij B

/-- Local one-pair carrier-intersection data plus component-wise savings imply
the corresponding rational pair-crossing bound without assembling a global
pairwise crossing table first. -/
theorem local_carrier_pair_crossing_bound_from_component_savings
    {n : Nat}
    {A : PrimitiveGeometry.EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat}
    {i j : Fin n} {hij : i < j}
    (D : PrimitiveGeometry.LocalPairCarrierCrossingData A cross i j hij)
    {bound : Nat}
    (B : PrimitiveGeometry.PairComponentSavings
      (A.lollipop i) (A.lollipop j) bound) :
    cross i j ≤ (bound : Rat) :=
  PrimitiveGeometry.localPairCarrierCrossingData_cross_le_of_pairComponentSavings
    D B

/-- Component-wise savings are a special case of direct whole-carrier
savings. -/
def direct_carrier_savings_from_component_savings
    {L M : PrimitiveGeometry.EuclideanLollipop} {bound : Nat}
    (B : PrimitiveGeometry.PairComponentSavings L M bound) :
    PrimitiveGeometry.PairCarrierSavings L M bound :=
  B.toPairCarrierSavings

/-- Direct whole-carrier savings for one primitive carrier pair imply the
corresponding rational pair-crossing bound. -/
theorem carrier_pair_crossing_bound_from_direct_savings
    {n : Nat}
    {A : PrimitiveGeometry.EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat}
    (D : PrimitiveGeometry.PairwiseCarrierCrossingData A cross)
    {i j : Fin n} (hij : i < j) {bound : Nat}
    (B : PrimitiveGeometry.PairCarrierSavings
      (A.lollipop i) (A.lollipop j) bound) :
    cross i j ≤ (bound : Rat) :=
  PrimitiveGeometry.pairwiseCarrierCrossingData_cross_le_of_pairCarrierSavings
    D (hij := hij) B

/-- Local one-pair carrier-intersection data plus direct whole-carrier savings
imply the corresponding rational pair-crossing bound without assembling a
global pairwise crossing table first. -/
theorem local_carrier_pair_crossing_bound_from_direct_savings
    {n : Nat}
    {A : PrimitiveGeometry.EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat}
    {i j : Fin n} {hij : i < j}
    (D : PrimitiveGeometry.LocalPairCarrierCrossingData A cross i j hij)
    {bound : Nat}
    (B : PrimitiveGeometry.PairCarrierSavings
      (A.lollipop i) (A.lollipop j) bound) :
    cross i j ≤ (bound : Rat) :=
  PrimitiveGeometry.localPairCarrierCrossingData_cross_le_of_pairCarrierSavings
    D B

/-- Direct coupled component-count route: if one point lies in all four
circle/ray components, then the whole carrier intersection has at most four
points under the usual noncoincidence hypotheses. -/
def direct_four_savings_from_common_all_components
    {L M : PrimitiveGeometry.EuclideanLollipop}
    (hspheres :
      PrimitiveGeometry.euclideanSphere L.center L.radius ≠
        PrimitiveGeometry.euclideanSphere M.center M.radius)
    (hline : PrimitiveGeometry.euclideanRayLine L ≠
      PrimitiveGeometry.euclideanRayLine M)
    {q : PrimitiveGeometry.EuclideanR2}
    (hqcc : q ∈ PrimitiveGeometry.euclideanCircleCircleSet L M)
    (hqcr : q ∈ PrimitiveGeometry.euclideanCircleRaySet L M)
    (hqrc : q ∈ PrimitiveGeometry.euclideanRayCircleSet L M)
    (hqrr : q ∈ PrimitiveGeometry.euclideanRayRaySet L M) :
    PrimitiveGeometry.PairCarrierSavings L M 4 :=
  PrimitiveGeometry.pairCarrierSavingsFourOfCommonAllComponents
    hspheres hline hqcc hqcr hqrc hqrr

/-- Direct coupled component-count route: if one point lies in any three of
the four circle/ray components, then the whole carrier intersection has at
most five points under the usual noncoincidence hypotheses. -/
def direct_five_savings_from_triple_component_overlap
    {L M : PrimitiveGeometry.EuclideanLollipop}
    (hspheres :
      PrimitiveGeometry.euclideanSphere L.center L.radius ≠
        PrimitiveGeometry.euclideanSphere M.center M.radius)
    (hline : PrimitiveGeometry.euclideanRayLine L ≠
      PrimitiveGeometry.euclideanRayLine M)
    {q : PrimitiveGeometry.EuclideanR2}
    (H : PrimitiveGeometry.PairComponentTripleOverlap L M q) :
    PrimitiveGeometry.PairCarrierSavings L M 5 :=
  PrimitiveGeometry.pairCarrierSavingsFiveOfTripleComponentOverlap
    hspheres hline H

/-- Cardinality form of the direct triple-overlap route. -/
theorem carrier_card_le_five_from_triple_component_overlap
    {L M : PrimitiveGeometry.EuclideanLollipop}
    (hspheres :
      PrimitiveGeometry.euclideanSphere L.center L.radius ≠
        PrimitiveGeometry.euclideanSphere M.center M.radius)
    (hline : PrimitiveGeometry.euclideanRayLine L ≠
      PrimitiveGeometry.euclideanRayLine M)
    {q : PrimitiveGeometry.EuclideanR2}
    (H : PrimitiveGeometry.PairComponentTripleOverlap L M q)
    (S : Finset PrimitiveGeometry.EuclideanR2)
    (hS : ∀ p ∈ S,
      p ∈ PrimitiveGeometry.euclideanPairIntersectionSet L M) :
    S.card ≤ 5 :=
  (direct_five_savings_from_triple_component_overlap
    hspheres hline H).carrier_card_le S hS

/-- Direct coupled component-count route: if two overlap witnesses together
improve all four circle/ray component estimates, then the whole carrier
intersection has at most five points. -/
def direct_five_savings_from_two_double_component_overlap
    {L M : PrimitiveGeometry.EuclideanLollipop}
    (hspheres :
      PrimitiveGeometry.euclideanSphere L.center L.radius ≠
        PrimitiveGeometry.euclideanSphere M.center M.radius)
    (hline : PrimitiveGeometry.euclideanRayLine L ≠
      PrimitiveGeometry.euclideanRayLine M)
    {q r : PrimitiveGeometry.EuclideanR2}
    (H : PrimitiveGeometry.PairComponentTwoDoubleOverlap L M q r) :
    PrimitiveGeometry.PairCarrierSavings L M 5 :=
  PrimitiveGeometry.pairCarrierSavingsFiveOfTwoDoubleComponentOverlap
    hspheres hline H

/-- Cardinality form of the direct two-overlap route. -/
theorem carrier_card_le_five_from_two_double_component_overlap
    {L M : PrimitiveGeometry.EuclideanLollipop}
    (hspheres :
      PrimitiveGeometry.euclideanSphere L.center L.radius ≠
        PrimitiveGeometry.euclideanSphere M.center M.radius)
    (hline : PrimitiveGeometry.euclideanRayLine L ≠
      PrimitiveGeometry.euclideanRayLine M)
    {q r : PrimitiveGeometry.EuclideanR2}
    (H : PrimitiveGeometry.PairComponentTwoDoubleOverlap L M q r)
    (S : Finset PrimitiveGeometry.EuclideanR2)
    (hS : ∀ p ∈ S,
      p ∈ PrimitiveGeometry.euclideanPairIntersectionSet L M) :
    S.card ≤ 5 :=
  (direct_five_savings_from_two_double_component_overlap
    hspheres hline H).carrier_card_le S hS

/-- Cardinality form of the direct overlap route. -/
theorem carrier_card_le_four_from_common_all_components
    {L M : PrimitiveGeometry.EuclideanLollipop}
    (hspheres :
      PrimitiveGeometry.euclideanSphere L.center L.radius ≠
        PrimitiveGeometry.euclideanSphere M.center M.radius)
    (hline : PrimitiveGeometry.euclideanRayLine L ≠
      PrimitiveGeometry.euclideanRayLine M)
    {q : PrimitiveGeometry.EuclideanR2}
    (hqcc : q ∈ PrimitiveGeometry.euclideanCircleCircleSet L M)
    (hqcr : q ∈ PrimitiveGeometry.euclideanCircleRaySet L M)
    (hqrc : q ∈ PrimitiveGeometry.euclideanRayCircleSet L M)
    (hqrr : q ∈ PrimitiveGeometry.euclideanRayRaySet L M)
    (S : Finset PrimitiveGeometry.EuclideanR2)
    (hS : ∀ p ∈ S,
      p ∈ PrimitiveGeometry.euclideanPairIntersectionSet L M) :
    S.card ≤ 4 :=
  (direct_four_savings_from_common_all_components
    hspheres hline hqcc hqcr hqrc hqrr).carrier_card_le S hS

/-- The exact shared-anchor close-route audit pair has direct whole-carrier
`<= 4` savings. -/
def close_route_audit_direct_four_savings :
    PrimitiveGeometry.PairCarrierSavings
      PrimitiveGeometry.closeRouteAuditRight
      PrimitiveGeometry.closeRouteAuditDown 4 :=
  PrimitiveGeometry.closeRouteAudit_direct_savings_four

/-- A concrete way to prove a close/intriguing `<= 5` component-savings
obligation: show that the circle-circle component is empty. -/
def five_savings_from_empty_circle_circle_component
    {L M : PrimitiveGeometry.EuclideanLollipop}
    (hline : PrimitiveGeometry.euclideanRayLine L ≠
      PrimitiveGeometry.euclideanRayLine M)
    (hcc_empty : ∀ p : PrimitiveGeometry.EuclideanR2,
      p ∉ PrimitiveGeometry.euclideanCircleCircleSet L M) :
    PrimitiveGeometry.PairComponentSavings L M 5 :=
  PrimitiveGeometry.pairComponentSavingsFiveOfCircleCircleEmpty
    hline hcc_empty

/-- A concrete `<= 5` component-savings route for disjoint circles: prove the
center distance is greater than the sum of radii. -/
def five_savings_from_far_apart_circles
    {L M : PrimitiveGeometry.EuclideanLollipop}
    (hline : PrimitiveGeometry.euclideanRayLine L ≠
      PrimitiveGeometry.euclideanRayLine M)
    (hfar :
      L.radius + M.radius <
        dist (PrimitiveGeometry.toEuclideanR2 L.center)
          (PrimitiveGeometry.toEuclideanR2 M.center)) :
    PrimitiveGeometry.PairComponentSavings L M 5 :=
  PrimitiveGeometry.pairComponentSavingsFiveOfCircleCircleFarApart
    hline hfar

/-- Squared-coordinate version of `five_savings_from_far_apart_circles`. -/
def five_savings_from_far_apart_circles_sq
    {L M : PrimitiveGeometry.EuclideanLollipop}
    (hline : PrimitiveGeometry.euclideanRayLine L ≠
      PrimitiveGeometry.euclideanRayLine M)
    (hfar :
      (L.radius + M.radius) ^ 2 <
        PaulsenLinearAlgebra.distSq2 L.center M.center) :
    PrimitiveGeometry.PairComponentSavings L M 5 :=
  PrimitiveGeometry.pairComponentSavingsFiveOfCircleCircleFarApartSq
    hline hfar

/-- A concrete `<= 5` savings route for nonintersecting nested circles with
`L` strictly inside `M`. -/
def five_savings_from_left_circle_strictly_inside_right_circle
    {L M : PrimitiveGeometry.EuclideanLollipop}
    (hline : PrimitiveGeometry.euclideanRayLine L ≠
      PrimitiveGeometry.euclideanRayLine M)
    (hcontained :
      dist (PrimitiveGeometry.toEuclideanR2 L.center)
          (PrimitiveGeometry.toEuclideanR2 M.center) + L.radius <
        M.radius) :
    PrimitiveGeometry.PairComponentSavings L M 5 :=
  PrimitiveGeometry.pairComponentSavingsFiveOfCircleCircleContainedLeft
    hline hcontained

/-- Symmetric concrete `<= 5` savings route for nested nonintersecting
circles. -/
def five_savings_from_right_circle_strictly_inside_left_circle
    {L M : PrimitiveGeometry.EuclideanLollipop}
    (hline : PrimitiveGeometry.euclideanRayLine L ≠
      PrimitiveGeometry.euclideanRayLine M)
    (hcontained :
      dist (PrimitiveGeometry.toEuclideanR2 L.center)
          (PrimitiveGeometry.toEuclideanR2 M.center) + M.radius <
        L.radius) :
    PrimitiveGeometry.PairComponentSavings L M 5 :=
  PrimitiveGeometry.pairComponentSavingsFiveOfCircleCircleContainedRight
    hline hcontained

/-- Squared-coordinate nested-circle savings route with `L` strictly inside
`M`. -/
def five_savings_from_left_circle_strictly_inside_right_circle_sq
    {L M : PrimitiveGeometry.EuclideanLollipop}
    (hline : PrimitiveGeometry.euclideanRayLine L ≠
      PrimitiveGeometry.euclideanRayLine M)
    (hradius : L.radius < M.radius)
    (hcontained :
      PaulsenLinearAlgebra.distSq2 L.center M.center <
        (M.radius - L.radius) ^ 2) :
    PrimitiveGeometry.PairComponentSavings L M 5 :=
  PrimitiveGeometry.pairComponentSavingsFiveOfCircleCircleContainedLeftSq
    hline hradius hcontained

/-- Squared-coordinate nested-circle savings route with `M` strictly inside
`L`. -/
def five_savings_from_right_circle_strictly_inside_left_circle_sq
    {L M : PrimitiveGeometry.EuclideanLollipop}
    (hline : PrimitiveGeometry.euclideanRayLine L ≠
      PrimitiveGeometry.euclideanRayLine M)
    (hradius : M.radius < L.radius)
    (hcontained :
      PaulsenLinearAlgebra.distSq2 L.center M.center <
        (L.radius - M.radius) ^ 2) :
    PrimitiveGeometry.PairComponentSavings L M 5 :=
  PrimitiveGeometry.pairComponentSavingsFiveOfCircleCircleContainedRightSq
    hline hradius hcontained

/-- Packaged route for the manuscript phrase "the two circles do not meet":
any formal no-meet certificate gives the `<= 5` component savings obtained by
removing the circle-circle component. -/
def five_savings_from_circle_no_meet_certificate
    {L M : PrimitiveGeometry.EuclideanLollipop}
    (hline : PrimitiveGeometry.euclideanRayLine L ≠
      PrimitiveGeometry.euclideanRayLine M)
    (D : PrimitiveGeometry.CircleCircleNoMeetData L M) :
    PrimitiveGeometry.PairComponentSavings L M 5 :=
  PrimitiveGeometry.pairComponentSavingsFiveOfCircleCircleNoMeet hline D

/-- A concrete way to prove a close/intriguing `<= 5` component-savings
obligation: show that one mixed circle-ray component is empty. -/
def five_savings_from_empty_circle_ray_component
    {L M : PrimitiveGeometry.EuclideanLollipop}
    (hspheres :
      PrimitiveGeometry.euclideanSphere L.center L.radius ≠
        PrimitiveGeometry.euclideanSphere M.center M.radius)
    (hline : PrimitiveGeometry.euclideanRayLine L ≠
      PrimitiveGeometry.euclideanRayLine M)
    (hcr_empty : ∀ p : PrimitiveGeometry.EuclideanR2,
      p ∉ PrimitiveGeometry.euclideanCircleRaySet L M) :
    PrimitiveGeometry.PairComponentSavings L M 5 :=
  PrimitiveGeometry.pairComponentSavingsFiveOfCircleRayEmpty
    hspheres hline hcr_empty

/-- Line-separation version of the previous circle-ray savings route: if the
circle center is farther from the other ray's supporting line than the circle
radius, then the mixed component is empty. -/
def five_savings_from_circle_ray_line_separation
    {L M : PrimitiveGeometry.EuclideanLollipop}
    (hspheres :
      PrimitiveGeometry.euclideanSphere L.center L.radius ≠
        PrimitiveGeometry.euclideanSphere M.center M.radius)
    (hline : PrimitiveGeometry.euclideanRayLine L ≠
      PrimitiveGeometry.euclideanRayLine M)
    (hsep :
      L.radius <
        Metric.infDist (PrimitiveGeometry.toEuclideanR2 L.center)
          (PrimitiveGeometry.euclideanRayLine M :
            Set PrimitiveGeometry.EuclideanR2)) :
    PrimitiveGeometry.PairComponentSavings L M 5 :=
  PrimitiveGeometry.pairComponentSavingsFiveOfCircleRayNoMeet
    hspheres hline ⟨hsep⟩

/-- Projection-distance version of
`five_savings_from_circle_ray_line_separation`. -/
noncomputable def five_savings_from_circle_ray_projection_separation
    {L M : PrimitiveGeometry.EuclideanLollipop}
    (hspheres :
      PrimitiveGeometry.euclideanSphere L.center L.radius ≠
        PrimitiveGeometry.euclideanSphere M.center M.radius)
    (hline : PrimitiveGeometry.euclideanRayLine L ≠
      PrimitiveGeometry.euclideanRayLine M)
    (hsep :
      L.radius <
        dist (PrimitiveGeometry.toEuclideanR2 L.center)
          (PrimitiveGeometry.euclideanRayLineProjection M
            (PrimitiveGeometry.toEuclideanR2 L.center))) :
    PrimitiveGeometry.PairComponentSavings L M 5 :=
  PrimitiveGeometry.pairComponentSavingsFiveOfCircleRayProjectionSeparated
    hspheres hline hsep

/-- Coordinate determinant/Cauchy version of
`five_savings_from_circle_ray_line_separation`. -/
def five_savings_from_circle_ray_determinant_separation
    {L M : PrimitiveGeometry.EuclideanLollipop}
    (hspheres :
      PrimitiveGeometry.euclideanSphere L.center L.radius ≠
        PrimitiveGeometry.euclideanSphere M.center M.radius)
    (hline : PrimitiveGeometry.euclideanRayLine L ≠
      PrimitiveGeometry.euclideanRayLine M)
    (hsep :
      L.radius ^ 2 * PaulsenLinearAlgebra.normSq2 M.rayDirection <
        PrimitiveGeometry.det2 (M.anchor - L.center) M.rayDirection ^ 2) :
    PrimitiveGeometry.PairComponentSavings L M 5 :=
  PrimitiveGeometry.pairComponentSavingsFiveOfCircleRayDetSeparated
    hspheres hline hsep

/-- A concrete way to prove a close/intriguing `<= 5` component-savings
obligation: show that the other mixed circle-ray component is empty. -/
def five_savings_from_empty_ray_circle_component
    {L M : PrimitiveGeometry.EuclideanLollipop}
    (hspheres :
      PrimitiveGeometry.euclideanSphere L.center L.radius ≠
        PrimitiveGeometry.euclideanSphere M.center M.radius)
    (hline : PrimitiveGeometry.euclideanRayLine L ≠
      PrimitiveGeometry.euclideanRayLine M)
    (hrc_empty : ∀ p : PrimitiveGeometry.EuclideanR2,
      p ∉ PrimitiveGeometry.euclideanRayCircleSet L M) :
    PrimitiveGeometry.PairComponentSavings L M 5 :=
  PrimitiveGeometry.pairComponentSavingsFiveOfRayCircleEmpty
    hspheres hline hrc_empty

/-- Line-separation version of the ray-circle savings route. -/
def five_savings_from_ray_circle_line_separation
    {L M : PrimitiveGeometry.EuclideanLollipop}
    (hspheres :
      PrimitiveGeometry.euclideanSphere L.center L.radius ≠
        PrimitiveGeometry.euclideanSphere M.center M.radius)
    (hline : PrimitiveGeometry.euclideanRayLine L ≠
      PrimitiveGeometry.euclideanRayLine M)
    (hsep :
      M.radius <
        Metric.infDist (PrimitiveGeometry.toEuclideanR2 M.center)
          (PrimitiveGeometry.euclideanRayLine L :
            Set PrimitiveGeometry.EuclideanR2)) :
    PrimitiveGeometry.PairComponentSavings L M 5 :=
  PrimitiveGeometry.pairComponentSavingsFiveOfRayCircleNoMeet
    hspheres hline ⟨hsep⟩

/-- Projection-distance version of
`five_savings_from_ray_circle_line_separation`. -/
noncomputable def five_savings_from_ray_circle_projection_separation
    {L M : PrimitiveGeometry.EuclideanLollipop}
    (hspheres :
      PrimitiveGeometry.euclideanSphere L.center L.radius ≠
        PrimitiveGeometry.euclideanSphere M.center M.radius)
    (hline : PrimitiveGeometry.euclideanRayLine L ≠
      PrimitiveGeometry.euclideanRayLine M)
    (hsep :
      M.radius <
        dist (PrimitiveGeometry.toEuclideanR2 M.center)
          (PrimitiveGeometry.euclideanRayLineProjection L
            (PrimitiveGeometry.toEuclideanR2 M.center))) :
    PrimitiveGeometry.PairComponentSavings L M 5 :=
  PrimitiveGeometry.pairComponentSavingsFiveOfRayCircleProjectionSeparated
    hspheres hline hsep

/-- Coordinate determinant/Cauchy version of
`five_savings_from_ray_circle_line_separation`. -/
def five_savings_from_ray_circle_determinant_separation
    {L M : PrimitiveGeometry.EuclideanLollipop}
    (hspheres :
      PrimitiveGeometry.euclideanSphere L.center L.radius ≠
        PrimitiveGeometry.euclideanSphere M.center M.radius)
    (hline : PrimitiveGeometry.euclideanRayLine L ≠
      PrimitiveGeometry.euclideanRayLine M)
    (hsep :
      M.radius ^ 2 * PaulsenLinearAlgebra.normSq2 L.rayDirection <
        PrimitiveGeometry.det2 (L.anchor - M.center) L.rayDirection ^ 2) :
    PrimitiveGeometry.PairComponentSavings L M 5 :=
  PrimitiveGeometry.pairComponentSavingsFiveOfRayCircleDetSeparated
    hspheres hline hsep

/-- A concrete way to prove a `<= 4` component-savings obligation: show that
the circle-circle and ray-ray components are both empty. -/
def four_savings_from_empty_circle_circle_and_ray_ray_components
    {L M : PrimitiveGeometry.EuclideanLollipop}
    (hcc_empty : ∀ p : PrimitiveGeometry.EuclideanR2,
      p ∉ PrimitiveGeometry.euclideanCircleCircleSet L M)
    (hrr_empty : ∀ p : PrimitiveGeometry.EuclideanR2,
      p ∉ PrimitiveGeometry.euclideanRayRaySet L M) :
    PrimitiveGeometry.PairComponentSavings L M 4 :=
  PrimitiveGeometry.pairComponentSavingsFourOfCircleCircleAndRayRayEmpty
    hcc_empty hrr_empty

/-- A concrete `<= 4` route from an empty circle-circle component and the
parallel-ray determinant criterion for an empty ray-ray component. -/
def four_savings_from_empty_circle_circle_and_parallel_det_ray_ray
    {L M : PrimitiveGeometry.EuclideanLollipop}
    (hcc_empty : ∀ p : PrimitiveGeometry.EuclideanR2,
      p ∉ PrimitiveGeometry.euclideanCircleCircleSet L M)
    (hparallel :
      PrimitiveGeometry.det2 L.rayDirection M.rayDirection = 0)
    (hoffset :
      PrimitiveGeometry.det2 (M.anchor - L.anchor) L.rayDirection ≠ 0) :
    PrimitiveGeometry.PairComponentSavings L M 4 :=
  PrimitiveGeometry.pairComponentSavingsFourOfCircleCircleEmptyAndRayRayDetSeparated
    hcc_empty hparallel hoffset

/-- A packaged `<= 4` route combining a circle no-meet certificate with an
empty ray-ray component. -/
def four_savings_from_circle_no_meet_and_empty_ray_ray_component
    {L M : PrimitiveGeometry.EuclideanLollipop}
    (D : PrimitiveGeometry.CircleCircleNoMeetData L M)
    (hrr_empty : ∀ p : PrimitiveGeometry.EuclideanR2,
      p ∉ PrimitiveGeometry.euclideanRayRaySet L M) :
    PrimitiveGeometry.PairComponentSavings L M 4 :=
  PrimitiveGeometry.pairComponentSavingsFourOfCircleCircleNoMeetAndRayRayEmpty
    D hrr_empty

/-- A fully packaged `<= 4` route from no-meet certificates for the
circle-circle and ray-ray components. -/
def four_savings_from_circle_no_meet_and_ray_ray_no_meet
    {L M : PrimitiveGeometry.EuclideanLollipop}
    (Dcc : PrimitiveGeometry.CircleCircleNoMeetData L M)
    (Drr : PrimitiveGeometry.RayRayNoMeetData L M) :
    PrimitiveGeometry.PairComponentSavings L M 4 :=
  PrimitiveGeometry.pairComponentSavingsFourOfCircleCircleNoMeetAndRayRayNoMeet
    Dcc Drr

/-- A packaged `<= 4` route from a circle no-meet certificate and the
parallel-ray determinant criterion for an empty ray-ray component. -/
def four_savings_from_circle_no_meet_and_parallel_det_ray_ray
    {L M : PrimitiveGeometry.EuclideanLollipop}
    (Dcc : PrimitiveGeometry.CircleCircleNoMeetData L M)
    (hparallel :
      PrimitiveGeometry.det2 L.rayDirection M.rayDirection = 0)
    (hoffset :
      PrimitiveGeometry.det2 (M.anchor - L.anchor) L.rayDirection ≠ 0) :
    PrimitiveGeometry.PairComponentSavings L M 4 :=
  PrimitiveGeometry.pairComponentSavingsFourOfCircleCircleNoMeetAndRayRayDetSeparated
    Dcc hparallel hoffset

/-- A concrete way to prove a `<= 4` component-savings obligation: show that
both mixed circle-ray components are empty. -/
def four_savings_from_empty_mixed_ray_components
    {L M : PrimitiveGeometry.EuclideanLollipop}
    (hspheres :
      PrimitiveGeometry.euclideanSphere L.center L.radius ≠
        PrimitiveGeometry.euclideanSphere M.center M.radius)
    (hline : PrimitiveGeometry.euclideanRayLine L ≠
      PrimitiveGeometry.euclideanRayLine M)
    (hcr_empty : ∀ p : PrimitiveGeometry.EuclideanR2,
      p ∉ PrimitiveGeometry.euclideanCircleRaySet L M)
    (hrc_empty : ∀ p : PrimitiveGeometry.EuclideanR2,
      p ∉ PrimitiveGeometry.euclideanRayCircleSet L M) :
    PrimitiveGeometry.PairComponentSavings L M 4 :=
  PrimitiveGeometry.pairComponentSavingsFourOfMixedRayComponentsEmpty
    hspheres hline hcr_empty hrc_empty

/-- Line-separation certificates for both mixed circle-ray components give a
direct `<= 4` component-savings route. -/
def four_savings_from_mixed_ray_line_separations
    {L M : PrimitiveGeometry.EuclideanLollipop}
    (hspheres :
      PrimitiveGeometry.euclideanSphere L.center L.radius ≠
        PrimitiveGeometry.euclideanSphere M.center M.radius)
    (hline : PrimitiveGeometry.euclideanRayLine L ≠
      PrimitiveGeometry.euclideanRayLine M)
    (hsepLM :
      L.radius <
        Metric.infDist (PrimitiveGeometry.toEuclideanR2 L.center)
          (PrimitiveGeometry.euclideanRayLine M :
            Set PrimitiveGeometry.EuclideanR2))
    (hsepML :
      M.radius <
        Metric.infDist (PrimitiveGeometry.toEuclideanR2 M.center)
          (PrimitiveGeometry.euclideanRayLine L :
            Set PrimitiveGeometry.EuclideanR2)) :
    PrimitiveGeometry.PairComponentSavings L M 4 :=
  PrimitiveGeometry.pairComponentSavingsFourOfMixedRayComponentsNoMeet
    hspheres hline ⟨hsepLM⟩ ⟨hsepML⟩

/-- Projection-distance version of
`four_savings_from_mixed_ray_line_separations`. -/
noncomputable def four_savings_from_mixed_ray_projection_separations
    {L M : PrimitiveGeometry.EuclideanLollipop}
    (hspheres :
      PrimitiveGeometry.euclideanSphere L.center L.radius ≠
        PrimitiveGeometry.euclideanSphere M.center M.radius)
    (hline : PrimitiveGeometry.euclideanRayLine L ≠
      PrimitiveGeometry.euclideanRayLine M)
    (hsepLM :
      L.radius <
        dist (PrimitiveGeometry.toEuclideanR2 L.center)
          (PrimitiveGeometry.euclideanRayLineProjection M
            (PrimitiveGeometry.toEuclideanR2 L.center)))
    (hsepML :
      M.radius <
        dist (PrimitiveGeometry.toEuclideanR2 M.center)
          (PrimitiveGeometry.euclideanRayLineProjection L
            (PrimitiveGeometry.toEuclideanR2 M.center))) :
    PrimitiveGeometry.PairComponentSavings L M 4 :=
  PrimitiveGeometry.pairComponentSavingsFourOfMixedRayComponentsProjectionSeparated
    hspheres hline hsepLM hsepML

/-- Coordinate determinant/Cauchy version of
`four_savings_from_mixed_ray_line_separations`. -/
def four_savings_from_mixed_ray_determinant_separations
    {L M : PrimitiveGeometry.EuclideanLollipop}
    (hspheres :
      PrimitiveGeometry.euclideanSphere L.center L.radius ≠
        PrimitiveGeometry.euclideanSphere M.center M.radius)
    (hline : PrimitiveGeometry.euclideanRayLine L ≠
      PrimitiveGeometry.euclideanRayLine M)
    (hsepLM :
      L.radius ^ 2 * PaulsenLinearAlgebra.normSq2 M.rayDirection <
        PrimitiveGeometry.det2 (M.anchor - L.center) M.rayDirection ^ 2)
    (hsepML :
      M.radius ^ 2 * PaulsenLinearAlgebra.normSq2 L.rayDirection <
        PrimitiveGeometry.det2 (L.anchor - M.center) L.rayDirection ^ 2) :
    PrimitiveGeometry.PairComponentSavings L M 4 :=
  PrimitiveGeometry.pairComponentSavingsFourOfMixedRayComponentsDetSeparated
    hspheres hline hsepLM hsepML

/-- Component-savings primitive upper data imply the canonical exact upper
interface used by the colored-Turan proof stack. -/
noncomputable def exact_upper_data_from_component_savings
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveGeometry.PrimitiveCarrierComponentSavingsUpperGeometryData P) :
    PrimitiveGeometry.PrimitiveCarrierCertifiedExactUpperGeometryData P :=
  h.toPrimitiveCarrierCertifiedExactUpperGeometryData

/-- Direct whole-carrier savings primitive upper data imply the canonical
exact upper interface used by the colored-Turan proof stack. -/
noncomputable def exact_upper_data_from_direct_savings
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveGeometry.PrimitiveCarrierDirectSavingsUpperGeometryData P) :
    PrimitiveGeometry.PrimitiveCarrierCertifiedExactUpperGeometryData P :=
  h.toPrimitiveCarrierCertifiedExactUpperGeometryData

/-- The colored Turan theorem used in the manuscript: if the two forbidden
clique hypotheses hold, the ordered color weight is at most the internal
`S(n)` quantity. -/
theorem colored_turan_lemma
    {V : Type u} [Fintype V] [DecidableEq V]
    (C : ColoredGraph V)
    (hD : C.DGraph.CliqueFree 4) (hE : C.EGraph.CliqueFree 5) :
    C.orderedColorWeight / 2 ≤ concreteS (Fintype.card V) :=
  colored_turan_bound C hD hE

/-- Section 5's `3 x 4` matrix theorem, with the compression and all
star-forest normal-form cases discharged in Lean. -/
theorem section_five_matrix_theorem : MatrixTheoremStatement :=
  matrix_theorem_proven

end FormalizedProof
end TheoremOneManuscript
end Lollipop

/-!
Proof component 29: `Manuscript.FormalizedProof.FinalTheorem`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Formalized manuscript proof of Theorem 1.

The final theorem below is deliberately stated from the strongest currently
formalized manuscript subtheorem package.  Every generic argument on the path
to the formula is proved in the imported Lean files; the package fields are
exactly the remaining model-specific construction certificates.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace FormalizedProof

universe u

/-- Theorem 1 from the strongest current manuscript subtheorem package:
primitive carrier component savings for the upper bound and named incremental
Karlsson blow-up data for the lower bound. -/
theorem theorem_one_from_formalized_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : StrongestKnownTheoremOneSubtheorems P) :
    FinalTheoremOneStatement P := by
  exact theorem_one_from_component_savings_primitive_carrier_subtheorems P h

/-- Single-size Theorem 1 formula from the strongest current manuscript
subtheorem package. -/
theorem theorem_one_at_from_formalized_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : StrongestKnownTheoremOneSubtheorems P)
    (n : Nat) :
    FinalTheoremOneAtStatement P n := by
  exact theorem_one_from_formalized_subtheorems P h n

/-- Theorem 1 from direct whole-carrier primitive savings plus named
incremental Karlsson blow-up data. -/
theorem theorem_one_from_direct_savings_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : DirectSavingsTheoremOneSubtheorems P) :
    FinalTheoremOneStatement P := by
  exact theorem_one_from_direct_savings_primitive_carrier_subtheorems P h

/-- Single-size formula from direct whole-carrier primitive savings plus named
incremental Karlsson blow-up data. -/
theorem theorem_one_at_from_direct_savings_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : DirectSavingsTheoremOneSubtheorems P)
    (n : Nat) :
    FinalTheoremOneAtStatement P n := by
  exact theorem_one_from_direct_savings_subtheorems P h n

/-- Theorem 1 from primitive carrier component savings plus pairwise
Karlsson lower construction data. -/
theorem theorem_one_from_pairwise_lower_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PairwiseLowerTheoremOneSubtheorems P) :
    FinalTheoremOneStatement P := by
  exact
    theorem_one_from_component_savings_pairwise_lower_primitive_carrier_subtheorems
      P h

/-- Single-size formula from primitive carrier component savings plus
pairwise Karlsson lower construction data. -/
theorem theorem_one_at_from_pairwise_lower_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PairwiseLowerTheoremOneSubtheorems P)
    (n : Nat) :
    FinalTheoremOneAtStatement P n := by
  exact theorem_one_from_pairwise_lower_subtheorems P h n

/-- Theorem 1 from direct whole-carrier primitive savings plus pairwise
Karlsson lower construction data. -/
theorem theorem_one_from_direct_savings_pairwise_lower_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : DirectSavingsPairwiseLowerTheoremOneSubtheorems P) :
    FinalTheoremOneStatement P := by
  exact
    theorem_one_from_direct_savings_pairwise_lower_primitive_carrier_subtheorems
      P h

/-- Single-size formula from direct whole-carrier primitive savings plus
pairwise Karlsson lower construction data. -/
theorem theorem_one_at_from_direct_savings_pairwise_lower_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : DirectSavingsPairwiseLowerTheoremOneSubtheorems P)
    (n : Nat) :
    FinalTheoremOneAtStatement P n := by
  exact theorem_one_from_direct_savings_pairwise_lower_subtheorems P h n

/-- Theorem 1 from primitive carrier component savings plus monotone pairwise
Karlsson lower construction data. -/
theorem theorem_one_from_monotone_pairwise_lower_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MonotonePairwiseLowerTheoremOneSubtheorems P) :
    FinalTheoremOneStatement P := by
  exact
    theorem_one_from_component_savings_monotone_pairwise_lower_primitive_carrier_subtheorems
      P h

/-- Single-size formula from primitive carrier component savings plus
monotone pairwise Karlsson lower construction data. -/
theorem theorem_one_at_from_monotone_pairwise_lower_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MonotonePairwiseLowerTheoremOneSubtheorems P)
    (n : Nat) :
    FinalTheoremOneAtStatement P n := by
  exact theorem_one_from_monotone_pairwise_lower_subtheorems P h n

/-- Theorem 1 from direct whole-carrier primitive savings plus monotone
pairwise Karlsson lower construction data. -/
theorem theorem_one_from_direct_savings_monotone_pairwise_lower_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : DirectSavingsMonotonePairwiseLowerTheoremOneSubtheorems P) :
    FinalTheoremOneStatement P := by
  exact
    theorem_one_from_direct_savings_monotone_pairwise_lower_primitive_carrier_subtheorems
      P h

/-- Single-size formula from direct whole-carrier primitive savings plus
monotone pairwise Karlsson lower construction data. -/
theorem theorem_one_at_from_direct_savings_monotone_pairwise_lower_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : DirectSavingsMonotonePairwiseLowerTheoremOneSubtheorems P)
    (n : Nat) :
    FinalTheoremOneAtStatement P n := by
  exact theorem_one_from_direct_savings_monotone_pairwise_lower_subtheorems
    P h n

/-- Theorem 1 from primitive carrier component savings plus Karlsson's
four-base/local-blow-up lower construction package. -/
theorem theorem_one_from_karlsson_base_lower_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : KarlssonBaseLowerTheoremOneSubtheorems P) :
    FinalTheoremOneStatement P := by
  exact
    theorem_one_from_component_savings_karlsson_base_lower_primitive_carrier_subtheorems
      P h

/-- Single-size formula from primitive carrier component savings plus
Karlsson's four-base/local-blow-up lower construction package. -/
theorem theorem_one_at_from_karlsson_base_lower_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : KarlssonBaseLowerTheoremOneSubtheorems P)
    (n : Nat) :
    FinalTheoremOneAtStatement P n := by
  exact theorem_one_from_karlsson_base_lower_subtheorems P h n

/-- Theorem 1 from direct whole-carrier primitive savings plus Karlsson's
four-base/local-blow-up lower construction package. -/
theorem theorem_one_from_direct_savings_karlsson_base_lower_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : DirectSavingsKarlssonBaseLowerTheoremOneSubtheorems P) :
    FinalTheoremOneStatement P := by
  exact
    theorem_one_from_direct_savings_karlsson_base_lower_primitive_carrier_subtheorems
      P h

/-- Single-size formula from direct whole-carrier primitive savings plus
Karlsson's four-base/local-blow-up lower construction package. -/
theorem theorem_one_at_from_direct_savings_karlsson_base_lower_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : DirectSavingsKarlssonBaseLowerTheoremOneSubtheorems P)
    (n : Nat) :
    FinalTheoremOneAtStatement P n := by
  exact theorem_one_from_direct_savings_karlsson_base_lower_subtheorems P h n

/-- Theorem 1 from the slightly weaker component-bound package, where
close/intriguing savings are already supplied as numeric crossing bounds. -/
theorem theorem_one_from_component_bound_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ComponentBoundTheoremOneSubtheorems P) :
    FinalTheoremOneStatement P := by
  exact theorem_one_from_component_bound_primitive_carrier_subtheorems P h

/-- Single-size formula from the component-bound package. -/
theorem theorem_one_at_from_component_bound_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ComponentBoundTheoremOneSubtheorems P)
    (n : Nat) :
    FinalTheoremOneAtStatement P n := by
  exact theorem_one_from_component_bound_subtheorems P h n

end FormalizedProof
end TheoremOneManuscript
end Lollipop

/-!
Proof component 30: `Manuscript.FormalizedProof.DependencyGraph`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Manuscript proof dependency graph.

This module is intentionally small and non-disruptive.  It states the
paper-scale inputs that are still model-specific certificates, then proves the
displayed Theorem 1 statement from them.  All generic lemmas in the route
through the region equation, close/intriguing reduction, colored Zykov,
weighted Turan, partition matrix bookkeeping, Section 5, sorted `S(n)`, and
Karlsson finite counting are imported as proved Lean theorems.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace FormalizedProof

universe u

/-- The remaining model-specific certificate producers for the current
manuscript endpoint.

The upper field supplies primitive carrier component-savings certificates for
the geometric close/intriguing pair bounds.  The lower field supplies
Karlsson's four-base table together with local blow-up and ordered-insertion
data.  Lean proves the generic theorem-one chain from these fields. -/
structure TheoremOneDependencyGraph
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper_geometry :
    PrimitiveGeometry.PrimitiveCarrierComponentSavingsUpperGeometryData
      P.toProblemFamily
  lower_karlsson_base :
    ExplicitInputs.KarlssonBaseBlowUpIncrementalLowerData P.toProblemFamily

/-- Direct whole-carrier savings dependency graph.  This is the preferred
boundary for completing the close/intriguing route-savings proof when the
argument is coupled across carrier components. -/
structure DirectSavingsTheoremOneDependencyGraph
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper_geometry :
    PrimitiveGeometry.PrimitiveCarrierDirectSavingsUpperGeometryData
      P.toProblemFamily
  lower_karlsson_base :
    ExplicitInputs.KarlssonBaseBlowUpIncrementalLowerData P.toProblemFamily

/-- Radial-outward version of the dependency graph.  This is the manuscript
faithful upper boundary: every primitive lollipop stem is recorded as radial
outward, and the component-savings/crossing certificates are the same as in
`TheoremOneDependencyGraph`. -/
structure RadialTheoremOneDependencyGraph
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper_geometry :
    PrimitiveGeometry.PrimitiveRadialCarrierComponentSavingsUpperGeometryData
      P.toProblemFamily
  lower_karlsson_base :
    ExplicitInputs.KarlssonBaseBlowUpIncrementalLowerData P.toProblemFamily

/-- Radial-outward version of the direct whole-carrier savings dependency
graph. -/
structure DirectSavingsRadialTheoremOneDependencyGraph
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper_geometry :
    PrimitiveGeometry.PrimitiveRadialCarrierDirectSavingsUpperGeometryData
      P.toProblemFamily
  lower_karlsson_base :
    ExplicitInputs.KarlssonBaseBlowUpIncrementalLowerData P.toProblemFamily

/-- Routed version of the dependency graph: the upper close/intriguing
component savings are supplied through named geometric route constructors,
then Lean converts those routes into the component-savings package. -/
structure RoutedTheoremOneDependencyGraph
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper_geometry :
    PrimitiveGeometry.PrimitiveCarrierRoutedComponentSavingsUpperGeometryData
      P.toProblemFamily
  lower_karlsson_base :
    ExplicitInputs.KarlssonBaseBlowUpIncrementalLowerData P.toProblemFamily

/-- Radial-outward routed dependency graph, matching the manuscript stem
condition while keeping the close/intriguing savings route-based. -/
structure RoutedRadialTheoremOneDependencyGraph
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper_geometry :
    PrimitiveGeometry.PrimitiveRadialCarrierRoutedComponentSavingsUpperGeometryData
      P.toProblemFamily
  lower_karlsson_base :
    ExplicitInputs.KarlssonBaseBlowUpIncrementalLowerData P.toProblemFamily

namespace TheoremOneDependencyGraph

/-- Convert the explicit proof-DAG fields to the theorem package used by the
formalized manuscript proof. -/
noncomputable def toKarlssonBaseLowerSubtheorems
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : TheoremOneDependencyGraph P) :
    KarlssonBaseLowerTheoremOneSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson_base := h.lower_karlsson_base

end TheoremOneDependencyGraph

namespace DirectSavingsTheoremOneDependencyGraph

/-- Convert direct whole-carrier proof-DAG fields to the theorem package used
by the formalized manuscript proof. -/
noncomputable def toDirectSavingsKarlssonBaseLowerSubtheorems
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : DirectSavingsTheoremOneDependencyGraph P) :
    DirectSavingsKarlssonBaseLowerTheoremOneSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson_base := h.lower_karlsson_base

end DirectSavingsTheoremOneDependencyGraph

namespace RadialTheoremOneDependencyGraph

/-- Forget only the radial-outward record, after it has been made explicit at
the manuscript-facing proof boundary. -/
noncomputable def toTheoremOneDependencyGraph
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : RadialTheoremOneDependencyGraph P) :
    TheoremOneDependencyGraph P where
  upper_geometry := h.upper_geometry.toComponentSavingsUpperGeometryData
  lower_karlsson_base := h.lower_karlsson_base

end RadialTheoremOneDependencyGraph

namespace DirectSavingsRadialTheoremOneDependencyGraph

/-- Forget only the radial-outward record in the direct-savings graph. -/
noncomputable def toDirectSavingsTheoremOneDependencyGraph
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : DirectSavingsRadialTheoremOneDependencyGraph P) :
    DirectSavingsTheoremOneDependencyGraph P where
  upper_geometry := h.upper_geometry.toDirectSavingsUpperGeometryData
  lower_karlsson_base := h.lower_karlsson_base

end DirectSavingsRadialTheoremOneDependencyGraph

namespace RoutedTheoremOneDependencyGraph

/-- Convert the routed proof-DAG fields to the existing dependency graph by
converting named route certificates into component-savings certificates. -/
noncomputable def toTheoremOneDependencyGraph
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : RoutedTheoremOneDependencyGraph P) :
    TheoremOneDependencyGraph P where
  upper_geometry := h.upper_geometry.toComponentSavingsUpperGeometryData
  lower_karlsson_base := h.lower_karlsson_base

end RoutedTheoremOneDependencyGraph

namespace RoutedRadialTheoremOneDependencyGraph

/-- Convert routed radial proof-DAG fields to the radial dependency graph by
converting named route certificates into component-savings certificates. -/
noncomputable def toRadialTheoremOneDependencyGraph
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : RoutedRadialTheoremOneDependencyGraph P) :
    RadialTheoremOneDependencyGraph P where
  upper_geometry := h.upper_geometry.toRadialComponentSavingsUpperGeometryData
  lower_karlsson_base := h.lower_karlsson_base

/-- Forget the radial field after converting route certificates to
component-savings certificates. -/
noncomputable def toTheoremOneDependencyGraph
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : RoutedRadialTheoremOneDependencyGraph P) :
    TheoremOneDependencyGraph P :=
  h.toRadialTheoremOneDependencyGraph.toTheoremOneDependencyGraph

end RoutedRadialTheoremOneDependencyGraph

/-- The displayed manuscript Theorem 1 formula follows from the explicit
proof-DAG certificate producers. -/
theorem theorem_one_from_dependency_graph
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : TheoremOneDependencyGraph P) :
    FinalTheoremOneStatement P := by
  exact theorem_one_from_karlsson_base_lower_subtheorems P
    h.toKarlssonBaseLowerSubtheorems

/-- Single-size displayed formula from the explicit proof-DAG certificate
producers. -/
theorem theorem_one_at_from_dependency_graph
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : TheoremOneDependencyGraph P)
    (n : Nat) :
    FinalTheoremOneAtStatement P n := by
  exact theorem_one_from_dependency_graph P h n

/-- The displayed manuscript Theorem 1 formula follows from the direct
whole-carrier savings proof-DAG certificate producers. -/
theorem theorem_one_from_direct_savings_dependency_graph
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : DirectSavingsTheoremOneDependencyGraph P) :
    FinalTheoremOneStatement P := by
  exact theorem_one_from_direct_savings_karlsson_base_lower_subtheorems P
    h.toDirectSavingsKarlssonBaseLowerSubtheorems

/-- Single-size displayed formula from the direct whole-carrier savings
proof-DAG certificate producers. -/
theorem theorem_one_at_from_direct_savings_dependency_graph
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : DirectSavingsTheoremOneDependencyGraph P)
    (n : Nat) :
    FinalTheoremOneAtStatement P n := by
  exact theorem_one_from_direct_savings_dependency_graph P h n

/-- The displayed manuscript Theorem 1 formula follows from the radial-outward
proof-DAG certificate producers. -/
theorem theorem_one_from_radial_dependency_graph
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : RadialTheoremOneDependencyGraph P) :
    FinalTheoremOneStatement P := by
  exact theorem_one_from_dependency_graph P h.toTheoremOneDependencyGraph

/-- Single-size displayed formula from the radial-outward proof-DAG
certificate producers. -/
theorem theorem_one_at_from_radial_dependency_graph
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : RadialTheoremOneDependencyGraph P)
    (n : Nat) :
    FinalTheoremOneAtStatement P n := by
  exact theorem_one_from_radial_dependency_graph P h n

/-- The displayed manuscript Theorem 1 formula follows from the radial
direct-savings proof-DAG certificate producers. -/
theorem theorem_one_from_direct_savings_radial_dependency_graph
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : DirectSavingsRadialTheoremOneDependencyGraph P) :
    FinalTheoremOneStatement P := by
  exact theorem_one_from_direct_savings_dependency_graph P
    h.toDirectSavingsTheoremOneDependencyGraph

/-- Single-size displayed formula from the radial direct-savings proof-DAG
certificate producers. -/
theorem theorem_one_at_from_direct_savings_radial_dependency_graph
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : DirectSavingsRadialTheoremOneDependencyGraph P)
    (n : Nat) :
    FinalTheoremOneAtStatement P n := by
  exact theorem_one_from_direct_savings_radial_dependency_graph P h n

/-- The displayed manuscript Theorem 1 formula follows from routed proof-DAG
certificate producers. -/
theorem theorem_one_from_routed_dependency_graph
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : RoutedTheoremOneDependencyGraph P) :
    FinalTheoremOneStatement P := by
  exact theorem_one_from_dependency_graph P h.toTheoremOneDependencyGraph

/-- Single-size displayed formula from routed proof-DAG certificate
producers. -/
theorem theorem_one_at_from_routed_dependency_graph
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : RoutedTheoremOneDependencyGraph P)
    (n : Nat) :
    FinalTheoremOneAtStatement P n := by
  exact theorem_one_from_routed_dependency_graph P h n

/-- The displayed manuscript Theorem 1 formula follows from routed radial
proof-DAG certificate producers. -/
theorem theorem_one_from_routed_radial_dependency_graph
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : RoutedRadialTheoremOneDependencyGraph P) :
    FinalTheoremOneStatement P := by
  exact theorem_one_from_radial_dependency_graph P
    h.toRadialTheoremOneDependencyGraph

/-- Single-size displayed formula from routed radial proof-DAG certificate
producers. -/
theorem theorem_one_at_from_routed_radial_dependency_graph
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : RoutedRadialTheoremOneDependencyGraph P)
    (n : Nat) :
    FinalTheoremOneAtStatement P n := by
  exact theorem_one_from_routed_radial_dependency_graph P h n

end FormalizedProof
end TheoremOneManuscript
end Lollipop

/-!
Proof component 31: `Manuscript.FirstPrinciples.Boundary`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
First-principles boundary for manuscript Theorem 1.

This module is deliberately separate from the existing formalized proof stack.
It records the exact certificate boundary that would close Theorem 1 from
Euclidean lollipop geometry and Karlsson's lower construction.  The theorem at
the bottom is fully proved from these certificates through the radial
manuscript catalogue endpoint; the certificate fields are the remaining
model-specific construction obligations.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace FirstPrinciples

universe u

/-- The upper Euclidean certificate currently needed for a first-principles
Theorem 1 proof: primitive lollipop carriers, radial-outward stems, finite
carrier-intersection crossing witnesses, generic noncoincidence, and
component-wise close/intriguing savings. -/
abbrev EuclideanUpperCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u :=
  PrimitiveGeometry.PrimitiveRadialCarrierComponentSavingsUpperGeometryData P

/-- The lower certificate currently needed for a first-principles Theorem 1
proof: Karlsson's four-base table, a four-base region-increment certificate,
and sorted local blow-up arrangements with pairwise crossing and insertion
data. -/
abbrev KarlssonLowerCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u :=
  ExplicitInputs.KarlssonBaseBlowUpIncrementalLowerData P

/-- The complete current first-principles boundary for manuscript Theorem 1.

Supplying a term of this structure means all generic combinatorial, algebraic,
and finite-counting lemmas are already available in Lean; only the two concrete
model constructors below have to be built. -/
structure TheoremOneCertificates
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper : EuclideanUpperCertificate P.toProblemFamily
  lower : KarlssonLowerCertificate P.toProblemFamily

namespace EuclideanUpperCertificate

/-- Upper certificates supply actual primitive arrangements. -/
def provided_arrangements
    {P : TheoremOne.ProblemFamily.{u}}
    (h : EuclideanUpperCertificate P) :
    ∀ n : Nat, P.Arrangement n → PrimitiveGeometry.EuclideanLollipopArrangement n :=
  h.arrangement

/-- Upper certificates supply a pairwise crossing table. -/
def provided_pair_crossing_table
    {P : TheoremOne.ProblemFamily.{u}}
    (h : EuclideanUpperCertificate P) :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat :=
  h.cross

/-- Upper certificates identify each pair table entry with a finite carrier
intersection witness. -/
def provided_finite_carrier_intersections
    {P : TheoremOne.ProblemFamily.{u}}
    (h : EuclideanUpperCertificate P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      PrimitiveGeometry.PairwiseCarrierCrossingData
        (h.arrangement n A) (h.cross n A) :=
  h.pairwise_crossings

/-- Upper certificates prove distinct circle carriers for every unordered pair. -/
theorem provided_spheres_distinct
    {P : TheoremOne.ProblemFamily.{u}}
    (h : EuclideanUpperCertificate P) :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      PrimitiveGeometry.euclideanSphere ((h.arrangement n A).lollipop i).center
          ((h.arrangement n A).lollipop i).radius ≠
        PrimitiveGeometry.euclideanSphere ((h.arrangement n A).lollipop j).center
          ((h.arrangement n A).lollipop j).radius :=
  h.spheres_distinct

/-- Upper certificates prove distinct ray-supporting lines for every unordered
pair. -/
theorem provided_ray_lines_distinct
    {P : TheoremOne.ProblemFamily.{u}}
    (h : EuclideanUpperCertificate P) :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      PrimitiveGeometry.euclideanRayLine ((h.arrangement n A).lollipop i) ≠
        PrimitiveGeometry.euclideanRayLine ((h.arrangement n A).lollipop j) :=
  h.rayLines_distinct

/-- Upper certificates give component-wise savings for close pairs. -/
def provided_close_savings
    {P : TheoremOne.ProblemFamily.{u}}
    (h : EuclideanUpperCertificate P) :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => (h.arrangement n A).normalizedDirection k) i j →
        PrimitiveGeometry.PairComponentSavings ((h.arrangement n A).lollipop i)
          ((h.arrangement n A).lollipop j) 5 :=
  h.close_savings

/-- Upper certificates give component-wise savings for intriguing pairs. -/
def provided_intriguing_savings
    {P : TheoremOne.ProblemFamily.{u}}
    (h : EuclideanUpperCertificate P) :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
        (fun k => (h.arrangement n A).center k)
        (fun k => (h.arrangement n A).radius k) i j →
        PrimitiveGeometry.PairComponentSavings ((h.arrangement n A).lollipop i)
          ((h.arrangement n A).lollipop j) 5 :=
  h.intriguing_savings

/-- Upper certificates give the stronger component-wise savings for pairs that
are both close and intriguing. -/
def provided_close_intriguing_savings
    {P : TheoremOne.ProblemFamily.{u}}
    (h : EuclideanUpperCertificate P) :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => (h.arrangement n A).normalizedDirection k) i j →
      TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
        (fun k => (h.arrangement n A).center k)
        (fun k => (h.arrangement n A).radius k) i j →
        PrimitiveGeometry.PairComponentSavings ((h.arrangement n A).lollipop i)
          ((h.arrangement n A).lollipop j) 4 :=
  h.close_intriguing_savings

/-- Upper certificates supply the ordered insertion-region equation for their
pairwise crossing table. -/
def provided_region_increment
    {P : TheoremOne.ProblemFamily.{u}}
    (h : EuclideanUpperCertificate P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      OrderedIncrementalPairRegionData n (P.region n A) (h.cross n A) :=
  h.region_increment

/-- Upper certificates record that every stem is radial outward, matching the
manuscript lollipop convention. -/
theorem provided_radial_outward
    {P : TheoremOne.ProblemFamily.{u}}
    (h : EuclideanUpperCertificate P) :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i : Fin n,
      ((h.arrangement n A).lollipop i).IsRadialOutward :=
  h.radial_outward

end EuclideanUpperCertificate

namespace KarlssonLowerCertificate

/-- Lower certificates contain the four-lollipop Karlsson base arrangement. -/
def provided_base_arrangement
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonLowerCertificate P) :
    P.Arrangement 4 :=
  h.base_arrangement

/-- Lower certificates contain a four-base pair table. -/
def provided_base_pair_table
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonLowerCertificate P) :
    Fin 4 → Fin 4 → Rat :=
  h.base_pair_cross

/-- Lower certificates prove the four-base pair table is Karlsson's displayed
`5,7,7,7,7,7` table on distinct base pairs. -/
theorem provided_base_pair_table_eq_karlsson
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonLowerCertificate P) :
    ∀ a b : Fin 4, a ≠ b →
      h.base_pair_cross a b = ExplicitInputs.karlssonBasePairCrossing a b :=
  h.base_pair_cross_eq_karlsson

/-- Lower certificates prove the ordered insertion-region equation for the
four-base arrangement. -/
def provided_base_region_increment
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonLowerCertificate P) :
    OrderedIncrementalPairRegionData 4
      (P.region 4 h.base_arrangement) h.base_pair_cross :=
  h.base_region_increment

/-- Lower certificates produce one blow-up arrangement for each sorted quadruple
of cluster sizes. -/
def provided_blowup_arrangements
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonLowerCertificate P) :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n :=
  h.arrangement

/-- Lower certificates provide the canonical cardinality-cluster witness for
each sorted quadruple. -/
def provided_cluster_witnesses
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonLowerCertificate P) :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      ExplicitInputs.CardinalityClusteredKarlssonTableWitness q :=
  h.cluster_witness

/-- Lower certificates provide a pairwise crossing table for produced
arrangements. -/
def provided_pair_crossing_table
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonLowerCertificate P) :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat :=
  h.pair_cross

/-- Lower certificates prove each copy-pair value is inherited from either the
same-cluster value or the appropriate Karlsson base pair value. -/
theorem provided_pair_crossing_eq_base_copy
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonLowerCertificate P) :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        h.pair_cross n (h.arrangement n q hq) i j =
          ExplicitInputs.karlssonBaseCopyPairCrossing h.base_pair_cross
            ((h.cluster_witness n q hq).cluster) i j :=
  h.pair_cross_eq_base_copy

/-- Lower certificates supply ordered insertion-region equations for every
produced blow-up arrangement. -/
def provided_region_increment
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonLowerCertificate P) :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      OrderedIncrementalPairRegionData n
        (P.region n (h.arrangement n q hq))
        (h.pair_cross n (h.arrangement n q hq)) :=
  h.region_increment

end KarlssonLowerCertificate

namespace TheoremOneCertificates

/-- Convert the explicit first-principles boundary into the radial proof-DAG
used by the manuscript catalogue. -/
noncomputable def toRadialDependencyGraph
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : TheoremOneCertificates P) :
    FormalizedProof.RadialTheoremOneDependencyGraph P where
  upper_geometry := h.upper
  lower_karlsson_base := h.lower

end TheoremOneCertificates

/-- Manuscript Theorem 1 follows from the current first-principles boundary. -/
theorem theorem_one_from_first_principles_boundary
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : TheoremOneCertificates P) :
    FormalizedProof.FinalTheoremOneStatement P :=
  FormalizedProof.theorem_one_from_radial_dependency_graph P
    h.toRadialDependencyGraph

/-- Single-size form of Theorem 1 from the current first-principles boundary. -/
theorem theorem_one_at_from_first_principles_boundary
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : TheoremOneCertificates P)
    (n : Nat) :
    FormalizedProof.FinalTheoremOneAtStatement P n :=
  FormalizedProof.theorem_one_at_from_radial_dependency_graph P
    h.toRadialDependencyGraph n

end FirstPrinciples
end TheoremOneManuscript
end Lollipop

/-!
Proof component 32: `Manuscript.FirstPrinciples.LocalBoundary`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Local first-principles boundary for manuscript Theorem 1.

`Boundary.lean` records the theorem-facing certificate boundary after all
generic Lean proof work has been discharged.  This file refines its upper
Euclidean input by replacing the global pairwise carrier-intersection
certificate with one local certificate for each unordered pair `i < j`.
Lean assembles those local certificates before invoking the existing
first-principles theorem.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace FirstPrinciples

universe u

/-- Lower certificate with Karlsson's four-base table supplied as the six
visible unordered values plus symmetry, rather than as a universal ordered
table theorem. -/
abbrev LocalKarlssonLowerCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u :=
  ExplicitInputs.KarlssonBaseSixPairBlowUpIncrementalLowerData P

/-- Expand the six-pair lower certificate into the theorem-facing lower
certificate used by `Boundary.lean`. -/
noncomputable def localKarlssonLowerCertificate_toKarlssonLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : LocalKarlssonLowerCertificate P) :
    KarlssonLowerCertificate P :=
  h.toKarlssonBaseBlowUpIncrementalLowerData

/-- Lower certificate where the local blow-up pair-value facts are supplied
one copy-pair at a time. -/
abbrev PairLocalKarlssonLowerCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u :=
  ExplicitInputs.KarlssonBaseSixPairLocalBlowUpIncrementalLowerData P

/-- Assemble local blow-up copy-pair values into the six-pair lower
certificate used by the theorem stack. -/
noncomputable def pairLocalKarlssonLowerCertificate_toLocalKarlssonLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PairLocalKarlssonLowerCertificate P) :
    LocalKarlssonLowerCertificate P :=
  h.toKarlssonBaseSixPairBlowUpIncrementalLowerData

/-- Lower certificate with both local six-entry Karlsson base table data and
stepwise ordered insertion-region data. -/
structure StepwiseLocalKarlssonLowerCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u where
  base_arrangement : P.Arrangement 4
  base_pair_cross : Fin 4 → Fin 4 → Rat
  base_pair_table :
    ExplicitInputs.KarlssonBaseSixPairTableCertificate base_pair_cross
  base_region_increment :
    StepwiseOrderedIncrementalPairRegionData 4
      (P.region 4 base_arrangement) base_pair_cross
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  cluster_witness :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      ExplicitInputs.CardinalityClusteredKarlssonTableWitness q
  pair_cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  pair_cross_eq_base_copy :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        pair_cross n (arrangement n q hq) i j =
          ExplicitInputs.karlssonBaseCopyPairCrossing base_pair_cross
            ((cluster_witness n q hq).cluster) i j
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      StepwiseOrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

namespace StepwiseLocalKarlssonLowerCertificate

/-- Assemble stepwise lower-region data into the fully local lower certificate
used by the theorem stack. -/
noncomputable def toLocalKarlssonLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseLocalKarlssonLowerCertificate P) :
    LocalKarlssonLowerCertificate P where
  base_arrangement := h.base_arrangement
  base_pair_cross := h.base_pair_cross
  base_pair_table := h.base_pair_table
  base_region_increment :=
    h.base_region_increment.toOrderedIncrementalPairRegionData
  arrangement := h.arrangement
  cluster_witness := h.cluster_witness
  pair_cross := h.pair_cross
  pair_cross_eq_base_copy := h.pair_cross_eq_base_copy
  region_increment := by
    intro n q hq
    exact (h.region_increment n q hq).toOrderedIncrementalPairRegionData

end StepwiseLocalKarlssonLowerCertificate

/-- Lower certificate with local six-entry base table data, local copy-pair
value certificates, and stepwise ordered insertion-region data. -/
structure StepwisePairLocalKarlssonLowerCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u where
  base_arrangement : P.Arrangement 4
  base_pair_cross : Fin 4 → Fin 4 → Rat
  base_pair_table :
    ExplicitInputs.KarlssonBaseSixPairTableCertificate base_pair_cross
  base_region_increment :
    StepwiseOrderedIncrementalPairRegionData 4
      (P.region 4 base_arrangement) base_pair_cross
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  cluster_witness :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      ExplicitInputs.CardinalityClusteredKarlssonTableWitness q
  pair_cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  local_pair_cross_eq_base_copy :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        ExplicitInputs.LocalKarlssonBaseCopyPairCrossingData
          base_pair_cross ((cluster_witness n q hq).cluster)
          (pair_cross n (arrangement n q hq)) i j hij
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      StepwiseOrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

namespace StepwisePairLocalKarlssonLowerCertificate

/-- Assemble local copy-pair and local region-step data into the stepwise
lower certificate with a universal copy-pair theorem. -/
noncomputable def toStepwiseLocalKarlssonLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwisePairLocalKarlssonLowerCertificate P) :
    StepwiseLocalKarlssonLowerCertificate P where
  base_arrangement := h.base_arrangement
  base_pair_cross := h.base_pair_cross
  base_pair_table := h.base_pair_table
  base_region_increment := h.base_region_increment
  arrangement := h.arrangement
  cluster_witness := h.cluster_witness
  pair_cross := h.pair_cross
  pair_cross_eq_base_copy := by
    intro n q hq i j hij
    exact ExplicitInputs.pair_cross_eq_base_copy_from_local
      (h.local_pair_cross_eq_base_copy n q hq) i j hij
  region_increment := h.region_increment

/-- Assemble all local lower data into the six-pair lower certificate used by
the theorem stack. -/
noncomputable def toLocalKarlssonLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwisePairLocalKarlssonLowerCertificate P) :
    LocalKarlssonLowerCertificate P :=
  h.toStepwiseLocalKarlssonLowerCertificate.toLocalKarlssonLowerCertificate

end StepwisePairLocalKarlssonLowerCertificate

/-- Lower certificate with local monotone copy-pair lower-bound certificates
and stepwise ordered insertion-region data.  Unlike
`StepwisePairLocalKarlssonLowerCertificate`, this does not require exact
classification of the copy-pair crossing value; proving the Karlsson cluster
value is a lower bound is enough for the lower half of Theorem 1. -/
structure StepwisePairLocalKarlssonLowerBoundCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u where
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  cluster_witness :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      ExplicitInputs.CardinalityClusteredKarlssonTableWitness q
  pair_cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  local_pair_cross_ge_cluster :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        ExplicitInputs.LocalClusterPairLowerBoundData
          ((cluster_witness n q hq).cluster)
          (pair_cross n (arrangement n q hq)) i j hij
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      StepwiseOrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

namespace StepwisePairLocalKarlssonLowerBoundCertificate

/-- Assemble local monotone copy-pair certificates into the theorem-facing
monotone pairwise lower package. -/
noncomputable def toPairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwisePairLocalKarlssonLowerBoundCertificate P) :
    ExplicitInputs.PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData
      P where
  arrangement := h.arrangement
  cluster_witness := h.cluster_witness
  pair_cross := h.pair_cross
  pair_cross_ge_cluster := by
    intro n q hq i j hij
    exact ExplicitInputs.pair_cross_ge_cluster_from_local
      (h.local_pair_cross_ge_cluster n q hq) i j hij
  region_increment := by
    intro n q hq
    exact (h.region_increment n q hq).toOrderedIncrementalPairRegionData

end StepwisePairLocalKarlssonLowerBoundCertificate

/-- One local upper pair certificate: it bundles the finite carrier
intersection witness, generic noncoincidence facts, and all close/intriguing
component-savings branches for a single unordered pair `i < j`. -/
structure LocalEuclideanUpperPairData
    {n : Nat} (A : PrimitiveGeometry.EuclideanLollipopArrangement n)
    (cross : Fin n → Fin n → Rat) (i j : Fin n) (hij : i < j) where
  carrier_crossing :
    PrimitiveGeometry.LocalPairCarrierCrossingData A cross i j hij
  spheres_distinct :
    PrimitiveGeometry.euclideanSphere (A.lollipop i).center
        (A.lollipop i).radius ≠
      PrimitiveGeometry.euclideanSphere (A.lollipop j).center
        (A.lollipop j).radius
  rayLines_distinct :
    PrimitiveGeometry.euclideanRayLine (A.lollipop i) ≠
      PrimitiveGeometry.euclideanRayLine (A.lollipop j)
  close_savings :
    TheoremOneEndToEnd.CloseDirection.cyclicClose
      (fun k => A.normalizedDirection k) i j →
      PrimitiveGeometry.PairComponentSavings (A.lollipop i) (A.lollipop j) 5
  intriguing_savings :
    TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
      (fun k => A.center k) (fun k => A.radius k) i j →
      PrimitiveGeometry.PairComponentSavings (A.lollipop i) (A.lollipop j) 5
  close_intriguing_savings :
    TheoremOneEndToEnd.CloseDirection.cyclicClose
      (fun k => A.normalizedDirection k) i j →
    TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
      (fun k => A.center k) (fun k => A.radius k) i j →
      PrimitiveGeometry.PairComponentSavings (A.lollipop i) (A.lollipop j) 4

namespace LocalEuclideanUpperPairData

/-- The local upper pair certificate proves the generic `<= 7` crossing bound
for its pair. -/
theorem generic_cross_le_seven
    {n : Nat} {A : PrimitiveGeometry.EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
    (D : LocalEuclideanUpperPairData A cross i j hij) :
    cross i j ≤ 7 :=
  PrimitiveGeometry.localPairCarrierCrossingData_cross_le_seven
    D.carrier_crossing D.spheres_distinct D.rayLines_distinct

/-- On a close pair, the local upper pair certificate proves the `<= 5`
crossing bound consumed by the colored-Turan argument. -/
theorem close_cross_le_five
    {n : Nat} {A : PrimitiveGeometry.EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
    (D : LocalEuclideanUpperPairData A cross i j hij)
    (hclose :
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => A.normalizedDirection k) i j) :
    cross i j ≤ 5 :=
  PrimitiveGeometry.localPairCarrierCrossingData_cross_le_of_pairComponentSavings
    D.carrier_crossing (D.close_savings hclose)

/-- On an intriguing pair, the local upper pair certificate proves the `<= 5`
crossing bound consumed by the colored-Turan argument. -/
theorem intriguing_cross_le_five
    {n : Nat} {A : PrimitiveGeometry.EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
    (D : LocalEuclideanUpperPairData A cross i j hij)
    (hintriguing :
      TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
        (fun k => A.center k) (fun k => A.radius k) i j) :
    cross i j ≤ 5 :=
  PrimitiveGeometry.localPairCarrierCrossingData_cross_le_of_pairComponentSavings
    D.carrier_crossing (D.intriguing_savings hintriguing)

/-- On a pair that is both close and intriguing, the local upper pair
certificate proves the stronger `<= 4` crossing bound. -/
theorem close_intriguing_cross_le_four
    {n : Nat} {A : PrimitiveGeometry.EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
    (D : LocalEuclideanUpperPairData A cross i j hij)
    (hclose :
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => A.normalizedDirection k) i j)
    (hintriguing :
      TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
        (fun k => A.center k) (fun k => A.radius k) i j) :
    cross i j ≤ 4 :=
  PrimitiveGeometry.localPairCarrierCrossingData_cross_le_of_pairComponentSavings
    D.carrier_crossing (D.close_intriguing_savings hclose hintriguing)

end LocalEuclideanUpperPairData

/-- One local upper pair certificate whose close/intriguing savings are given
by named geometric route certificates rather than raw component-savings
objects. -/
structure RoutedLocalEuclideanUpperPairData
    {n : Nat} (A : PrimitiveGeometry.EuclideanLollipopArrangement n)
    (cross : Fin n → Fin n → Rat) (i j : Fin n) (hij : i < j) where
  carrier_crossing :
    PrimitiveGeometry.LocalPairCarrierCrossingData A cross i j hij
  spheres_distinct :
    PrimitiveGeometry.euclideanSphere (A.lollipop i).center
        (A.lollipop i).radius ≠
      PrimitiveGeometry.euclideanSphere (A.lollipop j).center
        (A.lollipop j).radius
  rayLines_distinct :
    PrimitiveGeometry.euclideanRayLine (A.lollipop i) ≠
      PrimitiveGeometry.euclideanRayLine (A.lollipop j)
  close_savings_route :
    TheoremOneEndToEnd.CloseDirection.cyclicClose
      (fun k => A.normalizedDirection k) i j →
      PrimitiveGeometry.PairComponentSavingsFiveRoute
        (A.lollipop i) (A.lollipop j)
  intriguing_savings_route :
    TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
      (fun k => A.center k) (fun k => A.radius k) i j →
      PrimitiveGeometry.PairComponentSavingsFiveRoute
        (A.lollipop i) (A.lollipop j)
  close_intriguing_savings_route :
    TheoremOneEndToEnd.CloseDirection.cyclicClose
      (fun k => A.normalizedDirection k) i j →
    TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
      (fun k => A.center k) (fun k => A.radius k) i j →
      PrimitiveGeometry.PairComponentSavingsFourRoute
        (A.lollipop i) (A.lollipop j)

namespace RoutedLocalEuclideanUpperPairData

/-- Promote a primitive routed local pair-data object to the first-principles
local upper pair record. -/
noncomputable def ofPrimitiveRoutedLocalPairData
    {n : Nat} {A : PrimitiveGeometry.EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
    (D : PrimitiveGeometry.PrimitiveRoutedLocalPairData A cross i j hij) :
    RoutedLocalEuclideanUpperPairData A cross i j hij where
  carrier_crossing := D.carrier_crossing
  spheres_distinct := D.spheres_distinct
  rayLines_distinct := D.rayLines_distinct
  close_savings_route := D.close_savings_route
  intriguing_savings_route := D.intriguing_savings_route
  close_intriguing_savings_route := D.close_intriguing_savings_route

/-- Convert routed upper pair data into the component-savings pair data used
by the current theorem stack. -/
noncomputable def toLocalEuclideanUpperPairData
    {n : Nat} {A : PrimitiveGeometry.EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
    (D : RoutedLocalEuclideanUpperPairData A cross i j hij) :
    LocalEuclideanUpperPairData A cross i j hij where
  carrier_crossing := D.carrier_crossing
  spheres_distinct := D.spheres_distinct
  rayLines_distinct := D.rayLines_distinct
  close_savings := by
    intro hclose
    exact (D.close_savings_route hclose).toPairComponentSavings
  intriguing_savings := by
    intro hintriguing
    exact (D.intriguing_savings_route hintriguing).toPairComponentSavings
  close_intriguing_savings := by
    intro hclose hintriguing
    exact (D.close_intriguing_savings_route hclose hintriguing).toPairComponentSavings

/-- The routed local upper pair certificate proves the generic `<= 7`
crossing bound for its pair. -/
theorem generic_cross_le_seven
    {n : Nat} {A : PrimitiveGeometry.EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
    (D : RoutedLocalEuclideanUpperPairData A cross i j hij) :
    cross i j ≤ 7 :=
  D.toLocalEuclideanUpperPairData.generic_cross_le_seven

/-- On a close pair, routed local upper data prove the `<= 5` crossing bound. -/
theorem close_cross_le_five
    {n : Nat} {A : PrimitiveGeometry.EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
    (D : RoutedLocalEuclideanUpperPairData A cross i j hij)
    (hclose :
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => A.normalizedDirection k) i j) :
    cross i j ≤ 5 :=
  D.toLocalEuclideanUpperPairData.close_cross_le_five hclose

/-- On an intriguing pair, routed local upper data prove the `<= 5` crossing
bound. -/
theorem intriguing_cross_le_five
    {n : Nat} {A : PrimitiveGeometry.EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
    (D : RoutedLocalEuclideanUpperPairData A cross i j hij)
    (hintriguing :
      TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
        (fun k => A.center k) (fun k => A.radius k) i j) :
    cross i j ≤ 5 :=
  D.toLocalEuclideanUpperPairData.intriguing_cross_le_five hintriguing

/-- On a pair that is both close and intriguing, routed local upper data prove
the stronger `<= 4` crossing bound. -/
theorem close_intriguing_cross_le_four
    {n : Nat} {A : PrimitiveGeometry.EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
    (D : RoutedLocalEuclideanUpperPairData A cross i j hij)
    (hclose :
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => A.normalizedDirection k) i j)
    (hintriguing :
      TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
        (fun k => A.center k) (fun k => A.radius k) i j) :
    cross i j ≤ 4 :=
  D.toLocalEuclideanUpperPairData.close_intriguing_cross_le_four
    hclose hintriguing

end RoutedLocalEuclideanUpperPairData

/-- Local upper Euclidean certificate.

This is the version closest to a first-principles coordinate calculation:
for each concrete arrangement and each local pair `i < j`, one supplies the
finite carrier-intersection set for that pair only.  Lean assembles these
local certificates into the global pairwise crossing table expected by the
theorem stack. -/
structure LocalEuclideanUpperCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u where
  arrangement :
    ∀ n : Nat, P.Arrangement n →
      PrimitiveGeometry.EuclideanLollipopArrangement n
  cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  local_pairwise_crossings :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, ∀ hij : i < j,
      PrimitiveGeometry.LocalPairCarrierCrossingData
        (arrangement n A) (cross n A) i j hij
  spheres_distinct :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      PrimitiveGeometry.euclideanSphere ((arrangement n A).lollipop i).center
          ((arrangement n A).lollipop i).radius ≠
        PrimitiveGeometry.euclideanSphere ((arrangement n A).lollipop j).center
          ((arrangement n A).lollipop j).radius
  rayLines_distinct :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      PrimitiveGeometry.euclideanRayLine ((arrangement n A).lollipop i) ≠
        PrimitiveGeometry.euclideanRayLine ((arrangement n A).lollipop j)
  close_savings :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => (arrangement n A).normalizedDirection k) i j →
        PrimitiveGeometry.PairComponentSavings ((arrangement n A).lollipop i)
          ((arrangement n A).lollipop j) 5
  intriguing_savings :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
        (fun k => (arrangement n A).center k)
        (fun k => (arrangement n A).radius k) i j →
        PrimitiveGeometry.PairComponentSavings ((arrangement n A).lollipop i)
          ((arrangement n A).lollipop j) 5
  close_intriguing_savings :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => (arrangement n A).normalizedDirection k) i j →
      TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
        (fun k => (arrangement n A).center k)
        (fun k => (arrangement n A).radius k) i j →
        PrimitiveGeometry.PairComponentSavings ((arrangement n A).lollipop i)
          ((arrangement n A).lollipop j) 4
  region_increment :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      OrderedIncrementalPairRegionData n (P.region n A) (cross n A)
  radial_outward :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i : Fin n,
      ((arrangement n A).lollipop i).IsRadialOutward

namespace LocalEuclideanUpperCertificate

/-- Assemble local one-pair carrier certificates into the global upper
certificate used by `Boundary.lean`. -/
noncomputable def toEuclideanUpperCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : LocalEuclideanUpperCertificate P) :
    EuclideanUpperCertificate P where
  arrangement := h.arrangement
  cross := h.cross
  pairwise_crossings := by
    intro n A
    exact PrimitiveGeometry.PairwiseCarrierCrossingData.ofLocal
      (h.local_pairwise_crossings n A)
  spheres_distinct := h.spheres_distinct
  rayLines_distinct := h.rayLines_distinct
  close_savings := h.close_savings
  intriguing_savings := h.intriguing_savings
  close_intriguing_savings := h.close_intriguing_savings
  region_increment := h.region_increment
  radial_outward := h.radial_outward

/-- Local upper certificates supply the local finite carrier-intersection
obligations directly. -/
def provided_local_finite_carrier_intersections
    {P : TheoremOne.ProblemFamily.{u}}
    (h : LocalEuclideanUpperCertificate P) :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, ∀ hij : i < j,
      PrimitiveGeometry.LocalPairCarrierCrossingData
        (h.arrangement n A) (h.cross n A) i j hij :=
  h.local_pairwise_crossings

/-- Local upper certificates also provide the assembled global crossing data. -/
noncomputable def provided_assembled_finite_carrier_intersections
    {P : TheoremOne.ProblemFamily.{u}}
    (h : LocalEuclideanUpperCertificate P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      PrimitiveGeometry.PairwiseCarrierCrossingData
        (h.arrangement n A) (h.cross n A) :=
  h.toEuclideanUpperCertificate.pairwise_crossings

end LocalEuclideanUpperCertificate

/-- Local upper Euclidean certificate whose ordered region recurrence is also
split into local insertion-step certificates. -/
structure StepwiseLocalEuclideanUpperCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u where
  arrangement :
    ∀ n : Nat, P.Arrangement n →
      PrimitiveGeometry.EuclideanLollipopArrangement n
  cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  local_pairwise_crossings :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, ∀ hij : i < j,
      PrimitiveGeometry.LocalPairCarrierCrossingData
        (arrangement n A) (cross n A) i j hij
  spheres_distinct :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      PrimitiveGeometry.euclideanSphere ((arrangement n A).lollipop i).center
          ((arrangement n A).lollipop i).radius ≠
        PrimitiveGeometry.euclideanSphere ((arrangement n A).lollipop j).center
          ((arrangement n A).lollipop j).radius
  rayLines_distinct :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      PrimitiveGeometry.euclideanRayLine ((arrangement n A).lollipop i) ≠
        PrimitiveGeometry.euclideanRayLine ((arrangement n A).lollipop j)
  close_savings :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => (arrangement n A).normalizedDirection k) i j →
        PrimitiveGeometry.PairComponentSavings ((arrangement n A).lollipop i)
          ((arrangement n A).lollipop j) 5
  intriguing_savings :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
        (fun k => (arrangement n A).center k)
        (fun k => (arrangement n A).radius k) i j →
        PrimitiveGeometry.PairComponentSavings ((arrangement n A).lollipop i)
          ((arrangement n A).lollipop j) 5
  close_intriguing_savings :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => (arrangement n A).normalizedDirection k) i j →
      TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
        (fun k => (arrangement n A).center k)
        (fun k => (arrangement n A).radius k) i j →
        PrimitiveGeometry.PairComponentSavings ((arrangement n A).lollipop i)
          ((arrangement n A).lollipop j) 4
  region_increment :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      StepwiseOrderedIncrementalPairRegionData n (P.region n A) (cross n A)
  radial_outward :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i : Fin n,
      ((arrangement n A).lollipop i).IsRadialOutward

namespace StepwiseLocalEuclideanUpperCertificate

/-- Assemble stepwise upper-region data into the local upper certificate used
by the theorem stack. -/
noncomputable def toLocalEuclideanUpperCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseLocalEuclideanUpperCertificate P) :
    LocalEuclideanUpperCertificate P where
  arrangement := h.arrangement
  cross := h.cross
  local_pairwise_crossings := h.local_pairwise_crossings
  spheres_distinct := h.spheres_distinct
  rayLines_distinct := h.rayLines_distinct
  close_savings := h.close_savings
  intriguing_savings := h.intriguing_savings
  close_intriguing_savings := h.close_intriguing_savings
  region_increment := by
    intro n A
    exact (h.region_increment n A).toOrderedIncrementalPairRegionData
  radial_outward := h.radial_outward

/-- Assemble stepwise local upper data into the non-radial component-savings
upper package used by monotone lower theorem endpoints. -/
noncomputable def toComponentSavingsUpperGeometryData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseLocalEuclideanUpperCertificate P) :
    PrimitiveGeometry.PrimitiveCarrierComponentSavingsUpperGeometryData P :=
  h.toLocalEuclideanUpperCertificate
    |>.toEuclideanUpperCertificate
    |>.toComponentSavingsUpperGeometryData

end StepwiseLocalEuclideanUpperCertificate

/-- Upper certificate where every unordered pair carries one local bundle of
carrier-crossing, genericity, and close/intriguing component-savings data, and
the ordered region recurrence is supplied step by step. -/
structure PairStepwiseLocalEuclideanUpperCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u where
  arrangement :
    ∀ n : Nat, P.Arrangement n →
      PrimitiveGeometry.EuclideanLollipopArrangement n
  cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  local_pair_data :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, ∀ hij : i < j,
      LocalEuclideanUpperPairData (arrangement n A) (cross n A) i j hij
  region_increment :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      StepwiseOrderedIncrementalPairRegionData n (P.region n A) (cross n A)
  radial_outward :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i : Fin n,
      ((arrangement n A).lollipop i).IsRadialOutward

namespace PairStepwiseLocalEuclideanUpperCertificate

/-- Assemble pair-local upper data into the stepwise local upper certificate
used by the theorem stack. -/
noncomputable def toStepwiseLocalEuclideanUpperCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PairStepwiseLocalEuclideanUpperCertificate P) :
    StepwiseLocalEuclideanUpperCertificate P where
  arrangement := h.arrangement
  cross := h.cross
  local_pairwise_crossings := by
    intro n A i j hij
    exact (h.local_pair_data n A i j hij).carrier_crossing
  spheres_distinct := by
    intro n A i j hij
    exact (h.local_pair_data n A i j hij).spheres_distinct
  rayLines_distinct := by
    intro n A i j hij
    exact (h.local_pair_data n A i j hij).rayLines_distinct
  close_savings := by
    intro n A i j hij hclose
    exact (h.local_pair_data n A i j hij).close_savings hclose
  intriguing_savings := by
    intro n A i j hij hintriguing
    exact (h.local_pair_data n A i j hij).intriguing_savings hintriguing
  close_intriguing_savings := by
    intro n A i j hij hclose hintriguing
    exact (h.local_pair_data n A i j hij).close_intriguing_savings
      hclose hintriguing
  region_increment := h.region_increment
  radial_outward := h.radial_outward

/-- Assemble pair-local upper data directly into the local upper certificate
with bundled ordered region recurrences. -/
noncomputable def toLocalEuclideanUpperCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PairStepwiseLocalEuclideanUpperCertificate P) :
    LocalEuclideanUpperCertificate P :=
  h.toStepwiseLocalEuclideanUpperCertificate.toLocalEuclideanUpperCertificate

/-- Assemble pair-local upper data into the component-savings upper package
used by monotone lower theorem endpoints. -/
noncomputable def toComponentSavingsUpperGeometryData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PairStepwiseLocalEuclideanUpperCertificate P) :
    PrimitiveGeometry.PrimitiveCarrierComponentSavingsUpperGeometryData P :=
  h.toStepwiseLocalEuclideanUpperCertificate.toComponentSavingsUpperGeometryData

end PairStepwiseLocalEuclideanUpperCertificate

/-- Route-based upper certificate: every unordered upper pair supplies one
local carrier/genericity bundle, and close/intriguing savings are supplied via
named geometric route constructors. -/
structure RoutedPairStepwiseLocalEuclideanUpperCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u where
  arrangement :
    ∀ n : Nat, P.Arrangement n →
      PrimitiveGeometry.EuclideanLollipopArrangement n
  cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  routed_local_pair_data :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, ∀ hij : i < j,
      RoutedLocalEuclideanUpperPairData (arrangement n A) (cross n A) i j hij
  region_increment :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      StepwiseOrderedIncrementalPairRegionData n (P.region n A) (cross n A)
  radial_outward :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i : Fin n,
      ((arrangement n A).lollipop i).IsRadialOutward

namespace RoutedPairStepwiseLocalEuclideanUpperCertificate

/-- Assemble routed upper savings data into the all-pair local upper
certificate used by the theorem stack. -/
noncomputable def toPairStepwiseLocalEuclideanUpperCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : RoutedPairStepwiseLocalEuclideanUpperCertificate P) :
    PairStepwiseLocalEuclideanUpperCertificate P where
  arrangement := h.arrangement
  cross := h.cross
  local_pair_data := by
    intro n A i j hij
    exact (h.routed_local_pair_data n A i j hij).toLocalEuclideanUpperPairData
  region_increment := h.region_increment
  radial_outward := h.radial_outward

/-- Assemble routed upper savings data directly into the stepwise local upper
certificate. -/
noncomputable def toStepwiseLocalEuclideanUpperCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : RoutedPairStepwiseLocalEuclideanUpperCertificate P) :
    StepwiseLocalEuclideanUpperCertificate P :=
  h.toPairStepwiseLocalEuclideanUpperCertificate
    |>.toStepwiseLocalEuclideanUpperCertificate

/-- Assemble routed upper data into the component-savings upper package used
by monotone lower theorem endpoints. -/
noncomputable def toComponentSavingsUpperGeometryData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : RoutedPairStepwiseLocalEuclideanUpperCertificate P) :
    PrimitiveGeometry.PrimitiveCarrierComponentSavingsUpperGeometryData P :=
  h.toStepwiseLocalEuclideanUpperCertificate.toComponentSavingsUpperGeometryData

end RoutedPairStepwiseLocalEuclideanUpperCertificate

/-- The complete local first-principles boundary for manuscript Theorem 1.

Compared with `TheoremOneCertificates`, this asks for local one-pair upper
carrier-intersection certificates, then lets Lean assemble the global upper
certificate. -/
structure LocalTheoremOneCertificates
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper : LocalEuclideanUpperCertificate P.toProblemFamily
  lower : KarlssonLowerCertificate P.toProblemFamily

namespace LocalTheoremOneCertificates

/-- Convert the local first-principles boundary to the theorem-facing boundary
by assembling the upper pairwise carrier-crossing data. -/
noncomputable def toTheoremOneCertificates
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : LocalTheoremOneCertificates P) :
    TheoremOneCertificates P where
  upper := h.upper.toEuclideanUpperCertificate
  lower := h.lower

end LocalTheoremOneCertificates

/-- Fully local first-principles boundary: local one-pair upper carrier
certificates and a six-entry symmetric Karlsson base lower certificate. -/
structure FullyLocalTheoremOneCertificates
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper : LocalEuclideanUpperCertificate P.toProblemFamily
  lower : LocalKarlssonLowerCertificate P.toProblemFamily

namespace FullyLocalTheoremOneCertificates

/-- Convert the fully local boundary into the local-upper/theorem-facing-lower
boundary. -/
noncomputable def toLocalTheoremOneCertificates
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : FullyLocalTheoremOneCertificates P) :
    LocalTheoremOneCertificates P where
  upper := h.upper
  lower :=
    localKarlssonLowerCertificate_toKarlssonLowerCertificate h.lower

/-- Convert the fully local boundary directly to the theorem-facing boundary. -/
noncomputable def toTheoremOneCertificates
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : FullyLocalTheoremOneCertificates P) :
    TheoremOneCertificates P :=
  h.toLocalTheoremOneCertificates.toTheoremOneCertificates

end FullyLocalTheoremOneCertificates

/-- Fully stepwise local first-principles boundary: local one-pair carrier
certificates, local region-step certificates, and a six-entry symmetric
Karlsson lower base table. -/
structure StepwiseFullyLocalTheoremOneCertificates
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper : StepwiseLocalEuclideanUpperCertificate P.toProblemFamily
  lower : StepwiseLocalKarlssonLowerCertificate P.toProblemFamily

namespace StepwiseFullyLocalTheoremOneCertificates

/-- Assemble all stepwise local data into the fully local theorem boundary. -/
noncomputable def toFullyLocalTheoremOneCertificates
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : StepwiseFullyLocalTheoremOneCertificates P) :
    FullyLocalTheoremOneCertificates P where
  upper := h.upper.toLocalEuclideanUpperCertificate
  lower := h.lower.toLocalKarlssonLowerCertificate

/-- Convert directly to the theorem-facing first-principles boundary. -/
noncomputable def toTheoremOneCertificates
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : StepwiseFullyLocalTheoremOneCertificates P) :
    TheoremOneCertificates P :=
  h.toFullyLocalTheoremOneCertificates.toTheoremOneCertificates

end StepwiseFullyLocalTheoremOneCertificates

/-- Strongest current local first-principles boundary: upper carrier
intersections are local per pair, lower blow-up values are local per copy pair,
and both upper/lower region recurrences are local per insertion step. -/
structure PairStepwiseFullyLocalTheoremOneCertificates
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper : StepwiseLocalEuclideanUpperCertificate P.toProblemFamily
  lower : StepwisePairLocalKarlssonLowerCertificate P.toProblemFamily

namespace PairStepwiseFullyLocalTheoremOneCertificates

/-- Assemble the strongest local boundary into the stepwise fully local
boundary with universal lower copy-pair values. -/
noncomputable def toStepwiseFullyLocalTheoremOneCertificates
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : PairStepwiseFullyLocalTheoremOneCertificates P) :
    StepwiseFullyLocalTheoremOneCertificates P where
  upper := h.upper
  lower := h.lower.toStepwiseLocalKarlssonLowerCertificate

/-- Convert directly to the theorem-facing first-principles boundary. -/
noncomputable def toTheoremOneCertificates
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : PairStepwiseFullyLocalTheoremOneCertificates P) :
    TheoremOneCertificates P :=
  h.toStepwiseFullyLocalTheoremOneCertificates.toTheoremOneCertificates

end PairStepwiseFullyLocalTheoremOneCertificates

/-- Strongest current all-pair local first-principles boundary: each upper
unordered pair supplies one local carrier/genericity/savings bundle, each lower
copy pair supplies one local inherited-value certificate, and both region
recurrences are supplied step by step. -/
structure AllPairStepwiseFullyLocalTheoremOneCertificates
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper : PairStepwiseLocalEuclideanUpperCertificate P.toProblemFamily
  lower : StepwisePairLocalKarlssonLowerCertificate P.toProblemFamily

namespace AllPairStepwiseFullyLocalTheoremOneCertificates

/-- Assemble the all-pair local boundary into the previous stepwise local
boundary. -/
noncomputable def toPairStepwiseFullyLocalTheoremOneCertificates
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : AllPairStepwiseFullyLocalTheoremOneCertificates P) :
    PairStepwiseFullyLocalTheoremOneCertificates P where
  upper := h.upper.toStepwiseLocalEuclideanUpperCertificate
  lower := h.lower

/-- Convert directly to the theorem-facing first-principles boundary. -/
noncomputable def toTheoremOneCertificates
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : AllPairStepwiseFullyLocalTheoremOneCertificates P) :
    TheoremOneCertificates P :=
  h.toPairStepwiseFullyLocalTheoremOneCertificates.toTheoremOneCertificates

end AllPairStepwiseFullyLocalTheoremOneCertificates

/-- Strongest current route-based local first-principles boundary: upper
close/intriguing savings are supplied by named geometric route constructors,
lower copy-pair values are local, and both region recurrences are stepwise. -/
structure RoutedAllPairStepwiseFullyLocalTheoremOneCertificates
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper : RoutedPairStepwiseLocalEuclideanUpperCertificate P.toProblemFamily
  lower : StepwisePairLocalKarlssonLowerCertificate P.toProblemFamily

namespace RoutedAllPairStepwiseFullyLocalTheoremOneCertificates

/-- Assemble the route-based boundary into the all-pair local boundary. -/
noncomputable def toAllPairStepwiseFullyLocalTheoremOneCertificates
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : RoutedAllPairStepwiseFullyLocalTheoremOneCertificates P) :
    AllPairStepwiseFullyLocalTheoremOneCertificates P where
  upper := h.upper.toPairStepwiseLocalEuclideanUpperCertificate
  lower := h.lower

/-- Convert directly to the theorem-facing first-principles boundary. -/
noncomputable def toTheoremOneCertificates
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : RoutedAllPairStepwiseFullyLocalTheoremOneCertificates P) :
    TheoremOneCertificates P :=
  h.toAllPairStepwiseFullyLocalTheoremOneCertificates.toTheoremOneCertificates

end RoutedAllPairStepwiseFullyLocalTheoremOneCertificates

/-- Pair-local upper boundary with monotone local lower pair inequalities.
This is the strongest lower-bound-facing local boundary: it avoids exact
copy-pair crossing classification while retaining stepwise region data. -/
structure PairStepwiseMonotoneLowerTheoremOneCertificates
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper : PairStepwiseLocalEuclideanUpperCertificate P.toProblemFamily
  lower :
    StepwisePairLocalKarlssonLowerBoundCertificate P.toProblemFamily

namespace PairStepwiseMonotoneLowerTheoremOneCertificates

/-- Convert the pair-local monotone first-principles boundary into the
formalized monotone pairwise lower subtheorem package. -/
noncomputable def toMonotonePairwiseLowerTheoremOneSubtheorems
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : PairStepwiseMonotoneLowerTheoremOneCertificates P) :
    FormalizedProof.MonotonePairwiseLowerTheoremOneSubtheorems P where
  upper_geometry := h.upper.toComponentSavingsUpperGeometryData
  lower_pairwise_bound :=
    h.lower
      |>.toPairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData

end PairStepwiseMonotoneLowerTheoremOneCertificates

/-- Route-based upper boundary with monotone local lower pair inequalities. -/
structure RoutedAllPairStepwiseMonotoneLowerTheoremOneCertificates
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper : RoutedPairStepwiseLocalEuclideanUpperCertificate P.toProblemFamily
  lower :
    StepwisePairLocalKarlssonLowerBoundCertificate P.toProblemFamily

namespace RoutedAllPairStepwiseMonotoneLowerTheoremOneCertificates

/-- Convert routed upper data and monotone local lower data into the
formalized monotone pairwise lower subtheorem package. -/
noncomputable def toMonotonePairwiseLowerTheoremOneSubtheorems
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : RoutedAllPairStepwiseMonotoneLowerTheoremOneCertificates P) :
    FormalizedProof.MonotonePairwiseLowerTheoremOneSubtheorems P where
  upper_geometry := h.upper.toComponentSavingsUpperGeometryData
  lower_pairwise_bound :=
    h.lower
      |>.toPairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData

end RoutedAllPairStepwiseMonotoneLowerTheoremOneCertificates

/-- Manuscript Theorem 1 follows from route-based all-pair local
first-principles certificates. -/
theorem theorem_one_from_routed_all_pair_stepwise_fully_local_first_principles_boundary
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : RoutedAllPairStepwiseFullyLocalTheoremOneCertificates P) :
    FormalizedProof.FinalTheoremOneStatement P :=
  theorem_one_from_first_principles_boundary P h.toTheoremOneCertificates

/-- Single-size form of Theorem 1 from route-based all-pair local
first-principles certificates. -/
theorem theorem_one_at_from_routed_all_pair_stepwise_fully_local_first_principles_boundary
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : RoutedAllPairStepwiseFullyLocalTheoremOneCertificates P)
    (n : Nat) :
    FormalizedProof.FinalTheoremOneAtStatement P n :=
  theorem_one_at_from_first_principles_boundary
    P h.toTheoremOneCertificates n

end FirstPrinciples
end TheoremOneManuscript
end Lollipop

/-!
Proof component 33: `Manuscript.EndToEndFormalization.AutomaticLower`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Automatic lower witnesses from finite primitive carrier subsets.

This module refines the theorem-facing monotone lower boundary.  Instead of
asking the construction to prove pair-crossing lower inequalities directly, it
can supply finite subsets inside each primitive pair carrier.  Mathlib's
`Finset.card_le_card` monotonicity, already packaged in
`PrimitiveGeometry.LowerWitness`, then turns those subsets into the local
Karlsson lower certificates consumed by Theorem 1.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace EndToEndFormalization
namespace AutomaticLower

open PrimitiveGeometry

universe u

noncomputable section

/-- Stepwise monotone lower certificate generated from automatic finite
carrier intersections.

For each sorted blow-up arrangement and each unordered copy pair, the
construction supplies a finite lower subset of the corresponding primitive
carrier.  The pair table used by the region recurrence is required to agree
on produced arrangements with the automatic finite-carrier table.  Lean then
derives the monotone Karlsson lower pair inequality for every copy pair. -/
structure StepwiseMonotoneCarrierSubsetLowerCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u where
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  primitive_arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      EuclideanLollipopArrangement n
  cluster_witness :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      ExplicitInputs.CardinalityClusteredKarlssonTableWitness q
  spheres_distinct :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        euclideanSphere
            ((primitive_arrangement n q hq).lollipop i).center
            ((primitive_arrangement n q hq).lollipop i).radius ≠
          euclideanSphere
            ((primitive_arrangement n q hq).lollipop j).center
            ((primitive_arrangement n q hq).lollipop j).radius
  rayLines_distinct :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        euclideanRayLine ((primitive_arrangement n q hq).lollipop i) ≠
          euclideanRayLine ((primitive_arrangement n q hq).lollipop j)
  pair_cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  pair_cross_eq_automatic :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      pair_cross n (arrangement n q hq) =
        CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable
          (primitive_arrangement n q hq)
          (spheres_distinct n q hq)
          (rayLines_distinct n q hq)
  local_lower_bound :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      ∀ i j : Fin n, i < j → Nat
  cluster_le_local_lower_bound :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        ExplicitInputs.karlssonClusterPairCrossing
            ((cluster_witness n q hq).cluster i)
            ((cluster_witness n q hq).cluster j) ≤
          (local_lower_bound n q hq i j hij : Rat)
  lower_subset :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        LocalPairCarrierLowerSubsetData
          (primitive_arrangement n q hq) i j hij
          (local_lower_bound n q hq i j hij)
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      StepwiseOrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

namespace StepwiseMonotoneCarrierSubsetLowerCertificate

/-- The automatic finite carrier table gives a local carrier-crossing
certificate for every produced copy pair. -/
noncomputable def localCarrierCrossingData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseMonotoneCarrierSubsetLowerCertificate P)
    {n : Nat} {q : QuadVec n} {hq : q ∈ sortedQuadVecs n}
    {i j : Fin n} (hij : i < j) :
    LocalPairCarrierCrossingData (h.primitive_arrangement n q hq)
      (h.pair_cross n (h.arrangement n q hq)) i j hij := by
  refine
    CompleteFormalization.FiniteCarrier.localPairCarrierCrossingDataOfFiniteCarrierEq
      (A := h.primitive_arrangement n q hq)
      (cross := h.pair_cross n (h.arrangement n q hq))
      hij
      (h.spheres_distinct n q hq i j hij)
      (h.rayLines_distinct n q hq i j hij)
      ?_
  calc
    h.pair_cross n (h.arrangement n q hq) i j =
        CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable
          (h.primitive_arrangement n q hq)
          (h.spheres_distinct n q hq)
          (h.rayLines_distinct n q hq) i j := by
      exact congrFun (congrFun (h.pair_cross_eq_automatic n q hq) i) j
    _ =
        ((CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
          (h.primitive_arrangement n q hq) hij
          (h.spheres_distinct n q hq i j hij)
          (h.rayLines_distinct n q hq i j hij)).card : Rat) := by
      exact CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable_eq_card
        (h.spheres_distinct n q hq) (h.rayLines_distinct n q hq) hij

/-- The finite lower subset supplied for one pair gives the local monotone
Karlsson lower certificate for that pair. -/
noncomputable def localClusterPairLowerBoundData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseMonotoneCarrierSubsetLowerCertificate P)
    {n : Nat} {q : QuadVec n} {hq : q ∈ sortedQuadVecs n}
    {i j : Fin n} (hij : i < j) :
    ExplicitInputs.LocalClusterPairLowerBoundData
      ((h.cluster_witness n q hq).cluster)
      (h.pair_cross n (h.arrangement n q hq)) i j hij :=
  (h.lower_subset n q hq i j hij).toLocalClusterPairLowerBoundData
    (h.localCarrierCrossingData hij)
    (h.cluster_le_local_lower_bound n q hq i j hij)

/-- Assemble automatic finite carrier lower subsets into the local monotone
lower boundary already consumed by the final Theorem 1 pipeline. -/
noncomputable def toStepwisePairLocalKarlssonLowerBoundCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseMonotoneCarrierSubsetLowerCertificate P) :
    FirstPrinciples.StepwisePairLocalKarlssonLowerBoundCertificate P where
  arrangement := h.arrangement
  cluster_witness := h.cluster_witness
  pair_cross := h.pair_cross
  local_pair_cross_ge_cluster := by
    intro n q hq i j hij
    exact h.localClusterPairLowerBoundData hij
  region_increment := h.region_increment

/-- Direct conversion to the monotone pairwise lower package used by the
Theorem 1 subtheorem stack. -/
noncomputable def toPairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseMonotoneCarrierSubsetLowerCertificate P) :
    ExplicitInputs.PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData
      P :=
  h.toStepwisePairLocalKarlssonLowerBoundCertificate
    |>.toPairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData

/-- The automatic finite carrier lower-subset boundary proves lower-bound
attainment in the displayed candidate form. -/
theorem lower_bound_attainment_choose
    (P : TheoremOne.ProblemFamily.{u})
    (h : StepwiseMonotoneCarrierSubsetLowerCertificate P) :
    ∀ n : Nat, ∃ A : P.Arrangement n,
      candidateRegionsChoose n ≤ P.region n A :=
  ExplicitInputs.PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData.lower_bound_attainment_choose
    P
    h.toPairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData

end StepwiseMonotoneCarrierSubsetLowerCertificate

/-- Common automatic-lower specialization where each finite lower subset is
required to have exactly the Nat-valued Karlsson cluster-table size
`4`, `5`, or `7`.  Lean proves internally that this Nat size coerces to the
rational lower table used by the theorem stack. -/
structure StepwiseKarlssonCarrierSubsetLowerCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u where
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  primitive_arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      EuclideanLollipopArrangement n
  cluster_witness :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      ExplicitInputs.CardinalityClusteredKarlssonTableWitness q
  spheres_distinct :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        euclideanSphere
            ((primitive_arrangement n q hq).lollipop i).center
            ((primitive_arrangement n q hq).lollipop i).radius ≠
          euclideanSphere
            ((primitive_arrangement n q hq).lollipop j).center
            ((primitive_arrangement n q hq).lollipop j).radius
  rayLines_distinct :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        euclideanRayLine ((primitive_arrangement n q hq).lollipop i) ≠
          euclideanRayLine ((primitive_arrangement n q hq).lollipop j)
  pair_cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  pair_cross_eq_automatic :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      pair_cross n (arrangement n q hq) =
        CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable
          (primitive_arrangement n q hq)
          (spheres_distinct n q hq)
          (rayLines_distinct n q hq)
  lower_subset :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        LocalPairCarrierLowerSubsetData
          (primitive_arrangement n q hq) i j hij
          (ExplicitInputs.karlssonClusterPairCrossingNat
            ((cluster_witness n q hq).cluster i)
            ((cluster_witness n q hq).cluster j))
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      StepwiseOrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

namespace StepwiseKarlssonCarrierSubsetLowerCertificate

/-- A Karlsson-sized lower-subset certificate is a special case of the more
flexible automatic monotone carrier-subset lower certificate. -/
noncomputable def toStepwiseMonotoneCarrierSubsetLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseKarlssonCarrierSubsetLowerCertificate P) :
    StepwiseMonotoneCarrierSubsetLowerCertificate P where
  arrangement := h.arrangement
  primitive_arrangement := h.primitive_arrangement
  cluster_witness := h.cluster_witness
  spheres_distinct := h.spheres_distinct
  rayLines_distinct := h.rayLines_distinct
  pair_cross := h.pair_cross
  pair_cross_eq_automatic := h.pair_cross_eq_automatic
  local_lower_bound := by
    intro n q hq i j _hij
    exact ExplicitInputs.karlssonClusterPairCrossingNat
      ((h.cluster_witness n q hq).cluster i)
      ((h.cluster_witness n q hq).cluster j)
  cluster_le_local_lower_bound := by
    intro n q hq i j _hij
    rw [ExplicitInputs.karlssonClusterPairCrossing_eq_nat]
  lower_subset := h.lower_subset
  region_increment := h.region_increment

/-- Convert Karlsson-sized carrier lower subsets directly to the monotone
local lower boundary. -/
noncomputable def toStepwisePairLocalKarlssonLowerBoundCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseKarlssonCarrierSubsetLowerCertificate P) :
    FirstPrinciples.StepwisePairLocalKarlssonLowerBoundCertificate P :=
  h.toStepwiseMonotoneCarrierSubsetLowerCertificate
    |>.toStepwisePairLocalKarlssonLowerBoundCertificate

/-- Direct conversion to the monotone pairwise lower package. -/
noncomputable def toPairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseKarlssonCarrierSubsetLowerCertificate P) :
    ExplicitInputs.PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData
      P :=
  h.toStepwisePairLocalKarlssonLowerBoundCertificate
    |>.toPairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData

end StepwiseKarlssonCarrierSubsetLowerCertificate

/-- Automatic lower specialization where the construction proves the
automatic carrier finset itself has at least the Nat-valued Karlsson
`4/5/7` size.  Lean then uses that automatic finset as the lower subset. -/
structure StepwiseKarlssonCarrierCardLowerCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u where
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  primitive_arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      EuclideanLollipopArrangement n
  cluster_witness :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      ExplicitInputs.CardinalityClusteredKarlssonTableWitness q
  spheres_distinct :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        euclideanSphere
            ((primitive_arrangement n q hq).lollipop i).center
            ((primitive_arrangement n q hq).lollipop i).radius ≠
          euclideanSphere
            ((primitive_arrangement n q hq).lollipop j).center
            ((primitive_arrangement n q hq).lollipop j).radius
  rayLines_distinct :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        euclideanRayLine ((primitive_arrangement n q hq).lollipop i) ≠
          euclideanRayLine ((primitive_arrangement n q hq).lollipop j)
  pair_cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  pair_cross_eq_automatic :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      pair_cross n (arrangement n q hq) =
        CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable
          (primitive_arrangement n q hq)
          (spheres_distinct n q hq)
          (rayLines_distinct n q hq)
  automatic_card_ge :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        ExplicitInputs.karlssonClusterPairCrossingNat
            ((cluster_witness n q hq).cluster i)
            ((cluster_witness n q hq).cluster j) ≤
          (CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
            (primitive_arrangement n q hq) hij
            (spheres_distinct n q hq i j hij)
            (rayLines_distinct n q hq i j hij)).card
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      StepwiseOrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

namespace StepwiseKarlssonCarrierCardLowerCertificate

/-- The automatic carrier finset supplies the lower subset when its
cardinality reaches the Nat-valued Karlsson table size. -/
noncomputable def toStepwiseKarlssonCarrierSubsetLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseKarlssonCarrierCardLowerCertificate P) :
    StepwiseKarlssonCarrierSubsetLowerCertificate P where
  arrangement := h.arrangement
  primitive_arrangement := h.primitive_arrangement
  cluster_witness := h.cluster_witness
  spheres_distinct := h.spheres_distinct
  rayLines_distinct := h.rayLines_distinct
  pair_cross := h.pair_cross
  pair_cross_eq_automatic := h.pair_cross_eq_automatic
  lower_subset := by
    intro n q hq i j hij
    refine
      { lowerPoints :=
          CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
            (h.primitive_arrangement n q hq) hij
            (h.spheres_distinct n q hq i j hij)
            (h.rayLines_distinct n q hq i j hij)
        lowerPoints_subset := ?_
        bound_le_card := h.automatic_card_ge n q hq i j hij }
    intro p hp
    have hp_set :
        p ∈ ((CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
          (h.primitive_arrangement n q hq) hij
          (h.spheres_distinct n q hq i j hij)
          (h.rayLines_distinct n q hq i j hij) : Finset R2) : Set R2) := by
      simpa using hp
    simpa
      [CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset_spec
        (h.spheres_distinct n q hq i j hij)
        (h.rayLines_distinct n q hq i j hij)]
      using hp_set
  region_increment := h.region_increment

/-- Convert automatic carrier-cardinality lower data to the monotone local
lower boundary. -/
noncomputable def toStepwisePairLocalKarlssonLowerBoundCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseKarlssonCarrierCardLowerCertificate P) :
    FirstPrinciples.StepwisePairLocalKarlssonLowerBoundCertificate P :=
  h.toStepwiseKarlssonCarrierSubsetLowerCertificate
    |>.toStepwisePairLocalKarlssonLowerBoundCertificate

end StepwiseKarlssonCarrierCardLowerCertificate

/-- Automatic lower specialization with the canonical sorted-quad cluster
witness built in.

Compared with `StepwiseKarlssonCarrierCardLowerCertificate`, this removes the
`cluster_witness` input from the theorem-facing boundary.  The lower
construction only has to prove that each automatic carrier finset has
cardinality at least the Nat-valued Karlsson table entry for the canonical
cluster labels of the sorted quadruple. -/
structure StepwiseCanonicalKarlssonCarrierCardLowerCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u where
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  primitive_arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      EuclideanLollipopArrangement n
  spheres_distinct :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        euclideanSphere
            ((primitive_arrangement n q hq).lollipop i).center
            ((primitive_arrangement n q hq).lollipop i).radius ≠
          euclideanSphere
            ((primitive_arrangement n q hq).lollipop j).center
            ((primitive_arrangement n q hq).lollipop j).radius
  rayLines_distinct :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        euclideanRayLine ((primitive_arrangement n q hq).lollipop i) ≠
          euclideanRayLine ((primitive_arrangement n q hq).lollipop j)
  pair_cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  pair_cross_eq_automatic :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      pair_cross n (arrangement n q hq) =
        CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable
          (primitive_arrangement n q hq)
          (spheres_distinct n q hq)
          (rayLines_distinct n q hq)
  automatic_card_ge :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        ExplicitInputs.karlssonClusterPairCrossingNat
            ((ExplicitInputs.cardinalityClusteredKarlssonTableWitnessOfSortedQuad
              q hq).cluster i)
            ((ExplicitInputs.cardinalityClusteredKarlssonTableWitnessOfSortedQuad
              q hq).cluster j) ≤
          (CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
            (primitive_arrangement n q hq) hij
            (spheres_distinct n q hq i j hij)
            (rayLines_distinct n q hq i j hij)).card
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      StepwiseOrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

namespace StepwiseCanonicalKarlssonCarrierCardLowerCertificate

/-- Add the canonical sorted-quad cluster witness to obtain the previous
automatic carrier-cardinality lower certificate. -/
noncomputable def toStepwiseKarlssonCarrierCardLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonCarrierCardLowerCertificate P) :
    StepwiseKarlssonCarrierCardLowerCertificate P where
  arrangement := h.arrangement
  primitive_arrangement := h.primitive_arrangement
  cluster_witness := fun _ q hq =>
    ExplicitInputs.cardinalityClusteredKarlssonTableWitnessOfSortedQuad q hq
  spheres_distinct := h.spheres_distinct
  rayLines_distinct := h.rayLines_distinct
  pair_cross := h.pair_cross
  pair_cross_eq_automatic := h.pair_cross_eq_automatic
  automatic_card_ge := h.automatic_card_ge
  region_increment := h.region_increment

/-- Canonical automatic carrier-cardinality lower data assemble to the
monotone local lower boundary. -/
noncomputable def toStepwisePairLocalKarlssonLowerBoundCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonCarrierCardLowerCertificate P) :
    FirstPrinciples.StepwisePairLocalKarlssonLowerBoundCertificate P :=
  h.toStepwiseKarlssonCarrierCardLowerCertificate
    |>.toStepwisePairLocalKarlssonLowerBoundCertificate

end StepwiseCanonicalKarlssonCarrierCardLowerCertificate

end

end AutomaticLower
end EndToEndFormalization
end TheoremOneManuscript
end Lollipop

/-!
Proof component 34: `Manuscript.Construction.AutomaticCardinalityWitness`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Automatic-carrier cardinality lower bounds from explicit points.

The strongest current lower boundary asks the construction to prove lower
cardinality bounds on the automatic finite carrier witnesses.  This module
turns explicit indexed carrier points into exactly those bounds.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace ConstructionFormalization

open PrimitiveGeometry

universe u

noncomputable section

/-- The Nat-valued canonical Karlsson lower-table entry for one pair in a
sorted quadruple, using Lean's canonical sorted-quad cluster witness. -/
def canonicalKarlssonLowerSize
    {n : Nat} (q : QuadVec n) (hq : q ∈ sortedQuadVecs n)
    (i j : Fin n) : Nat :=
  ExplicitInputs.karlssonClusterPairCrossingNat
    ((ExplicitInputs.cardinalityClusteredKarlssonTableWitnessOfSortedQuad
      q hq).cluster i)
    ((ExplicitInputs.cardinalityClusteredKarlssonTableWitnessOfSortedQuad
      q hq).cluster j)

/-- The canonical rational lower table used by the theorem-facing exact-carrier
boundary.  Increasing entries are the canonical Karlsson `4/5/7` sizes and
non-increasing entries are `0`, matching the pair-sum convention. -/
def canonicalKarlssonLowerTable
    {n : Nat} (q : QuadVec n) (hq : q ∈ sortedQuadVecs n) :
    Fin n → Fin n → Rat :=
  fun i j =>
    if i < j then
      (canonicalKarlssonLowerSize q hq i j : Rat)
    else
      0

/-- On increasing pairs, the canonical rational lower table is the canonical
Nat-valued Karlsson size coerced to `Rat`. -/
theorem canonicalKarlssonLowerTable_eq_size
    {n : Nat} (q : QuadVec n) (hq : q ∈ sortedQuadVecs n)
    {i j : Fin n} (hij : i < j) :
    canonicalKarlssonLowerTable q hq i j =
      (canonicalKarlssonLowerSize q hq i j : Rat) := by
  simp [canonicalKarlssonLowerTable, hij]

/-- Non-increasing entries of the canonical rational lower table are zero. -/
theorem canonicalKarlssonLowerTable_eq_zero_of_not_lt
    {n : Nat} (q : QuadVec n) (hq : q ∈ sortedQuadVecs n)
    {i j : Fin n} (hij : ¬ i < j) :
    canonicalKarlssonLowerTable q hq i j = 0 := by
  simp [canonicalKarlssonLowerTable, hij]

/-- An injective indexed family of carrier-intersection points gives the same
lower bound on the automatically produced finite carrier witness. -/
theorem indexed_points_le_arrangementPairIntersectionFinset_card
    {n bound : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n} {hij : i < j}
    (hLM :
      euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
        euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      euclideanRayLine (A.lollipop i) ≠ euclideanRayLine (A.lollipop j))
    (points : Fin bound → R2)
    (hinj : Function.Injective points)
    (hmem : ∀ k : Fin bound, points k ∈ A.pairIntersectionSet i j) :
    bound ≤
      (CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
        A hij hLM hline).card := by
  classical
  let S : Finset R2 := Finset.univ.image points
  have hSsub :
      S ⊆
        CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
          A hij hLM hline := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨k, _hk, rfl⟩
    have hp_pair : points k ∈ A.pairIntersectionSet i j := hmem k
    have hp_auto :
        points k ∈
          ((CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
            A hij hLM hline : Finset R2) : Set R2) := by
      simpa
        [CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset_spec
          hLM hline]
        using hp_pair
    simpa using hp_auto
  have hScard : S.card = bound := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ hinj]
    exact Finset.card_fin bound
  rw [← hScard]
  exact Finset.card_le_card hSsub

/-- Indexed carrier points give a rational lower bound on the automatic
carrier crossing table. -/
theorem indexed_points_le_automaticCarrierCrossingTable
    {n bound : Nat} {A : EuclideanLollipopArrangement n}
    (hLM :
      ∀ i j : Fin n, i < j →
        euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
          euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      ∀ i j : Fin n, i < j →
        euclideanRayLine (A.lollipop i) ≠
          euclideanRayLine (A.lollipop j))
    {i j : Fin n} (hij : i < j)
    (points : Fin bound → R2)
    (hinj : Function.Injective points)
    (hmem : ∀ k : Fin bound, points k ∈ A.pairIntersectionSet i j) :
    (bound : Rat) ≤
      CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable
        A hLM hline i j := by
  rw [CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable_eq_card
    hLM hline hij]
  exact_mod_cast
    indexed_points_le_arrangementPairIntersectionFinset_card
      (hLM i j hij) (hline i j hij) points hinj hmem

/-- A shared primitive anchor gives a one-point lower bound on the automatic
finite carrier witness for that pair. -/
theorem one_le_arrangementPairIntersectionFinset_card_of_common_anchor
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n} {hij : i < j}
    (hLM :
      euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
        euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      euclideanRayLine (A.lollipop i) ≠ euclideanRayLine (A.lollipop j))
    (hanchor : (A.lollipop i).anchor = (A.lollipop j).anchor) :
    1 ≤
      (CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
        A hij hLM hline).card := by
  classical
  let p : R2 := (A.lollipop i).anchor
  let S : Finset R2 := {p}
  have hSsub :
      S ⊆
        CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
          A hij hLM hline := by
    intro q hq
    have hqeq : q = p := by
      simpa [S] using hq
    subst q
    have hp_pair : p ∈ A.pairIntersectionSet i j := by
      exact arrangement_left_anchor_mem_pairIntersectionSet_of_common_anchor
        A hanchor
    have hp_auto :
        p ∈
          ((CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
            A hij hLM hline : Finset R2) : Set R2) := by
      simpa
        [CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset_spec
          hLM hline]
        using hp_pair
    simpa using hp_auto
  have hScard : S.card = 1 := by
    simp [S]
  rw [← hScard]
  exact Finset.card_le_card hSsub

/-- A shared primitive anchor gives a rational `>= 1` lower bound on the
automatic carrier crossing table. -/
theorem one_le_automaticCarrierCrossingTable_of_common_anchor
    {n : Nat} {A : EuclideanLollipopArrangement n}
    (hLM :
      ∀ i j : Fin n, i < j →
        euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
          euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      ∀ i j : Fin n, i < j →
        euclideanRayLine (A.lollipop i) ≠
          euclideanRayLine (A.lollipop j))
    {i j : Fin n} (hij : i < j)
    (hanchor : (A.lollipop i).anchor = (A.lollipop j).anchor) :
    (1 : Rat) ≤
      CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable
        A hLM hline i j := by
  rw [CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable_eq_card
    hLM hline hij]
  exact_mod_cast
    one_le_arrangementPairIntersectionFinset_card_of_common_anchor
      (hLM i j hij) (hline i j hij) hanchor

/-- Canonical lower certificate whose local lower data are explicit indexed
families of distinct primitive carrier-intersection points.

This is a construction-facing replacement for the raw
`automatic_card_ge` field: the construction gives the actual points, and Lean
converts them into the automatic carrier-cardinality inequalities. -/
structure StepwiseCanonicalKarlssonIndexedPointLowerCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u where
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  primitive_arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      EuclideanLollipopArrangement n
  spheres_distinct :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        euclideanSphere
            ((primitive_arrangement n q hq).lollipop i).center
            ((primitive_arrangement n q hq).lollipop i).radius ≠
          euclideanSphere
            ((primitive_arrangement n q hq).lollipop j).center
            ((primitive_arrangement n q hq).lollipop j).radius
  rayLines_distinct :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        euclideanRayLine ((primitive_arrangement n q hq).lollipop i) ≠
          euclideanRayLine ((primitive_arrangement n q hq).lollipop j)
  pair_cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  pair_cross_eq_automatic :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      pair_cross n (arrangement n q hq) =
        CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable
          (primitive_arrangement n q hq)
          (spheres_distinct n q hq)
          (rayLines_distinct n q hq)
  lower_points :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j,
        Fin (canonicalKarlssonLowerSize q hq i j) → R2
  lower_points_injective :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Function.Injective (lower_points n q hq i j hij)
  lower_points_mem :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        ∀ k : Fin (canonicalKarlssonLowerSize q hq i j),
          lower_points n q hq i j hij k ∈
            (primitive_arrangement n q hq).pairIntersectionSet i j
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      StepwiseOrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

namespace StepwiseCanonicalKarlssonIndexedPointLowerCertificate

/-- Explicit indexed lower points imply the canonical automatic
carrier-cardinality lower certificate. -/
noncomputable def toStepwiseCanonicalKarlssonCarrierCardLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonIndexedPointLowerCertificate P) :
    EndToEndFormalization.AutomaticLower.StepwiseCanonicalKarlssonCarrierCardLowerCertificate
      P where
  arrangement := h.arrangement
  primitive_arrangement := h.primitive_arrangement
  spheres_distinct := h.spheres_distinct
  rayLines_distinct := h.rayLines_distinct
  pair_cross := h.pair_cross
  pair_cross_eq_automatic := h.pair_cross_eq_automatic
  automatic_card_ge := by
    intro n q hq i j hij
    simpa [canonicalKarlssonLowerSize] using
      indexed_points_le_arrangementPairIntersectionFinset_card
        (h.spheres_distinct n q hq i j hij)
        (h.rayLines_distinct n q hq i j hij)
        (h.lower_points n q hq i j hij)
        (h.lower_points_injective n q hq i j hij)
        (h.lower_points_mem n q hq i j hij)
  region_increment := h.region_increment

end StepwiseCanonicalKarlssonIndexedPointLowerCertificate

/-- Canonical lower certificate whose local lower data are split into four
component-indexed point families.

Unlike the exact component-finset boundaries below, this lower-bound endpoint
does not ask the construction to cover the whole primitive carrier.  It only
asks for enough distinct points lying in the four component intersections.
Pairwise disjointness of the four indexed images and the component-size sum
let Lean enumerate their union as the canonical indexed lower-point family. -/
structure StepwiseCanonicalKarlssonComponentIndexedPointLowerCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u where
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  primitive_arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      EuclideanLollipopArrangement n
  spheres_distinct :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        euclideanSphere
            ((primitive_arrangement n q hq).lollipop i).center
            ((primitive_arrangement n q hq).lollipop i).radius ≠
          euclideanSphere
            ((primitive_arrangement n q hq).lollipop j).center
            ((primitive_arrangement n q hq).lollipop j).radius
  rayLines_distinct :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        euclideanRayLine ((primitive_arrangement n q hq).lollipop i) ≠
          euclideanRayLine ((primitive_arrangement n q hq).lollipop j)
  pair_cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  pair_cross_eq_automatic :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      pair_cross n (arrangement n q hq) =
        CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable
          (primitive_arrangement n q hq)
          (spheres_distinct n q hq)
          (rayLines_distinct n q hq)
  circle_circle_size :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Nat
  circle_ray_size :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Nat
  ray_circle_size :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Nat
  ray_ray_size :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Nat
  circle_circle_points :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Fin (circle_circle_size n q hq i j hij) → R2
  circle_ray_points :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Fin (circle_ray_size n q hq i j hij) → R2
  ray_circle_points :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Fin (ray_circle_size n q hq i j hij) → R2
  ray_ray_points :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Fin (ray_ray_size n q hq i j hij) → R2
  circle_circle_injective :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Function.Injective (circle_circle_points n q hq i j hij)
  circle_ray_injective :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Function.Injective (circle_ray_points n q hq i j hij)
  ray_circle_injective :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Function.Injective (ray_circle_points n q hq i j hij)
  ray_ray_injective :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Function.Injective (ray_ray_points n q hq i j hij)
  circle_circle_mem :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        ∀ k : Fin (circle_circle_size n q hq i j hij),
          circle_circle_points n q hq i j hij k ∈
              circleSet ((primitive_arrangement n q hq).lollipop i).center
                ((primitive_arrangement n q hq).lollipop i).radius ∧
            circle_circle_points n q hq i j hij k ∈
              circleSet ((primitive_arrangement n q hq).lollipop j).center
                ((primitive_arrangement n q hq).lollipop j).radius
  circle_ray_mem :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        ∀ k : Fin (circle_ray_size n q hq i j hij),
          circle_ray_points n q hq i j hij k ∈
              circleSet ((primitive_arrangement n q hq).lollipop i).center
                ((primitive_arrangement n q hq).lollipop i).radius ∧
            circle_ray_points n q hq i j hij k ∈
              raySet ((primitive_arrangement n q hq).lollipop j).anchor
                ((primitive_arrangement n q hq).lollipop j).rayDirection
  ray_circle_mem :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        ∀ k : Fin (ray_circle_size n q hq i j hij),
          ray_circle_points n q hq i j hij k ∈
              raySet ((primitive_arrangement n q hq).lollipop i).anchor
                ((primitive_arrangement n q hq).lollipop i).rayDirection ∧
            ray_circle_points n q hq i j hij k ∈
              circleSet ((primitive_arrangement n q hq).lollipop j).center
                ((primitive_arrangement n q hq).lollipop j).radius
  ray_ray_mem :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        ∀ k : Fin (ray_ray_size n q hq i j hij),
          ray_ray_points n q hq i j hij k ∈
              raySet ((primitive_arrangement n q hq).lollipop i).anchor
                ((primitive_arrangement n q hq).lollipop i).rayDirection ∧
            ray_ray_points n q hq i j hij k ∈
              raySet ((primitive_arrangement n q hq).lollipop j).anchor
                ((primitive_arrangement n q hq).lollipop j).rayDirection
  disjoint_circle_circle_circle_ray :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Disjoint
          (indexedCarrierFinset (circle_circle_points n q hq i j hij))
          (indexedCarrierFinset (circle_ray_points n q hq i j hij))
  disjoint_circle_circle_ray_circle :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Disjoint
          (indexedCarrierFinset (circle_circle_points n q hq i j hij))
          (indexedCarrierFinset (ray_circle_points n q hq i j hij))
  disjoint_circle_circle_ray_ray :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Disjoint
          (indexedCarrierFinset (circle_circle_points n q hq i j hij))
          (indexedCarrierFinset (ray_ray_points n q hq i j hij))
  disjoint_circle_ray_ray_circle :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Disjoint
          (indexedCarrierFinset (circle_ray_points n q hq i j hij))
          (indexedCarrierFinset (ray_circle_points n q hq i j hij))
  disjoint_circle_ray_ray_ray :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Disjoint
          (indexedCarrierFinset (circle_ray_points n q hq i j hij))
          (indexedCarrierFinset (ray_ray_points n q hq i j hij))
  disjoint_ray_circle_ray_ray :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Disjoint
          (indexedCarrierFinset (ray_circle_points n q hq i j hij))
          (indexedCarrierFinset (ray_ray_points n q hq i j hij))
  component_size_sum :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        circle_circle_size n q hq i j hij +
          circle_ray_size n q hq i j hij +
          ray_circle_size n q hq i j hij +
          ray_ray_size n q hq i j hij =
            canonicalKarlssonLowerSize q hq i j
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      StepwiseOrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

namespace StepwiseCanonicalKarlssonComponentIndexedPointLowerCertificate

/-- The finite union of the four component indexed images. -/
def lower_point_finset
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonComponentIndexedPointLowerCertificate P)
    (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n)
    (i j : Fin n) (hij : i < j) : Finset R2 :=
  componentCarrierFinset
    (indexedCarrierFinset (h.circle_circle_points n q hq i j hij))
    (indexedCarrierFinset (h.circle_ray_points n q hq i j hij))
    (indexedCarrierFinset (h.ray_circle_points n q hq i j hij))
    (indexedCarrierFinset (h.ray_ray_points n q hq i j hij))

/-- Every point in the component-indexed union lies in the primitive pair
carrier. -/
theorem lower_point_finset_mem_pairIntersectionSet
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonComponentIndexedPointLowerCertificate P)
    {n : Nat} {q : QuadVec n} {hq : q ∈ sortedQuadVecs n}
    {i j : Fin n} (hij : i < j) :
    ∀ p : R2, p ∈ h.lower_point_finset n q hq i j hij →
      p ∈ (h.primitive_arrangement n q hq).pairIntersectionSet i j := by
  classical
  refine
    componentCarrierFinset_mem_pairIntersectionSet
      (A := h.primitive_arrangement n q hq) (i := i) (j := j)
      (indexedCarrierFinset (h.circle_circle_points n q hq i j hij))
      (indexedCarrierFinset (h.circle_ray_points n q hq i j hij))
      (indexedCarrierFinset (h.ray_circle_points n q hq i j hij))
      (indexedCarrierFinset (h.ray_ray_points n q hq i j hij))
      ?_ ?_ ?_ ?_
  · intro p hp
    rcases
        (by
          simpa [indexedCarrierFinset] using hp :
          ∃ k : Fin (h.circle_circle_size n q hq i j hij),
            h.circle_circle_points n q hq i j hij k = p) with
      ⟨k, rfl⟩
    exact h.circle_circle_mem n q hq i j hij k
  · intro p hp
    rcases
        (by
          simpa [indexedCarrierFinset] using hp :
          ∃ k : Fin (h.circle_ray_size n q hq i j hij),
            h.circle_ray_points n q hq i j hij k = p) with
      ⟨k, rfl⟩
    exact h.circle_ray_mem n q hq i j hij k
  · intro p hp
    rcases
        (by
          simpa [indexedCarrierFinset] using hp :
          ∃ k : Fin (h.ray_circle_size n q hq i j hij),
            h.ray_circle_points n q hq i j hij k = p) with
      ⟨k, rfl⟩
    exact h.ray_circle_mem n q hq i j hij k
  · intro p hp
    rcases
        (by
          simpa [indexedCarrierFinset] using hp :
          ∃ k : Fin (h.ray_ray_size n q hq i j hij),
            h.ray_ray_points n q hq i j hij k = p) with
      ⟨k, rfl⟩
    exact h.ray_ray_mem n q hq i j hij k

/-- The component-indexed union has exactly the canonical lower size. -/
theorem lower_point_finset_card
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonComponentIndexedPointLowerCertificate P)
    {n : Nat} {q : QuadVec n} {hq : q ∈ sortedQuadVecs n}
    {i j : Fin n} (hij : i < j) :
    (h.lower_point_finset n q hq i j hij).card =
      canonicalKarlssonLowerSize q hq i j := by
  unfold lower_point_finset
  calc
    (componentCarrierFinset
        (indexedCarrierFinset (h.circle_circle_points n q hq i j hij))
        (indexedCarrierFinset (h.circle_ray_points n q hq i j hij))
        (indexedCarrierFinset (h.ray_circle_points n q hq i j hij))
        (indexedCarrierFinset (h.ray_ray_points n q hq i j hij))).card =
        h.circle_circle_size n q hq i j hij +
          h.circle_ray_size n q hq i j hij +
          h.ray_circle_size n q hq i j hij +
          h.ray_ray_size n q hq i j hij := by
      exact
        componentCarrierFinset_card_eq_of_disjoint
          (indexedCarrierFinset (h.circle_circle_points n q hq i j hij))
          (indexedCarrierFinset (h.circle_ray_points n q hq i j hij))
          (indexedCarrierFinset (h.ray_circle_points n q hq i j hij))
          (indexedCarrierFinset (h.ray_ray_points n q hq i j hij))
          (h.disjoint_circle_circle_circle_ray n q hq i j hij)
          (h.disjoint_circle_circle_ray_circle n q hq i j hij)
          (h.disjoint_circle_circle_ray_ray n q hq i j hij)
          (h.disjoint_circle_ray_ray_circle n q hq i j hij)
          (h.disjoint_circle_ray_ray_ray n q hq i j hij)
          (h.disjoint_ray_circle_ray_ray n q hq i j hij)
          (indexedCarrierFinset_card
            (h.circle_circle_points n q hq i j hij)
            (h.circle_circle_injective n q hq i j hij))
          (indexedCarrierFinset_card
            (h.circle_ray_points n q hq i j hij)
            (h.circle_ray_injective n q hq i j hij))
          (indexedCarrierFinset_card
            (h.ray_circle_points n q hq i j hij)
            (h.ray_circle_injective n q hq i j hij))
          (indexedCarrierFinset_card
            (h.ray_ray_points n q hq i j hij)
            (h.ray_ray_injective n q hq i j hij))
    _ = canonicalKarlssonLowerSize q hq i j := by
      exact h.component_size_sum n q hq i j hij

/-- Enumerate the component-indexed lower-point union by the canonical lower
size. -/
noncomputable def lower_points
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonComponentIndexedPointLowerCertificate P)
    (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n)
    (i j : Fin n) (hij : i < j) :
    Fin (canonicalKarlssonLowerSize q hq i j) → R2 :=
  fun k =>
    (((h.lower_point_finset n q hq i j hij).equivFinOfCardEq
      (h.lower_point_finset_card hij)).symm k : R2)

/-- The canonical enumeration of the component-indexed union is injective. -/
theorem lower_points_injective
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonComponentIndexedPointLowerCertificate P)
    {n : Nat} {q : QuadVec n} {hq : q ∈ sortedQuadVecs n}
    {i j : Fin n} (hij : i < j) :
    Function.Injective (h.lower_points n q hq i j hij) := by
  intro a b hab
  have hsub :
      ((h.lower_point_finset n q hq i j hij).equivFinOfCardEq
          (h.lower_point_finset_card hij)).symm a =
        ((h.lower_point_finset n q hq i j hij).equivFinOfCardEq
          (h.lower_point_finset_card hij)).symm b := by
    exact Subtype.ext hab
  exact
    ((h.lower_point_finset n q hq i j hij).equivFinOfCardEq
      (h.lower_point_finset_card hij)).symm.injective hsub

/-- The canonical enumeration of the component-indexed union consists of
primitive carrier-intersection points. -/
theorem lower_points_mem
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonComponentIndexedPointLowerCertificate P)
    {n : Nat} {q : QuadVec n} {hq : q ∈ sortedQuadVecs n}
    {i j : Fin n} (hij : i < j)
    (k : Fin (canonicalKarlssonLowerSize q hq i j)) :
    h.lower_points n q hq i j hij k ∈
      (h.primitive_arrangement n q hq).pairIntersectionSet i j := by
  have hp :
      h.lower_points n q hq i j hij k ∈
        h.lower_point_finset n q hq i j hij := by
    dsimp [lower_points]
    exact
      (((h.lower_point_finset n q hq i j hij).equivFinOfCardEq
        (h.lower_point_finset_card hij)).symm k).property
  exact h.lower_point_finset_mem_pairIntersectionSet hij
    (h.lower_points n q hq i j hij k) hp

/-- Component-indexed lower points are a special case of the canonical
indexed lower-point boundary. -/
noncomputable def toStepwiseCanonicalKarlssonIndexedPointLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonComponentIndexedPointLowerCertificate P) :
    StepwiseCanonicalKarlssonIndexedPointLowerCertificate P where
  arrangement := h.arrangement
  primitive_arrangement := h.primitive_arrangement
  spheres_distinct := h.spheres_distinct
  rayLines_distinct := h.rayLines_distinct
  pair_cross := h.pair_cross
  pair_cross_eq_automatic := h.pair_cross_eq_automatic
  lower_points := h.lower_points
  lower_points_injective := by
    intro n q hq i j hij
    exact h.lower_points_injective hij
  lower_points_mem := by
    intro n q hq i j hij k
    exact h.lower_points_mem hij k
  region_increment := h.region_increment

/-- Component-indexed lower points give the canonical automatic
carrier-cardinality lower certificate. -/
noncomputable def toStepwiseCanonicalKarlssonCarrierCardLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonComponentIndexedPointLowerCertificate P) :
    EndToEndFormalization.AutomaticLower.StepwiseCanonicalKarlssonCarrierCardLowerCertificate
      P :=
  h.toStepwiseCanonicalKarlssonIndexedPointLowerCertificate
    |>.toStepwiseCanonicalKarlssonCarrierCardLowerCertificate

end StepwiseCanonicalKarlssonComponentIndexedPointLowerCertificate

/-- Canonical lower certificate whose local data are exact indexed
enumerations of the whole primitive pair carrier, of the canonical
Nat-valued Karlsson `4/5/7` sizes.

Compared with `StepwiseCanonicalKarlssonIndexedPointLowerCertificate`, this
boundary asks the coordinate construction to prove that the indexed points are
not merely lower witnesses but enumerate the entire primitive carrier.  Lean
then derives membership in the carrier and equality with the automatic
finite-carrier table. -/
structure StepwiseCanonicalKarlssonExactIndexedCarrierLowerCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u where
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  primitive_arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      EuclideanLollipopArrangement n
  spheres_distinct :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        euclideanSphere
            ((primitive_arrangement n q hq).lollipop i).center
            ((primitive_arrangement n q hq).lollipop i).radius ≠
          euclideanSphere
            ((primitive_arrangement n q hq).lollipop j).center
            ((primitive_arrangement n q hq).lollipop j).radius
  rayLines_distinct :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        euclideanRayLine ((primitive_arrangement n q hq).lollipop i) ≠
          euclideanRayLine ((primitive_arrangement n q hq).lollipop j)
  pair_cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  pair_cross_eq_size :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j,
        pair_cross n (arrangement n q hq) i j =
          (canonicalKarlssonLowerSize q hq i j : Rat)
  pair_cross_eq_zero_of_not_lt :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ¬ i < j →
        pair_cross n (arrangement n q hq) i j = 0
  carrier_points :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j,
        Fin (canonicalKarlssonLowerSize q hq i j) → R2
  carrier_points_injective :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Function.Injective (carrier_points n q hq i j hij)
  carrier_points_spec :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        ((indexedCarrierFinset
          (carrier_points n q hq i j hij) : Finset R2) : Set R2) =
          (primitive_arrangement n q hq).pairIntersectionSet i j
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      StepwiseOrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

/-- Canonical exact indexed carrier lower certificate whose pair table is
given by one equality to the canonical rational Karlsson table.

This is a construction-facing variant of
`StepwiseCanonicalKarlssonExactIndexedCarrierLowerCertificate`: instead of
separate increasing-entry and non-increasing-entry pair-table fields, the
construction proves a single pointwise table equality. -/
structure StepwiseCanonicalKarlssonTableExactIndexedCarrierLowerCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u where
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  primitive_arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      EuclideanLollipopArrangement n
  spheres_distinct :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        euclideanSphere
            ((primitive_arrangement n q hq).lollipop i).center
            ((primitive_arrangement n q hq).lollipop i).radius ≠
          euclideanSphere
            ((primitive_arrangement n q hq).lollipop j).center
            ((primitive_arrangement n q hq).lollipop j).radius
  rayLines_distinct :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        euclideanRayLine ((primitive_arrangement n q hq).lollipop i) ≠
          euclideanRayLine ((primitive_arrangement n q hq).lollipop j)
  pair_cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  pair_cross_eq_canonical_table :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      pair_cross n (arrangement n q hq) =
        canonicalKarlssonLowerTable q hq
  carrier_points :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j,
        Fin (canonicalKarlssonLowerSize q hq i j) → R2
  carrier_points_injective :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Function.Injective (carrier_points n q hq i j hij)
  carrier_points_spec :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        ((indexedCarrierFinset
          (carrier_points n q hq i j hij) : Finset R2) : Set R2) =
          (primitive_arrangement n q hq).pairIntersectionSet i j
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      StepwiseOrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

/-- Canonical exact carrier lower certificate whose local data are finite
carrier sets rather than indexed enumerations.

For each increasing pair, the construction supplies the finite primitive
carrier itself, proves its coercion is exactly the pair carrier, and computes
its cardinality as the canonical Nat-valued Karlsson `4/5/7` size.  This
boundary is often closer to component-by-component coordinate calculations
than an explicit `Fin k -> R2` enumeration. -/
structure StepwiseCanonicalKarlssonFinsetExactCarrierLowerCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u where
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  primitive_arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      EuclideanLollipopArrangement n
  spheres_distinct :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        euclideanSphere
            ((primitive_arrangement n q hq).lollipop i).center
            ((primitive_arrangement n q hq).lollipop i).radius ≠
          euclideanSphere
            ((primitive_arrangement n q hq).lollipop j).center
            ((primitive_arrangement n q hq).lollipop j).radius
  rayLines_distinct :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        euclideanRayLine ((primitive_arrangement n q hq).lollipop i) ≠
          euclideanRayLine ((primitive_arrangement n q hq).lollipop j)
  pair_cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  pair_cross_eq_canonical_table :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      pair_cross n (arrangement n q hq) =
        canonicalKarlssonLowerTable q hq
  carrier_finset :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Finset R2
  carrier_finset_spec :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        ((carrier_finset n q hq i j hij : Finset R2) : Set R2) =
          (primitive_arrangement n q hq).pairIntersectionSet i j
  carrier_finset_card :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        (carrier_finset n q hq i j hij).card =
          canonicalKarlssonLowerSize q hq i j
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      StepwiseOrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

/-- Canonical finite-carrier lower certificate whose exact carrier equality is
proved from membership plus exhaustive component coverage.

For each increasing pair, the construction supplies a finite primitive carrier
set, proves every listed point is in the pair carrier, covers each of the four
circle/ray component cases, and computes the cardinality as the canonical
Nat-valued Karlsson `4/5/7` size.  Lean derives the exact carrier equality
needed by `StepwiseCanonicalKarlssonFinsetExactCarrierLowerCertificate`. -/
structure StepwiseCanonicalKarlssonComponentCoveredFinsetLowerCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u where
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  primitive_arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      EuclideanLollipopArrangement n
  spheres_distinct :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        euclideanSphere
            ((primitive_arrangement n q hq).lollipop i).center
            ((primitive_arrangement n q hq).lollipop i).radius ≠
          euclideanSphere
            ((primitive_arrangement n q hq).lollipop j).center
            ((primitive_arrangement n q hq).lollipop j).radius
  rayLines_distinct :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        euclideanRayLine ((primitive_arrangement n q hq).lollipop i) ≠
          euclideanRayLine ((primitive_arrangement n q hq).lollipop j)
  pair_cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  pair_cross_eq_canonical_table :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      pair_cross n (arrangement n q hq) =
        canonicalKarlssonLowerTable q hq
  carrier_finset :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Finset R2
  carrier_finset_mem :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        ∀ p : R2, p ∈ carrier_finset n q hq i j hij →
          p ∈ (primitive_arrangement n q hq).pairIntersectionSet i j
  carrier_finset_covers_circle_circle :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ circleSet ((primitive_arrangement n q hq).lollipop i).center
            ((primitive_arrangement n q hq).lollipop i).radius →
        p ∈ circleSet ((primitive_arrangement n q hq).lollipop j).center
            ((primitive_arrangement n q hq).lollipop j).radius →
          p ∈ carrier_finset n q hq i j hij
  carrier_finset_covers_circle_ray :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ circleSet ((primitive_arrangement n q hq).lollipop i).center
            ((primitive_arrangement n q hq).lollipop i).radius →
        p ∈ raySet ((primitive_arrangement n q hq).lollipop j).anchor
            ((primitive_arrangement n q hq).lollipop j).rayDirection →
          p ∈ carrier_finset n q hq i j hij
  carrier_finset_covers_ray_circle :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ raySet ((primitive_arrangement n q hq).lollipop i).anchor
            ((primitive_arrangement n q hq).lollipop i).rayDirection →
        p ∈ circleSet ((primitive_arrangement n q hq).lollipop j).center
            ((primitive_arrangement n q hq).lollipop j).radius →
          p ∈ carrier_finset n q hq i j hij
  carrier_finset_covers_ray_ray :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ raySet ((primitive_arrangement n q hq).lollipop i).anchor
            ((primitive_arrangement n q hq).lollipop i).rayDirection →
        p ∈ raySet ((primitive_arrangement n q hq).lollipop j).anchor
            ((primitive_arrangement n q hq).lollipop j).rayDirection →
          p ∈ carrier_finset n q hq i j hij
  carrier_finset_card :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        (carrier_finset n q hq i j hij).card =
          canonicalKarlssonLowerSize q hq i j
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      StepwiseOrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

/-- Canonical finite-carrier lower certificate whose data are separated by
the four primitive circle/ray components.

For each increasing pair, the construction supplies four component finsets,
proves membership and coverage for the corresponding circle-circle,
circle-ray, ray-circle, and ray-ray components, and computes the cardinality
of their union as the canonical Nat-valued Karlsson `4/5/7` size.  Lean
assembles the carrier finset and derives the exact carrier equality. -/
structure StepwiseCanonicalKarlssonComponentFinsetLowerCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u where
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  primitive_arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      EuclideanLollipopArrangement n
  spheres_distinct :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        euclideanSphere
            ((primitive_arrangement n q hq).lollipop i).center
            ((primitive_arrangement n q hq).lollipop i).radius ≠
          euclideanSphere
            ((primitive_arrangement n q hq).lollipop j).center
            ((primitive_arrangement n q hq).lollipop j).radius
  rayLines_distinct :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        euclideanRayLine ((primitive_arrangement n q hq).lollipop i) ≠
          euclideanRayLine ((primitive_arrangement n q hq).lollipop j)
  pair_cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  pair_cross_eq_canonical_table :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      pair_cross n (arrangement n q hq) =
        canonicalKarlssonLowerTable q hq
  circle_circle_finset :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Finset R2
  circle_ray_finset :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Finset R2
  ray_circle_finset :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Finset R2
  ray_ray_finset :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Finset R2
  circle_circle_mem :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ circle_circle_finset n q hq i j hij →
          p ∈ circleSet ((primitive_arrangement n q hq).lollipop i).center
              ((primitive_arrangement n q hq).lollipop i).radius ∧
          p ∈ circleSet ((primitive_arrangement n q hq).lollipop j).center
              ((primitive_arrangement n q hq).lollipop j).radius
  circle_ray_mem :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ circle_ray_finset n q hq i j hij →
          p ∈ circleSet ((primitive_arrangement n q hq).lollipop i).center
              ((primitive_arrangement n q hq).lollipop i).radius ∧
          p ∈ raySet ((primitive_arrangement n q hq).lollipop j).anchor
              ((primitive_arrangement n q hq).lollipop j).rayDirection
  ray_circle_mem :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ ray_circle_finset n q hq i j hij →
          p ∈ raySet ((primitive_arrangement n q hq).lollipop i).anchor
              ((primitive_arrangement n q hq).lollipop i).rayDirection ∧
          p ∈ circleSet ((primitive_arrangement n q hq).lollipop j).center
              ((primitive_arrangement n q hq).lollipop j).radius
  ray_ray_mem :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ ray_ray_finset n q hq i j hij →
          p ∈ raySet ((primitive_arrangement n q hq).lollipop i).anchor
              ((primitive_arrangement n q hq).lollipop i).rayDirection ∧
          p ∈ raySet ((primitive_arrangement n q hq).lollipop j).anchor
              ((primitive_arrangement n q hq).lollipop j).rayDirection
  circle_circle_cover :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ circleSet ((primitive_arrangement n q hq).lollipop i).center
            ((primitive_arrangement n q hq).lollipop i).radius →
        p ∈ circleSet ((primitive_arrangement n q hq).lollipop j).center
            ((primitive_arrangement n q hq).lollipop j).radius →
          p ∈ circle_circle_finset n q hq i j hij
  circle_ray_cover :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ circleSet ((primitive_arrangement n q hq).lollipop i).center
            ((primitive_arrangement n q hq).lollipop i).radius →
        p ∈ raySet ((primitive_arrangement n q hq).lollipop j).anchor
            ((primitive_arrangement n q hq).lollipop j).rayDirection →
          p ∈ circle_ray_finset n q hq i j hij
  ray_circle_cover :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ raySet ((primitive_arrangement n q hq).lollipop i).anchor
            ((primitive_arrangement n q hq).lollipop i).rayDirection →
        p ∈ circleSet ((primitive_arrangement n q hq).lollipop j).center
            ((primitive_arrangement n q hq).lollipop j).radius →
          p ∈ ray_circle_finset n q hq i j hij
  ray_ray_cover :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ raySet ((primitive_arrangement n q hq).lollipop i).anchor
            ((primitive_arrangement n q hq).lollipop i).rayDirection →
        p ∈ raySet ((primitive_arrangement n q hq).lollipop j).anchor
            ((primitive_arrangement n q hq).lollipop j).rayDirection →
          p ∈ ray_ray_finset n q hq i j hij
  carrier_finset_card :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        (componentCarrierFinset
          (circle_circle_finset n q hq i j hij)
          (circle_ray_finset n q hq i j hij)
          (ray_circle_finset n q hq i j hij)
          (ray_ray_finset n q hq i j hij)).card =
          canonicalKarlssonLowerSize q hq i j
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      StepwiseOrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

/-- Canonical component-finset lower certificate where Lean derives the union
cardinality from pairwise disjointness and individual component counts. -/
structure StepwiseCanonicalKarlssonDisjointComponentFinsetLowerCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u where
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  primitive_arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      EuclideanLollipopArrangement n
  spheres_distinct :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        euclideanSphere
            ((primitive_arrangement n q hq).lollipop i).center
            ((primitive_arrangement n q hq).lollipop i).radius ≠
          euclideanSphere
            ((primitive_arrangement n q hq).lollipop j).center
            ((primitive_arrangement n q hq).lollipop j).radius
  rayLines_distinct :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        euclideanRayLine ((primitive_arrangement n q hq).lollipop i) ≠
          euclideanRayLine ((primitive_arrangement n q hq).lollipop j)
  pair_cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  pair_cross_eq_canonical_table :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      pair_cross n (arrangement n q hq) =
        canonicalKarlssonLowerTable q hq
  circle_circle_finset :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Finset R2
  circle_ray_finset :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Finset R2
  ray_circle_finset :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Finset R2
  ray_ray_finset :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Finset R2
  circle_circle_size :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Nat
  circle_ray_size :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Nat
  ray_circle_size :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Nat
  ray_ray_size :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Nat
  circle_circle_mem :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ circle_circle_finset n q hq i j hij →
          p ∈ circleSet ((primitive_arrangement n q hq).lollipop i).center
              ((primitive_arrangement n q hq).lollipop i).radius ∧
          p ∈ circleSet ((primitive_arrangement n q hq).lollipop j).center
              ((primitive_arrangement n q hq).lollipop j).radius
  circle_ray_mem :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ circle_ray_finset n q hq i j hij →
          p ∈ circleSet ((primitive_arrangement n q hq).lollipop i).center
              ((primitive_arrangement n q hq).lollipop i).radius ∧
          p ∈ raySet ((primitive_arrangement n q hq).lollipop j).anchor
              ((primitive_arrangement n q hq).lollipop j).rayDirection
  ray_circle_mem :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ ray_circle_finset n q hq i j hij →
          p ∈ raySet ((primitive_arrangement n q hq).lollipop i).anchor
              ((primitive_arrangement n q hq).lollipop i).rayDirection ∧
          p ∈ circleSet ((primitive_arrangement n q hq).lollipop j).center
              ((primitive_arrangement n q hq).lollipop j).radius
  ray_ray_mem :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ ray_ray_finset n q hq i j hij →
          p ∈ raySet ((primitive_arrangement n q hq).lollipop i).anchor
              ((primitive_arrangement n q hq).lollipop i).rayDirection ∧
          p ∈ raySet ((primitive_arrangement n q hq).lollipop j).anchor
              ((primitive_arrangement n q hq).lollipop j).rayDirection
  circle_circle_cover :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ circleSet ((primitive_arrangement n q hq).lollipop i).center
            ((primitive_arrangement n q hq).lollipop i).radius →
        p ∈ circleSet ((primitive_arrangement n q hq).lollipop j).center
            ((primitive_arrangement n q hq).lollipop j).radius →
          p ∈ circle_circle_finset n q hq i j hij
  circle_ray_cover :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ circleSet ((primitive_arrangement n q hq).lollipop i).center
            ((primitive_arrangement n q hq).lollipop i).radius →
        p ∈ raySet ((primitive_arrangement n q hq).lollipop j).anchor
            ((primitive_arrangement n q hq).lollipop j).rayDirection →
          p ∈ circle_ray_finset n q hq i j hij
  ray_circle_cover :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ raySet ((primitive_arrangement n q hq).lollipop i).anchor
            ((primitive_arrangement n q hq).lollipop i).rayDirection →
        p ∈ circleSet ((primitive_arrangement n q hq).lollipop j).center
            ((primitive_arrangement n q hq).lollipop j).radius →
          p ∈ ray_circle_finset n q hq i j hij
  ray_ray_cover :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ raySet ((primitive_arrangement n q hq).lollipop i).anchor
            ((primitive_arrangement n q hq).lollipop i).rayDirection →
        p ∈ raySet ((primitive_arrangement n q hq).lollipop j).anchor
            ((primitive_arrangement n q hq).lollipop j).rayDirection →
          p ∈ ray_ray_finset n q hq i j hij
  disjoint_circle_circle_circle_ray :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Disjoint
          (circle_circle_finset n q hq i j hij)
          (circle_ray_finset n q hq i j hij)
  disjoint_circle_circle_ray_circle :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Disjoint
          (circle_circle_finset n q hq i j hij)
          (ray_circle_finset n q hq i j hij)
  disjoint_circle_circle_ray_ray :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Disjoint
          (circle_circle_finset n q hq i j hij)
          (ray_ray_finset n q hq i j hij)
  disjoint_circle_ray_ray_circle :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Disjoint
          (circle_ray_finset n q hq i j hij)
          (ray_circle_finset n q hq i j hij)
  disjoint_circle_ray_ray_ray :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Disjoint
          (circle_ray_finset n q hq i j hij)
          (ray_ray_finset n q hq i j hij)
  disjoint_ray_circle_ray_ray :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Disjoint
          (ray_circle_finset n q hq i j hij)
          (ray_ray_finset n q hq i j hij)
  circle_circle_card :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        (circle_circle_finset n q hq i j hij).card =
          circle_circle_size n q hq i j hij
  circle_ray_card :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        (circle_ray_finset n q hq i j hij).card =
          circle_ray_size n q hq i j hij
  ray_circle_card :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        (ray_circle_finset n q hq i j hij).card =
          ray_circle_size n q hq i j hij
  ray_ray_card :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        (ray_ray_finset n q hq i j hij).card =
          ray_ray_size n q hq i j hij
  component_size_sum :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        circle_circle_size n q hq i j hij +
          circle_ray_size n q hq i j hij +
          ray_circle_size n q hq i j hij +
          ray_ray_size n q hq i j hij =
            canonicalKarlssonLowerSize q hq i j
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      StepwiseOrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

/-- Canonical lower certificate where each component finset is generated from
an injective indexed list of concrete component points.

This is the coordinate-facing refinement of the disjoint component boundary:
the construction enumerates the four circle/ray components separately, proves
membership and coverage for each component, proves that the four images are
pairwise disjoint, and supplies the component-size sum.  Lean turns the
indexed images into finite component sets and derives all component
cardinality fields. -/
structure StepwiseCanonicalKarlssonIndexedDisjointComponentFinsetLowerCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u where
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  primitive_arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      EuclideanLollipopArrangement n
  spheres_distinct :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        euclideanSphere
            ((primitive_arrangement n q hq).lollipop i).center
            ((primitive_arrangement n q hq).lollipop i).radius ≠
          euclideanSphere
            ((primitive_arrangement n q hq).lollipop j).center
            ((primitive_arrangement n q hq).lollipop j).radius
  rayLines_distinct :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        euclideanRayLine ((primitive_arrangement n q hq).lollipop i) ≠
          euclideanRayLine ((primitive_arrangement n q hq).lollipop j)
  pair_cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  pair_cross_eq_canonical_table :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      pair_cross n (arrangement n q hq) =
        canonicalKarlssonLowerTable q hq
  circle_circle_size :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Nat
  circle_ray_size :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Nat
  ray_circle_size :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Nat
  ray_ray_size :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Nat
  circle_circle_points :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Fin (circle_circle_size n q hq i j hij) → R2
  circle_ray_points :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Fin (circle_ray_size n q hq i j hij) → R2
  ray_circle_points :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Fin (ray_circle_size n q hq i j hij) → R2
  ray_ray_points :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Fin (ray_ray_size n q hq i j hij) → R2
  circle_circle_injective :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Function.Injective (circle_circle_points n q hq i j hij)
  circle_ray_injective :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Function.Injective (circle_ray_points n q hq i j hij)
  ray_circle_injective :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Function.Injective (ray_circle_points n q hq i j hij)
  ray_ray_injective :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Function.Injective (ray_ray_points n q hq i j hij)
  circle_circle_mem :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        ∀ k : Fin (circle_circle_size n q hq i j hij),
          circle_circle_points n q hq i j hij k ∈
              circleSet ((primitive_arrangement n q hq).lollipop i).center
                ((primitive_arrangement n q hq).lollipop i).radius ∧
            circle_circle_points n q hq i j hij k ∈
              circleSet ((primitive_arrangement n q hq).lollipop j).center
                ((primitive_arrangement n q hq).lollipop j).radius
  circle_ray_mem :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        ∀ k : Fin (circle_ray_size n q hq i j hij),
          circle_ray_points n q hq i j hij k ∈
              circleSet ((primitive_arrangement n q hq).lollipop i).center
                ((primitive_arrangement n q hq).lollipop i).radius ∧
            circle_ray_points n q hq i j hij k ∈
              raySet ((primitive_arrangement n q hq).lollipop j).anchor
                ((primitive_arrangement n q hq).lollipop j).rayDirection
  ray_circle_mem :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        ∀ k : Fin (ray_circle_size n q hq i j hij),
          ray_circle_points n q hq i j hij k ∈
              raySet ((primitive_arrangement n q hq).lollipop i).anchor
                ((primitive_arrangement n q hq).lollipop i).rayDirection ∧
            ray_circle_points n q hq i j hij k ∈
              circleSet ((primitive_arrangement n q hq).lollipop j).center
                ((primitive_arrangement n q hq).lollipop j).radius
  ray_ray_mem :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        ∀ k : Fin (ray_ray_size n q hq i j hij),
          ray_ray_points n q hq i j hij k ∈
              raySet ((primitive_arrangement n q hq).lollipop i).anchor
                ((primitive_arrangement n q hq).lollipop i).rayDirection ∧
            ray_ray_points n q hq i j hij k ∈
              raySet ((primitive_arrangement n q hq).lollipop j).anchor
                ((primitive_arrangement n q hq).lollipop j).rayDirection
  circle_circle_cover :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ circleSet ((primitive_arrangement n q hq).lollipop i).center
            ((primitive_arrangement n q hq).lollipop i).radius →
        p ∈ circleSet ((primitive_arrangement n q hq).lollipop j).center
            ((primitive_arrangement n q hq).lollipop j).radius →
          ∃ k : Fin (circle_circle_size n q hq i j hij),
            circle_circle_points n q hq i j hij k = p
  circle_ray_cover :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ circleSet ((primitive_arrangement n q hq).lollipop i).center
            ((primitive_arrangement n q hq).lollipop i).radius →
        p ∈ raySet ((primitive_arrangement n q hq).lollipop j).anchor
            ((primitive_arrangement n q hq).lollipop j).rayDirection →
          ∃ k : Fin (circle_ray_size n q hq i j hij),
            circle_ray_points n q hq i j hij k = p
  ray_circle_cover :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ raySet ((primitive_arrangement n q hq).lollipop i).anchor
            ((primitive_arrangement n q hq).lollipop i).rayDirection →
        p ∈ circleSet ((primitive_arrangement n q hq).lollipop j).center
            ((primitive_arrangement n q hq).lollipop j).radius →
          ∃ k : Fin (ray_circle_size n q hq i j hij),
            ray_circle_points n q hq i j hij k = p
  ray_ray_cover :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ raySet ((primitive_arrangement n q hq).lollipop i).anchor
            ((primitive_arrangement n q hq).lollipop i).rayDirection →
        p ∈ raySet ((primitive_arrangement n q hq).lollipop j).anchor
            ((primitive_arrangement n q hq).lollipop j).rayDirection →
          ∃ k : Fin (ray_ray_size n q hq i j hij),
            ray_ray_points n q hq i j hij k = p
  disjoint_circle_circle_circle_ray :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Disjoint
          (indexedCarrierFinset (circle_circle_points n q hq i j hij))
          (indexedCarrierFinset (circle_ray_points n q hq i j hij))
  disjoint_circle_circle_ray_circle :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Disjoint
          (indexedCarrierFinset (circle_circle_points n q hq i j hij))
          (indexedCarrierFinset (ray_circle_points n q hq i j hij))
  disjoint_circle_circle_ray_ray :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Disjoint
          (indexedCarrierFinset (circle_circle_points n q hq i j hij))
          (indexedCarrierFinset (ray_ray_points n q hq i j hij))
  disjoint_circle_ray_ray_circle :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Disjoint
          (indexedCarrierFinset (circle_ray_points n q hq i j hij))
          (indexedCarrierFinset (ray_circle_points n q hq i j hij))
  disjoint_circle_ray_ray_ray :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Disjoint
          (indexedCarrierFinset (circle_ray_points n q hq i j hij))
          (indexedCarrierFinset (ray_ray_points n q hq i j hij))
  disjoint_ray_circle_ray_ray :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Disjoint
          (indexedCarrierFinset (ray_circle_points n q hq i j hij))
          (indexedCarrierFinset (ray_ray_points n q hq i j hij))
  component_size_sum :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        circle_circle_size n q hq i j hij +
          circle_ray_size n q hq i j hij +
          ray_circle_size n q hq i j hij +
          ray_ray_size n q hq i j hij =
            canonicalKarlssonLowerSize q hq i j
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      StepwiseOrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

namespace StepwiseCanonicalKarlssonExactIndexedCarrierLowerCertificate

/-- Exact indexed carrier lower data are a special case of the indexed
lower-point certificate. -/
noncomputable def toStepwiseCanonicalKarlssonIndexedPointLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonExactIndexedCarrierLowerCertificate P) :
    StepwiseCanonicalKarlssonIndexedPointLowerCertificate P where
  arrangement := h.arrangement
  primitive_arrangement := h.primitive_arrangement
  spheres_distinct := h.spheres_distinct
  rayLines_distinct := h.rayLines_distinct
  pair_cross := h.pair_cross
  pair_cross_eq_automatic := by
    intro n q hq
    funext i j
    by_cases hij : i < j
    · calc
        h.pair_cross n (h.arrangement n q hq) i j =
            (canonicalKarlssonLowerSize q hq i j : Rat) := by
          exact h.pair_cross_eq_size n q hq i j hij
        _ =
            CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable
              (h.primitive_arrangement n q hq)
              (h.spheres_distinct n q hq)
              (h.rayLines_distinct n q hq) i j := by
          exact
            (automaticCarrierCrossingTable_eq_of_indexedCarrier
              (h.spheres_distinct n q hq)
              (h.rayLines_distinct n q hq)
              hij
              (h.carrier_points n q hq i j hij)
              (h.carrier_points_injective n q hq i j hij)
              (h.carrier_points_spec n q hq i j hij)).symm
    · calc
        h.pair_cross n (h.arrangement n q hq) i j = 0 := by
          exact h.pair_cross_eq_zero_of_not_lt n q hq i j hij
        _ =
            CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable
              (h.primitive_arrangement n q hq)
              (h.spheres_distinct n q hq)
              (h.rayLines_distinct n q hq) i j := by
          simp [CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable,
            hij]
  lower_points := h.carrier_points
  lower_points_injective := h.carrier_points_injective
  lower_points_mem := by
    intro n q hq i j hij k
    exact
      indexedCarrier_mem_pairIntersectionSet_of_spec
        (h.carrier_points n q hq i j hij)
        (h.carrier_points_spec n q hq i j hij) k
  region_increment := h.region_increment

/-- Exact indexed carrier lower data imply the canonical automatic
carrier-cardinality lower certificate. -/
noncomputable def toStepwiseCanonicalKarlssonCarrierCardLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonExactIndexedCarrierLowerCertificate P) :
    EndToEndFormalization.AutomaticLower.StepwiseCanonicalKarlssonCarrierCardLowerCertificate
      P :=
  h.toStepwiseCanonicalKarlssonIndexedPointLowerCertificate
    |>.toStepwiseCanonicalKarlssonCarrierCardLowerCertificate

end StepwiseCanonicalKarlssonExactIndexedCarrierLowerCertificate

namespace StepwiseCanonicalKarlssonTableExactIndexedCarrierLowerCertificate

/-- A one-equation canonical-table exact carrier certificate implies the
existing exact indexed carrier lower certificate. -/
noncomputable def toStepwiseCanonicalKarlssonExactIndexedCarrierLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonTableExactIndexedCarrierLowerCertificate P) :
    StepwiseCanonicalKarlssonExactIndexedCarrierLowerCertificate P where
  arrangement := h.arrangement
  primitive_arrangement := h.primitive_arrangement
  spheres_distinct := h.spheres_distinct
  rayLines_distinct := h.rayLines_distinct
  pair_cross := h.pair_cross
  pair_cross_eq_size := by
    intro n q hq i j hij
    rw [h.pair_cross_eq_canonical_table n q hq]
    exact canonicalKarlssonLowerTable_eq_size q hq hij
  pair_cross_eq_zero_of_not_lt := by
    intro n q hq i j hij
    rw [h.pair_cross_eq_canonical_table n q hq]
    exact canonicalKarlssonLowerTable_eq_zero_of_not_lt q hq hij
  carrier_points := h.carrier_points
  carrier_points_injective := h.carrier_points_injective
  carrier_points_spec := h.carrier_points_spec
  region_increment := h.region_increment

/-- A one-equation canonical-table exact carrier certificate also gives the
indexed lower-point certificate. -/
noncomputable def toStepwiseCanonicalKarlssonIndexedPointLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonTableExactIndexedCarrierLowerCertificate P) :
    StepwiseCanonicalKarlssonIndexedPointLowerCertificate P :=
  h.toStepwiseCanonicalKarlssonExactIndexedCarrierLowerCertificate
    |>.toStepwiseCanonicalKarlssonIndexedPointLowerCertificate

/-- A one-equation canonical-table exact carrier certificate gives the
canonical automatic carrier-cardinality lower certificate. -/
noncomputable def toStepwiseCanonicalKarlssonCarrierCardLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonTableExactIndexedCarrierLowerCertificate P) :
    EndToEndFormalization.AutomaticLower.StepwiseCanonicalKarlssonCarrierCardLowerCertificate
      P :=
  h.toStepwiseCanonicalKarlssonExactIndexedCarrierLowerCertificate
    |>.toStepwiseCanonicalKarlssonCarrierCardLowerCertificate

end StepwiseCanonicalKarlssonTableExactIndexedCarrierLowerCertificate

namespace StepwiseCanonicalKarlssonFinsetExactCarrierLowerCertificate

/-- The automatic finite carrier produced from generic noncoincidence is the
same finset as the construction-supplied exact carrier. -/
theorem automaticCarrierFinset_eq_carrierFinset
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonFinsetExactCarrierLowerCertificate P)
    {n : Nat} {q : QuadVec n} {hq : q ∈ sortedQuadVecs n}
    {i j : Fin n} (hij : i < j) :
    CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
        (h.primitive_arrangement n q hq) hij
        (h.spheres_distinct n q hq i j hij)
        (h.rayLines_distinct n q hq i j hij) =
      h.carrier_finset n q hq i j hij := by
  classical
  apply Finset.ext
  intro p
  constructor
  · intro hp
    have hp_set :
        p ∈
          ((CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
            (h.primitive_arrangement n q hq) hij
            (h.spheres_distinct n q hq i j hij)
            (h.rayLines_distinct n q hq i j hij) : Finset R2) : Set R2) := by
      simpa using hp
    have hp_pair :
        p ∈ (h.primitive_arrangement n q hq).pairIntersectionSet i j := by
      simpa
        [CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset_spec
          (h.spheres_distinct n q hq i j hij)
          (h.rayLines_distinct n q hq i j hij)]
        using hp_set
    have hp_carrier :
        p ∈ ((h.carrier_finset n q hq i j hij : Finset R2) : Set R2) := by
      simpa [h.carrier_finset_spec n q hq i j hij] using hp_pair
    simpa using hp_carrier
  · intro hp
    have hp_carrier :
        p ∈ ((h.carrier_finset n q hq i j hij : Finset R2) : Set R2) := by
      simpa using hp
    have hp_pair :
        p ∈ (h.primitive_arrangement n q hq).pairIntersectionSet i j := by
      simpa [h.carrier_finset_spec n q hq i j hij] using hp_carrier
    have hp_auto :
        p ∈
          ((CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
            (h.primitive_arrangement n q hq) hij
            (h.spheres_distinct n q hq i j hij)
            (h.rayLines_distinct n q hq i j hij) : Finset R2) : Set R2) := by
      simpa
        [CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset_spec
          (h.spheres_distinct n q hq i j hij)
          (h.rayLines_distinct n q hq i j hij)]
        using hp_pair
    simpa using hp_auto

/-- Finset-exact carrier lower data give the canonical automatic
carrier-cardinality lower certificate. -/
noncomputable def toStepwiseCanonicalKarlssonCarrierCardLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonFinsetExactCarrierLowerCertificate P) :
    EndToEndFormalization.AutomaticLower.StepwiseCanonicalKarlssonCarrierCardLowerCertificate
      P where
  arrangement := h.arrangement
  primitive_arrangement := h.primitive_arrangement
  spheres_distinct := h.spheres_distinct
  rayLines_distinct := h.rayLines_distinct
  pair_cross := h.pair_cross
  pair_cross_eq_automatic := by
    intro n q hq
    funext i j
    by_cases hij : i < j
    · calc
        h.pair_cross n (h.arrangement n q hq) i j =
            canonicalKarlssonLowerTable q hq i j := by
          rw [h.pair_cross_eq_canonical_table n q hq]
        _ = (canonicalKarlssonLowerSize q hq i j : Rat) := by
          exact canonicalKarlssonLowerTable_eq_size q hq hij
        _ =
            CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable
              (h.primitive_arrangement n q hq)
              (h.spheres_distinct n q hq)
              (h.rayLines_distinct n q hq) i j := by
          rw [CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable_eq_card
            (h.spheres_distinct n q hq) (h.rayLines_distinct n q hq) hij]
          rw [h.automaticCarrierFinset_eq_carrierFinset hij]
          exact_mod_cast (h.carrier_finset_card n q hq i j hij).symm
    · calc
        h.pair_cross n (h.arrangement n q hq) i j =
            canonicalKarlssonLowerTable q hq i j := by
          rw [h.pair_cross_eq_canonical_table n q hq]
        _ = 0 := canonicalKarlssonLowerTable_eq_zero_of_not_lt q hq hij
        _ =
            CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable
              (h.primitive_arrangement n q hq)
              (h.spheres_distinct n q hq)
              (h.rayLines_distinct n q hq) i j := by
          simp [CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable,
            hij]
  automatic_card_ge := by
    intro n q hq i j hij
    have hcard :
        (CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
          (h.primitive_arrangement n q hq) hij
          (h.spheres_distinct n q hq i j hij)
          (h.rayLines_distinct n q hq i j hij)).card =
          canonicalKarlssonLowerSize q hq i j := by
      rw [h.automaticCarrierFinset_eq_carrierFinset hij]
      exact h.carrier_finset_card n q hq i j hij
    simpa [canonicalKarlssonLowerSize] using le_of_eq hcard.symm
  region_increment := h.region_increment

end StepwiseCanonicalKarlssonFinsetExactCarrierLowerCertificate

namespace StepwiseCanonicalKarlssonComponentCoveredFinsetLowerCertificate

/-- Component coverage supplies the exact carrier equality required by the
finset-exact lower boundary. -/
theorem carrier_finset_spec
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonComponentCoveredFinsetLowerCertificate P)
    {n : Nat} {q : QuadVec n} {hq : q ∈ sortedQuadVecs n}
    {i j : Fin n} (hij : i < j) :
    ((h.carrier_finset n q hq i j hij : Finset R2) : Set R2) =
      (h.primitive_arrangement n q hq).pairIntersectionSet i j :=
  carrierFinset_spec_of_component_covers
    (A := h.primitive_arrangement n q hq) (i := i) (j := j)
    (h.carrier_finset n q hq i j hij)
    (h.carrier_finset_mem n q hq i j hij)
    (h.carrier_finset_covers_circle_circle n q hq i j hij)
    (h.carrier_finset_covers_circle_ray n q hq i j hij)
    (h.carrier_finset_covers_ray_circle n q hq i j hij)
    (h.carrier_finset_covers_ray_ray n q hq i j hij)

/-- Component-covered finite carrier data are a special case of finset-exact
carrier lower data. -/
noncomputable def toStepwiseCanonicalKarlssonFinsetExactCarrierLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonComponentCoveredFinsetLowerCertificate P) :
    StepwiseCanonicalKarlssonFinsetExactCarrierLowerCertificate P where
  arrangement := h.arrangement
  primitive_arrangement := h.primitive_arrangement
  spheres_distinct := h.spheres_distinct
  rayLines_distinct := h.rayLines_distinct
  pair_cross := h.pair_cross
  pair_cross_eq_canonical_table := h.pair_cross_eq_canonical_table
  carrier_finset := h.carrier_finset
  carrier_finset_spec := by
    intro n q hq i j hij
    exact h.carrier_finset_spec hij
  carrier_finset_card := h.carrier_finset_card
  region_increment := h.region_increment

/-- Component-covered finite carrier data give the canonical automatic
carrier-cardinality lower certificate. -/
noncomputable def toStepwiseCanonicalKarlssonCarrierCardLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonComponentCoveredFinsetLowerCertificate P) :
    EndToEndFormalization.AutomaticLower.StepwiseCanonicalKarlssonCarrierCardLowerCertificate
      P :=
  h.toStepwiseCanonicalKarlssonFinsetExactCarrierLowerCertificate
    |>.toStepwiseCanonicalKarlssonCarrierCardLowerCertificate

end StepwiseCanonicalKarlssonComponentCoveredFinsetLowerCertificate

namespace StepwiseCanonicalKarlssonComponentFinsetLowerCertificate

/-- The carrier finset assembled from the four construction-supplied component
finsets. -/
def carrier_finset
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonComponentFinsetLowerCertificate P)
    (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n)
    (i j : Fin n) (hij : i < j) : Finset R2 :=
  componentCarrierFinset
    (h.circle_circle_finset n q hq i j hij)
    (h.circle_ray_finset n q hq i j hij)
    (h.ray_circle_finset n q hq i j hij)
    (h.ray_ray_finset n q hq i j hij)

/-- The component finsets assemble to the full primitive pair carrier. -/
theorem carrier_finset_spec
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonComponentFinsetLowerCertificate P)
    {n : Nat} {q : QuadVec n} {hq : q ∈ sortedQuadVecs n}
    {i j : Fin n} (hij : i < j) :
    ((h.carrier_finset n q hq i j hij : Finset R2) : Set R2) =
      (h.primitive_arrangement n q hq).pairIntersectionSet i j :=
  componentCarrierFinset_spec_of_component_covers
    (A := h.primitive_arrangement n q hq) (i := i) (j := j)
    (h.circle_circle_finset n q hq i j hij)
    (h.circle_ray_finset n q hq i j hij)
    (h.ray_circle_finset n q hq i j hij)
    (h.ray_ray_finset n q hq i j hij)
    (h.circle_circle_mem n q hq i j hij)
    (h.circle_ray_mem n q hq i j hij)
    (h.ray_circle_mem n q hq i j hij)
    (h.ray_ray_mem n q hq i j hij)
    (h.circle_circle_cover n q hq i j hij)
    (h.circle_ray_cover n q hq i j hij)
    (h.ray_circle_cover n q hq i j hij)
    (h.ray_ray_cover n q hq i j hij)

/-- Component-separated finite carrier data are a special case of the
component-covered finite-carrier lower boundary. -/
noncomputable def toStepwiseCanonicalKarlssonComponentCoveredFinsetLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonComponentFinsetLowerCertificate P) :
    StepwiseCanonicalKarlssonComponentCoveredFinsetLowerCertificate P where
  arrangement := h.arrangement
  primitive_arrangement := h.primitive_arrangement
  spheres_distinct := h.spheres_distinct
  rayLines_distinct := h.rayLines_distinct
  pair_cross := h.pair_cross
  pair_cross_eq_canonical_table := h.pair_cross_eq_canonical_table
  carrier_finset := h.carrier_finset
  carrier_finset_mem := by
    intro n q hq i j hij p hp
    exact
      componentCarrierFinset_mem_pairIntersectionSet
        (A := h.primitive_arrangement n q hq) (i := i) (j := j)
        (h.circle_circle_finset n q hq i j hij)
        (h.circle_ray_finset n q hq i j hij)
        (h.ray_circle_finset n q hq i j hij)
        (h.ray_ray_finset n q hq i j hij)
        (h.circle_circle_mem n q hq i j hij)
        (h.circle_ray_mem n q hq i j hij)
        (h.ray_circle_mem n q hq i j hij)
        (h.ray_ray_mem n q hq i j hij) p hp
  carrier_finset_covers_circle_circle := by
    intro n q hq i j hij p hp_i hp_j
    simp [carrier_finset, componentCarrierFinset,
      h.circle_circle_cover n q hq i j hij p hp_i hp_j]
  carrier_finset_covers_circle_ray := by
    intro n q hq i j hij p hp_i hp_j
    simp [carrier_finset, componentCarrierFinset,
      h.circle_ray_cover n q hq i j hij p hp_i hp_j]
  carrier_finset_covers_ray_circle := by
    intro n q hq i j hij p hp_i hp_j
    simp [carrier_finset, componentCarrierFinset,
      h.ray_circle_cover n q hq i j hij p hp_i hp_j]
  carrier_finset_covers_ray_ray := by
    intro n q hq i j hij p hp_i hp_j
    simp [carrier_finset, componentCarrierFinset,
      h.ray_ray_cover n q hq i j hij p hp_i hp_j]
  carrier_finset_card := h.carrier_finset_card
  region_increment := h.region_increment

/-- Component-separated finite carrier data are a special case of the
finset-exact carrier lower boundary. -/
noncomputable def toStepwiseCanonicalKarlssonFinsetExactCarrierLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonComponentFinsetLowerCertificate P) :
    StepwiseCanonicalKarlssonFinsetExactCarrierLowerCertificate P :=
  h.toStepwiseCanonicalKarlssonComponentCoveredFinsetLowerCertificate
    |>.toStepwiseCanonicalKarlssonFinsetExactCarrierLowerCertificate

/-- Component-separated finite carrier data give the canonical automatic
carrier-cardinality lower certificate. -/
noncomputable def toStepwiseCanonicalKarlssonCarrierCardLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonComponentFinsetLowerCertificate P) :
    EndToEndFormalization.AutomaticLower.StepwiseCanonicalKarlssonCarrierCardLowerCertificate
      P :=
  h.toStepwiseCanonicalKarlssonComponentCoveredFinsetLowerCertificate
    |>.toStepwiseCanonicalKarlssonCarrierCardLowerCertificate

end StepwiseCanonicalKarlssonComponentFinsetLowerCertificate

namespace StepwiseCanonicalKarlssonDisjointComponentFinsetLowerCertificate

/-- The carrier finset assembled from the four disjoint construction-supplied
component finsets. -/
def carrier_finset
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonDisjointComponentFinsetLowerCertificate P)
    (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n)
    (i j : Fin n) (hij : i < j) : Finset R2 :=
  componentCarrierFinset
    (h.circle_circle_finset n q hq i j hij)
    (h.circle_ray_finset n q hq i j hij)
    (h.ray_circle_finset n q hq i j hij)
    (h.ray_ray_finset n q hq i j hij)

/-- Pairwise disjointness and the four component cardinalities compute the
canonical lower carrier size. -/
theorem carrier_finset_card
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonDisjointComponentFinsetLowerCertificate P)
    {n : Nat} {q : QuadVec n} {hq : q ∈ sortedQuadVecs n}
    {i j : Fin n} (hij : i < j) :
    (h.carrier_finset n q hq i j hij).card =
      canonicalKarlssonLowerSize q hq i j := by
  unfold carrier_finset
  calc
    (componentCarrierFinset
        (h.circle_circle_finset n q hq i j hij)
        (h.circle_ray_finset n q hq i j hij)
        (h.ray_circle_finset n q hq i j hij)
        (h.ray_ray_finset n q hq i j hij)).card =
        h.circle_circle_size n q hq i j hij +
          h.circle_ray_size n q hq i j hij +
          h.ray_circle_size n q hq i j hij +
          h.ray_ray_size n q hq i j hij := by
      exact
        componentCarrierFinset_card_eq_of_disjoint
          (h.circle_circle_finset n q hq i j hij)
          (h.circle_ray_finset n q hq i j hij)
          (h.ray_circle_finset n q hq i j hij)
          (h.ray_ray_finset n q hq i j hij)
          (h.disjoint_circle_circle_circle_ray n q hq i j hij)
          (h.disjoint_circle_circle_ray_circle n q hq i j hij)
          (h.disjoint_circle_circle_ray_ray n q hq i j hij)
          (h.disjoint_circle_ray_ray_circle n q hq i j hij)
          (h.disjoint_circle_ray_ray_ray n q hq i j hij)
          (h.disjoint_ray_circle_ray_ray n q hq i j hij)
          (h.circle_circle_card n q hq i j hij)
          (h.circle_ray_card n q hq i j hij)
          (h.ray_circle_card n q hq i j hij)
          (h.ray_ray_card n q hq i j hij)
    _ = canonicalKarlssonLowerSize q hq i j := by
      exact h.component_size_sum n q hq i j hij

/-- Disjoint component-count lower data are a special case of the
component-separated finite-carrier lower boundary. -/
noncomputable def toStepwiseCanonicalKarlssonComponentFinsetLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonDisjointComponentFinsetLowerCertificate P) :
    StepwiseCanonicalKarlssonComponentFinsetLowerCertificate P where
  arrangement := h.arrangement
  primitive_arrangement := h.primitive_arrangement
  spheres_distinct := h.spheres_distinct
  rayLines_distinct := h.rayLines_distinct
  pair_cross := h.pair_cross
  pair_cross_eq_canonical_table := h.pair_cross_eq_canonical_table
  circle_circle_finset := h.circle_circle_finset
  circle_ray_finset := h.circle_ray_finset
  ray_circle_finset := h.ray_circle_finset
  ray_ray_finset := h.ray_ray_finset
  circle_circle_mem := h.circle_circle_mem
  circle_ray_mem := h.circle_ray_mem
  ray_circle_mem := h.ray_circle_mem
  ray_ray_mem := h.ray_ray_mem
  circle_circle_cover := h.circle_circle_cover
  circle_ray_cover := h.circle_ray_cover
  ray_circle_cover := h.ray_circle_cover
  ray_ray_cover := h.ray_ray_cover
  carrier_finset_card := by
    intro n q hq i j hij
    exact h.carrier_finset_card hij
  region_increment := h.region_increment

/-- Disjoint component-count lower data also give the component-covered
finite-carrier lower boundary. -/
noncomputable def toStepwiseCanonicalKarlssonComponentCoveredFinsetLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonDisjointComponentFinsetLowerCertificate P) :
    StepwiseCanonicalKarlssonComponentCoveredFinsetLowerCertificate P :=
  h.toStepwiseCanonicalKarlssonComponentFinsetLowerCertificate
    |>.toStepwiseCanonicalKarlssonComponentCoveredFinsetLowerCertificate

/-- Disjoint component-count lower data also give the finset-exact carrier
lower boundary. -/
noncomputable def toStepwiseCanonicalKarlssonFinsetExactCarrierLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonDisjointComponentFinsetLowerCertificate P) :
    StepwiseCanonicalKarlssonFinsetExactCarrierLowerCertificate P :=
  h.toStepwiseCanonicalKarlssonComponentFinsetLowerCertificate
    |>.toStepwiseCanonicalKarlssonFinsetExactCarrierLowerCertificate

/-- Disjoint component-count lower data give the canonical automatic
carrier-cardinality lower certificate. -/
noncomputable def toStepwiseCanonicalKarlssonCarrierCardLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonDisjointComponentFinsetLowerCertificate P) :
    EndToEndFormalization.AutomaticLower.StepwiseCanonicalKarlssonCarrierCardLowerCertificate
      P :=
  h.toStepwiseCanonicalKarlssonComponentFinsetLowerCertificate
    |>.toStepwiseCanonicalKarlssonCarrierCardLowerCertificate

end StepwiseCanonicalKarlssonDisjointComponentFinsetLowerCertificate

namespace StepwiseCanonicalKarlssonIndexedDisjointComponentFinsetLowerCertificate

/-- The circle-circle component finset generated by the indexed component
points. -/
def circle_circle_finset
    {P : TheoremOne.ProblemFamily.{u}}
    (h :
      StepwiseCanonicalKarlssonIndexedDisjointComponentFinsetLowerCertificate
        P)
    (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n)
    (i j : Fin n) (hij : i < j) : Finset R2 :=
  indexedCarrierFinset (h.circle_circle_points n q hq i j hij)

/-- The circle-ray component finset generated by the indexed component
points. -/
def circle_ray_finset
    {P : TheoremOne.ProblemFamily.{u}}
    (h :
      StepwiseCanonicalKarlssonIndexedDisjointComponentFinsetLowerCertificate
        P)
    (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n)
    (i j : Fin n) (hij : i < j) : Finset R2 :=
  indexedCarrierFinset (h.circle_ray_points n q hq i j hij)

/-- The ray-circle component finset generated by the indexed component
points. -/
def ray_circle_finset
    {P : TheoremOne.ProblemFamily.{u}}
    (h :
      StepwiseCanonicalKarlssonIndexedDisjointComponentFinsetLowerCertificate
        P)
    (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n)
    (i j : Fin n) (hij : i < j) : Finset R2 :=
  indexedCarrierFinset (h.ray_circle_points n q hq i j hij)

/-- The ray-ray component finset generated by the indexed component points. -/
def ray_ray_finset
    {P : TheoremOne.ProblemFamily.{u}}
    (h :
      StepwiseCanonicalKarlssonIndexedDisjointComponentFinsetLowerCertificate
        P)
    (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n)
    (i j : Fin n) (hij : i < j) : Finset R2 :=
  indexedCarrierFinset (h.ray_ray_points n q hq i j hij)

/-- Indexed disjoint component data are a special case of the disjoint
component-finset lower boundary. -/
noncomputable def toStepwiseCanonicalKarlssonDisjointComponentFinsetLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h :
      StepwiseCanonicalKarlssonIndexedDisjointComponentFinsetLowerCertificate
        P) :
    StepwiseCanonicalKarlssonDisjointComponentFinsetLowerCertificate P where
  arrangement := h.arrangement
  primitive_arrangement := h.primitive_arrangement
  spheres_distinct := h.spheres_distinct
  rayLines_distinct := h.rayLines_distinct
  pair_cross := h.pair_cross
  pair_cross_eq_canonical_table := h.pair_cross_eq_canonical_table
  circle_circle_finset := h.circle_circle_finset
  circle_ray_finset := h.circle_ray_finset
  ray_circle_finset := h.ray_circle_finset
  ray_ray_finset := h.ray_ray_finset
  circle_circle_size := h.circle_circle_size
  circle_ray_size := h.circle_ray_size
  ray_circle_size := h.ray_circle_size
  ray_ray_size := h.ray_ray_size
  circle_circle_mem := by
    intro n q hq i j hij p hp
    rcases
        (by
          simpa [circle_circle_finset, indexedCarrierFinset] using hp :
          ∃ k : Fin (h.circle_circle_size n q hq i j hij),
            h.circle_circle_points n q hq i j hij k = p) with
      ⟨k, rfl⟩
    exact h.circle_circle_mem n q hq i j hij k
  circle_ray_mem := by
    intro n q hq i j hij p hp
    rcases
        (by
          simpa [circle_ray_finset, indexedCarrierFinset] using hp :
          ∃ k : Fin (h.circle_ray_size n q hq i j hij),
            h.circle_ray_points n q hq i j hij k = p) with
      ⟨k, rfl⟩
    exact h.circle_ray_mem n q hq i j hij k
  ray_circle_mem := by
    intro n q hq i j hij p hp
    rcases
        (by
          simpa [ray_circle_finset, indexedCarrierFinset] using hp :
          ∃ k : Fin (h.ray_circle_size n q hq i j hij),
            h.ray_circle_points n q hq i j hij k = p) with
      ⟨k, rfl⟩
    exact h.ray_circle_mem n q hq i j hij k
  ray_ray_mem := by
    intro n q hq i j hij p hp
    rcases
        (by
          simpa [ray_ray_finset, indexedCarrierFinset] using hp :
          ∃ k : Fin (h.ray_ray_size n q hq i j hij),
            h.ray_ray_points n q hq i j hij k = p) with
      ⟨k, rfl⟩
    exact h.ray_ray_mem n q hq i j hij k
  circle_circle_cover := by
    intro n q hq i j hij p hp_i hp_j
    rcases h.circle_circle_cover n q hq i j hij p hp_i hp_j with ⟨k, hk⟩
    exact
      (by
        simpa [circle_circle_finset, indexedCarrierFinset] using
          (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hk⟩))
  circle_ray_cover := by
    intro n q hq i j hij p hp_i hp_j
    rcases h.circle_ray_cover n q hq i j hij p hp_i hp_j with ⟨k, hk⟩
    exact
      (by
        simpa [circle_ray_finset, indexedCarrierFinset] using
          (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hk⟩))
  ray_circle_cover := by
    intro n q hq i j hij p hp_i hp_j
    rcases h.ray_circle_cover n q hq i j hij p hp_i hp_j with ⟨k, hk⟩
    exact
      (by
        simpa [ray_circle_finset, indexedCarrierFinset] using
          (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hk⟩))
  ray_ray_cover := by
    intro n q hq i j hij p hp_i hp_j
    rcases h.ray_ray_cover n q hq i j hij p hp_i hp_j with ⟨k, hk⟩
    exact
      (by
        simpa [ray_ray_finset, indexedCarrierFinset] using
          (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hk⟩))
  disjoint_circle_circle_circle_ray := by
    intro n q hq i j hij
    simpa [circle_circle_finset, circle_ray_finset] using
      h.disjoint_circle_circle_circle_ray n q hq i j hij
  disjoint_circle_circle_ray_circle := by
    intro n q hq i j hij
    simpa [circle_circle_finset, ray_circle_finset] using
      h.disjoint_circle_circle_ray_circle n q hq i j hij
  disjoint_circle_circle_ray_ray := by
    intro n q hq i j hij
    simpa [circle_circle_finset, ray_ray_finset] using
      h.disjoint_circle_circle_ray_ray n q hq i j hij
  disjoint_circle_ray_ray_circle := by
    intro n q hq i j hij
    simpa [circle_ray_finset, ray_circle_finset] using
      h.disjoint_circle_ray_ray_circle n q hq i j hij
  disjoint_circle_ray_ray_ray := by
    intro n q hq i j hij
    simpa [circle_ray_finset, ray_ray_finset] using
      h.disjoint_circle_ray_ray_ray n q hq i j hij
  disjoint_ray_circle_ray_ray := by
    intro n q hq i j hij
    simpa [ray_circle_finset, ray_ray_finset] using
      h.disjoint_ray_circle_ray_ray n q hq i j hij
  circle_circle_card := by
    intro n q hq i j hij
    simpa [circle_circle_finset] using
      indexedCarrierFinset_card
        (h.circle_circle_points n q hq i j hij)
        (h.circle_circle_injective n q hq i j hij)
  circle_ray_card := by
    intro n q hq i j hij
    simpa [circle_ray_finset] using
      indexedCarrierFinset_card
        (h.circle_ray_points n q hq i j hij)
        (h.circle_ray_injective n q hq i j hij)
  ray_circle_card := by
    intro n q hq i j hij
    simpa [ray_circle_finset] using
      indexedCarrierFinset_card
        (h.ray_circle_points n q hq i j hij)
        (h.ray_circle_injective n q hq i j hij)
  ray_ray_card := by
    intro n q hq i j hij
    simpa [ray_ray_finset] using
      indexedCarrierFinset_card
        (h.ray_ray_points n q hq i j hij)
        (h.ray_ray_injective n q hq i j hij)
  component_size_sum := h.component_size_sum
  region_increment := h.region_increment

/-- Indexed disjoint component data also give the component-separated
finite-carrier lower boundary. -/
noncomputable def toStepwiseCanonicalKarlssonComponentFinsetLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h :
      StepwiseCanonicalKarlssonIndexedDisjointComponentFinsetLowerCertificate
        P) :
    StepwiseCanonicalKarlssonComponentFinsetLowerCertificate P :=
  h.toStepwiseCanonicalKarlssonDisjointComponentFinsetLowerCertificate
    |>.toStepwiseCanonicalKarlssonComponentFinsetLowerCertificate

/-- Indexed disjoint component data also give the component-covered
finite-carrier lower boundary. -/
noncomputable def toStepwiseCanonicalKarlssonComponentCoveredFinsetLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h :
      StepwiseCanonicalKarlssonIndexedDisjointComponentFinsetLowerCertificate
        P) :
    StepwiseCanonicalKarlssonComponentCoveredFinsetLowerCertificate P :=
  h.toStepwiseCanonicalKarlssonDisjointComponentFinsetLowerCertificate
    |>.toStepwiseCanonicalKarlssonComponentCoveredFinsetLowerCertificate

/-- Indexed disjoint component data also give the finset-exact carrier lower
boundary. -/
noncomputable def toStepwiseCanonicalKarlssonFinsetExactCarrierLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h :
      StepwiseCanonicalKarlssonIndexedDisjointComponentFinsetLowerCertificate
        P) :
    StepwiseCanonicalKarlssonFinsetExactCarrierLowerCertificate P :=
  h.toStepwiseCanonicalKarlssonDisjointComponentFinsetLowerCertificate
    |>.toStepwiseCanonicalKarlssonFinsetExactCarrierLowerCertificate

/-- Exact indexed disjoint component data also give the weaker
component-indexed lower-point boundary.

The component point families, membership, injectivity, disjointness, and size
sum are copied directly.  The automatic pair-table equality is inherited from
the exact component-coverage route. -/
noncomputable def toStepwiseCanonicalKarlssonComponentIndexedPointLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h :
      StepwiseCanonicalKarlssonIndexedDisjointComponentFinsetLowerCertificate
        P) :
    StepwiseCanonicalKarlssonComponentIndexedPointLowerCertificate P where
  arrangement := h.arrangement
  primitive_arrangement := h.primitive_arrangement
  spheres_distinct := h.spheres_distinct
  rayLines_distinct := h.rayLines_distinct
  pair_cross := h.pair_cross
  pair_cross_eq_automatic :=
    h.toStepwiseCanonicalKarlssonFinsetExactCarrierLowerCertificate
      |>.toStepwiseCanonicalKarlssonCarrierCardLowerCertificate
      |>.pair_cross_eq_automatic
  circle_circle_size := h.circle_circle_size
  circle_ray_size := h.circle_ray_size
  ray_circle_size := h.ray_circle_size
  ray_ray_size := h.ray_ray_size
  circle_circle_points := h.circle_circle_points
  circle_ray_points := h.circle_ray_points
  ray_circle_points := h.ray_circle_points
  ray_ray_points := h.ray_ray_points
  circle_circle_injective := h.circle_circle_injective
  circle_ray_injective := h.circle_ray_injective
  ray_circle_injective := h.ray_circle_injective
  ray_ray_injective := h.ray_ray_injective
  circle_circle_mem := h.circle_circle_mem
  circle_ray_mem := h.circle_ray_mem
  ray_circle_mem := h.ray_circle_mem
  ray_ray_mem := h.ray_ray_mem
  disjoint_circle_circle_circle_ray :=
    h.disjoint_circle_circle_circle_ray
  disjoint_circle_circle_ray_circle :=
    h.disjoint_circle_circle_ray_circle
  disjoint_circle_circle_ray_ray :=
    h.disjoint_circle_circle_ray_ray
  disjoint_circle_ray_ray_circle :=
    h.disjoint_circle_ray_ray_circle
  disjoint_circle_ray_ray_ray :=
    h.disjoint_circle_ray_ray_ray
  disjoint_ray_circle_ray_ray :=
    h.disjoint_ray_circle_ray_ray
  component_size_sum := h.component_size_sum
  region_increment := h.region_increment

/-- Indexed disjoint component data give the canonical automatic
carrier-cardinality lower certificate. -/
noncomputable def toStepwiseCanonicalKarlssonCarrierCardLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h :
      StepwiseCanonicalKarlssonIndexedDisjointComponentFinsetLowerCertificate
        P) :
    EndToEndFormalization.AutomaticLower.StepwiseCanonicalKarlssonCarrierCardLowerCertificate
      P :=
  h.toStepwiseCanonicalKarlssonDisjointComponentFinsetLowerCertificate
    |>.toStepwiseCanonicalKarlssonCarrierCardLowerCertificate

end StepwiseCanonicalKarlssonIndexedDisjointComponentFinsetLowerCertificate

end

end ConstructionFormalization
end TheoremOneManuscript
end Lollipop

/-!
Proof component 35: `EndToEnd.Lower.BlowUp`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
# Four-cluster blow-up

This file combines:

1. the exact rational four-lollipop base;
2. the corrected polynomial four-crossing family inside each cluster;
3. openness of all strict inter-cluster pair chambers;
4. genericization without changing any pair count;
5. the repository's existing finite cluster-cardinality algebra.

The result is a concrete `LowerCrossingRealization` for every admissible
quadruple, with no caller-supplied geometry certificate.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace Lower
namespace BlowUp

open Set BigOperators
open TheoremOneManuscript ExplicitInputs

/-- Canonical cluster label supplied by the existing finite equivalence. -/
def clusterOf {n : ℕ} (q : QuadVec n) (hq : q ∈ quadVecs n) :
    Fin n → Fin 4 :=
  canonicalQuadCluster q hq

/-- Position of a member inside its canonical cluster. -/
def rankOf {n : ℕ} (q : QuadVec n) (hq : q ∈ quadVecs n)
    (i : Fin n) : ℕ :=
  (quadClusterEquiv q hq i).2.1

@[simp] theorem clusterOf_eq_first {n : ℕ}
    (q : QuadVec n) (hq : q ∈ quadVecs n) (i : Fin n) :
    clusterOf q hq i = (quadClusterEquiv q hq i).1 := rfl

/-- Rank is strictly smaller than its cluster size. -/
theorem rankOf_lt_clusterSize {n : ℕ}
    (q : QuadVec n) (hq : q ∈ quadVecs n) (i : Fin n) :
    rankOf q hq i < (q (clusterOf q hq i) : ℕ) :=
  (quadClusterEquiv q hq i).2.2

/-- Every cluster size is at most the total size. -/
theorem clusterSize_le_n {n : ℕ}
    (q : QuadVec n) (hq : q ∈ quadVecs n) (r : Fin 4) :
    (q r : ℕ) ≤ n := by
  have hsum : (∑ s : Fin 4, quadEntry q s) = (n : ℚ) := by
    simpa [Fin.sum_univ_four] using quadEntry_sum_eq_of_mem hq
  have hnonneg : ∀ s : Fin 4, (0 : ℚ) ≤ quadEntry q s := by
    intro s
    unfold quadEntry
    positivity
  have hr : quadEntry q r ≤ n := by
    have hle : quadEntry q r ≤ ∑ s : Fin 4, quadEntry q s :=
      Finset.single_le_sum (fun s _ => hnonneg s) (Finset.mem_univ r)
    rwa [hsum] at hle
  have hr' : (((q r : ℕ) : ℚ) ≤ (n : ℚ)) := by
    simpa [quadEntry] using hr
  exact_mod_cast hr'

/-- A small, distinct positive parameter for each member. -/
def memberParameter {n : ℕ}
    (ε : ℝ) (q : QuadVec n) (hq : q ∈ quadVecs n) (i : Fin n) : ℝ :=
  ε * ((rankOf q hq i + 1 : ℕ) : ℝ) / (n + 1 : ℕ)

/-- Member parameters lie in `(0,ε)` when `ε>0`. -/
theorem memberParameter_bounds {n : ℕ}
    {ε : ℝ} (hε : 0 < ε)
    (q : QuadVec n) (hq : q ∈ quadVecs n) (i : Fin n) :
    0 < memberParameter ε q hq i ∧
      memberParameter ε q hq i < ε := by
  have hrank := rankOf_lt_clusterSize q hq i
  have hsize := clusterSize_le_n q hq (clusterOf q hq i)
  have hnum : rankOf q hq i + 1 ≤ n := by omega
  have hden : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hratio0 : 0 < (((rankOf q hq i + 1 : ℕ) : ℝ) /
      (n + 1 : ℕ)) := by positivity
  have hratio1 : (((rankOf q hq i + 1 : ℕ) : ℝ) /
      (n + 1 : ℕ)) < 1 := by
    rw [div_lt_one hden]
    exact_mod_cast (Nat.lt_succ_of_le hnum)
  unfold memberParameter
  constructor
  · positivity
  · have hlt : ε *
        ((((rankOf q hq i + 1 : ℕ) : ℝ) / (n + 1 : ℕ))) < ε :=
      mul_lt_of_lt_one_right hε hratio1
    simpa [mul_div_assoc] using hlt

/-- Two different members in the same cluster receive different parameters. -/
theorem memberParameter_ne_of_same_cluster {n : ℕ}
    {ε : ℝ} (hε : 0 < ε)
    (q : QuadVec n) (hq : q ∈ quadVecs n)
    {i j : Fin n} (hij : i ≠ j)
    (hcluster : clusterOf q hq i = clusterOf q hq j) :
    memberParameter ε q hq i ≠ memberParameter ε q hq j := by
  intro ht
  have hrank : rankOf q hq i = rankOf q hq j := by
    unfold memberParameter at ht
    have hε0 : ε ≠ 0 := hε.ne'
    have hden0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have ht' :
        ε * ((((rankOf q hq i + 1 : ℕ) : ℝ) / (n + 1 : ℕ))) =
          ε * ((((rankOf q hq j + 1 : ℕ) : ℝ) / (n + 1 : ℕ))) := by
      simpa [mul_div_assoc] using ht
    have hratio :
        (((rankOf q hq i + 1 : ℕ) : ℝ) / (n + 1 : ℕ)) =
          (((rankOf q hq j + 1 : ℕ) : ℝ) / (n + 1 : ℕ)) :=
      mul_left_cancel₀ hε0 ht'
    rw [div_left_inj' hden0] at hratio
    exact Nat.succ.inj (Nat.cast_injective hratio)
  apply hij
  apply (quadClusterEquiv q hq).injective
  change (quadClusterEquiv q hq i).1 = (quadClusterEquiv q hq j).1 at hcluster
  change (quadClusterEquiv q hq i).2.1 =
    (quadClusterEquiv q hq j).2.1 at hrank
  rcases hxi : quadClusterEquiv q hq i with ⟨ri, ki⟩
  rcases hxj : quadClusterEquiv q hq j with ⟨rj, kj⟩
  rw [hxi, hxj] at hcluster hrank
  dsimp at hcluster hrank ⊢
  subst rj
  congr
  exact Fin.ext hrank

/-- Crossing code determined only by two base clusters. -/
def interClusterCode (r s : Fin 4) : StrictPairCode :=
  RationalBase.baseCode r s

theorem interClusterCode_swap (r s : Fin 4) :
    interClusterCode s r = (interClusterCode r s).swap :=
  RationalBase.baseCode_swap r s

/-- The numerical contribution of a base-cluster code is Karlsson's symmetric
`4/5/7` table for distinct clusters. -/
theorem interClusterCode_crossings
    {r s : Fin 4} (hrs : r ≠ s) :
    ((interClusterCode r s).crossings : ℚ) =
      karlssonClusterPairCrossing r s := by
  fin_cases r <;> fin_cases s <;>
    first
    | contradiction
    | norm_num [interClusterCode, RationalBase.baseCode,
        StrictPairCode.crossings, StrictPairCode.five,
        StrictPairCode.seven, StrictPairCode.swap,
        MixedCode.crossings, karlssonClusterPairCrossing]

@[simp] theorem strictPairCode_swap_swap (code : StrictPairCode) :
    code.swap.swap = code := by
  rcases code with ⟨left, right, rayRay⟩
  rfl

@[simp] theorem strictPairCode_four_swap_crossings :
    StrictPairCode.four.swap.crossings = 4 := by
  rfl

/-- A one-sided nonnegative interval inside an open neighborhood of `0`. -/
theorem exists_nonneg_interval_subset_of_isOpen
    {U : Set ℝ} (hU : IsOpen U) (h0 : (0 : ℝ) ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, 0 ≤ x → x ≤ δ → x ∈ U := by
  rcases (Metric.isOpen_iff.mp hU 0 h0) with ⟨δ, hδ, hsub⟩
  refine ⟨δ / 2, by positivity, ?_⟩
  intro x hx0 hx
  apply hsub
  rw [Metric.mem_ball, Real.dist_eq]
  have habs : |x - 0| = x := by
    simpa using abs_of_nonneg hx0
  rw [habs]
  nlinarith

/-- A strict chamber for one ordered distinct base pair persists on a small
rectangle of polynomial perturbation parameters. -/
theorem exists_intercluster_radius (r s : Fin 4) (hrs : r ≠ s) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ u v : ℝ, 0 ≤ u → u ≤ δ → 0 ≤ v → v ≤ δ →
        RealizesStrictPairCode (interClusterCode r s)
          (PolynomialFamily.around (RationalBase.base r) u)
          (PolynomialFamily.around (RationalBase.base s) v) := by
  have hbase : RealizesStrictPairCode (interClusterCode r s)
      (RationalBase.base r) (RationalBase.base s) := by
    change RealizesStrictPairCode (RationalBase.baseCode r s)
      (RationalBase.base r) (RationalBase.base s)
    exact RationalBase.base_realizes_code hrs
  rcases exists_pair_chamber_neighborhood hbase with
    ⟨U, V, hU, hV, hbaseU, hbaseV, hsub⟩
  have hpreU : IsOpen
      {t : ℝ | PolynomialFamily.around (RationalBase.base r) t ∈ U} :=
    hU.preimage (PolynomialFamily.continuous_around (RationalBase.base r))
  have hpreV : IsOpen
      {t : ℝ | PolynomialFamily.around (RationalBase.base s) t ∈ V} :=
    hV.preimage (PolynomialFamily.continuous_around (RationalBase.base s))
  have h0U : (0 : ℝ) ∈
      {t : ℝ | PolynomialFamily.around (RationalBase.base r) t ∈ U} := by
    simpa using hbaseU
  have h0V : (0 : ℝ) ∈
      {t : ℝ | PolynomialFamily.around (RationalBase.base s) t ∈ V} := by
    simpa using hbaseV
  rcases exists_nonneg_interval_subset_of_isOpen hpreU h0U with
    ⟨δU, hδU, hsubU⟩
  rcases exists_nonneg_interval_subset_of_isOpen hpreV h0V with
    ⟨δV, hδV, hsubV⟩
  refine ⟨min δU δV, lt_min hδU hδV, ?_⟩
  intro u v hu0 hu hv0 hv
  exact hsub
    (PolynomialFamily.around (RationalBase.base r) u)
    (hsubU u hu0 (le_trans hu (min_le_left _ _)))
    (PolynomialFamily.around (RationalBase.base s) v)
    (hsubV v hv0 (le_trans hv (min_le_right _ _)))

/-- Uniform inter-cluster chamber radius for all ordered distinct base pairs. -/
theorem exists_uniform_intercluster_radius :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ (1 : ℝ) / 4 ∧
      ∀ r s : Fin 4, r ≠ s →
      ∀ u v : ℝ, 0 ≤ u → u ≤ ε → 0 ≤ v → v ≤ ε →
        RealizesStrictPairCode (interClusterCode r s)
          (PolynomialFamily.around (RationalBase.base r) u)
          (PolynomialFamily.around (RationalBase.base s) v) := by
  classical
  let δ : Fin 4 → Fin 4 → ℝ := fun r s =>
    if h : r = s then 1 else Classical.choose (exists_intercluster_radius r s h)
  have hδpos : ∀ r s : Fin 4, 0 < δ r s := by
    intro r s
    by_cases h : r = s
    · simp [δ, h]
    · simpa [δ, h] using
        (Classical.choose_spec (exists_intercluster_radius r s h)).1
  have hnonempty : (Finset.univ : Finset (Fin 4 × Fin 4)).Nonempty := by
    simp
  let ε := min ((1 : ℝ) / 4)
    (Finset.univ.inf' hnonempty
      (fun p : Fin 4 × Fin 4 => δ p.1 p.2 / 2))
  have hinfpos :
      0 < Finset.univ.inf' hnonempty
        (fun p : Fin 4 × Fin 4 => δ p.1 p.2 / 2) := by
    rw [Finset.lt_inf'_iff hnonempty]
    intro p _hp
    exact half_pos (hδpos p.1 p.2)
  have hεpos : 0 < ε := by
    exact lt_min (by norm_num) hinfpos
  refine ⟨ε, hεpos, min_le_left _ _, ?_⟩
  intro r s hrs u v hu0 hu hv0 hv
  have hεδ : ε ≤ δ r s / 2 := by
    exact le_trans (min_le_right _ _)
      (Finset.inf'_le _ (Finset.mem_univ (r, s)))
  have huδ : u ≤ δ r s := by
    nlinarith [hu, hεδ, hδpos r s]
  have hvδ : v ≤ δ r s := by
    nlinarith [hv, hεδ, hδpos r s]
  have hlocal :=
    (Classical.choose_spec (exists_intercluster_radius r s hrs)).2
  exact hlocal u v hu0 (by simpa [δ, hrs] using huδ)
    hv0 (by simpa [δ, hrs] using hvδ)

/-- Choose one uniform radius once and for all. -/
def epsilon : ℝ :=
  Classical.choose exists_uniform_intercluster_radius

@[simp] theorem epsilon_pos : 0 < epsilon :=
  (Classical.choose_spec exists_uniform_intercluster_radius).1

@[simp] theorem epsilon_le_quarter :
    epsilon ≤ (1 : ℝ) / 4 :=
  (Classical.choose_spec exists_uniform_intercluster_radius).2.1

/-- Concrete pre-arrangement before genericization. -/
def preArrangement {n : ℕ} (q : QuadVec n) (hq : q ∈ quadVecs n) :
    Arrangement n :=
  fun i => PolynomialFamily.around
    (RationalBase.base (clusterOf q hq i))
    (memberParameter epsilon q hq i)

/-- Oriented code of one pre-arrangement pair. -/
def pairCode {n : ℕ} (q : QuadVec n) (hq : q ∈ quadVecs n)
    (i j : Fin n) : StrictPairCode :=
  if clusterOf q hq i = clusterOf q hq j then
    if memberParameter epsilon q hq i <
        memberParameter epsilon q hq j
    then StrictPairCode.four
    else StrictPairCode.four.swap
  else interClusterCode (clusterOf q hq i) (clusterOf q hq j)

@[simp] theorem pairCode_swap {n : ℕ}
    (q : QuadVec n) (hq : q ∈ quadVecs n) (i j : Fin n)
    (hij : i ≠ j) :
    pairCode q hq j i = (pairCode q hq i j).swap := by
  unfold pairCode
  by_cases hc : clusterOf q hq i = clusterOf q hq j
  · have hc' : clusterOf q hq j = clusterOf q hq i := hc.symm
    have hpne : memberParameter epsilon q hq i ≠
        memberParameter epsilon q hq j :=
      memberParameter_ne_of_same_cluster epsilon_pos q hq hij hc
    by_cases hlt : memberParameter epsilon q hq i <
        memberParameter epsilon q hq j
    · have hnot : ¬ memberParameter epsilon q hq j <
          memberParameter epsilon q hq i := not_lt_of_ge (le_of_lt hlt)
      rw [if_pos hc', if_neg hnot, if_pos hc, if_pos hlt]
    · have hrev : memberParameter epsilon q hq j <
          memberParameter epsilon q hq i :=
        lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hpne)
      rw [if_pos hc', if_pos hrev, if_pos hc, if_neg hlt,
        strictPairCode_swap_swap]
  · have hc' : clusterOf q hq j ≠ clusterOf q hq i := by
      exact fun h => hc h.symm
    rw [if_neg hc', if_neg hc]
    exact interClusterCode_swap (clusterOf q hq i) (clusterOf q hq j)

/-- Pair-code specification of one quadruple. -/
def codeSpec {n : ℕ} (q : QuadVec n) (hq : q ∈ quadVecs n) :
    PairCodeSpec n where
  code := pairCode q hq
  swap := pairCode_swap q hq

/-- The constructed pre-arrangement realizes every intended strict pair
chamber. -/
theorem preArrangement_realizes_concrete {n : ℕ}
    (q : QuadVec n) (hq : q ∈ quadVecs n) :
    RealizesPairCodeSpec (codeSpec q hq) (preArrangement q hq) := by
  intro i j hij
  have hpi := memberParameter_bounds epsilon_pos q hq i
  have hpj := memberParameter_bounds epsilon_pos q hq j
  change RealizesStrictPairCode (pairCode q hq i j)
    (PolynomialFamily.around (RationalBase.base (clusterOf q hq i))
      (memberParameter epsilon q hq i))
    (PolynomialFamily.around (RationalBase.base (clusterOf q hq j))
      (memberParameter epsilon q hq j))
  unfold pairCode
  by_cases hc : clusterOf q hq i = clusterOf q hq j
  · have hpne : memberParameter epsilon q hq i ≠
        memberParameter epsilon q hq j :=
      memberParameter_ne_of_same_cluster epsilon_pos q hq
        (ne_of_lt hij) hc
    by_cases hlt : memberParameter epsilon q hq i <
        memberParameter epsilon q hq j
    · rw [if_pos hc, if_pos hlt]
      rw [← hc]
      have hlocal := PolynomialFamily.local_realizes_four
        (le_of_lt hpi.1) hlt
        (le_trans (le_of_lt hpj.2) epsilon_le_quarter)
      have hmapped := (Lower.realizes_similarityTo_iff
        (RationalBase.base (clusterOf q hq i))
        StrictPairCode.four _ _).2 hlocal
      simpa [PolynomialFamily.around] using hmapped
    · rw [if_pos hc, if_neg hlt]
      rw [← hc]
      have hrev : memberParameter epsilon q hq j <
          memberParameter epsilon q hq i :=
        lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hpne)
      have hlocal := PolynomialFamily.local_realizes_four
        (le_of_lt hpj.1) hrev
        (le_trans (le_of_lt hpi.2) epsilon_le_quarter)
      have hmapped := (Lower.realizes_similarityTo_iff
        (RationalBase.base (clusterOf q hq i))
        StrictPairCode.four _ _).2 hlocal
      exact (realizes_swap_iff StrictPairCode.four _ _).1
        (by simpa [PolynomialFamily.around] using hmapped)
  · rw [if_neg hc]
    exact (Classical.choose_spec exists_uniform_intercluster_radius).2.2
      (clusterOf q hq i) (clusterOf q hq j) hc
      (memberParameter epsilon q hq i)
      (memberParameter epsilon q hq j)
      (le_of_lt hpi.1) (le_of_lt hpi.2)
      (le_of_lt hpj.1) (le_of_lt hpj.2)

/-- Numerical pair code is exactly Karlsson's symmetric cluster table. -/
theorem pairCode_crossings_eq_clusterTable {n : ℕ}
    (q : QuadVec n) (hq : q ∈ quadVecs n)
    (i j : Fin n) (_hij : i ≠ j) :
    (((pairCode q hq i j).crossings : ℕ) : ℚ) =
      karlssonClusterPairCrossing (clusterOf q hq i) (clusterOf q hq j) := by
  unfold pairCode
  by_cases hc : clusterOf q hq i = clusterOf q hq j
  · by_cases hlt : memberParameter epsilon q hq i <
    memberParameter epsilon q hq j
    · rw [if_pos hc, if_pos hlt]
      rw [hc]
      simp [karlssonClusterPairCrossing]
    · rw [if_pos hc, if_neg hlt]
      rw [hc]
      simp [karlssonClusterPairCrossing]
  · rw [if_neg hc]
    exact interClusterCode_crossings hc

/-- Generic concrete realization of one admissible quadruple. -/
theorem exists_generic_blowUp {n : ℕ}
    (havoid : GenericityPort.ChamberGenericityAvoidance n)
    (q : QuadVec n) (hq : q ∈ quadVecs n) :
    ∃ A : Arrangement n,
      IsGeneric A ∧
      ∀ i j : Fin n, i < j →
        pairCrossingCount (A i) (A j) =
          (pairCode q hq i j).crossings := by
  exact exists_generic_with_pairCrossingCounts_of_chamber_avoidance havoid
    (preArrangement_realizes_concrete q hq)

/-- The generic blow-up crossing sum is exactly the existing clustered table. -/
theorem totalCrossingsRat_eq_clusteredTable {n : ℕ}
    (q : QuadVec n) (hq : q ∈ quadVecs n)
    {A : Arrangement n} (hpair : ∀ i j : Fin n, i < j →
      pairCrossingCount (A i) (A j) = (pairCode q hq i j).crossings) :
    ((totalCrossingsNat A : ℕ) : ℚ) =
      clusteredKarlssonPairTableCrossings (clusterOf q hq) := by
  unfold totalCrossingsNat clusteredKarlssonPairTableCrossings pairSum
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hp_lt : p.1 < p.2 := by
    rw [pairFinset, Finset.mem_filter] at hp
    exact hp.2
  rw [hpair p.1 p.2 hp_lt]
  exact pairCode_crossings_eq_clusterTable q hq p.1 p.2 (ne_of_lt hp_lt)

/-- Exact lower crossing total for one admissible quadruple. -/
theorem exists_generic_crossings_eq_lowerCrossingsOfQuad {n : ℕ}
    (havoid : GenericityPort.ChamberGenericityAvoidance n)
    (q : QuadVec n) (hq : q ∈ quadVecs n) :
    ∃ A : Arrangement n,
      IsGeneric A ∧
      ((totalCrossingsNat A : ℕ) : ℚ) = lowerCrossingsOfQuad q := by
  rcases exists_generic_blowUp havoid q hq with ⟨A, hgen, hpair⟩
  refine ⟨A, hgen, ?_⟩
  calc
    ((totalCrossingsNat A : ℕ) : ℚ) =
        clusteredKarlssonPairTableCrossings (clusterOf q hq) :=
      totalCrossingsRat_eq_clusteredTable q hq hpair
    _ = karlssonClusterTableCrossingsOfQuad q := by
      exact (cardinalityClusteredKarlssonTableWitnessOfQuad q hq).pairSum_eq_table
    _ = lowerCrossingsOfQuad q :=
      karlssonClusterTableCrossingsOfQuad_eq_lowerCrossingsOfQuad q

/-- Exact generic region equation for one admissible quadruple. -/
theorem exists_region_eq_lowerRegionsOfQuad {n : ℕ}
    (hregion : ∀ {m : ℕ} {A : Arrangement m}, IsGeneric A →
      regionCountRat A = ((totalCrossingsNat A : ℕ) : ℚ) + (m : ℚ) + 1)
    (havoid : GenericityPort.ChamberGenericityAvoidance n)
    (q : QuadVec n) (hq : q ∈ quadVecs n) :
    ∃ A : Arrangement n,
      regionCountRat A = lowerRegionsOfQuad q := by
  rcases exists_generic_crossings_eq_lowerCrossingsOfQuad havoid q hq with
    ⟨A, hgen, hcross⟩
  refine ⟨A, ?_⟩
  unfold lowerRegionsOfQuad
  rw [hregion hgen, hcross]

/-- Concrete lower realization in the existing algebraic interface. -/
theorem lowerRealization
    (hregion : ∀ {m : ℕ} {A : Arrangement m}, IsGeneric A →
      regionCountRat A = ((totalCrossingsNat A : ℕ) : ℚ) + (m : ℚ) + 1)
    (havoid : ∀ n : ℕ, GenericityPort.ChamberGenericityAvoidance n) (n : ℕ) :
    LowerRealization (Arrangement n) regionCountRat n := by
  intro q hq
  exact exists_region_eq_lowerRegionsOfQuad hregion (havoid n) q hq

/-- Crossing-level concrete lower realization. -/
theorem lowerCrossingRealization
    (hregion : ∀ {m : ℕ} {A : Arrangement m}, IsGeneric A →
      regionCountRat A = ((totalCrossingsNat A : ℕ) : ℚ) + (m : ℚ) + 1)
    (havoid : ∀ n : ℕ, GenericityPort.ChamberGenericityAvoidance n) (n : ℕ) :
    LowerCrossingRealization (Arrangement n) regionCountRat
      (fun A => ((totalCrossingsNat A : ℕ) : ℚ)) n := by
  intro q hq
  rcases exists_generic_crossings_eq_lowerCrossingsOfQuad (havoid n) q hq with
    ⟨A, hgen, hcross⟩
  refine ⟨A, hcross, ?_⟩
  exact hregion hgen

end BlowUp
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
Manuscript Lemma 8.5 (`lem:blowup`): every admissible four-cluster size vector
has a generic realization with the Karlsson lower crossing polynomial.
-/

namespace Lollipop.Manuscript.Lemma_8_5

open Concrete Concrete.EndToEnd Concrete.EndToEnd.Lower

abbrev CoreStatement {n : Nat} (q : QuadVec n) : Prop :=
  GenericityPort.ChamberGenericityAvoidance n ->
  q ∈ quadVecs n ->
    exists A : Arrangement n,
      IsGeneric A /\
      ((totalCrossingsNat A : Nat) : Rat) = lowerCrossingsOfQuad q

end Lollipop.Manuscript.Lemma_8_5

/-! The actual numbered proof. -/

namespace Lollipop.Manuscript.Lemma_8_5

open Concrete Concrete.EndToEnd Concrete.EndToEnd.Lower

theorem proof {n : Nat} (q : QuadVec n) : CoreStatement q := by
  intro hAvoid hq
  exact BlowUp.exists_generic_crossings_eq_lowerCrossingsOfQuad hAvoid q hq

end Lollipop.Manuscript.Lemma_8_5
