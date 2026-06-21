import Lollipop.Internal.Manuscript.PrimitiveGeometry.SphereBridge

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
