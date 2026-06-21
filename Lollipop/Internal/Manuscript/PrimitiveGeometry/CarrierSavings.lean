import Lollipop.Internal.Manuscript.PrimitiveGeometry.ComponentBounds

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
