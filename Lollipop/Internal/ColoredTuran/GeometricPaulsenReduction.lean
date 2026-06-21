import Lollipop.Internal.ColoredTuran.GeometricReduction
import Lollipop.Internal.ColoredTuran.CloseDirection
import Lollipop.Internal.ColoredTuran.PaulsenLinearAlgebra

/-!
Geometric-input reduction with Paulsen's five-circle obstruction internalized.

`GeometricReduction.lean` asks directly for the manuscript fact that every
five lollipops contain an intriguing pair.  This module replaces that one
field by Paulsen vector data, by circle-coordinate distance data on each
five-element subset, or by one global circle-coordinate model per arrangement,
and derives the forbidden-pair field using
`PaulsenLinearAlgebra.no_paulsen_gram_five`.
-/

namespace Lollipop
namespace TheoremOneEndToEnd

open BigOperators

universe u

/-- Geometric upper-bound data where the `K_5`-free input is supplied through
Paulsen's linear-algebra witnesses rather than as a bare hypothesis. -/
structure PairwisePaulsenGeometricLollipopUpper where
  nNat : Nat
  crossings : Rat
  regions : Rat
  close : Fin nNat → Fin nNat → Prop
  intriguing : Fin nNat → Fin nNat → Prop
  [close_decidable : DecidableRel close]
  [intriguing_decidable : DecidableRel intriguing]
  close_symm : ∀ i j : Fin nNat, close i j ↔ close j i
  intriguing_symm : ∀ i j : Fin nNat, intriguing i j ↔ intriguing j i
  cross : Fin nNat → Fin nNat → Rat
  crossings_le_pairSum : crossings ≤ pairSum nNat cross
  cross_le_general : ∀ i j : Fin nNat, i < j → cross i j ≤ 7
  cross_le_close : ∀ i j : Fin nNat, i < j → close i j → cross i j ≤ 5
  cross_le_intriguing :
    ∀ i j : Fin nNat, i < j → intriguing i j → cross i j ≤ 5
  cross_le_close_intriguing :
    ∀ i j : Fin nNat, i < j → close i j → intriguing i j → cross i j ≤ 4
  close_pair_in_every_four :
    ∀ t : Finset (Fin nNat), t.card = 4 →
      ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ close i j
  paulsen_data_in_every_five :
    ∀ t : Finset (Fin nNat), t.card = 5 →
      PaulsenLinearAlgebra.FiveSetPaulsenData intriguing t
  regions_eq : regions = crossings + (nNat : Rat) + 1

/-- Geometric upper-bound data where Paulsen's five-set input is supplied in
the circle-coordinate form used in the appendix: centers, positive radii, and
the two obtuse-intersection distance inequalities for non-intriguing pairs. -/
structure PairwisePaulsenCircleGeometricLollipopUpper where
  nNat : Nat
  crossings : Rat
  regions : Rat
  close : Fin nNat → Fin nNat → Prop
  intriguing : Fin nNat → Fin nNat → Prop
  [close_decidable : DecidableRel close]
  [intriguing_decidable : DecidableRel intriguing]
  close_symm : ∀ i j : Fin nNat, close i j ↔ close j i
  intriguing_symm : ∀ i j : Fin nNat, intriguing i j ↔ intriguing j i
  cross : Fin nNat → Fin nNat → Rat
  crossings_le_pairSum : crossings ≤ pairSum nNat cross
  cross_le_general : ∀ i j : Fin nNat, i < j → cross i j ≤ 7
  cross_le_close : ∀ i j : Fin nNat, i < j → close i j → cross i j ≤ 5
  cross_le_intriguing :
    ∀ i j : Fin nNat, i < j → intriguing i j → cross i j ≤ 5
  cross_le_close_intriguing :
    ∀ i j : Fin nNat, i < j → close i j → intriguing i j → cross i j ≤ 4
  close_pair_in_every_four :
    ∀ t : Finset (Fin nNat), t.card = 4 →
      ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ close i j
  paulsen_circle_data_in_every_five :
    ∀ t : Finset (Fin nNat), t.card = 5 →
      PaulsenLinearAlgebra.FiveSetPaulsenCircleData intriguing t
  regions_eq : regions = crossings + (nNat : Rat) + 1

/-- Geometric upper-bound data with one global circle-coordinate model.  From
global centers/radii and the two distance inequalities for every
non-intriguing pair, Lean builds the five-set Paulsen circle data for every
five-subset. -/
structure PairwiseGlobalCircleGeometricLollipopUpper where
  nNat : Nat
  crossings : Rat
  regions : Rat
  close : Fin nNat → Fin nNat → Prop
  intriguing : Fin nNat → Fin nNat → Prop
  [close_decidable : DecidableRel close]
  [intriguing_decidable : DecidableRel intriguing]
  close_symm : ∀ i j : Fin nNat, close i j ↔ close j i
  intriguing_symm : ∀ i j : Fin nNat, intriguing i j ↔ intriguing j i
  center : Fin nNat → PaulsenLinearAlgebra.R2
  radius : Fin nNat → ℝ
  radius_pos : ∀ i : Fin nNat, 0 < radius i
  nonintriguing_dist_low :
    ∀ i j : Fin nNat, i ≠ j → ¬ intriguing i j →
      radius i ^ 2 + radius j ^ 2 <
        PaulsenLinearAlgebra.distSq2 (center i) (center j)
  nonintriguing_dist_high :
    ∀ i j : Fin nNat, i ≠ j → ¬ intriguing i j →
      PaulsenLinearAlgebra.distSq2 (center i) (center j) <
        (radius i + radius j) ^ 2
  cross : Fin nNat → Fin nNat → Rat
  crossings_le_pairSum : crossings ≤ pairSum nNat cross
  cross_le_general : ∀ i j : Fin nNat, i < j → cross i j ≤ 7
  cross_le_close : ∀ i j : Fin nNat, i < j → close i j → cross i j ≤ 5
  cross_le_intriguing :
    ∀ i j : Fin nNat, i < j → intriguing i j → cross i j ≤ 5
  cross_le_close_intriguing :
    ∀ i j : Fin nNat, i < j → close i j → intriguing i j → cross i j ≤ 4
  close_pair_in_every_four :
    ∀ t : Finset (Fin nNat), t.card = 4 →
      ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ close i j
  regions_eq : regions = crossings + (nNat : Rat) + 1

/-- Geometric upper-bound data with one global circle-coordinate model and the
intriguing relation fixed to the canonical Paulsen circle relation
`circleIntriguing center radius`.  This removes the separate
non-intriguing-distance implication field: it is true by definition of the
relation. -/
structure PairwiseCanonicalCircleGeometricLollipopUpper where
  nNat : Nat
  crossings : Rat
  regions : Rat
  close : Fin nNat → Fin nNat → Prop
  [close_decidable : DecidableRel close]
  close_symm : ∀ i j : Fin nNat, close i j ↔ close j i
  center : Fin nNat → PaulsenLinearAlgebra.R2
  radius : Fin nNat → ℝ
  radius_pos : ∀ i : Fin nNat, 0 < radius i
  cross : Fin nNat → Fin nNat → Rat
  crossings_le_pairSum : crossings ≤ pairSum nNat cross
  cross_le_general : ∀ i j : Fin nNat, i < j → cross i j ≤ 7
  cross_le_close : ∀ i j : Fin nNat, i < j → close i j → cross i j ≤ 5
  cross_le_intriguing :
    ∀ i j : Fin nNat, i < j →
      PaulsenLinearAlgebra.circleIntriguing center radius i j →
        cross i j ≤ 5
  cross_le_close_intriguing :
    ∀ i j : Fin nNat, i < j → close i j →
      PaulsenLinearAlgebra.circleIntriguing center radius i j →
        cross i j ≤ 4
  close_pair_in_every_four :
    ∀ t : Finset (Fin nNat), t.card = 4 →
      ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ close i j
  regions_eq : regions = crossings + (nNat : Rat) + 1

/-- Strongest current upper-bound data: one global circle-coordinate model for
the circle part and one global normalized direction model for stems.  The
`close` and `intriguing` relations are fixed to the canonical relations from
those coordinates; Lean derives both finite forbidden-pair facts. -/
structure PairwiseCanonicalGeometricLollipopUpper where
  nNat : Nat
  crossings : Rat
  regions : Rat
  center : Fin nNat → PaulsenLinearAlgebra.R2
  radius : Fin nNat → ℝ
  radius_pos : ∀ i : Fin nNat, 0 < radius i
  direction : Fin nNat → ℝ
  direction_nonneg : ∀ i : Fin nNat, 0 ≤ direction i
  direction_lt_one : ∀ i : Fin nNat, direction i < 1
  direction_order_data_in_every_four :
    ∀ t : Finset (Fin nNat), t.card = 4 →
      CloseDirection.FourSetCyclicOrderData direction t
  cross : Fin nNat → Fin nNat → Rat
  crossings_le_pairSum : crossings ≤ pairSum nNat cross
  cross_le_general : ∀ i j : Fin nNat, i < j → cross i j ≤ 7
  cross_le_close :
    ∀ i j : Fin nNat, i < j →
      CloseDirection.cyclicClose direction i j →
        cross i j ≤ 5
  cross_le_intriguing :
    ∀ i j : Fin nNat, i < j →
      PaulsenLinearAlgebra.circleIntriguing center radius i j →
        cross i j ≤ 5
  cross_le_close_intriguing :
    ∀ i j : Fin nNat, i < j →
      CloseDirection.cyclicClose direction i j →
      PaulsenLinearAlgebra.circleIntriguing center radius i j →
        cross i j ≤ 4
  regions_eq : regions = crossings + (nNat : Rat) + 1

/-- The manuscript's four pairwise crossing-count cases as one canonical
table, after `close` and `intriguing` have both been fixed to their coordinate
definitions. -/
noncomputable def canonicalCrossingCaseBound
    {n : Nat}
    (direction : Fin n → ℝ)
    (center : Fin n → PaulsenLinearAlgebra.R2)
    (radius : Fin n → ℝ)
    (i j : Fin n) : Rat := by
  classical
  exact
    if CloseDirection.cyclicClose direction i j then
      if PaulsenLinearAlgebra.circleIntriguing center radius i j then 4 else 5
    else if PaulsenLinearAlgebra.circleIntriguing center radius i j then
      5
    else
      7

/-- Stronger canonical geometric upper-bound data where the pointwise
crossing estimate is supplied as the single four-case table
`canonicalCrossingCaseBound`.  Lean derives the four separate crossing
inequality fields used by the older geometric reduction. -/
structure PairwiseCanonicalCaseBoundGeometricLollipopUpper where
  nNat : Nat
  crossings : Rat
  regions : Rat
  center : Fin nNat → PaulsenLinearAlgebra.R2
  radius : Fin nNat → ℝ
  radius_pos : ∀ i : Fin nNat, 0 < radius i
  direction : Fin nNat → ℝ
  direction_nonneg : ∀ i : Fin nNat, 0 ≤ direction i
  direction_lt_one : ∀ i : Fin nNat, direction i < 1
  direction_order_data_in_every_four :
    ∀ t : Finset (Fin nNat), t.card = 4 →
      CloseDirection.FourSetCyclicOrderData direction t
  cross : Fin nNat → Fin nNat → Rat
  crossings_le_pairSum : crossings ≤ pairSum nNat cross
  cross_le_case :
    ∀ i j : Fin nNat, i < j →
      cross i j ≤ canonicalCrossingCaseBound direction center radius i j
  regions_eq : regions = crossings + (nNat : Rat) + 1

/-- Strongest current coordinate upper-bound data.  It supplies one global
circle-coordinate model, one global normalized direction map, and one
canonical four-case crossing table.  Lean now derives close-pair-in-four by
sorting each four-subset, so no per-four direction-order certificate is
needed. -/
structure PairwiseCanonicalCoordinateGeometricLollipopUpper where
  nNat : Nat
  crossings : Rat
  regions : Rat
  center : Fin nNat → PaulsenLinearAlgebra.R2
  radius : Fin nNat → ℝ
  radius_pos : ∀ i : Fin nNat, 0 < radius i
  direction : Fin nNat → ℝ
  direction_nonneg : ∀ i : Fin nNat, 0 ≤ direction i
  direction_lt_one : ∀ i : Fin nNat, direction i < 1
  cross : Fin nNat → Fin nNat → Rat
  crossings_le_pairSum : crossings ≤ pairSum nNat cross
  cross_le_case :
    ∀ i j : Fin nNat, i < j →
      cross i j ≤ canonicalCrossingCaseBound direction center radius i j
  regions_eq : regions = crossings + (nNat : Rat) + 1

/-- Strongest current exact pairwise-count upper data.  It supplies pairwise
crossing counts directly and the generic region equation in the exact
pair-sum form, so Lean fills the older total-crossing field and
`crossings <= pairSum cross` automatically. -/
structure PairwiseCanonicalExactCoordinateGeometricLollipopUpper where
  nNat : Nat
  regions : Rat
  center : Fin nNat → PaulsenLinearAlgebra.R2
  radius : Fin nNat → ℝ
  radius_pos : ∀ i : Fin nNat, 0 < radius i
  direction : Fin nNat → ℝ
  direction_nonneg : ∀ i : Fin nNat, 0 ≤ direction i
  direction_lt_one : ∀ i : Fin nNat, direction i < 1
  cross : Fin nNat → Fin nNat → Rat
  cross_le_case :
    ∀ i j : Fin nNat, i < j →
      cross i j ≤ canonicalCrossingCaseBound direction center radius i j
  regions_eq_pairSum : regions = pairSum nNat cross + (nNat : Rat) + 1

namespace PairwisePaulsenGeometricLollipopUpper

/-- Paulsen's formalized obstruction supplies the intriguing-pair-in-five
field needed by the existing geometric reduction. -/
theorem intriguing_pair_in_every_five
    (L : PairwisePaulsenGeometricLollipopUpper) :
    ∀ t : Finset (Fin L.nNat), t.card = 5 →
      ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ L.intriguing i j := by
  exact PaulsenLinearAlgebra.intriguing_pair_in_every_five_of_paulsen_data
    L.intriguing L.paulsen_data_in_every_five

/-- Forget the Paulsen witnesses after Lean has used them to derive the
five-set intriguing-pair theorem. -/
noncomputable def toPairwiseGeometricLollipopUpper
    (L : PairwisePaulsenGeometricLollipopUpper) :
    PairwiseGeometricLollipopUpper where
  nNat := L.nNat
  crossings := L.crossings
  regions := L.regions
  close := L.close
  intriguing := L.intriguing
  close_decidable := L.close_decidable
  intriguing_decidable := L.intriguing_decidable
  close_symm := L.close_symm
  intriguing_symm := L.intriguing_symm
  cross := L.cross
  crossings_le_pairSum := L.crossings_le_pairSum
  cross_le_general := L.cross_le_general
  cross_le_close := L.cross_le_close
  cross_le_intriguing := L.cross_le_intriguing
  cross_le_close_intriguing := L.cross_le_close_intriguing
  close_pair_in_every_four := L.close_pair_in_every_four
  intriguing_pair_in_every_five := L.intriguing_pair_in_every_five
  regions_eq := L.regions_eq

/-- Convert Paulsen-geometric data directly into the colored-graph certificate
used by the internalized colored Turan proof. -/
noncomputable def toPairwiseColoredGraphCertifiedLollipopUpper
    (L : PairwisePaulsenGeometricLollipopUpper) :
    PairwiseColoredGraphCertifiedLollipopUpper :=
  L.toPairwiseGeometricLollipopUpper.toPairwiseColoredGraphCertifiedLollipopUpper

end PairwisePaulsenGeometricLollipopUpper

namespace PairwisePaulsenCircleGeometricLollipopUpper

/-- Convert circle-coordinate Paulsen data to the vector-witness package. -/
noncomputable def toPairwisePaulsenGeometricLollipopUpper
    (L : PairwisePaulsenCircleGeometricLollipopUpper) :
    PairwisePaulsenGeometricLollipopUpper where
  nNat := L.nNat
  crossings := L.crossings
  regions := L.regions
  close := L.close
  intriguing := L.intriguing
  close_decidable := L.close_decidable
  intriguing_decidable := L.intriguing_decidable
  close_symm := L.close_symm
  intriguing_symm := L.intriguing_symm
  cross := L.cross
  crossings_le_pairSum := L.crossings_le_pairSum
  cross_le_general := L.cross_le_general
  cross_le_close := L.cross_le_close
  cross_le_intriguing := L.cross_le_intriguing
  cross_le_close_intriguing := L.cross_le_close_intriguing
  close_pair_in_every_four := L.close_pair_in_every_four
  paulsen_data_in_every_five := by
    intro t ht
    exact (L.paulsen_circle_data_in_every_five t ht).toFiveSetPaulsenData
  regions_eq := L.regions_eq

/-- Convert circle-coordinate Paulsen data into the existing geometric upper
certificate. -/
noncomputable def toPairwiseGeometricLollipopUpper
    (L : PairwisePaulsenCircleGeometricLollipopUpper) :
    PairwiseGeometricLollipopUpper :=
  L.toPairwisePaulsenGeometricLollipopUpper.toPairwiseGeometricLollipopUpper

end PairwisePaulsenCircleGeometricLollipopUpper

namespace PairwiseGlobalCircleGeometricLollipopUpper

/-- The five-set Paulsen circle data obtained by restricting the global
centers/radii to a five-element subset. -/
noncomputable def fiveSetPaulsenCircleData
    (L : PairwiseGlobalCircleGeometricLollipopUpper)
    (t : Finset (Fin L.nNat)) (ht : t.card = 5) :
    PaulsenLinearAlgebra.FiveSetPaulsenCircleData L.intriguing t where
  enumerate := (t.equivFinOfCardEq ht).symm
  center := fun i => L.center ((t.equivFinOfCardEq ht).symm i)
  radius := fun i => L.radius ((t.equivFinOfCardEq ht).symm i)
  radius_pos := by
    intro i
    exact L.radius_pos ((t.equivFinOfCardEq ht).symm i)
  nonintriguing_dist_low := by
    intro i j hij hnon
    have hne :
        (((t.equivFinOfCardEq ht).symm i : t) : Fin L.nNat) ≠
          (((t.equivFinOfCardEq ht).symm j : t) : Fin L.nNat) := by
      intro hval
      have hsub :
          ((t.equivFinOfCardEq ht).symm i : t) =
            ((t.equivFinOfCardEq ht).symm j : t) := Subtype.ext hval
      exact hij ((t.equivFinOfCardEq ht).symm.injective hsub)
    exact L.nonintriguing_dist_low
      (((t.equivFinOfCardEq ht).symm i : t) : Fin L.nNat)
      (((t.equivFinOfCardEq ht).symm j : t) : Fin L.nNat)
      hne hnon
  nonintriguing_dist_high := by
    intro i j hij hnon
    have hne :
        (((t.equivFinOfCardEq ht).symm i : t) : Fin L.nNat) ≠
          (((t.equivFinOfCardEq ht).symm j : t) : Fin L.nNat) := by
      intro hval
      have hsub :
          ((t.equivFinOfCardEq ht).symm i : t) =
            ((t.equivFinOfCardEq ht).symm j : t) := Subtype.ext hval
      exact hij ((t.equivFinOfCardEq ht).symm.injective hsub)
    exact L.nonintriguing_dist_high
      (((t.equivFinOfCardEq ht).symm i : t) : Fin L.nNat)
      (((t.equivFinOfCardEq ht).symm j : t) : Fin L.nNat)
      hne hnon

/-- Convert a global circle-coordinate model to the per-five-set
Paulsen-circle certificate package. -/
noncomputable def toPairwisePaulsenCircleGeometricLollipopUpper
    (L : PairwiseGlobalCircleGeometricLollipopUpper) :
    PairwisePaulsenCircleGeometricLollipopUpper where
  nNat := L.nNat
  crossings := L.crossings
  regions := L.regions
  close := L.close
  intriguing := L.intriguing
  close_decidable := L.close_decidable
  intriguing_decidable := L.intriguing_decidable
  close_symm := L.close_symm
  intriguing_symm := L.intriguing_symm
  cross := L.cross
  crossings_le_pairSum := L.crossings_le_pairSum
  cross_le_general := L.cross_le_general
  cross_le_close := L.cross_le_close
  cross_le_intriguing := L.cross_le_intriguing
  cross_le_close_intriguing := L.cross_le_close_intriguing
  close_pair_in_every_four := L.close_pair_in_every_four
  paulsen_circle_data_in_every_five := L.fiveSetPaulsenCircleData
  regions_eq := L.regions_eq

/-- Convert a global circle-coordinate model into the existing geometric upper
certificate. -/
noncomputable def toPairwiseGeometricLollipopUpper
    (L : PairwiseGlobalCircleGeometricLollipopUpper) :
    PairwiseGeometricLollipopUpper :=
  L.toPairwisePaulsenCircleGeometricLollipopUpper.toPairwiseGeometricLollipopUpper

end PairwiseGlobalCircleGeometricLollipopUpper

namespace PairwiseCanonicalCircleGeometricLollipopUpper

/-- Convert the canonical circle-coordinate model to the global-circle model
with an explicit intriguing relation and explicit distance-inequality fields. -/
noncomputable def toPairwiseGlobalCircleGeometricLollipopUpper
    (L : PairwiseCanonicalCircleGeometricLollipopUpper) :
    PairwiseGlobalCircleGeometricLollipopUpper := by
  classical
  exact
    { nNat := L.nNat
      crossings := L.crossings
      regions := L.regions
      close := L.close
      intriguing := PaulsenLinearAlgebra.circleIntriguing L.center L.radius
      close_decidable := L.close_decidable
      intriguing_decidable := inferInstance
      close_symm := L.close_symm
      intriguing_symm :=
        PaulsenLinearAlgebra.circleIntriguing_symm L.center L.radius
      center := L.center
      radius := L.radius
      radius_pos := L.radius_pos
      nonintriguing_dist_low := by
        intro i j _hij hnot
        exact (PaulsenLinearAlgebra.circleObtuseCondition_of_not_circleIntriguing
          L.center L.radius hnot).1
      nonintriguing_dist_high := by
        intro i j _hij hnot
        exact (PaulsenLinearAlgebra.circleObtuseCondition_of_not_circleIntriguing
          L.center L.radius hnot).2
      cross := L.cross
      crossings_le_pairSum := L.crossings_le_pairSum
      cross_le_general := L.cross_le_general
      cross_le_close := L.cross_le_close
      cross_le_intriguing := L.cross_le_intriguing
      cross_le_close_intriguing := L.cross_le_close_intriguing
      close_pair_in_every_four := L.close_pair_in_every_four
      regions_eq := L.regions_eq }

/-- Convert the canonical circle-coordinate model into the existing geometric
upper certificate. -/
noncomputable def toPairwiseGeometricLollipopUpper
    (L : PairwiseCanonicalCircleGeometricLollipopUpper) :
    PairwiseGeometricLollipopUpper :=
  L.toPairwiseGlobalCircleGeometricLollipopUpper.toPairwiseGeometricLollipopUpper

end PairwiseCanonicalCircleGeometricLollipopUpper

namespace PairwiseCanonicalGeometricLollipopUpper

/-- The close-pair-in-four fact follows from the checked cyclic-direction
pigeonhole theorem. -/
theorem close_pair_in_every_four
    (L : PairwiseCanonicalGeometricLollipopUpper) :
    ∀ t : Finset (Fin L.nNat), t.card = 4 →
      ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧
        CloseDirection.cyclicClose L.direction i j := by
  intro t ht
  exact (L.direction_order_data_in_every_four t ht).exists_cyclicClose_pair
    (fun i _hi => L.direction_nonneg i)
    (fun i _hi => L.direction_lt_one i)

/-- Convert canonical circle/direction data to the canonical-circle package,
forgetting that the close-pair-in-four fact was derived by Lean. -/
noncomputable def toPairwiseCanonicalCircleGeometricLollipopUpper
    (L : PairwiseCanonicalGeometricLollipopUpper) :
    PairwiseCanonicalCircleGeometricLollipopUpper where
  nNat := L.nNat
  crossings := L.crossings
  regions := L.regions
  close := CloseDirection.cyclicClose L.direction
  close_decidable := by
    classical
    exact inferInstance
  close_symm := CloseDirection.cyclicClose_symm L.direction
  center := L.center
  radius := L.radius
  radius_pos := L.radius_pos
  cross := L.cross
  crossings_le_pairSum := L.crossings_le_pairSum
  cross_le_general := L.cross_le_general
  cross_le_close := L.cross_le_close
  cross_le_intriguing := L.cross_le_intriguing
  cross_le_close_intriguing := L.cross_le_close_intriguing
  close_pair_in_every_four := L.close_pair_in_every_four
  regions_eq := L.regions_eq

/-- Convert canonical circle/direction data into the existing geometric upper
certificate. -/
noncomputable def toPairwiseGeometricLollipopUpper
    (L : PairwiseCanonicalGeometricLollipopUpper) :
    PairwiseGeometricLollipopUpper :=
  L.toPairwiseCanonicalCircleGeometricLollipopUpper.toPairwiseGeometricLollipopUpper

end PairwiseCanonicalGeometricLollipopUpper

namespace PairwiseCanonicalCaseBoundGeometricLollipopUpper

/-- Expand the single canonical pairwise crossing table into the four
pointwise crossing inequalities expected by the canonical geometric package. -/
noncomputable def toPairwiseCanonicalGeometricLollipopUpper
    (L : PairwiseCanonicalCaseBoundGeometricLollipopUpper) :
    PairwiseCanonicalGeometricLollipopUpper := by
  classical
  refine
    { nNat := L.nNat
      crossings := L.crossings
      regions := L.regions
      center := L.center
      radius := L.radius
      radius_pos := L.radius_pos
      direction := L.direction
      direction_nonneg := L.direction_nonneg
      direction_lt_one := L.direction_lt_one
      direction_order_data_in_every_four :=
        L.direction_order_data_in_every_four
      cross := L.cross
      crossings_le_pairSum := L.crossings_le_pairSum
      cross_le_general := ?_
      cross_le_close := ?_
      cross_le_intriguing := ?_
      cross_le_close_intriguing := ?_
      regions_eq := L.regions_eq }
  · intro i j hij
    have h := L.cross_le_case i j hij
    by_cases hc : CloseDirection.cyclicClose L.direction i j
    · by_cases hi :
        PaulsenLinearAlgebra.circleIntriguing L.center L.radius i j
      · have h' : L.cross i j ≤ (4 : Rat) := by
          simpa [canonicalCrossingCaseBound, hc, hi] using h
        exact le_trans h' (by norm_num)
      · have h' : L.cross i j ≤ (5 : Rat) := by
          simpa [canonicalCrossingCaseBound, hc, hi] using h
        exact le_trans h' (by norm_num)
    · by_cases hi :
        PaulsenLinearAlgebra.circleIntriguing L.center L.radius i j
      · have h' : L.cross i j ≤ (5 : Rat) := by
          simpa [canonicalCrossingCaseBound, hc, hi] using h
        exact le_trans h' (by norm_num)
      · simpa [canonicalCrossingCaseBound, hc, hi] using h
  · intro i j hij hc
    have h := L.cross_le_case i j hij
    by_cases hi :
        PaulsenLinearAlgebra.circleIntriguing L.center L.radius i j
    · have h' : L.cross i j ≤ (4 : Rat) := by
        simpa [canonicalCrossingCaseBound, hc, hi] using h
      exact le_trans h' (by norm_num)
    · simpa [canonicalCrossingCaseBound, hc, hi] using h
  · intro i j hij hi
    have h := L.cross_le_case i j hij
    by_cases hc : CloseDirection.cyclicClose L.direction i j
    · have h' : L.cross i j ≤ (4 : Rat) := by
        simpa [canonicalCrossingCaseBound, hc, hi] using h
      exact le_trans h' (by norm_num)
    · simpa [canonicalCrossingCaseBound, hc, hi] using h
  · intro i j hij hc hi
    have h := L.cross_le_case i j hij
    simpa [canonicalCrossingCaseBound, hc, hi] using h

/-- Convert the one-table canonical package into the existing geometric upper
certificate. -/
noncomputable def toPairwiseGeometricLollipopUpper
    (L : PairwiseCanonicalCaseBoundGeometricLollipopUpper) :
    PairwiseGeometricLollipopUpper :=
  L.toPairwiseCanonicalGeometricLollipopUpper.toPairwiseGeometricLollipopUpper

end PairwiseCanonicalCaseBoundGeometricLollipopUpper

namespace PairwiseCanonicalCoordinateGeometricLollipopUpper

/-- Expand the single canonical crossing table into the canonical-circle
package.  The close-pair-in-four input is derived from the unordered
normalized-direction pigeonhole theorem. -/
noncomputable def toPairwiseCanonicalCircleGeometricLollipopUpper
    (L : PairwiseCanonicalCoordinateGeometricLollipopUpper) :
    PairwiseCanonicalCircleGeometricLollipopUpper := by
  classical
  refine
    { nNat := L.nNat
      crossings := L.crossings
      regions := L.regions
      close := CloseDirection.cyclicClose L.direction
      close_decidable := inferInstance
      close_symm := CloseDirection.cyclicClose_symm L.direction
      center := L.center
      radius := L.radius
      radius_pos := L.radius_pos
      cross := L.cross
      crossings_le_pairSum := L.crossings_le_pairSum
      cross_le_general := ?_
      cross_le_close := ?_
      cross_le_intriguing := ?_
      cross_le_close_intriguing := ?_
      close_pair_in_every_four := ?_
      regions_eq := L.regions_eq }
  · intro i j hij
    have h := L.cross_le_case i j hij
    by_cases hc : CloseDirection.cyclicClose L.direction i j
    · by_cases hi :
        PaulsenLinearAlgebra.circleIntriguing L.center L.radius i j
      · have h' : L.cross i j ≤ (4 : Rat) := by
          simpa [canonicalCrossingCaseBound, hc, hi] using h
        exact le_trans h' (by norm_num)
      · have h' : L.cross i j ≤ (5 : Rat) := by
          simpa [canonicalCrossingCaseBound, hc, hi] using h
        exact le_trans h' (by norm_num)
    · by_cases hi :
        PaulsenLinearAlgebra.circleIntriguing L.center L.radius i j
      · have h' : L.cross i j ≤ (5 : Rat) := by
          simpa [canonicalCrossingCaseBound, hc, hi] using h
        exact le_trans h' (by norm_num)
      · simpa [canonicalCrossingCaseBound, hc, hi] using h
  · intro i j hij hc
    have h := L.cross_le_case i j hij
    by_cases hi :
        PaulsenLinearAlgebra.circleIntriguing L.center L.radius i j
    · have h' : L.cross i j ≤ (4 : Rat) := by
        simpa [canonicalCrossingCaseBound, hc, hi] using h
      exact le_trans h' (by norm_num)
    · simpa [canonicalCrossingCaseBound, hc, hi] using h
  · intro i j hij hi
    have h := L.cross_le_case i j hij
    by_cases hc : CloseDirection.cyclicClose L.direction i j
    · have h' : L.cross i j ≤ (4 : Rat) := by
        simpa [canonicalCrossingCaseBound, hc, hi] using h
      exact le_trans h' (by norm_num)
    · simpa [canonicalCrossingCaseBound, hc, hi] using h
  · intro i j hij hc hi
    have h := L.cross_le_case i j hij
    simpa [canonicalCrossingCaseBound, hc, hi] using h
  · intro t ht
    exact CloseDirection.exists_cyclicClose_pair_of_card_four
      L.direction ht
      (fun i _hi => L.direction_nonneg i)
      (fun i _hi => L.direction_lt_one i)

/-- Convert the coordinate package into the existing geometric upper
certificate. -/
noncomputable def toPairwiseGeometricLollipopUpper
    (L : PairwiseCanonicalCoordinateGeometricLollipopUpper) :
    PairwiseGeometricLollipopUpper :=
  L.toPairwiseCanonicalCircleGeometricLollipopUpper.toPairwiseGeometricLollipopUpper

end PairwiseCanonicalCoordinateGeometricLollipopUpper

namespace PairwiseCanonicalExactCoordinateGeometricLollipopUpper

/-- Convert exact pairwise-count coordinate data to the previous coordinate
package by setting the total crossing count to the pair sum. -/
noncomputable def toPairwiseCanonicalCoordinateGeometricLollipopUpper
    (L : PairwiseCanonicalExactCoordinateGeometricLollipopUpper) :
    PairwiseCanonicalCoordinateGeometricLollipopUpper where
  nNat := L.nNat
  crossings := pairSum L.nNat L.cross
  regions := L.regions
  center := L.center
  radius := L.radius
  radius_pos := L.radius_pos
  direction := L.direction
  direction_nonneg := L.direction_nonneg
  direction_lt_one := L.direction_lt_one
  cross := L.cross
  crossings_le_pairSum := le_rfl
  cross_le_case := L.cross_le_case
  regions_eq := L.regions_eq_pairSum

/-- Convert exact pairwise-count coordinate data into the existing geometric
upper certificate. -/
noncomputable def toPairwiseGeometricLollipopUpper
    (L : PairwiseCanonicalExactCoordinateGeometricLollipopUpper) :
    PairwiseGeometricLollipopUpper :=
  L.toPairwiseCanonicalCoordinateGeometricLollipopUpper.toPairwiseGeometricLollipopUpper

end PairwiseCanonicalExactCoordinateGeometricLollipopUpper

/-- Upper certificates for every arrangement from geometric data where the
five-intriguing-pair fact is certified by Paulsen vector witnesses. -/
def PairwisePaulsenGeometricUpperCertificates
    (P : TheoremOne.ProblemFamily.{u}) : Prop :=
  ∀ n : Nat, ∀ A : P.Arrangement n,
    ∃ L : PairwisePaulsenGeometricLollipopUpper,
      L.nNat = n ∧ L.regions = P.region n A

/-- Upper certificates for every arrangement from geometric data where
Paulsen's five-intriguing-pair input is supplied by circle-coordinate
distance-inequality witnesses. -/
def PairwisePaulsenCircleGeometricUpperCertificates
    (P : TheoremOne.ProblemFamily.{u}) : Prop :=
  ∀ n : Nat, ∀ A : P.Arrangement n,
    ∃ L : PairwisePaulsenCircleGeometricLollipopUpper,
      L.nNat = n ∧ L.regions = P.region n A

/-- Upper certificates for every arrangement from one global circle-coordinate
model per arrangement. -/
def PairwiseGlobalCircleGeometricUpperCertificates
    (P : TheoremOne.ProblemFamily.{u}) : Prop :=
  ∀ n : Nat, ∀ A : P.Arrangement n,
    ∃ L : PairwiseGlobalCircleGeometricLollipopUpper,
      L.nNat = n ∧ L.regions = P.region n A

/-- Upper certificates for every arrangement from one global circle-coordinate
model whose intriguing relation is the canonical Paulsen circle relation. -/
def PairwiseCanonicalCircleGeometricUpperCertificates
    (P : TheoremOne.ProblemFamily.{u}) : Prop :=
  ∀ n : Nat, ∀ A : P.Arrangement n,
    ∃ L : PairwiseCanonicalCircleGeometricLollipopUpper,
      L.nNat = n ∧ L.regions = P.region n A

/-- Upper certificates for every arrangement from canonical circle and
canonical direction coordinate data. -/
def PairwiseCanonicalGeometricUpperCertificates
    (P : TheoremOne.ProblemFamily.{u}) : Prop :=
  ∀ n : Nat, ∀ A : P.Arrangement n,
    ∃ L : PairwiseCanonicalGeometricLollipopUpper,
      L.nNat = n ∧ L.regions = P.region n A

/-- Upper certificates for every arrangement from canonical circle/direction
coordinate data plus one canonical four-case crossing-count table. -/
def PairwiseCanonicalCaseBoundGeometricUpperCertificates
    (P : TheoremOne.ProblemFamily.{u}) : Prop :=
  ∀ n : Nat, ∀ A : P.Arrangement n,
    ∃ L : PairwiseCanonicalCaseBoundGeometricLollipopUpper,
      L.nNat = n ∧ L.regions = P.region n A

/-- Upper certificates for every arrangement from global circle coordinates,
global normalized directions, and one canonical crossing-count table. -/
def PairwiseCanonicalCoordinateGeometricUpperCertificates
    (P : TheoremOne.ProblemFamily.{u}) : Prop :=
  ∀ n : Nat, ∀ A : P.Arrangement n,
    ∃ L : PairwiseCanonicalCoordinateGeometricLollipopUpper,
      L.nNat = n ∧ L.regions = P.region n A

/-- Upper certificates for every arrangement from exact pairwise crossing
counts, global circle coordinates, global normalized directions, and one
canonical crossing-count table. -/
def PairwiseCanonicalExactCoordinateGeometricUpperCertificates
    (P : TheoremOne.ProblemFamily.{u}) : Prop :=
  ∀ n : Nat, ∀ A : P.Arrangement n,
    ∃ L : PairwiseCanonicalExactCoordinateGeometricLollipopUpper,
      L.nNat = n ∧ L.regions = P.region n A

/-- Convert Paulsen-geometric certificate families to the existing geometric
certificate families. -/
noncomputable def pairwise_paulsen_geometric_upper_certificates_to_geometric
    {P : TheoremOne.ProblemFamily.{u}}
    (hupper : PairwisePaulsenGeometricUpperCertificates P) :
    PairwiseGeometricUpperCertificates P := by
  intro n A
  rcases hupper n A with ⟨L, hLn, hLreg⟩
  exact ⟨L.toPairwiseGeometricLollipopUpper, hLn, hLreg⟩

/-- Convert circle-coordinate Paulsen-geometric certificate families to the
vector-witness Paulsen-geometric certificate families. -/
noncomputable def pairwise_paulsen_circle_geometric_upper_certificates_to_paulsen
    {P : TheoremOne.ProblemFamily.{u}}
    (hupper : PairwisePaulsenCircleGeometricUpperCertificates P) :
    PairwisePaulsenGeometricUpperCertificates P := by
  intro n A
  rcases hupper n A with ⟨L, hLn, hLreg⟩
  exact ⟨L.toPairwisePaulsenGeometricLollipopUpper, hLn, hLreg⟩

/-- Convert circle-coordinate Paulsen-geometric certificate families to the
existing geometric certificate families. -/
noncomputable def pairwise_paulsen_circle_geometric_upper_certificates_to_geometric
    {P : TheoremOne.ProblemFamily.{u}}
    (hupper : PairwisePaulsenCircleGeometricUpperCertificates P) :
    PairwiseGeometricUpperCertificates P :=
  pairwise_paulsen_geometric_upper_certificates_to_geometric
    (pairwise_paulsen_circle_geometric_upper_certificates_to_paulsen hupper)

/-- Convert global circle-coordinate certificate families to the per-five-set
Paulsen-circle certificate families. -/
noncomputable def pairwise_global_circle_geometric_upper_certificates_to_paulsen_circle
    {P : TheoremOne.ProblemFamily.{u}}
    (hupper : PairwiseGlobalCircleGeometricUpperCertificates P) :
    PairwisePaulsenCircleGeometricUpperCertificates P := by
  intro n A
  rcases hupper n A with ⟨L, hLn, hLreg⟩
  exact ⟨L.toPairwisePaulsenCircleGeometricLollipopUpper, hLn, hLreg⟩

/-- Convert global circle-coordinate certificate families to the existing
geometric certificate families. -/
noncomputable def pairwise_global_circle_geometric_upper_certificates_to_geometric
    {P : TheoremOne.ProblemFamily.{u}}
    (hupper : PairwiseGlobalCircleGeometricUpperCertificates P) :
    PairwiseGeometricUpperCertificates P :=
  pairwise_paulsen_circle_geometric_upper_certificates_to_geometric
    (pairwise_global_circle_geometric_upper_certificates_to_paulsen_circle hupper)

/-- Convert canonical circle-coordinate certificate families to global
circle-coordinate certificate families. -/
noncomputable def pairwise_canonical_circle_geometric_upper_certificates_to_global
    {P : TheoremOne.ProblemFamily.{u}}
    (hupper : PairwiseCanonicalCircleGeometricUpperCertificates P) :
    PairwiseGlobalCircleGeometricUpperCertificates P := by
  intro n A
  rcases hupper n A with ⟨L, hLn, hLreg⟩
  exact ⟨L.toPairwiseGlobalCircleGeometricLollipopUpper, hLn, hLreg⟩

/-- Convert canonical circle-coordinate certificate families to the existing
geometric certificate families. -/
noncomputable def pairwise_canonical_circle_geometric_upper_certificates_to_geometric
    {P : TheoremOne.ProblemFamily.{u}}
    (hupper : PairwiseCanonicalCircleGeometricUpperCertificates P) :
    PairwiseGeometricUpperCertificates P :=
  pairwise_global_circle_geometric_upper_certificates_to_geometric
    (pairwise_canonical_circle_geometric_upper_certificates_to_global hupper)

/-- Convert canonical circle/direction certificate families to canonical
circle certificate families. -/
noncomputable def pairwise_canonical_geometric_upper_certificates_to_canonical_circle
    {P : TheoremOne.ProblemFamily.{u}}
    (hupper : PairwiseCanonicalGeometricUpperCertificates P) :
    PairwiseCanonicalCircleGeometricUpperCertificates P := by
  intro n A
  rcases hupper n A with ⟨L, hLn, hLreg⟩
  exact ⟨L.toPairwiseCanonicalCircleGeometricLollipopUpper, hLn, hLreg⟩

/-- Convert canonical circle/direction certificate families to the existing
geometric certificate families. -/
noncomputable def pairwise_canonical_geometric_upper_certificates_to_geometric
    {P : TheoremOne.ProblemFamily.{u}}
    (hupper : PairwiseCanonicalGeometricUpperCertificates P) :
    PairwiseGeometricUpperCertificates P :=
  pairwise_canonical_circle_geometric_upper_certificates_to_geometric
    (pairwise_canonical_geometric_upper_certificates_to_canonical_circle hupper)

/-- Convert one-table canonical certificate families to canonical
circle/direction certificate families. -/
noncomputable def pairwise_canonical_case_bound_geometric_upper_certificates_to_canonical
    {P : TheoremOne.ProblemFamily.{u}}
    (hupper : PairwiseCanonicalCaseBoundGeometricUpperCertificates P) :
    PairwiseCanonicalGeometricUpperCertificates P := by
  intro n A
  rcases hupper n A with ⟨L, hLn, hLreg⟩
  exact ⟨L.toPairwiseCanonicalGeometricLollipopUpper, hLn, hLreg⟩

/-- Convert one-table canonical certificate families to the existing geometric
certificate families. -/
noncomputable def pairwise_canonical_case_bound_geometric_upper_certificates_to_geometric
    {P : TheoremOne.ProblemFamily.{u}}
    (hupper : PairwiseCanonicalCaseBoundGeometricUpperCertificates P) :
    PairwiseGeometricUpperCertificates P :=
  pairwise_canonical_geometric_upper_certificates_to_geometric
    (pairwise_canonical_case_bound_geometric_upper_certificates_to_canonical
      hupper)

/-- Convert coordinate certificate families to canonical-circle certificate
families. -/
noncomputable def pairwise_canonical_coordinate_geometric_upper_certificates_to_canonical_circle
    {P : TheoremOne.ProblemFamily.{u}}
    (hupper : PairwiseCanonicalCoordinateGeometricUpperCertificates P) :
    PairwiseCanonicalCircleGeometricUpperCertificates P := by
  intro n A
  rcases hupper n A with ⟨L, hLn, hLreg⟩
  exact ⟨L.toPairwiseCanonicalCircleGeometricLollipopUpper, hLn, hLreg⟩

/-- Convert coordinate certificate families to the existing geometric
certificate families. -/
noncomputable def pairwise_canonical_coordinate_geometric_upper_certificates_to_geometric
    {P : TheoremOne.ProblemFamily.{u}}
    (hupper : PairwiseCanonicalCoordinateGeometricUpperCertificates P) :
    PairwiseGeometricUpperCertificates P :=
  pairwise_canonical_circle_geometric_upper_certificates_to_geometric
    (pairwise_canonical_coordinate_geometric_upper_certificates_to_canonical_circle
      hupper)

/-- Convert exact pairwise-count coordinate certificate families to coordinate
certificate families. -/
noncomputable def pairwise_canonical_exact_coordinate_geometric_upper_certificates_to_coordinate
    {P : TheoremOne.ProblemFamily.{u}}
    (hupper : PairwiseCanonicalExactCoordinateGeometricUpperCertificates P) :
    PairwiseCanonicalCoordinateGeometricUpperCertificates P := by
  intro n A
  rcases hupper n A with ⟨L, hLn, hLreg⟩
  exact ⟨L.toPairwiseCanonicalCoordinateGeometricLollipopUpper, hLn, hLreg⟩

/-- Convert exact pairwise-count coordinate certificate families to the
existing geometric certificate families. -/
noncomputable def pairwise_canonical_exact_coordinate_geometric_upper_certificates_to_geometric
    {P : TheoremOne.ProblemFamily.{u}}
    (hupper : PairwiseCanonicalExactCoordinateGeometricUpperCertificates P) :
    PairwiseGeometricUpperCertificates P :=
  pairwise_canonical_coordinate_geometric_upper_certificates_to_geometric
    (pairwise_canonical_exact_coordinate_geometric_upper_certificates_to_coordinate
      hupper)

/-- Upper-bound half of Theorem 1 from geometric data whose five-set
intriguing-pair input is discharged by Paulsen's checked linear algebra. -/
theorem upper_bound_of_pairwise_paulsen_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (hupper : PairwisePaulsenGeometricUpperCertificates P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact upper_bound_of_pairwise_geometric_certificates P
    (pairwise_paulsen_geometric_upper_certificates_to_geometric hupper)

/-- Upper-bound half of Theorem 1 from geometric data whose five-set
intriguing-pair input is discharged from circle-coordinate Paulsen witnesses. -/
theorem upper_bound_of_pairwise_paulsen_circle_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (hupper : PairwisePaulsenCircleGeometricUpperCertificates P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact upper_bound_of_pairwise_paulsen_geometric_certificates P
    (pairwise_paulsen_circle_geometric_upper_certificates_to_paulsen hupper)

/-- Upper-bound half of Theorem 1 from one global circle-coordinate model per
arrangement. -/
theorem upper_bound_of_pairwise_global_circle_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (hupper : PairwiseGlobalCircleGeometricUpperCertificates P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact upper_bound_of_pairwise_paulsen_circle_geometric_certificates P
    (pairwise_global_circle_geometric_upper_certificates_to_paulsen_circle hupper)

/-- Upper-bound half of Theorem 1 from one global circle-coordinate model per
arrangement, with intriguing fixed to the canonical Paulsen circle relation. -/
theorem upper_bound_of_pairwise_canonical_circle_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (hupper : PairwiseCanonicalCircleGeometricUpperCertificates P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact upper_bound_of_pairwise_global_circle_geometric_certificates P
    (pairwise_canonical_circle_geometric_upper_certificates_to_global hupper)

/-- Upper-bound half of Theorem 1 from canonical circle and direction
coordinate data. -/
theorem upper_bound_of_pairwise_canonical_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (hupper : PairwiseCanonicalGeometricUpperCertificates P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact upper_bound_of_pairwise_canonical_circle_geometric_certificates P
    (pairwise_canonical_geometric_upper_certificates_to_canonical_circle hupper)

/-- Upper-bound half of Theorem 1 from canonical circle/direction coordinate
data and one canonical four-case crossing-count table. -/
theorem upper_bound_of_pairwise_canonical_case_bound_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (hupper : PairwiseCanonicalCaseBoundGeometricUpperCertificates P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact upper_bound_of_pairwise_canonical_geometric_certificates P
    (pairwise_canonical_case_bound_geometric_upper_certificates_to_canonical
      hupper)

/-- Upper-bound half of Theorem 1 from global circle coordinates, global
normalized directions, and one canonical crossing-count table. -/
theorem upper_bound_of_pairwise_canonical_coordinate_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (hupper : PairwiseCanonicalCoordinateGeometricUpperCertificates P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact upper_bound_of_pairwise_canonical_circle_geometric_certificates P
    (pairwise_canonical_coordinate_geometric_upper_certificates_to_canonical_circle
      hupper)

/-- Upper-bound half of Theorem 1 from exact pairwise crossing counts, global
circle coordinates, global normalized directions, and one canonical
crossing-count table. -/
theorem upper_bound_of_pairwise_canonical_exact_coordinate_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (hupper : PairwiseCanonicalExactCoordinateGeometricUpperCertificates P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact upper_bound_of_pairwise_canonical_coordinate_geometric_certificates P
    (pairwise_canonical_exact_coordinate_geometric_upper_certificates_to_coordinate
      hupper)

end TheoremOneEndToEnd
end Lollipop
