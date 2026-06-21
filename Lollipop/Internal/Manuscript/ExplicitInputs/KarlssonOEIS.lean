import Lollipop.Internal.Manuscript.ExplicitInputs.KarlssonBase
import Lollipop.Internal.Manuscript.PrimitiveGeometry.NormalizedBearing

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
    interval_cases k <;> native_decide
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
    interval_cases k <;> native_decide
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
