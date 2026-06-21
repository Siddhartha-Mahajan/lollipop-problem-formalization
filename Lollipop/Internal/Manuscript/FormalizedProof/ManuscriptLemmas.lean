import Lollipop.Internal.Manuscript.FormalizedProof.Statements
import Lollipop.Internal.Manuscript.ExplicitInputs.KarlssonOEISGeometry
import Lollipop.Internal.ColoredTuran.ColoredQuotientCertificates
import Lollipop.Internal.Manuscript.PrimitiveGeometry.CloseRouteAudit
import Lollipop.Internal.Manuscript.PrimitiveGeometry.LowerWitness

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
