import Lollipop.Internal.Manuscript.CompleteFormalization.OEISBaseCertificates
import Lollipop.Internal.Manuscript.EndToEndFormalization.OEISBaseUpper

/-!
Final OEIS/Karlsson base geometry.

This file contains the concrete geometry certificates already proved in Lean:
the exact four-lollipop OEIS/Karlsson coordinate base, its six pair
intersection certificates, the routed upper certificate for the exceptional
base pair, and the canonical all-ones relabeling used by the theorem stack.

These are base certificates.  They do not construct the remaining
all-family direct whole-carrier upper savings certificates or all sorted
blow-up automatic carrier-cardinality lower certificates.
-/

namespace Lollipop
namespace Final

noncomputable section

/-- The exact OEIS/Karlsson four-lollipop base arrangement. -/
abbrev OEISBaseArrangement : Type :=
  TheoremOneManuscript.PrimitiveGeometry.EuclideanLollipopArrangement 4

/-- The exact OEIS/Karlsson four-lollipop base arrangement. -/
noncomputable def oeisBaseArrangement : OEISBaseArrangement :=
  TheoremOneManuscript.ExplicitInputs.karlssonOEISBaseArrangement

/-- The Karlsson `5,7,7,7,7,7` base-pair crossing table. -/
def oeisBasePairCrossing : Fin 4 → Fin 4 → Rat :=
  TheoremOneManuscript.ExplicitInputs.karlssonBasePairCrossing

/-- A coordinate-crossing certificate for one OEIS/Karlsson base pair. -/
abbrev OEISBasePairCoordinateCertificate
    (i j : Fin 4) (hij : i < j) : Type :=
  TheoremOneManuscript.ExplicitInputs.KarlssonOEISBasePairCoordinateCrossingCertificate
    i j hij

/-- The six proved pair-coordinate certificates for the exact OEIS/Karlsson
four-base arrangement. -/
abbrev OEISBaseSixPairCoordinateCertificates : Type :=
  TheoremOneManuscript.ExplicitInputs.KarlssonOEISBaseSixPairCoordinateCrossingCertificate

/-- The all-pairs coordinate-crossing certificate assembled from the six local
OEIS/Karlsson pair certificates. -/
abbrev OEISBaseCoordinateCertificates : Type :=
  TheoremOneManuscript.ExplicitInputs.KarlssonOEISBaseCoordinateCrossingCertificate

/-- The concrete six-pair OEIS/Karlsson coordinate certificate proved in Lean. -/
noncomputable def oeisBaseSixPairCoordinateCertificates :
    OEISBaseSixPairCoordinateCertificates :=
  TheoremOneManuscript.CompleteFormalization.karlsson_oeis_base_six_pair_coordinate_crossing_certificate

/-- The concrete all-pairs OEIS/Karlsson coordinate certificate proved in Lean. -/
noncomputable def oeisBaseCoordinateCertificates :
    OEISBaseCoordinateCertificates :=
  TheoremOneManuscript.CompleteFormalization.karlsson_oeis_base_coordinate_crossing_certificate

/-- The routed local upper certificate for the exceptional OEIS/Karlsson base
pair `(Q0,Q1)`. -/
abbrev OEISBaseZeroOneUpperCertificate : Type :=
  TheoremOneManuscript.PrimitiveGeometry.PrimitiveRoutedLocalPairData
    TheoremOneManuscript.ExplicitInputs.karlssonOEISBaseArrangement
    TheoremOneManuscript.ExplicitInputs.karlssonBasePairCrossing
    (0 : Fin 4) (1 : Fin 4) (by decide)

/-- The concrete routed local upper certificate for the exceptional base pair
`(Q0,Q1)`: its close branch is proved by the circle-ray-outward route, and its
intriguing branches are impossible for these two circles. -/
noncomputable def oeisBaseZeroOneUpperCertificate :
    OEISBaseZeroOneUpperCertificate :=
  TheoremOneManuscript.ExplicitInputs.KarlssonOEISBaseSixPairCoordinateCrossingCertificate.zero_one_primitiveRoutedLocalPairData
    oeisBaseSixPairCoordinateCertificates

/-- The exceptional OEIS/Karlsson base pair has the sharp routed `<= 5`
crossing bound. -/
theorem oeisBaseZeroOne_cross_le_five :
    oeisBasePairCrossing (0 : Fin 4) (1 : Fin 4) ≤ 5 :=
  TheoremOneManuscript.ExplicitInputs.KarlssonOEISBaseSixPairCoordinateCrossingCertificate.zero_one_cross_le_five
    oeisBaseSixPairCoordinateCertificates

/-- Final-facing bundle of the concrete lower-base geometry already proved in
Lean. -/
structure OEISBaseLowerGeometryCertificates : Type where
  arrangement : OEISBaseArrangement
  pair_cross : Fin 4 → Fin 4 → Rat
  pair_table :
    TheoremOneManuscript.ExplicitInputs.KarlssonBaseSixPairTableCertificate
      pair_cross
  region_increment :
    TheoremOneManuscript.StepwiseOrderedIncrementalPairRegionData
      4 45 pair_cross
  coordinate_crossing : OEISBaseCoordinateCertificates
  radial_outward :
    ∀ i : Fin 4, (arrangement.lollipop i).IsRadialOutward
  spheres_distinct :
    ∀ {i j : Fin 4}, i < j →
      TheoremOneManuscript.PrimitiveGeometry.euclideanSphere
          (arrangement.lollipop i).center
          (arrangement.lollipop i).radius ≠
        TheoremOneManuscript.PrimitiveGeometry.euclideanSphere
          (arrangement.lollipop j).center
          (arrangement.lollipop j).radius
  rayLines_distinct :
    ∀ {i j : Fin 4}, i < j →
      TheoremOneManuscript.PrimitiveGeometry.euclideanRayLine
          (arrangement.lollipop i) ≠
        TheoremOneManuscript.PrimitiveGeometry.euclideanRayLine
          (arrangement.lollipop j)

/-- The concrete OEIS/Karlsson lower-base geometry bundle. -/
noncomputable def oeisBaseLowerGeometryCertificates :
    OEISBaseLowerGeometryCertificates where
  arrangement := oeisBaseArrangement
  pair_cross := oeisBasePairCrossing
  pair_table :=
    TheoremOneManuscript.ExplicitInputs.karlssonBasePairCrossing_sixPairTableCertificate
  region_increment :=
    TheoremOneManuscript.ExplicitInputs.karlssonOEISBaseStepwiseOrderedRegionData
  coordinate_crossing := oeisBaseCoordinateCertificates
  radial_outward := by
    intro i
    exact
      TheoremOneManuscript.ExplicitInputs.karlssonOEISBaseArrangement_isRadialOutward
        i
  spheres_distinct := by
    intro i j hij
    exact
      TheoremOneManuscript.ExplicitInputs.karlssonOEISBase_spheres_distinct
        hij
  rayLines_distinct := by
    intro i j hij
    exact
      TheoremOneManuscript.ExplicitInputs.karlssonOEISBase_rayLines_distinct
        hij

/-- The proved OEIS/Karlsson base region equation, in the form used by the
lower construction boundary. -/
theorem oeisBaseLowerGeometry_region_eq :
    (45 : Rat) = pairSum 4 oeisBasePairCrossing + (4 : Rat) + 1 :=
  oeisBaseLowerGeometryCertificates.region_increment.target_eq_pairSum_add

/-- The concrete OEIS/Karlsson coordinate certificate realizes the displayed
`5,7,7,7,7,7` carrier-intersection cardinalities. -/
theorem oeisBaseLowerGeometry_six_pair_cardinalities :
    oeisBaseCoordinateCertificates.SixPairCardinalities :=
  oeisBaseCoordinateCertificates.six_pair_cardinalities

/-! ## Canonical all-ones relabeling -/

/-- The canonical all-ones relabeling of the exact OEIS/Karlsson base. -/
noncomputable def oeisCanonicalAllOnesArrangement : OEISBaseArrangement :=
  TheoremOneManuscript.EndToEndFormalization.OEISBaseLower.canonicalOneOneOneOneArrangement

/-- The canonical all-ones cluster map into the four OEIS/Karlsson labels. -/
noncomputable def oeisCanonicalAllOnesCluster : Fin 4 → Fin 4 :=
  TheoremOneManuscript.EndToEndFormalization.OEISBaseLower.canonicalOneOneOneOneCluster

/-- The automatic finite-carrier crossing table for the canonical all-ones
OEIS/Karlsson base. -/
noncomputable def oeisCanonicalAllOnesPairCross : Fin 4 → Fin 4 → Rat :=
  TheoremOneManuscript.EndToEndFormalization.OEISBaseLower.canonicalOneOneOneOnePairCross

/-- The predicate selecting canonical pairs whose OEIS labels are `0` and
`1`, in either order. -/
abbrev ZeroOneLabelPair (a b : Fin 4) : Prop :=
  TheoremOneManuscript.EndToEndFormalization.OEISBaseUpper.zeroOneLabelPair
    a b

/-- Local carrier-crossing data for one canonical all-ones OEIS/Karlsson base
pair. -/
abbrev OEISCanonicalAllOnesLocalCarrierCrossingData
    (i j : Fin 4) (hij : i < j) : Type :=
  TheoremOneManuscript.PrimitiveGeometry.LocalPairCarrierCrossingData
    oeisCanonicalAllOnesArrangement oeisCanonicalAllOnesPairCross i j hij

/-- Local lower-subset data for one canonical all-ones OEIS/Karlsson base
pair, using the canonical Nat-valued Karlsson cluster size. -/
abbrev OEISCanonicalAllOnesLocalLowerSubsetData
    (i j : Fin 4) (hij : i < j) : Type :=
  TheoremOneManuscript.PrimitiveGeometry.LocalPairCarrierLowerSubsetData
    oeisCanonicalAllOnesArrangement i j hij
    (TheoremOneManuscript.ExplicitInputs.karlssonClusterPairCrossingNat
      (oeisCanonicalAllOnesCluster i)
      (oeisCanonicalAllOnesCluster j))

/-- Local monotone lower-bound certificate for one canonical all-ones
OEIS/Karlsson base pair. -/
abbrev OEISCanonicalAllOnesLocalLowerBound
    (i j : Fin 4) (hij : i < j) : Prop :=
  TheoremOneManuscript.ExplicitInputs.LocalClusterPairLowerBoundData
    oeisCanonicalAllOnesCluster oeisCanonicalAllOnesPairCross i j hij

/-- The concrete local carrier-crossing certificate for a canonical all-ones
OEIS/Karlsson base pair. -/
noncomputable def oeisCanonicalAllOnesLocalCarrierCrossingData
    {i j : Fin 4} (hij : i < j) :
    OEISCanonicalAllOnesLocalCarrierCrossingData i j hij :=
  TheoremOneManuscript.EndToEndFormalization.OEISBaseLower.canonicalOneOneOneOne_localCarrierCrossingData
    hij

/-- The concrete local lower-subset certificate for a canonical all-ones
OEIS/Karlsson base pair. -/
noncomputable def oeisCanonicalAllOnesLocalLowerSubsetData
    {i j : Fin 4} (hij : i < j) :
    OEISCanonicalAllOnesLocalLowerSubsetData i j hij :=
  TheoremOneManuscript.EndToEndFormalization.OEISBaseLower.canonicalOneOneOneOne_localLowerSubsetData
    hij

/-- The concrete local monotone lower-bound certificate for a canonical
all-ones OEIS/Karlsson base pair. -/
theorem oeisCanonicalAllOnesLocalLowerBound
    {i j : Fin 4} (hij : i < j) :
    OEISCanonicalAllOnesLocalLowerBound i j hij :=
  TheoremOneManuscript.EndToEndFormalization.OEISBaseLower.canonicalOneOneOneOne_localClusterPairLowerBoundData
    hij

/-- The canonical all-ones automatic pair table is exactly the rational
Karlsson cluster table for every increasing pair. -/
theorem oeisCanonicalAllOnes_pairCross_eq_cluster
    {i j : Fin 4} (hij : i < j) :
    oeisCanonicalAllOnesPairCross i j =
      TheoremOneManuscript.ExplicitInputs.karlssonClusterPairCrossing
        (oeisCanonicalAllOnesCluster i)
        (oeisCanonicalAllOnesCluster j) :=
  TheoremOneManuscript.EndToEndFormalization.OEISBaseUpper.canonicalOneOneOneOne_pairCross_eq_cluster
    hij

/-- Canonical all-ones pairs with OEIS labels `0` and `1` are close. -/
theorem oeisCanonicalAllOnes_zeroOne_cyclicClose
    {i j : Fin 4}
    (h01 : ZeroOneLabelPair
      (oeisCanonicalAllOnesCluster i) (oeisCanonicalAllOnesCluster j)) :
    TheoremOneEndToEnd.CloseDirection.cyclicClose
      (fun k : Fin 4 =>
        oeisCanonicalAllOnesArrangement.normalizedDirection k) i j := by
  simpa [oeisCanonicalAllOnesArrangement, oeisCanonicalAllOnesCluster]
    using
      TheoremOneManuscript.EndToEndFormalization.OEISBaseUpper.canonicalOneOneOneOne_zeroOne_cyclicClose
        h01

/-- Canonical all-ones pairs with OEIS labels `0` and `1` are not
circle-intriguing. -/
theorem oeisCanonicalAllOnes_zeroOne_not_circleIntriguing
    {i j : Fin 4}
    (h01 : ZeroOneLabelPair
      (oeisCanonicalAllOnesCluster i) (oeisCanonicalAllOnesCluster j)) :
    ¬ TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
      (fun k : Fin 4 => oeisCanonicalAllOnesArrangement.center k)
      (fun k : Fin 4 => oeisCanonicalAllOnesArrangement.radius k) i j := by
  simpa [oeisCanonicalAllOnesArrangement, oeisCanonicalAllOnesCluster]
    using
      TheoremOneManuscript.EndToEndFormalization.OEISBaseUpper.canonicalOneOneOneOne_zeroOne_not_circleIntriguing
        h01

/-- Every distinct canonical all-ones base pair is not circle-intriguing. -/
theorem oeisCanonicalAllOnes_not_circleIntriguing
    {i j : Fin 4} (hij : i < j) :
    ¬ TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
      (fun k : Fin 4 => oeisCanonicalAllOnesArrangement.center k)
      (fun k : Fin 4 => oeisCanonicalAllOnesArrangement.radius k) i j := by
  simpa [oeisCanonicalAllOnesArrangement, oeisCanonicalAllOnesCluster]
    using
      TheoremOneManuscript.EndToEndFormalization.OEISBaseUpper.canonicalOneOneOneOne_not_circleIntriguing
        hij

/-- A canonical all-ones pair whose OEIS labels are not `0/1` is not close. -/
theorem oeisCanonicalAllOnes_not_zeroOne_not_cyclicClose
    {i j : Fin 4} (hij : i < j)
    (h01 : ¬ ZeroOneLabelPair
      (oeisCanonicalAllOnesCluster i) (oeisCanonicalAllOnesCluster j)) :
    ¬ TheoremOneEndToEnd.CloseDirection.cyclicClose
      (fun k : Fin 4 =>
        oeisCanonicalAllOnesArrangement.normalizedDirection k) i j := by
  simpa [oeisCanonicalAllOnesArrangement, oeisCanonicalAllOnesCluster]
    using
      TheoremOneManuscript.EndToEndFormalization.OEISBaseUpper.canonicalOneOneOneOne_not_zeroOne_not_cyclicClose
        hij h01

/-- The canonical crossing case bound is exactly `5` for the `0/1` pair. -/
theorem oeisCanonicalAllOnes_zeroOne_caseBound_eq_five
    {i j : Fin 4}
    (h01 : ZeroOneLabelPair
      (oeisCanonicalAllOnesCluster i) (oeisCanonicalAllOnesCluster j)) :
    TheoremOneEndToEnd.canonicalCrossingCaseBound
      (fun k : Fin 4 =>
        oeisCanonicalAllOnesArrangement.normalizedDirection k)
      (fun k : Fin 4 => oeisCanonicalAllOnesArrangement.center k)
      (fun k : Fin 4 => oeisCanonicalAllOnesArrangement.radius k)
      i j = 5 := by
  simpa [oeisCanonicalAllOnesArrangement, oeisCanonicalAllOnesCluster]
    using
      TheoremOneManuscript.EndToEndFormalization.OEISBaseUpper.canonicalOneOneOneOne_zeroOne_caseBound_eq_five
        h01

/-- The canonical crossing case bound is exactly `7` for non-`0/1` pairs. -/
theorem oeisCanonicalAllOnes_not_zeroOne_caseBound_eq_seven
    {i j : Fin 4} (hij : i < j)
    (h01 : ¬ ZeroOneLabelPair
      (oeisCanonicalAllOnesCluster i) (oeisCanonicalAllOnesCluster j)) :
    TheoremOneEndToEnd.canonicalCrossingCaseBound
      (fun k : Fin 4 =>
        oeisCanonicalAllOnesArrangement.normalizedDirection k)
      (fun k : Fin 4 => oeisCanonicalAllOnesArrangement.center k)
      (fun k : Fin 4 => oeisCanonicalAllOnesArrangement.radius k)
      i j = 7 := by
  simpa [oeisCanonicalAllOnesArrangement, oeisCanonicalAllOnesCluster]
    using
      TheoremOneManuscript.EndToEndFormalization.OEISBaseUpper.canonicalOneOneOneOne_not_zeroOne_caseBound_eq_seven
        hij h01

/-- The canonical all-ones automatic pair table satisfies the manuscript's
canonical geometric case bound for every increasing pair. -/
theorem oeisCanonicalAllOnes_pairCross_le_caseBound
    {i j : Fin 4} (hij : i < j) :
    oeisCanonicalAllOnesPairCross i j ≤
      TheoremOneEndToEnd.canonicalCrossingCaseBound
        (fun k : Fin 4 =>
          oeisCanonicalAllOnesArrangement.normalizedDirection k)
        (fun k : Fin 4 => oeisCanonicalAllOnesArrangement.center k)
        (fun k : Fin 4 => oeisCanonicalAllOnesArrangement.radius k)
        i j :=
  TheoremOneManuscript.EndToEndFormalization.OEISBaseUpper.canonicalOneOneOneOne_pairCross_le_caseBound
    hij

/-- The canonical all-ones automatic pair table satisfies the monotone
Karlsson lower bound for every increasing pair. -/
theorem oeisCanonicalAllOnes_pairCross_ge_cluster
    {i j : Fin 4} (hij : i < j) :
    TheoremOneManuscript.ExplicitInputs.karlssonClusterPairCrossing
        (oeisCanonicalAllOnesCluster i)
        (oeisCanonicalAllOnesCluster j) ≤
      oeisCanonicalAllOnesPairCross i j :=
  TheoremOneManuscript.EndToEndFormalization.OEISBaseLower.canonicalOneOneOneOne_pairCross_ge_cluster
    hij

/-- The exceptional canonical all-ones pair has automatic pair-table value
exactly `5`. -/
theorem oeisCanonicalAllOnes_pairCross_eq_five_of_zeroOne
    {i j : Fin 4} (hij : i < j)
    (h01 : ZeroOneLabelPair
      (oeisCanonicalAllOnesCluster i) (oeisCanonicalAllOnesCluster j)) :
    oeisCanonicalAllOnesPairCross i j = 5 :=
  TheoremOneManuscript.EndToEndFormalization.OEISBaseUpper.canonicalOneOneOneOne_pairCross_eq_five_of_zeroOne
    hij h01

/-- Every non-exceptional canonical all-ones pair has automatic pair-table
value exactly `7`. -/
theorem oeisCanonicalAllOnes_pairCross_eq_seven_of_not_zeroOne
    {i j : Fin 4} (hij : i < j)
    (h01 : ¬ ZeroOneLabelPair
      (oeisCanonicalAllOnesCluster i) (oeisCanonicalAllOnesCluster j)) :
    oeisCanonicalAllOnesPairCross i j = 7 :=
  TheoremOneManuscript.EndToEndFormalization.OEISBaseUpper.canonicalOneOneOneOne_pairCross_eq_seven_of_not_zeroOne
    hij h01

/-- The exact canonical all-ones OEIS/Karlsson automatic pair table has
unordered pair sum `40`. -/
theorem oeisCanonicalAllOnes_pairSum_eq_forty :
    pairSum 4 oeisCanonicalAllOnesPairCross = 40 :=
  TheoremOneManuscript.EndToEndFormalization.OEISBaseUpper.canonicalOneOneOneOne_pairSum_eq_forty

/-- The exact canonical all-ones OEIS/Karlsson automatic pair table gives the
base region equation `45 = 40 + 4 + 1`. -/
theorem oeisCanonicalAllOnes_region_eq_pairSum_add :
    (45 : Rat) =
      pairSum 4 oeisCanonicalAllOnesPairCross + (4 : Rat) + 1 :=
  TheoremOneManuscript.EndToEndFormalization.OEISBaseUpper.canonicalOneOneOneOne_region_eq_pairSum_add

/-- Final-facing bundle for the canonical all-ones base after Lean relabels
the OEIS/Karlsson base through the canonical sorted-quad cluster witness. -/
structure OEISCanonicalAllOnesGeometryCertificates : Type where
  arrangement : OEISBaseArrangement
  cluster : Fin 4 → Fin 4
  pair_cross : Fin 4 → Fin 4 → Rat
  pair_cross_eq_cluster :
    ∀ {i j : Fin 4}, i < j →
      pair_cross i j =
        TheoremOneManuscript.ExplicitInputs.karlssonClusterPairCrossing
          (cluster i) (cluster j)
  zero_one_close :
    ∀ {i j : Fin 4}, ZeroOneLabelPair (cluster i) (cluster j) →
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k : Fin 4 => arrangement.normalizedDirection k) i j
  zero_one_not_intriguing :
    ∀ {i j : Fin 4}, ZeroOneLabelPair (cluster i) (cluster j) →
      ¬ TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
        (fun k : Fin 4 => arrangement.center k)
        (fun k : Fin 4 => arrangement.radius k) i j
  not_intriguing :
    ∀ {i j : Fin 4}, i < j →
      ¬ TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
        (fun k : Fin 4 => arrangement.center k)
        (fun k : Fin 4 => arrangement.radius k) i j
  not_zeroOne_not_close :
    ∀ {i j : Fin 4}, (hij : i < j) →
      ¬ ZeroOneLabelPair (cluster i) (cluster j) →
      ¬ TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k : Fin 4 => arrangement.normalizedDirection k) i j
  zero_one_case_bound_eq_five :
    ∀ {i j : Fin 4}, ZeroOneLabelPair (cluster i) (cluster j) →
      TheoremOneEndToEnd.canonicalCrossingCaseBound
        (fun k : Fin 4 => arrangement.normalizedDirection k)
        (fun k : Fin 4 => arrangement.center k)
        (fun k : Fin 4 => arrangement.radius k)
        i j = 5
  not_zeroOne_case_bound_eq_seven :
    ∀ {i j : Fin 4}, (hij : i < j) →
      ¬ ZeroOneLabelPair (cluster i) (cluster j) →
      TheoremOneEndToEnd.canonicalCrossingCaseBound
        (fun k : Fin 4 => arrangement.normalizedDirection k)
        (fun k : Fin 4 => arrangement.center k)
        (fun k : Fin 4 => arrangement.radius k)
        i j = 7
  pair_cross_le_caseBound :
    ∀ {i j : Fin 4}, i < j →
      pair_cross i j ≤
        TheoremOneEndToEnd.canonicalCrossingCaseBound
          (fun k : Fin 4 => arrangement.normalizedDirection k)
          (fun k : Fin 4 => arrangement.center k)
          (fun k : Fin 4 => arrangement.radius k)
          i j
  pair_cross_ge_cluster :
    ∀ {i j : Fin 4}, i < j →
      TheoremOneManuscript.ExplicitInputs.karlssonClusterPairCrossing
          (cluster i) (cluster j) ≤
        pair_cross i j
  local_lower_bound :
    ∀ {i j : Fin 4}, (hij : i < j) →
      TheoremOneManuscript.ExplicitInputs.LocalClusterPairLowerBoundData
        cluster pair_cross i j hij
  pair_sum_eq_forty :
    pairSum 4 pair_cross = 40
  region_eq_pairSum_add :
    (45 : Rat) = pairSum 4 pair_cross + (4 : Rat) + 1

/-- The proved canonical all-ones OEIS/Karlsson geometry package. -/
noncomputable def oeisCanonicalAllOnesGeometryCertificates :
    OEISCanonicalAllOnesGeometryCertificates where
  arrangement := oeisCanonicalAllOnesArrangement
  cluster := oeisCanonicalAllOnesCluster
  pair_cross := oeisCanonicalAllOnesPairCross
  pair_cross_eq_cluster := by
    intro i j hij
    exact oeisCanonicalAllOnes_pairCross_eq_cluster hij
  zero_one_close := by
    intro i j h01
    exact oeisCanonicalAllOnes_zeroOne_cyclicClose h01
  zero_one_not_intriguing := by
    intro i j h01
    exact oeisCanonicalAllOnes_zeroOne_not_circleIntriguing h01
  not_intriguing := by
    intro i j hij
    exact oeisCanonicalAllOnes_not_circleIntriguing hij
  not_zeroOne_not_close := by
    intro i j hij h01
    exact oeisCanonicalAllOnes_not_zeroOne_not_cyclicClose hij h01
  zero_one_case_bound_eq_five := by
    intro i j h01
    exact oeisCanonicalAllOnes_zeroOne_caseBound_eq_five h01
  not_zeroOne_case_bound_eq_seven := by
    intro i j hij h01
    exact oeisCanonicalAllOnes_not_zeroOne_caseBound_eq_seven hij h01
  pair_cross_le_caseBound := by
    intro i j hij
    exact oeisCanonicalAllOnes_pairCross_le_caseBound hij
  pair_cross_ge_cluster := by
    intro i j hij
    exact oeisCanonicalAllOnes_pairCross_ge_cluster hij
  local_lower_bound := by
    intro i j hij
    exact oeisCanonicalAllOnesLocalLowerBound hij
  pair_sum_eq_forty := oeisCanonicalAllOnes_pairSum_eq_forty
  region_eq_pairSum_add := oeisCanonicalAllOnes_region_eq_pairSum_add

end

end Final
end Lollipop
