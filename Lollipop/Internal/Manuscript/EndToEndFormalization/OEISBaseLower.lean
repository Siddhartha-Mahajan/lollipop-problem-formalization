import Lollipop.Internal.Manuscript.CompleteFormalization.OEISGeometry
import Lollipop.Internal.Manuscript.CompleteFormalization.OEISPair02
import Lollipop.Internal.Manuscript.CompleteFormalization.OEISPair03
import Lollipop.Internal.Manuscript.CompleteFormalization.OEISPair12
import Lollipop.Internal.Manuscript.CompleteFormalization.OEISPair13
import Lollipop.Internal.Manuscript.CompleteFormalization.OEISPair23
import Lollipop.Internal.Manuscript.ExplicitInputs.ClusteredLower
import Lollipop.Internal.Manuscript.PrimitiveGeometry.LowerWitness

/-!
Exact OEIS base lower table for the automatic finite carrier.

The non-exceptional seven-point files already show that the automatic carrier
finset has cardinality `7` for the five non-exceptional base pairs.  This file
adds the exceptional `(Q0,Q1)` automatic-cardinality bridge and packages all
six base pairs as the Nat-valued Karlsson `5/7` lower table.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace EndToEndFormalization
namespace OEISBaseLower

open PrimitiveGeometry
open ExplicitInputs

noncomputable section

/-- The exact five-point `(Q0,Q1)` carrier description pins the automatic
finite carrier witness down to cardinality five. -/
theorem zero_one_automatic_witness_card_eq_five :
    (CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
      karlssonOEISBaseArrangement
      (show (0 : Fin 4) < (1 : Fin 4) by decide)
      (karlssonOEISBase_spheres_distinct
        (show (0 : Fin 4) < (1 : Fin 4) by decide))
      (karlssonOEISBase_rayLines_distinct
        (show (0 : Fin 4) < (1 : Fin 4) by decide))).card = 5 := by
  classical
  let hij : (0 : Fin 4) < (1 : Fin 4) := by decide
  let hLM :=
    karlssonOEISBase_spheres_distinct
      (show (0 : Fin 4) < (1 : Fin 4) by decide)
  let hline :=
    karlssonOEISBase_rayLines_distinct
      (show (0 : Fin 4) < (1 : Fin 4) by decide)
  let auto :=
    CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
      karlssonOEISBaseArrangement hij hLM hline
  have hauto :
      (auto : Set R2) =
        karlssonOEISBaseArrangement.pairIntersectionSet
          (0 : Fin 4) (1 : Fin 4) := by
    simpa [auto, hij, hLM, hline] using
      (CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset_spec
        (A := karlssonOEISBaseArrangement)
        (i := (0 : Fin 4)) (j := (1 : Fin 4)) (hij := hij)
        hLM hline)
  have hexact :
      (CompleteFormalization.OEISGeometry.q0q1FivePointFinset : Set R2) =
        karlssonOEISBaseArrangement.pairIntersectionSet
          (0 : Fin 4) (1 : Fin 4) := by
    simpa [EuclideanLollipopArrangement.pairIntersectionSet] using
      CompleteFormalization.OEISGeometry.q0q1FivePointFinset_spec
  have hfinset : auto = CompleteFormalization.OEISGeometry.q0q1FivePointFinset := by
    ext p
    have hp :=
      congrArg (fun s : Set R2 => p ∈ s) (hauto.trans hexact.symm)
    simpa using hp
  change auto.card = 5
  rw [hfinset, CompleteFormalization.OEISGeometry.q0q1FivePointFinset_card]

/-- Exact automatic finite-carrier cardinality `7` for the OEIS base pair
`(Q0,Q2)`. -/
theorem zero_two_automatic_witness_card_eq_seven :
    (CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
      karlssonOEISBaseArrangement
      (show (0 : Fin 4) < (2 : Fin 4) by decide)
      (karlssonOEISBase_spheres_distinct
        (show (0 : Fin 4) < (2 : Fin 4) by decide))
      (karlssonOEISBase_rayLines_distinct
        (show (0 : Fin 4) < (2 : Fin 4) by decide))).card = 7 :=
  CompleteFormalization.OEISSevenPoint.automatic_witness_card_eq_seven
    (hij := (show (0 : Fin 4) < (2 : Fin 4) by decide))
    CompleteFormalization.OEISPair02.q0q2SevenPointSubset

/-- Exact automatic finite-carrier cardinality `7` for the OEIS base pair
`(Q0,Q3)`. -/
theorem zero_three_automatic_witness_card_eq_seven :
    (CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
      karlssonOEISBaseArrangement
      (show (0 : Fin 4) < (3 : Fin 4) by decide)
      (karlssonOEISBase_spheres_distinct
        (show (0 : Fin 4) < (3 : Fin 4) by decide))
      (karlssonOEISBase_rayLines_distinct
        (show (0 : Fin 4) < (3 : Fin 4) by decide))).card = 7 :=
  CompleteFormalization.OEISSevenPoint.automatic_witness_card_eq_seven
    (hij := (show (0 : Fin 4) < (3 : Fin 4) by decide))
    CompleteFormalization.OEISPair03.q0q3SevenPointSubset

/-- Exact automatic finite-carrier cardinality `7` for the OEIS base pair
`(Q1,Q2)`. -/
theorem one_two_automatic_witness_card_eq_seven :
    (CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
      karlssonOEISBaseArrangement
      (show (1 : Fin 4) < (2 : Fin 4) by decide)
      (karlssonOEISBase_spheres_distinct
        (show (1 : Fin 4) < (2 : Fin 4) by decide))
      (karlssonOEISBase_rayLines_distinct
        (show (1 : Fin 4) < (2 : Fin 4) by decide))).card = 7 :=
  CompleteFormalization.OEISSevenPoint.automatic_witness_card_eq_seven
    (hij := (show (1 : Fin 4) < (2 : Fin 4) by decide))
    CompleteFormalization.OEISPair12.q1q2SevenPointSubset

/-- Exact automatic finite-carrier cardinality `7` for the OEIS base pair
`(Q1,Q3)`. -/
theorem one_three_automatic_witness_card_eq_seven :
    (CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
      karlssonOEISBaseArrangement
      (show (1 : Fin 4) < (3 : Fin 4) by decide)
      (karlssonOEISBase_spheres_distinct
        (show (1 : Fin 4) < (3 : Fin 4) by decide))
      (karlssonOEISBase_rayLines_distinct
        (show (1 : Fin 4) < (3 : Fin 4) by decide))).card = 7 :=
  CompleteFormalization.OEISSevenPoint.automatic_witness_card_eq_seven
    (hij := (show (1 : Fin 4) < (3 : Fin 4) by decide))
    CompleteFormalization.OEISPair13.q1q3SevenPointSubset

/-- Exact automatic finite-carrier cardinality `7` for the OEIS base pair
`(Q2,Q3)`. -/
theorem two_three_automatic_witness_card_eq_seven :
    (CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
      karlssonOEISBaseArrangement
      (show (2 : Fin 4) < (3 : Fin 4) by decide)
      (karlssonOEISBase_spheres_distinct
        (show (2 : Fin 4) < (3 : Fin 4) by decide))
      (karlssonOEISBase_rayLines_distinct
        (show (2 : Fin 4) < (3 : Fin 4) by decide))).card = 7 :=
  CompleteFormalization.OEISSevenPoint.automatic_witness_card_eq_seven
    (hij := (show (2 : Fin 4) < (3 : Fin 4) by decide))
    CompleteFormalization.OEISPair23.q2q3SevenPointSubset

/-- Every increasing OEIS base pair has automatic finite-carrier cardinality
exactly equal to the Nat-valued Karlsson base-pair table. -/
theorem automatic_witness_card_eq_karlssonClusterPairCrossingNat
    {i j : Fin 4} (hij : i < j) :
    (CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
      karlssonOEISBaseArrangement hij
      (karlssonOEISBase_spheres_distinct hij)
      (karlssonOEISBase_rayLines_distinct hij)).card =
        karlssonClusterPairCrossingNat i j := by
  have hijNat : (i : Nat) < (j : Nat) := hij
  fin_cases i <;> fin_cases j <;> norm_num at hijNat
  · simpa [karlssonClusterPairCrossingNat] using
      zero_one_automatic_witness_card_eq_five
  · simpa [karlssonClusterPairCrossingNat] using
      zero_two_automatic_witness_card_eq_seven
  · simpa [karlssonClusterPairCrossingNat] using
      zero_three_automatic_witness_card_eq_seven
  · simpa [karlssonClusterPairCrossingNat] using
      one_two_automatic_witness_card_eq_seven
  · simpa [karlssonClusterPairCrossingNat] using
      one_three_automatic_witness_card_eq_seven
  · simpa [karlssonClusterPairCrossingNat] using
      two_three_automatic_witness_card_eq_seven

/-- Inequality form of the exact OEIS base automatic lower table. -/
theorem karlssonClusterPairCrossingNat_le_automatic_witness_card
    {i j : Fin 4} (hij : i < j) :
    karlssonClusterPairCrossingNat i j ≤
      (CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
        karlssonOEISBaseArrangement hij
        (karlssonOEISBase_spheres_distinct hij)
        (karlssonOEISBase_rayLines_distinct hij)).card := by
  rw [automatic_witness_card_eq_karlssonClusterPairCrossingNat hij]

/-- The Nat-valued Karlsson cluster table is symmetric. -/
theorem karlssonClusterPairCrossingNat_symm (a b : Fin 4) :
    karlssonClusterPairCrossingNat a b =
      karlssonClusterPairCrossingNat b a := by
  unfold karlssonClusterPairCrossingNat
  by_cases hab : a = b
  · subst b
    simp
  · have hba : b ≠ a := by
      intro h
      exact hab h.symm
    simp [hab, hba, and_comm, or_comm]

/-- Lifted spheres in distinct OEIS base labels are noncoincident, in
unordered form. -/
theorem karlssonOEISBase_spheres_distinct_of_ne
    {a b : Fin 4} (hab : a ≠ b) :
    euclideanSphere (karlssonOEISBaseArrangement.lollipop a).center
        (karlssonOEISBaseArrangement.lollipop a).radius ≠
      euclideanSphere (karlssonOEISBaseArrangement.lollipop b).center
        (karlssonOEISBaseArrangement.lollipop b).radius := by
  rcases lt_or_gt_of_ne hab with hab_lt | hba_lt
  · exact karlssonOEISBase_spheres_distinct hab_lt
  · intro h
    exact karlssonOEISBase_spheres_distinct hba_lt h.symm

/-- Supporting ray lines in distinct OEIS base labels are noncoincident, in
unordered form. -/
theorem karlssonOEISBase_rayLines_distinct_of_ne
    {a b : Fin 4} (hab : a ≠ b) :
    euclideanRayLine (karlssonOEISBaseArrangement.lollipop a) ≠
      euclideanRayLine (karlssonOEISBaseArrangement.lollipop b) := by
  rcases lt_or_gt_of_ne hab with hab_lt | hba_lt
  · exact karlssonOEISBase_rayLines_distinct hab_lt
  · intro h
    exact karlssonOEISBase_rayLines_distinct hba_lt h.symm

/-- The exact OEIS base automatic lower table can be used for either ordering
of two distinct base labels. -/
theorem base_pairIntersectionFinset_card_eq_karlssonClusterPairCrossingNat
    {a b : Fin 4} (hab : a ≠ b)
    (hLM :
      euclideanSphere (karlssonOEISBaseArrangement.lollipop a).center
          (karlssonOEISBaseArrangement.lollipop a).radius ≠
        euclideanSphere (karlssonOEISBaseArrangement.lollipop b).center
          (karlssonOEISBaseArrangement.lollipop b).radius)
    (hline :
      euclideanRayLine (karlssonOEISBaseArrangement.lollipop a) ≠
        euclideanRayLine (karlssonOEISBaseArrangement.lollipop b)) :
    (CompleteFormalization.FiniteCarrier.pairIntersectionFinset
      (karlssonOEISBaseArrangement.lollipop a)
      (karlssonOEISBaseArrangement.lollipop b) hLM hline).card =
        karlssonClusterPairCrossingNat a b := by
  classical
  rcases lt_or_gt_of_ne hab with hab_lt | hba_lt
  · let S :=
      CompleteFormalization.FiniteCarrier.pairIntersectionFinset
        (karlssonOEISBaseArrangement.lollipop a)
        (karlssonOEISBaseArrangement.lollipop b) hLM hline
    let T :=
      CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
        karlssonOEISBaseArrangement hab_lt
        (karlssonOEISBase_spheres_distinct hab_lt)
        (karlssonOEISBase_rayLines_distinct hab_lt)
    have hST : S = T := by
      ext p
      constructor
      · intro hp
        have hp_set :
            p ∈ pairIntersectionSet
              (karlssonOEISBaseArrangement.lollipop a)
              (karlssonOEISBaseArrangement.lollipop b) := by
          have hpS : p ∈ (S : Set R2) := by
            simpa [S] using hp
          simpa [S,
            CompleteFormalization.FiniteCarrier.pairIntersectionFinset_spec
              hLM hline] using hpS
        have hpT : p ∈ (T : Set R2) := by
          simpa [T, EuclideanLollipopArrangement.pairIntersectionSet,
            CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset_spec
                (karlssonOEISBase_spheres_distinct hab_lt)
                (karlssonOEISBase_rayLines_distinct hab_lt)] using hp_set
        simpa [T] using hpT
      · intro hp
        have hp_set :
            p ∈ pairIntersectionSet
              (karlssonOEISBaseArrangement.lollipop a)
              (karlssonOEISBaseArrangement.lollipop b) := by
          have hpT : p ∈ (T : Set R2) := by
            simpa [T] using hp
          simpa [T, EuclideanLollipopArrangement.pairIntersectionSet,
            CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset_spec
                (karlssonOEISBase_spheres_distinct hab_lt)
                (karlssonOEISBase_rayLines_distinct hab_lt)] using hpT
        have hpS : p ∈ (S : Set R2) := by
          simpa [S,
            CompleteFormalization.FiniteCarrier.pairIntersectionFinset_spec
              hLM hline] using hp_set
        simpa [S] using hpS
    rw [show
      CompleteFormalization.FiniteCarrier.pairIntersectionFinset
        (karlssonOEISBaseArrangement.lollipop a)
        (karlssonOEISBaseArrangement.lollipop b) hLM hline = S by rfl]
    rw [hST, show T.card =
      (CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
        karlssonOEISBaseArrangement hab_lt
        (karlssonOEISBase_spheres_distinct hab_lt)
        (karlssonOEISBase_rayLines_distinct hab_lt)).card by rfl]
    exact automatic_witness_card_eq_karlssonClusterPairCrossingNat hab_lt
  · let S :=
      CompleteFormalization.FiniteCarrier.pairIntersectionFinset
        (karlssonOEISBaseArrangement.lollipop a)
        (karlssonOEISBaseArrangement.lollipop b) hLM hline
    let T :=
      CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
        karlssonOEISBaseArrangement hba_lt
        (karlssonOEISBase_spheres_distinct hba_lt)
        (karlssonOEISBase_rayLines_distinct hba_lt)
    have hST : S = T := by
      ext p
      constructor
      · intro hp
        have hp_set :
            p ∈ pairIntersectionSet
              (karlssonOEISBaseArrangement.lollipop a)
              (karlssonOEISBaseArrangement.lollipop b) := by
          have hpS : p ∈ (S : Set R2) := by
            simpa [S] using hp
          simpa [S,
            CompleteFormalization.FiniteCarrier.pairIntersectionFinset_spec
              hLM hline] using hpS
        have hp_set_sym :
            p ∈ pairIntersectionSet
              (karlssonOEISBaseArrangement.lollipop b)
              (karlssonOEISBaseArrangement.lollipop a) := by
          simpa [pairIntersectionSet_symm
            (karlssonOEISBaseArrangement.lollipop b)
            (karlssonOEISBaseArrangement.lollipop a)] using hp_set
        have hpT : p ∈ (T : Set R2) := by
          simpa [T, EuclideanLollipopArrangement.pairIntersectionSet,
            CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset_spec
                (karlssonOEISBase_spheres_distinct hba_lt)
                (karlssonOEISBase_rayLines_distinct hba_lt)] using hp_set_sym
        simpa [T] using hpT
      · intro hp
        have hp_set_sym :
            p ∈ pairIntersectionSet
              (karlssonOEISBaseArrangement.lollipop b)
              (karlssonOEISBaseArrangement.lollipop a) := by
          have hpT : p ∈ (T : Set R2) := by
            simpa [T] using hp
          simpa [T, EuclideanLollipopArrangement.pairIntersectionSet,
            CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset_spec
                (karlssonOEISBase_spheres_distinct hba_lt)
                (karlssonOEISBase_rayLines_distinct hba_lt)] using hpT
        have hp_set :
            p ∈ pairIntersectionSet
              (karlssonOEISBaseArrangement.lollipop a)
              (karlssonOEISBaseArrangement.lollipop b) := by
          simpa [pairIntersectionSet_symm
            (karlssonOEISBaseArrangement.lollipop a)
            (karlssonOEISBaseArrangement.lollipop b)] using hp_set_sym
        have hpS : p ∈ (S : Set R2) := by
          simpa [S,
            CompleteFormalization.FiniteCarrier.pairIntersectionFinset_spec
              hLM hline] using hp_set
        simpa [S] using hpS
    rw [show
      CompleteFormalization.FiniteCarrier.pairIntersectionFinset
        (karlssonOEISBaseArrangement.lollipop a)
        (karlssonOEISBaseArrangement.lollipop b) hLM hline = S by rfl]
    rw [hST, show T.card =
      (CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
        karlssonOEISBaseArrangement hba_lt
        (karlssonOEISBase_spheres_distinct hba_lt)
        (karlssonOEISBase_rayLines_distinct hba_lt)).card by rfl]
    rw [automatic_witness_card_eq_karlssonClusterPairCrossingNat hba_lt]
    exact (karlssonClusterPairCrossingNat_symm a b).symm

/-- The all-ones sorted quadruple used by the exact four-base lower model. -/
def oneOneOneOneQuad : QuadVec 4 :=
  fun _ => ⟨1, by decide⟩

/-- The all-ones quadruple is in the sorted manuscript search space. -/
theorem oneOneOneOneQuad_mem_sortedQuadVecs :
    oneOneOneOneQuad ∈ sortedQuadVecs 4 := by
  simp [oneOneOneOneQuad, sortedQuadVecs, quadVecs, quadVecSum,
    quadVecSorted, Fin.sum_univ_four]

/-- Lean's canonical cardinality-cluster witness for the all-ones quadruple. -/
noncomputable def canonicalOneOneOneOneWitness :
    CardinalityClusteredKarlssonTableWitness oneOneOneOneQuad :=
  cardinalityClusteredKarlssonTableWitnessOfSortedQuad
    oneOneOneOneQuad oneOneOneOneQuad_mem_sortedQuadVecs

/-- The canonical all-ones cluster map. -/
noncomputable def canonicalOneOneOneOneCluster : Fin 4 → Fin 4 :=
  canonicalOneOneOneOneWitness.cluster

/-- Every canonical all-ones cluster fiber has exactly one element. -/
theorem canonicalOneOneOneOneCluster_fiber_card
    (r : Fin 4) :
    (clusterFiber canonicalOneOneOneOneCluster r).card = 1 := by
  have hRat :
      (((clusterFiber canonicalOneOneOneOneCluster r).card : Nat) : Rat) =
        1 := by
    simpa [canonicalOneOneOneOneCluster, canonicalOneOneOneOneWitness,
      oneOneOneOneQuad, quadEntry] using
      (canonicalOneOneOneOneWitness.cluster_card_eq r)
  exact_mod_cast hRat

/-- The canonical all-ones cluster map is injective. -/
theorem canonicalOneOneOneOneCluster_injective :
    Function.Injective canonicalOneOneOneOneCluster := by
  intro i j hij_cluster
  by_contra hij_ne
  let r := canonicalOneOneOneOneCluster i
  have hcard : (clusterFiber canonicalOneOneOneOneCluster r).card = 1 :=
    canonicalOneOneOneOneCluster_fiber_card r
  have hle : (clusterFiber canonicalOneOneOneOneCluster r).card ≤ 1 := by
    rw [hcard]
  rw [Finset.card_le_one] at hle
  have hi : i ∈ clusterFiber canonicalOneOneOneOneCluster r := by
    simp [clusterFiber, r]
  have hj : j ∈ clusterFiber canonicalOneOneOneOneCluster r := by
    simp [clusterFiber, r, hij_cluster.symm]
  exact hij_ne (hle i hi j hj)

/-- Increasing domain indices have distinct canonical all-ones cluster labels. -/
theorem canonicalOneOneOneOneCluster_ne_of_lt
    {i j : Fin 4} (hij : i < j) :
    canonicalOneOneOneOneCluster i ≠ canonicalOneOneOneOneCluster j := by
  intro h
  exact (ne_of_lt hij) (canonicalOneOneOneOneCluster_injective h)

/-- The exact OEIS base arrangement relabeled by Lean's canonical all-ones
cluster map. -/
noncomputable def canonicalOneOneOneOneArrangement :
    EuclideanLollipopArrangement 4 where
  lollipop i :=
    karlssonOEISBaseArrangement.lollipop
      (canonicalOneOneOneOneCluster i)

/-- The canonical relabeled base arrangement has distinct lifted spheres. -/
theorem canonicalOneOneOneOne_spheres_distinct
    {i j : Fin 4} (hij : i < j) :
    euclideanSphere
        (canonicalOneOneOneOneArrangement.lollipop i).center
        (canonicalOneOneOneOneArrangement.lollipop i).radius ≠
      euclideanSphere
        (canonicalOneOneOneOneArrangement.lollipop j).center
        (canonicalOneOneOneOneArrangement.lollipop j).radius := by
  simpa [canonicalOneOneOneOneArrangement] using
    karlssonOEISBase_spheres_distinct_of_ne
      (canonicalOneOneOneOneCluster_ne_of_lt hij)

/-- The canonical relabeled base arrangement has distinct ray-supporting
lines. -/
theorem canonicalOneOneOneOne_rayLines_distinct
    {i j : Fin 4} (hij : i < j) :
    euclideanRayLine (canonicalOneOneOneOneArrangement.lollipop i) ≠
      euclideanRayLine (canonicalOneOneOneOneArrangement.lollipop j) := by
  simpa [canonicalOneOneOneOneArrangement] using
    karlssonOEISBase_rayLines_distinct_of_ne
      (canonicalOneOneOneOneCluster_ne_of_lt hij)

/-- The canonical relabeled exact base arrangement realizes the canonical
Nat-valued lower table through the automatic carrier finsets. -/
theorem canonicalOneOneOneOne_automatic_witness_card_eq_karlssonClusterPairCrossingNat
    {i j : Fin 4} (hij : i < j) :
    (CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
      canonicalOneOneOneOneArrangement hij
      (canonicalOneOneOneOne_spheres_distinct hij)
      (canonicalOneOneOneOne_rayLines_distinct hij)).card =
        karlssonClusterPairCrossingNat
          (canonicalOneOneOneOneCluster i)
          (canonicalOneOneOneOneCluster j) := by
  simpa [CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset,
    canonicalOneOneOneOneArrangement] using
    base_pairIntersectionFinset_card_eq_karlssonClusterPairCrossingNat
      (canonicalOneOneOneOneCluster_ne_of_lt hij)
      (canonicalOneOneOneOne_spheres_distinct hij)
      (canonicalOneOneOneOne_rayLines_distinct hij)

/-- Inequality form for the canonical relabeled exact base lower table. -/
theorem canonicalOneOneOneOne_karlssonClusterPairCrossingNat_le_automatic_witness_card
    {i j : Fin 4} (hij : i < j) :
    karlssonClusterPairCrossingNat
        (canonicalOneOneOneOneCluster i)
        (canonicalOneOneOneOneCluster j) ≤
      (CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
        canonicalOneOneOneOneArrangement hij
        (canonicalOneOneOneOne_spheres_distinct hij)
        (canonicalOneOneOneOne_rayLines_distinct hij)).card := by
  rw [canonicalOneOneOneOne_automatic_witness_card_eq_karlssonClusterPairCrossingNat hij]

/-- Automatic crossing table for the canonical relabeled exact base
arrangement. -/
noncomputable def canonicalOneOneOneOnePairCross : Fin 4 → Fin 4 → Rat :=
  CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable
    canonicalOneOneOneOneArrangement
    (fun _ _ hij => canonicalOneOneOneOne_spheres_distinct hij)
    (fun _ _ hij => canonicalOneOneOneOne_rayLines_distinct hij)

/-- Local carrier-crossing certificate for the canonical relabeled exact base
arrangement, using the automatic finite carrier. -/
noncomputable def canonicalOneOneOneOne_localCarrierCrossingData
    {i j : Fin 4} (hij : i < j) :
    LocalPairCarrierCrossingData
      canonicalOneOneOneOneArrangement
      canonicalOneOneOneOnePairCross i j hij := by
  refine
    CompleteFormalization.FiniteCarrier.localPairCarrierCrossingDataOfFiniteCarrierEq
      (A := canonicalOneOneOneOneArrangement)
      (cross := canonicalOneOneOneOnePairCross)
      hij
      (canonicalOneOneOneOne_spheres_distinct hij)
      (canonicalOneOneOneOne_rayLines_distinct hij)
      ?_
  exact CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable_eq_card
    (fun i j hij => canonicalOneOneOneOne_spheres_distinct hij)
    (fun i j hij => canonicalOneOneOneOne_rayLines_distinct hij)
    hij

/-- The automatic finite carrier itself is the lower subset for each
canonical relabeled exact base pair. -/
noncomputable def canonicalOneOneOneOne_localLowerSubsetData
    {i j : Fin 4} (hij : i < j) :
    LocalPairCarrierLowerSubsetData
      canonicalOneOneOneOneArrangement i j hij
      (karlssonClusterPairCrossingNat
        (canonicalOneOneOneOneCluster i)
        (canonicalOneOneOneOneCluster j)) where
  lowerPoints :=
    CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
      canonicalOneOneOneOneArrangement hij
      (canonicalOneOneOneOne_spheres_distinct hij)
      (canonicalOneOneOneOne_rayLines_distinct hij)
  lowerPoints_subset := by
    intro p hp
    have hp_set :
        p ∈ ((CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
          canonicalOneOneOneOneArrangement hij
          (canonicalOneOneOneOne_spheres_distinct hij)
          (canonicalOneOneOneOne_rayLines_distinct hij) : Finset R2) : Set R2) := by
      simpa using hp
    simpa
      [CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset_spec
        (canonicalOneOneOneOne_spheres_distinct hij)
        (canonicalOneOneOneOne_rayLines_distinct hij)]
      using hp_set
  bound_le_card :=
    canonicalOneOneOneOne_karlssonClusterPairCrossingNat_le_automatic_witness_card
      hij

/-- The canonical relabeled exact base pair supplies the local monotone
Karlsson lower certificate consumed by the pairwise lower interface. -/
noncomputable def canonicalOneOneOneOne_localClusterPairLowerBoundData
    {i j : Fin 4} (hij : i < j) :
    LocalClusterPairLowerBoundData
      canonicalOneOneOneOneCluster
      canonicalOneOneOneOnePairCross i j hij :=
  (canonicalOneOneOneOne_localLowerSubsetData hij)
    |>.toLocalClusterPairLowerBoundData
      (canonicalOneOneOneOne_localCarrierCrossingData hij)
      (by
        rw [karlssonClusterPairCrossing_eq_nat])

/-- Inequality form of the local monotone lower certificate for the canonical
relabeled exact base arrangement. -/
theorem canonicalOneOneOneOne_pairCross_ge_cluster
    {i j : Fin 4} (hij : i < j) :
    karlssonClusterPairCrossing
        (canonicalOneOneOneOneCluster i)
        (canonicalOneOneOneOneCluster j) ≤
      canonicalOneOneOneOnePairCross i j :=
  (canonicalOneOneOneOne_localClusterPairLowerBoundData hij).pair_cross_ge_cluster

end

end OEISBaseLower
end EndToEndFormalization
end TheoremOneManuscript
end Lollipop
