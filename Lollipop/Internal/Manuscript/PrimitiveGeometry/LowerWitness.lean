import Lollipop.Internal.Manuscript.ExplicitInputs.PairwiseLower
import Lollipop.Internal.Manuscript.PrimitiveGeometry.Basic

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

end PrimitiveGeometry
end TheoremOneManuscript
end Lollipop
