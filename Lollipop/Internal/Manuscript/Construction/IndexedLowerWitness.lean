import Lollipop.Internal.Manuscript.PrimitiveGeometry.LowerWitness

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
