import Lollipop.Internal.PairReduction
import Mathlib.Tactic

/-!
Incremental region-count algebra for the manuscript-facing Theorem 1 layer.

This file isolates the purely finite algebra behind the usual planar-region
recurrence: start with one region, insert the lollipops one at a time, and add
`added k + 1` regions at step `k`.  The theorem below proves that this implies
the final equation `regions = total crossings + n + 1` once the incremental
crossing contributions sum to the stated total.
-/

namespace Lollipop
namespace TheoremOneManuscript

open BigOperators

/-- Telescoping algebra for an incremental region count.  If `partialRegions 0 = 1`
and each step `k < n` adds `added k + 1`, then after `n` steps the count is
the sum of all incremental additions plus `n + 1`. -/
theorem region_eq_sum_added_of_increment
    (partialRegions added : Nat → Rat) :
    ∀ n : Nat,
      partialRegions 0 = 1 →
      (∀ k : Nat, k < n →
        partialRegions (k + 1) = partialRegions k + added k + 1) →
      partialRegions n = (∑ k ∈ Finset.range n, added k) + (n : Rat) + 1
  | 0, hzero, _ => by
      simp [hzero]
  | Nat.succ n, hzero, hstep => by
      have hprev :
          ∀ k : Nat, k < n →
            partialRegions (k + 1) = partialRegions k + added k + 1 := by
        intro k hk
        exact hstep k (Nat.lt_trans hk (Nat.lt_succ_self n))
      have ih :=
        region_eq_sum_added_of_increment partialRegions added n hzero hprev
      have hlast :
          partialRegions (n + 1) = partialRegions n + added n + 1 :=
        hstep n (Nat.lt_succ_self n)
      calc
        partialRegions (Nat.succ n)
            = partialRegions n + added n + 1 := by
                simpa [Nat.succ_eq_add_one] using hlast
        _ = ((∑ k ∈ Finset.range n, added k) + (n : Rat) + 1) +
              added n + 1 := by
                rw [ih]
        _ = (∑ k ∈ Finset.range (Nat.succ n), added k) +
              (Nat.succ n : Rat) + 1 := by
                rw [Finset.sum_range_succ]
                simp [Nat.cast_succ]
                ring

/-- Concrete incremental data for deriving a final region equation.  The
`added_sum_eq_total` field can later be supplied either by a direct finite
crossing-count calculation or by a more structured pair-indexing lemma. -/
structure IncrementalRegionData
    (n : Nat) (target totalCrossings : Rat) where
  partialRegions : Nat → Rat
  added : Nat → Rat
  partialRegions_zero : partialRegions 0 = 1
  partialRegions_step :
    ∀ k : Nat, k < n →
      partialRegions (k + 1) = partialRegions k + added k + 1
  partialRegions_final : partialRegions n = target
  added_sum_eq_total : (∑ k ∈ Finset.range n, added k) = totalCrossings

namespace IncrementalRegionData

/-- The incremental data imply the final `target = totalCrossings + n + 1`
region equation. -/
theorem target_eq_totalCrossings_add
    {n : Nat} {target totalCrossings : Rat}
    (D : IncrementalRegionData n target totalCrossings) :
    target = totalCrossings + (n : Rat) + 1 := by
  rw [← D.partialRegions_final]
  rw [region_eq_sum_added_of_increment D.partialRegions D.added n
    D.partialRegions_zero D.partialRegions_step]
  rw [D.added_sum_eq_total]

end IncrementalRegionData

/-- Incremental data specialized to the pair-sum crossing total used in the
upper-bound certificates. -/
abbrev IncrementalPairRegionData
    (n : Nat) (target : Rat) (cross : Fin n → Fin n → Rat) : Type :=
  IncrementalRegionData n target (pairSum n cross)

/-- The pair-sum-specialized incremental package gives exactly the region
equation required by the final upper-certificate stack. -/
theorem region_eq_pairSum_of_incremental_pair_region_data
    {n : Nat} {target : Rat} {cross : Fin n → Fin n → Rat}
    (D : IncrementalPairRegionData n target cross) :
    target = pairSum n cross + (n : Rat) + 1 :=
  D.target_eq_totalCrossings_add

/-- The crossing contribution against all earlier indices for a fixed inserted
index `j`. -/
def previousPairSum
    {n : Nat} (cross : Fin n → Fin n → Rat) (j : Fin n) : Rat :=
  ∑ i : Fin n, if i < j then cross i j else 0

/-- The previous-pair contribution written as a natural-indexed sequence,
with value `0` outside `0, ..., n - 1`. -/
def previousPairAdded
    {n : Nat} (cross : Fin n → Fin n → Rat) (k : Nat) : Rat :=
  if h : k < n then previousPairSum cross ⟨k, h⟩ else 0

/-- Previous-pair sums respect pointwise equality of crossing tables. -/
theorem previousPairSum_congr
    {n : Nat} {cross cross' : Fin n → Fin n → Rat}
    (hcross : ∀ i j : Fin n, cross i j = cross' i j)
    (j : Fin n) :
    previousPairSum cross j = previousPairSum cross' j := by
  classical
  unfold previousPairSum
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hij : i < j
  · simp [hij, hcross i j]
  · simp [hij]

/-- Natural-indexed previous-pair additions respect pointwise equality of
crossing tables. -/
theorem previousPairAdded_congr
    {n : Nat} {cross cross' : Fin n → Fin n → Rat}
    (hcross : ∀ i j : Fin n, cross i j = cross' i j)
    (k : Nat) :
    previousPairAdded cross k = previousPairAdded cross' k := by
  unfold previousPairAdded
  by_cases hk : k < n
  · simp [hk, previousPairSum_congr hcross ⟨k, hk⟩]
  · simp [hk]

/-- Summing previous-pair contributions over insertion indices is the same as
summing over unordered increasing pairs. -/
theorem pairSum_eq_sum_previousPairSum
    (n : Nat) (cross : Fin n → Fin n → Rat) :
    pairSum n cross = ∑ j : Fin n, previousPairSum cross j := by
  classical
  unfold pairSum previousPairSum
  let fibers : Fin n → Finset (Fin n) :=
    fun j => (Finset.univ.filter fun i : Fin n => i < j)
  have hprod :
      (∑ p ∈ pairFinset n, cross p.1 p.2) =
        ∑ j ∈ (Finset.univ : Finset (Fin n)),
          ∑ i ∈ fibers j, cross i j := by
    refine Finset.sum_finset_product_right
      (r := pairFinset n) (s := (Finset.univ : Finset (Fin n)))
      (t := fibers) ?_
    intro p
    simp [pairFinset, fibers]
  calc
    (∑ p ∈ pairFinset n, cross p.1 p.2)
        = ∑ j ∈ (Finset.univ : Finset (Fin n)),
            ∑ i ∈ fibers j, cross i j := hprod
    _ = ∑ j : Fin n, ∑ i : Fin n,
            if i < j then cross i j else 0 := by
          simp [fibers, Finset.sum_filter]

/-- The natural-indexed previous-pair sequence sums to `pairSum`. -/
theorem sum_range_previousPairAdded_eq_pairSum
    {n : Nat} (cross : Fin n → Fin n → Rat) :
    (∑ k ∈ Finset.range n, previousPairAdded cross k) = pairSum n cross := by
  rw [pairSum_eq_sum_previousPairSum n cross]
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  simp [previousPairAdded]

/-- Region-increment data where the crossing contribution at step `k` is the
canonical sum over previous pairs `i < k`. -/
structure OrderedIncrementalPairRegionData
    (n : Nat) (target : Rat) (cross : Fin n → Fin n → Rat) where
  partialRegions : Nat → Rat
  partialRegions_zero : partialRegions 0 = 1
  partialRegions_step :
    ∀ k : Nat, k < n →
      partialRegions (k + 1) =
        partialRegions k + previousPairAdded cross k + 1
  partialRegions_final : partialRegions n = target

namespace OrderedIncrementalPairRegionData

/-- Ordered previous-pair increment data imply the general incremental
pair-region package. -/
def toIncrementalPairRegionData
    {n : Nat} {target : Rat} {cross : Fin n → Fin n → Rat}
    (D : OrderedIncrementalPairRegionData n target cross) :
    IncrementalPairRegionData n target cross where
  partialRegions := D.partialRegions
  added := previousPairAdded cross
  partialRegions_zero := D.partialRegions_zero
  partialRegions_step := D.partialRegions_step
  partialRegions_final := D.partialRegions_final
  added_sum_eq_total := sum_range_previousPairAdded_eq_pairSum cross

/-- Ordered previous-pair increment data prove the pair-sum region equation. -/
theorem target_eq_pairSum_add
    {n : Nat} {target : Rat} {cross : Fin n → Fin n → Rat}
    (D : OrderedIncrementalPairRegionData n target cross) :
    target = pairSum n cross + (n : Rat) + 1 :=
  region_eq_pairSum_of_incremental_pair_region_data
    D.toIncrementalPairRegionData

/-- Ordered incremental region data can be transported across pointwise
equality of crossing tables. -/
def congr_cross
    {n : Nat} {target : Rat} {cross cross' : Fin n → Fin n → Rat}
    (D : OrderedIncrementalPairRegionData n target cross)
    (hcross : ∀ i j : Fin n, cross i j = cross' i j) :
    OrderedIncrementalPairRegionData n target cross' where
  partialRegions := D.partialRegions
  partialRegions_zero := D.partialRegions_zero
  partialRegions_step := by
    intro k hk
    calc
      D.partialRegions (k + 1) =
          D.partialRegions k + previousPairAdded cross k + 1 :=
        D.partialRegions_step k hk
      _ = D.partialRegions k + previousPairAdded cross' k + 1 := by
        rw [previousPairAdded_congr hcross k]
  partialRegions_final := D.partialRegions_final

end OrderedIncrementalPairRegionData

/-- One local insertion step in the ordered previous-pair region recurrence.
This is the per-step certificate that a first-principles construction can
prove independently before Lean assembles the full recurrence. -/
structure OrderedIncrementStepData
    (n : Nat) (partialRegions : Nat → Rat)
    (cross : Fin n → Fin n → Rat) (k : Nat) (hk : k < n) where
  step_eq :
    partialRegions (k + 1) =
      partialRegions k + previousPairAdded cross k + 1

namespace OrderedIncrementStepData

/-- A local insertion-step certificate can be transported across pointwise
equality of crossing tables. -/
def congr_cross
    {n : Nat} {partialRegions : Nat → Rat}
    {cross cross' : Fin n → Fin n → Rat} {k : Nat} {hk : k < n}
    (D : OrderedIncrementStepData n partialRegions cross k hk)
    (hcross : ∀ i j : Fin n, cross i j = cross' i j) :
    OrderedIncrementStepData n partialRegions cross' k hk where
  step_eq := by
    calc
      partialRegions (k + 1) =
          partialRegions k + previousPairAdded cross k + 1 := D.step_eq
      _ = partialRegions k + previousPairAdded cross' k + 1 := by
        rw [previousPairAdded_congr hcross k]

end OrderedIncrementStepData

/-- Ordered region-increment data supplied as one local certificate for each
insertion step. -/
structure StepwiseOrderedIncrementalPairRegionData
    (n : Nat) (target : Rat) (cross : Fin n → Fin n → Rat) where
  partialRegions : Nat → Rat
  partialRegions_zero : partialRegions 0 = 1
  step :
    ∀ k : Nat, ∀ hk : k < n,
      OrderedIncrementStepData n partialRegions cross k hk
  partialRegions_final : partialRegions n = target

namespace StepwiseOrderedIncrementalPairRegionData

/-- Assemble local insertion-step certificates into the bundled ordered
incremental region data used by the theorem stack. -/
def toOrderedIncrementalPairRegionData
    {n : Nat} {target : Rat} {cross : Fin n → Fin n → Rat}
    (D : StepwiseOrderedIncrementalPairRegionData n target cross) :
    OrderedIncrementalPairRegionData n target cross where
  partialRegions := D.partialRegions
  partialRegions_zero := D.partialRegions_zero
  partialRegions_step := by
    intro k hk
    exact (D.step k hk).step_eq
  partialRegions_final := D.partialRegions_final

/-- Stepwise ordered region data prove the pair-sum region equation. -/
theorem target_eq_pairSum_add
    {n : Nat} {target : Rat} {cross : Fin n → Fin n → Rat}
    (D : StepwiseOrderedIncrementalPairRegionData n target cross) :
    target = pairSum n cross + (n : Rat) + 1 :=
  D.toOrderedIncrementalPairRegionData.target_eq_pairSum_add

/-- Stepwise ordered region data can be transported across pointwise equality
of crossing tables. -/
def congr_cross
    {n : Nat} {target : Rat} {cross cross' : Fin n → Fin n → Rat}
    (D : StepwiseOrderedIncrementalPairRegionData n target cross)
    (hcross : ∀ i j : Fin n, cross i j = cross' i j) :
    StepwiseOrderedIncrementalPairRegionData n target cross' where
  partialRegions := D.partialRegions
  partialRegions_zero := D.partialRegions_zero
  step := by
    intro k hk
    exact (D.step k hk).congr_cross hcross
  partialRegions_final := D.partialRegions_final

end StepwiseOrderedIncrementalPairRegionData

end TheoremOneManuscript
end Lollipop
