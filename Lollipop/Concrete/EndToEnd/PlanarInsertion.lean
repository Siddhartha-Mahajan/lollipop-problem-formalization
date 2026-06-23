import Lollipop.Concrete.Empty
import Lollipop.Concrete.EndToEnd.Insertion
import Lollipop.Internal.Manuscript.RegionEquation
import Mathlib.Tactic

/-!
# Ordered insertion reduction for the planar complement inequality

This file isolates a finite prefixArrangement reduction for the remaining planar
topology.  It does not prove the Jordan/embedded-graph step.  Instead, it
shows that local insertion bounds, or stronger split-chain data for each
insertion, imply the global arbitrary-arrangement pair-excess inequality used
by `PlanarTopologyPorts`.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace PlanarInsertion

open BigOperators

/-- Restrict a final arrangement to its first `k` natural indices. -/
def prefixArrangement {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k ≤ n) :
    Arrangement k :=
  fun i => A ⟨i.1, i.2.trans_le hk⟩

@[simp] theorem prefix_apply {n : ℕ} (A : Arrangement n)
    (k : ℕ) (hk : k ≤ n) (i : Fin k) :
    prefixArrangement A k hk i = A ⟨i.1, i.2.trans_le hk⟩ := rfl

/-- Restricting to all `n` indices recovers the original arrangement. -/
theorem prefix_full {n : ℕ} (A : Arrangement n) :
    prefixArrangement A n le_rfl = A := by
  funext i
  apply congrArg A
  exact Fin.ext rfl

/-- The next occupied prefixArrangement is the old occupied prefixArrangement union the new carrier.
-/
theorem occupied_prefix_succ {n : ℕ} (A : Arrangement n)
    {k : ℕ} (hk : k < n) :
    occupied (prefixArrangement A (k + 1) (Nat.succ_le_of_lt hk)) =
      occupied (prefixArrangement A k (Nat.le_of_lt hk)) ∪
        (A ⟨k, hk⟩).carrier := by
  ext x
  constructor
  · intro hx
    rcases mem_occupied_iff.mp hx with ⟨i, hi⟩
    by_cases hik : i.1 < k
    · left
      apply mem_occupied_iff.mpr
      let j : Fin k := ⟨i.1, hik⟩
      refine ⟨j, ?_⟩
      change x ∈ (A ⟨i.1,
        i.2.trans_le (Nat.succ_le_of_lt hk)⟩).carrier at hi
      change x ∈ (A ⟨j.1,
        j.2.trans_le (Nat.le_of_lt hk)⟩).carrier
      simpa [j] using hi
    · right
      have hieq : i.1 = k := by omega
      change x ∈ (A ⟨i.1,
        i.2.trans_le (Nat.succ_le_of_lt hk)⟩).carrier at hi
      simpa [hieq] using hi
  · intro hx
    rcases hx with hx | hx
    · rcases mem_occupied_iff.mp hx with ⟨i, hi⟩
      apply mem_occupied_iff.mpr
      let j : Fin (k + 1) := ⟨i.1, by omega⟩
      refine ⟨j, ?_⟩
      change x ∈ (A ⟨i.1,
        i.2.trans_le (Nat.le_of_lt hk)⟩).carrier at hi
      change x ∈ (A ⟨j.1,
        j.2.trans_le (Nat.succ_le_of_lt hk)⟩).carrier
      simpa [j] using hi
    · apply mem_occupied_iff.mpr
      let j : Fin (k + 1) := ⟨k, by omega⟩
      refine ⟨j, ?_⟩
      change x ∈ (A ⟨j.1,
        j.2.trans_le (Nat.succ_le_of_lt hk)⟩).carrier
      simpa [j] using hx

/-- The next prefixArrangement is the append of the old prefixArrangement by the new lollipop. -/
theorem prefix_succ_eq_snocArrangement {n : ℕ} (A : Arrangement n)
    {k : ℕ} (hk : k < n) :
    prefixArrangement A (k + 1) (Nat.succ_le_of_lt hk) =
      Insertion.snocArrangement
        (prefixArrangement A k (Nat.le_of_lt hk)) (A ⟨k, hk⟩) := by
  funext i
  by_cases hik : i.1 < k
  · simp [prefixArrangement, Insertion.snocArrangement, hik]
  · have hi : i = Fin.last k := Insertion.fin_eq_last_of_not_lt hik
    subst i
    simp [prefixArrangement, Insertion.snocArrangement]

/-- Finite component count for the empty prefixArrangement. -/
theorem finite_prefixComponents_zero {n : ℕ} (A : Arrangement n)
    (hk : 0 ≤ n) :
    Finite (ConnectedComponents (FreeSpace (prefixArrangement A 0 hk))) := by
  have hset : {x : Point | x ∉ occupied (prefixArrangement A 0 hk)} = Set.univ := by
    ext x
    simp [occupied_zero (prefixArrangement A 0 hk)]
  have hpre : IsPreconnected
      ({x : Point | x ∉ occupied (prefixArrangement A 0 hk)}) := by
    rw [hset]
    exact isPreconnected_univ
  haveI : PreconnectedSpace (FreeSpace (prefixArrangement A 0 hk)) :=
    Subtype.preconnectedSpace hpre
  exact .of_subsingleton

/-- Local upper-topology proposition for one fixed final arrangement. -/
def OrderedInsertionRegionBound {n : ℕ} (A : Arrangement n) : Prop :=
  ∀ (k : ℕ) (hk : k < n),
    regionCountRat
        (prefixArrangement A (k + 1) (Nat.succ_le_of_lt hk)) ≤
      regionCountRat (prefixArrangement A k (Nat.le_of_lt hk)) +
        TheoremOneManuscript.previousPairAdded (pairExcessTable A) k + 1

/-- Universal form of the remaining ordered insertion theorem. -/
def PlanarInsertionRegionBoundStatement : Prop :=
  ∀ {n : ℕ} (A : Arrangement n), OrderedInsertionRegionBound A

/-- Stronger split-chain input for one fixed final arrangement. -/
def OrderedInsertionSplitChainBound {n : ℕ} (A : Arrangement n) : Prop :=
  ∀ (k : ℕ) (hk : k < n),
    ∃ h : Insertion.InsertionSplitChain
        (prefixArrangement A k (Nat.le_of_lt hk)) (A ⟨k, hk⟩),
      (h.edgeCount : ℚ) ≤
        TheoremOneManuscript.previousPairAdded (pairExcessTable A) k + 1

/-- Split-chain data propagate finiteness through all ordered prefixes. -/
theorem finite_prefixComponents_of_orderedSplitChain
    {n : ℕ} (A : Arrangement n)
    (hsplit : OrderedInsertionSplitChainBound A) :
    ∀ (k : ℕ) (hk : k ≤ n),
      Finite (ConnectedComponents (FreeSpace (prefixArrangement A k hk))) := by
  intro k
  induction k with
  | zero =>
      intro hk
      exact finite_prefixComponents_zero A hk
  | succ k ih =>
      intro hkSucc
      have hk : k < n := Nat.lt_of_succ_le hkSucc
      rcases hsplit k hk with ⟨hchain, _hbudget⟩
      haveI : Finite
          (ConnectedComponents
            (FreeSpace (prefixArrangement A k (Nat.le_of_lt hk)))) :=
        ih (Nat.le_of_lt hk)
      rw [prefix_succ_eq_snocArrangement A hk]
      exact Insertion.finite_newComponents_of_insertionSplitChain hchain

/-- Split-chain data with a rational edge budget imply the ordered insertion
region bound. -/
theorem orderedInsertionRegionBound_of_splitChain
    {n : ℕ} (A : Arrangement n)
    (hsplit : OrderedInsertionSplitChainBound A) :
    OrderedInsertionRegionBound A := by
  intro k hk
  rcases hsplit k hk with ⟨hchain, hbudget⟩
  haveI : Finite
      (ConnectedComponents
        (FreeSpace (prefixArrangement A k (Nat.le_of_lt hk)))) :=
    finite_prefixComponents_of_orderedSplitChain A hsplit k
      (Nat.le_of_lt hk)
  have hnat :
      regionCount (prefixArrangement A (k + 1) (Nat.succ_le_of_lt hk)) ≤
        regionCount (prefixArrangement A k (Nat.le_of_lt hk)) +
          hchain.edgeCount := by
    rw [prefix_succ_eq_snocArrangement A hk]
    exact Insertion.regionCount_snoc_le_add_edgeCount hchain
  have hq :
      regionCountRat (prefixArrangement A (k + 1) (Nat.succ_le_of_lt hk)) ≤
        regionCountRat (prefixArrangement A k (Nat.le_of_lt hk)) +
          (hchain.edgeCount : ℚ) := by
    unfold regionCountRat
    exact_mod_cast hnat
  linarith

/-- Finite induction over prefixes: local insertion inequalities bound every
prefixArrangement by the sum of all earlier-pair contributions seen so far. -/
theorem prefix_regionCountRat_le_of_orderedInsertion
    {n : ℕ} (A : Arrangement n)
    (hinsert : OrderedInsertionRegionBound A) :
    ∀ (k : ℕ) (hk : k ≤ n),
      regionCountRat (prefixArrangement A k hk) ≤
        (∑ r ∈ Finset.range k,
          TheoremOneManuscript.previousPairAdded (pairExcessTable A) r) +
          (k : ℚ) + 1 := by
  intro k
  induction k with
  | zero =>
      intro hk
      rw [regionCountRat_zero]
      simp
  | succ k ih =>
      intro hkSucc
      have hk : k < n := Nat.lt_of_succ_le hkSucc
      have hstep := hinsert k hk
      have hprev := ih (Nat.le_of_lt hk)
      calc
        regionCountRat (prefixArrangement A (Nat.succ k) hkSucc) ≤
            regionCountRat (prefixArrangement A k (Nat.le_of_lt hk)) +
              TheoremOneManuscript.previousPairAdded (pairExcessTable A) k + 1 := by
          simpa [Nat.succ_eq_add_one] using hstep
        _ ≤ ((∑ r ∈ Finset.range k,
                TheoremOneManuscript.previousPairAdded (pairExcessTable A) r) +
              (k : ℚ) + 1) +
            TheoremOneManuscript.previousPairAdded (pairExcessTable A) k + 1 := by
          gcongr
        _ = (∑ r ∈ Finset.range (Nat.succ k),
                TheoremOneManuscript.previousPairAdded (pairExcessTable A) r) +
              (Nat.succ k : ℚ) + 1 := by
          rw [Finset.sum_range_succ]
          simp [Nat.cast_succ]
          ring

/-- The local ordered insertion theorem implies the full planar complement
pair-sum upper inequality for the fixed arrangement. -/
theorem regionCountRat_le_pairSum_of_orderedInsertion
    {n : ℕ} (A : Arrangement n)
    (hinsert : OrderedInsertionRegionBound A) :
    regionCountRat A ≤
      (n : ℚ) + 1 + pairSum n (pairExcessTable A) := by
  have hprefix :=
    prefix_regionCountRat_le_of_orderedInsertion A hinsert n le_rfl
  calc
    regionCountRat A = regionCountRat (prefixArrangement A n le_rfl) := by
      rw [prefix_full]
    _ ≤ (∑ r ∈ Finset.range n,
          TheoremOneManuscript.previousPairAdded (pairExcessTable A) r) +
          (n : ℚ) + 1 := hprefix
    _ = pairSum n (pairExcessTable A) + (n : ℚ) + 1 := by
      rw [TheoremOneManuscript.sum_range_previousPairAdded_eq_pairSum]
    _ = (n : ℚ) + 1 + pairSum n (pairExcessTable A) := by
      ring

/-- Ordered insertion control implies the exact planar-topology inequality
field required by `PlanarTopologyPorts`. -/
theorem crossing_excess_le_pairSum_of_orderedInsertion
    {n : ℕ} (A : Arrangement n)
    (hinsert : OrderedInsertionRegionBound A) :
    regionCountRat A - (n : ℚ) - 1 ≤ pairSum n (pairExcessTable A) := by
  have h := regionCountRat_le_pairSum_of_orderedInsertion A hinsert
  linarith

/-- Universal ordered insertion control is sufficient for the
arbitrary-arrangement planar complement inequality. -/
theorem crossing_excess_le_pairSum_of_insertion
    (hinsert : PlanarInsertionRegionBoundStatement) :
    ∀ {n : ℕ} (A : Arrangement n),
      regionCountRat A - (n : ℚ) - 1 ≤ pairSum n (pairExcessTable A) := by
  intro n A
  exact crossing_excess_le_pairSum_of_orderedInsertion A (hinsert A)

/-- Split-chain control is a stronger route to the same ordered insertion
statement. -/
theorem planarInsertionRegionBoundStatement_of_splitChain
    (hsplit : ∀ {n : ℕ} (A : Arrangement n),
      OrderedInsertionSplitChainBound A) :
    PlanarInsertionRegionBoundStatement := by
  intro n A
  exact orderedInsertionRegionBound_of_splitChain A (hsplit A)

end PlanarInsertion
end EndToEnd
end Concrete
end Lollipop
