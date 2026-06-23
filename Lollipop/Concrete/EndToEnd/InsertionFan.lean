import Lollipop.Concrete.EndToEnd.PairGeometry
import Lollipop.Concrete.EndToEnd.PlanarInsertion

/-!
# Insertion fans

For an ordered prefix insertion, the compactified old/new overlap is the
pointed union of the new lollipop's pair intersections with all earlier
lollipops.  This module proves the finite component budget for that fan and
connects fan-bounded insertion split chains to the global ordered-insertion
reduction.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace InsertionFan

open BigOperators Set

/-- Earlier indices than a fixed insertion index. -/
def previousIndices {n : ℕ} (j : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => i < j)

/-- Compactified pair-intersection fan for an arbitrary finite set of old
lollipops and one new lollipop. -/
def pairIntersectionFan {ι : Type*} (s : Finset ι)
    (A : ι → Lollipop) (L : Lollipop) : Set Sphere2 :=
  pointedFinsetUnion infinity s (fun i => hatPairIntersection (A i) L)

/-- The compactified old/new intersection fan at ordered insertion index `k`. -/
def insertionFan {n : ℕ} (A : Arrangement n)
    (k : ℕ) (hk : k < n) : Set Sphere2 :=
  pairIntersectionFan
    (previousIndices (⟨k, hk⟩ : Fin n)) A (A ⟨k, hk⟩)

/-- The fan distributes as the new compactified carrier intersected with the
pointed union of old compactified carriers. -/
theorem pairIntersectionFan_eq_inter_pointedCarrierUnion
    {ι : Type*} (s : Finset ι) (A : ι → Lollipop) (L : Lollipop) :
    pairIntersectionFan s A L =
      hatCarrier L ∩ pointedFinsetUnion infinity s
        (fun i => hatCarrier (A i)) := by
  ext z
  change
    z ∈ pointedFinsetUnion infinity s
        (fun i => hatPairIntersection (A i) L) ↔
      z ∈ hatCarrier L ∩ pointedFinsetUnion infinity s
        (fun i => hatCarrier (A i))
  rw [mem_pointedFinsetUnion_iff infinity z s
    (fun i => hatPairIntersection (A i) L)]
  simp only [mem_inter_iff]
  rw [
    mem_pointedFinsetUnion_iff infinity z s
      (fun i => hatCarrier (A i))]
  constructor
  · rintro (rfl | ⟨i, hi, hz⟩)
    · exact ⟨infinity_mem_hatCarrier L, Or.inl rfl⟩
    · exact ⟨hz.2, Or.inr ⟨i, hi, hz.1⟩⟩
  · rintro ⟨hzL, rfl | ⟨i, hi, hzA⟩⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨i, hi, ⟨hzA, hzL⟩⟩

/-- Membership in an occupied prefix is membership in one final-arrangement
carrier with natural index below the prefix length. -/
theorem mem_occupied_prefix_iff_exists_lt
    {n : ℕ} (A : Arrangement n) {k : ℕ} (hk : k < n) (x : Point) :
    x ∈ occupied (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk)) ↔
      ∃ i : Fin n, i.1 < k ∧ x ∈ (A i).carrier := by
  constructor
  · intro hx
    obtain ⟨r, hr⟩ := mem_occupied_iff.mp hx
    let i : Fin n := ⟨r.1, lt_trans r.2 hk⟩
    refine ⟨i, r.2, ?_⟩
    change x ∈
      (A ⟨r.1, r.2.trans_le (Nat.le_of_lt hk)⟩).carrier at hr
    simpa [i] using hr
  · rintro ⟨i, hik, hi⟩
    apply mem_occupied_iff.mpr
    let r : Fin k := ⟨i.1, hik⟩
    refine ⟨r, ?_⟩
    change x ∈
      (A ⟨r.1, r.2.trans_le (Nat.le_of_lt hk)⟩).carrier
    simpa [r] using hi

/-- The pointed union of compactified previous carriers is exactly the
compactified occupied set of the old prefix. -/
theorem pointedPreviousCarriers_eq_hatOccupied_prefix
    {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n) :
    pointedFinsetUnion infinity
        (previousIndices (⟨k, hk⟩ : Fin n))
        (fun i => hatCarrier (A i)) =
      hatOccupied (PlanarInsertion.prefixArrangement A k
        (Nat.le_of_lt hk)) := by
  ext z
  cases z using OnePoint.rec with
  | infty =>
      change infinity ∈ pointedFinsetUnion infinity
          (previousIndices (⟨k, hk⟩ : Fin n))
          (fun i => hatCarrier (A i)) ↔
        infinity ∈ hatOccupied (PlanarInsertion.prefixArrangement A k
          (Nat.le_of_lt hk))
      simp [pointedFinsetUnion]
  | coe x =>
      change finitePoint x ∈ pointedFinsetUnion infinity
          (previousIndices (⟨k, hk⟩ : Fin n))
          (fun i => hatCarrier (A i)) ↔
        finitePoint x ∈ hatOccupied (PlanarInsertion.prefixArrangement A k
          (Nat.le_of_lt hk))
      rw [mem_pointedFinsetUnion_iff infinity (finitePoint x)
        (previousIndices (⟨k, hk⟩ : Fin n)) (fun i => hatCarrier (A i))]
      rw [finitePoint_mem_hatOccupied_iff]
      rw [mem_occupied_prefix_iff_exists_lt A hk x]
      constructor
      · rintro (hInf | ⟨i, hi, hmem⟩)
        · exact (finitePoint_ne_infinity x hInf).elim
        · have hlt : i.1 < k := by
            have hltFin : i < (⟨k, hk⟩ : Fin n) := by
              simpa [previousIndices] using hi
            change i.1 < (⟨k, hk⟩ : Fin n).1 at hltFin
            simpa using hltFin
          exact ⟨i, hlt,
            (finitePoint_mem_hatCarrier_iff (A i) x).1 hmem⟩
      · rintro ⟨i, hik, hmem⟩
        exact Or.inr ⟨i, by
          have hltFin : i < (⟨k, hk⟩ : Fin n) := by
            change i.1 < (⟨k, hk⟩ : Fin n).1
            simpa using hik
          simpa [previousIndices] using hltFin,
          (finitePoint_mem_hatCarrier_iff (A i) x).2 hmem⟩

/-- The insertion fan is the actual compactified overlap of the new carrier
with the old prefix occupied carrier. -/
theorem insertionFan_eq_inter_hatOccupied_prefix
    {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n) :
    insertionFan A k hk =
      hatCarrier (A ⟨k, hk⟩) ∩
        hatOccupied (PlanarInsertion.prefixArrangement A k
          (Nat.le_of_lt hk)) := by
  rw [insertionFan, pairIntersectionFan_eq_inter_pointedCarrierUnion,
    pointedPreviousCarriers_eq_hatOccupied_prefix]

/-- Natural component-excess budget for a pair-intersection fan. -/
theorem componentCount_pairIntersectionFan_sub_one_le_sum
    {ι : Type*} (s : Finset ι) (A : ι → Lollipop) (L : Lollipop) :
    componentCount (pairIntersectionFan s A L) - 1 ≤
      ∑ i ∈ s, pairExcessNat (A i) L := by
  unfold pairIntersectionFan
  simpa [pairExcessNat] using
    componentCount_pointedFinsetUnion_sub_one_le_sum_sub_one
      infinity s (fun i => hatPairIntersection (A i) L)
      (by intro i _hi; exact infinity_mem_hatPairIntersection (A i) L)
      (by
        intro i _hi
        exact PairGeometry.finite_connectedComponents_hatPairIntersection
          (A i) L)

/-- Natural component-count budget for a pair-intersection fan. -/
theorem componentCount_pairIntersectionFan_le_one_add_sum
    {ι : Type*} (s : Finset ι) (A : ι → Lollipop) (L : Lollipop) :
    componentCount (pairIntersectionFan s A L) ≤
      1 + ∑ i ∈ s, pairExcessNat (A i) L := by
  have h :=
    componentCount_pairIntersectionFan_sub_one_le_sum s A L
  have h' := Nat.sub_le_iff_le_add.mp h
  omega

/-- Natural component-count budget for the ordered insertion fan. -/
theorem componentCount_insertionFan_le_one_add_sum
    {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n) :
    componentCount (insertionFan A k hk) ≤
      1 + ∑ i ∈ previousIndices (⟨k, hk⟩ : Fin n),
        pairExcessNat (A i) (A ⟨k, hk⟩) := by
  simpa [insertionFan] using
    componentCount_pairIntersectionFan_le_one_add_sum
      (previousIndices (⟨k, hk⟩ : Fin n)) A (A ⟨k, hk⟩)

/-- `previousPairAdded` is the sum over the filtered set of earlier indices. -/
theorem previousPairAdded_eq_sum_previousIndices
    {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n) :
    TheoremOneManuscript.previousPairAdded (pairExcessTable A) k =
      ∑ i ∈ previousIndices (⟨k, hk⟩ : Fin n),
        pairExcess (A i) (A ⟨k, hk⟩) := by
  classical
  unfold TheoremOneManuscript.previousPairAdded
  simp only [dif_pos hk]
  unfold TheoremOneManuscript.previousPairSum previousIndices pairExcessTable
  rw [Finset.sum_filter]

/-- Casted natural pair-excess sum equals the rational previous-pair budget. -/
theorem natCast_sum_pairExcessNat_eq_previousPairAdded
    {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n) :
    ((∑ i ∈ previousIndices (⟨k, hk⟩ : Fin n),
        pairExcessNat (A i) (A ⟨k, hk⟩) : ℕ) : ℚ) =
      TheoremOneManuscript.previousPairAdded (pairExcessTable A) k := by
  rw [previousPairAdded_eq_sum_previousIndices A k hk]
  simp [pairExcess]

/-- Rational form of the insertion-fan component budget. -/
theorem componentCount_insertionFan_cast_le_previousPairAdded_add_one
    {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n) :
    (componentCount (insertionFan A k hk) : ℚ) ≤
      TheoremOneManuscript.previousPairAdded (pairExcessTable A) k + 1 := by
  have hnat := componentCount_insertionFan_le_one_add_sum A k hk
  calc
    (componentCount (insertionFan A k hk) : ℚ) ≤
        ((1 + ∑ i ∈ previousIndices (⟨k, hk⟩ : Fin n),
          pairExcessNat (A i) (A ⟨k, hk⟩) : ℕ) : ℚ) := by
      exact_mod_cast hnat
    _ = TheoremOneManuscript.previousPairAdded (pairExcessTable A) k + 1 := by
      rw [Nat.cast_add, Nat.cast_one,
        natCast_sum_pairExcessNat_eq_previousPairAdded A k hk]
      ring

/-- Strong fan-bounded split-chain input for one fixed final arrangement. -/
def OrderedInsertionFanSplitChainBound {n : ℕ} (A : Arrangement n) : Prop :=
  ∀ (k : ℕ) (hk : k < n),
    ∃ h : Insertion.InsertionSplitChain
        (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk))
        (A ⟨k, hk⟩),
      (h.edgeCount : ℚ) ≤ (componentCount (insertionFan A k hk) : ℚ)

/-- Fan-bounded split chains imply the older previous-pair split-chain input. -/
theorem orderedInsertionSplitChainBound_of_fan
    {n : ℕ} (A : Arrangement n)
    (hfan : OrderedInsertionFanSplitChainBound A) :
    PlanarInsertion.OrderedInsertionSplitChainBound A := by
  intro k hk
  rcases hfan k hk with ⟨hchain, hbudget⟩
  refine ⟨hchain, ?_⟩
  have hfanBudget :=
    componentCount_insertionFan_cast_le_previousPairAdded_add_one A k hk
  exact hbudget.trans hfanBudget

/-- Universal fan-bounded split-chain data imply the ordered insertion region
bound used by `PlanarTopologyPorts`. -/
theorem planarInsertionRegionBoundStatement_of_fan
    (hfan : ∀ {n : ℕ} (A : Arrangement n),
      OrderedInsertionFanSplitChainBound A) :
    PlanarInsertion.PlanarInsertionRegionBoundStatement := by
  exact PlanarInsertion.planarInsertionRegionBoundStatement_of_splitChain
    (fun A => orderedInsertionSplitChainBound_of_fan A (hfan A))

/-- Build the planar topology port from fan-bounded insertion split chains and
the still-separate generic Euler equation. -/
def planarTopologyPorts_of_fan
    (hfan : ∀ {n : ℕ} (A : Arrangement n),
      OrderedInsertionFanSplitChainBound A)
    (hgeneric :
      ∀ {n : ℕ} {A : Arrangement n}, IsGeneric A →
        regionCountRat A = ((totalCrossingsNat A : ℕ) : ℚ) + (n : ℚ) + 1) :
    PlanarTopologyPorts :=
  PlanarTopologyPorts.ofSplitChain
    (fun A => orderedInsertionSplitChainBound_of_fan A (hfan A))
    hgeneric

end InsertionFan
end EndToEnd
end Concrete
end Lollipop
