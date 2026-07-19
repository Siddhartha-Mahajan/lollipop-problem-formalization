import old_lean_folder.Concrete.EndToEnd.PairGeometry
import old_lean_folder.Concrete.EndToEnd.PlanarInsertion

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

/-- Union of a family of sets over a finite index set. -/
def finsetSetUnion {ι X : Type*} (s : Finset ι) (S : ι → Set X) :
    Set X :=
  ⋃ i : {i // i ∈ s}, S i.1

theorem mem_finsetSetUnion_iff
    {ι X : Type*} (s : Finset ι) (S : ι → Set X) (x : X) :
    x ∈ finsetSetUnion s S ↔ ∃ i ∈ s, x ∈ S i := by
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
    exact ⟨i.1, i.2, hi⟩
  · rintro ⟨i, hi, hx⟩
    exact Set.mem_iUnion_of_mem (⟨i, hi⟩ : {i // i ∈ s}) hx

/-- Inserting one index adds one ordinary binary union. -/
theorem finsetSetUnion_insert
    {ι X : Type*} [DecidableEq ι]
    (s : Finset ι) (S : ι → Set X) (a : ι) :
    finsetSetUnion (insert a s) S = finsetSetUnion s S ∪ S a := by
  ext x
  rw [mem_finsetSetUnion_iff, mem_union]
  constructor
  · rintro ⟨i, hi, hx⟩
    rw [Finset.mem_insert] at hi
    rcases hi with rfl | hi
    · exact Or.inr hx
    · exact Or.inl ((mem_finsetSetUnion_iff s S x).2 ⟨i, hi, hx⟩)
  · rintro (hx | hx)
    · rcases (mem_finsetSetUnion_iff s S x).1 hx with ⟨i, hi, hx⟩
      exact ⟨i, Finset.mem_insert_of_mem hi, hx⟩
    · exact ⟨a, Finset.mem_insert_self a s, hx⟩

/-- A finite union of finite sets is finite. -/
theorem finite_finsetSetUnion
    {ι X : Type*} [DecidableEq ι]
    (s : Finset ι) (S : ι → Set X)
    (hfinite : ∀ i ∈ s, (S i).Finite) :
    (finsetSetUnion s S).Finite := by
  classical
  revert hfinite
  refine Finset.induction_on s ?_ ?_
  · intro _hfinite
    simp [finsetSetUnion]
  · intro a s ha ih hfinite
    have hfiniteS : ∀ i ∈ s, (S i).Finite := by
      intro i hi
      exact hfinite i (Finset.mem_insert_of_mem hi)
    have hfiniteA : (S a).Finite :=
      hfinite a (Finset.mem_insert_self a s)
    rw [finsetSetUnion_insert]
    exact (ih hfiniteS).union hfiniteA

/-- Pairwise disjointness restricted to a finite index set. -/
def PairwiseDisjointOn {ι X : Type*}
    (s : Finset ι) (S : ι → Set X) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (S i) (S j)

/-- The cardinality of a finite pairwise-disjoint union is the sum of the
individual cardinalities. -/
theorem ncard_finsetSetUnion_eq_sum
    {ι X : Type*} [DecidableEq ι]
    (s : Finset ι) (S : ι → Set X)
    (hfinite : ∀ i ∈ s, (S i).Finite)
    (hdisjoint : PairwiseDisjointOn s S) :
    (finsetSetUnion s S).ncard = ∑ i ∈ s, (S i).ncard := by
  classical
  revert hfinite hdisjoint
  refine Finset.induction_on s ?_ ?_
  · intro _hfinite _hdisjoint
    simp [finsetSetUnion]
  · intro a s ha ih hfinite hdisjoint
    have hfiniteS : ∀ i ∈ s, (S i).Finite := by
      intro i hi
      exact hfinite i (Finset.mem_insert_of_mem hi)
    have hfiniteA : (S a).Finite :=
      hfinite a (Finset.mem_insert_self a s)
    have hdisjointS : PairwiseDisjointOn s S := by
      intro i hi j hj hij
      exact hdisjoint i (Finset.mem_insert_of_mem hi)
        j (Finset.mem_insert_of_mem hj) hij
    have hhead : Disjoint (finsetSetUnion s S) (S a) := by
      refine Set.disjoint_left.2 ?_
      intro x hxUnion hxA
      rcases (mem_finsetSetUnion_iff s S x).1 hxUnion with
        ⟨i, hi, hxi⟩
      have hia : i ≠ a := by
        intro hia
        subst i
        exact ha hi
      have hd : Disjoint (S i) (S a) :=
        hdisjoint i (Finset.mem_insert_of_mem hi)
          a (Finset.mem_insert_self a s) hia
      exact Set.disjoint_left.1 hd hxi hxA
    have hfiniteUnion : (finsetSetUnion s S).Finite :=
      finite_finsetSetUnion s S hfiniteS
    rw [finsetSetUnion_insert,
      Set.ncard_union_eq hhead hfiniteUnion hfiniteA,
      ih hfiniteS hdisjointS,
      Finset.sum_insert ha]
    omega

/-- Ordinary finite union of old/new carrier intersections. -/
def ordinaryPairIntersectionUnion {ι : Type*}
    (s : Finset ι) (A : ι → Lollipop) (L : Lollipop) : Set Point :=
  finsetSetUnion s (fun i => pairCrossingSet (A i) L)

theorem mem_ordinaryPairIntersectionUnion_iff
    {ι : Type*} (s : Finset ι) (A : ι → Lollipop)
    (L : Lollipop) (x : Point) :
    x ∈ ordinaryPairIntersectionUnion s A L ↔
      ∃ i ∈ s, x ∈ pairCrossingSet (A i) L := by
  exact mem_finsetSetUnion_iff s _ x

/-- The pointed compactified fan is the compactification of the ordinary
finite union of old/new carrier intersections. -/
theorem pairIntersectionFan_eq_finiteLift_ordinaryPairIntersectionUnion
    {ι : Type*} (s : Finset ι) (A : ι → Lollipop) (L : Lollipop) :
    pairIntersectionFan s A L =
      finiteLift (ordinaryPairIntersectionUnion s A L) ∪ {infinity} := by
  ext z
  cases z using OnePoint.rec with
  | infty =>
      change infinity ∈ pairIntersectionFan s A L ↔
        infinity ∈ finiteLift (ordinaryPairIntersectionUnion s A L) ∪
          {infinity}
      simp [pairIntersectionFan]
  | coe x =>
      change finitePoint x ∈ pairIntersectionFan s A L ↔
        finitePoint x ∈
          finiteLift (ordinaryPairIntersectionUnion s A L) ∪ {infinity}
      rw [pairIntersectionFan,
        mem_pointedFinsetUnion_iff infinity (finitePoint x) s
          (fun i => hatPairIntersection (A i) L)]
      constructor
      · rintro (hInfinity | ⟨i, hi, hpair⟩)
        · exact (finitePoint_ne_infinity x hInfinity).elim
        · apply Or.inl
          rw [mem_finiteLift_iff]
          apply (mem_ordinaryPairIntersectionUnion_iff s A L x).2
          refine ⟨i, hi, ?_⟩
          simpa [hatPairIntersection, hatCarrier, pairCrossingSet] using hpair
      · intro hx
        rcases hx with hx | hInfinity
        · rw [mem_finiteLift_iff] at hx
          rcases (mem_ordinaryPairIntersectionUnion_iff s A L x).1 hx with
            ⟨i, hi, hpair⟩
          exact Or.inr ⟨i, hi, by
            simpa [hatPairIntersection, hatCarrier, pairCrossingSet]
              using hpair⟩
        · simp at hInfinity

/-- The ordinary pair intersections in a fan are pairwise disjoint. -/
def PairIntersectionsPairwiseDisjoint {ι : Type*}
    (s : Finset ι) (A : ι → Lollipop) (L : Lollipop) : Prop :=
  PairwiseDisjointOn s (fun i => pairCrossingSet (A i) L)

/-- Under finite pair intersections and no triple points, the fan component
count is exactly one plus the sum of robust pair excesses. -/
theorem componentCount_pairIntersectionFan_eq_one_add_sum
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → Lollipop) (L : Lollipop)
    (hfinite : ∀ i ∈ s, (pairCrossingSet (A i) L).Finite)
    (hdisjoint : PairIntersectionsPairwiseDisjoint s A L) :
    componentCount (pairIntersectionFan s A L) =
      1 + ∑ i ∈ s, pairExcessNat (A i) L := by
  classical
  have hUnionFinite :
      (ordinaryPairIntersectionUnion s A L).Finite :=
    finite_finsetSetUnion s
      (fun i => pairCrossingSet (A i) L) hfinite
  have hUnionCard :
      (ordinaryPairIntersectionUnion s A L).ncard =
        ∑ i ∈ s, pairCrossingCount (A i) L :=
    ncard_finsetSetUnion_eq_sum s
      (fun i => pairCrossingSet (A i) L) hfinite hdisjoint
  have hcount :
      componentCount
          (finiteLift (ordinaryPairIntersectionUnion s A L) ∪ {infinity}) =
        (ordinaryPairIntersectionUnion s A L).ncard + 1 := by
    let U : Set Sphere2 :=
      finiteLift (ordinaryPairIntersectionUnion s A L) ∪ {infinity}
    change componentCount U =
      (ordinaryPairIntersectionUnion s A L).ncard + 1
    have hsub :
        componentCount U - 1 =
          (ordinaryPairIntersectionUnion s A L).ncard := by
      simpa [U] using
        componentCount_finiteLift_union_infinity_sub_one hUnionFinite
    haveI : Finite (ConnectedComponents U) := by
      dsimp [U]
      exact finite_connectedComponents_finiteLift_union_infinity hUnionFinite
    haveI : Nonempty (ConnectedComponents U) :=
      ConnectedComponents.nonempty_iff_nonempty.mpr
        ⟨⟨infinity, by simp [U]⟩⟩
    have hpos : 0 < componentCount U := by
      exact Nat.card_pos
    omega
  rw [pairIntersectionFan_eq_finiteLift_ordinaryPairIntersectionUnion,
    hcount, hUnionCard]
  have hsum :
      (∑ i ∈ s, pairCrossingCount (A i) L) =
        ∑ i ∈ s, pairExcessNat (A i) L := by
    apply Finset.sum_congr rfl
    intro i hi
    exact (pairExcessNat_eq_pairCrossingCount_of_finite
      (hfinite i hi)).symm
  rw [hsum]
  omega

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

/-- Natural exact count for an ordered insertion fan under finite pair
intersections and no triple points along that insertion. -/
theorem componentCount_insertionFan_eq_one_add_sum
    {n : ℕ} {A : Arrangement n} (k : ℕ) (hk : k < n)
    (hfinite : ∀ i ∈ previousIndices (⟨k, hk⟩ : Fin n),
      (pairCrossingSet (A i) (A ⟨k, hk⟩)).Finite)
    (hdisjoint : PairIntersectionsPairwiseDisjoint
      (previousIndices (⟨k, hk⟩ : Fin n)) A (A ⟨k, hk⟩)) :
    componentCount (insertionFan A k hk) =
      1 + ∑ i ∈ previousIndices (⟨k, hk⟩ : Fin n),
        pairExcessNat (A i) (A ⟨k, hk⟩) := by
  simpa [insertionFan] using
    componentCount_pairIntersectionFan_eq_one_add_sum
      (previousIndices (⟨k, hk⟩ : Fin n)) A (A ⟨k, hk⟩)
      hfinite hdisjoint

/-- Genericity gives finite previous/new pair intersections. -/
theorem previous_pair_finite_of_isGeneric
    {n : ℕ} {A : Arrangement n} (hA : IsGeneric A)
    (k : ℕ) (hk : k < n) :
    ∀ i ∈ previousIndices (⟨k, hk⟩ : Fin n),
      (pairCrossingSet (A i) (A ⟨k, hk⟩)).Finite := by
  intro i hi
  have hlt : i < (⟨k, hk⟩ : Fin n) := by
    simpa [previousIndices] using hi
  exact hA.pair_finite i ⟨k, hk⟩ (ne_of_lt hlt)

/-- Generic no-triple position gives disjoint previous/new pair
intersections. -/
theorem previous_pair_disjoint_of_isGeneric
    {n : ℕ} {A : Arrangement n} (hA : IsGeneric A)
    (k : ℕ) (hk : k < n) :
    PairIntersectionsPairwiseDisjoint
      (previousIndices (⟨k, hk⟩ : Fin n)) A (A ⟨k, hk⟩) := by
  intro i hi j hj hij
  have hik : i < (⟨k, hk⟩ : Fin n) := by
    simpa [previousIndices] using hi
  have hjk : j < (⟨k, hk⟩ : Fin n) := by
    simpa [previousIndices] using hj
  refine Set.disjoint_left.2 ?_
  intro x hxi hxj
  have hno :=
    hA.no_triple i j ⟨k, hk⟩ hij (ne_of_lt hik) (ne_of_lt hjk)
  have hxij : x ∈ pairCrossingSet (A i) (A j) := ⟨hxi.1, hxj.1⟩
  have hxk : x ∈ (A ⟨k, hk⟩).carrier := hxi.2
  have hxempty : x ∈ (∅ : Set Point) := by
    have hxinter :
        x ∈ pairCrossingSet (A i) (A j) ∩
          (A ⟨k, hk⟩).carrier := ⟨hxij, hxk⟩
    rw [← hno]
    exact hxinter
  simp at hxempty

/-- Generic arrangements have exact ordered insertion fan counts. -/
theorem componentCount_insertionFan_eq_one_add_sum_of_isGeneric
    {n : ℕ} {A : Arrangement n} (hA : IsGeneric A)
    (k : ℕ) (hk : k < n) :
    componentCount (insertionFan A k hk) =
      1 + ∑ i ∈ previousIndices (⟨k, hk⟩ : Fin n),
        pairExcessNat (A i) (A ⟨k, hk⟩) :=
  componentCount_insertionFan_eq_one_add_sum k hk
    (previous_pair_finite_of_isGeneric hA k hk)
    (previous_pair_disjoint_of_isGeneric hA k hk)

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

/-- Rational exact count for an ordered insertion fan. -/
theorem componentCount_insertionFan_cast_eq_previousPairAdded_add_one
    {n : ℕ} {A : Arrangement n} (k : ℕ) (hk : k < n)
    (hfinite : ∀ i ∈ previousIndices (⟨k, hk⟩ : Fin n),
      (pairCrossingSet (A i) (A ⟨k, hk⟩)).Finite)
    (hdisjoint : PairIntersectionsPairwiseDisjoint
      (previousIndices (⟨k, hk⟩ : Fin n)) A (A ⟨k, hk⟩)) :
    (componentCount (insertionFan A k hk) : ℚ) =
      TheoremOneManuscript.previousPairAdded (pairExcessTable A) k + 1 := by
  have hnat :=
    componentCount_insertionFan_eq_one_add_sum k hk hfinite hdisjoint
  calc
    (componentCount (insertionFan A k hk) : ℚ) =
        ((1 + ∑ i ∈ previousIndices (⟨k, hk⟩ : Fin n),
          pairExcessNat (A i) (A ⟨k, hk⟩) : ℕ) : ℚ) := by
      exact_mod_cast hnat
    _ = TheoremOneManuscript.previousPairAdded (pairExcessTable A) k + 1 := by
      rw [Nat.cast_add, Nat.cast_one,
        natCast_sum_pairExcessNat_eq_previousPairAdded A k hk]
      ring

/-- Rational exact count for an ordered insertion fan in generic position. -/
theorem componentCount_insertionFan_cast_eq_previousPairAdded_add_one_of_isGeneric
    {n : ℕ} {A : Arrangement n} (hA : IsGeneric A)
    (k : ℕ) (hk : k < n) :
    (componentCount (insertionFan A k hk) : ℚ) =
      TheoremOneManuscript.previousPairAdded (pairExcessTable A) k + 1 :=
  componentCount_insertionFan_cast_eq_previousPairAdded_add_one k hk
    (previous_pair_finite_of_isGeneric hA k hk)
    (previous_pair_disjoint_of_isGeneric hA k hk)

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

/-- Exact fan-sized split-chain input for one fixed final arrangement. -/
def OrderedExactInsertionFanSplitChain {n : ℕ} (A : Arrangement n) : Prop :=
  ∀ (k : ℕ) (hk : k < n),
    ∃ h : Insertion.ExactInsertionSplitChain
        (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk))
        (A ⟨k, hk⟩),
      h.edgeCount = componentCount (insertionFan A k hk)

/-- Exact fan-sized chains imply the bounded fan-chain input. -/
theorem orderedInsertionFanSplitChainBound_of_exact
    {n : ℕ} {A : Arrangement n}
    (hexact : OrderedExactInsertionFanSplitChain A) :
    OrderedInsertionFanSplitChainBound A := by
  intro k hk
  rcases hexact k hk with ⟨hchain, hcount⟩
  refine ⟨hchain.toInsertionSplitChain, ?_⟩
  change (hchain.edgeCount : ℚ) ≤
    (componentCount (insertionFan A k hk) : ℚ)
  rw [hcount]

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

/-- Exact fan-region recurrence for one fixed final arrangement. -/
def OrderedInsertionFanRegionEquality {n : ℕ} (A : Arrangement n) : Prop :=
  ∀ (k : ℕ) (hk : k < n),
    regionCountRat
        (PlanarInsertion.prefixArrangement A (k + 1)
          (Nat.succ_le_of_lt hk)) =
      regionCountRat
        (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk)) +
        (componentCount (insertionFan A k hk) : ℚ)

/-- Exact fan-sized split chains imply the exact fan-region recurrence. -/
theorem orderedInsertionFanRegionEquality_of_exactFan
    {n : ℕ} (A : Arrangement n)
    (hexact : OrderedExactInsertionFanSplitChain A) :
    OrderedInsertionFanRegionEquality A := by
  intro k hk
  rcases hexact k hk with ⟨hchain, hcount⟩
  have hfanBound : OrderedInsertionFanSplitChainBound A :=
    orderedInsertionFanSplitChainBound_of_exact hexact
  have hsplit : PlanarInsertion.OrderedInsertionSplitChainBound A :=
    orderedInsertionSplitChainBound_of_fan A hfanBound
  haveI : Finite
      (ConnectedComponents
        (FreeSpace
          (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk)))) :=
    PlanarInsertion.finite_prefixComponents_of_orderedSplitChain A hsplit k
      (Nat.le_of_lt hk)
  have hnat :
      regionCount
          (PlanarInsertion.prefixArrangement A (k + 1)
            (Nat.succ_le_of_lt hk)) =
        regionCount
          (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk)) +
          componentCount (insertionFan A k hk) := by
    rw [PlanarInsertion.prefix_succ_eq_snocArrangement A hk]
    have hstep := Insertion.regionCount_snoc_eq_add_edgeCount hchain
    rw [hstep, hcount]
  unfold regionCountRat
  exact_mod_cast hnat

/-- Exact ordered insertion recurrence in the previous-pair coordinates used
by the manuscript algebra. -/
def OrderedInsertionRegionEquality {n : ℕ} (A : Arrangement n) : Prop :=
  ∀ (k : ℕ) (hk : k < n),
    regionCountRat
        (PlanarInsertion.prefixArrangement A (k + 1)
          (Nat.succ_le_of_lt hk)) =
      regionCountRat
        (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk)) +
        TheoremOneManuscript.previousPairAdded (pairExcessTable A) k + 1

/-- Exact fan-region recurrence plus generic fan counts gives the exact
previous-pair insertion recurrence. -/
theorem orderedInsertionRegionEquality_of_fanRegionEquality_of_isGeneric
    {n : ℕ} {A : Arrangement n}
    (hA : IsGeneric A)
    (hfan : OrderedInsertionFanRegionEquality A) :
    OrderedInsertionRegionEquality A := by
  intro k hk
  calc
    regionCountRat
        (PlanarInsertion.prefixArrangement A (k + 1)
          (Nat.succ_le_of_lt hk)) =
      regionCountRat
        (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk)) +
        (componentCount (insertionFan A k hk) : ℚ) := hfan k hk
    _ =
      regionCountRat
        (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk)) +
        TheoremOneManuscript.previousPairAdded (pairExcessTable A) k + 1 := by
      rw [componentCount_insertionFan_cast_eq_previousPairAdded_add_one_of_isGeneric
        hA k hk]
      ring

/-- Exact fan-sized split chains plus genericity give the exact previous-pair
insertion recurrence. -/
theorem orderedInsertionRegionEquality_of_exactFan_of_isGeneric
    {n : ℕ} {A : Arrangement n}
    (hA : IsGeneric A)
    (hexact : OrderedExactInsertionFanSplitChain A) :
    OrderedInsertionRegionEquality A :=
  orderedInsertionRegionEquality_of_fanRegionEquality_of_isGeneric hA
    (orderedInsertionFanRegionEquality_of_exactFan A hexact)

/-- Finite induction over prefixes for exact ordered insertion recurrences. -/
theorem prefix_regionCountRat_eq_of_orderedInsertion
    {n : ℕ} (A : Arrangement n)
    (hinsert : OrderedInsertionRegionEquality A) :
    ∀ (k : ℕ) (hk : k ≤ n),
      regionCountRat (PlanarInsertion.prefixArrangement A k hk) =
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
        regionCountRat
            (PlanarInsertion.prefixArrangement A (Nat.succ k) hkSucc) =
          regionCountRat
              (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk)) +
            TheoremOneManuscript.previousPairAdded (pairExcessTable A) k +
            1 := by
          simpa [Nat.succ_eq_add_one] using hstep
        _ = ((∑ r ∈ Finset.range k,
                TheoremOneManuscript.previousPairAdded (pairExcessTable A) r) +
              (k : ℚ) + 1) +
            TheoremOneManuscript.previousPairAdded (pairExcessTable A) k +
            1 := by
          rw [hprev]
        _ = (∑ r ∈ Finset.range (Nat.succ k),
                TheoremOneManuscript.previousPairAdded (pairExcessTable A) r) +
              (Nat.succ k : ℚ) + 1 := by
          rw [Finset.sum_range_succ]
          simp [Nat.cast_succ]
          ring

/-- Exact ordered insertion recurrence gives the pair-excess region equation. -/
theorem regionCountRat_eq_pairSum_of_orderedInsertion
    {n : ℕ} (A : Arrangement n)
    (hinsert : OrderedInsertionRegionEquality A) :
    regionCountRat A =
      pairSum n (pairExcessTable A) + (n : ℚ) + 1 := by
  have hprefix :=
    prefix_regionCountRat_eq_of_orderedInsertion A hinsert n le_rfl
  calc
    regionCountRat A =
        regionCountRat (PlanarInsertion.prefixArrangement A n le_rfl) := by
      rw [PlanarInsertion.prefix_full]
    _ = (∑ r ∈ Finset.range n,
          TheoremOneManuscript.previousPairAdded (pairExcessTable A) r) +
          (n : ℚ) + 1 := hprefix
    _ = pairSum n (pairExcessTable A) + (n : ℚ) + 1 := by
      rw [TheoremOneManuscript.sum_range_previousPairAdded_eq_pairSum]

/-- For a generic arrangement, robust pair excess is exactly ordinary finite
crossing count after summing over all unordered pairs. -/
theorem pairSum_pairExcessTable_eq_totalCrossingsNat_of_isGeneric
    {n : ℕ} {A : Arrangement n} (hA : IsGeneric A) :
    pairSum n (pairExcessTable A) = ((totalCrossingsNat A : ℕ) : ℚ) := by
  classical
  unfold pairSum totalCrossingsNat pairExcessTable pairExcess
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hp_lt : p.1 < p.2 := by
    rw [Lollipop.pairFinset, Finset.mem_filter] at hp
    exact hp.2
  exact_mod_cast
    (pairExcessNat_eq_pairCrossingCount_of_finite
      (hA.pair_finite p.1 p.2 (ne_of_lt hp_lt)))

/-- Exact generic fan chains prove the generic Euler-region equation needed
by `PlanarTopologyPorts`. -/
theorem generic_region_eq_of_exactFan
    {n : ℕ} {A : Arrangement n}
    (hA : IsGeneric A)
    (hexact : OrderedExactInsertionFanSplitChain A) :
    regionCountRat A = ((totalCrossingsNat A : ℕ) : ℚ) + (n : ℚ) + 1 := by
  calc
    regionCountRat A =
        pairSum n (pairExcessTable A) + (n : ℚ) + 1 :=
      regionCountRat_eq_pairSum_of_orderedInsertion A
        (orderedInsertionRegionEquality_of_exactFan_of_isGeneric hA hexact)
    _ = ((totalCrossingsNat A : ℕ) : ℚ) + (n : ℚ) + 1 := by
      rw [pairSum_pairExcessTable_eq_totalCrossingsNat_of_isGeneric hA]

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

/-- Build the planar topology port from fan-bounded arbitrary insertions and
exact fan-sized generic insertions. -/
def planarTopologyPorts_of_fan_and_genericExactFan
    (hfan : ∀ {n : ℕ} (A : Arrangement n),
      OrderedInsertionFanSplitChainBound A)
    (hexact :
      ∀ {n : ℕ} {A : Arrangement n}, IsGeneric A →
        OrderedExactInsertionFanSplitChain A) :
    PlanarTopologyPorts :=
  planarTopologyPorts_of_fan hfan
    (fun hA => generic_region_eq_of_exactFan hA (hexact hA))

/-- Sharper remaining planar-topology package after the insertion-fan
reduction.  The arbitrary field is the upper-bound insertion theorem; the
generic field is the exact Euler-region theorem restricted to generic
arrangements. -/
structure FanTopologyPorts : Prop where
  arbitrary_fan_bound :
    ∀ {n : ℕ} (A : Arrangement n), OrderedInsertionFanSplitChainBound A
  generic_exact_fan :
    ∀ {n : ℕ} {A : Arrangement n}, IsGeneric A →
      OrderedExactInsertionFanSplitChain A

/-- The fan-topology package supplies the older planar-topology port. -/
def FanTopologyPorts.toPlanarTopologyPorts
    (ports : FanTopologyPorts) : PlanarTopologyPorts :=
  planarTopologyPorts_of_fan_and_genericExactFan
    ports.arbitrary_fan_bound ports.generic_exact_fan

end InsertionFan
end EndToEnd
end Concrete
end Lollipop
