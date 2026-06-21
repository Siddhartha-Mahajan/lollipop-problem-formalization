import Lollipop.Internal.Manuscript.ExplicitInputs.ClusteredLower

/-!
Pair-counted clustered Karlsson lower construction data.

`ClusteredLower.lean` exposes the individual cluster map, but its witness still
contains the collapsed equality from the individual-pair sum to the
four-cluster Karlsson table.  This module splits that equality into finite
pair-count facts.  Lean proves:

* the individual pair sum is the sum over oriented cluster-label pair counts;
* the oriented count table collapses to Karlsson's six unordered inter-cluster
  terms plus the four same-cluster terms;
* the resulting table is the already-checked lower polynomial.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace ExplicitInputs

universe u

open BigOperators

/-- Fiber of a cluster map over one Karlsson base cluster. -/
def clusterFiber {n : Nat} (cluster : Fin n → Fin 4) (r : Fin 4) :
    Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun i => cluster i = r)

/-- The `pairFinset` pairs whose two endpoints lie in a subset `s` are counted
by `#s choose 2`.  This is the subset version of `pairFinset_card`. -/
theorem pairFinset_filter_mem_card
    {n : Nat} (s : Finset (Fin n)) :
    ((pairFinset n).filter (fun p : Fin n × Fin n => p.1 ∈ s ∧ p.2 ∈ s)).card =
      s.card.choose 2 := by
  classical
  have hfilter :
      (pairFinset n).filter (fun p : Fin n × Fin n => p.1 ∈ s ∧ p.2 ∈ s) =
        s.offDiag.filter (fun p : Fin n × Fin n => p.1 < p.2) := by
    ext p
    by_cases hlt : p.1 < p.2
    · simp [pairFinset, Finset.mem_offDiag, hlt, ne_of_lt hlt,
        and_comm]
    · simp [pairFinset, Finset.mem_offDiag, hlt]
  rw [hfilter]
  have hsum :=
    Finset.sum_sym2_filter_not_isDiag (s := s) (p := fun _ => (1 : Nat))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  have hsumNat :
      (s.sym2.filter fun a : Sym2 (Fin n) => ¬a.IsDiag).card =
        (s.offDiag.filter fun p : Fin n × Fin n => p.1 < p.2).card := by
    exact_mod_cast hsum
  rw [← hsumNat, Finset.sym2_eq_image, Sym2.filter_image_mk_not_isDiag]
  exact Sym2.card_image_offDiag s

/-- For two disjoint subsets, the two canonical orientations of inter-set
pairs in `pairFinset` add up to the product of the subset cardinalities. -/
theorem pairFinset_filter_inter_card
    {n : Nat} (s t : Finset (Fin n)) (hst : Disjoint s t) :
    ((pairFinset n).filter
        (fun p : Fin n × Fin n => p.1 ∈ s ∧ p.2 ∈ t)).card +
      ((pairFinset n).filter
        (fun p : Fin n × Fin n => p.1 ∈ t ∧ p.2 ∈ s)).card =
        s.card * t.card := by
  classical
  let stLT : Finset (Fin n × Fin n) :=
    (s ×ˢ t).filter (fun p : Fin n × Fin n => p.1 < p.2)
  let stGT : Finset (Fin n × Fin n) :=
    (s ×ˢ t).filter (fun p : Fin n × Fin n => p.2 < p.1)
  have hfirst :
      stLT =
        (pairFinset n).filter
          (fun p : Fin n × Fin n => p.1 ∈ s ∧ p.2 ∈ t) := by
    ext p
    simp [stLT, pairFinset, and_comm]
  let swapEmbedding : Fin n × Fin n ↪ Fin n × Fin n :=
    { toFun := fun p => (p.2, p.1)
      inj' := by
        intro p q h
        cases p
        cases q
        simp at h
        simp [h.1, h.2] }
  have hmap :
      stGT.map swapEmbedding =
        (pairFinset n).filter
          (fun p : Fin n × Fin n => p.1 ∈ t ∧ p.2 ∈ s) := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_map.mp hp with ⟨q, hq, hqp⟩
      simp [stGT] at hq
      rw [← hqp]
      simp [swapEmbedding, pairFinset, hq.1.1, hq.1.2, hq.2]
    · intro hp
      simp [pairFinset] at hp
      refine Finset.mem_map.mpr ⟨(p.2, p.1), ?_, ?_⟩
      · simp [stGT, hp.2.2, hp.2.1, hp.1]
      · simp [swapEmbedding]
  have hsecond :
      stGT.card =
        ((pairFinset n).filter
          (fun p : Fin n × Fin n => p.1 ∈ t ∧ p.2 ∈ s)).card := by
    rw [← hmap, Finset.card_map]
  have hsplit : s ×ˢ t = stLT ∪ stGT := by
    ext p
    constructor
    · intro hp
      have hps : p.1 ∈ s := (Finset.mem_product.mp hp).1
      have hpt : p.2 ∈ t := (Finset.mem_product.mp hp).2
      have hne : p.1 ≠ p.2 := by
        intro hp_eq
        have hp2s : p.2 ∈ s := by simpa [hp_eq] using hps
        exact (Finset.disjoint_left.mp hst) hp2s hpt
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Finset.mem_union.mpr (Or.inl (by simp [stLT, hp, hlt]))
      · exact Finset.mem_union.mpr (Or.inr (by simp [stGT, hp, hgt]))
    · intro hp
      rcases Finset.mem_union.mp hp with hp | hp
      · exact (Finset.mem_filter.mp hp).1
      · exact (Finset.mem_filter.mp hp).1
  have hdisj : Disjoint stLT stGT := by
    rw [Finset.disjoint_left]
    intro p hpLT hpGT
    have hlt : p.1 < p.2 := (Finset.mem_filter.mp hpLT).2
    have hgt : p.2 < p.1 := (Finset.mem_filter.mp hpGT).2
    exact (not_lt_of_gt hgt) hlt
  have hcard :
      (s ×ˢ t).card = stLT.card + stGT.card := by
    rw [hsplit, Finset.card_union_of_disjoint hdisj]
  rw [← hfirst, ← hsecond]
  rw [← Finset.card_product]
  exact hcard.symm

/-- Number of unordered lollipop pairs, represented by `pairFinset n`, whose
first representative lies in cluster `a` and second representative lies in
cluster `b`.  The orientation is only the canonical `i < j` orientation of the
underlying unordered pair; later inter-cluster hypotheses add both directions. -/
def orientedClusterPairCountQ
    {n : Nat} (cluster : Fin n → Fin 4) (a b : Fin 4) : Rat :=
  (((pairFinset n).filter
    (fun p : Fin n × Fin n => cluster p.1 = a ∧ cluster p.2 = b)).card : Rat)

/-- Karlsson's individual-pair sum regrouped by oriented cluster labels. -/
def orientedKarlssonPairCountedCrossings
    {n : Nat} (cluster : Fin n → Fin 4) : Rat :=
  ∑ a : Fin 4, ∑ b : Fin 4,
    karlssonClusterPairCrossing a b *
      orientedClusterPairCountQ cluster a b

theorem orientedClusterPairCountQ_eq_indicator_sum
    {n : Nat} (cluster : Fin n → Fin 4) (a b : Fin 4) :
    orientedClusterPairCountQ cluster a b =
      ∑ p ∈ pairFinset n,
        if cluster p.1 = a ∧ cluster p.2 = b then (1 : Rat) else 0 := by
  unfold orientedClusterPairCountQ
  rw [Finset.card_eq_sum_ones]
  simp

/-- Same-cluster oriented pair counts are determined by the cluster fiber
cardinality. -/
theorem orientedClusterPairCountQ_same_eq_fiber_choose
    {n : Nat} (cluster : Fin n → Fin 4) (r : Fin 4) :
    orientedClusterPairCountQ cluster r r =
      (((clusterFiber cluster r).card.choose 2 : Nat) : Rat) := by
  let s := clusterFiber cluster r
  have hnat := pairFinset_filter_mem_card (n := n) s
  have hrat :
      (((pairFinset n).filter
        (fun p : Fin n × Fin n => p.1 ∈ s ∧ p.2 ∈ s)).card : Rat) =
        ((s.card.choose 2 : Nat) : Rat) := by
    exact_mod_cast hnat
  simpa [orientedClusterPairCountQ, clusterFiber, s] using hrat

/-- If a cluster fiber has rational size `m`, its same-cluster pair count is
`m choose 2`. -/
theorem orientedClusterPairCountQ_same_eq_binomTwoQ_of_card
    {n : Nat} {q : QuadVec n} {cluster : Fin n → Fin 4}
    (hcard :
      ∀ r : Fin 4,
        (((clusterFiber cluster r).card : Nat) : Rat) = quadEntry q r)
    (r : Fin 4) :
    orientedClusterPairCountQ cluster r r =
      binomTwoQ (quadEntry q r) := by
  rw [orientedClusterPairCountQ_same_eq_fiber_choose]
  unfold binomTwoQ
  rw [← hcard r]
  rw [Nat.cast_choose_two]

/-- Inter-cluster oriented pair counts are determined by the two cluster fiber
cardinalities. -/
theorem orientedClusterPairCountQ_inter_add_eq_fiber_mul
    {n : Nat} (cluster : Fin n → Fin 4) {a b : Fin 4}
    (hab : a ≠ b) :
    orientedClusterPairCountQ cluster a b +
      orientedClusterPairCountQ cluster b a =
        (((clusterFiber cluster a).card *
          (clusterFiber cluster b).card : Nat) : Rat) := by
  let s := clusterFiber cluster a
  let t := clusterFiber cluster b
  have hdisj : Disjoint s t := by
    rw [Finset.disjoint_left]
    intro i his hit
    have hia : cluster i = a := by
      simpa [s, clusterFiber] using his
    have hib : cluster i = b := by
      simpa [t, clusterFiber] using hit
    exact hab (hia.symm.trans hib)
  have hnat := pairFinset_filter_inter_card (n := n) s t hdisj
  have hrat :
      (((pairFinset n).filter
          (fun p : Fin n × Fin n => p.1 ∈ s ∧ p.2 ∈ t)).card : Rat) +
        (((pairFinset n).filter
          (fun p : Fin n × Fin n => p.1 ∈ t ∧ p.2 ∈ s)).card : Rat) =
          (((s.card * t.card : Nat)) : Rat) := by
    exact_mod_cast hnat
  simpa [orientedClusterPairCountQ, clusterFiber, s, t] using hrat

/-- If two cluster fibers have rational sizes `m_a` and `m_b`, their unordered
inter-cluster pair count is `m_a * m_b`. -/
theorem orientedClusterPairCountQ_inter_add_eq_mul_of_card
    {n : Nat} {q : QuadVec n} {cluster : Fin n → Fin 4}
    (hcard :
      ∀ r : Fin 4,
        (((clusterFiber cluster r).card : Nat) : Rat) = quadEntry q r)
    {a b : Fin 4} (hab : a ≠ b) :
    orientedClusterPairCountQ cluster a b +
      orientedClusterPairCountQ cluster b a =
        quadEntry q a * quadEntry q b := by
  rw [orientedClusterPairCountQ_inter_add_eq_fiber_mul cluster hab]
  rw [Nat.cast_mul, hcard a, hcard b]

theorem clusteredKarlssonPairTableCrossings_eq_orientedPairCounted
    {n : Nat} (cluster : Fin n → Fin 4) :
    clusteredKarlssonPairTableCrossings cluster =
      orientedKarlssonPairCountedCrossings cluster := by
  unfold clusteredKarlssonPairTableCrossings pairSum
  unfold orientedKarlssonPairCountedCrossings
  simp_rw [orientedClusterPairCountQ_eq_indicator_sum]
  simp_rw [Finset.mul_sum]
  symm
  calc
    (∑ a : Fin 4, ∑ b : Fin 4, ∑ p ∈ pairFinset n,
        karlssonClusterPairCrossing a b *
          (if cluster p.1 = a ∧ cluster p.2 = b then (1 : Rat) else 0))
        =
      ∑ a : Fin 4, ∑ p ∈ pairFinset n, ∑ b : Fin 4,
        karlssonClusterPairCrossing a b *
          (if cluster p.1 = a ∧ cluster p.2 = b then (1 : Rat) else 0) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm]
    _ =
      ∑ p ∈ pairFinset n, ∑ a : Fin 4, ∑ b : Fin 4,
        karlssonClusterPairCrossing a b *
          (if cluster p.1 = a ∧ cluster p.2 = b then (1 : Rat) else 0) := by
        rw [Finset.sum_comm]
    _ =
      ∑ p ∈ pairFinset n,
        karlssonClusterPairCrossing (cluster p.1) (cluster p.2) := by
        apply Finset.sum_congr rfl
        intro p _
        rw [Fintype.sum_eq_single (cluster p.1)]
        · rw [Fintype.sum_eq_single (cluster p.2)]
          · simp
          · intro b hb
            simp [hb.symm]
        · intro a ha
          rw [Fintype.sum_eq_zero]
          intro b
          simp [ha.symm]

/-- Pair-counted cluster witness.  Same-cluster counts are supplied directly;
for distinct cluster labels the two possible orientations in `pairFinset n`
are supplied as one unordered count. -/
structure PairCountedClusteredKarlssonTableWitness
    {n : Nat} (q : QuadVec n) where
  cluster : Fin n → Fin 4
  cluster_card_eq :
    ∀ r : Fin 4,
      (((Finset.univ : Finset (Fin n)).filter
        (fun i => cluster i = r)).card : Rat) = quadEntry q r
  same_pair_count_eq :
    ∀ r : Fin 4,
      orientedClusterPairCountQ cluster r r =
        binomTwoQ (quadEntry q r)
  inter_pair_count_eq_zero_one :
    orientedClusterPairCountQ cluster 0 1 +
      orientedClusterPairCountQ cluster 1 0 =
        quadEntry q 0 * quadEntry q 1
  inter_pair_count_eq_zero_two :
    orientedClusterPairCountQ cluster 0 2 +
      orientedClusterPairCountQ cluster 2 0 =
        quadEntry q 0 * quadEntry q 2
  inter_pair_count_eq_zero_three :
    orientedClusterPairCountQ cluster 0 3 +
      orientedClusterPairCountQ cluster 3 0 =
        quadEntry q 0 * quadEntry q 3
  inter_pair_count_eq_one_two :
    orientedClusterPairCountQ cluster 1 2 +
      orientedClusterPairCountQ cluster 2 1 =
        quadEntry q 1 * quadEntry q 2
  inter_pair_count_eq_one_three :
    orientedClusterPairCountQ cluster 1 3 +
      orientedClusterPairCountQ cluster 3 1 =
        quadEntry q 1 * quadEntry q 3
  inter_pair_count_eq_two_three :
    orientedClusterPairCountQ cluster 2 3 +
      orientedClusterPairCountQ cluster 3 2 =
        quadEntry q 2 * quadEntry q 3

namespace PairCountedClusteredKarlssonTableWitness

theorem orientedPairCounted_eq_table
    {n : Nat} {q : QuadVec n}
    (w : PairCountedClusteredKarlssonTableWitness q) :
    orientedKarlssonPairCountedCrossings w.cluster =
      karlssonClusterTableCrossingsOfQuad q := by
  unfold orientedKarlssonPairCountedCrossings
    karlssonClusterTableCrossingsOfQuad karlssonClusterTableCrossingsQ
    karlssonClusterPairCrossing karlssonInterClusterCrossing
  simp [Fin.sum_univ_four, w.same_pair_count_eq 0, w.same_pair_count_eq 1,
    w.same_pair_count_eq 2, w.same_pair_count_eq 3]
  nlinarith [w.inter_pair_count_eq_zero_one,
    w.inter_pair_count_eq_zero_two,
    w.inter_pair_count_eq_zero_three,
    w.inter_pair_count_eq_one_two,
    w.inter_pair_count_eq_one_three,
    w.inter_pair_count_eq_two_three]

theorem pairSum_eq_table
    {n : Nat} {q : QuadVec n}
    (w : PairCountedClusteredKarlssonTableWitness q) :
    clusteredKarlssonPairTableCrossings w.cluster =
      karlssonClusterTableCrossingsOfQuad q := by
  rw [clusteredKarlssonPairTableCrossings_eq_orientedPairCounted]
  exact w.orientedPairCounted_eq_table

/-- Forget the explicit pair-count equations after Lean has collapsed them to
the older clustered witness interface. -/
def toClusteredKarlssonTableWitness
    {n : Nat} {q : QuadVec n}
    (w : PairCountedClusteredKarlssonTableWitness q) :
    ClusteredKarlssonTableWitness q where
  cluster := w.cluster
  cluster_card_eq := w.cluster_card_eq
  pairSum_eq_table := w.pairSum_eq_table

end PairCountedClusteredKarlssonTableWitness

/-- A lighter cluster witness: same-cluster pair counts are not fields, because
Lean derives them from the fiber cardinalities.  The six inter-cluster counts
remain explicit finite counting obligations. -/
structure FiberCountedClusteredKarlssonTableWitness
    {n : Nat} (q : QuadVec n) where
  cluster : Fin n → Fin 4
  cluster_card_eq :
    ∀ r : Fin 4,
      (((clusterFiber cluster r).card : Nat) : Rat) = quadEntry q r
  inter_pair_count_eq_zero_one :
    orientedClusterPairCountQ cluster 0 1 +
      orientedClusterPairCountQ cluster 1 0 =
        quadEntry q 0 * quadEntry q 1
  inter_pair_count_eq_zero_two :
    orientedClusterPairCountQ cluster 0 2 +
      orientedClusterPairCountQ cluster 2 0 =
        quadEntry q 0 * quadEntry q 2
  inter_pair_count_eq_zero_three :
    orientedClusterPairCountQ cluster 0 3 +
      orientedClusterPairCountQ cluster 3 0 =
        quadEntry q 0 * quadEntry q 3
  inter_pair_count_eq_one_two :
    orientedClusterPairCountQ cluster 1 2 +
      orientedClusterPairCountQ cluster 2 1 =
        quadEntry q 1 * quadEntry q 2
  inter_pair_count_eq_one_three :
    orientedClusterPairCountQ cluster 1 3 +
      orientedClusterPairCountQ cluster 3 1 =
        quadEntry q 1 * quadEntry q 3
  inter_pair_count_eq_two_three :
    orientedClusterPairCountQ cluster 2 3 +
      orientedClusterPairCountQ cluster 3 2 =
        quadEntry q 2 * quadEntry q 3

namespace FiberCountedClusteredKarlssonTableWitness

/-- Add the derived same-cluster pair-count equations, obtaining the stronger
pair-counted witness interface. -/
def toPairCountedClusteredKarlssonTableWitness
    {n : Nat} {q : QuadVec n}
    (w : FiberCountedClusteredKarlssonTableWitness q) :
    PairCountedClusteredKarlssonTableWitness q where
  cluster := w.cluster
  cluster_card_eq := by
    intro r
    simpa [clusterFiber] using w.cluster_card_eq r
  same_pair_count_eq := by
    intro r
    exact orientedClusterPairCountQ_same_eq_binomTwoQ_of_card
      w.cluster_card_eq r
  inter_pair_count_eq_zero_one := w.inter_pair_count_eq_zero_one
  inter_pair_count_eq_zero_two := w.inter_pair_count_eq_zero_two
  inter_pair_count_eq_zero_three := w.inter_pair_count_eq_zero_three
  inter_pair_count_eq_one_two := w.inter_pair_count_eq_one_two
  inter_pair_count_eq_one_three := w.inter_pair_count_eq_one_three
  inter_pair_count_eq_two_three := w.inter_pair_count_eq_two_three

theorem pairSum_eq_table
    {n : Nat} {q : QuadVec n}
    (w : FiberCountedClusteredKarlssonTableWitness q) :
    clusteredKarlssonPairTableCrossings w.cluster =
      karlssonClusterTableCrossingsOfQuad q :=
  w.toPairCountedClusteredKarlssonTableWitness.pairSum_eq_table

end FiberCountedClusteredKarlssonTableWitness

/-- Strongest finite-counting cluster witness in this file.  It supplies only
a cluster map whose four fibers have the desired cardinalities.  Lean derives
all four same-cluster counts and all six inter-cluster counts. -/
structure CardinalityClusteredKarlssonTableWitness
    {n : Nat} (q : QuadVec n) where
  cluster : Fin n → Fin 4
  cluster_card_eq :
    ∀ r : Fin 4,
      (((clusterFiber cluster r).card : Nat) : Rat) = quadEntry q r

namespace CardinalityClusteredKarlssonTableWitness

def toFiberCountedClusteredKarlssonTableWitness
    {n : Nat} {q : QuadVec n}
    (w : CardinalityClusteredKarlssonTableWitness q) :
    FiberCountedClusteredKarlssonTableWitness q where
  cluster := w.cluster
  cluster_card_eq := w.cluster_card_eq
  inter_pair_count_eq_zero_one :=
    orientedClusterPairCountQ_inter_add_eq_mul_of_card
      w.cluster_card_eq (by decide)
  inter_pair_count_eq_zero_two :=
    orientedClusterPairCountQ_inter_add_eq_mul_of_card
      w.cluster_card_eq (by decide)
  inter_pair_count_eq_zero_three :=
    orientedClusterPairCountQ_inter_add_eq_mul_of_card
      w.cluster_card_eq (by decide)
  inter_pair_count_eq_one_two :=
    orientedClusterPairCountQ_inter_add_eq_mul_of_card
      w.cluster_card_eq (by decide)
  inter_pair_count_eq_one_three :=
    orientedClusterPairCountQ_inter_add_eq_mul_of_card
      w.cluster_card_eq (by decide)
  inter_pair_count_eq_two_three :=
    orientedClusterPairCountQ_inter_add_eq_mul_of_card
      w.cluster_card_eq (by decide)

def toPairCountedClusteredKarlssonTableWitness
    {n : Nat} {q : QuadVec n}
    (w : CardinalityClusteredKarlssonTableWitness q) :
    PairCountedClusteredKarlssonTableWitness q :=
  w.toFiberCountedClusteredKarlssonTableWitness.toPairCountedClusteredKarlssonTableWitness

theorem pairSum_eq_table
    {n : Nat} {q : QuadVec n}
    (w : CardinalityClusteredKarlssonTableWitness q) :
    clusteredKarlssonPairTableCrossings w.cluster =
      karlssonClusterTableCrossingsOfQuad q :=
  w.toFiberCountedClusteredKarlssonTableWitness.pairSum_eq_table

end CardinalityClusteredKarlssonTableWitness

/-- The finite type containing one element for each intended lollipop in each
of the four clusters of a quadruple. -/
abbrev quadClusterIndex {n : Nat} (q : QuadVec n) : Type :=
  Σ r : Fin 4, Fin ((q r : Nat))

theorem quadClusterIndex_card {n : Nat} {q : QuadVec n}
    (hq : q ∈ quadVecs n) :
    Fintype.card (quadClusterIndex q) = n := by
  rw [quadVecs, Finset.mem_filter] at hq
  have hsum : (∑ r : Fin 4, (q r : Nat)) = n := by
    simpa [quadVecSum] using hq.2
  simp [quadClusterIndex, hsum]

/-- Noncomputably identify `Fin n` with the disjoint union of four finite
cluster fibers having sizes prescribed by `q`. -/
noncomputable def quadClusterEquiv {n : Nat} (q : QuadVec n)
    (hq : q ∈ quadVecs n) :
    Fin n ≃ quadClusterIndex q :=
  (Fintype.equivFinOfCardEq (quadClusterIndex_card (q := q) hq)).symm

/-- Canonical cluster map obtained from the first coordinate of the finite
equivalence with the disjoint union of four fibers. -/
noncomputable def canonicalQuadCluster {n : Nat} (q : QuadVec n)
    (hq : q ∈ quadVecs n) :
    Fin n → Fin 4 :=
  fun i => (quadClusterEquiv q hq i).1

/-- The subtype of the sigma cluster index over one fixed cluster is exactly
that cluster's finite fiber. -/
def quadClusterIndexFiberEquiv {n : Nat} (q : QuadVec n) (r : Fin 4) :
    {x : quadClusterIndex q // x.1 = r} ≃ Fin ((q r : Nat)) where
  toFun x :=
    Fin.cast (by
      exact congrArg (fun s : Fin 4 => (q s : Nat)) x.2) x.1.2
  invFun y := ⟨⟨r, y⟩, rfl⟩
  left_inv := by
    intro x
    rcases x with ⟨⟨s, y⟩, hsr⟩
    subst hsr
    simp
  right_inv := by
    intro y
    simp

theorem canonicalQuadCluster_card_eq
    {n : Nat} (q : QuadVec n) (hq : q ∈ quadVecs n) (r : Fin 4) :
    (((clusterFiber (canonicalQuadCluster q hq) r).card : Nat) : Rat) =
      quadEntry q r := by
  let e := quadClusterEquiv q hq
  let cluster := canonicalQuadCluster q hq
  have hmem :
      ∀ i : Fin n, i ∈ clusterFiber cluster r ↔ cluster i = r := by
    intro i
    simp [clusterFiber]
  let memEquiv :
      {i : Fin n // i ∈ clusterFiber cluster r} ≃
        {i : Fin n // cluster i = r} :=
    Equiv.subtypeEquivRight hmem
  have hsub :
      ∀ i : Fin n, cluster i = r ↔ (e i).1 = r := by
    intro i
    rfl
  let imageEquiv :
      {i : Fin n // cluster i = r} ≃
        {x : quadClusterIndex q // x.1 = r} :=
    e.subtypeEquiv hsub
  let fiberEquiv :
      {i : Fin n // i ∈ clusterFiber cluster r} ≃ Fin ((q r : Nat)) :=
    memEquiv.trans (imageEquiv.trans (quadClusterIndexFiberEquiv q r))
  have hcard :
      (clusterFiber cluster r).card = (q r : Nat) := by
    calc
      (clusterFiber cluster r).card =
          Fintype.card {i : Fin n // i ∈ clusterFiber cluster r} := by
            exact (Fintype.card_coe (clusterFiber cluster r)).symm
      _ = Fintype.card (Fin ((q r : Nat))) := Fintype.card_congr fiberEquiv
      _ = (q r : Nat) := Fintype.card_fin ((q r : Nat))
  rw [hcard]
  rfl

/-- Every admissible quadruple has a cardinality-clustered witness; all finite
same/inter-cluster pair counts are then derived internally. -/
noncomputable def cardinalityClusteredKarlssonTableWitnessOfQuad
    {n : Nat} (q : QuadVec n) (hq : q ∈ quadVecs n) :
    CardinalityClusteredKarlssonTableWitness q where
  cluster := canonicalQuadCluster q hq
  cluster_card_eq := canonicalQuadCluster_card_eq q hq

/-- A sorted quadruple has the canonical cardinality-clustered witness. -/
noncomputable def cardinalityClusteredKarlssonTableWitnessOfSortedQuad
    {n : Nat} (q : QuadVec n) (hq : q ∈ sortedQuadVecs n) :
    CardinalityClusteredKarlssonTableWitness q :=
  cardinalityClusteredKarlssonTableWitnessOfQuad q (by
    rw [sortedQuadVecs, Finset.mem_filter] at hq
    exact hq.1)

/-- Named sorted Karlsson blow-up construction whose lower crossing count is
certified by finite same/inter-cluster pair counts. -/
structure PairCountedClusteredKarlssonBlowUpLowerData
    (P : TheoremOne.ProblemFamily.{u}) where
  crossings : (n : Nat) → P.Arrangement n → Rat
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  cluster_witness :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      PairCountedClusteredKarlssonTableWitness q
  crossings_eq_clustered_pair_sum :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      crossings n (arrangement n q hq) =
        clusteredKarlssonPairTableCrossings
          ((cluster_witness n q hq).cluster)
  regions_eq :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      P.region n (arrangement n q hq) =
        crossings n (arrangement n q hq) + (n : Rat) + 1

namespace PairCountedClusteredKarlssonBlowUpLowerData

def toClusteredKarlssonBlowUpLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PairCountedClusteredKarlssonBlowUpLowerData P) :
    ClusteredKarlssonBlowUpLowerData P where
  crossings := h.crossings
  arrangement := h.arrangement
  cluster_witness := by
    intro n q hq
    exact (h.cluster_witness n q hq).toClusteredKarlssonTableWitness
  crossings_eq_clustered_pair_sum := h.crossings_eq_clustered_pair_sum
  regions_eq := h.regions_eq

def toKarlssonTableBlowUpLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PairCountedClusteredKarlssonBlowUpLowerData P) :
    KarlssonTableBlowUpLowerData P :=
  h.toClusteredKarlssonBlowUpLowerData.toKarlssonTableBlowUpLowerData

end PairCountedClusteredKarlssonBlowUpLowerData

/-- Incremental lower construction with pair-counted clustered table data. -/
structure PairCountedClusteredKarlssonBlowUpIncrementalLowerData
    (P : TheoremOne.ProblemFamily.{u}) where
  crossings : (n : Nat) → P.Arrangement n → Rat
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  cluster_witness :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      PairCountedClusteredKarlssonTableWitness q
  crossings_eq_clustered_pair_sum :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      crossings n (arrangement n q hq) =
        clusteredKarlssonPairTableCrossings
          ((cluster_witness n q hq).cluster)
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      IncrementalRegionData n
        (P.region n (arrangement n q hq))
        (crossings n (arrangement n q hq))

namespace PairCountedClusteredKarlssonBlowUpIncrementalLowerData

def toPairCountedClusteredKarlssonBlowUpLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PairCountedClusteredKarlssonBlowUpIncrementalLowerData P) :
    PairCountedClusteredKarlssonBlowUpLowerData P where
  crossings := h.crossings
  arrangement := h.arrangement
  cluster_witness := h.cluster_witness
  crossings_eq_clustered_pair_sum := h.crossings_eq_clustered_pair_sum
  regions_eq := by
    intro n q hq
    exact (h.region_increment n q hq).target_eq_totalCrossings_add

def toClusteredKarlssonBlowUpIncrementalLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PairCountedClusteredKarlssonBlowUpIncrementalLowerData P) :
    ClusteredKarlssonBlowUpIncrementalLowerData P where
  crossings := h.crossings
  arrangement := h.arrangement
  cluster_witness := by
    intro n q hq
    exact (h.cluster_witness n q hq).toClusteredKarlssonTableWitness
  crossings_eq_clustered_pair_sum := h.crossings_eq_clustered_pair_sum
  region_increment := h.region_increment

def toKarlssonTableBlowUpIncrementalLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PairCountedClusteredKarlssonBlowUpIncrementalLowerData P) :
    KarlssonTableBlowUpIncrementalLowerData P :=
  h.toClusteredKarlssonBlowUpIncrementalLowerData.toKarlssonTableBlowUpIncrementalLowerData

end PairCountedClusteredKarlssonBlowUpIncrementalLowerData

/-- Named sorted Karlsson blow-up construction whose same-cluster pair counts
are derived from cluster fiber cardinalities, with only the six inter-cluster
counts supplied explicitly. -/
structure FiberCountedClusteredKarlssonBlowUpLowerData
    (P : TheoremOne.ProblemFamily.{u}) where
  crossings : (n : Nat) → P.Arrangement n → Rat
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  cluster_witness :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      FiberCountedClusteredKarlssonTableWitness q
  crossings_eq_clustered_pair_sum :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      crossings n (arrangement n q hq) =
        clusteredKarlssonPairTableCrossings
          ((cluster_witness n q hq).cluster)
  regions_eq :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      P.region n (arrangement n q hq) =
        crossings n (arrangement n q hq) + (n : Rat) + 1

namespace FiberCountedClusteredKarlssonBlowUpLowerData

def toPairCountedClusteredKarlssonBlowUpLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : FiberCountedClusteredKarlssonBlowUpLowerData P) :
    PairCountedClusteredKarlssonBlowUpLowerData P where
  crossings := h.crossings
  arrangement := h.arrangement
  cluster_witness := by
    intro n q hq
    exact
      (h.cluster_witness n q hq).toPairCountedClusteredKarlssonTableWitness
  crossings_eq_clustered_pair_sum := h.crossings_eq_clustered_pair_sum
  regions_eq := h.regions_eq

def toClusteredKarlssonBlowUpLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : FiberCountedClusteredKarlssonBlowUpLowerData P) :
    ClusteredKarlssonBlowUpLowerData P :=
  h.toPairCountedClusteredKarlssonBlowUpLowerData.toClusteredKarlssonBlowUpLowerData

end FiberCountedClusteredKarlssonBlowUpLowerData

/-- Incremental lower construction with same-cluster pair counts derived from
cluster fiber cardinalities and explicit inter-cluster counts. -/
structure FiberCountedClusteredKarlssonBlowUpIncrementalLowerData
    (P : TheoremOne.ProblemFamily.{u}) where
  crossings : (n : Nat) → P.Arrangement n → Rat
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  cluster_witness :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      FiberCountedClusteredKarlssonTableWitness q
  crossings_eq_clustered_pair_sum :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      crossings n (arrangement n q hq) =
        clusteredKarlssonPairTableCrossings
          ((cluster_witness n q hq).cluster)
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      IncrementalRegionData n
        (P.region n (arrangement n q hq))
        (crossings n (arrangement n q hq))

namespace FiberCountedClusteredKarlssonBlowUpIncrementalLowerData

def toFiberCountedClusteredKarlssonBlowUpLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : FiberCountedClusteredKarlssonBlowUpIncrementalLowerData P) :
    FiberCountedClusteredKarlssonBlowUpLowerData P where
  crossings := h.crossings
  arrangement := h.arrangement
  cluster_witness := h.cluster_witness
  crossings_eq_clustered_pair_sum := h.crossings_eq_clustered_pair_sum
  regions_eq := by
    intro n q hq
    exact (h.region_increment n q hq).target_eq_totalCrossings_add

def toPairCountedClusteredKarlssonBlowUpIncrementalLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : FiberCountedClusteredKarlssonBlowUpIncrementalLowerData P) :
    PairCountedClusteredKarlssonBlowUpIncrementalLowerData P where
  crossings := h.crossings
  arrangement := h.arrangement
  cluster_witness := by
    intro n q hq
    exact
      (h.cluster_witness n q hq).toPairCountedClusteredKarlssonTableWitness
  crossings_eq_clustered_pair_sum := h.crossings_eq_clustered_pair_sum
  region_increment := h.region_increment

def toClusteredKarlssonBlowUpIncrementalLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : FiberCountedClusteredKarlssonBlowUpIncrementalLowerData P) :
    ClusteredKarlssonBlowUpIncrementalLowerData P :=
  h.toPairCountedClusteredKarlssonBlowUpIncrementalLowerData.toClusteredKarlssonBlowUpIncrementalLowerData

end FiberCountedClusteredKarlssonBlowUpIncrementalLowerData

/-- Named sorted Karlsson blow-up construction whose finite counting input is
only a cluster map with the required four fiber cardinalities. -/
structure CardinalityClusteredKarlssonBlowUpLowerData
    (P : TheoremOne.ProblemFamily.{u}) where
  crossings : (n : Nat) → P.Arrangement n → Rat
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  cluster_witness :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      CardinalityClusteredKarlssonTableWitness q
  crossings_eq_clustered_pair_sum :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      crossings n (arrangement n q hq) =
        clusteredKarlssonPairTableCrossings
          ((cluster_witness n q hq).cluster)
  regions_eq :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      P.region n (arrangement n q hq) =
        crossings n (arrangement n q hq) + (n : Rat) + 1

namespace CardinalityClusteredKarlssonBlowUpLowerData

def toFiberCountedClusteredKarlssonBlowUpLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CardinalityClusteredKarlssonBlowUpLowerData P) :
    FiberCountedClusteredKarlssonBlowUpLowerData P where
  crossings := h.crossings
  arrangement := h.arrangement
  cluster_witness := by
    intro n q hq
    exact
      (h.cluster_witness n q hq).toFiberCountedClusteredKarlssonTableWitness
  crossings_eq_clustered_pair_sum := h.crossings_eq_clustered_pair_sum
  regions_eq := h.regions_eq

def toPairCountedClusteredKarlssonBlowUpLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CardinalityClusteredKarlssonBlowUpLowerData P) :
    PairCountedClusteredKarlssonBlowUpLowerData P :=
  h.toFiberCountedClusteredKarlssonBlowUpLowerData.toPairCountedClusteredKarlssonBlowUpLowerData

def toClusteredKarlssonBlowUpLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CardinalityClusteredKarlssonBlowUpLowerData P) :
    ClusteredKarlssonBlowUpLowerData P :=
  h.toFiberCountedClusteredKarlssonBlowUpLowerData.toClusteredKarlssonBlowUpLowerData

end CardinalityClusteredKarlssonBlowUpLowerData

/-- Incremental lower construction whose finite counting input is only the
cluster map and its four fiber cardinalities. -/
structure CardinalityClusteredKarlssonBlowUpIncrementalLowerData
    (P : TheoremOne.ProblemFamily.{u}) where
  crossings : (n : Nat) → P.Arrangement n → Rat
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  cluster_witness :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      CardinalityClusteredKarlssonTableWitness q
  crossings_eq_clustered_pair_sum :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      crossings n (arrangement n q hq) =
        clusteredKarlssonPairTableCrossings
          ((cluster_witness n q hq).cluster)
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      IncrementalRegionData n
        (P.region n (arrangement n q hq))
        (crossings n (arrangement n q hq))

namespace CardinalityClusteredKarlssonBlowUpIncrementalLowerData

def toCardinalityClusteredKarlssonBlowUpLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CardinalityClusteredKarlssonBlowUpIncrementalLowerData P) :
    CardinalityClusteredKarlssonBlowUpLowerData P where
  crossings := h.crossings
  arrangement := h.arrangement
  cluster_witness := h.cluster_witness
  crossings_eq_clustered_pair_sum := h.crossings_eq_clustered_pair_sum
  regions_eq := by
    intro n q hq
    exact (h.region_increment n q hq).target_eq_totalCrossings_add

def toFiberCountedClusteredKarlssonBlowUpIncrementalLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CardinalityClusteredKarlssonBlowUpIncrementalLowerData P) :
    FiberCountedClusteredKarlssonBlowUpIncrementalLowerData P where
  crossings := h.crossings
  arrangement := h.arrangement
  cluster_witness := by
    intro n q hq
    exact
      (h.cluster_witness n q hq).toFiberCountedClusteredKarlssonTableWitness
  crossings_eq_clustered_pair_sum := h.crossings_eq_clustered_pair_sum
  region_increment := h.region_increment

def toPairCountedClusteredKarlssonBlowUpIncrementalLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CardinalityClusteredKarlssonBlowUpIncrementalLowerData P) :
    PairCountedClusteredKarlssonBlowUpIncrementalLowerData P :=
  h.toFiberCountedClusteredKarlssonBlowUpIncrementalLowerData.toPairCountedClusteredKarlssonBlowUpIncrementalLowerData

def toClusteredKarlssonBlowUpIncrementalLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CardinalityClusteredKarlssonBlowUpIncrementalLowerData P) :
    ClusteredKarlssonBlowUpIncrementalLowerData P :=
  h.toFiberCountedClusteredKarlssonBlowUpIncrementalLowerData.toClusteredKarlssonBlowUpIncrementalLowerData

end CardinalityClusteredKarlssonBlowUpIncrementalLowerData

/- A direct named Karlsson blow-up lower construction can be upgraded to the
cardinality-clustered interface: Lean supplies the canonical four-fiber cluster
map and proves its pair table is the closed lower crossing formula.  This is a
numeric counting refinement of the older interface. -/
namespace KarlssonBlowUpLowerData

noncomputable def toCardinalityClusteredKarlssonBlowUpLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonBlowUpLowerData P) :
    CardinalityClusteredKarlssonBlowUpLowerData P where
  crossings := h.crossings
  arrangement := h.arrangement
  cluster_witness := by
    intro n q hq
    exact cardinalityClusteredKarlssonTableWitnessOfSortedQuad q hq
  crossings_eq_clustered_pair_sum := by
    intro n q hq
    let w := cardinalityClusteredKarlssonTableWitnessOfSortedQuad q hq
    rw [h.crossings_eq_lower n q hq]
    exact (w.pairSum_eq_table.trans
      (karlssonClusterTableCrossingsOfQuad_eq_lowerCrossingsOfQuad q)).symm
  regions_eq := h.regions_eq

end KarlssonBlowUpLowerData

/- Incremental named Karlsson blow-up lower data have the same canonical
cardinality-clustered finite counting refinement. -/
namespace KarlssonBlowUpIncrementalLowerData

noncomputable def toCardinalityClusteredKarlssonBlowUpIncrementalLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : KarlssonBlowUpIncrementalLowerData P) :
    CardinalityClusteredKarlssonBlowUpIncrementalLowerData P where
  crossings := h.crossings
  arrangement := h.arrangement
  cluster_witness := by
    intro n q hq
    exact cardinalityClusteredKarlssonTableWitnessOfSortedQuad q hq
  crossings_eq_clustered_pair_sum := by
    intro n q hq
    let w := cardinalityClusteredKarlssonTableWitnessOfSortedQuad q hq
    rw [h.crossings_eq_lower n q hq]
    exact (w.pairSum_eq_table.trans
      (karlssonClusterTableCrossingsOfQuad_eq_lowerCrossingsOfQuad q)).symm
  region_increment := h.region_increment

end KarlssonBlowUpIncrementalLowerData

end ExplicitInputs
end TheoremOneManuscript
end Lollipop
