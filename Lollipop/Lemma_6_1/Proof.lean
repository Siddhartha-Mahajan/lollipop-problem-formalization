import Lollipop.Lemma_7_2.Proof
import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Data.Sym.Sym2
import Mathlib.Tactic

/-!
This is the substantive proof compilation unit for `Lemma_6_1`.
All project proof components used below are integrated here or imported
directly from another manuscript-numbered `Proof.lean` file.
-/

/-!
Proof component 1: `ColoredTuran.WeightedTuran`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Weighted Turan algebra for the blocker step.

This file does not prove the weighted Turan extremal theorem itself.  It
formalizes the algebraic interface needed after that theorem has supplied a
numeric upper bound for the off-diagonal complement relation against a chosen
partition.  From that numeric complement bound, Lean derives the blocker lower
bound `w(A) >= (rho - Q) / 2`.

The file also proves a separate sufficient condition: if every complement edge
crosses the chosen partition, then the same numeric complement bound follows.
That crossing condition is stronger than the manuscript's weighted Turan input
and is not used as the main Theorem 1 boundary.
-/

namespace Lollipop
namespace TheoremOneEndToEnd

open BigOperators

set_option linter.unusedSectionVars false

variable {V κ : Type*} [Fintype V] [DecidableEq V] [Fintype κ] [DecidableEq κ]

/-- Ordered weighted mass of a binary relation.  For a symmetric irreflexive
graph relation this is twice the usual unordered edge weight. -/
def orderedRelWeight (x : V → Nat) (R : V → V → Prop) [DecidableRel R] : Rat :=
  ∑ v : V, ∑ w : V, if R v w then (x v : Rat) * (x w : Rat) else 0

/-- Unordered weighted edge mass, represented as half of the ordered mass. -/
def weightedEdgeMass (x : V → Nat) (R : V → V → Prop) [DecidableRel R] : Rat :=
  orderedRelWeight x R / 2

/-- Square-sum of part weights for a partition map. -/
def partitionSquareWeight (x : V → Nat) (p : V → κ) : Rat :=
  ∑ c : κ, (∑ v : V, if p v = c then (x v : Rat) else 0)^2

/-- Ordered weighted mass is monotone under relation inclusion. -/
theorem orderedRelWeight_le_of_imp
    (x : V → Nat) (R S : V → V → Prop) [DecidableRel R] [DecidableRel S]
    (h : ∀ v w, R v w → S v w) :
    orderedRelWeight x R ≤ orderedRelWeight x S := by
  classical
  unfold orderedRelWeight
  apply Finset.sum_le_sum
  intro v _hv
  apply Finset.sum_le_sum
  intro w _hw
  by_cases hR : R v w
  · have hS : S v w := h v w hR
    simp [hR, hS]
  · by_cases hS : S v w
    · simp [hR, hS]
      positivity
    · simp [hR, hS]

private theorem offDiag_sum_inner
    (x : V → Nat) (v : V) :
    (∑ w : V, if v ≠ w then (x v : Rat) * (x w : Rat) else 0) =
      (∑ w : V, (x v : Rat) * (x w : Rat)) - (x v : Rat)^2 := by
  have hdiag :
      (∑ w : V, if v = w then (x v : Rat) * (x w : Rat) else 0) =
        (x v : Rat)^2 := by
    simp
    ring
  have hsum :
      (∑ w : V, (x v : Rat) * (x w : Rat)) =
        (∑ w : V, if v ≠ w then (x v : Rat) * (x w : Rat) else 0) +
        (∑ w : V, if v = w then (x v : Rat) * (x w : Rat) else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w _hw
    by_cases h : v = w <;> simp [h]
  rw [hdiag] at hsum
  linarith

/-- The ordered mass of the off-diagonal relation is `n^2 - Q`. -/
theorem orderedRelWeight_offDiag
    (x : V → Nat) :
    orderedRelWeight x (fun v w : V => v ≠ w) =
      (totalWeightNat x : Rat)^2 - weightSquareSumRat x := by
  classical
  unfold orderedRelWeight totalWeightNat weightSquareSumRat
  have hcast : ((∑ v : V, x v : Nat) : Rat) = ∑ v : V, (x v : Rat) := by
    norm_cast
  rw [hcast]
  have htotal :
      ((∑ v : V, (x v : Rat))^2) =
        ∑ v : V, ∑ w : V, (x v : Rat) * (x w : Rat) := by
    rw [sq]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro v _hv
    rw [Finset.mul_sum]
  rw [htotal]
  calc
    (∑ v : V, ∑ w : V, if v ≠ w then (x v : Rat) * (x w : Rat) else 0)
        = ∑ v : V,
            ((∑ w : V, (x v : Rat) * (x w : Rat)) - (x v : Rat)^2) := by
            apply Finset.sum_congr rfl
            intro v _hv
            exact offDiag_sum_inner x v
    _ = (∑ v : V, ∑ w : V, (x v : Rat) * (x w : Rat)) -
          ∑ v : V, (x v : Rat)^2 := by
            rw [Finset.sum_sub_distrib]

private theorem partitionSame_sum_inner
    (x : V → Nat) (p : V → κ) (v w : V) :
    (∑ c : κ, if p v = c ∧ p w = c then
        (x v : Rat) * (x w : Rat) else 0) =
      if p v = p w then (x v : Rat) * (x w : Rat) else 0 := by
  by_cases hp : p v = p w
  · simp [hp]
  · rw [if_neg hp]
    apply Finset.sum_eq_zero
    intro c _hc
    by_cases hv : p v = c
    · have hw : p w ≠ c := by
        intro hw
        exact hp (hv.trans hw.symm)
      simp [hv, hw]
    · simp [hv]

/-- The ordered mass of pairs inside the same part is exactly the square-sum
of the part weights. -/
theorem orderedRelWeight_partition_eq
    (x : V → Nat) (p : V → κ) :
    orderedRelWeight x (fun v w : V => p v = p w) =
      partitionSquareWeight x p := by
  classical
  unfold orderedRelWeight partitionSquareWeight
  symm
  calc
    (∑ c : κ, (∑ v : V, if p v = c then (x v : Rat) else 0)^2)
        = ∑ c : κ, ∑ v : V, ∑ w : V,
          if p v = c ∧ p w = c then (x v : Rat) * (x w : Rat) else 0 := by
          apply Finset.sum_congr rfl
          intro c _hc
          have hmul :
              (∑ v : V, if p v = c then (x v : Rat) else 0)^2 =
                (∑ v : V, if p v = c then (x v : Rat) else 0) *
                (∑ w : V, if p w = c then (x w : Rat) else 0) := by
            ring
          rw [hmul]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro v _hv
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro w _hw
          by_cases hv : p v = c <;> by_cases hw : p w = c <;> simp [hv, hw]
    _ = ∑ v : V, ∑ w : V, ∑ c : κ,
          if p v = c ∧ p w = c then (x v : Rat) * (x w : Rat) else 0 := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro v _hv
          rw [Finset.sum_comm]
    _ = ∑ v : V, ∑ w : V, if p v = p w then
          (x v : Rat) * (x w : Rat) else 0 := by
          apply Finset.sum_congr rfl
          intro v _hv
          apply Finset.sum_congr rfl
          intro w _hw
          exact partitionSame_sum_inner x p v w

/-- The ordered mass of all pairs is the square of the total weight. -/
theorem orderedRelWeight_univ
    (x : V → Nat) :
    orderedRelWeight x (fun _ _ : V => True) =
      (totalWeightNat x : Rat)^2 := by
  classical
  unfold orderedRelWeight totalWeightNat
  have hcast : ((∑ v : V, x v : Nat) : Rat) = ∑ v : V, (x v : Rat) := by
    norm_cast
  rw [hcast]
  rw [sq]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v _hv
  rw [Finset.mul_sum]
  simp

/-- Same-part and cross-part ordered masses split the total ordered mass. -/
theorem orderedRelWeight_partition_add_cross
    (x : V → Nat) (p : V → κ) :
    orderedRelWeight x (fun v w : V => p v = p w) +
      orderedRelWeight x (fun v w : V => p v ≠ p w) =
      orderedRelWeight x (fun _ _ : V => True) := by
  classical
  unfold orderedRelWeight
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _hv
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _hw
  by_cases hp : p v = p w <;> simp [hp]

/-- The ordered mass crossing a partition is `n^2` minus the square-sum of
part weights. -/
theorem orderedRelWeight_partition_ne
    (x : V → Nat) (p : V → κ) :
    orderedRelWeight x (fun v w : V => p v ≠ p w) =
      (totalWeightNat x : Rat)^2 - partitionSquareWeight x p := by
  have hsplit := orderedRelWeight_partition_add_cross x p
  have hsame := orderedRelWeight_partition_eq x p
  have hall := orderedRelWeight_univ (V := V) x
  nlinarith

/-- An irreflexive relation and its off-diagonal complement partition the
off-diagonal ordered mass. -/
theorem orderedRelWeight_add_offDiag_complement
    (x : V → Nat) (R : V → V → Prop) [DecidableRel R]
    (hloop : ∀ v, ¬ R v v) :
    orderedRelWeight x R +
      orderedRelWeight x (fun v w : V => v ≠ w ∧ ¬ R v w) =
      orderedRelWeight x (fun v w : V => v ≠ w) := by
  classical
  unfold orderedRelWeight
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _hv
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _hw
  by_cases hR : R v w
  · have hne : v ≠ w := by
      intro hvw
      subst w
      exact hloop v hR
    simp [hR, hne]
  · by_cases hne : v ≠ w <;> simp [hR, hne]

/-- Checked weighted-Turan-to-blocker step.  If the off-diagonal complement
of `R` has ordered mass at most `n^2 - rho` for a partition with square mass
`rho`, then the unordered mass of `R` is at least `(rho - Q) / 2`. -/
theorem weightedEdgeMass_ge_of_complement_le_partition
    (x : V → Nat) (R : V → V → Prop) [DecidableRel R] (p : V → κ)
    (hloop : ∀ v, ¬ R v v)
    (hcomp :
      orderedRelWeight x (fun v w : V => v ≠ w ∧ ¬ R v w) ≤
        (totalWeightNat x : Rat)^2 - partitionSquareWeight x p) :
    weightedEdgeMass x R ≥
      (partitionSquareWeight x p - weightSquareSumRat x) / 2 := by
  have hsplit := orderedRelWeight_add_offDiag_complement x R hloop
  have hoff := orderedRelWeight_offDiag (V := V) x
  unfold weightedEdgeMass
  rw [hoff] at hsplit
  nlinarith

/-- A checkable partition certificate for the weighted Turan complement
bound: if every complement edge crosses `p`, then its ordered mass is bounded
by `n^2 - partitionSquareWeight x p`.

This is only a sufficient condition.  The weighted Turan theorem used in the
manuscript is stronger: it supplies the same numeric bound for every
`K_{r+1}`-free complement, even when that complement is not itself colored by
the minimizing partition. -/
theorem orderedRelWeight_complement_le_of_crosses_partition
    (x : V → Nat) (R : V → V → Prop) [DecidableRel R] (p : V → κ)
    (hcross : ∀ v w, v ≠ w ∧ ¬ R v w → p v ≠ p w) :
    orderedRelWeight x (fun v w : V => v ≠ w ∧ ¬ R v w) ≤
      (totalWeightNat x : Rat)^2 - partitionSquareWeight x p := by
  have hle :=
    orderedRelWeight_le_of_imp x
      (fun v w : V => v ≠ w ∧ ¬ R v w)
      (fun v w : V => p v ≠ p w)
      hcross
  rw [orderedRelWeight_partition_ne] at hle
  exact hle

/-- The `Fin 3` partition square is the row-square side of the intersection
matrix. -/
theorem partitionSquareWeight_fin3_eq_rowSq_partitionMatrixNat
    (x : V → Nat) (p3 : V → Fin 3) (p4 : V → Fin 4) :
    partitionSquareWeight x p3 =
      ∑ i : Fin 3, (rowSum (matrixOfNat (partitionMatrixNat x p3 p4)) i)^2 := by
  classical
  unfold partitionSquareWeight
  apply Finset.sum_congr rfl
  intro i _hi
  rw [rowSum_partitionMatrixNat]

/-- The `Fin 4` partition square is the column-square side of the intersection
matrix. -/
theorem partitionSquareWeight_fin4_eq_colSq_partitionMatrixNat
    (x : V → Nat) (p3 : V → Fin 3) (p4 : V → Fin 4) :
    partitionSquareWeight x p4 =
      ∑ j : Fin 4, (colSum (matrixOfNat (partitionMatrixNat x p3 p4)) j)^2 := by
  classical
  unfold partitionSquareWeight
  apply Finset.sum_congr rfl
  intro j _hj
  rw [colSum_partitionMatrixNat]

end TheoremOneEndToEnd
end Lollipop

/-!
Proof component 2: `ColoredTuran.WeightedTuranTheorem`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Weighted Turan theorem infrastructure.

Mathlib contains the unweighted Zykov/Turan theorem in
`Mathlib.Combinatorics.SimpleGraph.Extremal.Turan`.  The manuscript needs the
weighted analogue, where each quotient vertex has an integral weight and the
objective is `sum x_i x_j` over graph edges.  This file starts the local
weighted version using mathlib's `SimpleGraph` API.
-/

namespace Lollipop
namespace TheoremOneEndToEnd

open BigOperators

universe u

set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 800000

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- `orderedRelWeight` is independent of the particular decidability instance
used for the relation. -/
theorem orderedRelWeight_eq_of_decidableRel
    (x : V → Nat) (R : V → V → Prop)
    [d₁ : DecidableRel R] [d₂ : DecidableRel R] :
    @orderedRelWeight V _ x R d₁ = @orderedRelWeight V _ x R d₂ := by
  classical
  unfold orderedRelWeight
  apply Finset.sum_congr rfl
  intro v _hv
  apply Finset.sum_congr rfl
  intro w _hw
  by_cases h : R v w <;> simp [h]

/-- Weight of an unordered pair of vertices. -/
def sym2Weight (x : V → Nat) : Sym2 V → Rat :=
  Sym2.lift ⟨fun v w => (x v : Rat) * (x w : Rat), by
    intro v w
    ring⟩

@[simp]
theorem sym2Weight_mk (x : V → Nat) (v w : V) :
    sym2Weight x s(v, w) = (x v : Rat) * (x w : Rat) := by
  rfl

/-- Unordered weighted edge mass of a simple graph. -/
noncomputable def simpleGraphEdgeWeight
    (x : V → Nat) (G : SimpleGraph V) : Rat := by
  classical
  exact ∑ e ∈ G.edgeFinset, sym2Weight x e

/-- Weighted degree of one vertex. -/
noncomputable def simpleGraphWeightedDegree
    (x : V → Nat) (G : SimpleGraph V) (v : V) : Rat := by
  classical
  exact ∑ w : V, if G.Adj v w then (x w : Rat) else 0

theorem simpleGraphWeightedDegree_eq_sum
    (x : V → Nat) (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    simpleGraphWeightedDegree x G v =
      ∑ w : V, if G.Adj v w then (x w : Rat) else 0 := by
  unfold simpleGraphWeightedDegree
  apply Finset.sum_congr rfl
  intro w _hw
  by_cases h : G.Adj v w <;> simp [h]

theorem simpleGraphWeightedDegree_eq_neighborFinset
    (x : V → Nat) (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    simpleGraphWeightedDegree x G v =
      ∑ w ∈ G.neighborFinset v, (x w : Rat) := by
  rw [simpleGraphWeightedDegree_eq_sum x G v]
  rw [SimpleGraph.neighborFinset_eq_filter]
  rw [Finset.sum_filter]

theorem weightedAdjacencySum_eq_mul_weightedDegree
    (x : V → Nat) (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : Rat) (v : V) :
    (∑ w : V, if G.Adj v w then c * (x w : Rat) else 0) =
      c * simpleGraphWeightedDegree x G v := by
  classical
  rw [simpleGraphWeightedDegree_eq_sum x G v]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _hw
  by_cases h : G.Adj v w <;> simp [h]

theorem simpleGraphRowWeight_eq_mul_weightedDegree
    (x : V → Nat) (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (∑ w : V, if G.Adj v w then (x v : Rat) * (x w : Rat) else 0) =
      (x v : Rat) * simpleGraphWeightedDegree x G v := by
  exact weightedAdjacencySum_eq_mul_weightedDegree x G (x v : Rat) v

theorem replaceVertex_row_t_of_not_adj
    (x : V → Nat) (G : SimpleGraph V) [DecidableRel G.Adj]
    {s t : V} (hn : ¬ G.Adj s t) :
    (∑ w : V,
      if (G.replaceVertex s t).Adj t w then (x t : Rat) * (x w : Rat) else 0) =
      (x t : Rat) * simpleGraphWeightedDegree x G s := by
  classical
  rw [← weightedAdjacencySum_eq_mul_weightedDegree x G (x t : Rat) s]
  apply Finset.sum_congr rfl
  intro w _hw
  by_cases hwt : w = t
  · subst w
    simp [SimpleGraph.replaceVertex, hn]
  · by_cases h : G.Adj s w <;> simp [SimpleGraph.replaceVertex, hwt, h]

theorem replaceVertex_col_t_of_not_adj
    (x : V → Nat) (G : SimpleGraph V) [DecidableRel G.Adj]
    {s t : V} (hn : ¬ G.Adj s t) :
    (∑ v : V,
      if (G.replaceVertex s t).Adj v t then (x v : Rat) * (x t : Rat) else 0) =
      (x t : Rat) * simpleGraphWeightedDegree x G s := by
  classical
  rw [← weightedAdjacencySum_eq_mul_weightedDegree x G (x t : Rat) s]
  apply Finset.sum_congr rfl
  intro v _hv
  by_cases hvt : v = t
  · subst v
    simp [SimpleGraph.replaceVertex, hn]
  · by_cases h : G.Adj v s
    · have hs : G.Adj s v := h.symm
      simp [SimpleGraph.replaceVertex, hvt, h, hs, mul_comm]
    · have hs : ¬ G.Adj s v := by
        intro hsv
        exact h hsv.symm
      simp [SimpleGraph.replaceVertex, hvt, h, hs]

theorem orderedRelWeight_split_vertex
    (x : V → Nat) (R : V → V → Prop) [DecidableRel R] (t : V) :
    orderedRelWeight x R =
      (∑ w : V, if R t w then (x t : Rat) * (x w : Rat) else 0) +
        ∑ v ∈ (Finset.univ.erase t),
          ∑ w : V, if R v w then (x v : Rat) * (x w : Rat) else 0 := by
  classical
  unfold orderedRelWeight
  rw [← Finset.add_sum_erase Finset.univ
    (fun v : V => ∑ w : V, if R v w then (x v : Rat) * (x w : Rat) else 0)
    (Finset.mem_univ t)]

theorem replaceVertex_row_ne_t
    (x : V → Nat) (G : SimpleGraph V) [DecidableRel G.Adj]
    {s t v : V} (hvt : v ≠ t) :
    (∑ w : V,
      if (G.replaceVertex s t).Adj v w then (x v : Rat) * (x w : Rat) else 0) =
      (∑ w : V, if G.Adj v w then (x v : Rat) * (x w : Rat) else 0) -
        (if G.Adj v t then (x v : Rat) * (x t : Rat) else 0) +
        (if G.Adj v s then (x v : Rat) * (x t : Rat) else 0) := by
  classical
  rw [← Finset.add_sum_erase Finset.univ
    (fun w : V =>
      if (G.replaceVertex s t).Adj v w then (x v : Rat) * (x w : Rat) else 0)
    (Finset.mem_univ t)]
  rw [← Finset.add_sum_erase Finset.univ
    (fun w : V => if G.Adj v w then (x v : Rat) * (x w : Rat) else 0)
    (Finset.mem_univ t)]
  have herase :
      (∑ x_1 ∈ Finset.univ.erase t,
          if (G.replaceVertex s t).Adj v x_1 then
            (x v : Rat) * (x x_1 : Rat) else 0) =
        ∑ x_1 ∈ Finset.univ.erase t,
          if G.Adj v x_1 then (x v : Rat) * (x x_1 : Rat) else 0 := by
    apply Finset.sum_congr rfl
    intro w hw
    have hwt : w ≠ t := by
      exact Finset.mem_erase.mp hw |>.1
    have hiff := G.adj_replaceVertex_iff_of_ne s hvt hwt
    by_cases h : G.Adj v w
    · have hr : (G.replaceVertex s t).Adj v w := hiff.mpr h
      simp [h, hr]
    · have hr : ¬ (G.replaceVertex s t).Adj v w := by
        intro hp
        exact h (hiff.mp hp)
      simp [h, hr]
  rw [herase]
  by_cases hvs : G.Adj v s
  · by_cases hvtAdj : G.Adj v t
    · simp [SimpleGraph.replaceVertex, hvt, hvs, hvtAdj]
      try ring_nf
    · simp [SimpleGraph.replaceVertex, hvt, hvs, hvtAdj]
      try ring_nf
  · by_cases hvtAdj : G.Adj v t
    · simp [SimpleGraph.replaceVertex, hvt, hvs, hvtAdj]
      try ring_nf
    · simp [SimpleGraph.replaceVertex, hvt, hvs, hvtAdj]

/-- The sum of the ordered weights of edges entering `t`, with `t` itself
removed from the outer sum, is `x_t` times the weighted degree of `t`. -/
theorem sum_adj_to_vertex_erase
    (x : V → Nat) (G : SimpleGraph V) [DecidableRel G.Adj] (t : V) :
    (∑ v ∈ Finset.univ.erase t,
      if G.Adj v t then (x v : Rat) * (x t : Rat) else 0) =
      (x t : Rat) * simpleGraphWeightedDegree x G t := by
  classical
  have hzero :
      (if G.Adj t t then (x t : Rat) * (x t : Rat) else 0) = 0 := by
    simp
  rw [Finset.sum_erase
    (s := Finset.univ)
    (a := t)
    (f := fun v : V => if G.Adj v t then (x v : Rat) * (x t : Rat) else 0)
    hzero]
  rw [← weightedAdjacencySum_eq_mul_weightedDegree x G (x t : Rat) t]
  apply Finset.sum_congr rfl
  intro v _hv
  by_cases h : G.Adj t v
  · have hv : G.Adj v t := h.symm
    simp [h, hv, mul_comm]
  · have hv : ¬ G.Adj v t := by
      intro hvt
      exact h hvt.symm
    simp [h, hv]

/-- If `s` and `t` are nonadjacent, then the ordered weights of the new
clone edges entering `t` sum to `x_t` times the weighted degree of `s`. -/
theorem sum_adj_to_clone_source_erase_of_not_adj
    (x : V → Nat) (G : SimpleGraph V) [DecidableRel G.Adj]
    {s t : V} (hn : ¬ G.Adj s t) :
    (∑ v ∈ Finset.univ.erase t,
      if G.Adj v s then (x v : Rat) * (x t : Rat) else 0) =
      (x t : Rat) * simpleGraphWeightedDegree x G s := by
  classical
  have hts : ¬ G.Adj t s := by
    intro h
    exact hn h.symm
  have hzero :
      (if G.Adj t s then (x t : Rat) * (x t : Rat) else 0) = 0 := by
    simp [hts]
  rw [Finset.sum_erase
    (s := Finset.univ)
    (a := t)
    (f := fun v : V => if G.Adj v s then (x v : Rat) * (x t : Rat) else 0)
    hzero]
  rw [← weightedAdjacencySum_eq_mul_weightedDegree x G (x t : Rat) s]
  apply Finset.sum_congr rfl
  intro v _hv
  by_cases h : G.Adj s v
  · have hv : G.Adj v s := h.symm
    simp [h, hv, mul_comm]
  · have hv : ¬ G.Adj v s := by
      intro hvs
      exact h hvs.symm
    simp [h, hv]

/-- Replacing a nonadjacent vertex `t` by a clone of `s` changes the ordered
weighted edge mass by twice `x_t` times the weighted-degree difference. -/
theorem orderedRelWeight_replaceVertex_of_not_adj
    (x : V → Nat) (G : SimpleGraph V) [DecidableRel G.Adj]
    {s t : V} (hn : ¬ G.Adj s t) :
    orderedRelWeight x (G.replaceVertex s t).Adj =
      orderedRelWeight x G.Adj +
        2 * (x t : Rat) *
          (simpleGraphWeightedDegree x G s - simpleGraphWeightedDegree x G t) := by
  classical
  let rowRep : V → Rat := fun v =>
    ∑ w : V,
      if (G.replaceVertex s t).Adj v w then
        (x v : Rat) * (x w : Rat) else 0
  let rowG : V → Rat := fun v =>
    ∑ w : V, if G.Adj v w then (x v : Rat) * (x w : Rat) else 0
  let loss : V → Rat := fun v =>
    if G.Adj v t then (x v : Rat) * (x t : Rat) else 0
  let gain : V → Rat := fun v =>
    if G.Adj v s then (x v : Rat) * (x t : Rat) else 0
  have hrows :
      (∑ v ∈ Finset.univ.erase t, rowRep v) =
        (∑ v ∈ Finset.univ.erase t, rowG v) -
          (∑ v ∈ Finset.univ.erase t, loss v) +
          (∑ v ∈ Finset.univ.erase t, gain v) := by
    calc
      (∑ v ∈ Finset.univ.erase t, rowRep v)
          = ∑ v ∈ Finset.univ.erase t,
              (rowG v - loss v + gain v) := by
            apply Finset.sum_congr rfl
            intro v hv
            have hvt : v ≠ t := (Finset.mem_erase.mp hv).1
            exact replaceVertex_row_ne_t x G (s := s) (t := t) (v := v) hvt
      _ = (∑ v ∈ Finset.univ.erase t, rowG v) -
            (∑ v ∈ Finset.univ.erase t, loss v) +
            (∑ v ∈ Finset.univ.erase t, gain v) := by
          simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hrepSplit :=
    orderedRelWeight_split_vertex x (G.replaceVertex s t).Adj t
  have hGSplit := orderedRelWeight_split_vertex x G.Adj t
  have hrowTRep := replaceVertex_row_t_of_not_adj x G hn
  have hrowTG := simpleGraphRowWeight_eq_mul_weightedDegree x G t
  have hloss := sum_adj_to_vertex_erase x G t
  have hgain := sum_adj_to_clone_source_erase_of_not_adj x G hn
  rw [hrepSplit, hGSplit]
  change
    rowRep t + (∑ v ∈ Finset.univ.erase t, rowRep v) =
      (rowG t + (∑ v ∈ Finset.univ.erase t, rowG v)) +
        2 * (x t : Rat) *
          (simpleGraphWeightedDegree x G s - simpleGraphWeightedDegree x G t)
  simp only [rowRep, rowG, loss, gain] at hrows hrowTRep hrowTG hloss hgain ⊢
  rw [hrowTRep, hrowTG, hrows, hloss, hgain]
  ring

/-- A proper coloring bounds the weighted edge mass by the mass crossing the
corresponding color partition. -/
theorem orderedRelWeight_le_partition_of_coloring
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (x : V → Nat) (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : G.Coloring κ) :
    orderedRelWeight x G.Adj ≤
      (totalWeightNat x : Rat)^2 - partitionSquareWeight x (fun v : V => C v) := by
  classical
  have hle :=
    orderedRelWeight_le_of_imp x G.Adj
      (fun v w : V => C v ≠ C w)
      (by
        intro v w hvw
        exact C.valid hvw)
  rw [orderedRelWeight_partition_ne] at hle
  exact hle

/-- A colorable graph admits a partition whose crossing mass bounds its
weighted edge mass. -/
theorem exists_partition_bound_of_colorable
    (x : V → Nat) (G : SimpleGraph V) [DecidableRel G.Adj] {r : Nat}
    (hc : G.Colorable r) :
    ∃ p : V → Fin r,
      orderedRelWeight x G.Adj ≤
        (totalWeightNat x : Rat)^2 - partitionSquareWeight x p := by
  rcases hc with ⟨C⟩
  exact ⟨fun v : V => C v, orderedRelWeight_le_partition_of_coloring x G C⟩

/-- Ordered weighted edge mass of a simple graph, with decidability hidden
behind `classical`. -/
noncomputable def simpleGraphOrderedWeight
    (x : V → Nat) (G : SimpleGraph V) : Rat := by
  classical
  exact orderedRelWeight x G.Adj

theorem simpleGraphOrderedWeight_eq_orderedRelWeight
    (x : V → Nat) (G : SimpleGraph V) [DecidableRel G.Adj] :
    simpleGraphOrderedWeight x G = orderedRelWeight x G.Adj := by
  classical
  unfold simpleGraphOrderedWeight
  exact @orderedRelWeight_eq_of_decidableRel V _ _ x G.Adj
    (fun a b => Classical.propDecidable (G.Adj a b)) _

/-- A graph is extremal for ordered weighted edge mass among graphs satisfying
`P`. -/
def IsOrderedWeightedExtremal
    (x : V → Nat) (G : SimpleGraph V)
    (P : SimpleGraph V → Prop) : Prop :=
  P G ∧
    ∀ ⦃H : SimpleGraph V⦄,
      P H → simpleGraphOrderedWeight x H ≤ simpleGraphOrderedWeight x G

namespace IsOrderedWeightedExtremal

theorem prop
    {x : V → Nat} {G : SimpleGraph V}
    {P : SimpleGraph V → Prop}
    (h : IsOrderedWeightedExtremal x G P) :
    P G :=
  h.1

theorem orderedWeight_le
    {x : V → Nat} {G H : SimpleGraph V} {P : SimpleGraph V → Prop}
    (h : IsOrderedWeightedExtremal x G P) (hH : P H) :
    simpleGraphOrderedWeight x H ≤ simpleGraphOrderedWeight x G :=
  h.2 hH

end IsOrderedWeightedExtremal

/-- Existence of an ordered-weight extremal graph for any satisfiable property
on a finite vertex set. -/
theorem exists_isOrderedWeightedExtremal_of_exists
    (x : V → Nat) (P : SimpleGraph V → Prop)
    (hex : ∃ G : SimpleGraph V, P G) :
    ∃ G : SimpleGraph V, IsOrderedWeightedExtremal x G P := by
  classical
  obtain ⟨G₀, hG₀⟩ := hex
  obtain ⟨G, hGmem, hmax⟩ :=
    Finset.exists_max_image
      ({G : SimpleGraph V | P G} : Finset (SimpleGraph V))
      (fun G : SimpleGraph V =>
        simpleGraphOrderedWeight x G)
      ⟨G₀, by simp [hG₀]⟩
  refine ⟨G, ?_⟩
  constructor
  · exact (Finset.mem_filter.mp hGmem).2
  · intro H hH
    exact hmax H (Finset.mem_filter.mpr ⟨Finset.mem_univ H, hH⟩)

/-- In an ordered-weight extremal family closed under cloning, cloning `t` to a
nonadjacent `s` cannot increase the weighted edge mass.  If `x_t > 0`, this
forces the weighted degree of `s` to be at most that of `t`. -/
theorem weightedDegree_le_of_not_adj_of_orderedExtremal
    (x : V → Nat) (G : SimpleGraph V) [DecidableRel G.Adj]
    {P : SimpleGraph V → Prop}
    (hG : IsOrderedWeightedExtremal x G P)
    {s t : V} (hn : ¬ G.Adj s t) (hxt : 0 < x t)
    (hreplace : P (G.replaceVertex s t)) :
    simpleGraphWeightedDegree x G s ≤ simpleGraphWeightedDegree x G t := by
  classical
  have hle := hG.orderedWeight_le hreplace
  rw [simpleGraphOrderedWeight_eq_orderedRelWeight x (G.replaceVertex s t),
    simpleGraphOrderedWeight_eq_orderedRelWeight x G] at hle
  rw [orderedRelWeight_replaceVertex_of_not_adj x G hn] at hle
  have hxtRat : 0 < (x t : Rat) := by exact_mod_cast hxt
  nlinarith

/-- In an ordered-weight extremal `K_{r+1}`-free graph, nonadjacent positive
vertices have ordered weighted degrees in the cloning order. -/
theorem weightedDegree_le_of_not_adj_of_cliqueFree_extremal
    (x : V → Nat) (G : SimpleGraph V) [DecidableRel G.Adj]
    {r : Nat}
    (hG : IsOrderedWeightedExtremal x G
      (fun H : SimpleGraph V => H.CliqueFree (r + 1)))
    {s t : V} (hn : ¬ G.Adj s t) (hxt : 0 < x t) :
    simpleGraphWeightedDegree x G s ≤ simpleGraphWeightedDegree x G t := by
  exact weightedDegree_le_of_not_adj_of_orderedExtremal x G hG hn hxt
    (hG.prop.replaceVertex s t)

/-- Nonadjacent positive vertices in an ordered-weight extremal `K_{r+1}`-free
graph have equal weighted degrees. -/
theorem weightedDegree_eq_of_not_adj_of_cliqueFree_extremal
    (x : V → Nat) (G : SimpleGraph V) [DecidableRel G.Adj]
    {r : Nat}
    (hG : IsOrderedWeightedExtremal x G
      (fun H : SimpleGraph V => H.CliqueFree (r + 1)))
    {s t : V} (hn : ¬ G.Adj s t) (hxs : 0 < x s) (hxt : 0 < x t) :
    simpleGraphWeightedDegree x G s = simpleGraphWeightedDegree x G t := by
  have hst :=
    weightedDegree_le_of_not_adj_of_cliqueFree_extremal x G hG hn hxt
  have hts_not : ¬ G.Adj t s := by
    intro h
    exact hn h.symm
  have hts :=
    weightedDegree_le_of_not_adj_of_cliqueFree_extremal x G hG hts_not hxs
  exact le_antisymm hst hts

/-- Replacing a nonadjacent `t` by a clone of `s` leaves the weighted degree
of `s` unchanged. -/
theorem simpleGraphWeightedDegree_replaceVertex_source_of_not_adj
    (x : V → Nat) (G : SimpleGraph V) [DecidableRel G.Adj]
    {s t : V} (hn : ¬ G.Adj s t) :
    simpleGraphWeightedDegree x (G.replaceVertex s t) s =
      simpleGraphWeightedDegree x G s := by
  classical
  rw [simpleGraphWeightedDegree_eq_sum x (G.replaceVertex s t) s,
    simpleGraphWeightedDegree_eq_sum x G s]
  apply Finset.sum_congr rfl
  intro w _hw
  by_cases hwt : w = t
  · subst w
    have hrep : ¬ (G.replaceVertex s t).Adj s t :=
      SimpleGraph.not_adj_replaceVertex_same G s t
    simp [hrep, hn]
  · have hiff := G.adj_replaceVertex_iff_of_ne_left (s := s) hwt
    by_cases h : G.Adj s w
    · have hr : (G.replaceVertex s t).Adj s w := hiff.mpr h
      simp [h, hr]
    · have hr : ¬ (G.replaceVertex s t).Adj s w := by
        intro hp
        exact h (hiff.mp hp)
      simp [h, hr]

/-- If `u` was adjacent to `t` but not to `s`, replacing `t` by a clone of
`s` subtracts exactly `x_t` from the weighted degree of `u`. -/
theorem simpleGraphWeightedDegree_replaceVertex_eq_sub_of_adj_target_not_adj_source
    (x : V → Nat) (G : SimpleGraph V) [DecidableRel G.Adj]
    {s t u : V} (hut : G.Adj u t) (hus : ¬ G.Adj u s) :
    simpleGraphWeightedDegree x (G.replaceVertex s t) u =
      simpleGraphWeightedDegree x G u - (x t : Rat) := by
  have hut_ne : u ≠ t := hut.ne
  rw [simpleGraphWeightedDegree_eq_sum x (G.replaceVertex s t) u,
    simpleGraphWeightedDegree_eq_sum x G u]
  have herase :
      (∑ x_1 ∈ Finset.univ.erase t,
          if (G.replaceVertex s t).Adj u x_1 then (x x_1 : Rat) else 0) =
        ∑ x_1 ∈ Finset.univ.erase t,
          if G.Adj u x_1 then (x x_1 : Rat) else 0 := by
    apply Finset.sum_congr rfl
    intro w hw
    have hwt : w ≠ t := (Finset.mem_erase.mp hw).1
    have hiff := G.adj_replaceVertex_iff_of_ne (s := s) hut_ne hwt
    by_cases h : G.Adj u w
    · have hr : (G.replaceVertex s t).Adj u w := hiff.mpr h
      simp [h, hr]
    · have hr : ¬ (G.replaceVertex s t).Adj u w := by
        intro hp
        exact h (hiff.mp hp)
      simp [h, hr]
  have hrep_t : ¬ (G.replaceVertex s t).Adj u t := by
    simp [SimpleGraph.replaceVertex, hut_ne, hus]
  have hrep_zero :
      (if (G.replaceVertex s t).Adj u t then (x t : Rat) else 0) = 0 := by
    simp [hrep_t]
  have hrep_full :
      (∑ w : V,
          if (G.replaceVertex s t).Adj u w then (x w : Rat) else 0) =
        (∑ w ∈ Finset.univ.erase t,
          if (G.replaceVertex s t).Adj u w then (x w : Rat) else 0) := by
    symm
    exact Finset.sum_erase
      (s := Finset.univ)
      (a := t)
      (f := fun w : V =>
        if (G.replaceVertex s t).Adj u w then (x w : Rat) else 0)
      hrep_zero
  have horig_full :
      (∑ w : V, if G.Adj u w then (x w : Rat) else 0) =
        (x t : Rat) +
          (∑ w ∈ Finset.univ.erase t,
            if G.Adj u w then (x w : Rat) else 0) := by
    simpa [hut] using
      (Finset.add_sum_erase
        (s := Finset.univ)
        (f := fun w : V => if G.Adj u w then (x w : Rat) else 0)
        (a := t)
        (Finset.mem_univ t)).symm
  calc
    (∑ w : V,
        if (G.replaceVertex s t).Adj u w then (x w : Rat) else 0)
        = (∑ w ∈ Finset.univ.erase t,
            if (G.replaceVertex s t).Adj u w then (x w : Rat) else 0) := hrep_full
    _ = (∑ w ∈ Finset.univ.erase t,
            if G.Adj u w then (x w : Rat) else 0) := herase
    _ = ((x t : Rat) +
            (∑ w ∈ Finset.univ.erase t,
              if G.Adj u w then (x w : Rat) else 0)) - (x t : Rat) := by
          ring
    _ = (∑ w : V, if G.Adj u w then (x w : Rat) else 0) -
          (x t : Rat) := by
          rw [horig_full]

/-- On positive-weight vertices of an ordered-weight extremal `K_{r+1}`-free
graph, non-adjacency is transitive. -/
theorem not_adj_trans_on_positive_of_cliqueFree_extremal
    (x : V → Nat) (G : SimpleGraph V) [DecidableRel G.Adj]
    {r : Nat}
    (hG : IsOrderedWeightedExtremal x G
      (fun H : SimpleGraph V => H.CliqueFree (r + 1)))
    {s t u : V} (hxs : 0 < x s) (hxt : 0 < x t) (hxu : 0 < x u)
    (hts : ¬ G.Adj t s) (hsu : ¬ G.Adj s u) :
    ¬ G.Adj t u := by
  intro htu
  have hst : ¬ G.Adj s t := by
    intro h
    exact hts h.symm
  have hus : ¬ G.Adj u s := by
    intro h
    exact hsu h.symm
  have hdeg_st :=
    weightedDegree_eq_of_not_adj_of_cliqueFree_extremal x G hG hst hxs hxt
  have hdeg_su :=
    weightedDegree_eq_of_not_adj_of_cliqueFree_extremal x G hG hsu hxs hxu
  let G' := G.replaceVertex s t
  let H := G'.replaceVertex s u
  have hG'_su : ¬ G'.Adj s u := by
    have hut_ne : u ≠ t := htu.ne.symm
    have hiff :
        (G.replaceVertex s t).Adj s u ↔ G.Adj s u :=
      G.adj_replaceVertex_iff_of_ne_left (s := s) (t := t) (w := u) hut_ne
    intro h
    exact hsu (hiff.mp h)
  have hdeg_s_rep :
      simpleGraphWeightedDegree x G' s =
        simpleGraphWeightedDegree x G s := by
    simpa [G'] using
      simpleGraphWeightedDegree_replaceVertex_source_of_not_adj x G hst
  have hdeg_u_rep :
      simpleGraphWeightedDegree x G' u =
        simpleGraphWeightedDegree x G u - (x t : Rat) := by
    simpa [G'] using
      simpleGraphWeightedDegree_replaceVertex_eq_sub_of_adj_target_not_adj_source
        x G (s := s) (t := t) (u := u) htu.symm hus
  have hHcf : H.CliqueFree (r + 1) := by
    simpa [H, G'] using
      (hG.prop.replaceVertex s t).replaceVertex s u
  have hle := hG.orderedWeight_le hHcf
  rw [simpleGraphOrderedWeight_eq_orderedRelWeight x H,
    simpleGraphOrderedWeight_eq_orderedRelWeight x G] at hle
  have htotal :
      orderedRelWeight x H.Adj =
        orderedRelWeight x G.Adj + 2 * (x u : Rat) * (x t : Rat) := by
    dsimp [H, G']
    rw [orderedRelWeight_replaceVertex_of_not_adj x (G.replaceVertex s t) hG'_su]
    rw [orderedRelWeight_replaceVertex_of_not_adj x G hst]
    rw [hdeg_s_rep, hdeg_u_rep]
    nlinarith [hdeg_st, hdeg_su]
  rw [htotal] at hle
  have hxtRat : 0 < (x t : Rat) := by exact_mod_cast hxt
  have hxuRat : 0 < (x u : Rat) := by exact_mod_cast hxu
  nlinarith

/-- The positive-weight induced subgraph of an ordered-weight extremal
`K_{r+1}`-free graph is complete multipartite. -/
theorem positive_induce_isCompleteMultipartite_of_cliqueFree_extremal
    (x : V → Nat) (G : SimpleGraph V) [DecidableRel G.Adj]
    {r : Nat}
    (hG : IsOrderedWeightedExtremal x G
      (fun H : SimpleGraph V => H.CliqueFree (r + 1))) :
    (G.induce {v : V | 0 < x v}).IsCompleteMultipartite := by
  constructor
  intro a b c hab hbc
  change ¬ G.Adj a.1 b.1 at hab
  change ¬ G.Adj b.1 c.1 at hbc
  have hts : ¬ G.Adj a.1 b.1 := hab
  have hsu : ¬ G.Adj b.1 c.1 := hbc
  have h :=
    not_adj_trans_on_positive_of_cliqueFree_extremal
      x G hG (s := b.1) (t := a.1) (u := c.1)
      b.2 a.2 c.2 hts hsu
  change ¬ G.Adj a.1 c.1
  exact h

/-- The positive-weight induced subgraph of an ordered-weight extremal
`K_{r+1}`-free graph is `r`-colorable. -/
theorem positive_induce_colorable_of_cliqueFree_extremal
    (x : V → Nat) (G : SimpleGraph V) [DecidableRel G.Adj]
    {r : Nat}
    (hG : IsOrderedWeightedExtremal x G
      (fun H : SimpleGraph V => H.CliqueFree (r + 1))) :
    (G.induce {v : V | 0 < x v}).Colorable r := by
  have hcmp :=
    positive_induce_isCompleteMultipartite_of_cliqueFree_extremal x G hG
  have hcf : (G.induce {v : V | 0 < x v}).CliqueFree (r + 1) := by
    rw [SimpleGraph.cliqueFree_induce_iff]
    exact hG.prop.cliqueFreeOn
  simpa using hcmp.colorable_of_cliqueFree hcf

/-- A coloring of the positive-weight induced subgraph gives a full partition
bound; zero-weight vertices can be assigned any color. -/
theorem exists_partition_bound_of_positive_induce_coloring
    (x : V → Nat) (G : SimpleGraph V) [DecidableRel G.Adj]
    {r : Nat} (hr : 0 < r)
    (C : (G.induce {v : V | 0 < x v}).Coloring (Fin r)) :
    ∃ p : V → Fin r,
      orderedRelWeight x G.Adj ≤
        (totalWeightNat x : Rat)^2 - partitionSquareWeight x p := by
  let defaultColor : Fin r := ⟨0, hr⟩
  let p : V → Fin r := fun v =>
    if hv : 0 < x v then C ⟨v, hv⟩ else defaultColor
  refine ⟨p, ?_⟩
  have hle :
      orderedRelWeight x G.Adj ≤
        orderedRelWeight x (fun v w : V => p v ≠ p w) := by
    unfold orderedRelWeight
    apply Finset.sum_le_sum
    intro v _hv
    apply Finset.sum_le_sum
    intro w _hw
    by_cases hAdj : G.Adj v w
    · by_cases hvpos : 0 < x v
      · by_cases hwpos : 0 < x w
        · have hAdjInd :
              (G.induce {z : V | 0 < x z}).Adj ⟨v, hvpos⟩ ⟨w, hwpos⟩ := by
            change G.Adj v w
            exact hAdj
          have hcolors : C ⟨v, hvpos⟩ ≠ C ⟨w, hwpos⟩ :=
            C.valid hAdjInd
          have hp : p v ≠ p w := by
            simpa [p, hvpos, hwpos] using hcolors
          simp [hAdj, hp]
        · have hxw : x w = 0 := Nat.eq_zero_of_not_pos hwpos
          by_cases hp : p v ≠ p w <;> simp [hAdj, hp, hxw]
      · have hxv : x v = 0 := Nat.eq_zero_of_not_pos hvpos
        by_cases hp : p v ≠ p w <;> simp [hAdj, hp, hxv]
    · by_cases hp : p v ≠ p w
      · simp [hAdj, hp]
        positivity
      · simp [hAdj, hp]
  rw [orderedRelWeight_partition_ne] at hle
  exact hle

/-- Weighted Turan partition bound for an ordered-weight extremal
`K_{r+1}`-free graph. -/
theorem exists_partition_bound_of_cliqueFree_extremal
    (x : V → Nat) (G : SimpleGraph V) [DecidableRel G.Adj]
    {r : Nat} (hr : 0 < r)
    (hG : IsOrderedWeightedExtremal x G
      (fun H : SimpleGraph V => H.CliqueFree (r + 1))) :
    ∃ p : V → Fin r,
      orderedRelWeight x G.Adj ≤
        (totalWeightNat x : Rat)^2 - partitionSquareWeight x p := by
  rcases positive_induce_colorable_of_cliqueFree_extremal x G hG with ⟨C⟩
  exact exists_partition_bound_of_positive_induce_coloring x G hr C

/-- Weighted Turan theorem in the partition form needed by the blocker step:
every `K_{r+1}`-free graph admits an `r`-partition whose crossing mass bounds
the graph's ordered weighted edge mass. -/
theorem exists_partition_bound_of_cliqueFree
    (x : V → Nat) (G : SimpleGraph V) [DecidableRel G.Adj]
    {r : Nat} (hr : 0 < r) (hcf : G.CliqueFree (r + 1)) :
    ∃ p : V → Fin r,
      orderedRelWeight x G.Adj ≤
        (totalWeightNat x : Rat)^2 - partitionSquareWeight x p := by
  classical
  obtain ⟨H, hH⟩ :=
    exists_isOrderedWeightedExtremal_of_exists x
      (fun H : SimpleGraph V => H.CliqueFree (r + 1))
      ⟨G, hcf⟩
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  obtain ⟨p, hp⟩ := exists_partition_bound_of_cliqueFree_extremal x H hr hH
  refine ⟨p, ?_⟩
  have hle := hH.orderedWeight_le hcf
  rw [simpleGraphOrderedWeight_eq_orderedRelWeight x G,
    simpleGraphOrderedWeight_eq_orderedRelWeight x H] at hle
  exact le_trans hle hp

/-- Summing unordered edge weights over the incidence set at `v` is the same
as summing `x_v x_w` over the neighbor set of `v`. -/
theorem sum_sym2Weight_incidenceSet
    (x : V → Nat) (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (∑ e : G.incidenceSet v, sym2Weight x e.1) =
      ∑ w : G.neighborSet v, (x v : Rat) * (x w.1 : Rat) := by
  classical
  let f : G.incidenceSet v ≃ G.neighborSet v :=
    G.incidenceSetEquivNeighborSet v
  symm
  exact Fintype.sum_equiv f.symm
    (fun w : G.neighborSet v => (x v : Rat) * (x w.1 : Rat))
    (fun e : G.incidenceSet v => sym2Weight x e.1) (by
      intro w
      simp [f, SimpleGraph.incidenceSetEquivNeighborSet])

/-- Version of `sum_sym2Weight_incidenceSet` using explicit set-builder
subtypes, matching `Finset.sum_toFinset_eq_subtype`. -/
theorem sum_sym2Weight_incidenceSubtype
    (x : V → Nat) (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (∑ e : {e // e ∈ G.incidenceSet v}, sym2Weight x e.1) =
      ∑ w : {w // w ∈ G.neighborSet v}, (x v : Rat) * (x w.1 : Rat) := by
  classical
  let f : {e // e ∈ G.incidenceSet v} ≃ {w // w ∈ G.neighborSet v} :=
    G.incidenceSetEquivNeighborSet v
  symm
  exact Fintype.sum_equiv f.symm
    (fun w : {w // w ∈ G.neighborSet v} =>
      (x v : Rat) * (x w.1 : Rat))
    (fun e : {e // e ∈ G.incidenceSet v} => sym2Weight x e.1) (by
      intro w
      simp [f, SimpleGraph.incidenceSetEquivNeighborSet])

theorem sum_sym2Weight_neighborImage
    (x : V → Nat) (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : V) :
    ∑ e ∈ (G.neighborFinset s).image (fun w => s(w, t)),
        sym2Weight x e =
      (x t : Rat) * simpleGraphWeightedDegree x G s := by
  classical
  rw [simpleGraphWeightedDegree_eq_neighborFinset, Finset.mul_sum]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro w hw
    simp [sym2Weight_mk]
    ring_nf
  · intro a ha b hb hab
    change s(a, t) = s(b, t) at hab
    rw [Sym2.eq_iff] at hab
    rcases hab with ⟨hab, _⟩ | ⟨hat, htb⟩
    · exact hab
    · subst a
      subst b
      have ht_neigh : t ∈ G.neighborFinset s := ha
      rw [SimpleGraph.mem_neighborFinset] at ht_neigh

/-- A graph is weighted-extremal for property `P` if it satisfies `P` and
maximizes weighted edge mass among all graphs on the same weighted vertex
set satisfying `P`. -/
def IsWeightedExtremal
    (x : V → Nat) (G : SimpleGraph V)
    (P : SimpleGraph V → Prop) : Prop :=
  P G ∧
    ∀ ⦃H : SimpleGraph V⦄,
      P H → simpleGraphEdgeWeight x H ≤ simpleGraphEdgeWeight x G

namespace IsWeightedExtremal

theorem prop
    {x : V → Nat} {G : SimpleGraph V}
    {P : SimpleGraph V → Prop}
    (h : IsWeightedExtremal x G P) :
    P G :=
  h.1

theorem edgeWeight_le
    {x : V → Nat} {G H : SimpleGraph V} {P : SimpleGraph V → Prop}
    (h : IsWeightedExtremal x G P) (hH : P H) :
    simpleGraphEdgeWeight x H ≤ simpleGraphEdgeWeight x G :=
  h.2 hH

end IsWeightedExtremal

/-- Existence of a weighted-extremal graph for any satisfiable property on a
finite vertex set. -/
theorem exists_isWeightedExtremal_of_exists
    (x : V → Nat) (P : SimpleGraph V → Prop)
    (hex : ∃ G : SimpleGraph V, P G) :
    ∃ G : SimpleGraph V, ∃ _ : DecidableRel G.Adj,
      IsWeightedExtremal x G P := by
  classical
  obtain ⟨G₀, hG₀⟩ := hex
  obtain ⟨G, hGmem, hmax⟩ :=
    Finset.exists_max_image
      ({G : SimpleGraph V | P G} : Finset (SimpleGraph V))
      (fun G : SimpleGraph V =>
        simpleGraphEdgeWeight x G)
      ⟨G₀, by simp [hG₀]⟩
  refine ⟨G, inferInstanceAs (DecidableRel G.Adj), ?_⟩
  constructor
  · exact (Finset.mem_filter.mp hGmem).2
  · intro H hH
    exact hmax H (Finset.mem_filter.mpr ⟨Finset.mem_univ H, hH⟩)

/-- Weighted-extremal `K_{r+1}`-free graphs exist when `r > 0`. -/
theorem exists_isWeightedTuranExtremal
    (x : V → Nat) {r : Nat} (hr : 0 < r) :
    ∃ G : SimpleGraph V, ∃ _ : DecidableRel G.Adj,
      IsWeightedExtremal x G (fun H : SimpleGraph V => H.CliqueFree (r + 1)) := by
  classical
  apply exists_isWeightedExtremal_of_exists
  exact ⟨⊥, SimpleGraph.cliqueFree_bot (by omega)⟩

end TheoremOneEndToEnd
end Lollipop

/-!
The manuscript-facing proposition is repeated here as `CoreStatement` so
this proof module does not cyclically import its public statement module.
`Statement.lean` imports this file and exposes the same expression under the
public name `Statement`.
-/

/-!
Manuscript Lemma 6.1 (`lem:weighted-turan`), in the equivalent ordered-edge
partition form used by the formalization.
-/

namespace Lollipop.Manuscript.Lemma_6_1

universe u

open TheoremOneEndToEnd

abbrev CoreStatement {V : Type u} [Fintype V] [DecidableEq V]
    (x : V -> Nat) (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : Nat) : Prop :=
  0 < r -> G.CliqueFree (r + 1) ->
    exists p : V -> Fin r,
      orderedRelWeight x G.Adj <=
        (totalWeightNat x : Rat) ^ 2 - partitionSquareWeight x p

end Lollipop.Manuscript.Lemma_6_1

/-! The actual numbered proof. -/

namespace Lollipop.Manuscript.Lemma_6_1

universe u

open TheoremOneEndToEnd

theorem proof {V : Type u} [Fintype V] [DecidableEq V]
    (x : V -> Nat) (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : Nat) : CoreStatement x G r := by
  intro hr hfree

  -- The referenced theorem is proved, rather than postulated, in
  -- The complete weighted symmetrization proof appears earlier in this same
  -- `Proof.lean`. It returns the required `r`-partition; no partition is
  -- supplied as an extra hypothesis here.
  exact exists_partition_bound_of_cliqueFree x G hr hfree

end Lollipop.Manuscript.Lemma_6_1
