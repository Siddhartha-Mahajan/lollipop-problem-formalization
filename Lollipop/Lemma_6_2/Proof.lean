import Lollipop.Lemma_6_1.Proof
import Lollipop.Theorem_7_1.Proof
import Mathlib.Tactic

/-!
Manuscript Lemma 6.2 (`lem:blocker`), with the complete proof chain.

The old numbered endpoint exposed only the last rational-arithmetic
implication.  This file now starts from the actual blocker graphs and proves
all of the intermediate premises:

1. apply the proved weighted Turán theorem to `Aᶜ` and `Bᶜ` to construct a
   three-partition and a four-partition;
2. turn the two complement upper bounds into lower bounds for `w(A)` and
   `w(B)`;
3. intersect the two partitions to form the natural `3 × 4` matrix;
4. prove that grouping weights into matrix cells can only increase the square
   sum `Q`;
5. apply the fully proved matrix theorem; and
6. combine the inequalities to obtain the blocker bound.

The foundational definitions used by both the weighted Turán and matrix
developments live in the numbered matrix proof file
`Lollipop/Lemma_7_2/Proof.lean`.  This avoids an import cycle while keeping the
actual Lemma 6.2 theorem and its complete assembly in this `Proof.lean` file.
-/

namespace Lollipop.Manuscript.Lemma_6_2

open Lollipop
open Lollipop.TheoremOneEndToEnd

universe u

/--
The manuscript blocker lemma in graph form.

For a graph `A`, the condition `Aᶜ.CliqueFree 4` is exactly the finite-graph
form of `α(A) ≤ 3`; similarly `Bᶜ.CliqueFree 5` expresses `α(B) ≤ 4`.
`weightSquareSumRat x` is `Q = ∑ᵢ xᵢ²`, `weightedEdgeMass` is the unordered
weighted edge mass `w`, and `concreteM (totalWeightNat x)` is the manuscript's
`M(n)`.
-/
abbrev CoreStatement
    {V : Type u} [Fintype V] [DecidableEq V]
    (x : V → Nat) (A B : SimpleGraph V)
    [DecidableRel A.Adj] [DecidableRel B.Adj] : Prop :=
  Aᶜ.CliqueFree 4 →
  Bᶜ.CliqueFree 5 →
    (3 / 2 : Rat) * weightSquareSumRat x +
        2 * weightedEdgeMass x A.Adj +
        2 * weightedEdgeMass x B.Adj ≥
      concreteM (totalWeightNat x)

/-- The complete checked proof of manuscript Lemma 6.2. -/
theorem proof
    {V : Type u} [Fintype V] [DecidableEq V]
    (x : V → Nat) (A B : SimpleGraph V)
    [DecidableRel A.Adj] [DecidableRel B.Adj] :
    CoreStatement x A B := by
  classical
  intro hA hB

  -- Because `Aᶜ` is `K₄`-free, the proved weighted Turán theorem constructs
  -- a three-partition whose crossing mass bounds the ordered mass of `Aᶜ`.
  obtain ⟨p3, hp3⟩ :=
    exists_partition_bound_of_cliqueFree x Aᶜ
      (r := 3) (by decide) hA

  -- Likewise `Bᶜ` is `K₅`-free, so weighted Turán constructs the required
  -- four-partition.  Neither partition is supplied as a hypothesis.
  obtain ⟨p4, hp4⟩ :=
    exists_partition_bound_of_cliqueFree x Bᶜ
      (r := 4) (by decide) hB

  -- Mathlib's graph complement is the off-diagonal complement relation used
  -- by the weighted-mass algebra.  This small conversion lets us feed the
  -- weighted Turán estimate for `Aᶜ` into that algebra.
  have hAcomp :
      orderedRelWeight x (fun v w : V => v ≠ w ∧ ¬ A.Adj v w) ≤
        (totalWeightNat x : Rat) ^ 2 - partitionSquareWeight x p3 := by
    have hle :=
      orderedRelWeight_le_of_imp x
        (fun v w : V => v ≠ w ∧ ¬ A.Adj v w)
        Aᶜ.Adj
        (by
          intro v w h
          exact (SimpleGraph.compl_adj A v w).2 h)
    exact le_trans hle hp3

  -- The complement estimate is equivalent to the manuscript lower bound
  -- `w(A) ≥ (ρ₃ - Q) / 2`.
  have ha :
      weightedEdgeMass x A.Adj ≥
        (partitionSquareWeight x p3 - weightSquareSumRat x) / 2 := by
    exact weightedEdgeMass_ge_of_complement_le_partition
      x A.Adj p3 (fun v => A.loopless.irrefl v) hAcomp

  -- Repeat the same conversion for `B` and its four-partition.
  have hBcomp :
      orderedRelWeight x (fun v w : V => v ≠ w ∧ ¬ B.Adj v w) ≤
        (totalWeightNat x : Rat) ^ 2 - partitionSquareWeight x p4 := by
    have hle :=
      orderedRelWeight_le_of_imp x
        (fun v w : V => v ≠ w ∧ ¬ B.Adj v w)
        Bᶜ.Adj
        (by
          intro v w h
          exact (SimpleGraph.compl_adj B v w).2 h)
    exact le_trans hle hp4

  have hb :
      weightedEdgeMass x B.Adj ≥
        (partitionSquareWeight x p4 - weightSquareSumRat x) / 2 := by
    exact weightedEdgeMass_ge_of_complement_le_partition
      x B.Adj p4 (fun v => B.loopless.irrefl v) hBcomp

  -- Intersect the three- and four-partitions.  Cell `(i,j)` contains the
  -- total vertex weight lying simultaneously in part `i` and part `j`.
  let U : NatMatrix := partitionMatrixNat x p3 p4

  -- Squaring after grouping nonnegative weights can only increase their
  -- square sum, giving the manuscript comparison `Q ≤ ∑ᵢⱼ uᵢⱼ²`.
  have hQ : weightSquareSumRat x ≤ entrySqNat U := by
    dsimp [U]
    exact weightSquareSumRat_le_entrySqNat_partitionMatrixNat x p3 p4

  -- The row-square and column-square sums of the intersection matrix are
  -- exactly the two partition square sums `ρ₃` and `ρ₄`.
  have hrho3 :
      partitionSquareWeight x p3 =
        ∑ i : Fin 3, (rowSum (matrixOfNat U) i) ^ 2 := by
    dsimp [U]
    exact partitionSquareWeight_fin3_eq_rowSq_partitionMatrixNat x p3 p4

  have hrho4 :
      partitionSquareWeight x p4 =
        ∑ j : Fin 4, (colSum (matrixOfNat U) j) ^ 2 := by
    dsimp [U]
    exact partitionSquareWeight_fin4_eq_colSq_partitionMatrixNat x p3 p4

  have hentry :
      entrySqNat U =
        ∑ i : Fin 3, ∑ j : Fin 4, ((matrixOfNat U) i j) ^ 2 := by
    rfl

  -- Theorem 7.1 is a fully proved theorem for every natural `3 × 4` matrix.
  -- The partition-intersection bookkeeping proves that `U` has total mass
  -- `∑ᵢ xᵢ`, so its lower bound is exactly the required `M(n)`.
  have hmatrix :
      matrixF (matrixOfNat U) ≥ concreteM (totalWeightNat x) := by
    have h := Lollipop.matrix_theorem_proven U
    change matrixF (matrixOfNat U) ≥ concreteM (matrixTotalNat U) at h
    rw [show matrixTotalNat U = totalWeightNat x by
      dsimp [U]
      exact matrixTotalNat_partitionMatrixNat x p3 p4] at h
    exact h

  -- The remaining calculation is now genuinely the last step: all four
  -- inputs (`ha`, `hb`, `hQ`, and `hmatrix`) were derived above from the two
  -- graph hypotheses by proved Lean theorems.
  have hblock :=
    blocker_cost_ge_of_matrixF_bound
      (matrixOfNat U) ha hb hQ hrho3 hrho4 hentry hmatrix
  simpa [blockerCost] using hblock

end Lollipop.Manuscript.Lemma_6_2
