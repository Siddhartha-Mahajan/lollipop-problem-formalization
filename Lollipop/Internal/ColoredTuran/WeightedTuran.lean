import Lollipop.Internal.SectionFive.PartitionMatrix
import Mathlib.Tactic

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
