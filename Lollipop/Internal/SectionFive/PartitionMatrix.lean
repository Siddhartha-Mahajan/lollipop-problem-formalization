import Lollipop.Internal.Matrix.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
Intersection matrices for the blocker step.

The weighted blocker lemma intersects a three-partition and a four-partition
of the quotient vertices.  This file proves the bookkeeping that the
manuscript states as "squaring after grouping can only increase the sum of
squares": the intersection matrix has the expected row and column sums, and
its entry-square sum dominates the original square-sum of the vertex weights.
-/

namespace Lollipop

open BigOperators

variable {ι : Type*} [Fintype ι]

private theorem sum_partition_indicator_eq
    (f : ι → Rat) (p3 : ι → Fin 3) (p4 : ι → Fin 4) :
    (∑ i : Fin 3, ∑ j : Fin 4, ∑ v : ι,
        if p3 v = i ∧ p4 v = j then f v else 0) =
      ∑ v : ι, f v := by
  classical
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2
    intro j
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _hv
  let i3 := p3 v
  let j4 := p4 v
  have hi3 : p3 v = i3 := rfl
  have hj4 : p4 v = j4 := rfl
  rw [hi3, hj4]
  rcases i3 with ⟨i3, hi3lt⟩
  rcases j4 with ⟨j4, hj4lt⟩
  interval_cases i3 <;> interval_cases j4 <;>
    simp [Fin.sum_univ_three]

/-- Natural `3 x 4` matrix obtained by intersecting a `3`-partition and a
`4`-partition of a finite weighted set.  The maps `p3` and `p4` are the part
labels. -/
def partitionMatrixNat
    (x : ι → Nat) (p3 : ι → Fin 3) (p4 : ι → Fin 4) : NatMatrix :=
  fun i j => ∑ v : ι, if p3 v = i ∧ p4 v = j then x v else 0

/-- Total weight of the finite weighted set. -/
def totalWeightNat (x : ι → Nat) : Nat :=
  ∑ v : ι, x v

/-- Square-sum of the original vertex weights, as a rational number. -/
def weightSquareSumRat (x : ι → Nat) : Rat :=
  ∑ v : ι, (x v : Rat)^2

/-- The row sum of the intersection matrix is the weight in the corresponding
part of the `3`-partition. -/
theorem rowSum_partitionMatrixNat
    (x : ι → Nat) (p3 : ι → Fin 3) (p4 : ι → Fin 4) (i : Fin 3) :
    rowSum (matrixOfNat (partitionMatrixNat x p3 p4)) i =
      ∑ v : ι, if p3 v = i then (x v : Rat) else 0 := by
  classical
  simp [rowSum, matrixOfNat, partitionMatrixNat]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _hv
  by_cases hi : p3 v = i <;> simp [hi]

/-- The column sum of the intersection matrix is the weight in the
corresponding part of the `4`-partition. -/
theorem colSum_partitionMatrixNat
    (x : ι → Nat) (p3 : ι → Fin 3) (p4 : ι → Fin 4) (j : Fin 4) :
    colSum (matrixOfNat (partitionMatrixNat x p3 p4)) j =
      ∑ v : ι, if p4 v = j then (x v : Rat) else 0 := by
  classical
  simp [colSum, matrixOfNat, partitionMatrixNat]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _hv
  by_cases hj : p4 v = j <;> simp [hj]

/-- The intersection matrix has the same total mass as the original weights. -/
theorem matrixTotalNat_partitionMatrixNat
    (x : ι → Nat) (p3 : ι → Fin 3) (p4 : ι → Fin 4) :
    matrixTotalNat (partitionMatrixNat x p3 p4) = totalWeightNat x := by
  classical
  apply Nat.cast_injective (R := Rat)
  calc
    (matrixTotalNat (partitionMatrixNat x p3 p4) : Rat)
        = ∑ i : Fin 3, rowSum (matrixOfNat (partitionMatrixNat x p3 p4)) i := by
            simp [matrixTotalNat, rowSum, matrixOfNat]
    _ = ∑ i : Fin 3, ∑ v : ι, if p3 v = i then (x v : Rat) else 0 := by
            apply Finset.sum_congr rfl
            intro i _hi
            exact rowSum_partitionMatrixNat x p3 p4 i
    _ = ∑ v : ι, ∑ i : Fin 3, if p3 v = i then (x v : Rat) else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ v : ι, (x v : Rat) := by
            apply Finset.sum_congr rfl
            intro v _hv
            simp
    _ = (totalWeightNat x : Rat) := by
            simp [totalWeightNat]

/-- Grouping vertex weights into intersection-matrix cells can only increase
the square sum. -/
theorem weightSquareSumRat_le_entrySqNat_partitionMatrixNat
    (x : ι → Nat) (p3 : ι → Fin 3) (p4 : ι → Fin 4) :
    weightSquareSumRat x ≤ entrySqNat (partitionMatrixNat x p3 p4) := by
  classical
  have hcell : ∀ i : Fin 3, ∀ j : Fin 4,
      (∑ v : ι, (if p3 v = i ∧ p4 v = j then (x v : Rat) else 0)^2) ≤
        (∑ v : ι, if p3 v = i ∧ p4 v = j then (x v : Rat) else 0)^2 := by
    intro i j
    exact Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
      (f := fun v : ι => if p3 v = i ∧ p4 v = j then (x v : Rat) else 0)
      (by intro v _hv; by_cases h : p3 v = i ∧ p4 v = j <;> simp [h])
  have hsum_le :
      (∑ i : Fin 3, ∑ j : Fin 4, ∑ v : ι,
          (if p3 v = i ∧ p4 v = j then (x v : Rat) else 0)^2) ≤
        (∑ i : Fin 3, ∑ j : Fin 4,
          (∑ v : ι, if p3 v = i ∧ p4 v = j then (x v : Rat) else 0)^2) := by
    apply Finset.sum_le_sum
    intro i _hi
    apply Finset.sum_le_sum
    intro j _hj
    exact hcell i j
  have hleft :
      (∑ i : Fin 3, ∑ j : Fin 4, ∑ v : ι,
          (if p3 v = i ∧ p4 v = j then (x v : Rat) else 0)^2) =
        weightSquareSumRat x := by
    have hsquares :
        (∑ i : Fin 3, ∑ j : Fin 4, ∑ v : ι,
            (if p3 v = i ∧ p4 v = j then (x v : Rat) else 0)^2) =
          (∑ i : Fin 3, ∑ j : Fin 4, ∑ v : ι,
            if p3 v = i ∧ p4 v = j then (x v : Rat)^2 else 0) := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      apply Finset.sum_congr rfl
      intro v _hv
      by_cases h : p3 v = i ∧ p4 v = j <;> simp [h]
    rw [hsquares]
    simpa [weightSquareSumRat] using
      (sum_partition_indicator_eq (fun v : ι => (x v : Rat)^2) p3 p4)
  have hright :
      (∑ i : Fin 3, ∑ j : Fin 4,
          (∑ v : ι, if p3 v = i ∧ p4 v = j then (x v : Rat) else 0)^2) =
        entrySqNat (partitionMatrixNat x p3 p4) := by
    simp [entrySqNat, partitionMatrixNat]
  rw [← hleft, ← hright]
  exact hsum_le

end Lollipop
