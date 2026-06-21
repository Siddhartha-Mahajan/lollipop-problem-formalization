import Lollipop.Internal.Matrix.Basic

/-!
Relabeling invariance for the `3 x 4` matrix quadratic form.

The local Section 5 moves are proved in canonical coordinates.  These lemmas
show that row and column permutations preserve the row sums, column sums,
entry-square sum, total mass, and `matrixF` after reindexing.
-/

namespace Lollipop

open BigOperators

/-- Relabel rows and columns of a rational `3 x 4` matrix. -/
def relabelMatrix
    (er : Fin 3 ≃ Fin 3) (ec : Fin 4 ≃ Fin 4)
    (U : Fin 3 → Fin 4 → ℚ) : Fin 3 → Fin 4 → ℚ :=
  fun i j => U (er i) (ec j)

/-- Relabel rows and columns of a natural `3 x 4` matrix. -/
def relabelNatMatrix
    (er : Fin 3 ≃ Fin 3) (ec : Fin 4 ≃ Fin 4)
    (U : NatMatrix) : NatMatrix :=
  fun i j => U (er i) (ec j)

/-- Coercing a relabeled natural matrix is the same as relabeling after
coercion. -/
theorem matrixOfNat_relabelNatMatrix
    (er : Fin 3 ≃ Fin 3) (ec : Fin 4 ≃ Fin 4)
    (U : NatMatrix) :
    matrixOfNat (relabelNatMatrix er ec U) =
      relabelMatrix er ec (matrixOfNat U) := by
  rfl

/-- Row sums are relabeled by the row permutation. -/
theorem rowSum_relabelMatrix
    (er : Fin 3 ≃ Fin 3) (ec : Fin 4 ≃ Fin 4)
    (U : Fin 3 → Fin 4 → ℚ) (i : Fin 3) :
    rowSum (relabelMatrix er ec U) i = rowSum U (er i) := by
  unfold rowSum relabelMatrix
  exact Equiv.sum_comp ec (fun j : Fin 4 => U (er i) j)

/-- Column sums are relabeled by the column permutation. -/
theorem colSum_relabelMatrix
    (er : Fin 3 ≃ Fin 3) (ec : Fin 4 ≃ Fin 4)
    (U : Fin 3 → Fin 4 → ℚ) (j : Fin 4) :
    colSum (relabelMatrix er ec U) j = colSum U (ec j) := by
  unfold colSum relabelMatrix
  exact Equiv.sum_comp er (fun i : Fin 3 => U i (ec j))

/-- Total mass is invariant under row and column relabeling. -/
theorem matrixTotal_relabelMatrix
    (er : Fin 3 ≃ Fin 3) (ec : Fin 4 ≃ Fin 4)
    (U : Fin 3 → Fin 4 → ℚ) :
    matrixTotal (relabelMatrix er ec U) = matrixTotal U := by
  unfold matrixTotal relabelMatrix
  calc
    (∑ i : Fin 3, ∑ j : Fin 4, U (er i) (ec j))
        = ∑ i : Fin 3, ∑ j : Fin 4, U i (ec j) := by
          exact Equiv.sum_comp er (fun i : Fin 3 => ∑ j : Fin 4, U i (ec j))
    _ = ∑ i : Fin 3, ∑ j : Fin 4, U i j := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact Equiv.sum_comp ec (fun j : Fin 4 => U i j)

/-- Natural total mass is invariant under row and column relabeling. -/
theorem matrixTotalNat_relabelNatMatrix
    (er : Fin 3 ≃ Fin 3) (ec : Fin 4 ≃ Fin 4)
    (U : NatMatrix) :
    matrixTotalNat (relabelNatMatrix er ec U) = matrixTotalNat U := by
  unfold matrixTotalNat relabelNatMatrix
  calc
    (∑ i : Fin 3, ∑ j : Fin 4, U (er i) (ec j))
        = ∑ i : Fin 3, ∑ j : Fin 4, U i (ec j) := by
          exact Equiv.sum_comp er (fun i : Fin 3 => ∑ j : Fin 4, U i (ec j))
    _ = ∑ i : Fin 3, ∑ j : Fin 4, U i j := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact Equiv.sum_comp ec (fun j : Fin 4 => U i j)

/-- The entry-square sum is invariant under row and column relabeling. -/
theorem entrySq_relabelMatrix
    (er : Fin 3 ≃ Fin 3) (ec : Fin 4 ≃ Fin 4)
    (U : Fin 3 → Fin 4 → ℚ) :
    (∑ i : Fin 3, ∑ j : Fin 4, (relabelMatrix er ec U i j)^2) =
      ∑ i : Fin 3, ∑ j : Fin 4, (U i j)^2 := by
  unfold relabelMatrix
  calc
    (∑ i : Fin 3, ∑ j : Fin 4, (U (er i) (ec j))^2)
        = ∑ i : Fin 3, ∑ j : Fin 4, (U i (ec j))^2 := by
          exact Equiv.sum_comp er
            (fun i : Fin 3 => ∑ j : Fin 4, (U i (ec j))^2)
    _ = ∑ i : Fin 3, ∑ j : Fin 4, (U i j)^2 := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact Equiv.sum_comp ec (fun j : Fin 4 => (U i j)^2)

/-- The matrix quadratic form is invariant under row and column relabeling. -/
theorem matrixF_relabelMatrix
    (er : Fin 3 ≃ Fin 3) (ec : Fin 4 ≃ Fin 4)
    (U : Fin 3 → Fin 4 → ℚ) :
    matrixF (relabelMatrix er ec U) = matrixF U := by
  unfold matrixF
  rw [entrySq_relabelMatrix er ec U]
  have hrow :
      (∑ i : Fin 3, (rowSum (relabelMatrix er ec U) i)^2) =
        ∑ i : Fin 3, (rowSum U i)^2 := by
    calc
      (∑ i : Fin 3, (rowSum (relabelMatrix er ec U) i)^2)
          = ∑ i : Fin 3, (rowSum U (er i))^2 := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [rowSum_relabelMatrix]
      _ = ∑ i : Fin 3, (rowSum U i)^2 := by
            exact Equiv.sum_comp er (fun i : Fin 3 => (rowSum U i)^2)
  have hcol :
      (∑ j : Fin 4, (colSum (relabelMatrix er ec U) j)^2) =
        ∑ j : Fin 4, (colSum U j)^2 := by
    calc
      (∑ j : Fin 4, (colSum (relabelMatrix er ec U) j)^2)
          = ∑ j : Fin 4, (colSum U (ec j))^2 := by
            apply Finset.sum_congr rfl
            intro j _hi
            rw [colSum_relabelMatrix]
      _ = ∑ j : Fin 4, (colSum U j)^2 := by
            exact Equiv.sum_comp ec (fun j : Fin 4 => (colSum U j)^2)
  rw [hrow, hcol]

/-- The natural-matrix quadratic form is invariant under row and column
relabeling. -/
theorem matrixFNat_relabelNatMatrix
    (er : Fin 3 ≃ Fin 3) (ec : Fin 4 ≃ Fin 4)
    (U : NatMatrix) :
    matrixFNat (relabelNatMatrix er ec U) = matrixFNat U := by
  unfold matrixFNat
  rw [matrixOfNat_relabelNatMatrix]
  exact matrixF_relabelMatrix er ec (matrixOfNat U)

end Lollipop
