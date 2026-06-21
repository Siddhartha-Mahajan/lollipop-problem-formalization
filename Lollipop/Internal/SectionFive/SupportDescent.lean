import Lollipop.Internal.Matrix.LocalMoves
import Lollipop.Internal.SectionFive.StarForestCases
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

/-!
Finite support-descent bookkeeping for the `3 x 4` matrix theorem.

The local polynomial moves live in `Lollipop.Matrix.LocalMoves`.  This file
adds the finite graph classification needed to apply those moves to an
arbitrary non-star support: up to row/column relabeling, such a support
contains a canonical four-cycle, a row-oriented four-edge path, a
column-oriented four-edge path, or a bounded double-star configuration.
-/

namespace Lollipop

open BigOperators

/-- Canonical four-cycle support used by `cycleMove`. -/
def descentCycleSupport : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4)), ((0 : Fin 3), (1 : Fin 4)),
    ((1 : Fin 3), (0 : Fin 4)), ((1 : Fin 3), (1 : Fin 4))}

/-- Canonical row-oriented four-edge path support used by `pathMove`. -/
def descentRowPathSupport : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4)), ((1 : Fin 3), (0 : Fin 4)),
    ((1 : Fin 3), (1 : Fin 4)), ((2 : Fin 3), (1 : Fin 4))}

/-- Canonical column-oriented four-edge path support. -/
def descentColPathSupport : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4)), ((0 : Fin 3), (1 : Fin 4)),
    ((1 : Fin 3), (1 : Fin 4)), ((1 : Fin 3), (2 : Fin 4))}

/-- The three required edges of the canonical double-star branch. -/
def descentDoubleStarCore : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4)), ((0 : Fin 3), (1 : Fin 4)),
    ((1 : Fin 3), (0 : Fin 4))}

/-- The allowed support envelope for the canonical double-star branch,
including possible disconnected leftover edges on the unused row/columns. -/
def descentDoubleStarSupport : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4)), ((0 : Fin 3), (1 : Fin 4)),
    ((1 : Fin 3), (0 : Fin 4)), ((0 : Fin 3), (2 : Fin 4)),
    ((0 : Fin 3), (3 : Fin 4)), ((2 : Fin 3), (0 : Fin 4)),
    ((2 : Fin 3), (2 : Fin 4)), ((2 : Fin 3), (3 : Fin 4))}

/-- Relabeling preserves support cardinality. -/
theorem supportRelabel_card :
    ∀ (er : Fin 3 ≃ Fin 3) (ec : Fin 4 ≃ Fin 4)
      (S : Finset MatrixEdge),
        (supportRelabel er ec S).card = S.card := by
  native_decide

/-- Relabeling a natural matrix preserves support cardinality. -/
theorem supportCardNat_relabelNatMatrix
    (er : Fin 3 ≃ Fin 3) (ec : Fin 4 ≃ Fin 4)
    (U : NatMatrix) :
    supportCardNat (relabelNatMatrix er ec U) = supportCardNat U := by
  unfold supportCardNat
  rw [supportOfNat_relabelNatMatrix, supportRelabel_card er.symm ec.symm]

/-- Finite classification of non-star supports into the local descent shapes. -/
theorem nonstar_support_has_descent_shape :
    ∀ S : Finset MatrixEdge,
      ¬ IsSupportStarForest S →
        (∃ er : Fin 3 ≃ Fin 3, ∃ ec : Fin 4 ≃ Fin 4,
          descentCycleSupport ⊆ supportRelabel er ec S) ∨
        (∃ er : Fin 3 ≃ Fin 3, ∃ ec : Fin 4 ≃ Fin 4,
          descentRowPathSupport ⊆ supportRelabel er ec S) ∨
        (∃ er : Fin 3 ≃ Fin 3, ∃ ec : Fin 4 ≃ Fin 4,
          descentColPathSupport ⊆ supportRelabel er ec S) ∨
        (∃ er : Fin 3 ≃ Fin 3, ∃ ec : Fin 4 ≃ Fin 4,
          descentDoubleStarCore ⊆ supportRelabel er ec S ∧
            supportRelabel er ec S ⊆ descentDoubleStarSupport) := by
  native_decide

/-- Positive endpoint of the canonical four-cycle move, as a natural matrix. -/
def cycleMoveNatPlus (U : NatMatrix) (N : Nat) : NatMatrix :=
  fun i j =>
    if i = 0 ∧ j = 0 then U i j + N else
    if i = 0 ∧ j = 1 then U i j - N else
    if i = 1 ∧ j = 1 then U i j + N else
    if i = 1 ∧ j = 0 then U i j - N else
    U i j

/-- Negative endpoint of the canonical four-cycle move, as a natural matrix. -/
def cycleMoveNatMinus (U : NatMatrix) (P : Nat) : NatMatrix :=
  fun i j =>
    if i = 0 ∧ j = 0 then U i j - P else
    if i = 0 ∧ j = 1 then U i j + P else
    if i = 1 ∧ j = 1 then U i j - P else
    if i = 1 ∧ j = 0 then U i j + P else
    U i j

theorem matrixTotalNat_cycleMoveNatPlus
    (U : NatMatrix) (N : Nat)
    (h01 : N <= U 0 1) (h10 : N <= U 1 0) :
    matrixTotalNat (cycleMoveNatPlus U N) = matrixTotalNat U := by
  simp [matrixTotalNat, cycleMoveNatPlus, Fin.sum_univ_three, Fin.sum_univ_four]
  omega

theorem matrixTotalNat_cycleMoveNatMinus
    (U : NatMatrix) (P : Nat)
    (h00 : P <= U 0 0) (h11 : P <= U 1 1) :
    matrixTotalNat (cycleMoveNatMinus U P) = matrixTotalNat U := by
  simp [matrixTotalNat, cycleMoveNatMinus, Fin.sum_univ_three, Fin.sum_univ_four]
  omega

theorem matrixOfNat_cycleMoveNatPlus
    (U : NatMatrix) (N : Nat)
    (h01 : N <= U 0 1) (h10 : N <= U 1 0) :
    matrixOfNat (cycleMoveNatPlus U N) =
      cycleMove (matrixOfNat U) (N : Rat) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixOfNat, cycleMoveNatPlus, cycleMove, h01, h10, Nat.cast_sub]

theorem matrixOfNat_cycleMoveNatMinus
    (U : NatMatrix) (P : Nat)
    (h00 : P <= U 0 0) (h11 : P <= U 1 1) :
    matrixOfNat (cycleMoveNatMinus U P) =
      cycleMove (matrixOfNat U) (-(P : Rat)) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixOfNat, cycleMoveNatMinus, cycleMove, h00, h11, Nat.cast_sub] <;>
      ring

theorem supportCardNat_lt_of_support_ssubset
    {V U : NatMatrix} (h : supportOfNat V ⊂ supportOfNat U) :
    supportCardNat V < supportCardNat U := by
  unfold supportCardNat
  exact Finset.card_lt_card h

theorem supportOfNat_cycleMoveNatPlus_subset
    (U : NatMatrix) (N : Nat)
    (hcycle : descentCycleSupport ⊆ supportOfNat U) :
    supportOfNat (cycleMoveNatPlus U N) ⊆ supportOfNat U := by
  have h00pos : 0 < U 0 0 := by
    rw [← mem_supportOfNat_iff U ((0 : Fin 3), (0 : Fin 4))]
    exact hcycle (by simp [descentCycleSupport])
  have h11pos : 0 < U 1 1 := by
    rw [← mem_supportOfNat_iff U ((1 : Fin 3), (1 : Fin 4))]
    exact hcycle (by simp [descentCycleSupport])
  intro e he
  rw [mem_supportOfNat_iff] at he ⊢
  rcases e with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [cycleMoveNatPlus] at he ⊢ <;> omega

theorem supportOfNat_cycleMoveNatMinus_subset
    (U : NatMatrix) (P : Nat)
    (hcycle : descentCycleSupport ⊆ supportOfNat U) :
    supportOfNat (cycleMoveNatMinus U P) ⊆ supportOfNat U := by
  have h01pos : 0 < U 0 1 := by
    rw [← mem_supportOfNat_iff U ((0 : Fin 3), (1 : Fin 4))]
    exact hcycle (by simp [descentCycleSupport])
  have h10pos : 0 < U 1 0 := by
    rw [← mem_supportOfNat_iff U ((1 : Fin 3), (0 : Fin 4))]
    exact hcycle (by simp [descentCycleSupport])
  intro e he
  rw [mem_supportOfNat_iff] at he ⊢
  rcases e with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [cycleMoveNatMinus] at he ⊢ <;> omega

theorem supportCardNat_cycleMoveNatPlus_lt
    (U : NatMatrix) (N : Nat)
    (hcycle : descentCycleSupport ⊆ supportOfNat U)
    (hNpos : 0 < N) (h01 : N <= U 0 1) (h10 : N <= U 1 0)
    (hNmin : N = Nat.min (U 0 1) (U 1 0)) :
    supportCardNat (cycleMoveNatPlus U N) < supportCardNat U := by
  apply supportCardNat_lt_of_support_ssubset
  refine ⟨supportOfNat_cycleMoveNatPlus_subset U N hcycle, ?_⟩
  intro hsubset
  have h01mem : ((0 : Fin 3), (1 : Fin 4)) ∈ supportOfNat U :=
    hcycle (by simp [descentCycleSupport])
  have h10mem : ((1 : Fin 3), (0 : Fin 4)) ∈ supportOfNat U :=
    hcycle (by simp [descentCycleSupport])
  by_cases hle : U 0 1 <= U 1 0
  · have hN : N = U 0 1 := by simpa [hNmin, hle] using hNmin
    have hkilled : ((0 : Fin 3), (1 : Fin 4)) ∉
        supportOfNat (cycleMoveNatPlus U N) := by
      rw [mem_supportOfNat_iff]
      simp [cycleMoveNatPlus, hN]
    exact hkilled (hsubset h01mem)
  · have hlt : U 1 0 < U 0 1 := Nat.lt_of_not_ge hle
    have hN : N = U 1 0 := by
      simpa [hNmin, Nat.min_eq_right (le_of_lt hlt)] using hNmin
    have hkilled : ((1 : Fin 3), (0 : Fin 4)) ∉
        supportOfNat (cycleMoveNatPlus U N) := by
      rw [mem_supportOfNat_iff]
      simp [cycleMoveNatPlus, hN]
    exact hkilled (hsubset h10mem)

theorem supportCardNat_cycleMoveNatMinus_lt
    (U : NatMatrix) (P : Nat)
    (hcycle : descentCycleSupport ⊆ supportOfNat U)
    (hPpos : 0 < P) (h00 : P <= U 0 0) (h11 : P <= U 1 1)
    (hPmin : P = Nat.min (U 0 0) (U 1 1)) :
    supportCardNat (cycleMoveNatMinus U P) < supportCardNat U := by
  apply supportCardNat_lt_of_support_ssubset
  refine ⟨supportOfNat_cycleMoveNatMinus_subset U P hcycle, ?_⟩
  intro hsubset
  have h00mem : ((0 : Fin 3), (0 : Fin 4)) ∈ supportOfNat U :=
    hcycle (by simp [descentCycleSupport])
  have h11mem : ((1 : Fin 3), (1 : Fin 4)) ∈ supportOfNat U :=
    hcycle (by simp [descentCycleSupport])
  by_cases hle : U 0 0 <= U 1 1
  · have hP : P = U 0 0 := by simpa [hPmin, hle] using hPmin
    have hkilled : ((0 : Fin 3), (0 : Fin 4)) ∉
        supportOfNat (cycleMoveNatMinus U P) := by
      rw [mem_supportOfNat_iff]
      simp [cycleMoveNatMinus, hP]
    exact hkilled (hsubset h00mem)
  · have hlt : U 1 1 < U 0 0 := Nat.lt_of_not_ge hle
    have hP : P = U 1 1 := by
      simpa [hPmin, Nat.min_eq_right (le_of_lt hlt)] using hPmin
    have hkilled : ((1 : Fin 3), (1 : Fin 4)) ∉
        supportOfNat (cycleMoveNatMinus U P) := by
      rw [mem_supportOfNat_iff]
      simp [cycleMoveNatMinus, hP]
    exact hkilled (hsubset h11mem)

/-- A support containing the canonical four-cycle has a one-step descent. -/
theorem canonical_cycle_descent
    (U : NatMatrix)
    (hcycle : descentCycleSupport ⊆ supportOfNat U) :
    ∃ V : NatMatrix,
      matrixTotalNat V = matrixTotalNat U ∧
      matrixFNat V <= matrixFNat U ∧
      supportCardNat V < supportCardNat U := by
  have h00pos : 0 < U 0 0 := by
    rw [← mem_supportOfNat_iff U ((0 : Fin 3), (0 : Fin 4))]
    exact hcycle (by simp [descentCycleSupport])
  have h01pos : 0 < U 0 1 := by
    rw [← mem_supportOfNat_iff U ((0 : Fin 3), (1 : Fin 4))]
    exact hcycle (by simp [descentCycleSupport])
  have h10pos : 0 < U 1 0 := by
    rw [← mem_supportOfNat_iff U ((1 : Fin 3), (0 : Fin 4))]
    exact hcycle (by simp [descentCycleSupport])
  have h11pos : 0 < U 1 1 := by
    rw [← mem_supportOfNat_iff U ((1 : Fin 3), (1 : Fin 4))]
    exact hcycle (by simp [descentCycleSupport])
  let P : Nat := Nat.min (U 0 0) (U 1 1)
  let N : Nat := Nat.min (U 0 1) (U 1 0)
  have hPpos : 0 < P := by
    dsimp [P]
    exact lt_min h00pos h11pos
  have hNpos : 0 < N := by
    dsimp [N]
    exact lt_min h01pos h10pos
  have hP00 : P <= U 0 0 := by
    dsimp [P]
    exact Nat.min_le_left _ _
  have hP11 : P <= U 1 1 := by
    dsimp [P]
    exact Nat.min_le_right _ _
  have hN01 : N <= U 0 1 := by
    dsimp [N]
    exact Nat.min_le_left _ _
  have hN10 : N <= U 1 0 := by
    dsimp [N]
    exact Nat.min_le_right _ _
  have hend := matrixF_cycleMove_endpoint_nonincreasing
    (matrixOfNat U) (P := (P : Rat)) (N := (N : Rat))
    (by positivity) (by positivity)
  rcases hend with hplus | hminus
  · refine ⟨cycleMoveNatPlus U N, ?_, ?_, ?_⟩
    · exact matrixTotalNat_cycleMoveNatPlus U N hN01 hN10
    · unfold matrixFNat
      rw [matrixOfNat_cycleMoveNatPlus U N hN01 hN10]
      exact hplus
    · exact supportCardNat_cycleMoveNatPlus_lt U N hcycle hNpos hN01 hN10 rfl
  · refine ⟨cycleMoveNatMinus U P, ?_, ?_, ?_⟩
    · exact matrixTotalNat_cycleMoveNatMinus U P hP00 hP11
    · unfold matrixFNat
      rw [matrixOfNat_cycleMoveNatMinus U P hP00 hP11]
      exact hminus
    · exact supportCardNat_cycleMoveNatMinus_lt U P hcycle hPpos hP00 hP11 rfl

/-- Positive endpoint of the canonical row-oriented path move. -/
def rowPathMoveNatPlus (U : NatMatrix) (N : Nat) : NatMatrix :=
  fun i j =>
    if i = 0 ∧ j = 0 then U i j + N else
    if i = 1 ∧ j = 0 then U i j - N else
    if i = 1 ∧ j = 1 then U i j + N else
    if i = 2 ∧ j = 1 then U i j - N else
    U i j

/-- Negative endpoint of the canonical row-oriented path move. -/
def rowPathMoveNatMinus (U : NatMatrix) (P : Nat) : NatMatrix :=
  fun i j =>
    if i = 0 ∧ j = 0 then U i j - P else
    if i = 1 ∧ j = 0 then U i j + P else
    if i = 1 ∧ j = 1 then U i j - P else
    if i = 2 ∧ j = 1 then U i j + P else
    U i j

theorem matrixTotalNat_rowPathMoveNatPlus
    (U : NatMatrix) (N : Nat)
    (h10 : N <= U 1 0) (h21 : N <= U 2 1) :
    matrixTotalNat (rowPathMoveNatPlus U N) = matrixTotalNat U := by
  simp [matrixTotalNat, rowPathMoveNatPlus, Fin.sum_univ_three, Fin.sum_univ_four]
  omega

theorem matrixTotalNat_rowPathMoveNatMinus
    (U : NatMatrix) (P : Nat)
    (h00 : P <= U 0 0) (h11 : P <= U 1 1) :
    matrixTotalNat (rowPathMoveNatMinus U P) = matrixTotalNat U := by
  simp [matrixTotalNat, rowPathMoveNatMinus, Fin.sum_univ_three, Fin.sum_univ_four]
  omega

theorem matrixOfNat_rowPathMoveNatPlus
    (U : NatMatrix) (N : Nat)
    (h10 : N <= U 1 0) (h21 : N <= U 2 1) :
    matrixOfNat (rowPathMoveNatPlus U N) =
      pathMove (matrixOfNat U) (N : Rat) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixOfNat, rowPathMoveNatPlus, pathMove, h10, h21, Nat.cast_sub]

theorem matrixOfNat_rowPathMoveNatMinus
    (U : NatMatrix) (P : Nat)
    (h00 : P <= U 0 0) (h11 : P <= U 1 1) :
    matrixOfNat (rowPathMoveNatMinus U P) =
      pathMove (matrixOfNat U) (-(P : Rat)) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixOfNat, rowPathMoveNatMinus, pathMove, h00, h11, Nat.cast_sub] <;>
      ring

theorem supportOfNat_rowPathMoveNatPlus_subset
    (U : NatMatrix) (N : Nat)
    (hpath : descentRowPathSupport ⊆ supportOfNat U) :
    supportOfNat (rowPathMoveNatPlus U N) ⊆ supportOfNat U := by
  have h00pos : 0 < U 0 0 := by
    rw [← mem_supportOfNat_iff U ((0 : Fin 3), (0 : Fin 4))]
    exact hpath (by simp [descentRowPathSupport])
  have h11pos : 0 < U 1 1 := by
    rw [← mem_supportOfNat_iff U ((1 : Fin 3), (1 : Fin 4))]
    exact hpath (by simp [descentRowPathSupport])
  intro e he
  rw [mem_supportOfNat_iff] at he ⊢
  rcases e with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [rowPathMoveNatPlus] at he ⊢ <;> omega

theorem supportOfNat_rowPathMoveNatMinus_subset
    (U : NatMatrix) (P : Nat)
    (hpath : descentRowPathSupport ⊆ supportOfNat U) :
    supportOfNat (rowPathMoveNatMinus U P) ⊆ supportOfNat U := by
  have h10pos : 0 < U 1 0 := by
    rw [← mem_supportOfNat_iff U ((1 : Fin 3), (0 : Fin 4))]
    exact hpath (by simp [descentRowPathSupport])
  have h21pos : 0 < U 2 1 := by
    rw [← mem_supportOfNat_iff U ((2 : Fin 3), (1 : Fin 4))]
    exact hpath (by simp [descentRowPathSupport])
  intro e he
  rw [mem_supportOfNat_iff] at he ⊢
  rcases e with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [rowPathMoveNatMinus] at he ⊢ <;> omega

theorem supportCardNat_rowPathMoveNatPlus_lt
    (U : NatMatrix) (N : Nat)
    (hpath : descentRowPathSupport ⊆ supportOfNat U)
    (_hNpos : 0 < N) (_h10 : N <= U 1 0) (_h21 : N <= U 2 1)
    (hNmin : N = Nat.min (U 1 0) (U 2 1)) :
    supportCardNat (rowPathMoveNatPlus U N) < supportCardNat U := by
  apply supportCardNat_lt_of_support_ssubset
  refine ⟨supportOfNat_rowPathMoveNatPlus_subset U N hpath, ?_⟩
  intro hsubset
  have h10mem : ((1 : Fin 3), (0 : Fin 4)) ∈ supportOfNat U :=
    hpath (by simp [descentRowPathSupport])
  have h21mem : ((2 : Fin 3), (1 : Fin 4)) ∈ supportOfNat U :=
    hpath (by simp [descentRowPathSupport])
  by_cases hle : U 1 0 <= U 2 1
  · have hN : N = U 1 0 := by simpa [hNmin, hle] using hNmin
    have hkilled : ((1 : Fin 3), (0 : Fin 4)) ∉
        supportOfNat (rowPathMoveNatPlus U N) := by
      rw [mem_supportOfNat_iff]
      simp [rowPathMoveNatPlus, hN]
    exact hkilled (hsubset h10mem)
  · have hlt : U 2 1 < U 1 0 := Nat.lt_of_not_ge hle
    have hN : N = U 2 1 := by
      simpa [hNmin, Nat.min_eq_right (le_of_lt hlt)] using hNmin
    have hkilled : ((2 : Fin 3), (1 : Fin 4)) ∉
        supportOfNat (rowPathMoveNatPlus U N) := by
      rw [mem_supportOfNat_iff]
      simp [rowPathMoveNatPlus, hN]
    exact hkilled (hsubset h21mem)

theorem supportCardNat_rowPathMoveNatMinus_lt
    (U : NatMatrix) (P : Nat)
    (hpath : descentRowPathSupport ⊆ supportOfNat U)
    (_hPpos : 0 < P) (_h00 : P <= U 0 0) (_h11 : P <= U 1 1)
    (hPmin : P = Nat.min (U 0 0) (U 1 1)) :
    supportCardNat (rowPathMoveNatMinus U P) < supportCardNat U := by
  apply supportCardNat_lt_of_support_ssubset
  refine ⟨supportOfNat_rowPathMoveNatMinus_subset U P hpath, ?_⟩
  intro hsubset
  have h00mem : ((0 : Fin 3), (0 : Fin 4)) ∈ supportOfNat U :=
    hpath (by simp [descentRowPathSupport])
  have h11mem : ((1 : Fin 3), (1 : Fin 4)) ∈ supportOfNat U :=
    hpath (by simp [descentRowPathSupport])
  by_cases hle : U 0 0 <= U 1 1
  · have hP : P = U 0 0 := by simpa [hPmin, hle] using hPmin
    have hkilled : ((0 : Fin 3), (0 : Fin 4)) ∉
        supportOfNat (rowPathMoveNatMinus U P) := by
      rw [mem_supportOfNat_iff]
      simp [rowPathMoveNatMinus, hP]
    exact hkilled (hsubset h00mem)
  · have hlt : U 1 1 < U 0 0 := Nat.lt_of_not_ge hle
    have hP : P = U 1 1 := by
      simpa [hPmin, Nat.min_eq_right (le_of_lt hlt)] using hPmin
    have hkilled : ((1 : Fin 3), (1 : Fin 4)) ∉
        supportOfNat (rowPathMoveNatMinus U P) := by
      rw [mem_supportOfNat_iff]
      simp [rowPathMoveNatMinus, hP]
    exact hkilled (hsubset h11mem)

/-- A support containing the canonical row-oriented four-edge path descends. -/
theorem canonical_row_path_descent
    (U : NatMatrix)
    (hpath : descentRowPathSupport ⊆ supportOfNat U) :
    ∃ V : NatMatrix,
      matrixTotalNat V = matrixTotalNat U ∧
      matrixFNat V <= matrixFNat U ∧
      supportCardNat V < supportCardNat U := by
  have h00pos : 0 < U 0 0 := by
    rw [← mem_supportOfNat_iff U ((0 : Fin 3), (0 : Fin 4))]
    exact hpath (by simp [descentRowPathSupport])
  have h10pos : 0 < U 1 0 := by
    rw [← mem_supportOfNat_iff U ((1 : Fin 3), (0 : Fin 4))]
    exact hpath (by simp [descentRowPathSupport])
  have h11pos : 0 < U 1 1 := by
    rw [← mem_supportOfNat_iff U ((1 : Fin 3), (1 : Fin 4))]
    exact hpath (by simp [descentRowPathSupport])
  have h21pos : 0 < U 2 1 := by
    rw [← mem_supportOfNat_iff U ((2 : Fin 3), (1 : Fin 4))]
    exact hpath (by simp [descentRowPathSupport])
  let P : Nat := Nat.min (U 0 0) (U 1 1)
  let N : Nat := Nat.min (U 1 0) (U 2 1)
  have hPpos : 0 < P := by
    dsimp [P]
    exact lt_min h00pos h11pos
  have hNpos : 0 < N := by
    dsimp [N]
    exact lt_min h10pos h21pos
  have hP00 : P <= U 0 0 := by
    dsimp [P]
    exact Nat.min_le_left _ _
  have hP11 : P <= U 1 1 := by
    dsimp [P]
    exact Nat.min_le_right _ _
  have hN10 : N <= U 1 0 := by
    dsimp [N]
    exact Nat.min_le_left _ _
  have hN21 : N <= U 2 1 := by
    dsimp [N]
    exact Nat.min_le_right _ _
  have hend := matrixF_pathMove_endpoint_nonincreasing
    (matrixOfNat U) (P := (P : Rat)) (N := (N : Rat))
    (by positivity) (by positivity)
  rcases hend with hplus | hminus
  · refine ⟨rowPathMoveNatPlus U N, ?_, ?_, ?_⟩
    · exact matrixTotalNat_rowPathMoveNatPlus U N hN10 hN21
    · unfold matrixFNat
      rw [matrixOfNat_rowPathMoveNatPlus U N hN10 hN21]
      exact hplus
    · exact supportCardNat_rowPathMoveNatPlus_lt U N hpath hNpos hN10 hN21 rfl
  · refine ⟨rowPathMoveNatMinus U P, ?_, ?_, ?_⟩
    · exact matrixTotalNat_rowPathMoveNatMinus U P hP00 hP11
    · unfold matrixFNat
      rw [matrixOfNat_rowPathMoveNatMinus U P hP00 hP11]
      exact hminus
    · exact supportCardNat_rowPathMoveNatMinus_lt U P hpath hPpos hP00 hP11 rfl

/-- Canonical column-oriented four-edge path move on the path
`col 0 - row 0 - col 1 - row 1 - col 2`. -/
def colPathMove (U : Fin 3 → Fin 4 → Rat) (eps : Rat) : Fin 3 → Fin 4 → Rat :=
  fun i j =>
    if i = 0 ∧ j = 0 then U i j + eps else
    if i = 0 ∧ j = 1 then U i j - eps else
    if i = 1 ∧ j = 1 then U i j + eps else
    if i = 1 ∧ j = 2 then U i j - eps else
    U i j

theorem matrixF_colPathMove_sub
    (U : Fin 3 → Fin 4 → Rat) (eps : Rat) :
    matrixF (colPathMove U eps) - matrixF U =
      eps *
        (2 * colSum U 0 - 2 * colSum U 2 -
          U 0 0 + U 0 1 - U 1 1 + U 1 2) := by
  simp [matrixF, rowSum, colSum, colPathMove, Fin.sum_univ_three, Fin.sum_univ_four]
  ring

theorem matrixF_colPathMove_endpoint_nonincreasing
    (U : Fin 3 → Fin 4 → Rat) {P N : Rat}
    (hP : 0 <= P) (hN : 0 <= N) :
    matrixF (colPathMove U N) <= matrixF U ∨
      matrixF (colPathMove U (-P)) <= matrixF U := by
  let b :=
    2 * colSum U 0 - 2 * colSum U 2 -
      U 0 0 + U 0 1 - U 1 1 + U 1 2
  have hend := endpoint_quadratic_nonpos
    (a := (0 : Rat)) (b := b) (by norm_num) hP hN
  rcases hend with hend | hend
  · left
    rw [← sub_nonpos, matrixF_colPathMove_sub]
    nlinarith
  · right
    rw [← sub_nonpos, matrixF_colPathMove_sub]
    nlinarith

/-- Positive endpoint of the canonical column-oriented path move. -/
def colPathMoveNatPlus (U : NatMatrix) (N : Nat) : NatMatrix :=
  fun i j =>
    if i = 0 ∧ j = 0 then U i j + N else
    if i = 0 ∧ j = 1 then U i j - N else
    if i = 1 ∧ j = 1 then U i j + N else
    if i = 1 ∧ j = 2 then U i j - N else
    U i j

/-- Negative endpoint of the canonical column-oriented path move. -/
def colPathMoveNatMinus (U : NatMatrix) (P : Nat) : NatMatrix :=
  fun i j =>
    if i = 0 ∧ j = 0 then U i j - P else
    if i = 0 ∧ j = 1 then U i j + P else
    if i = 1 ∧ j = 1 then U i j - P else
    if i = 1 ∧ j = 2 then U i j + P else
    U i j

theorem matrixTotalNat_colPathMoveNatPlus
    (U : NatMatrix) (N : Nat)
    (h01 : N <= U 0 1) (h12 : N <= U 1 2) :
    matrixTotalNat (colPathMoveNatPlus U N) = matrixTotalNat U := by
  simp [matrixTotalNat, colPathMoveNatPlus, Fin.sum_univ_three, Fin.sum_univ_four]
  omega

theorem matrixTotalNat_colPathMoveNatMinus
    (U : NatMatrix) (P : Nat)
    (h00 : P <= U 0 0) (h11 : P <= U 1 1) :
    matrixTotalNat (colPathMoveNatMinus U P) = matrixTotalNat U := by
  simp [matrixTotalNat, colPathMoveNatMinus, Fin.sum_univ_three, Fin.sum_univ_four]
  omega

theorem matrixOfNat_colPathMoveNatPlus
    (U : NatMatrix) (N : Nat)
    (h01 : N <= U 0 1) (h12 : N <= U 1 2) :
    matrixOfNat (colPathMoveNatPlus U N) =
      colPathMove (matrixOfNat U) (N : Rat) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixOfNat, colPathMoveNatPlus, colPathMove, h01, h12, Nat.cast_sub]

theorem matrixOfNat_colPathMoveNatMinus
    (U : NatMatrix) (P : Nat)
    (h00 : P <= U 0 0) (h11 : P <= U 1 1) :
    matrixOfNat (colPathMoveNatMinus U P) =
      colPathMove (matrixOfNat U) (-(P : Rat)) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixOfNat, colPathMoveNatMinus, colPathMove, h00, h11, Nat.cast_sub] <;>
      ring

theorem supportOfNat_colPathMoveNatPlus_subset
    (U : NatMatrix) (N : Nat)
    (hpath : descentColPathSupport ⊆ supportOfNat U) :
    supportOfNat (colPathMoveNatPlus U N) ⊆ supportOfNat U := by
  have h00pos : 0 < U 0 0 := by
    rw [← mem_supportOfNat_iff U ((0 : Fin 3), (0 : Fin 4))]
    exact hpath (by simp [descentColPathSupport])
  have h11pos : 0 < U 1 1 := by
    rw [← mem_supportOfNat_iff U ((1 : Fin 3), (1 : Fin 4))]
    exact hpath (by simp [descentColPathSupport])
  intro e he
  rw [mem_supportOfNat_iff] at he ⊢
  rcases e with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [colPathMoveNatPlus] at he ⊢ <;> omega

theorem supportOfNat_colPathMoveNatMinus_subset
    (U : NatMatrix) (P : Nat)
    (hpath : descentColPathSupport ⊆ supportOfNat U) :
    supportOfNat (colPathMoveNatMinus U P) ⊆ supportOfNat U := by
  have h01pos : 0 < U 0 1 := by
    rw [← mem_supportOfNat_iff U ((0 : Fin 3), (1 : Fin 4))]
    exact hpath (by simp [descentColPathSupport])
  have h12pos : 0 < U 1 2 := by
    rw [← mem_supportOfNat_iff U ((1 : Fin 3), (2 : Fin 4))]
    exact hpath (by simp [descentColPathSupport])
  intro e he
  rw [mem_supportOfNat_iff] at he ⊢
  rcases e with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [colPathMoveNatMinus] at he ⊢ <;> omega

theorem supportCardNat_colPathMoveNatPlus_lt
    (U : NatMatrix) (N : Nat)
    (hpath : descentColPathSupport ⊆ supportOfNat U)
    (_hNpos : 0 < N) (_h01 : N <= U 0 1) (_h12 : N <= U 1 2)
    (hNmin : N = Nat.min (U 0 1) (U 1 2)) :
    supportCardNat (colPathMoveNatPlus U N) < supportCardNat U := by
  apply supportCardNat_lt_of_support_ssubset
  refine ⟨supportOfNat_colPathMoveNatPlus_subset U N hpath, ?_⟩
  intro hsubset
  have h01mem : ((0 : Fin 3), (1 : Fin 4)) ∈ supportOfNat U :=
    hpath (by simp [descentColPathSupport])
  have h12mem : ((1 : Fin 3), (2 : Fin 4)) ∈ supportOfNat U :=
    hpath (by simp [descentColPathSupport])
  by_cases hle : U 0 1 <= U 1 2
  · have hN : N = U 0 1 := by simpa [hNmin, hle] using hNmin
    have hkilled : ((0 : Fin 3), (1 : Fin 4)) ∉
        supportOfNat (colPathMoveNatPlus U N) := by
      rw [mem_supportOfNat_iff]
      simp [colPathMoveNatPlus, hN]
    exact hkilled (hsubset h01mem)
  · have hlt : U 1 2 < U 0 1 := Nat.lt_of_not_ge hle
    have hN : N = U 1 2 := by
      simpa [hNmin, Nat.min_eq_right (le_of_lt hlt)] using hNmin
    have hkilled : ((1 : Fin 3), (2 : Fin 4)) ∉
        supportOfNat (colPathMoveNatPlus U N) := by
      rw [mem_supportOfNat_iff]
      simp [colPathMoveNatPlus, hN]
    exact hkilled (hsubset h12mem)

theorem supportCardNat_colPathMoveNatMinus_lt
    (U : NatMatrix) (P : Nat)
    (hpath : descentColPathSupport ⊆ supportOfNat U)
    (_hPpos : 0 < P) (_h00 : P <= U 0 0) (_h11 : P <= U 1 1)
    (hPmin : P = Nat.min (U 0 0) (U 1 1)) :
    supportCardNat (colPathMoveNatMinus U P) < supportCardNat U := by
  apply supportCardNat_lt_of_support_ssubset
  refine ⟨supportOfNat_colPathMoveNatMinus_subset U P hpath, ?_⟩
  intro hsubset
  have h00mem : ((0 : Fin 3), (0 : Fin 4)) ∈ supportOfNat U :=
    hpath (by simp [descentColPathSupport])
  have h11mem : ((1 : Fin 3), (1 : Fin 4)) ∈ supportOfNat U :=
    hpath (by simp [descentColPathSupport])
  by_cases hle : U 0 0 <= U 1 1
  · have hP : P = U 0 0 := by simpa [hPmin, hle] using hPmin
    have hkilled : ((0 : Fin 3), (0 : Fin 4)) ∉
        supportOfNat (colPathMoveNatMinus U P) := by
      rw [mem_supportOfNat_iff]
      simp [colPathMoveNatMinus, hP]
    exact hkilled (hsubset h00mem)
  · have hlt : U 1 1 < U 0 0 := Nat.lt_of_not_ge hle
    have hP : P = U 1 1 := by
      simpa [hPmin, Nat.min_eq_right (le_of_lt hlt)] using hPmin
    have hkilled : ((1 : Fin 3), (1 : Fin 4)) ∉
        supportOfNat (colPathMoveNatMinus U P) := by
      rw [mem_supportOfNat_iff]
      simp [colPathMoveNatMinus, hP]
    exact hkilled (hsubset h11mem)

/-- A support containing the canonical column-oriented four-edge path descends. -/
theorem canonical_col_path_descent
    (U : NatMatrix)
    (hpath : descentColPathSupport ⊆ supportOfNat U) :
    ∃ V : NatMatrix,
      matrixTotalNat V = matrixTotalNat U ∧
      matrixFNat V <= matrixFNat U ∧
      supportCardNat V < supportCardNat U := by
  have h00pos : 0 < U 0 0 := by
    rw [← mem_supportOfNat_iff U ((0 : Fin 3), (0 : Fin 4))]
    exact hpath (by simp [descentColPathSupport])
  have h01pos : 0 < U 0 1 := by
    rw [← mem_supportOfNat_iff U ((0 : Fin 3), (1 : Fin 4))]
    exact hpath (by simp [descentColPathSupport])
  have h11pos : 0 < U 1 1 := by
    rw [← mem_supportOfNat_iff U ((1 : Fin 3), (1 : Fin 4))]
    exact hpath (by simp [descentColPathSupport])
  have h12pos : 0 < U 1 2 := by
    rw [← mem_supportOfNat_iff U ((1 : Fin 3), (2 : Fin 4))]
    exact hpath (by simp [descentColPathSupport])
  let P : Nat := Nat.min (U 0 0) (U 1 1)
  let N : Nat := Nat.min (U 0 1) (U 1 2)
  have hPpos : 0 < P := by
    dsimp [P]
    exact lt_min h00pos h11pos
  have hNpos : 0 < N := by
    dsimp [N]
    exact lt_min h01pos h12pos
  have hP00 : P <= U 0 0 := by
    dsimp [P]
    exact Nat.min_le_left _ _
  have hP11 : P <= U 1 1 := by
    dsimp [P]
    exact Nat.min_le_right _ _
  have hN01 : N <= U 0 1 := by
    dsimp [N]
    exact Nat.min_le_left _ _
  have hN12 : N <= U 1 2 := by
    dsimp [N]
    exact Nat.min_le_right _ _
  have hend := matrixF_colPathMove_endpoint_nonincreasing
    (matrixOfNat U) (P := (P : Rat)) (N := (N : Rat))
    (by positivity) (by positivity)
  rcases hend with hplus | hminus
  · refine ⟨colPathMoveNatPlus U N, ?_, ?_, ?_⟩
    · exact matrixTotalNat_colPathMoveNatPlus U N hN01 hN12
    · unfold matrixFNat
      rw [matrixOfNat_colPathMoveNatPlus U N hN01 hN12]
      exact hplus
    · exact supportCardNat_colPathMoveNatPlus_lt U N hpath hNpos hN01 hN12 rfl
  · refine ⟨colPathMoveNatMinus U P, ?_, ?_, ?_⟩
    · exact matrixTotalNat_colPathMoveNatMinus U P hP00 hP11
    · unfold matrixFNat
      rw [matrixOfNat_colPathMoveNatMinus U P hP00 hP11]
      exact hminus
    · exact supportCardNat_colPathMoveNatMinus_lt U P hpath hPpos hP00 hP11 rfl

theorem entry_eq_zero_of_support_subset
    (U : NatMatrix) {S : Finset MatrixEdge}
    (hsub : supportOfNat U ⊆ S) {i : Fin 3} {j : Fin 4}
    (h : (i, j) ∉ S) :
    U i j = 0 := by
  exact entry_eq_zero_of_not_mem_support U (fun hmem => h (hsub hmem))

/-- Delete the canonical double-star central edge and move its mass to the
row-side leaf. -/
def doubleStarMoveXNat (U : NatMatrix) : NatMatrix :=
  fun i j =>
    if i = 0 ∧ j = 1 then U i j + U 0 0 else
    if i = 0 ∧ j = 0 then 0 else
    U i j

/-- Delete the canonical double-star central edge and move its mass to the
column-side leaf. -/
def doubleStarMoveZNat (U : NatMatrix) : NatMatrix :=
  fun i j =>
    if i = 1 ∧ j = 0 then U i j + U 0 0 else
    if i = 0 ∧ j = 0 then 0 else
    U i j

theorem matrixTotalNat_doubleStarMoveXNat (U : NatMatrix) :
    matrixTotalNat (doubleStarMoveXNat U) = matrixTotalNat U := by
  simp [matrixTotalNat, doubleStarMoveXNat, Fin.sum_univ_three, Fin.sum_univ_four]
  omega

theorem matrixTotalNat_doubleStarMoveZNat (U : NatMatrix) :
    matrixTotalNat (doubleStarMoveZNat U) = matrixTotalNat U := by
  simp [matrixTotalNat, doubleStarMoveZNat, Fin.sum_univ_three, Fin.sum_univ_four]
  omega

theorem supportOfNat_doubleStarMoveXNat_subset
    (U : NatMatrix)
    (hcore : descentDoubleStarCore ⊆ supportOfNat U) :
    supportOfNat (doubleStarMoveXNat U) ⊆ supportOfNat U := by
  have h01pos : 0 < U 0 1 := by
    rw [← mem_supportOfNat_iff U ((0 : Fin 3), (1 : Fin 4))]
    exact hcore (by simp [descentDoubleStarCore])
  intro e he
  rw [mem_supportOfNat_iff] at he ⊢
  rcases e with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [doubleStarMoveXNat] at he ⊢ <;> omega

theorem supportOfNat_doubleStarMoveZNat_subset
    (U : NatMatrix)
    (hcore : descentDoubleStarCore ⊆ supportOfNat U) :
    supportOfNat (doubleStarMoveZNat U) ⊆ supportOfNat U := by
  have h10pos : 0 < U 1 0 := by
    rw [← mem_supportOfNat_iff U ((1 : Fin 3), (0 : Fin 4))]
    exact hcore (by simp [descentDoubleStarCore])
  intro e he
  rw [mem_supportOfNat_iff] at he ⊢
  rcases e with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [doubleStarMoveZNat] at he ⊢ <;> omega

theorem supportCardNat_doubleStarMoveXNat_lt
    (U : NatMatrix)
    (hcore : descentDoubleStarCore ⊆ supportOfNat U) :
    supportCardNat (doubleStarMoveXNat U) < supportCardNat U := by
  apply supportCardNat_lt_of_support_ssubset
  refine ⟨supportOfNat_doubleStarMoveXNat_subset U hcore, ?_⟩
  intro hsubset
  have h00mem : ((0 : Fin 3), (0 : Fin 4)) ∈ supportOfNat U :=
    hcore (by simp [descentDoubleStarCore])
  have hkilled : ((0 : Fin 3), (0 : Fin 4)) ∉
      supportOfNat (doubleStarMoveXNat U) := by
    rw [mem_supportOfNat_iff]
    simp [doubleStarMoveXNat]
  exact hkilled (hsubset h00mem)

theorem supportCardNat_doubleStarMoveZNat_lt
    (U : NatMatrix)
    (hcore : descentDoubleStarCore ⊆ supportOfNat U) :
    supportCardNat (doubleStarMoveZNat U) < supportCardNat U := by
  apply supportCardNat_lt_of_support_ssubset
  refine ⟨supportOfNat_doubleStarMoveZNat_subset U hcore, ?_⟩
  intro hsubset
  have h00mem : ((0 : Fin 3), (0 : Fin 4)) ∈ supportOfNat U :=
    hcore (by simp [descentDoubleStarCore])
  have hkilled : ((0 : Fin 3), (0 : Fin 4)) ∉
      supportOfNat (doubleStarMoveZNat U) := by
    rw [mem_supportOfNat_iff]
    simp [doubleStarMoveZNat]
  exact hkilled (hsubset h00mem)

theorem matrixFNat_doubleStarMoveX_sub
    (U : NatMatrix)
    (h11 : U 1 1 = 0) (h12 : U 1 2 = 0)
    (h13 : U 1 3 = 0) (h21 : U 2 1 = 0) :
    matrixFNat U - matrixFNat (doubleStarMoveXNat U) =
      (U 0 0 : Rat) * (2 * (U 2 0 : Rat) + 2 * (U 1 0 : Rat) - (U 0 1 : Rat)) := by
  simp [matrixFNat, matrixOfNat, matrixF, rowSum, colSum, doubleStarMoveXNat,
    Fin.sum_univ_three, Fin.sum_univ_four, h11, h12, h13, h21]
  ring

theorem matrixFNat_doubleStarMoveZ_sub
    (U : NatMatrix)
    (h11 : U 1 1 = 0) (h12 : U 1 2 = 0)
    (h13 : U 1 3 = 0) (h21 : U 2 1 = 0) :
    matrixFNat U - matrixFNat (doubleStarMoveZNat U) =
      (U 0 0 : Rat) *
        (2 * ((U 0 2 : Rat) + (U 0 3 : Rat)) + 2 * (U 0 1 : Rat) - (U 1 0 : Rat)) := by
  simp [matrixFNat, matrixOfNat, matrixF, rowSum, colSum, doubleStarMoveZNat,
    Fin.sum_univ_three, Fin.sum_univ_four, h11, h12, h13, h21]
  ring

/-- A support in the canonical double-star envelope has a one-step descent. -/
theorem canonical_doubleStar_descent
    (U : NatMatrix)
    (hcore : descentDoubleStarCore ⊆ supportOfNat U)
    (henv : supportOfNat U ⊆ descentDoubleStarSupport) :
    ∃ V : NatMatrix,
      matrixTotalNat V = matrixTotalNat U ∧
      matrixFNat V <= matrixFNat U ∧
      supportCardNat V < supportCardNat U := by
  have h11 : U 1 1 = 0 := entry_eq_zero_of_support_subset U henv
    (by simp [descentDoubleStarSupport])
  have h12 : U 1 2 = 0 := entry_eq_zero_of_support_subset U henv
    (by simp [descentDoubleStarSupport])
  have h13 : U 1 3 = 0 := entry_eq_zero_of_support_subset U henv
    (by simp [descentDoubleStarSupport])
  have h21 : U 2 1 = 0 := entry_eq_zero_of_support_subset U henv
    (by simp [descentDoubleStarSupport])
  have hx0 : 0 <= (U 0 1 : Rat) := by positivity
  have hy0 : 0 <= (U 0 0 : Rat) := by positivity
  have hz0 : 0 <= (U 1 0 : Rat) := by positivity
  have hA : 0 <= (U 0 2 : Rat) + (U 0 3 : Rat) := by positivity
  have hB : 0 <= (U 2 0 : Rat) := by positivity
  rcases doubleStar_coeff_nonneg
      (A := (U 0 2 : Rat) + (U 0 3 : Rat))
      (B := (U 2 0 : Rat))
      (x := (U 0 1 : Rat))
      (z := (U 1 0 : Rat)) hA hB hx0 hz0 with hcoef | hcoef
  · refine ⟨doubleStarMoveXNat U, matrixTotalNat_doubleStarMoveXNat U, ?_, ?_⟩
    · rw [← sub_nonneg, matrixFNat_doubleStarMoveX_sub U h11 h12 h13 h21]
      exact mul_nonneg hy0 hcoef
    · exact supportCardNat_doubleStarMoveXNat_lt U hcore
  · refine ⟨doubleStarMoveZNat U, matrixTotalNat_doubleStarMoveZNat U, ?_, ?_⟩
    · rw [← sub_nonneg, matrixFNat_doubleStarMoveZ_sub U h11 h12 h13 h21]
      exact mul_nonneg hy0 hcoef
    · exact supportCardNat_doubleStarMoveZNat_lt U hcore

theorem descent_of_relabel_symm
    (er : Fin 3 ≃ Fin 3) (ec : Fin 4 ≃ Fin 4)
    (U : NatMatrix)
    (h :
      ∃ W : NatMatrix,
        matrixTotalNat W = matrixTotalNat (relabelNatMatrix er.symm ec.symm U) ∧
        matrixFNat W <= matrixFNat (relabelNatMatrix er.symm ec.symm U) ∧
        supportCardNat W < supportCardNat (relabelNatMatrix er.symm ec.symm U)) :
    ∃ V : NatMatrix,
      matrixTotalNat V = matrixTotalNat U ∧
      matrixFNat V <= matrixFNat U ∧
      supportCardNat V < supportCardNat U := by
  rcases h with ⟨W, htotal, hF, hcard⟩
  refine ⟨relabelNatMatrix er ec W, ?_, ?_, ?_⟩
  · rw [matrixTotalNat_relabelNatMatrix, htotal, matrixTotalNat_relabelNatMatrix]
  · rw [matrixFNat_relabelNatMatrix]
    rw [matrixFNat_relabelNatMatrix] at hF
    exact hF
  · rw [supportCardNat_relabelNatMatrix]
    rw [supportCardNat_relabelNatMatrix] at hcard
    exact hcard

/-- The one-step support descent lemma from Section 5. -/
theorem support_descent_step_proven : SupportDescentStepStatement := by
  intro U hnotstar
  rcases nonstar_support_has_descent_shape (supportOfNat U) hnotstar with
    hcycle | hrow | hcol | hdouble
  · rcases hcycle with ⟨er, ec, hcycle⟩
    apply descent_of_relabel_symm er ec U
    apply canonical_cycle_descent
    rw [supportOfNat_relabelNatMatrix]
    simpa using hcycle
  · rcases hrow with ⟨er, ec, hrow⟩
    apply descent_of_relabel_symm er ec U
    apply canonical_row_path_descent
    rw [supportOfNat_relabelNatMatrix]
    simpa using hrow
  · rcases hcol with ⟨er, ec, hcol⟩
    apply descent_of_relabel_symm er ec U
    apply canonical_col_path_descent
    rw [supportOfNat_relabelNatMatrix]
    simpa using hcol
  · rcases hdouble with ⟨er, ec, hcore, henv⟩
    apply descent_of_relabel_symm er ec U
    apply canonical_doubleStar_descent
    · rw [supportOfNat_relabelNatMatrix]
      simpa using hcore
    · rw [supportOfNat_relabelNatMatrix]
      simpa using henv

/-- The full matrix theorem, with support descent and star-forest minima both
proved. -/
theorem matrix_theorem_proven : MatrixTheoremStatement :=
  matrix_theorem_of_descent_step_and_star_forest
    support_descent_step_proven starForestMinimum_proven

end Lollipop
