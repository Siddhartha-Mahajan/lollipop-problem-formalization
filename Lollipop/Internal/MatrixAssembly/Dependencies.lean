import Lollipop.Internal.Matrix.Basic
import Lollipop.Internal.Model.Proof

/-!
Formal Theorem 1 dependency layer.

This folder keeps the manuscript-facing Theorem 1 proof separate from the
earlier certificate layer.  The main improvement here is that quotient
certificates carry the actual integer `3 x 4` matrix from Section 5.  Once
`MatrixTheoremStatement` is proved, the per-certificate matrix-bound field of
`DirectMatrixCertifiedQuotient` is generated automatically.
-/

namespace Lollipop
namespace TheoremOneFormal

open BigOperators

/-- A direct quotient certificate whose matrix is the integer matrix appearing
in Section 5. -/
structure NatMatrixCertifiedQuotient extends QuotientData where
  nNat : ℕ
  n_eq : n = (nNat : ℚ)
  U : NatMatrix
  matrix_total : matrixTotalNat U = nNat
  a_lower :
    aOnlyE ≥ ((∑ i : Fin 3, (rowSum (matrixOfNat U) i)^2) - Q) / 2
  b_lower :
    bOnlyD ≥ ((∑ j : Fin 4, (colSum (matrixOfNat U) j)^2) - Q) / 2
  Q_le_entrySq : Q ≤ ∑ i : Fin 3, ∑ j : Fin 4, (matrixOfNat U i j)^2

/-- The matrix theorem supplies the direct rational matrix certificate. -/
def NatMatrixCertifiedQuotient.toDirectMatrixCertifiedQuotient
    (hMatrix : MatrixTheoremStatement)
    (q : NatMatrixCertifiedQuotient) : DirectMatrixCertifiedQuotient where
  n := q.n
  Q := q.Q
  aOnlyE := q.aOnlyE
  bOnlyD := q.bOnlyD
  sigma := q.sigma
  nNat := q.nNat
  n_eq := q.n_eq
  U := matrixOfNat q.U
  a_lower := q.a_lower
  b_lower := q.b_lower
  Q_le_entrySq := q.Q_le_entrySq
  matrix_bound := by
    have h := hMatrix q.U
    unfold matrixFNat at h
    rw [q.matrix_total] at h
    exact h

@[simp]
theorem NatMatrixCertifiedQuotient.toDirect_toQuotientData
    (hMatrix : MatrixTheoremStatement)
    (q : NatMatrixCertifiedQuotient) :
    (q.toDirectMatrixCertifiedQuotient hMatrix).toQuotientData =
      q.toQuotientData := by
  rfl

/-- A colored pair certificate whose quotient matrix is integral, so the
Section 5 theorem discharges its matrix bound. -/
structure NatMatrixCertifiedColoredPair where
  nNat : ℕ
  sigma : ℚ
  quotient : NatMatrixCertifiedQuotient
  quotient_identity : QuotientIdentity quotient.toQuotientData
  quotient_nNat : quotient.nNat = nNat
  quotient_preserves_sigma : quotient.sigma ≥ sigma

/-- Convert an integral-matrix colored-pair certificate to the direct
certificate used by the existing upper-bound chain. -/
def NatMatrixCertifiedColoredPair.toDirectCertifiedColoredPair
    (hMatrix : MatrixTheoremStatement)
    (p : NatMatrixCertifiedColoredPair) : DirectCertifiedColoredPair where
  nNat := p.nNat
  sigma := p.sigma
  quotient := p.quotient.toDirectMatrixCertifiedQuotient hMatrix
  quotient_identity := by
    simpa using p.quotient_identity
  quotient_nNat := p.quotient_nNat
  quotient_preserves_sigma := p.quotient_preserves_sigma

/-- Colored Turan bound from an integral matrix quotient and the matrix
theorem. -/
theorem nat_matrix_certified_colored_turan_bound
    (hMatrix : MatrixTheoremStatement)
    (p : NatMatrixCertifiedColoredPair) :
    p.sigma ≤ concreteS p.nNat := by
  exact direct_certified_colored_turan_bound
    (p.toDirectCertifiedColoredPair hMatrix)

/-- Compact lollipop upper certificate whose colored-pair quotient matrix is
integral. -/
structure NatMatrixCertifiedLollipopUpper where
  nNat : ℕ
  crossings : ℚ
  regions : ℚ
  pair : NatMatrixCertifiedColoredPair
  pair_nNat : pair.nNat = nNat
  crossing_reduction :
    crossings ≤ 4 * ((nNat : ℚ) * ((nNat : ℚ) - 1) / 2) + pair.sigma
  regions_eq : regions = crossings + (nNat : ℚ) + 1

/-- Convert an integral-matrix upper certificate to the existing direct
certificate once Section 5 is available. -/
def NatMatrixCertifiedLollipopUpper.toDirectCertifiedLollipopUpper
    (hMatrix : MatrixTheoremStatement)
    (L : NatMatrixCertifiedLollipopUpper) : DirectCertifiedLollipopUpper where
  nNat := L.nNat
  crossings := L.crossings
  regions := L.regions
  pair := L.pair.toDirectCertifiedColoredPair hMatrix
  pair_nNat := L.pair_nNat
  crossing_reduction := L.crossing_reduction
  regions_eq := L.regions_eq

/-- End-to-end upper bound from a compact integral-matrix upper certificate. -/
theorem nat_matrix_certified_lollipop_upper_bound
    (hMatrix : MatrixTheoremStatement)
    (L : NatMatrixCertifiedLollipopUpper) :
    L.regions ≤ candidateRegions L.nNat := by
  exact direct_certified_lollipop_upper_bound
    (L.toDirectCertifiedLollipopUpper hMatrix)

/-- End-to-end upper bound in the displayed `4 * n.choose 2` form. -/
theorem nat_matrix_certified_lollipop_upper_bound_choose
    (hMatrix : MatrixTheoremStatement)
    (L : NatMatrixCertifiedLollipopUpper) :
    L.regions ≤ candidateRegionsChoose L.nNat := by
  simpa [candidateRegionsChoose_eq_candidateRegions] using
    nat_matrix_certified_lollipop_upper_bound hMatrix L

/-- Pairwise lollipop upper certificate with an integral matrix quotient. -/
structure PairwiseNatMatrixCertifiedLollipopUpper where
  nNat : ℕ
  crossings : ℚ
  regions : ℚ
  cross : Fin nNat → Fin nNat → ℚ
  score : Fin nNat → Fin nNat → ℚ
  pair : NatMatrixCertifiedColoredPair
  pair_nNat : pair.nNat = nNat
  crossings_le_pairSum : crossings ≤ pairSum nNat cross
  pointwise_crossing_bound :
    ∀ i j : Fin nNat, i < j → cross i j ≤ 4 + score i j
  score_sum_le_sigma : pairSum nNat score ≤ pair.sigma
  regions_eq : regions = crossings + (nNat : ℚ) + 1

/-- Pairwise estimates imply the compact crossing reduction. -/
theorem pairwise_nat_matrix_certified_lollipop_crossing_reduction_choose
    (L : PairwiseNatMatrixCertifiedLollipopUpper) :
    L.crossings ≤ 4 * ((L.nNat.choose 2 : ℕ) : ℚ) + L.pair.sigma := by
  have hpair :=
    pairSum_crossing_le_choose_plus_score L.cross L.score L.pointwise_crossing_bound
  linarith [L.crossings_le_pairSum, hpair, L.score_sum_le_sigma]

/-- Product-form crossing reduction for pairwise integral-matrix
certificates. -/
theorem pairwise_nat_matrix_certified_lollipop_crossing_reduction
    (L : PairwiseNatMatrixCertifiedLollipopUpper) :
    L.crossings ≤
      4 * ((L.nNat : ℚ) * ((L.nNat : ℚ) - 1) / 2) + L.pair.sigma := by
  have h := pairwise_nat_matrix_certified_lollipop_crossing_reduction_choose L
  rw [Nat.cast_choose_two] at h
  exact h

/-- Convert a pairwise integral-matrix upper certificate to the compact one. -/
def PairwiseNatMatrixCertifiedLollipopUpper.toNatMatrixCertifiedLollipopUpper
    (L : PairwiseNatMatrixCertifiedLollipopUpper) :
    NatMatrixCertifiedLollipopUpper where
  nNat := L.nNat
  crossings := L.crossings
  regions := L.regions
  pair := L.pair
  pair_nNat := L.pair_nNat
  crossing_reduction :=
    pairwise_nat_matrix_certified_lollipop_crossing_reduction L
  regions_eq := L.regions_eq

/-- End-to-end upper bound from pairwise integral-matrix data. -/
theorem pairwise_nat_matrix_certified_lollipop_upper_bound
    (hMatrix : MatrixTheoremStatement)
    (L : PairwiseNatMatrixCertifiedLollipopUpper) :
    L.regions ≤ candidateRegions L.nNat := by
  exact nat_matrix_certified_lollipop_upper_bound hMatrix
    L.toNatMatrixCertifiedLollipopUpper

/-- End-to-end upper bound from pairwise integral-matrix data in the displayed
`4 * n.choose 2` form. -/
theorem pairwise_nat_matrix_certified_lollipop_upper_bound_choose
    (hMatrix : MatrixTheoremStatement)
    (L : PairwiseNatMatrixCertifiedLollipopUpper) :
    L.regions ≤ candidateRegionsChoose L.nNat := by
  simpa [candidateRegionsChoose_eq_candidateRegions] using
    pairwise_nat_matrix_certified_lollipop_upper_bound hMatrix L

/-- Exactness theorem from pairwise integral-matrix upper certificates, the
Section 5 matrix theorem, and lower realization. -/
theorem candidateRegionsChoose_isGreatest_of_pairwise_nat_matrix_certified_bounds
    (hMatrix : MatrixTheoremStatement)
    {Arrangement : Type*} (region : Arrangement → ℚ) (n : ℕ)
    (upperCert :
      ∀ A : Arrangement,
        ∃ L : PairwiseNatMatrixCertifiedLollipopUpper,
          L.nNat = n ∧ L.regions = region A)
    (lowerRealization : LowerRealization Arrangement region n) :
    IsGreatest (Set.range region) (candidateRegionsChoose n) := by
  rw [candidateRegionsChoose_eq_candidateRegions]
  apply candidateRegions_isGreatest_of_direct_certified_bounds region n
  · intro A
    rcases upperCert A with ⟨L, hLn, hLreg⟩
    exact ⟨L.toNatMatrixCertifiedLollipopUpper.toDirectCertifiedLollipopUpper hMatrix,
      hLn, hLreg⟩
  · exact lowerRealization

end TheoremOneFormal
end Lollipop
