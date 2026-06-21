import Lollipop.Internal.Algebra
import Lollipop.Internal.Blocker
import Lollipop.Internal.Formula
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
Certified end-to-end dependency chain for the lollipop upper bound.

This file contains no global proof axioms.  Instead, the still-large external
or global ingredients are represented as fields of certificate structures.
Given those certificates, Lean checks the full algebraic implication to the
concrete finite formula `concreteS`.
-/

namespace Lollipop

/-- Abstract record for the quotient delivered by colored Zykov
symmetrization.  The fields are the quantities used in the blocker argument. -/
structure QuotientData where
  n : ℚ
  Q : ℚ
  aOnlyE : ℚ
  bOnlyD : ℚ
  sigma : ℚ

/-- The quotient identity for the colored objective. -/
def QuotientIdentity (q : QuotientData) : Prop :=
  q.sigma = (3 / 2 : ℚ) * q.n^2 -
    ((3 / 2 : ℚ) * q.Q + 2*q.aOnlyE + 2*q.bOnlyD)

/-- A quotient whose blocker/matrix certificate is stated against the concrete
finite definition of `M(n)`. -/
structure ConcreteCertifiedQuotient extends QuotientData where
  nNat : ℕ
  n_eq : n = (nNat : ℚ)
  rho3 : ℚ
  rho4 : ℚ
  entrySq : ℚ
  a_lower : aOnlyE ≥ (rho3 - Q) / 2
  b_lower : bOnlyD ≥ (rho4 - Q) / 2
  Q_le_entrySq : Q ≤ entrySq
  matrix_bound : partitionMatrixSide rho3 rho4 entrySq ≥ concreteM nNat

/-- Checked blocker conclusion for a concrete certified quotient. -/
theorem concrete_certified_weighted_blocker (q : ConcreteCertifiedQuotient) :
    (3 / 2 : ℚ) * q.Q + 2*q.aOnlyE + 2*q.bOnlyD ≥ concreteM q.nNat := by
  exact blocker_cost_ge_M q.a_lower q.b_lower q.Q_le_entrySq q.matrix_bound

/-- The quotient colored Turan bound against the concrete four-cluster
extremum `concreteS`. -/
theorem concrete_certified_quotient_sigma_le_concreteS
    (q : ConcreteCertifiedQuotient)
    (hid : QuotientIdentity q.toQuotientData) :
    q.sigma ≤ concreteS q.nNat := by
  have hblock := concrete_certified_weighted_blocker q
  have hS := concreteS_eq_concreteM q.nNat
  rw [← q.n_eq] at hS
  exact sigma_le_from_blocker hid hblock hS

/-- A concrete quotient certificate carrying the actual `3 x 4` matrix from
the intersection of the 3- and 4-partitions. -/
structure ConcreteMatrixCertifiedQuotient extends QuotientData where
  nNat : ℕ
  n_eq : n = (nNat : ℚ)
  rho3 : ℚ
  rho4 : ℚ
  entrySq : ℚ
  U : Fin 3 → Fin 4 → ℚ
  a_lower : aOnlyE ≥ (rho3 - Q) / 2
  b_lower : bOnlyD ≥ (rho4 - Q) / 2
  Q_le_entrySq : Q ≤ entrySq
  rho3_eq : rho3 = ∑ i : Fin 3, (rowSum U i)^2
  rho4_eq : rho4 = ∑ j : Fin 4, (colSum U j)^2
  entrySq_eq : entrySq = ∑ i : Fin 3, ∑ j : Fin 4, (U i j)^2
  matrix_bound : matrixF U ≥ concreteM nNat

/-- Checked blocker conclusion for a concrete quotient carrying an explicit
intersection matrix. -/
theorem concrete_matrix_certified_weighted_blocker
    (q : ConcreteMatrixCertifiedQuotient) :
    (3 / 2 : ℚ) * q.Q + 2*q.aOnlyE + 2*q.bOnlyD ≥ concreteM q.nNat := by
  exact blocker_cost_ge_of_matrixF_bound q.U q.a_lower q.b_lower q.Q_le_entrySq
    q.rho3_eq q.rho4_eq q.entrySq_eq q.matrix_bound

/-- The quotient colored Turan bound from an explicit matrix certificate. -/
theorem concrete_matrix_certified_quotient_sigma_le_concreteS
    (q : ConcreteMatrixCertifiedQuotient)
    (hid : QuotientIdentity q.toQuotientData) :
    q.sigma ≤ concreteS q.nNat := by
  have hblock := concrete_matrix_certified_weighted_blocker q
  have hS := concreteS_eq_concreteM q.nNat
  rw [← q.n_eq] at hS
  exact sigma_le_from_blocker hid hblock hS

/-- A leaner concrete quotient certificate: the row-square, column-square, and
entry-square quantities are computed directly from the matrix `U`. -/
structure DirectMatrixCertifiedQuotient extends QuotientData where
  nNat : ℕ
  n_eq : n = (nNat : ℚ)
  U : Fin 3 → Fin 4 → ℚ
  a_lower :
    aOnlyE ≥ ((∑ i : Fin 3, (rowSum U i)^2) - Q) / 2
  b_lower :
    bOnlyD ≥ ((∑ j : Fin 4, (colSum U j)^2) - Q) / 2
  Q_le_entrySq : Q ≤ ∑ i : Fin 3, ∑ j : Fin 4, (U i j)^2
  matrix_bound : matrixF U ≥ concreteM nNat

/-- Checked blocker conclusion for a direct matrix certificate. -/
theorem direct_matrix_certified_weighted_blocker
    (q : DirectMatrixCertifiedQuotient) :
    (3 / 2 : ℚ) * q.Q + 2*q.aOnlyE + 2*q.bOnlyD ≥ concreteM q.nNat := by
  exact blocker_cost_ge_of_matrixF_bound q.U q.a_lower q.b_lower q.Q_le_entrySq
    rfl rfl rfl q.matrix_bound

/-- The quotient colored Turan bound from a direct matrix certificate. -/
theorem direct_matrix_certified_quotient_sigma_le_concreteS
    (q : DirectMatrixCertifiedQuotient)
    (hid : QuotientIdentity q.toQuotientData) :
    q.sigma ≤ concreteS q.nNat := by
  have hblock := direct_matrix_certified_weighted_blocker q
  have hS := concreteS_eq_concreteM q.nNat
  rw [← q.n_eq] at hS
  exact sigma_le_from_blocker hid hblock hS

/-- A certified colored pair: this packages the output of colored Zykov
symmetrization, weighted Turan, partition intersection, and the matrix theorem
as explicit data. -/
structure CertifiedColoredPair where
  nNat : ℕ
  sigma : ℚ
  quotient : ConcreteMatrixCertifiedQuotient
  quotient_identity : QuotientIdentity quotient.toQuotientData
  quotient_nNat : quotient.nNat = nNat
  quotient_preserves_sigma : quotient.sigma ≥ sigma

/-- Colored Turan bound for a certified colored pair. -/
theorem certified_colored_turan_bound (p : CertifiedColoredPair) :
    p.sigma ≤ concreteS p.nNat := by
  have hq :=
    concrete_matrix_certified_quotient_sigma_le_concreteS p.quotient p.quotient_identity
  have hsig := p.quotient_preserves_sigma
  rw [p.quotient_nNat] at hq
  linarith

/-- Certified colored pair using the direct matrix quotient certificate. -/
structure DirectCertifiedColoredPair where
  nNat : ℕ
  sigma : ℚ
  quotient : DirectMatrixCertifiedQuotient
  quotient_identity : QuotientIdentity quotient.toQuotientData
  quotient_nNat : quotient.nNat = nNat
  quotient_preserves_sigma : quotient.sigma ≥ sigma

/-- Colored Turan bound for a direct certified colored pair. -/
theorem direct_certified_colored_turan_bound (p : DirectCertifiedColoredPair) :
    p.sigma ≤ concreteS p.nNat := by
  have hq :=
    direct_matrix_certified_quotient_sigma_le_concreteS p.quotient p.quotient_identity
  have hsig := p.quotient_preserves_sigma
  rw [p.quotient_nNat] at hq
  linarith

/-- The candidate region count from the manuscript formula. -/
def candidateRegions (n : ℕ) : ℚ :=
  4 * ((n : ℚ) * ((n : ℚ) - 1) / 2) + concreteS n + (n : ℚ) + 1

/-- The same candidate region count written with `Nat.choose`, matching the
manuscript's `4 binom(n,2) + S(n) + n + 1`. -/
def candidateRegionsChoose (n : ℕ) : ℚ :=
  4 * ((n.choose 2 : ℕ) : ℚ) + concreteS n + (n : ℚ) + 1

/-- The two displayed forms of the candidate formula agree. -/
theorem candidateRegionsChoose_eq_candidateRegions (n : ℕ) :
    candidateRegionsChoose n = candidateRegions n := by
  unfold candidateRegionsChoose candidateRegions
  rw [Nat.cast_choose_two]

/-- A certified lollipop arrangement for the upper-bound direction.  The
geometric pairwise estimates and the construction of the colored pair are
represented by the `crossing_reduction` field. -/
structure CertifiedLollipopUpper where
  nNat : ℕ
  crossings : ℚ
  regions : ℚ
  pair : CertifiedColoredPair
  pair_nNat : pair.nNat = nNat
  crossing_reduction :
    crossings ≤ 4 * ((nNat : ℚ) * ((nNat : ℚ) - 1) / 2) + pair.sigma
  regions_eq : regions = crossings + (nNat : ℚ) + 1

/-- End-to-end certified upper bound. -/
theorem certified_lollipop_upper_bound (L : CertifiedLollipopUpper) :
    L.regions ≤ candidateRegions L.nNat := by
  have ht := certified_colored_turan_bound L.pair
  rw [L.pair_nNat] at ht
  have hc := L.crossing_reduction
  unfold candidateRegions
  rw [L.regions_eq]
  linarith

/-- Upper-bound certificate using the direct colored-pair certificate. -/
structure DirectCertifiedLollipopUpper where
  nNat : ℕ
  crossings : ℚ
  regions : ℚ
  pair : DirectCertifiedColoredPair
  pair_nNat : pair.nNat = nNat
  crossing_reduction :
    crossings ≤ 4 * ((nNat : ℚ) * ((nNat : ℚ) - 1) / 2) + pair.sigma
  regions_eq : regions = crossings + (nNat : ℚ) + 1

/-- End-to-end certified upper bound using direct matrix certificates. -/
theorem direct_certified_lollipop_upper_bound (L : DirectCertifiedLollipopUpper) :
    L.regions ≤ candidateRegions L.nNat := by
  have ht := direct_certified_colored_turan_bound L.pair
  rw [L.pair_nNat] at ht
  have hc := L.crossing_reduction
  unfold candidateRegions
  rw [L.regions_eq]
  linarith

/-- Upper and lower certificates imply that the candidate value is the greatest
attained region count in the given class of arrangements. -/
theorem candidateRegions_isGreatest
    {Arrangement : Type*} (region : Arrangement → ℚ) (n : ℕ)
    (upper : ∀ A : Arrangement, region A ≤ candidateRegions n)
    (lower : ∃ A : Arrangement, region A = candidateRegions n) :
    IsGreatest (Set.range region) (candidateRegions n) := by
  constructor
  · rcases lower with ⟨A, hA⟩
    exact ⟨A, hA⟩
  · intro y hy
    rcases hy with ⟨A, rfl⟩
    exact upper A

end Lollipop
