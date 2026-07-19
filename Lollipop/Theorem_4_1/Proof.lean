import Lollipop.Lemma_5_1.Proof
import Lollipop.Lemma_6_1.Proof
import Lollipop.Lemma_6_2.Proof
import Lollipop.Lemma_7_2.Proof
import Lollipop.Lemma_7_3.Proof
import Lollipop.Theorem_7_1.Proof
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic
import Lollipop.Theorem_4_1.Statement

/-!
This is the substantive proof compilation unit for `Theorem_4_1`.
All project proof components used below are integrated here or imported
directly from another manuscript-numbered `Proof.lean` file.
-/

/-!
Proof component 1: `Core`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

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

/-!
Proof component 2: `Model.Statement`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Top-level statements for Theorem 1.

Mathlib's `IsGreatest` is the right shape for a maximum theorem over an
abstract arrangement class: it simultaneously states that the displayed value
is attained and that every arrangement has region count at most that value.
This avoids introducing a noncomputable supremum over `ℚ`.
-/

namespace Lollipop
namespace TheoremOne

universe u

/-- An abstract family of lollipop arrangements, indexed by the number of
lollipops, together with its region-count function. -/
structure ProblemFamily where
  Arrangement : ℕ → Type u
  region : (n : ℕ) → Arrangement n → ℚ

/-- The set of region counts attained by arrangements of size `n`. -/
def regionSet (P : ProblemFamily.{u}) (n : ℕ) : Set ℚ :=
  Set.range (P.region n)

/-- Theorem 1 in maximum form:
`4 * n.choose 2 + S(n) + n + 1` is the greatest attained region count. -/
def MaximumStatement (P : ProblemFamily.{u}) : Prop :=
  ∀ n : ℕ, IsGreatest (regionSet P n) (candidateRegionsChoose n)

/-- A problem family with a named maximum-count function `aLop`.  The field
`aLop_spec` is the mathematical meaning of that name: it is the greatest
attained region count. -/
structure MaxProblemFamily where
  Arrangement : ℕ → Type u
  region : (n : ℕ) → Arrangement n → ℚ
  aLop : ℕ → ℚ
  aLop_spec : ∀ n : ℕ, IsGreatest (Set.range (region n)) (aLop n)

/-- Forget the named maximum-count function. -/
def MaxProblemFamily.toProblemFamily (P : MaxProblemFamily.{u}) : ProblemFamily.{u} where
  Arrangement := P.Arrangement
  region := P.region

/-- Theorem 1 in formula form for a named maximum-count function. -/
def FormulaStatement (P : MaxProblemFamily.{u}) : Prop :=
  ∀ n : ℕ, P.aLop n = candidateRegionsChoose n

/-- If the candidate value is greatest, then any named maximum-count function
with an `IsGreatest` specification is equal to the candidate formula. -/
theorem formulaStatement_of_maximumStatement
    (P : MaxProblemFamily.{u})
    (hmax : MaximumStatement P.toProblemFamily) :
    FormulaStatement P := by
  intro n
  exact (P.aLop_spec n).unique (hmax n)

end TheoremOne
end Lollipop

/-!
Proof component 3: `Lower`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Lower-construction algebra for the lollipop formula.

The geometric assertion that Karlsson's four-lollipop configuration can be
blown up is represented by a realization hypothesis.  This file checks the
algebra: any realization of a quadruple attaining `concreteS n` has exactly
the candidate number of regions, and since `concreteS n` is a finite maximum
such a quadruple exists.
-/

namespace Lollipop

/-- Rational binomial coefficient `x choose 2`. -/
def binomTwoQ (x : ℚ) : ℚ :=
  x * (x - 1) / 2

/-- Crossing count of the four-cluster Karlsson blow-up pattern.  The pair
`(a,b)` is the unique inter-cluster pair with five crossings; the other five
inter-cluster pairs have seven crossings; intra-cluster pairs have four. -/
def lowerCrossingsQ (a b c d : ℚ) : ℚ :=
  4 * (binomTwoQ a + binomTwoQ b + binomTwoQ c + binomTwoQ d) +
    5 * a * b +
    7 * (a * c + a * d + b * c + b * d + c * d)

/-- Algebraic form of the lower crossing count. -/
theorem lowerCrossingsQ_eq_base_plus_clusterExcess
    {a b c d n : ℚ} (hn : n = a + b + c + d) :
    lowerCrossingsQ a b c d =
      4 * (n * (n - 1) / 2) + clusterExcess a b c d := by
  rw [hn]
  unfold lowerCrossingsQ binomTwoQ clusterExcess
  ring

/-- Lower crossing count attached to a bounded integer quadruple. -/
def lowerCrossingsOfQuad {n : ℕ} (q : QuadVec n) : ℚ :=
  lowerCrossingsQ (quadEntry q 0) (quadEntry q 1)
    (quadEntry q 2) (quadEntry q 3)

/-- Lower region count attached to a bounded integer quadruple. -/
def lowerRegionsOfQuad {n : ℕ} (q : QuadVec n) : ℚ :=
  lowerCrossingsOfQuad q + (n : ℚ) + 1

/-- If a quadruple has excess `concreteS n`, then its lower construction has
the candidate number of regions. -/
theorem lowerRegionsOfQuad_eq_candidate_of_excess
    {n : ℕ} {q : QuadVec n}
    (hq : q ∈ quadVecs n)
    (hmax : quadVecExcess q = concreteS n) :
    lowerRegionsOfQuad q = candidateRegions n := by
  unfold lowerRegionsOfQuad lowerCrossingsOfQuad candidateRegions
  rw [lowerCrossingsQ_eq_base_plus_clusterExcess
    (n := (n : ℚ)) (a := quadEntry q 0) (b := quadEntry q 1)
    (c := quadEntry q 2) (d := quadEntry q 3)
    (quadEntry_sum_eq_of_mem hq).symm]
  change clusterExcess (quadEntry q 0) (quadEntry q 1)
      (quadEntry q 2) (quadEntry q 3) = concreteS n at hmax
  rw [hmax]

/-- The finite maximum `concreteS n` is attained by some admissible quadruple. -/
theorem exists_quadVecExcess_eq_concreteS (n : ℕ) :
    ∃ q : QuadVec n, q ∈ quadVecs n ∧ quadVecExcess q = concreteS n := by
  unfold concreteS
  rcases Finset.exists_mem_eq_sup' (quadVecs_nonempty n) quadVecExcess with
    ⟨q, hq, hqmax⟩
  exact ⟨q, hq, hqmax.symm⟩

/-- A realization hypothesis for Karlsson blow-ups at size `n`: every
admissible quadruple can be realized by an arrangement with the corresponding
lower region count. -/
def LowerRealization (Arrangement : Type*) (region : Arrangement → ℚ) (n : ℕ) : Prop :=
  ∀ q : QuadVec n, q ∈ quadVecs n → ∃ A : Arrangement, region A = lowerRegionsOfQuad q

/-- A more geometric lower-realization hypothesis for Karlsson blow-ups at
size `n`: every admissible quadruple can be realized by an arrangement with
the corresponding crossing count, and the generic region equation
`regions = crossings + n + 1` holds for that arrangement. -/
def LowerCrossingRealization
    (Arrangement : Type*) (region crossings : Arrangement → ℚ) (n : ℕ) : Prop :=
  ∀ q : QuadVec n, q ∈ quadVecs n →
    ∃ A : Arrangement,
      crossings A = lowerCrossingsOfQuad q ∧
      region A = crossings A + (n : ℚ) + 1

/-- The crossing-count version of the lower construction implies the older
region-count realization interface. -/
theorem lowerRealization_of_lowerCrossingRealization
    {Arrangement : Type*} {region crossings : Arrangement → ℚ} {n : ℕ}
    (hreal : LowerCrossingRealization Arrangement region crossings n) :
    LowerRealization Arrangement region n := by
  intro q hq
  rcases hreal q hq with ⟨A, hcross, hregion⟩
  refine ⟨A, ?_⟩
  rw [hregion, hcross]
  rfl

/-- The lower realization hypothesis produces an arrangement attaining the
candidate value. -/
theorem exists_region_eq_candidate_of_lowerRealization
    {Arrangement : Type*} {region : Arrangement → ℚ} {n : ℕ}
    (hreal : LowerRealization Arrangement region n) :
    ∃ A : Arrangement, region A = candidateRegions n := by
  rcases exists_quadVecExcess_eq_concreteS n with ⟨q, hq, hqmax⟩
  rcases hreal q hq with ⟨A, hA⟩
  refine ⟨A, ?_⟩
  rw [hA, lowerRegionsOfQuad_eq_candidate_of_excess hq hqmax]

/-- Exactness theorem from upper certificates for all arrangements and a
lower-realization theorem for all quadruples. -/
theorem candidateRegions_isGreatest_of_certified_bounds
    {Arrangement : Type*} (region : Arrangement → ℚ) (n : ℕ)
    (upperCert :
      ∀ A : Arrangement,
        ∃ L : CertifiedLollipopUpper, L.nNat = n ∧ L.regions = region A)
    (lowerRealization : LowerRealization Arrangement region n) :
    IsGreatest (Set.range region) (candidateRegions n) := by
  apply candidateRegions_isGreatest region n
  · intro A
    rcases upperCert A with ⟨L, hLn, hLreg⟩
    have hupper := certified_lollipop_upper_bound L
    rw [hLn] at hupper
    rw [← hLreg]
    exact hupper
  · exact exists_region_eq_candidate_of_lowerRealization lowerRealization

/-- Exactness theorem in the manuscript's displayed `4 * n.choose 2` form. -/
theorem candidateRegionsChoose_isGreatest_of_certified_bounds
    {Arrangement : Type*} (region : Arrangement → ℚ) (n : ℕ)
    (upperCert :
      ∀ A : Arrangement,
        ∃ L : CertifiedLollipopUpper, L.nNat = n ∧ L.regions = region A)
    (lowerRealization : LowerRealization Arrangement region n) :
    IsGreatest (Set.range region) (candidateRegionsChoose n) := by
  rw [candidateRegionsChoose_eq_candidateRegions]
  exact candidateRegions_isGreatest_of_certified_bounds region n upperCert lowerRealization

/-- Exactness theorem using the direct upper certificates. -/
theorem candidateRegions_isGreatest_of_direct_certified_bounds
    {Arrangement : Type*} (region : Arrangement → ℚ) (n : ℕ)
    (upperCert :
      ∀ A : Arrangement,
        ∃ L : DirectCertifiedLollipopUpper, L.nNat = n ∧ L.regions = region A)
    (lowerRealization : LowerRealization Arrangement region n) :
    IsGreatest (Set.range region) (candidateRegions n) := by
  apply candidateRegions_isGreatest region n
  · intro A
    rcases upperCert A with ⟨L, hLn, hLreg⟩
    have hupper := direct_certified_lollipop_upper_bound L
    rw [hLn] at hupper
    rw [← hLreg]
    exact hupper
  · exact exists_region_eq_candidate_of_lowerRealization lowerRealization

/-- Direct exactness theorem in the manuscript's displayed `4 * n.choose 2`
form. -/
theorem candidateRegionsChoose_isGreatest_of_direct_certified_bounds
    {Arrangement : Type*} (region : Arrangement → ℚ) (n : ℕ)
    (upperCert :
      ∀ A : Arrangement,
        ∃ L : DirectCertifiedLollipopUpper, L.nNat = n ∧ L.regions = region A)
    (lowerRealization : LowerRealization Arrangement region n) :
    IsGreatest (Set.range region) (candidateRegionsChoose n) := by
  rw [candidateRegionsChoose_eq_candidateRegions]
  exact candidateRegions_isGreatest_of_direct_certified_bounds region n upperCert lowerRealization

end Lollipop

/-!
Proof component 4: `Upper`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Pairwise upper-bound certificates.

`Core.lean` has a compact upper certificate whose `crossing_reduction` field
already states the summed crossing inequality.  This file exposes the previous
step in the manuscript: pointwise pair estimates plus a score-sum comparison
imply that summed crossing inequality.
-/

namespace Lollipop

/-- Upper-bound certificate whose crossing reduction is given in pointwise
pair form. -/
structure PairwiseCertifiedLollipopUpper where
  nNat : ℕ
  crossings : ℚ
  regions : ℚ
  cross : Fin nNat → Fin nNat → ℚ
  score : Fin nNat → Fin nNat → ℚ
  pair : CertifiedColoredPair
  pair_nNat : pair.nNat = nNat
  crossings_le_pairSum : crossings ≤ pairSum nNat cross
  pointwise_crossing_bound :
    ∀ i j : Fin nNat, i < j → cross i j ≤ 4 + score i j
  score_sum_le_sigma : pairSum nNat score ≤ pair.sigma
  regions_eq : regions = crossings + (nNat : ℚ) + 1

/-- Pointwise pair estimates imply the manuscript's
`C <= 4 * binom(n,2) + sigma` crossing reduction. -/
theorem pairwise_certified_lollipop_crossing_reduction_choose
    (L : PairwiseCertifiedLollipopUpper) :
    L.crossings ≤ 4 * ((L.nNat.choose 2 : ℕ) : ℚ) + L.pair.sigma := by
  have hpair :=
    pairSum_crossing_le_choose_plus_score L.cross L.score L.pointwise_crossing_bound
  linarith [L.crossings_le_pairSum, hpair, L.score_sum_le_sigma]

/-- Product-form crossing reduction, matching `candidateRegions`. -/
theorem pairwise_certified_lollipop_crossing_reduction
    (L : PairwiseCertifiedLollipopUpper) :
    L.crossings ≤
      4 * ((L.nNat : ℚ) * ((L.nNat : ℚ) - 1) / 2) + L.pair.sigma := by
  have h := pairwise_certified_lollipop_crossing_reduction_choose L
  rw [Nat.cast_choose_two] at h
  exact h

/-- Convert a pairwise upper certificate to the compact upper certificate. -/
def PairwiseCertifiedLollipopUpper.toCertifiedLollipopUpper
    (L : PairwiseCertifiedLollipopUpper) : CertifiedLollipopUpper where
  nNat := L.nNat
  crossings := L.crossings
  regions := L.regions
  pair := L.pair
  pair_nNat := L.pair_nNat
  crossing_reduction := pairwise_certified_lollipop_crossing_reduction L
  regions_eq := L.regions_eq

/-- End-to-end upper bound from pairwise data. -/
theorem pairwise_certified_lollipop_upper_bound
    (L : PairwiseCertifiedLollipopUpper) :
    L.regions ≤ candidateRegions L.nNat := by
  exact certified_lollipop_upper_bound L.toCertifiedLollipopUpper

/-- End-to-end upper bound from pairwise data in the displayed
`4 * n.choose 2` form. -/
theorem pairwise_certified_lollipop_upper_bound_choose
    (L : PairwiseCertifiedLollipopUpper) :
    L.regions ≤ candidateRegionsChoose L.nNat := by
  simpa [candidateRegionsChoose_eq_candidateRegions] using
    pairwise_certified_lollipop_upper_bound L

/-- Direct upper-bound certificate whose crossing reduction is given in
pointwise pair form. -/
structure PairwiseDirectCertifiedLollipopUpper where
  nNat : ℕ
  crossings : ℚ
  regions : ℚ
  cross : Fin nNat → Fin nNat → ℚ
  score : Fin nNat → Fin nNat → ℚ
  pair : DirectCertifiedColoredPair
  pair_nNat : pair.nNat = nNat
  crossings_le_pairSum : crossings ≤ pairSum nNat cross
  pointwise_crossing_bound :
    ∀ i j : Fin nNat, i < j → cross i j ≤ 4 + score i j
  score_sum_le_sigma : pairSum nNat score ≤ pair.sigma
  regions_eq : regions = crossings + (nNat : ℚ) + 1

/-- Direct pointwise pair estimates imply the manuscript's
`C <= 4 * binom(n,2) + sigma` crossing reduction. -/
theorem pairwise_direct_certified_lollipop_crossing_reduction_choose
    (L : PairwiseDirectCertifiedLollipopUpper) :
    L.crossings ≤ 4 * ((L.nNat.choose 2 : ℕ) : ℚ) + L.pair.sigma := by
  have hpair :=
    pairSum_crossing_le_choose_plus_score L.cross L.score L.pointwise_crossing_bound
  linarith [L.crossings_le_pairSum, hpair, L.score_sum_le_sigma]

/-- Direct product-form crossing reduction, matching `candidateRegions`. -/
theorem pairwise_direct_certified_lollipop_crossing_reduction
    (L : PairwiseDirectCertifiedLollipopUpper) :
    L.crossings ≤
      4 * ((L.nNat : ℚ) * ((L.nNat : ℚ) - 1) / 2) + L.pair.sigma := by
  have h := pairwise_direct_certified_lollipop_crossing_reduction_choose L
  rw [Nat.cast_choose_two] at h
  exact h

/-- Convert a direct pairwise upper certificate to the compact direct upper
certificate. -/
def PairwiseDirectCertifiedLollipopUpper.toDirectCertifiedLollipopUpper
    (L : PairwiseDirectCertifiedLollipopUpper) : DirectCertifiedLollipopUpper where
  nNat := L.nNat
  crossings := L.crossings
  regions := L.regions
  pair := L.pair
  pair_nNat := L.pair_nNat
  crossing_reduction := pairwise_direct_certified_lollipop_crossing_reduction L
  regions_eq := L.regions_eq

/-- End-to-end upper bound from direct pairwise data. -/
theorem pairwise_direct_certified_lollipop_upper_bound
    (L : PairwiseDirectCertifiedLollipopUpper) :
    L.regions ≤ candidateRegions L.nNat := by
  exact direct_certified_lollipop_upper_bound L.toDirectCertifiedLollipopUpper

/-- End-to-end upper bound from direct pairwise data in the displayed
`4 * n.choose 2` form. -/
theorem pairwise_direct_certified_lollipop_upper_bound_choose
    (L : PairwiseDirectCertifiedLollipopUpper) :
    L.regions ≤ candidateRegionsChoose L.nNat := by
  simpa [candidateRegionsChoose_eq_candidateRegions] using
    pairwise_direct_certified_lollipop_upper_bound L

/-- Exactness theorem from pairwise upper certificates and lower realization. -/
theorem candidateRegions_isGreatest_of_pairwise_certified_bounds
    {Arrangement : Type*} (region : Arrangement → ℚ) (n : ℕ)
    (upperCert :
      ∀ A : Arrangement,
        ∃ L : PairwiseCertifiedLollipopUpper, L.nNat = n ∧ L.regions = region A)
    (lowerRealization : LowerRealization Arrangement region n) :
    IsGreatest (Set.range region) (candidateRegions n) := by
  apply candidateRegions_isGreatest_of_certified_bounds region n
  · intro A
    rcases upperCert A with ⟨L, hLn, hLreg⟩
    exact ⟨L.toCertifiedLollipopUpper, hLn, hLreg⟩
  · exact lowerRealization

/-- Exactness theorem from pairwise upper certificates in the displayed
`4 * n.choose 2` form. -/
theorem candidateRegionsChoose_isGreatest_of_pairwise_certified_bounds
    {Arrangement : Type*} (region : Arrangement → ℚ) (n : ℕ)
    (upperCert :
      ∀ A : Arrangement,
        ∃ L : PairwiseCertifiedLollipopUpper, L.nNat = n ∧ L.regions = region A)
    (lowerRealization : LowerRealization Arrangement region n) :
    IsGreatest (Set.range region) (candidateRegionsChoose n) := by
  rw [candidateRegionsChoose_eq_candidateRegions]
  exact candidateRegions_isGreatest_of_pairwise_certified_bounds
    region n upperCert lowerRealization

/-- Exactness theorem from direct pairwise upper certificates and lower
realization. -/
theorem candidateRegions_isGreatest_of_pairwise_direct_certified_bounds
    {Arrangement : Type*} (region : Arrangement → ℚ) (n : ℕ)
    (upperCert :
      ∀ A : Arrangement,
        ∃ L : PairwiseDirectCertifiedLollipopUpper, L.nNat = n ∧ L.regions = region A)
    (lowerRealization : LowerRealization Arrangement region n) :
    IsGreatest (Set.range region) (candidateRegions n) := by
  apply candidateRegions_isGreatest_of_direct_certified_bounds region n
  · intro A
    rcases upperCert A with ⟨L, hLn, hLreg⟩
    exact ⟨L.toDirectCertifiedLollipopUpper, hLn, hLreg⟩
  · exact lowerRealization

/-- Direct exactness theorem from pairwise upper certificates in the displayed
`4 * n.choose 2` form. -/
theorem candidateRegionsChoose_isGreatest_of_pairwise_direct_certified_bounds
    {Arrangement : Type*} (region : Arrangement → ℚ) (n : ℕ)
    (upperCert :
      ∀ A : Arrangement,
        ∃ L : PairwiseDirectCertifiedLollipopUpper, L.nNat = n ∧ L.regions = region A)
    (lowerRealization : LowerRealization Arrangement region n) :
    IsGreatest (Set.range region) (candidateRegionsChoose n) := by
  rw [candidateRegionsChoose_eq_candidateRegions]
  exact candidateRegions_isGreatest_of_pairwise_direct_certified_bounds
    region n upperCert lowerRealization

end Lollipop

/-!
Proof component 5: `Model.Proof`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Proof of the Theorem 1 statement from the certified subtheorems.

This file is intentionally only an orchestration layer.  The algebraic and
combinatorial work is proved in the imported modules; the remaining external
inputs are explicit certificate-producing hypotheses.
-/

namespace Lollipop
namespace TheoremOne

universe u

/-- Pairwise direct upper certificates for every arrangement in a problem
family.  This packages the geometric pointwise estimates, two-graph reduction,
colored quotient certificate, weighted blocker inputs, and matrix certificate
for each arrangement. -/
def PairwiseDirectUpperCertificates (P : ProblemFamily.{u}) : Prop :=
  ∀ n : ℕ, ∀ A : P.Arrangement n,
    ∃ L : PairwiseDirectCertifiedLollipopUpper,
      L.nNat = n ∧ L.regions = P.region n A

/-- Lower realization for every size in a problem family. -/
def LowerRealizations (P : ProblemFamily.{u}) : Prop :=
  ∀ n : ℕ, LowerRealization (P.Arrangement n) (P.region n) n

/-- Lower crossing-count realization for every size in a problem family.  The
extra function records the crossing count of each lower-construction
arrangement; Lean then uses `regions = crossings + n + 1` to recover the older
lower-realization interface. -/
def LowerCrossingRealizations
    (P : ProblemFamily.{u})
    (crossings : (n : ℕ) → P.Arrangement n → ℚ) : Prop :=
  ∀ n : ℕ,
    LowerCrossingRealization (P.Arrangement n) (P.region n) (crossings n) n

/-- Crossing-count lower realizations imply the older region-count lower
realizations. -/
theorem lowerRealizations_of_lowerCrossingRealizations
    (P : ProblemFamily.{u})
    {crossings : (n : ℕ) → P.Arrangement n → ℚ}
    (hlower : LowerCrossingRealizations P crossings) :
    LowerRealizations P := by
  intro n
  exact lowerRealization_of_lowerCrossingRealization (hlower n)

/-- The upper-bound half of Theorem 1, derived from pairwise direct
certificates. -/
theorem upper_bound_of_pairwise_direct_certificates
    (P : ProblemFamily.{u})
    (hupper : PairwiseDirectUpperCertificates P) :
    ∀ n : ℕ, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  intro n A
  rcases hupper n A with ⟨L, hLn, hLreg⟩
  have hbound := pairwise_direct_certified_lollipop_upper_bound_choose L
  rw [hLn] at hbound
  rw [← hLreg]
  exact hbound

/-- The lower-bound half of Theorem 1, derived from the lower-realization
hypothesis and the finite maximizer of `concreteS n`. -/
theorem lower_attainment_of_realizations
    (P : ProblemFamily.{u})
    (hlower : LowerRealizations P) :
    ∀ n : ℕ, ∃ A : P.Arrangement n,
      P.region n A = candidateRegionsChoose n := by
  intro n
  rcases exists_region_eq_candidate_of_lowerRealization
      (Arrangement := P.Arrangement n) (region := P.region n)
      (n := n) (hlower n) with ⟨A, hA⟩
  exact ⟨A, by simpa [candidateRegionsChoose_eq_candidateRegions] using hA⟩

/-- Upper bound plus lower attainment imply the maximum statement. -/
theorem maximumStatement_of_upper_bound_and_lower_attainment
    (P : ProblemFamily.{u})
    (hupper :
      ∀ n : ℕ, ∀ A : P.Arrangement n,
        P.region n A ≤ candidateRegionsChoose n)
    (hlower :
      ∀ n : ℕ, ∃ A : P.Arrangement n,
        P.region n A = candidateRegionsChoose n) :
    MaximumStatement P := by
  intro n
  constructor
  · rcases hlower n with ⟨A, hA⟩
    exact ⟨A, hA⟩
  · intro y hy
    rcases hy with ⟨A, rfl⟩
    exact hupper n A

/-- Theorem 1 in maximum form, proved from pairwise direct upper certificates
and lower realizations. -/
theorem theorem_one_maximum_from_pairwise_direct_certificates
    (P : ProblemFamily.{u})
    (hupper : PairwiseDirectUpperCertificates P)
    (hlower : LowerRealizations P) :
    MaximumStatement P := by
  exact maximumStatement_of_upper_bound_and_lower_attainment P
    (upper_bound_of_pairwise_direct_certificates P hupper)
    (lower_attainment_of_realizations P hlower)

/-- Pairwise direct upper certificates for a family with a named maximum
function. -/
def MaxPairwiseDirectUpperCertificates (P : MaxProblemFamily.{u}) : Prop :=
  PairwiseDirectUpperCertificates P.toProblemFamily

/-- Lower realizations for a family with a named maximum function. -/
def MaxLowerRealizations (P : MaxProblemFamily.{u}) : Prop :=
  LowerRealizations P.toProblemFamily

/-- Theorem 1 in formula form:
`a_Lop(n) = 4 * n.choose 2 + S(n) + n + 1`, proved from pairwise direct upper
certificates and lower realizations. -/
theorem theorem_one_formula_from_pairwise_direct_certificates
    (P : MaxProblemFamily.{u})
    (hupper : MaxPairwiseDirectUpperCertificates P)
    (hlower : MaxLowerRealizations P) :
    FormulaStatement P := by
  apply formulaStatement_of_maximumStatement
  exact theorem_one_maximum_from_pairwise_direct_certificates
    P.toProblemFamily hupper hlower

/-- A single-size version of Theorem 1 in formula form. -/
theorem theorem_one_formula_at
    (P : MaxProblemFamily.{u})
    (hupper : MaxPairwiseDirectUpperCertificates P)
    (hlower : MaxLowerRealizations P)
    (n : ℕ) :
    P.aLop n =
      4 * ((n.choose 2 : ℕ) : ℚ) + concreteS n + (n : ℚ) + 1 := by
  exact theorem_one_formula_from_pairwise_direct_certificates P hupper hlower n

end TheoremOne
end Lollipop

/-!
Proof component 6: `MatrixAssembly.Dependencies`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

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

/-!
Proof component 7: `MatrixAssembly.Proof`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Theorem 1, organized as a formal dependency graph.

This module states the final theorem using mathlib's `IsGreatest` idiom and
proves it from named subtheorems.  In contrast with the earlier direct
certificate layer, the matrix component is a single global hypothesis
`MatrixTheoremStatement`; it is not repeated as a field of every quotient
certificate.
-/

namespace Lollipop
namespace TheoremOneFormal

universe u

/-- Pairwise upper certificates for every arrangement in a problem family,
with the Section 5 matrix theorem used globally rather than carried inside
each quotient certificate. -/
def PairwiseNatMatrixUpperCertificates (P : TheoremOne.ProblemFamily.{u}) :
    Prop :=
  ∀ n : ℕ, ∀ A : P.Arrangement n,
    ∃ L : PairwiseNatMatrixCertifiedLollipopUpper,
      L.nNat = n ∧ L.regions = P.region n A

/-- The three subtheorems needed for the formal Theorem 1 chain. -/
structure TheoremOneSubtheorems (P : TheoremOne.ProblemFamily.{u}) : Prop where
  matrix_theorem : MatrixTheoremStatement
  upper_certificates : PairwiseNatMatrixUpperCertificates P
  lower_realizations : TheoremOne.LowerRealizations P

/-- A more detailed version of the subtheorem package, exposing the two
Section 5 inputs that imply the matrix theorem. -/
structure DetailedTheoremOneSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) : Prop where
  support_descent : SupportDescentStepStatement
  star_forest_minimum : StarForestMinimumStatement
  upper_certificates : PairwiseNatMatrixUpperCertificates P
  lower_realizations : TheoremOne.LowerRealizations P

/-- A Section 5 package reduced to the finite canonical star-forest cases. -/
structure CanonicalTheoremOneSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) : Prop where
  support_descent : SupportDescentStepStatement
  canonical_star_forest_cases : CanonicalStarForestMinimumCases
  upper_certificates : PairwiseNatMatrixUpperCertificates P
  lower_realizations : TheoremOne.LowerRealizations P

/-- Collapse the detailed Section 5 package to the shorter subtheorem package
by proving the matrix theorem from descent and the star-forest minimum. -/
def DetailedTheoremOneSubtheorems.toTheoremOneSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : DetailedTheoremOneSubtheorems P) :
    TheoremOneSubtheorems P where
  matrix_theorem :=
    matrix_theorem_of_descent_step_and_star_forest
      h.support_descent h.star_forest_minimum
  upper_certificates := h.upper_certificates
  lower_realizations := h.lower_realizations

/-- Collapse the canonical Section 5 package to the shorter subtheorem package
by proving the matrix theorem from descent and the canonical star-forest
cases. -/
def CanonicalTheoremOneSubtheorems.toTheoremOneSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CanonicalTheoremOneSubtheorems P) :
    TheoremOneSubtheorems P where
  matrix_theorem :=
    matrix_theorem_of_descent_step_and_canonical_cases
      h.support_descent h.canonical_star_forest_cases
  upper_certificates := h.upper_certificates
  lower_realizations := h.lower_realizations

/-- The upper-bound half of Theorem 1 from the matrix theorem and pairwise
integral-matrix upper certificates. -/
theorem upper_bound_of_pairwise_nat_matrix_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (hMatrix : MatrixTheoremStatement)
    (hupper : PairwiseNatMatrixUpperCertificates P) :
    ∀ n : ℕ, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  intro n A
  rcases hupper n A with ⟨L, hLn, hLreg⟩
  have hbound := pairwise_nat_matrix_certified_lollipop_upper_bound_choose hMatrix L
  rw [hLn] at hbound
  rw [← hLreg]
  exact hbound

/-- The lower-bound half is the previously checked lower-realization algebra,
converted to the displayed `Nat.choose` form. -/
theorem lower_attainment_of_realizations_choose
    (P : TheoremOne.ProblemFamily.{u})
    (hlower : TheoremOne.LowerRealizations P) :
    ∀ n : ℕ, ∃ A : P.Arrangement n,
      P.region n A = candidateRegionsChoose n := by
  intro n
  rcases TheoremOne.lower_attainment_of_realizations P hlower n with ⟨A, hA⟩
  exact ⟨A, by simpa [candidateRegionsChoose_eq_candidateRegions] using hA⟩

/-- Upper bound plus lower attainment imply the mathlib-style maximum
statement in the displayed formula form. -/
theorem maximumStatement_of_choose_upper_bound_and_lower_attainment
    (P : TheoremOne.ProblemFamily.{u})
    (hupper :
      ∀ n : ℕ, ∀ A : P.Arrangement n,
        P.region n A ≤ candidateRegionsChoose n)
    (hlower :
      ∀ n : ℕ, ∃ A : P.Arrangement n,
        P.region n A = candidateRegionsChoose n) :
    TheoremOne.MaximumStatement P := by
  intro n
  constructor
  · rcases hlower n with ⟨A, hA⟩
    exact ⟨A, hA⟩
  · intro y hy
    rcases hy with ⟨A, rfl⟩
    exact hupper n A

/-- Theorem 1 in maximum form from its named formal subtheorems. -/
theorem theorem_one_maximum_from_subtheorems
    (P : TheoremOne.ProblemFamily.{u})
    (h : TheoremOneSubtheorems P) :
    TheoremOne.MaximumStatement P := by
  exact maximumStatement_of_choose_upper_bound_and_lower_attainment P
    (upper_bound_of_pairwise_nat_matrix_certificates P
      h.matrix_theorem h.upper_certificates)
    (lower_attainment_of_realizations_choose P h.lower_realizations)

/-- Theorem 1 in maximum form from the detailed Section 5 subtheorems,
upper certificates, and lower realizations. -/
theorem theorem_one_maximum_from_detailed_subtheorems
    (P : TheoremOne.ProblemFamily.{u})
    (h : DetailedTheoremOneSubtheorems P) :
    TheoremOne.MaximumStatement P := by
  exact theorem_one_maximum_from_subtheorems P h.toTheoremOneSubtheorems

/-- Theorem 1 in maximum form from support descent, the finite canonical
star-forest cases, upper certificates, and lower realizations. -/
theorem theorem_one_maximum_from_canonical_subtheorems
    (P : TheoremOne.ProblemFamily.{u})
    (h : CanonicalTheoremOneSubtheorems P) :
    TheoremOne.MaximumStatement P := by
  exact theorem_one_maximum_from_subtheorems P h.toTheoremOneSubtheorems

/-- The same subtheorems for a family with a named maximum function. -/
def MaxTheoremOneSubtheorems (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  TheoremOneSubtheorems P.toProblemFamily

/-- Detailed subtheorems for a family with a named maximum function. -/
def MaxDetailedTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  DetailedTheoremOneSubtheorems P.toProblemFamily

/-- Canonical Section 5 subtheorems for a family with a named maximum
function. -/
def MaxCanonicalTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  CanonicalTheoremOneSubtheorems P.toProblemFamily

/-- Theorem 1 in formula form for a named maximum-count function. -/
theorem theorem_one_formula_from_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxTheoremOneSubtheorems P) :
    TheoremOne.FormulaStatement P := by
  exact TheoremOne.formulaStatement_of_maximumStatement P
    (theorem_one_maximum_from_subtheorems P.toProblemFamily h)

/-- Theorem 1 in formula form from the detailed Section 5 subtheorems. -/
theorem theorem_one_formula_from_detailed_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxDetailedTheoremOneSubtheorems P) :
    TheoremOne.FormulaStatement P := by
  exact TheoremOne.formulaStatement_of_maximumStatement P
    (theorem_one_maximum_from_detailed_subtheorems P.toProblemFamily h)

/-- Theorem 1 in formula form from support descent and the finite canonical
star-forest cases. -/
theorem theorem_one_formula_from_canonical_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxCanonicalTheoremOneSubtheorems P) :
    TheoremOne.FormulaStatement P := by
  exact TheoremOne.formulaStatement_of_maximumStatement P
    (theorem_one_maximum_from_canonical_subtheorems P.toProblemFamily h)

/-- Single-size formula statement for Theorem 1. -/
theorem theorem_one_formula_at_from_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxTheoremOneSubtheorems P)
    (n : ℕ) :
    P.aLop n =
      4 * ((n.choose 2 : ℕ) : ℚ) + concreteS n + (n : ℚ) + 1 := by
  exact theorem_one_formula_from_subtheorems P h n

/-- Single-size formula statement from the detailed Section 5 subtheorems. -/
theorem theorem_one_formula_at_from_detailed_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxDetailedTheoremOneSubtheorems P)
    (n : ℕ) :
    P.aLop n =
      4 * ((n.choose 2 : ℕ) : ℚ) + concreteS n + (n : ℚ) + 1 := by
  exact theorem_one_formula_from_detailed_subtheorems P h n

/-- Single-size formula statement from support descent and the finite
canonical star-forest cases. -/
theorem theorem_one_formula_at_from_canonical_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxCanonicalTheoremOneSubtheorems P)
    (n : ℕ) :
    P.aLop n =
      4 * ((n.choose 2 : ℕ) : ℚ) + concreteS n + (n : ℚ) + 1 := by
  exact theorem_one_formula_from_canonical_subtheorems P h n

end TheoremOneFormal
end Lollipop

/-!
Proof component 8: `ColoredTuran.PartitionCertificates`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
End-to-end Theorem 1 certificates with the partition-intersection step
internalized.

The upper-bound certificate now carries the weighted quotient vertices, the
two blocker relations, and the two partitions used in the blocker lemma.
Lean builds the `3 x 4` intersection matrix, proves its total mass, proves
`Q <= entrySq` from the square-sum grouping lemma, and derives the blocker
lower bounds from weighted-Turan-style complement bounds.  The remaining
certificate fields are exactly the external production steps: colored Zykov,
weighted Turan complement bounds, geometric pair bounds, and lower
realizations.

As elsewhere in this development, “certificate” names an ordinary Lean record
whose fields include proofs.  The records used for Theorem 4.1 are constructed
inside the proof from the coloring; they are not additional assumptions or
external verification artifacts.
-/

namespace Lollipop
namespace TheoremOneEndToEnd

open BigOperators

universe u

/-- A quotient certificate whose Section 4 blocker matrix is generated from
two actual partitions of a finite weighted quotient vertex set. -/
structure PartitionMatrixCertifiedQuotient
    (Vertex : Type u) [Fintype Vertex] [DecidableEq Vertex]
    extends QuotientData where
  nNat : Nat
  n_eq : n = (nNat : Rat)
  x : Vertex → Nat
  p3 : Vertex → Fin 3
  p4 : Vertex → Fin 4
  total_weight : totalWeightNat x = nNat
  Q_eq : Q = weightSquareSumRat x
  A : Vertex → Vertex → Prop
  B : Vertex → Vertex → Prop
  [decidable_A : DecidableRel A]
  [decidable_B : DecidableRel B]
  A_loopless : ∀ v, ¬ A v v
  B_loopless : ∀ v, ¬ B v v
  aOnlyE_eq : aOnlyE = weightedEdgeMass x A
  bOnlyD_eq : bOnlyD = weightedEdgeMass x B
  A_complement_le_p3 :
    orderedRelWeight x (fun v w : Vertex => v ≠ w ∧ ¬ A v w) ≤
      (totalWeightNat x : Rat)^2 - partitionSquareWeight x p3
  B_complement_le_p4 :
    orderedRelWeight x (fun v w : Vertex => v ≠ w ∧ ¬ B v w) ≤
      (totalWeightNat x : Rat)^2 - partitionSquareWeight x p4
  sigma_eq :
    sigma =
      3 * weightedEdgeMass x (fun v w : Vertex => v ≠ w) -
        2 * weightedEdgeMass x A - 2 * weightedEdgeMass x B

/-- The quotient objective identity follows from the concrete weighted
relations carried by the refined quotient certificate. -/
theorem PartitionMatrixCertifiedQuotient.quotient_identity
    {Vertex : Type u} [Fintype Vertex] [DecidableEq Vertex]
    (q : PartitionMatrixCertifiedQuotient Vertex) :
    QuotientIdentity q.toQuotientData := by
  letI : DecidableRel q.A := q.decidable_A
  letI : DecidableRel q.B := q.decidable_B
  let P := weightedEdgeMass q.x (fun v w : Vertex => v ≠ w)
  have hn : (totalWeightNat q.x : Rat) = q.n := by
    rw [q.total_weight, ← q.n_eq]
  have hP : P = (q.n^2 - q.Q) / 2 := by
    unfold P weightedEdgeMass
    rw [orderedRelWeight_offDiag, hn, q.Q_eq]
  have hsigma :
      q.sigma = 3 * P - 2 * q.aOnlyE - 2 * q.bOnlyD := by
    unfold P
    rw [q.sigma_eq, q.aOnlyE_eq, q.bOnlyD_eq]
  exact quotient_identity_from_cross_mass hP hsigma

/-- Convert a partition-generated quotient into the integral matrix quotient
used by the previous Theorem 1 dependency layer. -/
def PartitionMatrixCertifiedQuotient.toNatMatrixCertifiedQuotient
    {Vertex : Type u} [Fintype Vertex] [DecidableEq Vertex]
    (q : PartitionMatrixCertifiedQuotient Vertex) :
    TheoremOneFormal.NatMatrixCertifiedQuotient where
  n := q.n
  Q := q.Q
  aOnlyE := q.aOnlyE
  bOnlyD := q.bOnlyD
  sigma := q.sigma
  nNat := q.nNat
  n_eq := q.n_eq
  U := partitionMatrixNat q.x q.p3 q.p4
  matrix_total := by
    rw [matrixTotalNat_partitionMatrixNat, q.total_weight]
  a_lower := by
    letI : DecidableRel q.A := q.decidable_A
    have h :=
      weightedEdgeMass_ge_of_complement_le_partition
        q.x q.A q.p3 q.A_loopless q.A_complement_le_p3
    rw [q.aOnlyE_eq]
    rw [partitionSquareWeight_fin3_eq_rowSq_partitionMatrixNat q.x q.p3 q.p4] at h
    rw [q.Q_eq]
    exact h
  b_lower := by
    letI : DecidableRel q.B := q.decidable_B
    have h :=
      weightedEdgeMass_ge_of_complement_le_partition
        q.x q.B q.p4 q.B_loopless q.B_complement_le_p4
    rw [q.bOnlyD_eq]
    rw [partitionSquareWeight_fin4_eq_colSq_partitionMatrixNat q.x q.p3 q.p4] at h
    rw [q.Q_eq]
    exact h
  Q_le_entrySq := by
    rw [q.Q_eq]
    exact weightSquareSumRat_le_entrySqNat_partitionMatrixNat q.x q.p3 q.p4

@[simp]
theorem PartitionMatrixCertifiedQuotient.toNat_toQuotientData
    {Vertex : Type u} [Fintype Vertex] [DecidableEq Vertex]
    (q : PartitionMatrixCertifiedQuotient Vertex) :
    q.toNatMatrixCertifiedQuotient.toQuotientData = q.toQuotientData := by
  rfl

/-- Colored-pair certificate whose quotient matrix is generated by
intersecting the two weighted Turan partitions. -/
structure PartitionMatrixCertifiedColoredPair where
  nNat : Nat
  sigma : Rat
  Vertex : Type u
  [vertex_fintype : Fintype Vertex]
  [vertex_decidableEq : DecidableEq Vertex]
  quotient : PartitionMatrixCertifiedQuotient Vertex
  quotient_nNat : quotient.nNat = nNat
  quotient_preserves_sigma : quotient.sigma ≥ sigma

/-- Forget the partition witnesses after Lean has constructed the matrix
certificate from them. -/
def PartitionMatrixCertifiedColoredPair.toNatMatrixCertifiedColoredPair
    (p : PartitionMatrixCertifiedColoredPair.{u}) :
    TheoremOneFormal.NatMatrixCertifiedColoredPair := by
  letI : Fintype p.Vertex := p.vertex_fintype
  letI : DecidableEq p.Vertex := p.vertex_decidableEq
  exact
    { nNat := p.nNat
      sigma := p.sigma
      quotient := p.quotient.toNatMatrixCertifiedQuotient
      quotient_identity := by
        exact p.quotient.quotient_identity
      quotient_nNat := p.quotient_nNat
      quotient_preserves_sigma := p.quotient_preserves_sigma }

/-- Colored Turan bound with the matrix theorem and partition-intersection
algebra fully discharged. -/
theorem partition_matrix_certified_colored_turan_bound
    (p : PartitionMatrixCertifiedColoredPair.{u}) :
    p.sigma ≤ concreteS p.nNat := by
  exact TheoremOneFormal.nat_matrix_certified_colored_turan_bound
    matrix_theorem_proven p.toNatMatrixCertifiedColoredPair

/-- Pairwise lollipop upper certificate using partition-generated quotient
matrices. -/
structure PairwisePartitionMatrixCertifiedLollipopUpper where
  nNat : Nat
  crossings : Rat
  regions : Rat
  cross : Fin nNat → Fin nNat → Rat
  score : Fin nNat → Fin nNat → Rat
  pair : PartitionMatrixCertifiedColoredPair.{u}
  pair_nNat : pair.nNat = nNat
  crossings_le_pairSum : crossings ≤ pairSum nNat cross
  pointwise_crossing_bound :
    ∀ i j : Fin nNat, i < j → cross i j ≤ 4 + score i j
  score_sum_le_sigma : pairSum nNat score ≤ pair.sigma
  regions_eq : regions = crossings + (nNat : Rat) + 1

/-- Forget partition witnesses and produce the previous integral-matrix upper
certificate. -/
def PairwisePartitionMatrixCertifiedLollipopUpper.toPairwiseNatMatrixCertifiedLollipopUpper
    (L : PairwisePartitionMatrixCertifiedLollipopUpper.{u}) :
    TheoremOneFormal.PairwiseNatMatrixCertifiedLollipopUpper where
  nNat := L.nNat
  crossings := L.crossings
  regions := L.regions
  cross := L.cross
  score := L.score
  pair := L.pair.toNatMatrixCertifiedColoredPair
  pair_nNat := L.pair_nNat
  crossings_le_pairSum := L.crossings_le_pairSum
  pointwise_crossing_bound := L.pointwise_crossing_bound
  score_sum_le_sigma := L.score_sum_le_sigma
  regions_eq := L.regions_eq

/-- End-to-end upper bound for one arrangement from partition-generated
certificates. -/
theorem pairwise_partition_matrix_certified_lollipop_upper_bound_choose
    (L : PairwisePartitionMatrixCertifiedLollipopUpper.{u}) :
    L.regions ≤ candidateRegionsChoose L.nNat := by
  exact TheoremOneFormal.pairwise_nat_matrix_certified_lollipop_upper_bound_choose
    matrix_theorem_proven L.toPairwiseNatMatrixCertifiedLollipopUpper

/-- Upper certificates for every arrangement, with the blocker partition
intersection represented by concrete finite data. -/
def PairwisePartitionMatrixUpperCertificates
    (P : TheoremOne.ProblemFamily.{u}) : Prop :=
  ∀ n : Nat, ∀ A : P.Arrangement n,
    ∃ L : PairwisePartitionMatrixCertifiedLollipopUpper.{u},
      L.nNat = n ∧ L.regions = P.region n A

/-- Convert the refined upper-certificate family into the earlier certificate
shape. -/
theorem pairwise_partition_matrix_upper_certificates_to_nat_matrix
    {P : TheoremOne.ProblemFamily.{u}}
    (hupper : PairwisePartitionMatrixUpperCertificates P) :
    TheoremOneFormal.PairwiseNatMatrixUpperCertificates P := by
  intro n A
  rcases hupper n A with ⟨L, hLn, hLreg⟩
  exact ⟨L.toPairwiseNatMatrixCertifiedLollipopUpper, hLn, hLreg⟩

/-- Upper-bound half of Theorem 1 from refined partition-matrix
certificates. -/
theorem upper_bound_of_pairwise_partition_matrix_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (hupper : PairwisePartitionMatrixUpperCertificates P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact TheoremOneFormal.upper_bound_of_pairwise_nat_matrix_certificates P
    matrix_theorem_proven
    (pairwise_partition_matrix_upper_certificates_to_nat_matrix hupper)

end TheoremOneEndToEnd
end Lollipop

/-!
Proof component 9: `ColoredTuran.WeightedTuranCertificates`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
End-to-end quotient certificates using the proved weighted Turan theorem.

This layer removes the numeric weighted-Turan complement-bound fields from the
partition-matrix quotient certificate.  Instead, the quotient carries two actual
blocker graphs.  If their off-diagonal complements are `K_4`-free and
`K_5`-free, Lean chooses the `3`- and `4`-partitions supplied by the weighted
Turan theorem and then reuses the existing partition-intersection/matrix
pipeline.

Here “certificate” means a dependent record of an object and kernel-checked
proofs about it.  In the Theorem 4.1 call path the records below are built by
definitions in this directory.  There is no external certificate file,
unchecked solver result, or certificate-valued hypothesis at the theorem's
public boundary.
-/

namespace Lollipop
namespace TheoremOneEndToEnd

open BigOperators

universe u

/-- A quotient certificate in which the weighted Turan partitions are generated
from actual blocker graphs and clique-free complement hypotheses. -/
structure WeightedTuranCertifiedQuotient
    (Vertex : Type u) [Fintype Vertex] [DecidableEq Vertex]
    extends QuotientData where
  nNat : Nat
  n_eq : n = (nNat : Rat)
  x : Vertex → Nat
  total_weight : totalWeightNat x = nNat
  Q_eq : Q = weightSquareSumRat x
  Agraph : SimpleGraph Vertex
  Bgraph : SimpleGraph Vertex
  [decidable_A : DecidableRel Agraph.Adj]
  [decidable_B : DecidableRel Bgraph.Adj]
  aOnlyE_eq : aOnlyE = weightedEdgeMass x Agraph.Adj
  bOnlyD_eq : bOnlyD = weightedEdgeMass x Bgraph.Adj
  A_compl_cliqueFree : Agraphᶜ.CliqueFree 4
  B_compl_cliqueFree : Bgraphᶜ.CliqueFree 5
  sigma_eq :
    sigma =
      3 * weightedEdgeMass x (fun v w : Vertex => v ≠ w) -
        2 * weightedEdgeMass x Agraph.Adj - 2 * weightedEdgeMass x Bgraph.Adj

/-- Convert a weighted-Turan graph quotient into the existing
partition-generated quotient by choosing the two weighted Turan partitions. -/
noncomputable def WeightedTuranCertifiedQuotient.toPartitionMatrixCertifiedQuotient
    {Vertex : Type u} [Fintype Vertex] [DecidableEq Vertex]
    (q : WeightedTuranCertifiedQuotient Vertex) :
    PartitionMatrixCertifiedQuotient Vertex := by
  letI : DecidableRel q.Agraph.Adj := q.decidable_A
  letI : DecidableRel q.Bgraph.Adj := q.decidable_B
  have hAex :
      ∃ p3 : Vertex → Fin 3,
        orderedRelWeight q.x q.Agraphᶜ.Adj ≤
          (totalWeightNat q.x : Rat)^2 - partitionSquareWeight q.x p3 :=
    exists_partition_bound_of_cliqueFree q.x q.Agraphᶜ
      (r := 3) (by decide) q.A_compl_cliqueFree
  -- `p3` is chosen from the existential theorem just proved above.  It is not
  -- read from a table or trusted as an input.
  let p3 : Vertex → Fin 3 := Classical.choose hAex
  have hp3 :
      orderedRelWeight q.x q.Agraphᶜ.Adj ≤
        (totalWeightNat q.x : Rat)^2 - partitionSquareWeight q.x p3 :=
    Classical.choose_spec hAex
  have hBex :
      ∃ p4 : Vertex → Fin 4,
        orderedRelWeight q.x q.Bgraphᶜ.Adj ≤
          (totalWeightNat q.x : Rat)^2 - partitionSquareWeight q.x p4 :=
    exists_partition_bound_of_cliqueFree q.x q.Bgraphᶜ
      (r := 4) (by decide) q.B_compl_cliqueFree
  -- Likewise, the four-part partition is supplied by the proved weighted
  -- Turan theorem.
  let p4 : Vertex → Fin 4 := Classical.choose hBex
  have hp4 :
      orderedRelWeight q.x q.Bgraphᶜ.Adj ≤
        (totalWeightNat q.x : Rat)^2 - partitionSquareWeight q.x p4 :=
    Classical.choose_spec hBex
  exact
    { n := q.n
      Q := q.Q
      aOnlyE := q.aOnlyE
      bOnlyD := q.bOnlyD
      sigma := q.sigma
      nNat := q.nNat
      n_eq := q.n_eq
      x := q.x
      p3 := p3
      p4 := p4
      total_weight := q.total_weight
      Q_eq := q.Q_eq
      A := q.Agraph.Adj
      B := q.Bgraph.Adj
      decidable_A := q.decidable_A
      decidable_B := q.decidable_B
      A_loopless := by
        intro v
        exact q.Agraph.loopless.irrefl v
      B_loopless := by
        intro v
        exact q.Bgraph.loopless.irrefl v
      aOnlyE_eq := q.aOnlyE_eq
      bOnlyD_eq := q.bOnlyD_eq
      A_complement_le_p3 := by
        have hle :=
          orderedRelWeight_le_of_imp q.x
            (fun v w : Vertex => v ≠ w ∧ ¬ q.Agraph.Adj v w)
            q.Agraphᶜ.Adj
            (by
              intro v w h
              exact (SimpleGraph.compl_adj q.Agraph v w).2 h)
        exact le_trans hle hp3
      B_complement_le_p4 := by
        have hle :=
          orderedRelWeight_le_of_imp q.x
            (fun v w : Vertex => v ≠ w ∧ ¬ q.Bgraph.Adj v w)
            q.Bgraphᶜ.Adj
            (by
              intro v w h
              exact (SimpleGraph.compl_adj q.Bgraph v w).2 h)
        exact le_trans hle hp4
      sigma_eq := q.sigma_eq }

/-- Colored-pair certificate whose quotient partitions are supplied by the
proved weighted Turan theorem. -/
structure WeightedTuranCertifiedColoredPair where
  nNat : Nat
  sigma : Rat
  Vertex : Type u
  [vertex_fintype : Fintype Vertex]
  [vertex_decidableEq : DecidableEq Vertex]
  quotient : WeightedTuranCertifiedQuotient Vertex
  quotient_nNat : quotient.nNat = nNat
  quotient_preserves_sigma : quotient.sigma ≥ sigma

/-- Forget the weighted-Turan graph hypotheses after Lean has chosen the
partitions and built the partition-matrix certificate. -/
noncomputable def WeightedTuranCertifiedColoredPair.toPartitionMatrixCertifiedColoredPair
    (p : WeightedTuranCertifiedColoredPair.{u}) :
    PartitionMatrixCertifiedColoredPair.{u} := by
  classical
  letI : Fintype p.Vertex := p.vertex_fintype
  letI : DecidableEq p.Vertex := p.vertex_decidableEq
  exact
    { nNat := p.nNat
      sigma := p.sigma
      Vertex := p.Vertex
      quotient := p.quotient.toPartitionMatrixCertifiedQuotient
      quotient_nNat := by
        simpa [WeightedTuranCertifiedQuotient.toPartitionMatrixCertifiedQuotient]
          using p.quotient_nNat
      quotient_preserves_sigma := by
        simpa [WeightedTuranCertifiedQuotient.toPartitionMatrixCertifiedQuotient]
          using p.quotient_preserves_sigma }

/-- Colored Turan bound from actual blocker graphs plus the proved weighted
Turan theorem, partition-intersection bookkeeping, and matrix theorem. -/
theorem weighted_turan_certified_colored_turan_bound
    (p : WeightedTuranCertifiedColoredPair.{u}) :
    p.sigma ≤ concreteS p.nNat := by
  exact partition_matrix_certified_colored_turan_bound
    p.toPartitionMatrixCertifiedColoredPair

/-- Pairwise lollipop upper certificate using weighted-Turan-generated blocker
partitions. -/
structure PairwiseWeightedTuranCertifiedLollipopUpper where
  nNat : Nat
  crossings : Rat
  regions : Rat
  cross : Fin nNat → Fin nNat → Rat
  score : Fin nNat → Fin nNat → Rat
  pair : WeightedTuranCertifiedColoredPair.{u}
  pair_nNat : pair.nNat = nNat
  crossings_le_pairSum : crossings ≤ pairSum nNat cross
  pointwise_crossing_bound :
    ∀ i j : Fin nNat, i < j → cross i j ≤ 4 + score i j
  score_sum_le_sigma : pairSum nNat score ≤ pair.sigma
  regions_eq : regions = crossings + (nNat : Rat) + 1

/-- Convert the weighted-Turan-generated upper certificate into the existing
partition-matrix certificate. -/
noncomputable def PairwiseWeightedTuranCertifiedLollipopUpper.toPairwisePartitionMatrixCertifiedLollipopUpper
    (L : PairwiseWeightedTuranCertifiedLollipopUpper.{u}) :
    PairwisePartitionMatrixCertifiedLollipopUpper.{u} where
  nNat := L.nNat
  crossings := L.crossings
  regions := L.regions
  cross := L.cross
  score := L.score
  pair := L.pair.toPartitionMatrixCertifiedColoredPair
  pair_nNat := L.pair_nNat
  crossings_le_pairSum := L.crossings_le_pairSum
  pointwise_crossing_bound := L.pointwise_crossing_bound
  score_sum_le_sigma := L.score_sum_le_sigma
  regions_eq := L.regions_eq

/-- End-to-end upper bound for one arrangement from actual blocker graphs and
the proved weighted Turan theorem. -/
theorem pairwise_weighted_turan_certified_lollipop_upper_bound_choose
    (L : PairwiseWeightedTuranCertifiedLollipopUpper.{u}) :
    L.regions ≤ candidateRegionsChoose L.nNat := by
  exact pairwise_partition_matrix_certified_lollipop_upper_bound_choose
    L.toPairwisePartitionMatrixCertifiedLollipopUpper

/-- Upper certificates for every arrangement where the weighted Turan
partitions are generated internally from clique-free blocker complements. -/
def PairwiseWeightedTuranUpperCertificates
    (P : TheoremOne.ProblemFamily.{u}) : Prop :=
  ∀ n : Nat, ∀ A : P.Arrangement n,
    ∃ L : PairwiseWeightedTuranCertifiedLollipopUpper.{u},
      L.nNat = n ∧ L.regions = P.region n A

/-- Convert weighted-Turan-generated upper certificates into the existing
partition-matrix certificate family. -/
theorem pairwise_weighted_turan_upper_certificates_to_partition_matrix
    {P : TheoremOne.ProblemFamily.{u}}
    (hupper : PairwiseWeightedTuranUpperCertificates P) :
    PairwisePartitionMatrixUpperCertificates P := by
  intro n A
  rcases hupper n A with ⟨L, hLn, hLreg⟩
  exact ⟨L.toPairwisePartitionMatrixCertifiedLollipopUpper, hLn, hLreg⟩

/-- Upper-bound half of Theorem 1 from blocker graphs whose complements satisfy
the clique-free hypotheses required by weighted Turan. -/
theorem upper_bound_of_pairwise_weighted_turan_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (hupper : PairwiseWeightedTuranUpperCertificates P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact upper_bound_of_pairwise_partition_matrix_certificates P
    (pairwise_weighted_turan_upper_certificates_to_partition_matrix hupper)

end TheoremOneEndToEnd
end Lollipop

/-!
Proof component 10: `ColoredTuran.ColoredQuotientCertificates`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Colored quotient certificates.

Once colored Zykov has produced a no-zero colored quotient, the blocker graphs
`A` and `B` are read directly from the quotient colors.  The lemmas in
`ColoredZykov` prove that the quotient's `D`/`E` clique-free hypotheses imply
the clique-free complement hypotheses required by the weighted-Turan certificate
layer.

Terminology: in this file, a `...Certificate` is only a Lean structure that
bundles concrete objects together with proofs of their properties.  The public
theorem `colored_turan_bound` does not accept one of these structures as an
assumption.  It constructs every such bundle from the input coloring and the
two forbidden-clique hypotheses, and Lean's kernel checks every proof field.
-/

namespace Lollipop
namespace TheoremOneEndToEnd

open BigOperators

universe u

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {Vertex : Type u} [Fintype Vertex] [DecidableEq Vertex]

/-- Ordered weighted color objective of a finite colored quotient.  It counts
each unordered quotient edge twice and has zero diagonal contribution. -/
def weightedOrderedColorWeight
    (x : Vertex → Nat) (C : ColoredGraph Vertex) : Rat :=
  ∑ v : Vertex, ∑ w : Vertex,
    (x v : Rat) * (x w : Rat) * (C.color v w).weight

/-- Pointwise color-weight identity in a no-zero quotient. -/
theorem color_weight_eq_noZero_formula
    (C : ColoredGraph Vertex) (hzero : C.NoZeroOffDiag)
    (v w : Vertex) :
    (C.color v w).weight =
      3 * (if v ≠ w then (1 : Rat) else 0) -
        2 * (if C.AGraph.Adj v w then (1 : Rat) else 0) -
        2 * (if C.BGraph.Adj v w then (1 : Rat) else 0) := by
  by_cases hvw : v = w
  · subst w
    simp [C.color_self v, ColoredGraph.AGraph, ColoredGraph.BGraph,
      PairColor.weight]
  · have hnzero : C.color v w ≠ PairColor.zero := hzero hvw
    cases hc : C.color v w
    · exact False.elim (hnzero hc)
    · simp [hc, ColoredGraph.AGraph, ColoredGraph.BGraph,
        ColoredGraph.isAColor, ColoredGraph.isBColor, PairColor.weight, hvw]
      norm_num
    · simp [hc, ColoredGraph.AGraph, ColoredGraph.BGraph,
        ColoredGraph.isAColor, ColoredGraph.isBColor, PairColor.weight, hvw]
      norm_num
    · simp [hc, ColoredGraph.AGraph, ColoredGraph.BGraph,
        ColoredGraph.isAColor, ColoredGraph.isBColor, PairColor.weight, hvw]

/-- In a no-zero quotient, the ordered weighted color objective is
`2 * (3P - 2a - 2b)`, where `P` is cross-class mass and `a`, `b` are the
weighted masses of the `A` and `B` blocker graphs. -/
theorem weightedOrderedColorWeight_eq_noZero_formula
    (x : Vertex → Nat) (C : ColoredGraph Vertex)
    (hzero : C.NoZeroOffDiag) :
    weightedOrderedColorWeight x C =
      2 * (3 * weightedEdgeMass x (fun v w : Vertex => v ≠ w) -
        2 * weightedEdgeMass x C.AGraph.Adj -
        2 * weightedEdgeMass x C.BGraph.Adj) := by
  classical
  calc
    weightedOrderedColorWeight x C =
        ∑ v : Vertex, ∑ w : Vertex,
          (x v : Rat) * (x w : Rat) *
            (3 * (if v ≠ w then (1 : Rat) else 0) -
              2 * (if C.AGraph.Adj v w then (1 : Rat) else 0) -
              2 * (if C.BGraph.Adj v w then (1 : Rat) else 0)) := by
          unfold weightedOrderedColorWeight
          apply Finset.sum_congr rfl
          intro v _hv
          apply Finset.sum_congr rfl
          intro w _hw
          rw [color_weight_eq_noZero_formula C hzero v w]
    _ = 2 * (3 * weightedEdgeMass x (fun v w : Vertex => v ≠ w) -
          2 * weightedEdgeMass x C.AGraph.Adj -
          2 * weightedEdgeMass x C.BGraph.Adj) := by
          unfold weightedEdgeMass orderedRelWeight
          ring_nf
          simp [Finset.sum_sub_distrib, Finset.sum_mul]

/-- If `sigma` is defined as half the ordered weighted color objective, Lean
derives the manuscript's quotient objective identity. -/
theorem sigma_eq_of_weightedOrderedColorWeight
    {x : Vertex → Nat} {C : ColoredGraph Vertex} {sigma : Rat}
    (hzero : C.NoZeroOffDiag)
    (hsigma : sigma = weightedOrderedColorWeight x C / 2) :
    sigma =
      3 * weightedEdgeMass x (fun v w : Vertex => v ≠ w) -
        2 * weightedEdgeMass x C.AGraph.Adj -
        2 * weightedEdgeMass x C.BGraph.Adj := by
  rw [hsigma, weightedOrderedColorWeight_eq_noZero_formula x C hzero]
  ring

private theorem sum_fiber_card_mul
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (H : β → Rat) :
    (∑ b : β,
      (((Finset.univ : Finset α).filter
        (fun a : α => f a = b)).card : Rat) * H b) =
      ∑ a : α, H (f a) := by
  classical
  rw [← Finset.sum_fiberwise
    (s := (Finset.univ : Finset α)) (g := f)
    (f := fun a : α => H (f a))]
  apply Finset.sum_congr rfl
  intro b _hb
  have hconst :
      (∑ a ∈ (Finset.univ : Finset α).filter (fun a : α => f a = b),
          H (f a)) =
        ∑ _a ∈ (Finset.univ : Finset α).filter (fun a : α => f a = b),
          H b := by
    apply Finset.sum_congr rfl
    intro a ha
    have hfb : f a = b := (Finset.mem_filter.mp ha).2
    simp [hfb]
  rw [hconst]
  simp [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- The weighted ordered objective of the zero-twin quotient, with class-size
weights, is exactly the original ordered objective. -/
theorem orderedColorWeight_eq_weightedOrderedColorWeight_zeroQuotient
    {V : Type u} [Fintype V] [DecidableEq V]
    (C : ColoredGraph V) (h : C.ZeroTwinQuotientReady) :
    C.orderedColorWeight =
      weightedOrderedColorWeight
        (C.zeroClassWeight h) (C.zeroQuotientColoredGraph h) := by
  classical
  let Q := C.ZeroQuotient h
  let f : V → Q := Quotient.mk''
  let Cq : ColoredGraph Q := C.zeroQuotientColoredGraph h
  calc
    C.orderedColorWeight =
        ∑ v : V, ∑ w : V, (Cq.color (f v) (f w)).weight := by
          unfold ColoredGraph.orderedColorWeight ColoredGraph.colorDegree
          apply Finset.sum_congr rfl
          intro v _hv
          apply Finset.sum_congr rfl
          intro w _hw
          simp [Cq, f, ColoredGraph.zeroQuotientColoredGraph,
            ColoredGraph.quotientColor_mk]
    _ = ∑ v : V, ∑ r : Q,
          ((C.zeroClassWeight h r : Nat) : Rat) *
            (Cq.color (f v) r).weight := by
          apply Finset.sum_congr rfl
          intro v _hv
          symm
          simpa [ColoredGraph.zeroClassWeight, f, Cq, mul_comm] using
            sum_fiber_card_mul (α := V) (β := Q) f
              (fun r : Q => (Cq.color (f v) r).weight)
    _ = ∑ q : Q, ((C.zeroClassWeight h q : Nat) : Rat) *
          (∑ r : Q, ((C.zeroClassWeight h r : Nat) : Rat) *
            (Cq.color q r).weight) := by
          symm
          simpa [ColoredGraph.zeroClassWeight, f, Cq] using
            sum_fiber_card_mul (α := V) (β := Q) f
              (fun q : Q =>
                ∑ r : Q, ((C.zeroClassWeight h r : Nat) : Rat) *
                  (Cq.color q r).weight)
    _ = weightedOrderedColorWeight
          (C.zeroClassWeight h) (C.zeroQuotientColoredGraph h) := by
          unfold weightedOrderedColorWeight
          apply Finset.sum_congr rfl
          intro q _hq
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r _hr
          ring

/-- A no-zero colored quotient with weighted class sizes.  The `sigma_eq` field
is the quotient objective identity after colored Zykov has produced the quotient;
the blocker complement clique-free hypotheses are derived, not stored. -/
structure ColoredQuotientCertificate
    (Vertex : Type u) [Fintype Vertex] [DecidableEq Vertex]
    extends QuotientData where
  nNat : Nat
  n_eq : n = (nNat : Rat)
  x : Vertex → Nat
  total_weight : totalWeightNat x = nNat
  Q_eq : Q = weightSquareSumRat x
  C : ColoredGraph Vertex
  no_zero : C.NoZeroOffDiag
  D_cliqueFree : C.DGraph.CliqueFree 4
  E_cliqueFree : C.EGraph.CliqueFree 5
  aOnlyE_eq : aOnlyE = weightedEdgeMass x C.AGraph.Adj
  bOnlyD_eq : bOnlyD = weightedEdgeMass x C.BGraph.Adj
  sigma_eq :
    sigma =
      3 * weightedEdgeMass x (fun v w : Vertex => v ≠ w) -
        2 * weightedEdgeMass x C.AGraph.Adj -
        2 * weightedEdgeMass x C.BGraph.Adj

/-- Build the colored quotient certificate from a colored graph whose zero
classes are already twin classes.  This packages the formal quotient
construction, class-size weights, objective preservation, no-zero condition,
and inherited `D`/`E` clique-free hypotheses. -/
noncomputable def ColoredGraph.toColoredQuotientCertificate
    {V : Type u} [Fintype V] [DecidableEq V]
    (C : ColoredGraph V) (hready : C.ZeroTwinQuotientReady)
    (hD : C.DGraph.CliqueFree 4) (hE : C.EGraph.CliqueFree 5) :
    ColoredQuotientCertificate (C.ZeroQuotient hready) := by
  classical
  let Cq : ColoredGraph (C.ZeroQuotient hready) :=
    C.zeroQuotientColoredGraph hready
  let x : C.ZeroQuotient hready → Nat := C.zeroClassWeight hready
  have hno : Cq.NoZeroOffDiag := C.zeroQuotient_noZeroOffDiag hready
  exact
    { n := (Fintype.card V : Rat)
      Q := weightSquareSumRat x
      aOnlyE := weightedEdgeMass x Cq.AGraph.Adj
      bOnlyD := weightedEdgeMass x Cq.BGraph.Adj
      sigma := weightedOrderedColorWeight x Cq / 2
      nNat := Fintype.card V
      n_eq := rfl
      x := x
      total_weight := by
        simpa [x] using C.totalWeightNat_zeroClassWeight hready
      Q_eq := rfl
      C := Cq
      no_zero := hno
      D_cliqueFree := by
        simpa [Cq] using C.zeroQuotient_DGraph_cliqueFree hready hD
      E_cliqueFree := by
        simpa [Cq] using C.zeroQuotient_EGraph_cliqueFree hready hE
      aOnlyE_eq := rfl
      bOnlyD_eq := rfl
      sigma_eq := by
        exact sigma_eq_of_weightedOrderedColorWeight hno rfl }

/-- A colored quotient supplies the weighted-Turan quotient certificate by
deriving the blocker complement clique-free hypotheses from the no-zero quotient
condition and the original `D`/`E` clique-free hypotheses. -/
def ColoredQuotientCertificate.toWeightedTuranCertifiedQuotient
    {Vertex : Type u} [Fintype Vertex] [DecidableEq Vertex]
    (q : ColoredQuotientCertificate Vertex) :
    WeightedTuranCertifiedQuotient Vertex where
  n := q.n
  Q := q.Q
  aOnlyE := q.aOnlyE
  bOnlyD := q.bOnlyD
  sigma := q.sigma
  nNat := q.nNat
  n_eq := q.n_eq
  x := q.x
  total_weight := q.total_weight
  Q_eq := q.Q_eq
  Agraph := q.C.AGraph
  Bgraph := q.C.BGraph
  aOnlyE_eq := q.aOnlyE_eq
  bOnlyD_eq := q.bOnlyD_eq
  A_compl_cliqueFree :=
    ColoredGraph.AGraph_compl_cliqueFree_four_of_DGraph
      q.C q.no_zero q.D_cliqueFree
  B_compl_cliqueFree :=
    ColoredGraph.BGraph_compl_cliqueFree_five_of_EGraph
      q.C q.no_zero q.E_cliqueFree
  sigma_eq := q.sigma_eq

/-- Colored-pair certificate whose quotient is a no-zero colored quotient. -/
structure ColoredQuotientCertifiedColoredPair where
  nNat : Nat
  sigma : Rat
  Vertex : Type u
  [vertex_fintype : Fintype Vertex]
  [vertex_decidableEq : DecidableEq Vertex]
  quotient : ColoredQuotientCertificate Vertex
  quotient_nNat : quotient.nNat = nNat
  quotient_preserves_sigma : quotient.sigma ≥ sigma

/-- Convert a colored-quotient pair into the weighted-Turan certificate layer. -/
def ColoredQuotientCertifiedColoredPair.toWeightedTuranCertifiedColoredPair
    (p : ColoredQuotientCertifiedColoredPair.{u}) :
    WeightedTuranCertifiedColoredPair.{u} := by
  letI : Fintype p.Vertex := p.vertex_fintype
  letI : DecidableEq p.Vertex := p.vertex_decidableEq
  exact
    { nNat := p.nNat
      sigma := p.sigma
      Vertex := p.Vertex
      quotient := p.quotient.toWeightedTuranCertifiedQuotient
      quotient_nNat := p.quotient_nNat
      quotient_preserves_sigma := p.quotient_preserves_sigma }

/-- Colored Turan bound from a no-zero colored quotient, the proved weighted
Turan theorem, partition-intersection bookkeeping, and Section 5. -/
theorem colored_quotient_certified_colored_turan_bound
    (p : ColoredQuotientCertifiedColoredPair.{u}) :
    p.sigma ≤ concreteS p.nNat := by
  exact weighted_turan_certified_colored_turan_bound
    p.toWeightedTuranCertifiedColoredPair

/-- Colored Turan bound for a colored graph already in zero-twin quotient form.
The remaining global colored-Zykov task is to prove that every extremal pair can
be transformed into this `ZeroTwinQuotientReady` form. -/
theorem zeroTwin_colored_turan_bound
    {V : Type u} [Fintype V] [DecidableEq V]
    (C : ColoredGraph V) (hready : C.ZeroTwinQuotientReady)
    (hD : C.DGraph.CliqueFree 4) (hE : C.EGraph.CliqueFree 5) :
    C.orderedColorWeight / 2 ≤ concreteS (Fintype.card V) := by
  classical

  -- Collapse each zero-twin class to one quotient vertex and record the class
  -- cardinality as its natural-number weight.  The fields of `q` are proved
  -- here by `toColoredQuotientCertificate`; they are not supplied by a caller
  -- and are not an external or precomputed certificate.
  let q := C.toColoredQuotientCertificate hready hD hE

  -- Quotienting preserves the entire ordered color objective.  The quotient
  -- convention stores half of that ordered objective as `q.sigma`, matching
  -- the unordered-pair sum in the paper.
  have hsig :
      q.sigma = C.orderedColorWeight / 2 := by
    change
      weightedOrderedColorWeight
          (C.zeroClassWeight hready)
          (C.zeroQuotientColoredGraph hready) / 2 =
        C.orderedColorWeight / 2
    rw [← orderedColorWeight_eq_weightedOrderedColorWeight_zeroQuotient C hready]

  -- The long lower layer now has every piece of concrete data it needs:
  -- quotient vertices, their class weights, and the two inherited
  -- clique-freeness proofs.  It obtains the Turan partitions and proves the
  -- matrix inequality internally.
  have hbound :=
    colored_quotient_certified_colored_turan_bound
      { nNat := Fintype.card V
        sigma := C.orderedColorWeight / 2
        Vertex := C.ZeroQuotient hready
        quotient := q
        quotient_nNat := rfl
        quotient_preserves_sigma := by
          rw [hsig] }

  -- Replace the quotient's stored names by the original graph's cardinality
  -- and objective.
  simpa using hbound

/-- Full colored Turan bound for any colored graph satisfying the manuscript's
two forbidden-clique hypotheses.  Lean first selects a finite two-stage
Zykov-extremal graph on the same vertex type, proves it is quotient-ready via
the clone-potential theorem, applies the zero-twin quotient bound, and then
uses first-stage objective maximality to transfer the bound back to `C`. -/
theorem colored_turan_bound
    {V : Type u} [Fintype V] [DecidableEq V]
    (C : ColoredGraph V)
    (hD : C.DGraph.CliqueFree 4) (hE : C.EGraph.CliqueFree 5) :
    C.orderedColorWeight / 2 ≤ concreteS (Fintype.card V) := by
  classical

  -- The set of feasible colorings on a finite vertex type is finite, so an
  -- objective-maximal coloring exists.  A second finite maximization of the
  -- zero-twin potential gives the precise extremal object used by Zykov
  -- symmetrization.
  obtain ⟨Cmax, hCmax⟩ :=
    ColoredGraph.exists_isColoredZykovExtremal_of_exists
      (V := V) ⟨C, hD, hE⟩
  have hweight_le : C.orderedColorWeight ≤ Cmax.orderedColorWeight :=
    hCmax.orderedWeight_le hD hE

  -- The clone argument proves that distinct zero-twin classes cannot be
  -- connected by color zero in this extremal object.  Hence quotient colors
  -- are well-defined and nonzero off the diagonal.
  have hready : Cmax.ZeroTwinQuotientReady :=
    Cmax.zeroTwinQuotientReady_of_zykov_extremal hCmax

  -- Apply the weighted quotient/Turan/matrix argument to the extremizer.
  have hbound :
      Cmax.orderedColorWeight / 2 ≤ concreteS (Fintype.card V) :=
    zeroTwin_colored_turan_bound
      Cmax hready hCmax.D_cliqueFree hCmax.E_cliqueFree

  -- The original coloring has no larger objective than the extremizer.
  linarith

/-- Colored-pair certificate at the level of the original colored graph.  The
only graph-theoretic inputs are the two forbidden-clique hypotheses; colored
Zykov, quotienting, weighted Turan, partition-intersection bookkeeping, and the
matrix theorem are all invoked internally by `colored_turan_bound`. -/
structure ColoredGraphCertifiedColoredPair where
  nNat : Nat
  sigma : Rat
  Vertex : Type u
  [vertex_fintype : Fintype Vertex]
  [vertex_decidableEq : DecidableEq Vertex]
  C : ColoredGraph Vertex
  D_cliqueFree : C.DGraph.CliqueFree 4
  E_cliqueFree : C.EGraph.CliqueFree 5
  card_eq : Fintype.card Vertex = nNat
  sigma_le_color : sigma ≤ C.orderedColorWeight / 2

/-- Colored Turan bound from an original colored graph certificate. -/
theorem colored_graph_certified_colored_turan_bound
    (p : ColoredGraphCertifiedColoredPair.{u}) :
    p.sigma ≤ concreteS p.nNat := by
  letI : Fintype p.Vertex := p.vertex_fintype
  letI : DecidableEq p.Vertex := p.vertex_decidableEq
  have hbound :
      p.C.orderedColorWeight / 2 ≤ concreteS p.nNat := by
    simpa [p.card_eq] using
      colored_turan_bound p.C p.D_cliqueFree p.E_cliqueFree
  exact le_trans p.sigma_le_color hbound

/-- Pairwise lollipop upper certificate using the original colored graph for
the pair score. -/
structure PairwiseColoredGraphCertifiedLollipopUpper where
  nNat : Nat
  crossings : Rat
  regions : Rat
  cross : Fin nNat → Fin nNat → Rat
  score : Fin nNat → Fin nNat → Rat
  pair : ColoredGraphCertifiedColoredPair.{u}
  pair_nNat : pair.nNat = nNat
  crossings_le_pairSum : crossings ≤ pairSum nNat cross
  pointwise_crossing_bound :
    ∀ i j : Fin nNat, i < j → cross i j ≤ 4 + score i j
  score_sum_le_sigma : pairSum nNat score ≤ pair.sigma
  regions_eq : regions = crossings + (nNat : Rat) + 1

/-- Pairwise estimates imply the displayed crossing reduction for colored
graph certificates. -/
theorem pairwise_colored_graph_certified_lollipop_crossing_reduction_choose
    (L : PairwiseColoredGraphCertifiedLollipopUpper.{u}) :
    L.crossings ≤ 4 * ((L.nNat.choose 2 : Nat) : Rat) + L.pair.sigma := by
  have hpair :=
    pairSum_crossing_le_choose_plus_score L.cross L.score
      L.pointwise_crossing_bound
  linarith [L.crossings_le_pairSum, hpair, L.score_sum_le_sigma]

/-- Product-form crossing reduction for colored graph certificates. -/
theorem pairwise_colored_graph_certified_lollipop_crossing_reduction
    (L : PairwiseColoredGraphCertifiedLollipopUpper.{u}) :
    L.crossings ≤
      4 * ((L.nNat : Rat) * ((L.nNat : Rat) - 1) / 2) + L.pair.sigma := by
  have h := pairwise_colored_graph_certified_lollipop_crossing_reduction_choose L
  rw [Nat.cast_choose_two] at h
  exact h

/-- End-to-end upper bound for one arrangement from the original colored graph,
colored Zykov, the quotient construction, weighted Turan, and Section 5. -/
theorem pairwise_colored_graph_certified_lollipop_upper_bound_choose
    (L : PairwiseColoredGraphCertifiedLollipopUpper.{u}) :
    L.regions ≤ candidateRegionsChoose L.nNat := by
  have ht := colored_graph_certified_colored_turan_bound L.pair
  rw [L.pair_nNat] at ht
  have hc := pairwise_colored_graph_certified_lollipop_crossing_reduction L
  rw [candidateRegionsChoose_eq_candidateRegions]
  unfold candidateRegions
  rw [L.regions_eq]
  linarith

/-- Upper certificates for every arrangement whose two-graph colored pair is
provided as an original colored graph with `D`/`E` clique-free. -/
def PairwiseColoredGraphUpperCertificates
    (P : TheoremOne.ProblemFamily.{u}) : Prop :=
  ∀ n : Nat, ∀ A : P.Arrangement n,
    ∃ L : PairwiseColoredGraphCertifiedLollipopUpper.{u},
      L.nNat = n ∧ L.regions = P.region n A

/-- Upper-bound half of Theorem 1 from original colored graph certificates. -/
theorem upper_bound_of_pairwise_colored_graph_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (hupper : PairwiseColoredGraphUpperCertificates P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  intro n A
  rcases hupper n A with ⟨L, hLn, hLreg⟩
  rw [← hLreg, ← hLn]
  exact pairwise_colored_graph_certified_lollipop_upper_bound_choose L

/-- Pairwise lollipop upper certificate whose two-graph colored pair is
represented by a no-zero colored quotient. -/
structure PairwiseColoredQuotientCertifiedLollipopUpper where
  nNat : Nat
  crossings : Rat
  regions : Rat
  cross : Fin nNat → Fin nNat → Rat
  score : Fin nNat → Fin nNat → Rat
  pair : ColoredQuotientCertifiedColoredPair.{u}
  pair_nNat : pair.nNat = nNat
  crossings_le_pairSum : crossings ≤ pairSum nNat cross
  pointwise_crossing_bound :
    ∀ i j : Fin nNat, i < j → cross i j ≤ 4 + score i j
  score_sum_le_sigma : pairSum nNat score ≤ pair.sigma
  regions_eq : regions = crossings + (nNat : Rat) + 1

/-- Forget the colored-quotient layer after Lean has derived the blocker
graphs and weighted-Turan hypotheses. -/
def PairwiseColoredQuotientCertifiedLollipopUpper.toPairwiseWeightedTuranCertifiedLollipopUpper
    (L : PairwiseColoredQuotientCertifiedLollipopUpper.{u}) :
    PairwiseWeightedTuranCertifiedLollipopUpper.{u} where
  nNat := L.nNat
  crossings := L.crossings
  regions := L.regions
  cross := L.cross
  score := L.score
  pair := L.pair.toWeightedTuranCertifiedColoredPair
  pair_nNat := L.pair_nNat
  crossings_le_pairSum := L.crossings_le_pairSum
  pointwise_crossing_bound := L.pointwise_crossing_bound
  score_sum_le_sigma := L.score_sum_le_sigma
  regions_eq := L.regions_eq

/-- End-to-end upper bound for one arrangement from a no-zero colored quotient,
the proved weighted Turan theorem, partition-intersection bookkeeping, and
Section 5. -/
theorem pairwise_colored_quotient_certified_lollipop_upper_bound_choose
    (L : PairwiseColoredQuotientCertifiedLollipopUpper.{u}) :
    L.regions ≤ candidateRegionsChoose L.nNat := by
  exact pairwise_weighted_turan_certified_lollipop_upper_bound_choose
    L.toPairwiseWeightedTuranCertifiedLollipopUpper

/-- Upper certificates for every arrangement whose two-graph colored pair has
a no-zero colored quotient certificate. -/
def PairwiseColoredQuotientUpperCertificates
    (P : TheoremOne.ProblemFamily.{u}) : Prop :=
  ∀ n : Nat, ∀ A : P.Arrangement n,
    ∃ L : PairwiseColoredQuotientCertifiedLollipopUpper.{u},
      L.nNat = n ∧ L.regions = P.region n A

/-- Convert no-zero colored quotient upper certificates into weighted-Turan
upper certificates by deriving the blocker graphs and their clique-free
complement hypotheses. -/
theorem pairwise_colored_quotient_upper_certificates_to_weighted_turan
    {P : TheoremOne.ProblemFamily.{u}}
    (hupper : PairwiseColoredQuotientUpperCertificates P) :
    PairwiseWeightedTuranUpperCertificates P := by
  intro n A
  rcases hupper n A with ⟨L, hLn, hLreg⟩
  exact
    ⟨L.toPairwiseWeightedTuranCertifiedLollipopUpper, hLn, hLreg⟩

/-- Upper-bound half of Theorem 1 from no-zero colored quotient certificates. -/
theorem upper_bound_of_pairwise_colored_quotient_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (hupper : PairwiseColoredQuotientUpperCertificates P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact upper_bound_of_pairwise_weighted_turan_certificates P
    (pairwise_colored_quotient_upper_certificates_to_weighted_turan hupper)

end TheoremOneEndToEnd
end Lollipop

/-! The actual numbered proof. -/

/-!
Proof of manuscript Theorem 4.1.

This file intentionally spells out the top-level mathematical argument rather
than ending with `exact colored_turan_bound ...`.  The latter theorem remains a
useful library endpoint, but a reader of the manuscript-numbered proof should
be able to see the following three steps directly:

1. apply the manuscript's colored Zykov lemma to choose an extremal feasible
   coloring whose zero-color classes form a genuine quotient;
2. apply the fully proved weighted quotient/matrix bound to that extremal
   coloring;
3. transfer the bound back to the original coloring and rewrite the internal
   finite maximum as the manuscript's sorted definition of `S(n)`.

Every implementation theorem used below lives in a manuscript-numbered proof
file. The quotient construction and bound are integrated earlier in this file;
the weighted Turan, blocker, and `3 x 4` matrix arguments live in the numbered
proofs for Lemmas 6.1, 6.2, 7.2, 7.3, and Theorem 7.1.
-/

namespace Lollipop.Manuscript.Theorem_4_1

universe u

open TheoremOneEndToEnd

theorem proof {V : Type u} [Fintype V] [DecidableEq V]
    (C : ColoredGraph V) : Statement C := by
  -- These are exactly the two hypotheses in the manuscript: the graph formed
  -- by colors `B` and `X` is `K_4`-free, while the graph formed by colors `A`
  -- and `X` is `K_5`-free.
  intro hD hE

  -- The internal extremal proof is phrased using `concreteS`, a maximum over
  -- all four-tuples.  `manuscriptS_eq_concreteS` proves that this is equal to
  -- the manuscript's maximum over sorted tuples `a <= b <= c <= d`.
  rw [TheoremOneManuscript.manuscriptS_eq_concreteS]

  -- Manuscript Lemma 5.1 (proved in `Lollipop/Lemma_5_1/Proof.lean`) chooses a
  -- feasible coloring `Cmax` on the same vertex type.  Its objective is at
  -- least that of `C`, and its zero-twin classes are ready to be quotiented.
  obtain ⟨Cmax, hCmax, hweight_le, hquotient_ready⟩ :=
    Lollipop.Manuscript.Lemma_5_1.proof C ⟨hD, hE⟩

  -- The quotient theorem is the long combinatorial core.  It constructs the
  -- zero-twin quotient and its class-size weights, obtains the two weighted
  -- Turan partitions, intersects them into a `3 x 4` matrix, and applies the
  -- fully proved matrix theorem.  No quotient/partition/matrix object is an
  -- assumption of Theorem 4.1: all of them are built inside this theorem.
  have hmax_bound :
      Cmax.orderedColorWeight / 2 <= concreteS (Fintype.card V) :=
    TheoremOneEndToEnd.zeroTwin_colored_turan_bound
      Cmax hquotient_ready hCmax.D_cliqueFree hCmax.E_cliqueFree

  -- Division by two preserves the objective comparison.  Combining that
  -- comparison with the bound for `Cmax` proves the desired bound for `C`.
  linarith

end Lollipop.Manuscript.Theorem_4_1
