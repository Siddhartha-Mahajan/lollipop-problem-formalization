import Lollipop.Internal.Core
import Lollipop.Internal.Lower
import Lollipop.Internal.PairReduction
import Mathlib.Tactic

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
