import Lollipop.Internal.Core
import Mathlib.Tactic

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
