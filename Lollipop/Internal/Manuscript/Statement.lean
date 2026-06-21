import Lollipop.Internal.CertifiedEndpoint.Statement
import Lollipop.Internal.Manuscript.FormulaBridge
import Lollipop.Internal.Manuscript.RegionEquation

/-!
Manuscript-facing statement of Theorem 1.

The final proof stack in `TheoremOneFinal` uses the internal labeled extremum
`concreteS`.  `FormulaBridge` proves that this is the same as the manuscript's
sorted extremum `manuscriptS`, so this file exposes the displayed formula in
the paper's notation.
-/

namespace Lollipop
namespace TheoremOneManuscript

universe u

/-- Theorem 1 in the manuscript's displayed formula form, using the sorted
definition of `S(n)`. -/
def TheoremOneFormulaStatement (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  ∀ n : Nat,
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1

/-- Lower crossing-count realizations for the manuscript's sorted quadruples.
This is weaker than the older all-labeled-quadruple lower interface and
matches the displayed sorted maximum in the paper. -/
def SortedLowerCrossingRealization
    (Arrangement : Type*) (region crossings : Arrangement → Rat) (n : Nat) : Prop :=
  ∀ q : QuadVec n, q ∈ sortedQuadVecs n →
    ∃ A : Arrangement,
      crossings A = lowerCrossingsOfQuad q ∧
      region A = crossings A + (n : Rat) + 1

/-- Sorted lower crossing-count realizations for every size in a problem
family. -/
def SortedLowerCrossingRealizations
    (P : TheoremOne.ProblemFamily.{u})
    (crossings : (n : Nat) → P.Arrangement n → Rat) : Prop :=
  ∀ n : Nat,
    SortedLowerCrossingRealization (P.Arrangement n) (P.region n)
      (crossings n) n

/-- Sorted lower crossing-count realizations where the lower region equation
is supplied by incremental insertion data. -/
def SortedLowerIncrementalCrossingRealization
    (Arrangement : Type*) (region crossings : Arrangement → Rat) (n : Nat) : Prop :=
  ∀ q : QuadVec n, q ∈ sortedQuadVecs n →
    ∃ A : Arrangement,
      ∃ _ : IncrementalRegionData n (region A) (crossings A),
        crossings A = lowerCrossingsOfQuad q

/-- Incremental sorted lower crossing-count realizations for every size in a
problem family. -/
def SortedLowerIncrementalCrossingRealizations
    (P : TheoremOne.ProblemFamily.{u})
    (crossings : (n : Nat) → P.Arrangement n → Rat) : Prop :=
  ∀ n : Nat,
    SortedLowerIncrementalCrossingRealization (P.Arrangement n) (P.region n)
      (crossings n) n

/-- Monotone sorted lower crossing-count realizations.  For lower bounds the
construction does not need to prove the pair-sum is exactly Karlsson's table;
it is enough to produce at least that many crossings and satisfy the region
equation.  This interface is useful for concrete geometric blow-up proofs,
where proving lower witnesses can be easier than classifying every possible
carrier intersection. -/
def SortedLowerCrossingBoundRealization
    (Arrangement : Type*) (region crossings : Arrangement → Rat) (n : Nat) : Prop :=
  ∀ q : QuadVec n, q ∈ sortedQuadVecs n →
    ∃ A : Arrangement,
      lowerCrossingsOfQuad q ≤ crossings A ∧
      region A = crossings A + (n : Rat) + 1

/-- Monotone sorted lower crossing-count realizations for every size in a
problem family. -/
def SortedLowerCrossingBoundRealizations
    (P : TheoremOne.ProblemFamily.{u})
    (crossings : (n : Nat) → P.Arrangement n → Rat) : Prop :=
  ∀ n : Nat,
    SortedLowerCrossingBoundRealization (P.Arrangement n) (P.region n)
      (crossings n) n

/-- Incremental version of the monotone sorted lower interface. -/
def SortedLowerIncrementalCrossingBoundRealization
    (Arrangement : Type*) (region crossings : Arrangement → Rat) (n : Nat) : Prop :=
  ∀ q : QuadVec n, q ∈ sortedQuadVecs n →
    ∃ A : Arrangement,
      ∃ _ : IncrementalRegionData n (region A) (crossings A),
        lowerCrossingsOfQuad q ≤ crossings A

/-- Incremental monotone sorted lower realizations for every size in a problem
family. -/
def SortedLowerIncrementalCrossingBoundRealizations
    (P : TheoremOne.ProblemFamily.{u})
    (crossings : (n : Nat) → P.Arrangement n → Rat) : Prop :=
  ∀ n : Nat,
    SortedLowerIncrementalCrossingBoundRealization
      (P.Arrangement n) (P.region n) (crossings n) n

/-- Exact sorted lower realizations are a special case of the monotone lower
interface. -/
theorem sortedLowerCrossingBoundRealization_of_exact
    {Arrangement : Type*} {region crossings : Arrangement → Rat} {n : Nat}
    (hreal :
      SortedLowerCrossingRealization Arrangement region crossings n) :
    SortedLowerCrossingBoundRealization Arrangement region crossings n := by
  intro q hq
  rcases hreal q hq with ⟨A, hcross, hregion⟩
  exact ⟨A, by rw [hcross], hregion⟩

/-- Incremental monotone lower data imply the direct monotone lower
interface. -/
theorem sortedLowerCrossingBoundRealization_of_incremental_bound
    {Arrangement : Type*} {region crossings : Arrangement → Rat} {n : Nat}
    (hreal :
      SortedLowerIncrementalCrossingBoundRealization
        Arrangement region crossings n) :
    SortedLowerCrossingBoundRealization Arrangement region crossings n := by
  intro q hq
  rcases hreal q hq with ⟨A, D, hcross⟩
  exact ⟨A, hcross, D.target_eq_totalCrossings_add⟩

/-- Incremental monotone lower realizations for every size imply direct
monotone lower realizations for every size. -/
theorem sortedLowerCrossingBoundRealizations_of_incremental_bound
    (P : TheoremOne.ProblemFamily.{u})
    {crossings : (n : Nat) → P.Arrangement n → Rat}
    (hreal : SortedLowerIncrementalCrossingBoundRealizations P crossings) :
    SortedLowerCrossingBoundRealizations P crossings := by
  intro n
  exact sortedLowerCrossingBoundRealization_of_incremental_bound (hreal n)

/-- Incremental lower region data imply the ordinary sorted lower
crossing-count realization interface. -/
theorem sortedLowerCrossingRealization_of_incremental
    {Arrangement : Type*} {region crossings : Arrangement → Rat} {n : Nat}
    (hreal :
      SortedLowerIncrementalCrossingRealization Arrangement region crossings n) :
    SortedLowerCrossingRealization Arrangement region crossings n := by
  intro q hq
  rcases hreal q hq with ⟨A, hregion, hcross⟩
  exact ⟨A, hcross, hregion.target_eq_totalCrossings_add⟩

/-- Incremental lower realizations for every size imply the ordinary sorted
lower interface. -/
theorem sortedLowerCrossingRealizations_of_incremental
    (P : TheoremOne.ProblemFamily.{u})
    {crossings : (n : Nat) → P.Arrangement n → Rat}
    (hreal : SortedLowerIncrementalCrossingRealizations P crossings) :
    SortedLowerCrossingRealizations P crossings := by
  intro n
  exact sortedLowerCrossingRealization_of_incremental (hreal n)

/-- The manuscript's sorted finite maximum is attained. -/
theorem exists_quadVecExcess_eq_manuscriptS (n : Nat) :
    ∃ q : QuadVec n, q ∈ sortedQuadVecs n ∧ quadVecExcess q = manuscriptS n := by
  unfold manuscriptS
  rcases Finset.exists_mem_eq_sup' (sortedQuadVecs_nonempty n) quadVecExcess with
    ⟨q, hq, hqmax⟩
  exact ⟨q, hq, hqmax.symm⟩

/-- A sorted quadruple attaining the manuscript extremum gives the candidate
lower region count. -/
theorem lowerRegionsOfQuad_eq_candidate_of_manuscript_excess
    {n : Nat} {q : QuadVec n}
    (hq : q ∈ sortedQuadVecs n)
    (hmax : quadVecExcess q = manuscriptS n) :
    lowerRegionsOfQuad q = candidateRegions n := by
  have hquad : q ∈ quadVecs n := by
    rw [sortedQuadVecs, Finset.mem_filter] at hq
    exact hq.1
  apply lowerRegionsOfQuad_eq_candidate_of_excess hquad
  rwa [manuscriptS_eq_concreteS] at hmax

/-- Sorted lower crossing-count realizations are enough to attain the
candidate region count. -/
theorem exists_region_eq_candidate_of_sortedLowerCrossingRealization
    {Arrangement : Type*} {region crossings : Arrangement → Rat} {n : Nat}
    (hreal : SortedLowerCrossingRealization Arrangement region crossings n) :
    ∃ A : Arrangement, region A = candidateRegions n := by
  rcases exists_quadVecExcess_eq_manuscriptS n with ⟨q, hq, hmax⟩
  rcases hreal q hq with ⟨A, hcross, hregion⟩
  refine ⟨A, ?_⟩
  have hregionLower : region A = lowerRegionsOfQuad q := by
    rw [hregion, hcross]
    rfl
  rw [hregionLower, lowerRegionsOfQuad_eq_candidate_of_manuscript_excess hq hmax]

/-- Monotone sorted lower realizations produce an arrangement whose region
count is at least the candidate.  Combined with the already-proved upper
bound, this is enough for exactness, and it avoids requiring the lower
construction to classify all extra intersections away. -/
theorem exists_candidate_le_region_of_sortedLowerCrossingBoundRealization
    {Arrangement : Type*} {region crossings : Arrangement → Rat} {n : Nat}
    (hreal :
      SortedLowerCrossingBoundRealization Arrangement region crossings n) :
    ∃ A : Arrangement, candidateRegions n ≤ region A := by
  rcases exists_quadVecExcess_eq_manuscriptS n with ⟨q, hq, hmax⟩
  rcases hreal q hq with ⟨A, hcross, hregion⟩
  refine ⟨A, ?_⟩
  have hcandidate :
      candidateRegions n = lowerRegionsOfQuad q :=
    (lowerRegionsOfQuad_eq_candidate_of_manuscript_excess hq hmax).symm
  rw [hcandidate, lowerRegionsOfQuad, hregion]
  linarith

/-- Sorted lower crossing-count realizations give lower attainment in the
`Nat.choose` candidate form. -/
theorem lower_attainment_of_sortedLowerCrossingRealizations_choose
    (P : TheoremOne.ProblemFamily.{u})
    {crossings : (n : Nat) → P.Arrangement n → Rat}
    (hlower : SortedLowerCrossingRealizations P crossings) :
    ∀ n : Nat, ∃ A : P.Arrangement n,
      P.region n A = candidateRegionsChoose n := by
  intro n
  rcases exists_region_eq_candidate_of_sortedLowerCrossingRealization
      (hlower n) with ⟨A, hA⟩
  exact ⟨A, by simpa [candidateRegionsChoose_eq_candidateRegions] using hA⟩

/-- Monotone sorted lower crossing-count realizations give lower attainment as
an inequality in the `Nat.choose` candidate form. -/
theorem lower_bound_attainment_of_sortedLowerCrossingBoundRealizations_choose
    (P : TheoremOne.ProblemFamily.{u})
    {crossings : (n : Nat) → P.Arrangement n → Rat}
    (hlower : SortedLowerCrossingBoundRealizations P crossings) :
    ∀ n : Nat, ∃ A : P.Arrangement n,
      candidateRegionsChoose n ≤ P.region n A := by
  intro n
  rcases exists_candidate_le_region_of_sortedLowerCrossingBoundRealization
      (hlower n) with ⟨A, hA⟩
  exact ⟨A, by simpa [candidateRegionsChoose_eq_candidateRegions] using hA⟩

/-- Incremental sorted lower realizations give lower attainment in the
`Nat.choose` candidate form. -/
theorem lower_attainment_of_sortedLowerIncrementalCrossingRealizations_choose
    (P : TheoremOne.ProblemFamily.{u})
    {crossings : (n : Nat) → P.Arrangement n → Rat}
    (hlower : SortedLowerIncrementalCrossingRealizations P crossings) :
    ∀ n : Nat, ∃ A : P.Arrangement n,
      P.region n A = candidateRegionsChoose n := by
  exact
    lower_attainment_of_sortedLowerCrossingRealizations_choose
      P (sortedLowerCrossingRealizations_of_incremental P hlower)

/-- Incremental monotone sorted lower realizations give lower attainment as an
inequality in the `Nat.choose` candidate form. -/
theorem lower_bound_attainment_of_sortedLowerIncrementalCrossingBoundRealizations_choose
    (P : TheoremOne.ProblemFamily.{u})
    {crossings : (n : Nat) → P.Arrangement n → Rat}
    (hlower : SortedLowerIncrementalCrossingBoundRealizations P crossings) :
    ∀ n : Nat, ∃ A : P.Arrangement n,
      candidateRegionsChoose n ≤ P.region n A := by
  exact
    lower_bound_attainment_of_sortedLowerCrossingBoundRealizations_choose
      P (sortedLowerCrossingBoundRealizations_of_incremental_bound P hlower)

/-- Upper bound plus monotone lower attainment imply the maximum statement.
The lower construction need only reach at least the candidate value; the upper
bound then forces equality for the chosen arrangement. -/
theorem maximumStatement_of_choose_upper_bound_and_lower_bound_attainment
    (P : TheoremOne.ProblemFamily.{u})
    (hupper :
      ∀ n : Nat, ∀ A : P.Arrangement n,
        P.region n A ≤ candidateRegionsChoose n)
    (hlower :
      ∀ n : Nat, ∃ A : P.Arrangement n,
        candidateRegionsChoose n ≤ P.region n A) :
    TheoremOne.MaximumStatement P := by
  intro n
  constructor
  · rcases hlower n with ⟨A, hA_lower⟩
    exact ⟨A, le_antisymm (hupper n A) hA_lower⟩
  · intro y hy
    rcases hy with ⟨A, rfl⟩
    exact hupper n A

/-- Strongest current manuscript-facing upper/lower package.  Compared with
`TheoremOneFinal.CanonicalExactCoordinateGeometricCrossingModelSubtheorems`,
the lower side only asks for sorted Karlsson crossing-count realizations. -/
structure CanonicalExactCoordinateGeometricCrossingModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) : Prop where
  upper_certificates :
    TheoremOneEndToEnd.PairwiseCanonicalExactCoordinateGeometricUpperCertificates P
  lower_sorted_crossing_realizations :
    ∃ lower_crossings : (n : Nat) → P.Arrangement n → Rat,
      SortedLowerCrossingRealizations P lower_crossings

/-- The corresponding package for a family with a named maximum-count
function. -/
def MaxCanonicalExactCoordinateGeometricCrossingModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  CanonicalExactCoordinateGeometricCrossingModelSubtheorems P.toProblemFamily

/-- Monotone manuscript-facing upper/lower package.  The upper side is the
same exact-coordinate certificate package; the lower side only has to realize
arrangements whose crossing count is at least the sorted Karlsson value. -/
structure CanonicalExactCoordinateGeometricCrossingModelBoundSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) : Prop where
  upper_certificates :
    TheoremOneEndToEnd.PairwiseCanonicalExactCoordinateGeometricUpperCertificates P
  lower_sorted_crossing_bound_realizations :
    ∃ lower_crossings : (n : Nat) → P.Arrangement n → Rat,
      SortedLowerCrossingBoundRealizations P lower_crossings

/-- Monotone package for a family with a named maximum-count function. -/
def MaxCanonicalExactCoordinateGeometricCrossingModelBoundSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  CanonicalExactCoordinateGeometricCrossingModelBoundSubtheorems
    P.toProblemFamily

/-- Upper bound from the manuscript-facing exact coordinate package. -/
theorem upper_bound_proven_from_canonical_exact_coordinate_geometric_crossing_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : CanonicalExactCoordinateGeometricCrossingModelSubtheorems P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact
    TheoremOneEndToEnd.upper_bound_of_pairwise_canonical_exact_coordinate_geometric_certificates
      P h.upper_certificates

/-- Upper bound from the monotone manuscript-facing package. -/
theorem upper_bound_proven_from_canonical_exact_coordinate_geometric_crossing_bound_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : CanonicalExactCoordinateGeometricCrossingModelBoundSubtheorems P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact
    TheoremOneEndToEnd.upper_bound_of_pairwise_canonical_exact_coordinate_geometric_certificates
      P h.upper_certificates

/-- Maximum-form Theorem 1 from exact upper data and sorted-only lower
crossing-count realizations. -/
theorem theorem_one_statement_proven_from_canonical_exact_coordinate_geometric_crossing_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : CanonicalExactCoordinateGeometricCrossingModelSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  rcases h.lower_sorted_crossing_realizations with ⟨lower_crossings, hlower⟩
  exact
    TheoremOneFormal.maximumStatement_of_choose_upper_bound_and_lower_attainment
      P
      (upper_bound_proven_from_canonical_exact_coordinate_geometric_crossing_certificates
        P h)
      (lower_attainment_of_sortedLowerCrossingRealizations_choose
        P (crossings := lower_crossings) hlower)

/-- Maximum-form Theorem 1 from exact upper data and monotone sorted lower
crossing-count realizations. -/
theorem theorem_one_statement_proven_from_canonical_exact_coordinate_geometric_crossing_bound_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : CanonicalExactCoordinateGeometricCrossingModelBoundSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  rcases h.lower_sorted_crossing_bound_realizations with
    ⟨lower_crossings, hlower⟩
  exact
    maximumStatement_of_choose_upper_bound_and_lower_bound_attainment
      P
      (upper_bound_proven_from_canonical_exact_coordinate_geometric_crossing_bound_certificates
        P h)
      (lower_bound_attainment_of_sortedLowerCrossingBoundRealizations_choose
        P (crossings := lower_crossings) hlower)

/-- Formula-form Theorem 1 with the manuscript's sorted `S(n)`, from exact
upper data and sorted-only lower crossing-count realizations. -/
theorem theorem_one_formula_statement_proven_from_manuscript_canonical_exact_coordinate_geometric_crossing_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxCanonicalExactCoordinateGeometricCrossingModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  intro n
  have hmax :
      TheoremOne.MaximumStatement P.toProblemFamily :=
    theorem_one_statement_proven_from_canonical_exact_coordinate_geometric_crossing_certificates
      P.toProblemFamily h
  have hformula := TheoremOne.formulaStatement_of_maximumStatement P hmax n
  rw [hformula]
  unfold candidateRegionsChoose
  rw [← manuscriptS_eq_concreteS n]

/-- Formula-form Theorem 1 with the manuscript's sorted `S(n)`, from exact
upper data and monotone sorted lower crossing-count realizations. -/
theorem theorem_one_formula_statement_proven_from_manuscript_canonical_exact_coordinate_geometric_crossing_bound_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxCanonicalExactCoordinateGeometricCrossingModelBoundSubtheorems P) :
    TheoremOneFormulaStatement P := by
  intro n
  have hmax :
      TheoremOne.MaximumStatement P.toProblemFamily :=
    theorem_one_statement_proven_from_canonical_exact_coordinate_geometric_crossing_bound_certificates
      P.toProblemFamily h
  have hformula := TheoremOne.formulaStatement_of_maximumStatement P hmax n
  rw [hformula]
  unfold candidateRegionsChoose
  rw [← manuscriptS_eq_concreteS n]

/-- The final theorem using the manuscript's sorted `S(n)`, proved from the
ordinary final theorem plus the sorted/labeled extremum bridge. -/
theorem theorem_one_formula_statement_proven_from_canonical_exact_coordinate_geometric_crossing_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : TheoremOneFinal.MaxCanonicalExactCoordinateGeometricCrossingModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  intro n
  have hfinal :=
    TheoremOneFinal.theorem_one_formula_at_proven_from_canonical_exact_coordinate_geometric_crossing_certificates
      P h n
  rw [hfinal, manuscriptS_eq_concreteS]

/-- Single-size version of the manuscript-facing displayed formula. -/
theorem theorem_one_formula_at_proven_from_canonical_exact_coordinate_geometric_crossing_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : TheoremOneFinal.MaxCanonicalExactCoordinateGeometricCrossingModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact
    theorem_one_formula_statement_proven_from_canonical_exact_coordinate_geometric_crossing_certificates
      P h n

end TheoremOneManuscript
end Lollipop
