import Lollipop.Internal.ColoredTuran.GeometricReduction
import Lollipop.Internal.Manuscript.ConcreteModel

/-!
Manuscript-style geometric inputs for Theorem 1.

`ConcreteModel.lean` exposes a strong coordinate/canonical endpoint.  This
file also exposes the more literal interface used in the manuscript: for every
arrangement, provide close and intriguing predicates, the pairwise crossing
table bounds, and the four-subset and five-subset close/intriguing facts.  Lean then
constructs the colored graph and runs the already proved Zykov, weighted
Turan, blocker, matrix, and lower-attainment stacks.
-/

namespace Lollipop
namespace TheoremOneManuscript

universe u

/-- The manuscript's pair score
`1_{not close} + 1_{not intriguing} + 1_{not close and not intriguing}`. -/
noncomputable def manuscriptPairScore
    {V : Type*} (close intriguing : V → V → Prop) (i j : V) : Rat := by
  classical
  exact
    (if close i j then 0 else 1) +
    (if intriguing i j then 0 else 1) +
    (if close i j ∨ intriguing i j then 0 else 1)

/-- Global paper-style geometric upper data for every arrangement.  This is
the manuscript's geometric input written as extractor functions: close and
intriguing predicates, an exact pairwise crossing table, the four pointwise
crossing bounds including the baseline `<= 7` case, the close-pair-in-four and
intriguing-pair-in-five facts, and the total crossing/region equation. -/
structure ManuscriptGeometricUpperData
    (P : TheoremOne.ProblemFamily.{u}) where
  crossings : ∀ n : Nat, P.Arrangement n → Rat
  close : ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Prop
  intriguing : ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Prop
  close_decidable :
    ∀ n : Nat, ∀ A : P.Arrangement n, DecidableRel (close n A)
  intriguing_decidable :
    ∀ n : Nat, ∀ A : P.Arrangement n, DecidableRel (intriguing n A)
  close_symm :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n,
      close n A i j ↔ close n A j i
  intriguing_symm :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n,
      intriguing n A i j ↔ intriguing n A j i
  cross : ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  crossings_le_pairSum :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      crossings n A ≤ pairSum n (cross n A)
  cross_le_general :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      cross n A i j ≤ 7
  cross_le_close :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      close n A i j → cross n A i j ≤ 5
  cross_le_intriguing :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      intriguing n A i j → cross n A i j ≤ 5
  cross_le_close_intriguing :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      close n A i j → intriguing n A i j → cross n A i j ≤ 4
  close_pair_in_every_four :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ t : Finset (Fin n), t.card = 4 →
      ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ close n A i j
  intriguing_pair_in_every_five :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ t : Finset (Fin n), t.card = 5 →
      ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ intriguing n A i j
  regions_eq :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A = crossings n A + (n : Rat) + 1

namespace ManuscriptGeometricUpperData

/-- The four pointwise geometric crossing bounds imply the manuscript's
displayed estimate
`c_ij <= 4 + 1_D + 1_E + 1_{D cap E}`. -/
theorem pair_crossing_le_four_plus_score
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ManuscriptGeometricUpperData P)
    (n : Nat) (A : P.Arrangement n) :
    ∀ i j : Fin n, i < j →
      h.cross n A i j ≤
        4 + manuscriptPairScore (h.close n A) (h.intriguing n A) i j := by
  intro i j hij
  unfold manuscriptPairScore
  by_cases hc : h.close n A i j
  · by_cases hi : h.intriguing n A i j
    · have hcross := h.cross_le_close_intriguing n A i j hij hc hi
      simp [hc, hi] at hcross ⊢
      linarith
    · have hcross := h.cross_le_close n A i j hij hc
      simp [hc, hi] at hcross ⊢
      linarith
  · by_cases hi : h.intriguing n A i j
    · have hcross := h.cross_le_intriguing n A i j hij hi
      simp [hc, hi] at hcross ⊢
      linarith
    · have hcross := h.cross_le_general n A i j hij
      simp [hc, hi] at hcross ⊢
      linarith

/-- Convert global paper-style geometric extractors into the upper
certificates used by the geometric reduction. -/
noncomputable def toPairwiseGeometricUpperCertificates
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ManuscriptGeometricUpperData P) :
    TheoremOneEndToEnd.PairwiseGeometricUpperCertificates P := by
  intro n A
  exact
    ⟨{ nNat := n
       crossings := h.crossings n A
       regions := P.region n A
       close := h.close n A
       intriguing := h.intriguing n A
       close_decidable := h.close_decidable n A
       intriguing_decidable := h.intriguing_decidable n A
       close_symm := h.close_symm n A
       intriguing_symm := h.intriguing_symm n A
       cross := h.cross n A
       crossings_le_pairSum := h.crossings_le_pairSum n A
       cross_le_general := h.cross_le_general n A
       cross_le_close := h.cross_le_close n A
       cross_le_intriguing := h.cross_le_intriguing n A
       cross_le_close_intriguing := h.cross_le_close_intriguing n A
       close_pair_in_every_four := h.close_pair_in_every_four n A
       intriguing_pair_in_every_five := h.intriguing_pair_in_every_five n A
       regions_eq := h.regions_eq n A },
      rfl, rfl⟩

end ManuscriptGeometricUpperData

/-- Paper-style geometric upper data where the region equation is derived from
incremental insertion data rather than assumed directly. -/
structure ManuscriptGeometricIncrementalUpperData
    (P : TheoremOne.ProblemFamily.{u}) where
  crossings : ∀ n : Nat, P.Arrangement n → Rat
  close : ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Prop
  intriguing : ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Prop
  close_decidable :
    ∀ n : Nat, ∀ A : P.Arrangement n, DecidableRel (close n A)
  intriguing_decidable :
    ∀ n : Nat, ∀ A : P.Arrangement n, DecidableRel (intriguing n A)
  close_symm :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n,
      close n A i j ↔ close n A j i
  intriguing_symm :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n,
      intriguing n A i j ↔ intriguing n A j i
  cross : ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  crossings_le_pairSum :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      crossings n A ≤ pairSum n (cross n A)
  cross_le_general :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      cross n A i j ≤ 7
  cross_le_close :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      close n A i j → cross n A i j ≤ 5
  cross_le_intriguing :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      intriguing n A i j → cross n A i j ≤ 5
  cross_le_close_intriguing :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      close n A i j → intriguing n A i j → cross n A i j ≤ 4
  close_pair_in_every_four :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ t : Finset (Fin n), t.card = 4 →
      ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ close n A i j
  intriguing_pair_in_every_five :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ t : Finset (Fin n), t.card = 5 →
      ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ intriguing n A i j
  region_increment :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      IncrementalRegionData n (P.region n A) (crossings n A)

namespace ManuscriptGeometricIncrementalUpperData

/-- Derive the direct region-equation upper data from incremental insertion
data. -/
def toManuscriptGeometricUpperData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ManuscriptGeometricIncrementalUpperData P) :
    ManuscriptGeometricUpperData P where
  crossings := h.crossings
  close := h.close
  intriguing := h.intriguing
  close_decidable := h.close_decidable
  intriguing_decidable := h.intriguing_decidable
  close_symm := h.close_symm
  intriguing_symm := h.intriguing_symm
  cross := h.cross
  crossings_le_pairSum := h.crossings_le_pairSum
  cross_le_general := h.cross_le_general
  cross_le_close := h.cross_le_close
  cross_le_intriguing := h.cross_le_intriguing
  cross_le_close_intriguing := h.cross_le_close_intriguing
  close_pair_in_every_four := h.close_pair_in_every_four
  intriguing_pair_in_every_five := h.intriguing_pair_in_every_five
  regions_eq := by
    intro n A
    exact (h.region_increment n A).target_eq_totalCrossings_add

/-- The incremental upper-data variant also implies the manuscript's displayed
pointwise pair estimate. -/
theorem pair_crossing_le_four_plus_score
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ManuscriptGeometricIncrementalUpperData P)
    (n : Nat) (A : P.Arrangement n) :
    ∀ i j : Fin n, i < j →
      h.cross n A i j ≤
        4 + manuscriptPairScore (h.close n A) (h.intriguing n A) i j := by
  exact h.toManuscriptGeometricUpperData.pair_crossing_le_four_plus_score n A

/-- Convert incremental global paper-style geometric data into the upper
certificates used by the geometric reduction. -/
noncomputable def toPairwiseGeometricUpperCertificates
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ManuscriptGeometricIncrementalUpperData P) :
    TheoremOneEndToEnd.PairwiseGeometricUpperCertificates P :=
  h.toManuscriptGeometricUpperData.toPairwiseGeometricUpperCertificates

end ManuscriptGeometricIncrementalUpperData

/-- Manuscript-style subtheorems: the upper input is exactly the abstract
close/intriguing geometric package, and the lower input is sorted Karlsson
crossing-count realization data. -/
structure ManuscriptGeometricModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : TheoremOneEndToEnd.PairwiseGeometricUpperCertificates P
  lower_karlsson : SortedKarlssonLowerData P

/-- Manuscript-style subtheorems with the lower region equation supplied by
incremental insertion data. -/
structure ManuscriptGeometricIncrementalModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : TheoremOneEndToEnd.PairwiseGeometricUpperCertificates P
  lower_karlsson : SortedKarlssonIncrementalLowerData P

/-- Global-data version of the paper-style geometric subtheorems. -/
structure ManuscriptGeometricDataSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : ManuscriptGeometricUpperData P
  lower_karlsson : SortedKarlssonLowerData P

/-- Global-data version where both upper and lower region equations are
derived from incremental insertion data. -/
structure ManuscriptGeometricFullyIncrementalDataSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : ManuscriptGeometricIncrementalUpperData P
  lower_karlsson : SortedKarlssonIncrementalLowerData P

namespace ManuscriptGeometricIncrementalModelSubtheorems

/-- Forget lower incremental proof details after Lean derives
`regions = crossings + n + 1`. -/
def toManuscriptGeometricModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ManuscriptGeometricIncrementalModelSubtheorems P) :
    ManuscriptGeometricModelSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson := h.lower_karlsson.toSortedKarlssonLowerData

end ManuscriptGeometricIncrementalModelSubtheorems

namespace ManuscriptGeometricDataSubtheorems

/-- Convert global paper-style geometric data to the certificate-style
manuscript package. -/
noncomputable def toManuscriptGeometricModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ManuscriptGeometricDataSubtheorems P) :
    ManuscriptGeometricModelSubtheorems P where
  upper_geometry := h.upper_geometry.toPairwiseGeometricUpperCertificates
  lower_karlsson := h.lower_karlsson

end ManuscriptGeometricDataSubtheorems

namespace ManuscriptGeometricFullyIncrementalDataSubtheorems

/-- Convert fully incremental global paper-style geometric data to the
incremental certificate-style manuscript package. -/
noncomputable def toManuscriptGeometricIncrementalModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ManuscriptGeometricFullyIncrementalDataSubtheorems P) :
    ManuscriptGeometricIncrementalModelSubtheorems P where
  upper_geometry := h.upper_geometry.toPairwiseGeometricUpperCertificates
  lower_karlsson := h.lower_karlsson

end ManuscriptGeometricFullyIncrementalDataSubtheorems

/-- Upper bound from the manuscript's abstract close/intriguing geometric
package. -/
theorem upper_bound_proven_from_manuscript_geometric_model
    (P : TheoremOne.ProblemFamily.{u})
    (h : ManuscriptGeometricModelSubtheorems P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact
    TheoremOneEndToEnd.upper_bound_of_pairwise_geometric_certificates
      P h.upper_geometry

/-- Maximum-form Theorem 1 from manuscript-style geometric upper data and
sorted Karlsson lower data. -/
theorem theorem_one_statement_proven_from_manuscript_geometric_model
    (P : TheoremOne.ProblemFamily.{u})
    (h : ManuscriptGeometricModelSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact
    TheoremOneFormal.maximumStatement_of_choose_upper_bound_and_lower_attainment
      P
      (upper_bound_proven_from_manuscript_geometric_model P h)
      (lower_attainment_of_sortedLowerCrossingRealizations_choose
        P (crossings := h.lower_karlsson.crossings) h.lower_karlsson.realizations)

/-- Maximum-form Theorem 1 from manuscript-style geometric upper data and
incremental sorted Karlsson lower data. -/
theorem theorem_one_statement_proven_from_manuscript_geometric_incremental_model
    (P : TheoremOne.ProblemFamily.{u})
    (h : ManuscriptGeometricIncrementalModelSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_manuscript_geometric_model
    P h.toManuscriptGeometricModelSubtheorems

/-- Maximum-form Theorem 1 from global paper-style geometric upper data and
sorted Karlsson lower data. -/
theorem theorem_one_statement_proven_from_manuscript_geometric_data
    (P : TheoremOne.ProblemFamily.{u})
    (h : ManuscriptGeometricDataSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_manuscript_geometric_model
    P h.toManuscriptGeometricModelSubtheorems

/-- Maximum-form Theorem 1 from fully incremental global paper-style
geometric data. -/
theorem theorem_one_statement_proven_from_manuscript_geometric_fully_incremental_data
    (P : TheoremOne.ProblemFamily.{u})
    (h : ManuscriptGeometricFullyIncrementalDataSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_manuscript_geometric_incremental_model
    P h.toManuscriptGeometricIncrementalModelSubtheorems

/-- Manuscript-style geometric obligations for a family with a named maximum
count function. -/
def MaxManuscriptGeometricModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ManuscriptGeometricModelSubtheorems P.toProblemFamily

/-- Incremental manuscript-style geometric obligations for a family with a
named maximum count function. -/
def MaxManuscriptGeometricIncrementalModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ManuscriptGeometricIncrementalModelSubtheorems P.toProblemFamily

/-- Global paper-style geometric obligations for a family with a named maximum
count function. -/
def MaxManuscriptGeometricDataSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ManuscriptGeometricDataSubtheorems P.toProblemFamily

/-- Fully incremental global paper-style geometric obligations for a family
with a named maximum count function. -/
def MaxManuscriptGeometricFullyIncrementalDataSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ManuscriptGeometricFullyIncrementalDataSubtheorems P.toProblemFamily

/-- Formula-form Theorem 1 with the manuscript's sorted `S(n)`, from the
paper-style close/intriguing geometric input and sorted Karlsson lower data. -/
theorem theorem_one_formula_statement_proven_from_manuscript_geometric_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  intro n
  have hmax :
      TheoremOne.MaximumStatement P.toProblemFamily :=
    theorem_one_statement_proven_from_manuscript_geometric_model
      P.toProblemFamily h
  have hformula := TheoremOne.formulaStatement_of_maximumStatement P hmax n
  rw [hformula]
  unfold candidateRegionsChoose
  rw [← manuscriptS_eq_concreteS n]

/-- Formula-form Theorem 1 with the manuscript's sorted `S(n)`, from the
paper-style close/intriguing geometric input and incremental sorted Karlsson
lower data. -/
theorem theorem_one_formula_statement_proven_from_manuscript_geometric_incremental_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricIncrementalModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_manuscript_geometric_model
    P h.toManuscriptGeometricModelSubtheorems

/-- Formula-form Theorem 1 from global paper-style geometric upper data and
sorted Karlsson lower data. -/
theorem theorem_one_formula_statement_proven_from_manuscript_geometric_data
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricDataSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_manuscript_geometric_model
    P h.toManuscriptGeometricModelSubtheorems

/-- Formula-form Theorem 1 from fully incremental global paper-style
geometric data. -/
theorem theorem_one_formula_statement_proven_from_manuscript_geometric_fully_incremental_data
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricFullyIncrementalDataSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_manuscript_geometric_incremental_model
    P h.toManuscriptGeometricIncrementalModelSubtheorems

/-- Single-size displayed formula from paper-style close/intriguing
geometric input and sorted Karlsson lower data. -/
theorem theorem_one_formula_at_proven_from_manuscript_geometric_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_manuscript_geometric_model P h n

/-- Single-size displayed formula from paper-style close/intriguing
geometric input and incremental sorted Karlsson lower data. -/
theorem theorem_one_formula_at_proven_from_manuscript_geometric_incremental_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricIncrementalModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_manuscript_geometric_incremental_model P h n

/-- Single-size displayed formula from global paper-style geometric upper data
and sorted Karlsson lower data. -/
theorem theorem_one_formula_at_proven_from_manuscript_geometric_data
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricDataSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_manuscript_geometric_data P h n

/-- Single-size displayed formula from fully incremental global paper-style
geometric data. -/
theorem theorem_one_formula_at_proven_from_manuscript_geometric_fully_incremental_data
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxManuscriptGeometricFullyIncrementalDataSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_manuscript_geometric_fully_incremental_data P h n

end TheoremOneManuscript
end Lollipop
