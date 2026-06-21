import Lollipop.Internal.Manuscript.FormalizedProof.ManuscriptLemmas

/-!
Formalized manuscript proof of Theorem 1.

The final theorem below is deliberately stated from the strongest currently
formalized manuscript subtheorem package.  Every generic argument on the path
to the formula is proved in the imported Lean files; the package fields are
exactly the remaining model-specific construction certificates.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace FormalizedProof

universe u

/-- Theorem 1 from the strongest current manuscript subtheorem package:
primitive carrier component savings for the upper bound and named incremental
Karlsson blow-up data for the lower bound. -/
theorem theorem_one_from_formalized_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : StrongestKnownTheoremOneSubtheorems P) :
    FinalTheoremOneStatement P := by
  exact theorem_one_from_component_savings_primitive_carrier_subtheorems P h

/-- Single-size Theorem 1 formula from the strongest current manuscript
subtheorem package. -/
theorem theorem_one_at_from_formalized_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : StrongestKnownTheoremOneSubtheorems P)
    (n : Nat) :
    FinalTheoremOneAtStatement P n := by
  exact theorem_one_from_formalized_subtheorems P h n

/-- Theorem 1 from direct whole-carrier primitive savings plus named
incremental Karlsson blow-up data. -/
theorem theorem_one_from_direct_savings_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : DirectSavingsTheoremOneSubtheorems P) :
    FinalTheoremOneStatement P := by
  exact theorem_one_from_direct_savings_primitive_carrier_subtheorems P h

/-- Single-size formula from direct whole-carrier primitive savings plus named
incremental Karlsson blow-up data. -/
theorem theorem_one_at_from_direct_savings_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : DirectSavingsTheoremOneSubtheorems P)
    (n : Nat) :
    FinalTheoremOneAtStatement P n := by
  exact theorem_one_from_direct_savings_subtheorems P h n

/-- Theorem 1 from primitive carrier component savings plus pairwise
Karlsson lower construction data. -/
theorem theorem_one_from_pairwise_lower_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PairwiseLowerTheoremOneSubtheorems P) :
    FinalTheoremOneStatement P := by
  exact
    theorem_one_from_component_savings_pairwise_lower_primitive_carrier_subtheorems
      P h

/-- Single-size formula from primitive carrier component savings plus
pairwise Karlsson lower construction data. -/
theorem theorem_one_at_from_pairwise_lower_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : PairwiseLowerTheoremOneSubtheorems P)
    (n : Nat) :
    FinalTheoremOneAtStatement P n := by
  exact theorem_one_from_pairwise_lower_subtheorems P h n

/-- Theorem 1 from direct whole-carrier primitive savings plus pairwise
Karlsson lower construction data. -/
theorem theorem_one_from_direct_savings_pairwise_lower_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : DirectSavingsPairwiseLowerTheoremOneSubtheorems P) :
    FinalTheoremOneStatement P := by
  exact
    theorem_one_from_direct_savings_pairwise_lower_primitive_carrier_subtheorems
      P h

/-- Single-size formula from direct whole-carrier primitive savings plus
pairwise Karlsson lower construction data. -/
theorem theorem_one_at_from_direct_savings_pairwise_lower_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : DirectSavingsPairwiseLowerTheoremOneSubtheorems P)
    (n : Nat) :
    FinalTheoremOneAtStatement P n := by
  exact theorem_one_from_direct_savings_pairwise_lower_subtheorems P h n

/-- Theorem 1 from primitive carrier component savings plus monotone pairwise
Karlsson lower construction data. -/
theorem theorem_one_from_monotone_pairwise_lower_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MonotonePairwiseLowerTheoremOneSubtheorems P) :
    FinalTheoremOneStatement P := by
  exact
    theorem_one_from_component_savings_monotone_pairwise_lower_primitive_carrier_subtheorems
      P h

/-- Single-size formula from primitive carrier component savings plus
monotone pairwise Karlsson lower construction data. -/
theorem theorem_one_at_from_monotone_pairwise_lower_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MonotonePairwiseLowerTheoremOneSubtheorems P)
    (n : Nat) :
    FinalTheoremOneAtStatement P n := by
  exact theorem_one_from_monotone_pairwise_lower_subtheorems P h n

/-- Theorem 1 from direct whole-carrier primitive savings plus monotone
pairwise Karlsson lower construction data. -/
theorem theorem_one_from_direct_savings_monotone_pairwise_lower_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : DirectSavingsMonotonePairwiseLowerTheoremOneSubtheorems P) :
    FinalTheoremOneStatement P := by
  exact
    theorem_one_from_direct_savings_monotone_pairwise_lower_primitive_carrier_subtheorems
      P h

/-- Single-size formula from direct whole-carrier primitive savings plus
monotone pairwise Karlsson lower construction data. -/
theorem theorem_one_at_from_direct_savings_monotone_pairwise_lower_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : DirectSavingsMonotonePairwiseLowerTheoremOneSubtheorems P)
    (n : Nat) :
    FinalTheoremOneAtStatement P n := by
  exact theorem_one_from_direct_savings_monotone_pairwise_lower_subtheorems
    P h n

/-- Theorem 1 from primitive carrier component savings plus Karlsson's
four-base/local-blow-up lower construction package. -/
theorem theorem_one_from_karlsson_base_lower_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : KarlssonBaseLowerTheoremOneSubtheorems P) :
    FinalTheoremOneStatement P := by
  exact
    theorem_one_from_component_savings_karlsson_base_lower_primitive_carrier_subtheorems
      P h

/-- Single-size formula from primitive carrier component savings plus
Karlsson's four-base/local-blow-up lower construction package. -/
theorem theorem_one_at_from_karlsson_base_lower_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : KarlssonBaseLowerTheoremOneSubtheorems P)
    (n : Nat) :
    FinalTheoremOneAtStatement P n := by
  exact theorem_one_from_karlsson_base_lower_subtheorems P h n

/-- Theorem 1 from direct whole-carrier primitive savings plus Karlsson's
four-base/local-blow-up lower construction package. -/
theorem theorem_one_from_direct_savings_karlsson_base_lower_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : DirectSavingsKarlssonBaseLowerTheoremOneSubtheorems P) :
    FinalTheoremOneStatement P := by
  exact
    theorem_one_from_direct_savings_karlsson_base_lower_primitive_carrier_subtheorems
      P h

/-- Single-size formula from direct whole-carrier primitive savings plus
Karlsson's four-base/local-blow-up lower construction package. -/
theorem theorem_one_at_from_direct_savings_karlsson_base_lower_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : DirectSavingsKarlssonBaseLowerTheoremOneSubtheorems P)
    (n : Nat) :
    FinalTheoremOneAtStatement P n := by
  exact theorem_one_from_direct_savings_karlsson_base_lower_subtheorems P h n

/-- Theorem 1 from the slightly weaker component-bound package, where
close/intriguing savings are already supplied as numeric crossing bounds. -/
theorem theorem_one_from_component_bound_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ComponentBoundTheoremOneSubtheorems P) :
    FinalTheoremOneStatement P := by
  exact theorem_one_from_component_bound_primitive_carrier_subtheorems P h

/-- Single-size formula from the component-bound package. -/
theorem theorem_one_at_from_component_bound_subtheorems
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : ComponentBoundTheoremOneSubtheorems P)
    (n : Nat) :
    FinalTheoremOneAtStatement P n := by
  exact theorem_one_from_component_bound_subtheorems P h n

end FormalizedProof
end TheoremOneManuscript
end Lollipop
