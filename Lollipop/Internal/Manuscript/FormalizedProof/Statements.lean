import Lollipop.Internal.Manuscript.Formalization.FromComponentBounds

/-!
Manuscript-shaped statement layer for Theorem 1.

This folder is intentionally separate from the existing development.  It
presents the final theorem target and the strongest currently formalized
subtheorem package in the order used by the manuscript, while reusing the
proved modules underneath.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace FormalizedProof

universe u

/-- The displayed Theorem 1 statement in the paper's `S(n)` notation. -/
abbrev FinalTheoremOneStatement
    (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  TheoremOneStatement P

/-- The single-size displayed formula from Theorem 1. -/
abbrev FinalTheoremOneAtStatement
    (P : TheoremOne.MaxProblemFamily.{u}) (n : Nat) : Prop :=
  P.aLop n =
    4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1

/-- Unfolded form of the final theorem statement. -/
theorem finalTheoremOneStatement_iff
    (P : TheoremOne.MaxProblemFamily.{u}) :
    FinalTheoremOneStatement P ↔
      ∀ n : Nat, FinalTheoremOneAtStatement P n := by
  rfl

/-- The strongest currently exposed manuscript subtheorem package: primitive
carrier geometry with the generic `<= 7` case proved from component counts,
close/intriguing cases reduced to component-wise savings, and named
incremental Karlsson lower data. -/
abbrev StrongestKnownTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ComponentSavingsPrimitiveCarrierTheoremOneSubtheorems P

/-- Direct whole-carrier savings package: primitive carrier geometry with the
generic `<= 7` case proved from component counts, close/intriguing cases
reduced to finite-cardinality bounds on the whole carrier intersection, and
named incremental Karlsson lower data.  This is the preferred upper boundary
for coupled close-pair arguments. -/
abbrev DirectSavingsTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  DirectSavingsPrimitiveCarrierTheoremOneSubtheorems P

/-- Stronger lower-bound-facing package: the upper bound is still the
component-savings primitive carrier package, while the lower construction is
specified pairwise.  The aggregate Karlsson lower polynomial is then derived
inside Lean by summing the certified pair contributions. -/
abbrev PairwiseLowerTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ComponentSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems P

/-- Direct-savings version with pairwise Karlsson lower data. -/
abbrev DirectSavingsPairwiseLowerTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  DirectSavingsPairwiseLowerPrimitiveCarrierTheoremOneSubtheorems P

/-- Monotone pairwise lower package: lower copy-pair data are inequalities
`cluster value <= actual pair value`, which is enough for the lower-bound
half of Theorem 1. -/
abbrev MonotonePairwiseLowerTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ComponentSavingsMonotonePairwiseLowerPrimitiveCarrierTheoremOneSubtheorems P

/-- Direct-savings version with monotone pairwise Karlsson lower data. -/
abbrev DirectSavingsMonotonePairwiseLowerTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  DirectSavingsMonotonePairwiseLowerPrimitiveCarrierTheoremOneSubtheorems P

/-- Lower-bound-facing package closest to Karlsson's manuscript construction:
the lower side names the four-base table and supplies local blow-up/insertion
certificates before Lean converts it to the pairwise lower interface. -/
abbrev KarlssonBaseLowerTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ComponentSavingsKarlssonBaseLowerPrimitiveCarrierTheoremOneSubtheorems P

/-- Direct-savings version closest to Karlsson's manuscript lower
construction: whole-carrier close/intriguing savings on the upper side and
four-base/local-blow-up data on the lower side. -/
abbrev DirectSavingsKarlssonBaseLowerTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  DirectSavingsKarlssonBaseLowerPrimitiveCarrierTheoremOneSubtheorems P

/-- A weaker but useful package where the close/intriguing savings have
already been converted to final numeric pair-crossing inequalities. -/
abbrev ComponentBoundTheoremOneSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ComponentBoundPrimitiveCarrierTheoremOneSubtheorems P

end FormalizedProof
end TheoremOneManuscript
end Lollipop
