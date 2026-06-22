import Lollipop.Concrete.EndToEnd.Upper
import Lollipop.Concrete.EndToEnd.Lower.BlowUp
import Lollipop.Internal.Lower

/-!
# Concrete certificate-free lower theorem

The geometric blow-up is converted to the repository's already proved lower
algebra, which selects an admissible quadruple attaining `concreteS n`.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd

/-- Every admissible quadruple has a concrete lollipop realization with its
exact lower region count. -/
theorem lowerRealization_all (n : ℕ) :
    LowerRealization (Arrangement n) regionCountRat n :=
  Lower.BlowUp.lowerRealization n

/-- The displayed candidate is attained for every size. -/
theorem regionLower (n : ℕ) : RegionLowerStatement n := by
  rcases exists_region_eq_candidate_of_lowerRealization
    (lowerRealization_all n) with ⟨A, hA⟩
  refine ⟨A, ?_⟩
  rw [hA, candidate_eq_candidateRegionsChoose,
    candidateRegionsChoose_eq_candidateRegions]

/-- All-size lower theorem. -/
theorem regionLower_all : ∀ n : ℕ, RegionLowerStatement n := regionLower

end EndToEnd
end Concrete
end Lollipop
