import Lollipop.Concrete.EndToEnd.Lower

/-!
# Unconditional concrete endpoint

This is the intended public theorem.  It has no `GeometryCertificates`
argument and is stated directly for Euclidean lollipops and connected
components of their complement.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd

/-- Maximum number of complementary regions for `n` concrete Euclidean
lollipops. -/
theorem lollipopMaximum (n : ℕ) : LollipopMaximumStatement n :=
  lollipopMaximum_of_upper_lower (regionUpper n) (regionLower n)

/-- All-size version. -/
theorem lollipopMaximum_all : ∀ n : ℕ, LollipopMaximumStatement n :=
  lollipopMaximum_all_of_upper_lower regionUpper_all regionLower_all

/-- Expanded theorem statement, convenient for downstream use. -/
theorem lollipopMaximum_expanded (n : ℕ) :
    IsGreatest
      (Set.range (fun A : Arrangement n => (regionCount A : ℚ)))
      (4 * ((n.choose 2 : ℕ) : ℚ) +
        TheoremOneManuscript.manuscriptS n + (n : ℚ) + 1) := by
  simpa [LollipopMaximumStatement, regionCountRat, candidate] using
    lollipopMaximum n

end EndToEnd
end Concrete
end Lollipop
