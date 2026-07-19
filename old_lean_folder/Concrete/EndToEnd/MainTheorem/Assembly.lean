import old_lean_folder.Concrete.EndToEnd.Final
import old_lean_folder.Concrete.EndToEnd.MainTheorem.Upper
import old_lean_folder.Concrete.EndToEnd.MainTheorem.Lower

/-!
# Main theorem spine: final assembly

This file is the visible end-to-end target.  It contains no new mathematical
proof gaps of its own: the upper and lower routes are named in
`MainTheorem.Upper` and `MainTheorem.Lower`, and their remaining proof gaps are
concentrated in `MainTheorem.Topology` and `MainTheorem.Genericity`.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace MainTheorem

/-- Upper endpoint ports built from the named topology theorem target. -/
def upperPorts : UpperPorts where
  topology := Upper.upperPorts.topology

/-- Lower endpoint ports built from the named topology and genericity targets. -/
def lowerPorts : LowerPorts where
  topology := Lower.lowerPorts.topology
  genericity := Lower.lowerPorts.genericity

/-- Existing endpoint port package built from the named theorem targets. -/
def endToEndPorts : EndToEndPorts :=
  { upper := upperPorts, lower := lowerPorts }

/-- Unconditional concrete upper bound, pending only the named topology
`sorry`s. -/
theorem regionUpper (n : ℕ) : RegionUpperStatement n :=
  Upper.regionUpper n

/-- Unconditional concrete lower bound, pending only the named topology and
genericity `sorry`s. -/
theorem regionLower (n : ℕ) : RegionLowerStatement n :=
  Lower.regionLower n

/-- Final certificate-free lollipop maximum theorem.

When the named theorem-spine `sorry`s are removed, this theorem has no
caller-supplied ports or certificates. -/
theorem lollipopMaximum (n : ℕ) :
    LollipopMaximumStatement n :=
  Lollipop.Concrete.lollipopMaximum_of_upper_lower
    (regionUpper n) (regionLower n)

/-- All-size version of the final certificate-free theorem. -/
theorem lollipopMaximum_all :
    ∀ n : ℕ, LollipopMaximumStatement n :=
  fun n => lollipopMaximum n

/-- Expanded final statement in terms of the displayed manuscript formula. -/
theorem lollipopMaximum_expanded (n : ℕ) :
    IsGreatest
      (Set.range (fun A : Arrangement n => (regionCount A : ℚ)))
      (4 * ((n.choose 2 : ℕ) : ℚ) +
        TheoremOneManuscript.manuscriptS n + (n : ℚ) + 1) :=
  by
    simpa [LollipopMaximumStatement, regionCountRat, candidate] using
      lollipopMaximum n

end MainTheorem
end EndToEnd
end Concrete
end Lollipop
