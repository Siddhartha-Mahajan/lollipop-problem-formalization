import Lollipop.Concrete.EndToEnd.Final
import Lollipop.Concrete.EndToEnd.MainTheorem.Topology
import Lollipop.Concrete.EndToEnd.MainTheorem.Genericity

/-!
# Main theorem spine: final assembly

This file is the visible end-to-end target.  It contains no new mathematical
proof gaps of its own: the remaining work is concentrated in
`MainTheorem.Topology` and `MainTheorem.Genericity`.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace MainTheorem

/-- Upper endpoint ports built from the named topology theorem target. -/
def upperPorts : UpperPorts where
  topology := Topology.fanTopologyPorts

/-- Lower endpoint ports built from the named topology and genericity targets. -/
def lowerPorts : LowerPorts where
  topology := Topology.fanTopologyPorts
  genericity := Genericity.chamberGenericityAvoidance_all

/-- Existing endpoint port package built from the named theorem targets. -/
def endToEndPorts : EndToEndPorts :=
  EndToEndPorts.ofFanTopology
    Topology.fanTopologyPorts
    Genericity.chamberGenericityAvoidance_all

/-- Unconditional concrete upper bound, conditional only through the named
`sorry` in `MainTheorem.Topology`. -/
theorem regionUpper (n : ℕ) : RegionUpperStatement n :=
  Lollipop.Concrete.EndToEnd.regionUpper upperPorts n

/-- Unconditional concrete lower bound, conditional only through the named
`sorry`s in `MainTheorem.Topology` and `MainTheorem.Genericity`. -/
theorem regionLower (n : ℕ) : RegionLowerStatement n :=
  Lollipop.Concrete.EndToEnd.regionLower lowerPorts n

/-- Final certificate-free lollipop maximum theorem.

When the three named theorem-spine `sorry`s are removed, this theorem has no
caller-supplied ports or certificates. -/
theorem lollipopMaximum (n : ℕ) :
    LollipopMaximumStatement n :=
  Lollipop.Concrete.EndToEnd.lollipopMaximum endToEndPorts n

/-- All-size version of the final certificate-free theorem. -/
theorem lollipopMaximum_all :
    ∀ n : ℕ, LollipopMaximumStatement n :=
  Lollipop.Concrete.EndToEnd.lollipopMaximum_all endToEndPorts

/-- Expanded final statement in terms of the displayed manuscript formula. -/
theorem lollipopMaximum_expanded (n : ℕ) :
    IsGreatest
      (Set.range (fun A : Arrangement n => (regionCount A : ℚ)))
      (4 * ((n.choose 2 : ℕ) : ℚ) +
        TheoremOneManuscript.manuscriptS n + (n : ℚ) + 1) :=
  Lollipop.Concrete.EndToEnd.lollipopMaximum_expanded endToEndPorts n

end MainTheorem
end EndToEnd
end Concrete
end Lollipop
