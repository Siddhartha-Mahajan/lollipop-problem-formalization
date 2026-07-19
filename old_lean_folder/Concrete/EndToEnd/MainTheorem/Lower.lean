import old_lean_folder.Concrete.EndToEnd.Lower
import old_lean_folder.Concrete.EndToEnd.MainTheorem.Topology
import old_lean_folder.Concrete.EndToEnd.MainTheorem.Genericity

/-!
# Main theorem spine: lower bound

This file names the complete lower-construction theorem path for the concrete
certificate-free endpoint.  The lower proof depends on the same topology spine
as the upper bound plus the finite genericity-avoidance theorem in
`MainTheorem.Genericity`.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace MainTheorem
namespace Lower

/-- Lower-bound theorem package supplied by the main topology and genericity
spines. -/
def lowerPorts : Lollipop.Concrete.EndToEnd.LowerPorts where
  topology := Topology.fanTopologyPorts
  genericity := Genericity.chamberGenericityAvoidance_all

/-- Concrete realization theorem for the lower construction. -/
theorem lowerRealization_all (n : ℕ) :
    LowerRealization (Arrangement n) regionCountRat n :=
  Lollipop.Concrete.EndToEnd.lowerRealization_all lowerPorts n

/-- Concrete lower statement for one size. -/
theorem regionLower (n : ℕ) : RegionLowerStatement n :=
  Lollipop.Concrete.EndToEnd.regionLower lowerPorts n

/-- Concrete lower statement for every size. -/
theorem regionLower_all :
    ∀ n : ℕ, RegionLowerStatement n :=
  Lollipop.Concrete.EndToEnd.regionLower_all lowerPorts

end Lower
end MainTheorem
end EndToEnd
end Concrete
end Lollipop
