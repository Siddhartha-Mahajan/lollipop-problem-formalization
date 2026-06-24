import Lollipop.Concrete.EndToEnd.Upper
import Lollipop.Concrete.EndToEnd.MainTheorem.Topology

/-!
# Main theorem spine: upper bound

This file names the complete upper-bound theorem path for the concrete
certificate-free endpoint.  It deliberately does not introduce new
mathematical assumptions: the only remaining upper input is the topology
package built in `MainTheorem.Topology`.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace MainTheorem
namespace Upper

/-- Upper-bound theorem package supplied by the main topology spine. -/
def upperPorts : Lollipop.Concrete.EndToEnd.UpperPorts where
  topology := Topology.fanTopologyPorts

/-- Concrete upper bound for one arrangement. -/
theorem regionCountRat_le_candidate {n : ℕ} (A : Arrangement n) :
    regionCountRat A ≤ candidate n :=
  Lollipop.Concrete.EndToEnd.regionCountRat_le_candidate upperPorts A

/-- Concrete upper statement for one size. -/
theorem regionUpper (n : ℕ) : RegionUpperStatement n :=
  Lollipop.Concrete.EndToEnd.regionUpper upperPorts n

/-- Concrete upper statement for every size. -/
theorem regionUpper_all :
    ∀ n : ℕ, RegionUpperStatement n :=
  Lollipop.Concrete.EndToEnd.regionUpper_all upperPorts

end Upper
end MainTheorem
end EndToEnd
end Concrete
end Lollipop
