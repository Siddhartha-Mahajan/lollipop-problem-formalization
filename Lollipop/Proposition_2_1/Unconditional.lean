import Lollipop.Proposition_2_1.Proof
import Lollipop.Topology.PlanarPorts

/-!
Proposition 2.1 (`prop:top-region`), unconditional: the planar-topology
package `PlanarTopologyPorts` is now *proved* (first insertion via the circle
Jordan separation, later insertions via the carrier-cutting theorem), so the
numbered proof no longer takes it as a hypothesis.
-/

namespace Lollipop.Manuscript.Proposition_2_1

/-- Proposition 2.1 with no hypotheses (the numbered proof endpoint). -/
theorem proof : CoreStatement :=
  proof_of_ports Concrete.EndToEnd.MainTheorem.Topology.planarTopologyPorts

end Lollipop.Manuscript.Proposition_2_1
