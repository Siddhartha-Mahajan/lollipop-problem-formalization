import Lollipop.Topology.FirstInsertion
import Lollipop.Topology.Carrier.Final

/-!
# Unconditional planar-topology ports

For the first insertion the single lollipop is cut by its circle
(`FirstInsertion`); for every later insertion the carrier-cutting theorem
(`Carrier.Final.prefix_chain_bound` / `prefix_chain_exact`) supplies the
split chains.  Together they discharge `FanTopologyPorts`, hence
`PlanarTopologyPorts`, with no hypotheses.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace MainTheorem
namespace Topology

open InsertionFan PlanarInsertion

/-- Fan-bounded split chains for every ordered insertion of every arrangement. -/
theorem fan_bound {n : ℕ} (A : Arrangement n) : OrderedInsertionFanSplitChainBound A := by
  intro k hk
  by_cases hzero : k = 0
  · subst hzero
    obtain ⟨m, f, hb⟩ := localizedInsertionFiltration_bound_zero A hk
    exact ⟨InsertionFiltration.insertionSplitChainOfLocalizedFiltration f, hb⟩
  · exact Pieces.prefix_chain_bound A k hk (Nat.pos_of_ne_zero hzero)

/-- Exact fan-sized split chains for every ordered insertion of a generic arrangement. -/
theorem fan_exact {n : ℕ} {A : Arrangement n} (hA : IsGeneric A) :
    OrderedExactInsertionFanSplitChain A := by
  intro k hk
  by_cases hzero : k = 0
  · subst hzero
    obtain ⟨m, f, hb⟩ := localizedExactInsertionFiltration_zero A hk
    exact ⟨InsertionFiltration.exactInsertionSplitChainOfLocalizedFiltration f, hb⟩
  · exact Pieces.prefix_chain_exact hA k hk (Nat.pos_of_ne_zero hzero)

/-- The fan-topology package, proved. -/
def fanTopologyPorts : FanTopologyPorts where
  arbitrary_fan_bound := fun A => fan_bound A
  generic_exact_fan := fun hA => fan_exact hA

/-- The planar-topology package, proved. -/
def planarTopologyPorts : PlanarTopologyPorts :=
  fanTopologyPorts.toPlanarTopologyPorts

end Topology
end MainTheorem
end EndToEnd
end Concrete
end Lollipop
