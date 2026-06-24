import Lollipop.Concrete.EndToEnd.LocalizedTopology

/-!
# Main theorem spine: topology

This file states the concrete topology theorems needed by the final
certificate-free endpoint.

The missing topology is intentionally exposed as named `sorry`s here.  Future
supporting lemmas should be added only to remove these theorem-body `sorry`s.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace MainTheorem
namespace Topology

/-- Arbitrary localized filtration for one ordered insertion.

This is the exact topology object required for one insertion step: subdivide
the inserted lollipop relative to its old-new fan and build a localized edge
filtration whose length is bounded by the fan component count. -/
theorem localizedInsertionFiltration_bound
    {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n) :
    ∃ m : ℕ,
    ∃ _f : InsertionFiltration.LocalizedInsertionFiltration
        (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk))
        (A ⟨k, hk⟩) m,
      (m : ℚ) ≤
        (componentCount (InsertionFan.insertionFan A k hk) : ℚ) := by
  sorry

/-- Arbitrary-arrangement localized insertion topology.

This is the Lean replacement target for the manuscript's arbitrary
topological region inequality.  It must eventually be proved by finite
localized filtrations for every ordered lollipop insertion. -/
theorem arbitrary_localized_topology :
    ∀ {n : ℕ} (A : Arrangement n),
      LocalizedTopology.OrderedLocalizedFiltrationBound A := by
  intro n A k hk
  exact localizedInsertionFiltration_bound A k hk

/-- Exact localized filtration for one generic ordered insertion.

This is the exact topology object required for the manuscript's generic Euler
equality: in generic position the localized filtration length is exactly the
old-new insertion-fan component count. -/
theorem localizedExactInsertionFiltration_of_generic
    {n : ℕ} {A : Arrangement n} (hA : IsGeneric A)
    (k : ℕ) (hk : k < n) :
    ∃ m : ℕ,
    ∃ _f : InsertionFiltration.LocalizedExactInsertionFiltration
        (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk))
        (A ⟨k, hk⟩) m,
      m = componentCount (InsertionFan.insertionFan A k hk) := by
  sorry

/-- Generic exact localized insertion topology.

This is the Lean replacement target for the manuscript's generic Euler
region formula.  It must eventually be proved by exact localized filtrations
whose length is the insertion-fan component count. -/
theorem generic_exact_localized_topology :
    ∀ {n : ℕ} {A : Arrangement n}, IsGeneric A →
      LocalizedTopology.OrderedExactLocalizedFiltration A := by
  intro n A hA k hk
  exact localizedExactInsertionFiltration_of_generic hA k hk

/-- The fan-topology package obtained from the two main topology theorems. -/
def fanTopologyPorts : InsertionFan.FanTopologyPorts :=
  LocalizedTopology.fanTopologyPorts_of_localizedFiltrations
    arbitrary_localized_topology
    generic_exact_localized_topology

/-- The older planar-topology package consumed by upper and lower endpoints. -/
def planarTopologyPorts : PlanarTopologyPorts :=
  fanTopologyPorts.toPlanarTopologyPorts

/-- Finiteness of complement connected components, as supplied by topology. -/
theorem region_components_finite {n : ℕ} (A : Arrangement n) :
    Finite (ConnectedComponents (FreeSpace A)) :=
  planarTopologyPorts.region_components_finite A

/-- Concrete arbitrary topological region inequality. -/
theorem topological_region_inequality {n : ℕ} (A : Arrangement n) :
    regionCountRat A - (n : ℚ) - 1 ≤
      Lollipop.pairSum n (pairExcessTable A) :=
  planarTopologyPorts.crossing_excess_le_pairSum A

/-- Concrete generic Euler region equality. -/
theorem generic_euler_region_eq {n : ℕ} {A : Arrangement n}
    (hA : IsGeneric A) :
    regionCountRat A = ((totalCrossingsNat A : ℕ) : ℚ) + (n : ℚ) + 1 :=
  planarTopologyPorts.generic_region_eq hA

end Topology
end MainTheorem
end EndToEnd
end Concrete
end Lollipop
