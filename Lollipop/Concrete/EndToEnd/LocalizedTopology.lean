import Lollipop.Concrete.EndToEnd.InsertionFan
import Lollipop.Concrete.EndToEnd.InsertionFiltration

/-!
# Reduction from localized filtrations to the fan-topology port

The remaining geometric topology can now be stated as a finite-filtration
problem.  For every ordered insertion, produce a localized edge filtration
whose length is bounded by the insertion-fan component count; in generic
position, produce an exact localized filtration whose length is exactly that
count.

This file proves that those localized-filtration statements imply the
`InsertionFan.FanTopologyPorts` package consumed by the concrete upper and
lower endpoints.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace LocalizedTopology

/-- Localized-filtration form of the arbitrary insertion topology theorem for
one fixed final arrangement. -/
def OrderedLocalizedFiltrationBound {n : ℕ} (A : Arrangement n) : Prop :=
  ∀ (k : ℕ) (hk : k < n),
    ∃ m : ℕ,
    ∃ _f : InsertionFiltration.LocalizedInsertionFiltration
        (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk))
        (A ⟨k, hk⟩) m,
      (m : ℚ) ≤
        (componentCount (InsertionFan.insertionFan A k hk) : ℚ)

/-- Localized-filtration form of the generic exact insertion topology theorem
for one fixed final arrangement. -/
def OrderedExactLocalizedFiltration {n : ℕ} (A : Arrangement n) : Prop :=
  ∀ (k : ℕ) (hk : k < n),
    ∃ m : ℕ,
    ∃ _f : InsertionFiltration.LocalizedExactInsertionFiltration
        (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk))
        (A ⟨k, hk⟩) m,
      m = componentCount (InsertionFan.insertionFan A k hk)

/-- Localized bounded insertion filtrations compile to the fan-bounded split
chains expected by `InsertionFan`. -/
theorem orderedInsertionFanSplitChainBound_of_localizedFiltration
    {n : ℕ} {A : Arrangement n}
    (h : OrderedLocalizedFiltrationBound A) :
    InsertionFan.OrderedInsertionFanSplitChainBound A := by
  intro k hk
  rcases h k hk with ⟨m, f, hbudget⟩
  refine ⟨InsertionFiltration.insertionSplitChainOfLocalizedFiltration f, ?_⟩
  exact hbudget

/-- Exact localized insertion filtrations compile to exact fan-sized split
chains expected by `InsertionFan`. -/
theorem orderedExactInsertionFanSplitChain_of_exactLocalizedFiltration
    {n : ℕ} {A : Arrangement n}
    (h : OrderedExactLocalizedFiltration A) :
    InsertionFan.OrderedExactInsertionFanSplitChain A := by
  intro k hk
  rcases h k hk with ⟨m, f, hcount⟩
  refine ⟨InsertionFiltration.exactInsertionSplitChainOfLocalizedFiltration f,
    ?_⟩
  exact hcount

/-- Remaining localized-filtration topology package.  This is a more explicit
replacement target for `FanTopologyPorts`: it asks for actual localized edge
filtrations rather than quotient split chains. -/
structure LocalizedFiltrationTopologyPorts : Prop where
  arbitrary_localized :
    ∀ {n : ℕ} (A : Arrangement n), OrderedLocalizedFiltrationBound A
  generic_exact_localized :
    ∀ {n : ℕ} {A : Arrangement n}, IsGeneric A →
      OrderedExactLocalizedFiltration A

/-- Localized-filtration ports imply the sharper fan-topology port. -/
def LocalizedFiltrationTopologyPorts.toFanTopologyPorts
    (ports : LocalizedFiltrationTopologyPorts) :
    InsertionFan.FanTopologyPorts where
  arbitrary_fan_bound := fun A =>
    orderedInsertionFanSplitChainBound_of_localizedFiltration
      (ports.arbitrary_localized A)
  generic_exact_fan := fun hA =>
    orderedExactInsertionFanSplitChain_of_exactLocalizedFiltration
      (ports.generic_exact_localized hA)

/-- Direct constructor for `FanTopologyPorts` from the two localized
filtration statements. -/
def fanTopologyPorts_of_localizedFiltrations
    (harb : ∀ {n : ℕ} (A : Arrangement n),
      OrderedLocalizedFiltrationBound A)
    (hgen : ∀ {n : ℕ} {A : Arrangement n}, IsGeneric A →
      OrderedExactLocalizedFiltration A) :
    InsertionFan.FanTopologyPorts :=
  (LocalizedFiltrationTopologyPorts.mk harb hgen).toFanTopologyPorts

end LocalizedTopology
end EndToEnd
end Concrete
end Lollipop
