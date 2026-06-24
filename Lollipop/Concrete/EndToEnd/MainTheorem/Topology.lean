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

/-- At the first insertion there are no previous indices. -/
theorem previousIndices_zero_eq_empty {n : ℕ} (hk : 0 < n) :
    InsertionFan.previousIndices (⟨0, hk⟩ : Fin n) = ∅ := by
  ext i
  constructor
  · intro hi
    have hlt : i < (⟨0, hk⟩ : Fin n) := by
      simpa [InsertionFan.previousIndices] using hi
    change i.1 < 0 at hlt
    omega
  · intro hi
    simp at hi

/-- The first insertion fan is just the distinguished point at infinity. -/
theorem insertionFan_zero_eq_singleton_infinity
    {n : ℕ} (A : Arrangement n) (hk : 0 < n) :
    InsertionFan.insertionFan A 0 hk = ({infinity} : Set Sphere2) := by
  unfold InsertionFan.insertionFan
  rw [previousIndices_zero_eq_empty hk]
  ext z
  simp [InsertionFan.pairIntersectionFan, pointedFinsetUnion]

/-- The first insertion fan has component count one. -/
theorem componentCount_insertionFan_zero
    {n : ℕ} (A : Arrangement n) (hk : 0 < n) :
    componentCount (InsertionFan.insertionFan A 0 hk) = 1 := by
  rw [insertionFan_zero_eq_singleton_infinity A hk]
  exact componentCount_singleton infinity

/-- The remaining first-lollipop bounded topology theorem.

Mathematically, this says inserting one lollipop into the empty carrier is a
single localized split: the circle supplies the Jordan separation, while the
outward stem lies on the exterior side and creates no additional component. -/
noncomputable def firstInsertionLocalizedFiltration
    {n : ℕ} (A : Arrangement n) (hk : 0 < n) :
    InsertionFiltration.LocalizedInsertionFiltration
      (PlanarInsertion.prefixArrangement A 0 (Nat.le_of_lt hk))
      (A ⟨0, hk⟩) 1 := by
  sorry

/-- The exact first-lollipop topology theorem.

This strengthens `firstInsertionLocalizedFiltration` by proving that the two
Jordan sides are both realized, so the first insertion increases the region
count by exactly one. -/
noncomputable def firstInsertionLocalizedExactFiltration
    {n : ℕ} (A : Arrangement n) (hk : 0 < n) :
    InsertionFiltration.LocalizedExactInsertionFiltration
      (PlanarInsertion.prefixArrangement A 0 (Nat.le_of_lt hk))
      (A ⟨0, hk⟩) 1 := by
  sorry

/-- Arbitrary bounded topology for the first ordered insertion. -/
theorem localizedInsertionFiltration_bound_zero
    {n : ℕ} (A : Arrangement n) (hk : 0 < n) :
    ∃ m : ℕ,
    ∃ _f : InsertionFiltration.LocalizedInsertionFiltration
        (PlanarInsertion.prefixArrangement A 0 (Nat.le_of_lt hk))
        (A ⟨0, hk⟩) m,
      (m : ℚ) ≤
        (componentCount (InsertionFan.insertionFan A 0 hk) : ℚ) := by
  refine ⟨1, firstInsertionLocalizedFiltration A hk, ?_⟩
  rw [componentCount_insertionFan_zero A hk]

/-- Generic exact topology for the first ordered insertion. -/
theorem localizedExactInsertionFiltration_zero
    {n : ℕ} (A : Arrangement n) (hk : 0 < n) :
    ∃ m : ℕ,
    ∃ _f : InsertionFiltration.LocalizedExactInsertionFiltration
        (PlanarInsertion.prefixArrangement A 0 (Nat.le_of_lt hk))
        (A ⟨0, hk⟩) m,
      m = componentCount (InsertionFan.insertionFan A 0 hk) := by
  refine ⟨1, firstInsertionLocalizedExactFiltration A hk, ?_⟩
  rw [componentCount_insertionFan_zero A hk]

/-- Remaining arbitrary topology theorem for non-first insertions. -/
theorem localizedInsertionFiltration_bound_positive
    {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n) (hkpos : 0 < k) :
    ∃ m : ℕ,
    ∃ _f : InsertionFiltration.LocalizedInsertionFiltration
        (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk))
        (A ⟨k, hk⟩) m,
      (m : ℚ) ≤
        (componentCount (InsertionFan.insertionFan A k hk) : ℚ) := by
  sorry

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
  by_cases hzero : k = 0
  · subst k
    exact localizedInsertionFiltration_bound_zero A hk
  · exact localizedInsertionFiltration_bound_positive A k hk
      (Nat.pos_of_ne_zero hzero)

/-- Remaining exact topology theorem for non-first generic insertions. -/
theorem localizedExactInsertionFiltration_of_generic_positive
    {n : ℕ} {A : Arrangement n} (hA : IsGeneric A)
    (k : ℕ) (hk : k < n) (hkpos : 0 < k) :
    ∃ m : ℕ,
    ∃ _f : InsertionFiltration.LocalizedExactInsertionFiltration
        (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk))
        (A ⟨k, hk⟩) m,
      m = componentCount (InsertionFan.insertionFan A k hk) := by
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
  by_cases hzero : k = 0
  · subst k
    exact localizedExactInsertionFiltration_zero A hk
  · exact localizedExactInsertionFiltration_of_generic_positive hA k hk
      (Nat.pos_of_ne_zero hzero)

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
