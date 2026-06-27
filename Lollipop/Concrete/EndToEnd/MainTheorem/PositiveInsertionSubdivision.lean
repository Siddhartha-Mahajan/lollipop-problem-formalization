import Lollipop.Concrete.EndToEnd.LocalizedTopology
import Mathlib.Tactic

/-!
# Positive insertion subdivision target

This file isolates the remaining planar-subdivision construction for
non-first insertions.  The downstream API already knows how to turn localized
edge filtrations into insertion split chains; what is still missing is the
geometric construction of such filtrations by subdividing the inserted
lollipop against the previous carrier.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace MainTheorem

open Set

/-- Every insertion fan contains the compactification point at infinity. -/
theorem infinity_mem_insertionFan
    {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n) :
    infinity ∈ InsertionFan.insertionFan A k hk := by
  simp [InsertionFan.insertionFan, InsertionFan.pairIntersectionFan,
    pointedFinsetUnion]

/-- Every insertion fan is nonempty. -/
theorem insertionFan_nonempty
    {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n) :
    (InsertionFan.insertionFan A k hk).Nonempty :=
  ⟨infinity, infinity_mem_insertionFan A k hk⟩

/-- The component type of every insertion fan is nonempty. -/
theorem connectedComponents_insertionFan_nonempty
    {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n) :
    Nonempty
      (ConnectedComponents (InsertionFan.insertionFan A k hk)) :=
  ConnectedComponents.nonempty_iff_nonempty.mpr
    ⟨⟨infinity, infinity_mem_insertionFan A k hk⟩⟩

/-- The component type of every insertion fan is finite. -/
theorem finite_connectedComponents_insertionFan
    {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n) :
    Finite
      (ConnectedComponents (InsertionFan.insertionFan A k hk)) := by
  classical
  let s := InsertionFan.previousIndices (⟨k, hk⟩ : Fin n)
  let L := A ⟨k, hk⟩
  change Finite (ConnectedComponents
    (pointedFinsetUnion infinity s
      (fun i => hatPairIntersection (A i) L)))
  let Idx := {i // i ∈ s}
  let T : Option Idx → Set Sphere2
    | none => {infinity}
    | some i => hatPairIntersection (A i.1) L
  have hTfinite : ∀ o : Option Idx,
      Finite (ConnectedComponents (T o)) := by
    intro o
    cases o with
    | none =>
        dsimp [T]
        exact finite_connectedComponents_of_finite_set
          (finite_singleton infinity)
    | some i =>
        dsimp [T]
        exact PairGeometry.finite_connectedComponents_hatPairIntersection
          (A i.1) L
  haveI (o : Option Idx) : Finite (ConnectedComponents (T o)) :=
    hTfinite o
  have hunion :
      pointedFinsetUnion infinity s
          (fun i => hatPairIntersection (A i) L) =
        ⋃ o : Option Idx, T o := by
    ext z
    constructor
    · intro hz
      rcases hz with hz | hz
      · exact Set.mem_iUnion_of_mem none hz
      · rcases Set.mem_iUnion.mp hz with ⟨i, hi⟩
        exact Set.mem_iUnion_of_mem (some i) hi
    · intro hz
      rcases Set.mem_iUnion.mp hz with ⟨o, ho⟩
      cases o with
      | none => exact Or.inl ho
      | some i => exact Or.inr (Set.mem_iUnion_of_mem i ho)
  rw [hunion]
  exact finite_connectedComponents_iUnion

/-- Every insertion fan has positive component count. -/
theorem componentCount_insertionFan_pos
    {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n) :
    0 < componentCount (InsertionFan.insertionFan A k hk) := by
  haveI : Finite
      (ConnectedComponents (InsertionFan.insertionFan A k hk)) :=
    finite_connectedComponents_insertionFan A k hk
  haveI : Nonempty
      (ConnectedComponents (InsertionFan.insertionFan A k hk)) :=
    connectedComponents_insertionFan_nonempty A k hk
  exact Nat.card_pos

/-- Rational form of the universal one-edge insertion-fan budget. -/
theorem one_le_componentCount_insertionFan_cast
    {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n) :
    (1 : ℚ) ≤
      (componentCount (InsertionFan.insertionFan A k hk) : ℚ) := by
  exact_mod_cast
    (Nat.succ_le_of_lt (componentCount_insertionFan_pos A k hk))

/-- Bounded subdivision data for one positive ordered insertion.

Mathematically this should be built by cutting the inserted lollipop carrier
at its old-new fan and ordering the resulting localized edges. -/
structure PositiveInsertionSubdivision
    {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n) where
  edgeCount : ℕ
  filtration :
    InsertionFiltration.LocalizedInsertionFiltration
      (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk))
      (A ⟨k, hk⟩) edgeCount
  edgeCount_le_fan :
    (edgeCount : ℚ) ≤
      (componentCount (InsertionFan.insertionFan A k hk) : ℚ)

/-- Exact subdivision data for one positive generic ordered insertion. -/
structure ExactPositiveInsertionSubdivision
    {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n) where
  edgeCount : ℕ
  filtration :
    InsertionFiltration.LocalizedExactInsertionFiltration
      (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk))
      (A ⟨k, hk⟩) edgeCount
  edgeCount_eq_fan :
    edgeCount = componentCount (InsertionFan.insertionFan A k hk)

/-- One localized whole-carrier edge gives bounded subdivision data.

This is the base case for later subdivision proofs: after proving that the
entire inserted carrier is localized in one old component, the fan budget is
automatic because every insertion fan has at least one component. -/
noncomputable def positiveInsertionSubdivision_of_singleEdgeStep
    {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n)
    (step :
      LocalFiltration.LocalizedEdgeStep
        (occupied
          (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk)))
        (A ⟨k, hk⟩).carrier) :
    PositiveInsertionSubdivision A k hk where
  edgeCount := 1
  filtration := by
    let C :=
      occupied (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk))
    let L := A ⟨k, hk⟩
    let f : LocalFiltration.LocalizedEdgeFiltration 1 C
        (LocalInsertion.carrierExtension C L.carrier) :=
      LocalFiltration.LocalizedEdgeFiltration.snoc
        (LocalFiltration.LocalizedEdgeFiltration.nil C)
        L.carrier
        (by simpa [C, L] using step)
    simpa [InsertionFiltration.LocalizedInsertionFiltration, C, L,
      LocalInsertion.carrierExtension] using f
  edgeCount_le_fan := by
    simpa using one_le_componentCount_insertionFan_cast A k hk

/-- One exact localized whole-carrier edge gives exact subdivision data when
the insertion fan has component count one. -/
noncomputable def exactPositiveInsertionSubdivision_of_singleExactEdgeStep
    {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n)
    (hfan : componentCount (InsertionFan.insertionFan A k hk) = 1)
    (step :
      LocalFiltration.LocalizedExactEdgeStep (A ⟨k, hk⟩)
        (occupied
          (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk)))
        (A ⟨k, hk⟩).carrier) :
    ExactPositiveInsertionSubdivision A k hk where
  edgeCount := 1
  filtration := by
    let C :=
      occupied (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk))
    let L := A ⟨k, hk⟩
    let f : LocalFiltration.LocalizedExactEdgeFiltration L 1 C
        (LocalInsertion.carrierExtension C L.carrier) :=
      LocalFiltration.LocalizedExactEdgeFiltration.snoc
        (LocalFiltration.LocalizedExactEdgeFiltration.nil (L := L) C)
        L.carrier
        (by simpa [C, L] using step)
    simpa [InsertionFiltration.LocalizedExactInsertionFiltration, C, L,
      LocalInsertion.carrierExtension] using f
  edgeCount_eq_fan := hfan.symm

/-- A bounded subdivision gives the existential localized-filtration theorem
used by `LocalizedTopology`. -/
theorem localizedInsertionFiltration_bound_positive_of_subdivision
    {n : ℕ} {A : Arrangement n} {k : ℕ} {hk : k < n}
    (d : PositiveInsertionSubdivision A k hk) :
    ∃ m : ℕ,
    ∃ _f : InsertionFiltration.LocalizedInsertionFiltration
        (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk))
        (A ⟨k, hk⟩) m,
      (m : ℚ) ≤
        (componentCount (InsertionFan.insertionFan A k hk) : ℚ) :=
  ⟨d.edgeCount, d.filtration, d.edgeCount_le_fan⟩

/-- An exact subdivision gives the existential exact localized-filtration
theorem used by `LocalizedTopology`. -/
theorem localizedExactInsertionFiltration_of_exactPositiveSubdivision
    {n : ℕ} {A : Arrangement n} {k : ℕ} {hk : k < n}
    (d : ExactPositiveInsertionSubdivision A k hk) :
    ∃ m : ℕ,
    ∃ _f : InsertionFiltration.LocalizedExactInsertionFiltration
        (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk))
        (A ⟨k, hk⟩) m,
      m = componentCount (InsertionFan.insertionFan A k hk) :=
  ⟨d.edgeCount, d.filtration, d.edgeCount_eq_fan⟩

/-- Remaining bounded positive-insertion subdivision theorem.

This is the concrete planar-topology construction still required for the
upper bound: for every non-first insertion, subdivide the inserted lollipop
into localized edge additions using at most the old-new fan component count. -/
theorem positiveInsertionSubdivision_exists
    {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n) (_hkpos : 0 < k) :
    Nonempty (PositiveInsertionSubdivision A k hk) := by
  sorry

/-- Remaining exact positive-insertion subdivision theorem in generic
position.

This is the concrete planar-topology construction still required for the
generic Euler equality: the same subdivision is exact and has length exactly
the old-new fan component count. -/
theorem exactPositiveInsertionSubdivision_exists
    {n : ℕ} {A : Arrangement n} (_hA : IsGeneric A)
    (k : ℕ) (hk : k < n) (_hkpos : 0 < k) :
    Nonempty (ExactPositiveInsertionSubdivision A k hk) := by
  sorry

end MainTheorem
end EndToEnd
end Concrete
end Lollipop
