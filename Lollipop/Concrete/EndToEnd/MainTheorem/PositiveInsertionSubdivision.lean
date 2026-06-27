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

