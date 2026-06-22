import Lollipop.Internal.Manuscript.FormulaBridge
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finite.Card
import Mathlib.Topology.Connected.Clopen

/-!
# Concrete Euclidean lollipops

This file starts the certificate-free endpoint requested in
`audit/UNCONDITIONAL_FORMALIZATION_VERDICT.md`.

The older public theorem proves the manuscript formula from abstract geometry
certificates.  Here the geometric object is concrete: a lollipop in the
Euclidean plane is a circle together with the outward radial stem determined by
a single nonzero vector.  Regions are actual connected components of the
complement.

The hard upper and lower geometric theorems are not assumed here.  They are
named as concrete propositions, and `lollipopMaximum_of_upper_lower` records
the final assembly step those proofs must feed.
-/

noncomputable section

namespace Lollipop
namespace Concrete

open Set

/-- The Euclidean plane used for the certificate-free lollipop model. -/
abbrev Point : Type :=
  EuclideanSpace ℝ (Fin 2)

/--
A concrete lollipop is determined by a center and one nonzero radial vector.
The circle has radius `‖radial‖`, and the stem starts at `center + radial` and
continues in the same outward radial direction.
-/
structure Lollipop where
  center : Point
  radial : Point
  radial_ne_zero : radial ≠ 0

namespace Lollipop

/-- The circle radius determined by the radial vector. -/
def radius (L : Lollipop) : ℝ :=
  ‖L.radial‖

/-- The point where the stem attaches to the circle. -/
def anchor (L : Lollipop) : Point :=
  L.center + L.radial

/-- The circular primitive of a lollipop. -/
def circle (L : Lollipop) : Set Point :=
  {x | ‖x - L.center‖ = L.radius}

/-- The outward radial stem of a lollipop. -/
def stem (L : Lollipop) : Set Point :=
  {x | ∃ t : ℝ, 1 ≤ t ∧ x = L.center + t • L.radial}

/-- The full carrier: circle plus outward radial stem. -/
def carrier (L : Lollipop) : Set Point :=
  L.circle ∪ L.stem

theorem radius_pos (L : Lollipop) : 0 < L.radius := by
  simpa [radius, norm_pos_iff] using L.radial_ne_zero

theorem radius_ne_zero (L : Lollipop) : L.radius ≠ 0 :=
  ne_of_gt (radius_pos L)

theorem anchor_mem_circle (L : Lollipop) : L.anchor ∈ L.circle := by
  simp [circle, anchor, radius]

theorem anchor_mem_stem (L : Lollipop) : L.anchor ∈ L.stem := by
  refine ⟨1, le_rfl, ?_⟩
  simp [anchor]

theorem circle_subset_carrier (L : Lollipop) : L.circle ⊆ L.carrier :=
  fun _ hx => Or.inl hx

theorem stem_subset_carrier (L : Lollipop) : L.stem ⊆ L.carrier :=
  fun _ hx => Or.inr hx

theorem anchor_mem_carrier (L : Lollipop) : L.anchor ∈ L.carrier :=
  stem_subset_carrier L (anchor_mem_stem L)

end Lollipop

/-- An arrangement of `n` concrete lollipops. -/
abbrev Arrangement (n : ℕ) : Type :=
  Fin n → Lollipop

/-- The occupied carrier set of an arrangement. -/
def occupied {n : ℕ} (A : Arrangement n) : Set Point :=
  ⋃ i, (A i).carrier

theorem mem_occupied_iff {n : ℕ} {A : Arrangement n} {x : Point} :
    x ∈ occupied A ↔ ∃ i : Fin n, x ∈ (A i).carrier := by
  simp [occupied]

/-- The complement of the occupied set, as a topological subtype. -/
abbrev FreeSpace {n : ℕ} (A : Arrangement n) : Type :=
  {x : Point // x ∉ occupied A}

/--
The number of connected components of the complement.

This uses `Nat.card`, so it is zero if the connected-component type has not
yet been proved finite.  A complete formalization must separately prove
finiteness for finite lollipop arrangements and then connect this definition
to the planar graph/topology engine.
-/
def regionCount {n : ℕ} (A : Arrangement n) : ℕ :=
  Nat.card (ConnectedComponents (FreeSpace A))

/-- Finiteness obligation for concrete lollipop complement components. -/
def RegionFinitenessStatement (n : ℕ) : Prop :=
  ∀ A : Arrangement n, Finite (ConnectedComponents (FreeSpace A))

/-- Region count coerced to `ℚ`, matching the manuscript formula stack. -/
def regionCountRat {n : ℕ} (A : Arrangement n) : ℚ :=
  regionCount A

/-- The displayed manuscript candidate value. -/
def candidate (n : ℕ) : ℚ :=
  4 * ((n.choose 2 : ℕ) : ℚ) +
    TheoremOneManuscript.manuscriptS n + (n : ℚ) + 1

/-- Concrete upper-bound statement for the certificate-free endpoint. -/
def RegionUpperStatement (n : ℕ) : Prop :=
  ∀ A : Arrangement n, regionCountRat A ≤ candidate n

/-- Concrete lower-bound statement for the certificate-free endpoint. -/
def RegionLowerStatement (n : ℕ) : Prop :=
  ∃ A : Arrangement n, regionCountRat A = candidate n

/-- The intended certificate-free maximum theorem statement. -/
def LollipopMaximumStatement (n : ℕ) : Prop :=
  IsGreatest (Set.range (fun A : Arrangement n => regionCountRat A)) (candidate n)

/--
The final assembly step for the concrete endpoint.

The remaining work is to prove `RegionUpperStatement n` and
`RegionLowerStatement n` from the actual Euclidean geometry/topology.  Once
those are available, this theorem produces the desired `IsGreatest` statement
without any `GeometryCertificates` argument.
-/
theorem lollipopMaximum_of_upper_lower {n : ℕ}
    (hupper : RegionUpperStatement n)
    (hlower : RegionLowerStatement n) :
    LollipopMaximumStatement n := by
  constructor
  · rcases hlower with ⟨A, hA⟩
    exact ⟨A, hA⟩
  · intro y hy
    rcases hy with ⟨A, rfl⟩
    exact hupper A

/-- All-`n` assembly form of the certificate-free endpoint. -/
theorem lollipopMaximum_all_of_upper_lower
    (hupper : ∀ n : ℕ, RegionUpperStatement n)
    (hlower : ∀ n : ℕ, RegionLowerStatement n) :
    ∀ n : ℕ, LollipopMaximumStatement n :=
  fun n => lollipopMaximum_of_upper_lower (hupper n) (hlower n)

end Concrete
end Lollipop
