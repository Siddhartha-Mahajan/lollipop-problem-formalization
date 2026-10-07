import Lollipop.Lemma_8_5.Proof
import Lollipop.Topology.Carrier.Defs
import Lollipop.Topology.LocalInsertion
import Lollipop.Topology.ComponentSurjectivity

/-!
Definitions for the carrier-cutting driver: compactified closed sets, arc
connectivity to infinity, the component potential `Psi`, and the pieces of the
inserted lollipop that are added one at a time.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace Pieces

open Set

/-- Compactification of a plane set, with `∞` adjoined. -/
def hatSet (D : Set Point) : Set Sphere2 := finiteLift D ∪ {infinity}

/-- Every point of the compactified set is joined to `∞` by a sphere arc inside it. -/
def ArcConn (D : Set Point) : Prop :=
  ∀ p ∈ hatSet D, p = infinity ∨ ∃ P ⊆ hatSet D, IsSphereArc P p infinity

/-- Compactified intersection of the carrier of `L` with the closed set `D`. -/
def Kset (L : Lollipop) (D : Set Point) : Set Sphere2 := hatCarrier L ∩ hatSet D

open scoped Classical in
/-- The potential: components of the compactified overlap, plus one while the
circle of `L` is not yet inside `D`. -/
def Psi (L : Lollipop) (D : Set Point) : ℕ :=
  componentCount (Kset L D) + (if L.circle ⊆ D then 0 else 1)

/-- A closed piece of the carrier of `L` whose relative interior misses `D`
and whose end points lie in `D` (the ray end `∞` counts as lying in `D`). -/
inductive IsGapPiece (L : Lollipop) (D : Set Point) : Set Point → Prop
  | circle {α β : ℝ} (hαβ : α < β) (hβ : β ≤ α + 2 * Real.pi)
      (hopen : ∀ θ ∈ Ioo α β, circlePt L θ ∉ D)
      (hend : circlePt L α ∈ D ∧ circlePt L β ∈ D) :
      IsGapPiece L D (circleArcSet L α β)
  | seg {s t : ℝ} (hs : 1 ≤ s) (hst : s < t)
      (hopen : ∀ τ ∈ Ioo s t, stemPt L τ ∉ D)
      (hend : stemPt L s ∈ D ∧ stemPt L t ∈ D) :
      IsGapPiece L D (segSet L s t)
  | ray {s : ℝ} (hs : 1 ≤ s)
      (hopen : ∀ τ, s < τ → stemPt L τ ∉ D) (hend : stemPt L s ∈ D) :
      IsGapPiece L D (raySet L s)

/-- The first stem piece when the anchor is not yet in `D`: a free leaf. -/
inductive IsLeafPiece (L : Lollipop) (D : Set Point) : Set Point → Prop
  | seg {t : ℝ} (ht : 1 < t) (hfree : stemPt L 1 ∉ D)
      (hopen : ∀ τ ∈ Ioo 1 t, stemPt L τ ∉ D) (hend : stemPt L t ∈ D) :
      IsLeafPiece L D (segSet L 1 t)
  | ray (hfree : stemPt L 1 ∉ D) (hopen : ∀ τ, 1 < τ → stemPt L τ ∉ D) :
      IsLeafPiece L D (raySet L 1)

end Pieces
end EndToEnd
end Concrete
end Lollipop
