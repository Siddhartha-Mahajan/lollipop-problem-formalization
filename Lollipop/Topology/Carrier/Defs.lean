import Lollipop.Lemma_8_5.Proof
import Lollipop.Topology.PrimitiveArcs
import Lollipop.Topology.CircleJordan
import Lollipop.Topology.SimpleArcComplement
import Lollipop.Topology.JordanBridge
import Lollipop.Topology.ArcClosedCurve
import Mathlib.Tactic

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace Pieces

open Set

/-- Rotation of a plane vector by a quarter turn. -/
def perp (v : Point) : Point := !₂[-(v 1), v 0]

/-- Point of the lollipop circle at angle `θ` measured from the anchor
(`circlePt L 0 = L.anchor`). -/
def circlePt (L : Lollipop) (θ : ℝ) : Point :=
  L.center + Real.cos θ • L.radial + Real.sin θ • perp L.radial

/-- Point of the stem at parameter `t ≥ 1` (`stemPt L 1 = L.anchor`). -/
def stemPt (L : Lollipop) (t : ℝ) : Point := L.stemMap t

/-- Closed circular arc over the angle interval `[α, β]`. -/
def circleArcSet (L : Lollipop) (α β : ℝ) : Set Point := circlePt L '' Icc α β
/-- Its relative interior. -/
def circleArcOpen (L : Lollipop) (α β : ℝ) : Set Point := circlePt L '' Ioo α β
/-- Closed stem segment `[s, t]`. -/
def segSet (L : Lollipop) (s t : ℝ) : Set Point := stemPt L '' Icc s t
def segOpen (L : Lollipop) (s t : ℝ) : Set Point := stemPt L '' Ioo s t
/-- Closed stem ray `[s, ∞)`. -/
def raySet (L : Lollipop) (s : ℝ) : Set Point := stemPt L '' Ici s
def rayOpen (L : Lollipop) (s : ℝ) : Set Point := stemPt L '' Ioi s

/-- Two collars of a closed edge `E` relative to a closed carrier `D`: an open
set `U ⊆ Dᶜ` containing the new part `E \ D`, and two nonempty preconnected sets
`S₁ S₂ ⊆ U \ E` covering `U \ E`. -/
structure Collars (D E S₁ S₂ U : Set Point) : Prop where
  isOpen_U : IsOpen U
  new_sub : ∀ z ∈ E, z ∉ D → z ∈ U
  U_sub : U ⊆ Dᶜ
  pre₁ : IsPreconnected S₁
  pre₂ : IsPreconnected S₂
  sub₁ : S₁ ⊆ U \ E
  sub₂ : S₂ ⊆ U \ E
  cover : ∀ x ∈ U, x ∉ E → x ∈ S₁ ∨ x ∈ S₂
  ne₁ : S₁.Nonempty
  ne₂ : S₂.Nonempty

/-- One collar of a closed edge `E` with a free end: `U ⊆ Dᶜ` open contains
`E \ D`, and `U \ E` is a single nonempty preconnected set `S`. -/
structure OneCollar (D E S U : Set Point) : Prop where
  isOpen_U : IsOpen U
  new_sub : ∀ z ∈ E, z ∉ D → z ∈ U
  U_sub : U ⊆ Dᶜ
  pre : IsPreconnected S
  sub : S ⊆ U \ E
  cover : ∀ x ∈ U, x ∉ E → x ∈ S
  ne : S.Nonempty

/-- Local two-sided germ of `E` inside `U`: around the open subarc `γ` of `E`
there is an open `N ⊆ U` with `N ∩ E = γ` whose complement in `N` splits into
two nonempty preconnected sets lying in the two collars. -/
structure Germ (E S₁ S₂ U γ : Set Point) : Prop where
  ex : ∃ N N₁ N₂ : Set Point, IsOpen N ∧ N ⊆ U ∧ N ∩ E = γ ∧
    IsPreconnected N₁ ∧ IsPreconnected N₂ ∧ N₁.Nonempty ∧ N₂.Nonempty ∧
    N₁ ⊆ S₁ ∧ N₂ ⊆ S₂ ∧ N \ E ⊆ N₁ ∪ N₂

/-- Simple arc in the one-point compactification, from `x` to `y`. -/
def IsSphereArc (P : Set Sphere2) (x y : Sphere2) : Prop :=
  ∃ f : ℝ → Sphere2, P = f '' Icc 0 1 ∧ Continuous f ∧
    InjOn f (Icc 0 1) ∧ f 0 = x ∧ f 1 = y


end Pieces
end EndToEnd
end Concrete
end Lollipop
