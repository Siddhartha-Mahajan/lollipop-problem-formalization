import old_lean_folder.Concrete.EndToEnd.PrimitiveArcs
import old_lean_folder.Concrete.EndToEnd.CircleJordan
import old_lean_folder.Concrete.EndToEnd.SimpleArcComplement
import old_lean_folder.Concrete.EndToEnd.JordanBridge
import old_lean_folder.Concrete.EndToEnd.Compactification
import old_lean_folder.Concrete.EndToEnd.ArcClosedCurve
import Mathlib.Tactic

/-!
Shared specification for the carrier-cutting project.  Every statement below
is to be PROVED (no `sorry`, no new axioms) by the task owner in a separate
file that imports this one, or that copies the definitions verbatim.
-/

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

/-! ### Task A1: circular arcs -/

/-- Collars (with germs) for a circular arc of `L` whose interior misses the
closed carrier `D` and whose endpoints lie in `D`. Loops (`β = α + 2π`) are
allowed. -/
theorem circle_collars (L : Lollipop) {D : Set Point} (hD : IsClosed D)
    {α β : ℝ} (hαβ : α < β) (hβ : β ≤ α + 2 * Real.pi)
    (hopen : ∀ θ ∈ Ioo α β, circlePt L θ ∉ D)
    (hend : circlePt L α ∈ D ∧ circlePt L β ∈ D) :
    ∃ U S₁ S₂ : Set Point,
      Collars D (circleArcSet L α β) S₁ S₂ U ∧
      ∀ θ₀ ∈ Ioo α β, ∀ δ : ℝ, 0 < δ → Icc (θ₀ - δ) (θ₀ + δ) ⊆ Ioo α β →
        Germ (circleArcSet L α β) S₁ S₂ U (circlePt L '' Ioo (θ₀ - δ) (θ₀ + δ)) := by
  sorry

/-! ### Task A2: stem segments and rays -/

theorem seg_collars (L : Lollipop) {D : Set Point} (hD : IsClosed D)
    {s t : ℝ} (hs : 1 ≤ s) (hst : s < t)
    (hopen : ∀ τ ∈ Ioo s t, stemPt L τ ∉ D)
    (hend : stemPt L s ∈ D ∧ stemPt L t ∈ D) :
    ∃ U S₁ S₂ : Set Point,
      Collars D (segSet L s t) S₁ S₂ U ∧
      ∀ τ₀ ∈ Ioo s t, ∀ δ : ℝ, 0 < δ → Icc (τ₀ - δ) (τ₀ + δ) ⊆ Ioo s t →
        Germ (segSet L s t) S₁ S₂ U (stemPt L '' Ioo (τ₀ - δ) (τ₀ + δ)) := by
  sorry

theorem ray_collars (L : Lollipop) {D : Set Point} (hD : IsClosed D)
    {s : ℝ} (hs : 1 ≤ s)
    (hopen : ∀ τ, s < τ → stemPt L τ ∉ D)
    (hend : stemPt L s ∈ D) :
    ∃ U S₁ S₂ : Set Point,
      Collars D (raySet L s) S₁ S₂ U ∧
      ∀ τ₀, s < τ₀ → ∀ δ : ℝ, 0 < δ → s < τ₀ - δ →
        Germ (raySet L s) S₁ S₂ U (stemPt L '' Ioo (τ₀ - δ) (τ₀ + δ)) := by
  sorry

/-! ### Task A3: free leaves (stem piece whose first end is free) -/

theorem seg_leaf_collar (L : Lollipop) {D : Set Point} (hD : IsClosed D)
    {s t : ℝ} (hs : 1 ≤ s) (hst : s < t)
    (hfree : stemPt L s ∉ D) (hopen : ∀ τ ∈ Ioo s t, stemPt L τ ∉ D)
    (hend : stemPt L t ∈ D) :
    ∃ U S : Set Point, OneCollar D (segSet L s t) S U := by
  sorry

theorem ray_leaf_collar (L : Lollipop) {D : Set Point} (hD : IsClosed D)
    {s : ℝ} (hs : 1 ≤ s)
    (hfree : stemPt L s ∉ D) (hopen : ∀ τ, s < τ → stemPt L τ ∉ D) :
    ∃ U S : Set Point, OneCollar D (raySet L s) S U := by
  sorry

/-! ### Task B1: local sides of a Jordan curve are separated -/

theorem local_sides_separated
    {J R γ N N₁ N₂ : Set Point} {u v : Point}
    (hJ : IsSimpleClosedCurve J)
    (hR : IsSimpleArcEnd R u v)
    (hJR : J = R ∪ γ) (hRγ : Disjoint R γ)
    (hN : IsOpen N) (hNJ : N ∩ J = γ)
    (hN₁ : IsPreconnected N₁) (hN₂ : IsPreconnected N₂)
    (hne₁ : N₁.Nonempty) (hne₂ : N₂.Nonempty)
    (hN₁sub : N₁ ⊆ N \ J) (hN₂sub : N₂ ⊆ N \ J)
    (hcov : N \ J ⊆ N₁ ∪ N₂) :
    ∀ n₁ ∈ N₁, ∀ n₂ ∈ N₂, n₂ ∉ connectedComponentIn Jᶜ n₁ := by
  sorry


/-! ### Sphere objects (Tasks B2, B3) -/

/-- Simple arc in the one-point compactification, from `x` to `y`. -/
def IsSphereArc (P : Set Sphere2) (x y : Sphere2) : Prop :=
  ∃ f : ℝ → Sphere2, P = f '' Icc 0 1 ∧ Continuous f ∧
    InjOn f (Icc 0 1) ∧ f 0 = x ∧ f 1 = y

/-! ### Task B2: separation of the two local sides, with a return arc through ∞ -/

/-- Let `R` and `G` be simple arcs of the sphere from `u` to `v` meeting only
at `u, v`, and let `q` be a plane point off `R ∪ G`.  Let `N ∌ q` be open in
the plane with `N` meeting `R ∪ G` exactly in `G \ {u, v}`, and `N₁ N₂` two
nonempty preconnected sets covering `N` off `R ∪ G`.  Then no preconnected set
`W` of plane points avoiding `q` and `R ∪ G` meets both `N₁` and `N₂`. -/
theorem sphere_local_sides_separated
    (q : Point) {R G : Set Sphere2} {u v : Sphere2} (huv : u ≠ v)
    (hR : IsSphereArc R u v) (hG : IsSphereArc G u v) (hRG : R ∩ G = {u, v})
    (hqR : finitePoint q ∉ R) (hqG : finitePoint q ∉ G)
    {N N₁ N₂ : Set Point} (hN : IsOpen N) (hqN : q ∉ N)
    (hNJ : finiteLift N ∩ (R ∪ G) = G \ {u, v})
    (hN₁ : IsPreconnected N₁) (hN₂ : IsPreconnected N₂)
    (hne₁ : N₁.Nonempty) (hne₂ : N₂.Nonempty)
    (hN₁N : N₁ ⊆ N) (hN₂N : N₂ ⊆ N)
    (hN₁J : ∀ p ∈ N₁, finitePoint p ∉ R ∪ G)
    (hN₂J : ∀ p ∈ N₂, finitePoint p ∉ R ∪ G)
    (hcov : ∀ p ∈ N, finitePoint p ∉ R ∪ G → p ∈ N₁ ∨ p ∈ N₂) :
    ∀ W : Set Point, IsPreconnected W → q ∉ W →
      (∀ p ∈ W, finitePoint p ∉ R ∪ G) →
      ∀ n₁ ∈ N₁, ∀ n₂ ∈ N₂, ¬ (n₁ ∈ W ∧ n₂ ∈ W) := by
  sorry

/-! ### Task B3: arcs to infinity and merging -/

/-- Concatenation of sphere arcs. -/
theorem IsSphereArc.trans {A B : Set Sphere2} {x y z : Sphere2}
    (hA : IsSphereArc A x y) (hB : IsSphereArc B y z) (hAB : A ∩ B = {y}) :
    IsSphereArc (A ∪ B) x z := by
  sorry

theorem IsSphereArc.symm {A : Set Sphere2} {x y : Sphere2}
    (hA : IsSphereArc A x y) : IsSphereArc A y x := by
  sorry

/-- If every point of `X` is joined to `∞` by a sphere arc inside `X`, then any
two distinct points of `X` are joined by a sphere arc inside `X`. -/
theorem sphereArc_merge {X : Set Sphere2}
    (hX : ∀ p ∈ X, p = infinity ∨ ∃ P ⊆ X, IsSphereArc P p infinity)
    (hinf : infinity ∈ X) {x y : Sphere2} (hx : x ∈ X) (hy : y ∈ X)
    (hxy : x ≠ y) :
    ∃ P ⊆ X, IsSphereArc P x y := by
  sorry

/-- Every point of the compactified lollipop carrier is joined to `∞` by an
arc inside the compactified carrier. -/
theorem hatCarrier_arc_to_infinity (L : Lollipop) :
    ∀ p ∈ hatCarrier L, p = infinity ∨
      ∃ P ⊆ hatCarrier L, IsSphereArc P p infinity := by
  sorry

/-- Lift of a planar simple arc to the sphere. -/
theorem IsSphereArc.of_planar {A : Set Point} {x y : Point}
    (hA : IsSimpleArcEnd A x y) :
    IsSphereArc (finiteLift A) (finitePoint x) (finitePoint y) := by
  sorry

/-- A stem ray together with `∞` is a sphere arc from its start point. -/
theorem raySet_isSphereArc (L : Lollipop) {s : ℝ} (hs : 1 ≤ s) :
    IsSphereArc (finiteLift (raySet L s) ∪ {infinity}) (finitePoint (stemPt L s)) infinity := by
  sorry

end Pieces
end EndToEnd
end Concrete
end Lollipop
