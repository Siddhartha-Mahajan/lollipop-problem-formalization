import Carrier.Defs
import Carrier.Defs2
import Carrier.CircleCollars
import Carrier.StemCollars
import Carrier.LocalSides
import Carrier.SphereArcs
import Carrier.SphereSides
import Carrier.HatArcs
import Carrier.Collar
import Carrier.Gap
import Carrier.Zarc
import Mathlib.Tactic

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace Pieces

open Set

namespace ArcPresAux

theorem finitePoint_ne_infinity (x : Point) : finitePoint x ≠ infinity := by
  intro h
  exact OnePoint.coe_ne_infty x h

theorem mem_hatSet_of_mem {D : Set Point} {x : Point} (hx : x ∈ D) :
    finitePoint x ∈ hatSet D := Or.inl ⟨x, hx, rfl⟩

theorem hatSet_mono {D X : Set Point} (h : D ⊆ X) : hatSet D ⊆ hatSet X := by
  rintro p (⟨x, hx, rfl⟩ | hp)
  · exact mem_hatSet_of_mem (h hx)
  · exact Or.inr hp

/-- Gluing a planar sub-arc ending in `D` with an arc to `∞` inside `hatSet D`. -/
theorem glue {D X A : Set Point} (hDX : D ⊆ X) (hArc : ArcConn D) {a b : Point}
    (hA : IsSphereArc (finiteLift A) (finitePoint a) (finitePoint b)) (hb : b ∈ D)
    (hAX : A ⊆ X) (hAD : ∀ y ∈ A, y ∈ D → y = b) :
    ∃ P ⊆ hatSet X, IsSphereArc P (finitePoint a) infinity := by
  rcases hArc (finitePoint b) (mem_hatSet_of_mem hb) with h | ⟨Q, hQ, hQarc⟩
  · exact absurd h (finitePoint_ne_infinity b)
  · have hbA : finitePoint b ∈ finiteLift A := by
      obtain ⟨f, hf, -, -, -, h1⟩ := hA
      rw [hf]; exact ⟨1, ⟨zero_le_one, le_rfl⟩, h1⟩
    have hbQ : finitePoint b ∈ Q := by
      obtain ⟨f, hf, -, -, h0, -⟩ := hQarc
      rw [hf]; exact ⟨0, ⟨le_rfl, zero_le_one⟩, h0⟩
    have hAQ : finiteLift A ∩ Q = {finitePoint b} := by
      ext q
      constructor
      · rintro ⟨⟨y, hy, rfl⟩, hq⟩
        have hqD := hQ hq
        rcases hqD with ⟨z, hz, hzq⟩ | hinf
        · have : z = y := finitePoint_injective hzq
          subst this
          rw [hAD z hy hz]; rfl
        · exact absurd hinf (finitePoint_ne_infinity y)
      · intro hq
        rw [mem_singleton_iff] at hq
        subst hq
        exact ⟨hbA, hbQ⟩
    refine ⟨finiteLift A ∪ Q, ?_, hA.trans hQarc hAQ⟩
    rintro q (⟨y, hy, rfl⟩ | hq)
    · exact mem_hatSet_of_mem (hAX hy)
    · exact hatSet_mono hDX (hQ hq)

theorem reduce {D E : Set Point} (hArc : ArcConn D)
    (hnew : ∀ x ∈ E, x ∉ D → ∃ P ⊆ hatSet (D ∪ E), IsSphereArc P (finitePoint x) infinity) :
    ArcConn (D ∪ E) := by
  intro p hp
  rcases hp with ⟨x, hx, rfl⟩ | hp
  · by_cases hxD : x ∈ D
    · rcases hArc (finitePoint x) (mem_hatSet_of_mem hxD) with h | ⟨P, hP, hPa⟩
      · exact Or.inl h
      · exact Or.inr ⟨P, fun q hq => hatSet_mono subset_union_left (hP hq), hPa⟩
    · rcases hx with hx | hx
      · exact absurd hx hxD
      · exact Or.inr (hnew x hx hxD)
  · exact Or.inl hp

theorem segCase (L : Lollipop) {D E : Set Point} (hArc : ArcConn D) {τ t : ℝ}
    (hτ : 1 ≤ τ) (hτt : τ < t) (hend : stemPt L t ∈ D)
    (hnot : ∀ σ, τ ≤ σ → σ < t → stemPt L σ ∉ D) (hsub : segSet L τ t ⊆ E) :
    ∃ P ⊆ hatSet (D ∪ E), IsSphereArc P (finitePoint (stemPt L τ)) infinity := by
  refine glue (A := segSet L τ t) subset_union_left hArc (segSubArc L hτ hτt) hend
    (hsub.trans subset_union_right) ?_
  rintro y ⟨σ, hσ, rfl⟩ hy
  rcases eq_or_lt_of_le hσ.2 with h | h
  · rw [h]
  · exact absurd hy (hnot σ hσ.1 h)

theorem circleCase (L : Lollipop) {D E : Set Point} (hArc : ArcConn D) {θ β : ℝ}
    (hθβ : θ < β) (hβ : β < θ + 2 * Real.pi) (hend : circlePt L β ∈ D)
    (hnot : ∀ σ, θ ≤ σ → σ < β → circlePt L σ ∉ D) (hsub : circleArcSet L θ β ⊆ E) :
    ∃ P ⊆ hatSet (D ∪ E), IsSphereArc P (finitePoint (circlePt L θ)) infinity := by
  refine glue (A := circleArcSet L θ β) subset_union_left hArc (circleSubArc L hθβ hβ) hend
    (hsub.trans subset_union_right) ?_
  rintro y ⟨σ, hσ, rfl⟩ hy
  rcases eq_or_lt_of_le hσ.2 with h | h
  · rw [h]
  · exact absurd hy (hnot σ hσ.1 h)

theorem rayCase (L : Lollipop) {D E : Set Point} {s τ : ℝ}
    (hs : 1 ≤ s) (hsτ : s ≤ τ) (hsub : raySet L s ⊆ E) :
    ∃ P ⊆ hatSet (D ∪ E), IsSphereArc P (finitePoint (stemPt L τ)) infinity := by
  refine ⟨finiteLift (raySet L τ) ∪ {infinity}, ?_, raySet_isSphereArc L (hs.trans hsτ)⟩
  rintro q (⟨y, hy, rfl⟩ | hq)
  · refine mem_hatSet_of_mem (Or.inr (hsub ?_))
    obtain ⟨σ, hσ, rfl⟩ := hy
    exact ⟨σ, le_trans hsτ hσ, rfl⟩
  · exact Or.inr hq

end ArcPresAux

open ArcPresAux

theorem arcConn_union_gap (L : Lollipop) {D : Set Point} (hD : IsClosed D)
    (hArc : ArcConn D) {E : Set Point} (hE : IsGapPiece L D E) :
    ArcConn (D ∪ E) := by
  refine reduce hArc ?_
  intro x hx hxD
  cases hE with
  | @circle α β hαβ hβ hopen hend =>
    obtain ⟨θ, hθ, rfl⟩ := hx
    have h1 : α < θ := lt_of_le_of_ne hθ.1 (by rintro rfl; exact hxD hend.1)
    have h2 : θ < β := lt_of_le_of_ne hθ.2 (by rintro rfl; exact hxD hend.2)
    refine circleCase L hArc h2 (by linarith) hend.2 ?_ ?_
    · intro σ hσ hσβ
      exact hopen σ ⟨lt_of_lt_of_le h1 hσ, hσβ⟩
    · rintro _ ⟨σ, hσ, rfl⟩
      exact ⟨σ, ⟨le_trans hθ.1 hσ.1, hσ.2⟩, rfl⟩
  | @seg s t hs hst hopen hend =>
    obtain ⟨τ, hτ, rfl⟩ := hx
    have h1 : s < τ := lt_of_le_of_ne hτ.1 (by rintro rfl; exact hxD hend.1)
    have h2 : τ < t := lt_of_le_of_ne hτ.2 (by rintro rfl; exact hxD hend.2)
    refine segCase L hArc (hs.trans h1.le) h2 hend.2 ?_ ?_
    · intro σ hσ hσt
      exact hopen σ ⟨lt_of_lt_of_le h1 hσ, hσt⟩
    · rintro _ ⟨σ, hσ, rfl⟩
      exact ⟨σ, ⟨le_trans hτ.1 hσ.1, hσ.2⟩, rfl⟩
  | @ray s hs hopen hend =>
    obtain ⟨τ, hτ, rfl⟩ := hx
    exact rayCase L hs hτ subset_rfl

theorem arcConn_union_leaf (L : Lollipop) {D : Set Point} (hD : IsClosed D)
    (hArc : ArcConn D) {E : Set Point} (hE : IsLeafPiece L D E) :
    ArcConn (D ∪ E) := by
  refine reduce hArc ?_
  intro x hx hxD
  cases hE with
  | @seg t ht hfree hopen hend =>
    obtain ⟨τ, hτ, rfl⟩ := hx
    have h2 : τ < t := lt_of_le_of_ne hτ.2 (by rintro rfl; exact hxD hend)
    refine segCase L hArc hτ.1 h2 hend ?_ ?_
    · intro σ hσ hσt
      rcases eq_or_lt_of_le (hτ.1.trans hσ) with h | h
      · rw [← h]; exact hfree
      · exact hopen σ ⟨h, hσt⟩
    · rintro _ ⟨σ, hσ, rfl⟩
      exact ⟨σ, ⟨le_trans hτ.1 hσ.1, hσ.2⟩, rfl⟩
  | ray hfree hopen =>
    obtain ⟨τ, hτ, rfl⟩ := hx
    exact rayCase L le_rfl hτ subset_rfl


end Pieces
end EndToEnd
end Concrete
end Lollipop
