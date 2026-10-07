import Carrier.Defs
import Carrier.Defs2
import Carrier.CircleCollars
import Carrier.StemCollars
import Carrier.LocalSides
import Carrier.SphereArcs
import Carrier.SphereSides
import Carrier.HatArcs
import Carrier.Collar
import Mathlib.Tactic

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace Pieces

open Set

namespace ZarcAux

theorem circlePt_eq_imp (L : Lollipop) {a b : ℝ} (hab : circlePt L a = circlePt L b) :
    ∃ k : ℤ, a - b = 2 * Real.pi * k := by
  have hr : L.radial 0 ^ 2 + L.radial 1 ^ 2 ≠ 0 := by
    intro h
    apply L.radial_ne_zero
    have h0 : L.radial 0 = 0 := by nlinarith [sq_nonneg (L.radial 0), sq_nonneg (L.radial 1)]
    have h1 : L.radial 1 = 0 := by nlinarith [sq_nonneg (L.radial 0), sq_nonneg (L.radial 1)]
    ext i; fin_cases i <;> simp [h0, h1]
  have e0 := congrArg (fun p : Point => p 0) hab
  have e1 := congrArg (fun p : Point => p 1) hab
  simp only [HatAux.circlePt_comp, perp] at e0 e1
  simp at e0 e1
  have hc : Real.cos a = Real.cos b := by
    have : (Real.cos a - Real.cos b) * (L.radial 0 ^ 2 + L.radial 1 ^ 2) = 0 := by
      linear_combination L.radial 0 * e0 + L.radial 1 * e1
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h hr
  have hs : Real.sin a = Real.sin b := by
    have : (Real.sin a - Real.sin b) * (L.radial 0 ^ 2 + L.radial 1 ^ 2) = 0 := by
      linear_combination L.radial 0 * e1 - L.radial 1 * e0
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h hr
  have hang := Real.Angle.cos_sin_inj hc hs
  exact Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 hang

theorem circlePt_add_int (L : Lollipop) (b : ℝ) (k : ℤ) :
    circlePt L (b + 2 * Real.pi * k) = circlePt L b := by
  unfold circlePt
  have h1 : Real.cos (b + 2 * Real.pi * k) = Real.cos b := by
    rw [mul_comm (2 * Real.pi) (k : ℝ)]; exact Real.cos_add_int_mul_two_pi b k
  have h2 : Real.sin (b + 2 * Real.pi * k) = Real.sin b := by
    rw [mul_comm (2 * Real.pi) (k : ℝ)]; exact Real.sin_add_int_mul_two_pi b k
  rw [h1, h2]

theorem circlePt_injOn_of_lt (L : Lollipop) {x y : ℝ} (hy : y < x + 2 * Real.pi) :
    InjOn (circlePt L) (Icc x y) := by
  intro a ha b hb hab
  obtain ⟨k, hk⟩ := circlePt_eq_imp L hab
  have hpi := Real.pi_pos
  have h1 : (k : ℝ) < 1 := by nlinarith [ha.1, ha.2, hb.1, hb.2]
  have h2 : (-1 : ℝ) < k := by nlinarith [ha.1, ha.2, hb.1, hb.2]
  have h1' : k < 1 := by exact_mod_cast h1
  have h2' : -1 < k := by exact_mod_cast h2
  have hk0 : k = 0 := by omega
  rw [hk0] at hk
  simp at hk
  linarith

end ZarcAux

namespace ZarcAux

theorem circle_eq_range (M : Lollipop) : M.circle = range (circlePt M) := by
  ext x
  constructor
  · intro hx
    obtain ⟨θ, -, rfl⟩ := HatAux.circle_exists_angle M hx
    exact ⟨θ, rfl⟩
  · rintro ⟨θ, rfl⟩
    exact HatAux.circlePt_mem_circle M θ

theorem circle_diff (M : Lollipop) (θ : ℝ) :
    M.circle \ {circlePt M θ} = circlePt M '' Ioo θ (θ + 2 * Real.pi) := by
  have hpi := Real.pi_pos
  ext x
  constructor
  · rintro ⟨hx, hxθ⟩
    obtain ⟨φ, -, rfl⟩ := HatAux.circle_exists_angle M hx
    set φ' := toIocMod Real.two_pi_pos θ φ with hφ'
    have hmem : φ' ∈ Ioc θ (θ + 2 * Real.pi) := toIocMod_mem_Ioc Real.two_pi_pos θ φ
    have hφeq : φ' = φ - toIocDiv Real.two_pi_pos θ φ • (2 * Real.pi) := rfl
    have hcp : circlePt M φ' = circlePt M φ := by
      have := ZarcAux.circlePt_add_int M φ (-(toIocDiv Real.two_pi_pos θ φ))
      rw [hφeq, zsmul_eq_mul]
      convert this using 2
      push_cast; ring
    refine ⟨φ', ⟨hmem.1, lt_of_le_of_ne hmem.2 ?_⟩, hcp⟩
    intro h
    apply hxθ
    rw [← hcp, h]
    have := ZarcAux.circlePt_add_int M θ 1
    simpa using this
  · rintro ⟨φ, hφ, rfl⟩
    refine ⟨HatAux.circlePt_mem_circle M φ, ?_⟩
    intro h
    have h' : circlePt M φ = circlePt M θ := h
    obtain ⟨k, hk⟩ := circlePt_eq_imp M h'
    have h1 : (k : ℝ) < 1 := by nlinarith [hφ.1, hφ.2]
    have h2 : (0 : ℝ) < k := by nlinarith [hφ.1, hφ.2]
    have h1' : k < 1 := by exact_mod_cast h1
    have h2' : 0 < k := by exact_mod_cast h2
    omega

theorem circle_diff_preconnected (M : Lollipop) {q : Point} (hq : q ∈ M.circle) :
    IsPreconnected (finiteLift M.circle \ {finitePoint q}) := by
  obtain ⟨θ, -, rfl⟩ := HatAux.circle_exists_angle M hq
  have : finiteLift M.circle \ {finitePoint (circlePt M θ)} =
      (fun t => finitePoint (circlePt M t)) '' Ioo θ (θ + 2 * Real.pi) := by
    unfold finiteLift
    rw [← image_singleton, ← Set.image_diff finitePoint_injective, circle_diff, image_image]
  rw [this]
  exact (isPreconnected_Ioo).image _
    ((HatAux.continuous_finitePoint.comp (HatAux.continuous_circlePt M)).continuousOn)

theorem circle_preconnected (M : Lollipop) : IsPreconnected (finiteLift M.circle) := by
  unfold finiteLift
  rw [circle_eq_range, ← image_univ, image_image]
  exact isPreconnected_univ.image _
    ((HatAux.continuous_finitePoint.comp (HatAux.continuous_circlePt M)).continuousOn)

/-- no continuous injection of `[0,1]`-subset onto circle: core real-line statement. -/
theorem core {S : Set ℝ} {a b : ℝ} (hab : a < b) (ha : a ∈ S) (hb : b ∈ S)
    (hS : IsPreconnected S)
    (hdiff : ∀ z ∈ S, IsPreconnected (S \ {z})) : False := by
  have hz : (a + b) / 2 ∈ S := hS.ordConnected.out ha hb ⟨by linarith, by linarith⟩
  have h := (hdiff _ hz).ordConnected.out (x := a) (y := b)
    ⟨ha, by intro h; rw [mem_singleton_iff] at h; linarith⟩
    ⟨hb, by intro h; rw [mem_singleton_iff] at h; linarith⟩
    (show (a + b) / 2 ∈ Icc a b from ⟨by linarith, by linarith⟩)
  exact h.2 rfl

end ZarcAux

/-- A simple sphere arc cannot contain a whole circle. -/
theorem sphereArc_not_contains_circle {P : Set Sphere2} {x y : Sphere2}
    (hP : IsSphereArc P x y) (M : Lollipop) : ¬ finiteLift M.circle ⊆ P := by
  intro hsub
  obtain ⟨f, hPf, hc, hinj, -, -⟩ := hP
  set C : Set Sphere2 := finiteLift M.circle with hC
  let F : Icc (0:ℝ) 1 → Sphere2 := fun t => f t
  have hFc : Continuous F := hc.comp continuous_subtype_val
  have hFi : Function.Injective F := by
    intro a b hab
    exact Subtype.ext (hinj a.2 b.2 hab)
  have hemb : Topology.IsEmbedding F := (hFc.isClosedEmbedding hFi).isEmbedding
  have hCsub : C ⊆ range F := by
    intro p hp
    obtain ⟨t, ht, rfl⟩ := hPf ▸ hsub hp
    exact ⟨⟨t, ht⟩, rfl⟩
  set T : Set (Icc (0:ℝ) 1) := F ⁻¹' C with hT
  have hFT : F '' T = C := image_preimage_eq_of_subset hCsub
  have hTpre : IsPreconnected T := by
    rw [← hemb.isInducing.isPreconnected_image, hFT]
    exact ZarcAux.circle_preconnected M
  set S : Set ℝ := Subtype.val '' T with hS
  have hSpre : IsPreconnected S := hTpre.image _ continuous_subtype_val.continuousOn
  have hdiff : ∀ z ∈ S, IsPreconnected (S \ {z}) := by
    intro z hz
    obtain ⟨s, hsT, rfl⟩ := hz
    have hFs : F s ∈ C := hsT
    obtain ⟨q, hq, hqs⟩ := hFs
    have h1 : IsPreconnected (T \ {s}) := by
      rw [← hemb.isInducing.isPreconnected_image, image_diff hFi, hFT, image_singleton,
        ← hqs]
      exact ZarcAux.circle_diff_preconnected M hq
    have h2 : IsPreconnected (Subtype.val '' (T \ {s})) :=
      h1.image _ continuous_subtype_val.continuousOn
    have h3 : Subtype.val '' (T \ {s}) = S \ {s.1} := by
      rw [hS, image_diff Subtype.val_injective, image_singleton]
    rwa [h3] at h2
  -- two distinct points of S
  have hc1 : finitePoint (circlePt M 0) ∈ C := ⟨_, HatAux.circlePt_mem_circle M 0, rfl⟩
  have hc2 : finitePoint (circlePt M Real.pi) ∈ C :=
    ⟨_, HatAux.circlePt_mem_circle M Real.pi, rfl⟩
  have hne : finitePoint (circlePt M 0) ≠ finitePoint (circlePt M Real.pi) := by
    intro h
    obtain ⟨k, hk⟩ := ZarcAux.circlePt_eq_imp M (finitePoint_injective h)
    have hpi := Real.pi_pos
    have : (2 * (k : ℝ) + 1) * Real.pi = 0 := by linarith
    have h0 : (2 * (k : ℝ) + 1) = 0 := by
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd h hpi.ne'
    have : (2 * k + 1 : ℤ) = 0 := by exact_mod_cast h0
    omega
  rw [← hFT] at hc1 hc2
  obtain ⟨s1, hs1⟩ := hc1
  obtain ⟨s2, hs2⟩ := hc2
  have hs12 : s1.1 ≠ s2.1 := by
    intro h
    apply hne
    rw [← hs1.2, ← hs2.2, Subtype.ext h]
  rcases lt_or_gt_of_ne hs12 with h | h
  · exact ZarcAux.core (S := S) h ⟨s1, hs1.1, rfl⟩ ⟨s2, hs2.1, rfl⟩ hSpre hdiff
  · exact ZarcAux.core (S := S) h ⟨s2, hs2.1, rfl⟩ ⟨s1, hs1.1, rfl⟩ hSpre hdiff

/-- Closed sub-arc of a lollipop circle, as a sphere arc. -/
theorem circleSubArc (L : Lollipop) {x y : ℝ} (hxy : x < y) (hy : y < x + 2 * Real.pi) :
    IsSphereArc (finiteLift (circleArcSet L x y))
      (finitePoint (circlePt L x)) (finitePoint (circlePt L y)) := by
  apply IsSphereArc.of_planar
  refine ⟨fun t => circlePt L (x + t * (y - x)), ?_, ?_, ?_, ?_, ?_⟩
  · ext p
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      refine ⟨(φ - x) / (y - x), ⟨?_, ?_⟩, ?_⟩
      · exact div_nonneg (by linarith [hφ.1]) (by linarith)
      · rw [div_le_one (by linarith)]; linarith [hφ.2]
      · simp only
        congr 1
        rw [div_mul_cancel₀ _ (by linarith : y - x ≠ 0)]; ring
    · rintro ⟨t, ht, rfl⟩
      exact ⟨x + t * (y - x), ⟨by nlinarith [ht.1, ht.2], by nlinarith [ht.1, ht.2]⟩, rfl⟩
  · exact (HatAux.continuous_circlePt L).comp (by fun_prop)
  · intro a ha b hb hab
    have key := ZarcAux.circlePt_injOn_of_lt L hy
    have := @key (x + a * (y - x))
      ⟨by nlinarith [ha.1, ha.2], by nlinarith [ha.1, ha.2]⟩ (x + b * (y - x))
      ⟨by nlinarith [hb.1, hb.2], by nlinarith [hb.1, hb.2]⟩ hab
    have h2 : (a - b) * (y - x) = 0 := by linarith
    rcases mul_eq_zero.1 h2 with h | h
    · linarith
    · linarith
  · simp
  · simp

/-- Closed stem segment, as a sphere arc. -/
theorem segSubArc (L : Lollipop) {s t : ℝ} (hs : 1 ≤ s) (hst : s < t) :
    IsSphereArc (finiteLift (segSet L s t))
      (finitePoint (stemPt L s)) (finitePoint (stemPt L t)) := by
  apply IsSphereArc.of_planar
  refine ⟨fun u => stemPt L (s + u * (t - s)), ?_, ?_, ?_, ?_, ?_⟩
  · ext p
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      refine ⟨(φ - s) / (t - s), ⟨?_, ?_⟩, ?_⟩
      · exact div_nonneg (by linarith [hφ.1]) (by linarith)
      · rw [div_le_one (by linarith)]; linarith [hφ.2]
      · simp only
        congr 1
        rw [div_mul_cancel₀ _ (by linarith : t - s ≠ 0)]; ring
    · rintro ⟨u, hu, rfl⟩
      exact ⟨s + u * (t - s), ⟨by nlinarith [hu.1, hu.2], by nlinarith [hu.1, hu.2]⟩, rfl⟩
  · exact L.continuous_stemMap.comp (by fun_prop)
  · intro a ha b hb hab
    have := HatAux.stemPt_injective L hab
    have h2 : (a - b) * (t - s) = 0 := by linarith
    rcases mul_eq_zero.1 h2 with h | h
    · linarith
    · linarith
  · simp
  · simp


end Pieces
end EndToEnd
end Concrete
end Lollipop
