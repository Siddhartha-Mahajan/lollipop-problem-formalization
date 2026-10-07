import Lollipop.Lemma_8_5.Proof
import Lollipop.Topology.Carrier.Defs

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace Pieces

open Set

theorem IsSphereArc.trans {A B : Set Sphere2} {x y z : Sphere2}
    (hA : IsSphereArc A x y) (hB : IsSphereArc B y z) (hAB : A ∩ B = {y}) :
    IsSphereArc (A ∪ B) x z := by
  obtain ⟨f, rfl, hfc, hfi, hf0, hf1⟩ := hA
  obtain ⟨g, rfl, hgc, hgi, hg0, hg1⟩ := hB
  refine ⟨fun t => if t ≤ 1/2 then f (2 * t) else g (2 * t - 1), ?_, ?_, ?_, ?_, ?_⟩
  · ext a
    constructor
    · rintro (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
      · refine ⟨s / 2, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
        have : s / 2 ≤ 1 / 2 := by linarith [hs.2]
        simp only [this, if_true]
        congr 1; ring
      · by_cases h0 : s = 0
        · subst h0
          refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
          simp only [le_refl, if_true]
          rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, hf1, hg0]
        · have hs0 : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm h0)
          refine ⟨(s + 1) / 2, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
          have : ¬ ((s + 1) / 2 ≤ 1 / 2) := by intro h; linarith
          simp only [this, if_false]
          congr 1; ring
    · rintro ⟨t, ht, rfl⟩
      by_cases h : t ≤ 1 / 2
      · simp only [h, if_true]
        exact Or.inl ⟨2 * t, ⟨by linarith [ht.1], by linarith⟩, rfl⟩
      · simp only [h, if_false]
        have h' : 1 / 2 < t := not_le.mp h
        exact Or.inr ⟨2 * t - 1, ⟨by linarith, by linarith [ht.2]⟩, rfl⟩
  · refine Continuous.if_le (hfc.comp (continuous_const.mul continuous_id))
      (hgc.comp ((continuous_const.mul continuous_id).sub continuous_const))
      continuous_id continuous_const ?_
    intro t ht
    have : t = 1 / 2 := ht
    subst this
    show f (2 * (1 / 2)) = g (2 * (1 / 2) - 1)
    rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, show (1 : ℝ) - 1 = 0 by norm_num, hf1, hg0]
  · intro s hs t ht hst
    simp only at hst
    by_cases h1 : s ≤ 1 / 2 <;> by_cases h2 : t ≤ 1 / 2
    · simp only [h1, h2, if_true] at hst
      have := hfi ⟨by linarith [hs.1], by linarith⟩ ⟨by linarith [ht.1], by linarith⟩ hst
      linarith
    · simp only [h1, h2, if_true, if_false] at hst
      exfalso
      have hmem : f (2 * s) ∈ (f '' Icc 0 1) ∩ (g '' Icc 0 1) :=
        ⟨⟨2 * s, ⟨by linarith [hs.1], by linarith⟩, rfl⟩,
          ⟨2 * t - 1, ⟨by linarith [not_le.mp h2], by linarith [ht.2]⟩, hst.symm⟩⟩
      rw [hAB] at hmem
      have e1 : f (2 * s) = f 1 := by rw [hf1]; exact hmem
      have e2 : g (2 * t - 1) = g 0 := by rw [hg0, ← hst]; exact hmem
      have := hgi ⟨by linarith [not_le.mp h2], by linarith [ht.2]⟩ ⟨le_refl _, by norm_num⟩ e2
      linarith [not_le.mp h2]
    · simp only [h1, h2, if_true, if_false] at hst
      exfalso
      have hmem : f (2 * t) ∈ (f '' Icc 0 1) ∩ (g '' Icc 0 1) :=
        ⟨⟨2 * t, ⟨by linarith [ht.1], by linarith⟩, rfl⟩,
          ⟨2 * s - 1, ⟨by linarith [not_le.mp h1], by linarith [hs.2]⟩, hst⟩⟩
      rw [hAB] at hmem
      have e2 : g (2 * s - 1) = g 0 := by rw [hg0, hst]; exact hmem
      have := hgi ⟨by linarith [not_le.mp h1], by linarith [hs.2]⟩ ⟨le_refl _, by norm_num⟩ e2
      linarith [not_le.mp h1]
    · simp only [h1, h2, if_false] at hst
      have := hgi ⟨by linarith [not_le.mp h1], by linarith [hs.2]⟩
        ⟨by linarith [not_le.mp h2], by linarith [ht.2]⟩ hst
      linarith
  · simp only [show (0 : ℝ) ≤ 1 / 2 by norm_num, if_true, mul_zero]
    exact hf0
  · have : ¬ ((1 : ℝ) ≤ 1 / 2) := by norm_num
    simp only [this, if_false]
    rw [show (2 : ℝ) * 1 - 1 = 1 by norm_num]
    exact hg1

theorem IsSphereArc.symm {A : Set Sphere2} {x y : Sphere2}
    (hA : IsSphereArc A x y) : IsSphereArc A y x := by
  obtain ⟨f, rfl, hfc, hfi, hf0, hf1⟩ := hA
  refine ⟨fun t => f (1 - t), ?_, ?_, ?_, ?_, ?_⟩
  · ext a
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨1 - s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, by simp⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨1 - s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, rfl⟩
  · exact hfc.comp (continuous_const.sub continuous_id)
  · intro s hs t ht hst
    have := hfi ⟨by linarith [hs.2], by linarith [hs.1]⟩ ⟨by linarith [ht.2], by linarith [ht.1]⟩ hst
    linarith
  · simp [hf1]
  · simp [hf0]

/-- Restricting an arc to `[0,t]`. -/
theorem isSphereArc_subarc {f : ℝ → Sphere2} (hc : Continuous f) (hi : InjOn f (Icc 0 1))
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    IsSphereArc (f '' Icc 0 t) (f 0) (f t) := by
  refine ⟨fun s => f (t * s), ?_, ?_, ?_, ?_, ?_⟩
  · ext a
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u / t, ⟨by have := hu.1; positivity, ?_⟩, ?_⟩
      · rw [div_le_one ht0]; exact hu.2
      · simp only; congr 1; field_simp
    · rintro ⟨s, hs, rfl⟩
      exact ⟨t * s, ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩, rfl⟩
  · exact hc.comp (continuous_const.mul continuous_id)
  · intro s hs u hu hsu
    have := hi ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
      ⟨by nlinarith [hu.1], by nlinarith [hu.2]⟩ hsu
    exact mul_left_cancel₀ ht0.ne' this
  · simp
  · simp

theorem sphereArc_merge {X : Set Sphere2}
    (hX : ∀ p ∈ X, p = infinity ∨ ∃ P ⊆ X, IsSphereArc P p infinity)
    (hinf : infinity ∈ X) {x y : Sphere2} (hx : x ∈ X) (hy : y ∈ X)
    (hxy : x ≠ y) :
    ∃ P ⊆ X, IsSphereArc P x y := by
  by_cases hxi : x = infinity
  · subst hxi
    rcases hX y hy with h | ⟨P, hPX, hP⟩
    · exact absurd h.symm hxy
    · exact ⟨P, hPX, hP.symm⟩
  by_cases hyi : y = infinity
  · subst hyi
    rcases hX x hx with h | ⟨P, hPX, hP⟩
    · exact absurd h hxi
    · exact ⟨P, hPX, hP⟩
  obtain ⟨Px, hPxX, fx, rfl, hxc, hxi', hx0, hx1⟩ :=
    (hX x hx).resolve_left hxi
  obtain ⟨Py, hPyX, fy, rfl, hyc, hyi', hy0, hy1⟩ :=
    (hX y hy).resolve_left hyi
  -- the closed set T
  have hPyclosed : IsClosed (fy '' Icc 0 1) := (isCompact_Icc.image hyc).isClosed
  set T : Set ℝ := Icc 0 1 ∩ fx ⁻¹' (fy '' Icc 0 1) with hT
  have hTclosed : IsClosed T := isClosed_Icc.inter (hPyclosed.preimage hxc)
  have h1T : (1 : ℝ) ∈ T := by
    refine ⟨⟨by norm_num, le_refl _⟩, ?_⟩
    show fx 1 ∈ fy '' Icc 0 1
    rw [hx1]
    exact ⟨1, ⟨by norm_num, le_refl _⟩, hy1⟩
  have hTne : T.Nonempty := ⟨1, h1T⟩
  have hTbdd : BddBelow T := ⟨0, fun t ht => ht.1.1⟩
  have hts : sInf T ∈ T := hTclosed.csInf_mem hTne hTbdd
  set ts := sInf T with hts_def
  obtain ⟨hts01, s, hs, hsp⟩ := hts
  have hmin : ∀ t ∈ Icc (0:ℝ) 1, fx t ∈ fy '' Icc 0 1 → ts ≤ t := fun t ht h =>
    csInf_le hTbdd ⟨ht, h⟩
  by_cases hts0 : ts = 0
  · -- p = x
    have hs0 : s ≠ 0 := by
      intro h0
      apply hxy
      calc x = fx ts := by rw [hts0, hx0]
        _ = fy s := hsp.symm
        _ = y := by rw [h0, hy0]
    have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    have := (isSphereArc_subarc hyc hyi' hspos hs.2).symm
    refine ⟨fy '' Icc 0 s, ?_, ?_⟩
    · exact fun a ha => hPyX (by
        obtain ⟨u, hu, rfl⟩ := ha
        exact ⟨u, ⟨hu.1, le_trans hu.2 hs.2⟩, rfl⟩)
    · rw [hsp, hts0, hx0, hy0] at this
      exact this
  by_cases hs0 : s = 0
  · -- p = y
    have htpos : 0 < ts := lt_of_le_of_ne hts01.1 (Ne.symm hts0)
    have := isSphereArc_subarc hxc hxi' htpos hts01.2
    refine ⟨fx '' Icc 0 ts, ?_, ?_⟩
    · exact fun a ha => hPxX (by
        obtain ⟨u, hu, rfl⟩ := ha
        exact ⟨u, ⟨hu.1, le_trans hu.2 hts01.2⟩, rfl⟩)
    · rw [← hsp, hs0, hy0, hx0] at this
      exact this
  · have htpos : 0 < ts := lt_of_le_of_ne hts01.1 (Ne.symm hts0)
    have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    have hA := isSphereArc_subarc hxc hxi' htpos hts01.2
    have hB := (isSphereArc_subarc hyc hyi' hspos hs.2).symm
    rw [hx0] at hA
    rw [hy0, hsp] at hB
    refine ⟨_, ?_, hA.trans hB ?_⟩
    · rintro a (ha | ha)
      · obtain ⟨u, hu, rfl⟩ := ha
        exact hPxX ⟨u, ⟨hu.1, le_trans hu.2 hts01.2⟩, rfl⟩
      · obtain ⟨u, hu, rfl⟩ := ha
        exact hPyX ⟨u, ⟨hu.1, le_trans hu.2 hs.2⟩, rfl⟩
    · ext q
      constructor
      · rintro ⟨⟨u, hu, rfl⟩, ⟨v, hv, hvq⟩⟩
        have hmem : fx u ∈ fy '' Icc 0 1 :=
          ⟨v, ⟨hv.1, le_trans hv.2 hs.2⟩, hvq⟩
        have := hmin u ⟨hu.1, le_trans hu.2 hts01.2⟩ hmem
        have : u = ts := le_antisymm hu.2 this
        subst this
        rfl
      · intro hq
        have hq : q = fx ts := hq
        subst hq
        exact ⟨⟨ts, ⟨hts01.1, le_refl _⟩, rfl⟩, ⟨s, ⟨hs.1, le_refl _⟩, hsp⟩⟩


end Pieces
end EndToEnd
end Concrete
end Lollipop
