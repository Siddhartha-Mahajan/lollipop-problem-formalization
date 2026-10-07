import Carrier.Defs
import Mathlib.Analysis.SpecialFunctions.PolarCoord

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace Pieces

open Set

/-! ### Helper lemmas -/

namespace CircleAux

variable (L : Lollipop)

lemma circlePt_apply0 (θ : ℝ) :
    circlePt L θ 0 = L.center 0 + Real.cos θ * L.radial 0 - Real.sin θ * L.radial 1 := by
  simp [circlePt, perp]; ring

lemma circlePt_apply1 (θ : ℝ) :
    circlePt L θ 1 = L.center 1 + Real.cos θ * L.radial 1 + Real.sin θ * L.radial 0 := by
  simp [circlePt, perp]

lemma radius_sq : L.radius ^ 2 = L.radial 0 ^ 2 + L.radial 1 ^ 2 := by
  unfold Lollipop.radius
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_two]

lemma norm_circlePt_sub (θ : ℝ) : ‖circlePt L θ - L.center‖ = L.radius := by
  have h : ‖circlePt L θ - L.center‖ ^ 2 = L.radius ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, radius_sq]
    simp only [Fin.sum_univ_two, PiLp.sub_apply, circlePt_apply0, circlePt_apply1, Real.norm_eq_abs,
      sq_abs]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  exact (sq_eq_sq₀ (norm_nonneg _) (L.radius_pos.le)).1 h

lemma continuous_circlePt : Continuous (circlePt L) := by
  unfold circlePt; fun_prop


lemma exists_width {D : Set Point} (hD : IsClosed D) {α β : ℝ}
    (hopen : ∀ θ ∈ Ioo α β, circlePt L θ ∉ D) :
    ∃ w : ℝ → ℝ, Continuous w ∧ (∀ θ, w θ ≤ L.radius / 2) ∧ (∀ θ ∈ Ioo α β, 0 < w θ) ∧
      ∀ θ ∈ Ioo α β, ∀ z ∈ D, w θ < dist (circlePt L θ) z := by
  by_cases hne : D.Nonempty
  · refine ⟨fun θ => min (L.radius / 2) (Metric.infDist (circlePt L θ) D / 2), ?_, ?_, ?_, ?_⟩
    · exact continuous_const.min
        (((Metric.continuous_infDist_pt D).comp (continuous_circlePt L)).div_const 2)
    · intro θ; exact min_le_left _ _
    · intro θ hθ
      exact lt_min (by have := L.radius_pos; positivity)
        (div_pos ((hD.notMem_iff_infDist_pos hne).1 (hopen θ hθ)) two_pos)
    · intro θ hθ z hz
      have h1 : Metric.infDist (circlePt L θ) D ≤ dist (circlePt L θ) z :=
        Metric.infDist_le_dist_of_mem hz
      have h2 : 0 < Metric.infDist (circlePt L θ) D := (hD.notMem_iff_infDist_pos hne).1 (hopen θ hθ)
      calc _ ≤ Metric.infDist (circlePt L θ) D / 2 := min_le_right _ _
        _ < _ := by linarith
  · have hD' : D = ∅ := not_nonempty_iff_eq_empty.1 hne
    refine ⟨fun _ => L.radius / 2, continuous_const, fun _ => le_rfl, ?_, ?_⟩
    · intro θ _; have := L.radius_pos; positivity
    · intro θ _ z hz; rw [hD'] at hz; exact absurd hz (notMem_empty z)

/-- The tube map. -/
def tube (w : ℝ → ℝ) (p : ℝ × ℝ) : Point :=
  L.center + ((L.radius + p.2 * w p.1) / L.radius) • (circlePt L p.1 - L.center)

lemma tube_zero (w : ℝ → ℝ) (θ : ℝ) : tube L w (θ, 0) = circlePt L θ := by
  have hr := L.radius_ne_zero
  simp [tube, hr]

lemma continuous_tube {w : ℝ → ℝ} (hw : Continuous w) : Continuous (tube L w) := by
  have := continuous_circlePt L
  unfold tube
  fun_prop

lemma norm_tube_sub (w : ℝ → ℝ) (p : ℝ × ℝ) (h : 0 ≤ L.radius + p.2 * w p.1) :
    ‖tube L w p - L.center‖ = L.radius + p.2 * w p.1 := by
  have hr := L.radius_pos
  unfold tube
  rw [add_sub_cancel_left, norm_smul, norm_circlePt_sub, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg h hr.le)]
  field_simp

lemma dist_tube (w : ℝ → ℝ) (θ u : ℝ) :
    dist (circlePt L θ) (tube L w (θ, u)) = |u * w θ| := by
  have hr := L.radius_pos
  rw [dist_eq_norm]
  have : circlePt L θ - tube L w (θ, u) = (-(u * w θ) / L.radius) • (circlePt L θ - L.center) := by
    unfold tube
    simp only
    rw [sub_eq_iff_eq_add]
    ext i
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    field_simp
    ring
  rw [this, norm_smul, norm_circlePt_sub, Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos hr]
  field_simp


/-- KEY LEMMA: the tube map is open on `Ioo α β ×ˢ Ioo (-1) 1`. -/
lemma isOpen_image_tube {w : ℝ → ℝ} (hw : Continuous w) {α β : ℝ} (hβ : β ≤ α + 2 * Real.pi)
    (hwle : ∀ θ, w θ ≤ L.radius / 2) (hwpos : ∀ θ ∈ Ioo α β, 0 < w θ)
    {V : Set (ℝ × ℝ)} (hV : IsOpen V) (hVsub : V ⊆ Ioo α β ×ˢ Ioo (-1 : ℝ) 1) :
    IsOpen (tube L w '' V) := by
  have hr := L.radius_pos
  set m : ℝ := (α + β) / 2 with hm
  -- frame
  set a : ℝ := (Real.cos m * L.radial 0 - Real.sin m * L.radial 1) / L.radius with ha
  set b : ℝ := (Real.cos m * L.radial 1 + Real.sin m * L.radial 0) / L.radius with hb
  have hab : a ^ 2 + b ^ 2 = 1 := by
    have h := radius_sq L
    have h2 : a ^ 2 + b ^ 2 = (L.radial 0 ^ 2 + L.radial 1 ^ 2) / L.radius ^ 2 := by
      rw [ha, hb]; field_simp; nlinarith [Real.sin_sq_add_cos_sq m]
    rw [h2, ← h]; field_simp
  let Ψ : ℝ × ℝ → Point := fun p =>
    !₂[L.center 0 + p.1 * a - p.2 * b, L.center 1 + p.1 * b + p.2 * a]
  have hΨ0 : ∀ p, Ψ p 0 = L.center 0 + p.1 * a - p.2 * b := fun p => rfl
  have hΨ1 : ∀ p, Ψ p 1 = L.center 1 + p.1 * b + p.2 * a := fun p => rfl
  let Ψi : Point → ℝ × ℝ := fun x =>
    (a * (x 0 - L.center 0) + b * (x 1 - L.center 1),
      -b * (x 0 - L.center 0) + a * (x 1 - L.center 1))
  have hΨi : Continuous Ψi := by
    have h0 : Continuous fun x : Point => x 0 := (EuclideanSpace.proj (0 : Fin 2)).continuous
    have h1 : Continuous fun x : Point => x 1 := (EuclideanSpace.proj (1 : Fin 2)).continuous
    show Continuous fun x : Point => (a * (x 0 - L.center 0) + b * (x 1 - L.center 1),
      -b * (x 0 - L.center 0) + a * (x 1 - L.center 1))
    fun_prop
  have hΨ_open : ∀ O : Set (ℝ × ℝ), IsOpen O → IsOpen (Ψ '' O) := by
    intro O hO
    have : Ψ '' O = Ψi ⁻¹' O := by
      ext x
      constructor
      · rintro ⟨p, hp, rfl⟩
        have : Ψi (Ψ p) = p := by
          obtain ⟨p1, p2⟩ := p
          show (a * (Ψ (p1, p2) 0 - L.center 0) + b * (Ψ (p1, p2) 1 - L.center 1),
            -b * (Ψ (p1, p2) 0 - L.center 0) + a * (Ψ (p1, p2) 1 - L.center 1)) = (p1, p2)
          rw [hΨ0, hΨ1]
          ext
          · show _ = p1
            dsimp only
            linear_combination p1 * hab
          · show _ = p2
            dsimp only
            linear_combination p2 * hab
        show Ψi (Ψ p) ∈ O
        rw [this]; exact hp
      · intro hx
        refine ⟨Ψi x, hx, ?_⟩
        ext i
        fin_cases i
        · show Ψ (Ψi x) 0 = x 0
          rw [hΨ0]
          show L.center 0 + (a * (x 0 - L.center 0) + b * (x 1 - L.center 1)) * a -
            (-b * (x 0 - L.center 0) + a * (x 1 - L.center 1)) * b = x 0
          linear_combination (x 0 - L.center 0) * hab
        · show Ψ (Ψi x) 1 = x 1
          rw [hΨ1]
          show L.center 1 + (a * (x 0 - L.center 0) + b * (x 1 - L.center 1)) * b +
            (-b * (x 0 - L.center 0) + a * (x 1 - L.center 1)) * a = x 1
          linear_combination (x 1 - L.center 1) * hab
    rw [this]; exact hO.preimage hΨi
  -- key identity
  have hid : ∀ p : ℝ × ℝ, tube L w p = Ψ (polarCoord.symm (L.radius + p.2 * w p.1, p.1 - m)) := by
    rintro ⟨θ, u⟩
    have hc : Real.cos θ = Real.cos (θ - m) * Real.cos m - Real.sin (θ - m) * Real.sin m := by
      rw [← Real.cos_add]; congr 1; ring
    have hs : Real.sin θ = Real.sin (θ - m) * Real.cos m + Real.cos (θ - m) * Real.sin m := by
      rw [← Real.sin_add]; congr 1; ring
    have hr' : L.radius ≠ 0 := hr.ne'
    ext i
    fin_cases i
    · show tube L w (θ, u) 0 = Ψ _ 0
      rw [hΨ0]
      simp only [tube, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
        circlePt_apply0, smul_eq_mul, polarCoord_symm_apply]
      rw [hc, hs, ha, hb]; field_simp; ring
    · show tube L w (θ, u) 1 = Ψ _ 1
      rw [hΨ1]
      simp only [tube, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
        circlePt_apply1, smul_eq_mul, polarCoord_symm_apply]
      rw [hc, hs, ha, hb]; field_simp; ring
  let F : ℝ × ℝ → ℝ × ℝ := fun p => (L.radius + p.2 * w p.1, p.1 - m)
  let G : ℝ × ℝ → ℝ × ℝ := fun q => (q.2 + m, (q.1 - L.radius) / w (q.2 + m))
  let W : Set (ℝ × ℝ) := {q | q.2 + m ∈ Ioo α β}
  have hW : IsOpen W :=
    isOpen_Ioo.preimage (continuous_snd.add continuous_const)
  have hGc : ContinuousOn G W := by
    apply ContinuousOn.prodMk
    · exact (continuous_snd.add continuous_const).continuousOn
    · apply ContinuousOn.div
      · exact (continuous_fst.sub continuous_const).continuousOn
      · exact (hw.comp (continuous_snd.add continuous_const)).continuousOn
      · intro q hq; exact (hwpos _ hq).ne'
  have hFV : F '' V = W ∩ G ⁻¹' V := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨hp1, hp2⟩ := hVsub hp
      have hp1' : p.1 ∈ Ioo α β := hp1
      have hwp := hwpos _ hp1'
      refine ⟨?_, ?_⟩
      · show p.1 - m + m ∈ Ioo α β
        simpa using hp1'
      · show G (F p) ∈ V
        have : G (F p) = p := by
          obtain ⟨p1, p2⟩ := p
          simp only [G, F]
          have : p1 - m + m = p1 := by ring
          rw [this]
          ext
          · rfl
          · show (L.radius + p2 * w p1 - L.radius) / w p1 = p2
            field_simp at hwp ⊢
            ring
        rw [this]; exact hp
    · rintro ⟨hq, hGq⟩
      refine ⟨G q, hGq, ?_⟩
      have hwp := hwpos _ hq
      obtain ⟨q1, q2⟩ := q
      simp only [G, F]
      ext
      · show L.radius + (q1 - L.radius) / w (q2 + m) * w (q2 + m) = q1
        field_simp
        ring
      · show q2 + m - m = q2
        ring
  have hFopen : IsOpen (F '' V) := by
    rw [hFV]; exact hGc.isOpen_inter_preimage hW hV
  have hsub : F '' V ⊆ polarCoord.symm.source := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨hp1, hp2⟩ := hVsub hp
    have hp1' : p.1 ∈ Ioo α β := hp1
    have hp2' : p.2 ∈ Ioo (-1 : ℝ) 1 := hp2
    have hwp := hwpos _ hp1'
    have hwl := hwle p.1
    rw [OpenPartialHomeomorph.symm_source, polarCoord_target]
    refine ⟨?_, ?_, ?_⟩
    · show 0 < L.radius + p.2 * w p.1
      nlinarith [hp2'.1, hp2'.2]
    · show -Real.pi < p.1 - m
      have := hp1'.1; have := hp1'.2
      rw [hm]; linarith
    · show p.1 - m < Real.pi
      have := hp1'.1; have := hp1'.2
      rw [hm]; linarith
  have h1 : IsOpen (polarCoord.symm '' (F '' V)) :=
    polarCoord.symm.isOpen_image_of_subset_source hFopen hsub
  have h2 : tube L w '' V = Ψ '' (polarCoord.symm '' (F '' V)) := by
    rw [image_image, image_image]
    exact image_congr (fun p _ => hid p)
  rw [h2]
  exact hΨ_open _ h1


lemma tube_nonneg {w : ℝ → ℝ} (hwle : ∀ θ, w θ ≤ L.radius / 2) {θ u : ℝ} (hw : 0 < w θ)
    (hu : u ∈ Ioo (-1 : ℝ) 1) : 0 ≤ L.radius + u * w θ := by
  have := L.radius_pos
  have h1 := hu.1; have h2 := hu.2; have h3 := hwle θ
  nlinarith

lemma u_eq_zero_of_circle {w : ℝ → ℝ} (hwle : ∀ θ, w θ ≤ L.radius / 2) {θ u : ℝ}
    (hw : 0 < w θ) (hu : u ∈ Ioo (-1 : ℝ) 1) {θ' : ℝ} (h : tube L w (θ, u) = circlePt L θ') :
    u = 0 := by
  have h1 := norm_tube_sub L w (θ, u) (tube_nonneg L hwle hw hu)
  rw [h, norm_circlePt_sub] at h1
  have : u * w θ = 0 := by simp only at h1; linarith
  rcases mul_eq_zero.1 this with h0 | h0
  · exact h0
  · exact absurd h0 hw.ne'

lemma tube_norm_lt {w : ℝ → ℝ} (hwle : ∀ θ, w θ ≤ L.radius / 2) {θ u : ℝ}
    (hw : 0 < w θ) (hu : u ∈ Ioo (-1 : ℝ) 1) (hneg : u < 0) {θ' : ℝ}
    (h : tube L w (θ, u) = circlePt L θ') : False := by
  have := u_eq_zero_of_circle L hwle hw hu h
  linarith

lemma tube_not_circle_pos {w : ℝ → ℝ} (hwle : ∀ θ, w θ ≤ L.radius / 2) {θ u : ℝ}
    (hw : 0 < w θ) (hu : u ∈ Ioo (-1 : ℝ) 1) (hne : u ≠ 0) {θ' : ℝ}
    (h : tube L w (θ, u) = circlePt L θ') : False :=
  hne (u_eq_zero_of_circle L hwle hw hu h)

lemma preconnected_tube_image {w : ℝ → ℝ} (hw : Continuous w) {a b c d : ℝ} :
    IsPreconnected (tube L w '' (Ioo a b ×ˢ Ioo c d)) := by
  have hc : Convex ℝ (Ioo a b ×ˢ Ioo c d) := (convex_Ioo a b).prod (convex_Ioo c d)
  exact hc.isPreconnected.image _ (continuous_tube L hw).continuousOn

end CircleAux
open CircleAux


/-- Collars (with germs) for a circular arc. -/
theorem circle_collars (L : Lollipop) {D : Set Point} (hD : IsClosed D)
    {α β : ℝ} (hαβ : α < β) (hβ : β ≤ α + 2 * Real.pi)
    (hopen : ∀ θ ∈ Ioo α β, circlePt L θ ∉ D)
    (hend : circlePt L α ∈ D ∧ circlePt L β ∈ D) :
    ∃ U S₁ S₂ : Set Point,
      Collars D (circleArcSet L α β) S₁ S₂ U ∧
      ∀ θ₀ ∈ Ioo α β, ∀ δ : ℝ, 0 < δ → Icc (θ₀ - δ) (θ₀ + δ) ⊆ Ioo α β →
        Germ (circleArcSet L α β) S₁ S₂ U (circlePt L '' Ioo (θ₀ - δ) (θ₀ + δ)) := by
  obtain ⟨w, hw, hwle, hwpos, hwdist⟩ := exists_width L hD hopen
  have hΩ : IsOpen (Ioo α β ×ˢ Ioo (-1 : ℝ) 1) := isOpen_Ioo.prod isOpen_Ioo
  have hmid : (α + β) / 2 ∈ Ioo α β := ⟨by linarith, by linarith⟩
  refine ⟨tube L w '' (Ioo α β ×ˢ Ioo (-1 : ℝ) 1),
    tube L w '' (Ioo α β ×ˢ Ioo (-1 : ℝ) 0), tube L w '' (Ioo α β ×ˢ Ioo (0 : ℝ) 1), ?_, ?_⟩
  · refine
      { isOpen_U := isOpen_image_tube L hw hβ hwle hwpos hΩ subset_rfl
        new_sub := ?_
        U_sub := ?_
        pre₁ := preconnected_tube_image L hw
        pre₂ := preconnected_tube_image L hw
        sub₁ := ?_
        sub₂ := ?_
        cover := ?_
        ne₁ := ?_
        ne₂ := ?_ }
    · rintro z ⟨θ, hθ, rfl⟩ hzD
      have hθα : θ ≠ α := by rintro rfl; exact hzD hend.1
      have hθβ : θ ≠ β := by rintro rfl; exact hzD hend.2
      have hθ' : θ ∈ Ioo α β := ⟨lt_of_le_of_ne hθ.1 (Ne.symm hθα), lt_of_le_of_ne hθ.2 hθβ⟩
      exact ⟨(θ, 0), ⟨hθ', by norm_num, by norm_num⟩, tube_zero L w θ⟩
    · rintro _ ⟨⟨θ, u⟩, ⟨hθ, hu⟩, rfl⟩ hD'
      have h1 := hwdist θ hθ _ hD'
      rw [dist_tube] at h1
      have h2 : |u * w θ| ≤ w θ := by
        rw [abs_mul, abs_of_pos (hwpos θ hθ)]
        have : |u| ≤ 1 := abs_le.2 ⟨hu.1.le, hu.2.le⟩
        nlinarith [hwpos θ hθ]
      linarith
    · rintro _ ⟨⟨θ, u⟩, ⟨hθ, hu⟩, rfl⟩
      have hu' : u ∈ Ioo (-1 : ℝ) 1 := ⟨hu.1, by linarith [hu.2]⟩
      refine ⟨⟨(θ, u), ⟨hθ, hu'⟩, rfl⟩, ?_⟩
      rintro ⟨θ', _, h⟩
      exact tube_norm_lt L hwle (hwpos θ hθ) hu' hu.2 h.symm
    · rintro _ ⟨⟨θ, u⟩, ⟨hθ, hu⟩, rfl⟩
      have hu' : u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.1], hu.2⟩
      refine ⟨⟨(θ, u), ⟨hθ, hu'⟩, rfl⟩, ?_⟩
      rintro ⟨θ', _, h⟩
      exact tube_not_circle_pos L hwle (hwpos θ hθ) hu' hu.1.ne' h.symm
    · rintro x ⟨⟨θ, u⟩, ⟨hθ, hu⟩, rfl⟩ hxE
      have hne : u ≠ 0 := by
        rintro rfl
        rw [tube_zero] at hxE
        exact hxE ⟨θ, ⟨hθ.1.le, hθ.2.le⟩, rfl⟩
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl ⟨(θ, u), ⟨hθ, hu.1, h⟩, rfl⟩
      · exact Or.inr ⟨(θ, u), ⟨hθ, h, hu.2⟩, rfl⟩
    · exact ⟨_, ⟨((α + β) / 2, -1 / 2), ⟨hmid, by norm_num, by norm_num⟩, rfl⟩⟩
    · exact ⟨_, ⟨((α + β) / 2, 1 / 2), ⟨hmid, by norm_num, by norm_num⟩, rfl⟩⟩
  · intro θ₀ hθ₀ δ hδ hsub
    have hI : Ioo (θ₀ - δ) (θ₀ + δ) ⊆ Ioo α β := fun x hx => hsub ⟨hx.1.le, hx.2.le⟩
    have hΩ' : IsOpen (Ioo (θ₀ - δ) (θ₀ + δ) ×ˢ Ioo (-1 : ℝ) 1) := isOpen_Ioo.prod isOpen_Ioo
    have hΩsub : Ioo (θ₀ - δ) (θ₀ + δ) ×ˢ Ioo (-1 : ℝ) 1 ⊆ Ioo α β ×ˢ Ioo (-1 : ℝ) 1 :=
      prod_mono hI subset_rfl
    have hθ₀' : θ₀ ∈ Ioo (θ₀ - δ) (θ₀ + δ) := ⟨by linarith, by linarith⟩
    refine ⟨⟨tube L w '' (Ioo (θ₀ - δ) (θ₀ + δ) ×ˢ Ioo (-1 : ℝ) 1),
      tube L w '' (Ioo (θ₀ - δ) (θ₀ + δ) ×ˢ Ioo (-1 : ℝ) 0),
      tube L w '' (Ioo (θ₀ - δ) (θ₀ + δ) ×ˢ Ioo (0 : ℝ) 1), ?_⟩⟩
    refine ⟨isOpen_image_tube L hw hβ hwle hwpos hΩ' hΩsub, image_mono hΩsub, ?_,
      preconnected_tube_image L hw, preconnected_tube_image L hw,
      ⟨_, ⟨(θ₀, -1 / 2), ⟨hθ₀', by norm_num, by norm_num⟩, rfl⟩⟩,
      ⟨_, ⟨(θ₀, 1 / 2), ⟨hθ₀', by norm_num, by norm_num⟩, rfl⟩⟩,
      image_mono (prod_mono hI subset_rfl), image_mono (prod_mono hI subset_rfl), ?_⟩
    · ext x
      constructor
      · rintro ⟨⟨⟨θ, u⟩, ⟨hθ, hu⟩, rfl⟩, ⟨θ', _, h⟩⟩
        have hθ' := hI hθ
        have hu0 := u_eq_zero_of_circle L hwle (hwpos θ hθ') hu h.symm
        subst hu0
        rw [tube_zero]
        exact ⟨θ, hθ, rfl⟩
      · rintro ⟨θ, hθ, rfl⟩
        refine ⟨⟨(θ, 0), ⟨hθ, by norm_num, by norm_num⟩, tube_zero L w θ⟩, ?_⟩
        have := hI hθ
        exact ⟨θ, ⟨this.1.le, this.2.le⟩, rfl⟩
    · rintro x ⟨⟨⟨θ, u⟩, ⟨hθ, hu⟩, rfl⟩, hxE⟩
      have hne : u ≠ 0 := by
        rintro rfl
        rw [tube_zero] at hxE
        have := hI hθ
        exact hxE ⟨θ, ⟨this.1.le, this.2.le⟩, rfl⟩
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl ⟨(θ, u), ⟨hθ, hu.1, h⟩, rfl⟩
      · exact Or.inr ⟨(θ, u), ⟨hθ, h, hu.2⟩, rfl⟩

#print axioms circle_collars


end Pieces
end EndToEnd
end Concrete
end Lollipop
