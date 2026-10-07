import Lollipop.Lemma_8_5.Proof
import Lollipop.Topology.Carrier.SphereArcs

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace Pieces

open Set

/-! ### Lifting planar arcs -/

theorem IsSphereArc.of_planar {A : Set Point} {x y : Point}
    (hA : IsSimpleArcEnd A x y) :
    IsSphereArc (finiteLift A) (finitePoint x) (finitePoint y) := by
  obtain ⟨f, hAf, hc, hinj, h0, h1⟩ := hA
  have hcont : Continuous finitePoint := OnePoint.continuous_coe
  refine ⟨fun t => finitePoint (f t), ?_, hcont.comp hc, ?_, ?_, ?_⟩
  · rw [hAf]; unfold finiteLift; rw [Set.image_image]
  · intro a ha b hb hab
    exact hinj ha hb (finitePoint_injective hab)
  · simp [h0]
  · simp [h1]

namespace HatAux

/-! ### Stem rays -/

theorem stemPt_def (L : Lollipop) (t : ℝ) : stemPt L t = L.center + t • L.radial := rfl

theorem stemPt_injective (L : Lollipop) : Function.Injective (stemPt L) := by
  intro a b h
  rw [stemPt_def, stemPt_def] at h
  have h2 : a • L.radial = b • L.radial := add_left_cancel h
  have h3 : (a - b) • L.radial = 0 := by rw [sub_smul, h2, sub_self]
  rcases smul_eq_zero.1 h3 with h4 | h4
  · linarith
  · exact absurd h4 L.radial_ne_zero

theorem norm_stemPt_sub (L : Lollipop) (t : ℝ) :
    ‖stemPt L t - L.center‖ = |t| * ‖L.radial‖ := by
  rw [stemPt_def, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]

/-- Parametrisation of the ray `[s,∞) ∪ {∞}` by `[0,1]`. -/
def rayF (L : Lollipop) (s t : ℝ) : Sphere2 :=
  if t < 1 then finitePoint (stemPt L (s + max 0 t / (1 - t))) else infinity

theorem rayF_of_lt (L : Lollipop) (s : ℝ) {t : ℝ} (h : t < 1) :
    rayF L s t = finitePoint (stemPt L (s + max 0 t / (1 - t))) := by
  simp [rayF, h]

theorem rayF_of_ge (L : Lollipop) (s : ℝ) {t : ℝ} (h : 1 ≤ t) :
    rayF L s t = infinity := by
  simp [rayF, not_lt.2 h]

theorem continuous_finitePoint : Continuous finitePoint := OnePoint.continuous_coe

theorem rayF_continuous (L : Lollipop) {s : ℝ} (hs : 1 ≤ s) : Continuous (rayF L s) := by
  rw [continuous_iff_continuousAt]
  intro t0
  by_cases h0 : t0 < 1
  · have hne : (1 - t0) ≠ 0 := by linarith
    have hg : ContinuousAt (fun t : ℝ => s + max 0 t / (1 - t)) t0 :=
      continuousAt_const.add (ContinuousAt.div (continuous_const.max continuous_id).continuousAt
        (continuousAt_const.sub continuousAt_id) hne)
    have hk : ContinuousAt
        (fun t : ℝ => finitePoint (stemPt L (s + max 0 t / (1 - t)))) t0 :=
      (continuous_finitePoint.comp L.continuous_stemMap).continuousAt.comp hg
    refine hk.congr ?_
    filter_upwards [Iio_mem_nhds h0] with t ht
    exact (rayF_of_lt L s ht).symm
  · have h1 : 1 ≤ t0 := not_lt.1 h0
    have hρ : 0 < ‖L.radial‖ := norm_pos_iff.2 L.radial_ne_zero
    rw [ContinuousAt, rayF_of_ge L s h1]
    show Filter.Tendsto _ _ (nhds OnePoint.infty)
    refine (OnePoint.hasBasis_nhds_infty.tendsto_right_iff).2 ?_
    rintro K ⟨hKc, hKcomp⟩
    obtain ⟨R, hR⟩ := hKcomp.isBounded.subset_closedBall L.center
    set M : ℝ := max 0 (R / ‖L.radial‖) with hMdef
    have hM0 : 0 ≤ M := le_max_left _ _
    have hMR : R / ‖L.radial‖ ≤ M := le_max_right _ _
    have hMa : M / (1 + M) < 1 := by
      rw [div_lt_one (by linarith)]; linarith
    have hMa0 : 0 ≤ M / (1 + M) := div_nonneg hM0 (by linarith)
    filter_upwards [Ioi_mem_nhds (show M / (1 + M) < t0 by linarith)] with t ht
    by_cases h : t < 1
    · left
      have ht' : M / (1 + M) < t := ht
      have htpos : 0 < t := lt_of_le_of_lt hMa0 ht'
      have h1t : 0 < 1 - t := by linarith
      have hMt : M < t / (1 - t) := by
        rw [lt_div_iff₀ h1t]
        rw [div_lt_iff₀ (by linarith)] at ht'
        nlinarith
      refine ⟨stemPt L (s + max 0 t / (1 - t)), ?_, (rayF_of_lt L s h).symm⟩
      intro hmem
      have hd := hR hmem
      rw [Metric.mem_closedBall, dist_eq_norm, norm_stemPt_sub] at hd
      rw [max_eq_right htpos.le] at hd
      have hpos : 0 < s + t / (1 - t) := by
        have : 0 < t / (1 - t) := div_pos htpos h1t
        linarith
      rw [abs_of_pos hpos] at hd
      have : R / ‖L.radial‖ < s + t / (1 - t) := by linarith
      rw [div_lt_iff₀ hρ] at this
      linarith
    · right
      rw [rayF_of_ge L s (not_lt.1 h)]
      rfl

theorem raySet_isSphereArc (L : Lollipop) {s : ℝ} (hs : 1 ≤ s) :
    IsSphereArc (finiteLift (raySet L s) ∪ {infinity}) (finitePoint (stemPt L s)) infinity := by
  refine ⟨rayF L s, ?_, rayF_continuous L hs, ?_, ?_, ?_⟩
  · ext p
    constructor
    · rintro (⟨x, ⟨τ, hτ, rfl⟩, rfl⟩ | hp)
      · -- point on the ray
        have hτ' : s ≤ τ := hτ
        set d : ℝ := τ - s with hd
        have hd0 : 0 ≤ d := by linarith
        refine ⟨d / (1 + d), ⟨by positivity, ?_⟩, ?_⟩
        · rw [div_le_one (by linarith)]; linarith
        · have hlt : d / (1 + d) < 1 := by rw [div_lt_one (by linarith)]; linarith
          rw [rayF_of_lt L s hlt, max_eq_right (by positivity)]
          have : 1 - d / (1 + d) = 1 / (1 + d) := by field_simp; ring
          rw [this]
          have h2 : d / (1 + d) / (1 / (1 + d)) = d := by field_simp
          rw [h2]
          congr 2
          rw [hd]; ring
      · rw [Set.mem_singleton_iff] at hp
        subst hp
        exact ⟨1, ⟨by norm_num, le_rfl⟩, rayF_of_ge L s le_rfl⟩
    · rintro ⟨t, ht, rfl⟩
      by_cases h : t < 1
      · left
        rw [rayF_of_lt L s h]
        refine ⟨stemPt L (s + max 0 t / (1 - t)), ⟨_, ?_, rfl⟩, rfl⟩
        have : 0 ≤ max 0 t / (1 - t) := div_nonneg (le_max_left _ _) (by linarith)
        show s ≤ s + max 0 t / (1 - t)
        linarith
      · right
        rw [rayF_of_ge L s (not_lt.1 h)]
        rfl
  · intro a ha b hb hab
    by_cases h1 : a < 1 <;> by_cases h2 : b < 1
    · rw [rayF_of_lt L s h1, rayF_of_lt L s h2] at hab
      have h3 := stemPt_injective L (finitePoint_injective hab)
      rw [max_eq_right ha.1, max_eq_right hb.1] at h3
      have h1' : 0 < 1 - a := by linarith
      have h2' : 0 < 1 - b := by linarith
      have h4 : a / (1 - a) = b / (1 - b) := by linarith
      rw [div_eq_div_iff h1'.ne' h2'.ne'] at h4
      nlinarith
    · rw [rayF_of_lt L s h1, rayF_of_ge L s (not_lt.1 h2)] at hab
      exact absurd hab (finitePoint_ne_infinity _)
    · rw [rayF_of_lt L s h2, rayF_of_ge L s (not_lt.1 h1)] at hab
      exact absurd hab.symm (finitePoint_ne_infinity _)
    · linarith [ha.2, hb.2, not_lt.1 h1, not_lt.1 h2]
  · rw [rayF_of_lt L s (by norm_num : (0:ℝ) < 1)]
    simp
  · exact rayF_of_ge L s le_rfl

/-! ### Circle parametrisation -/

theorem point_norm_sq (x : Point) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp [Real.norm_eq_abs, sq_abs]

theorem circlePt_zero_eq_stemPt (L : Lollipop) : circlePt L 0 = stemPt L 1 := by
  simp [circlePt, stemPt_def]

theorem circlePt_comp (L : Lollipop) (θ : ℝ) (i : Fin 2) :
    circlePt L θ i = L.center i + Real.cos θ * L.radial i + Real.sin θ * perp L.radial i := by
  simp [circlePt]

theorem norm_circlePt_sub (L : Lollipop) (θ : ℝ) :
    ‖circlePt L θ - L.center‖ = ‖L.radial‖ := by
  have h : ‖circlePt L θ - L.center‖ ^ 2 = ‖L.radial‖ ^ 2 := by
    rw [point_norm_sq, point_norm_sq]
    have h0 : (circlePt L θ - L.center) 0 =
        Real.cos θ * L.radial 0 + Real.sin θ * perp L.radial 0 := by
      simp [circlePt]
      ring
    have h1 : (circlePt L θ - L.center) 1 =
        Real.cos θ * L.radial 1 + Real.sin θ * perp L.radial 1 := by
      simp [circlePt]
      ring
    rw [h0, h1]
    simp only [perp]
    simp
    nlinarith [Real.sin_sq_add_cos_sq θ]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

theorem circlePt_mem_circle (L : Lollipop) (θ : ℝ) : circlePt L θ ∈ L.circle := by
  show ‖circlePt L θ - L.center‖ = L.radius
  exact norm_circlePt_sub L θ

theorem continuous_circlePt (L : Lollipop) : Continuous (circlePt L) := by
  unfold circlePt
  fun_prop

theorem circlePt_injOn (L : Lollipop) : InjOn (circlePt L) (Ico 0 (2 * Real.pi)) := by
  intro a ha b hb hab
  have hr : L.radial 0 ^ 2 + L.radial 1 ^ 2 ≠ 0 := by
    intro h
    apply L.radial_ne_zero
    have h0 : L.radial 0 = 0 := by nlinarith [sq_nonneg (L.radial 0), sq_nonneg (L.radial 1)]
    have h1 : L.radial 1 = 0 := by nlinarith [sq_nonneg (L.radial 0), sq_nonneg (L.radial 1)]
    refine PiLp.ext (fun i => ?_); fin_cases i <;> simp [h0, h1]
  have e0 := congrArg (fun p : Point => p 0) hab
  have e1 := congrArg (fun p : Point => p 1) hab
  simp only [circlePt_comp, perp] at e0 e1
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
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 hang
  have hpi := Real.pi_pos
  have h1 : (k : ℝ) < 1 := by nlinarith [ha.1, ha.2, hb.1, hb.2]
  have h2 : (-1 : ℝ) < k := by nlinarith [ha.1, ha.2, hb.1, hb.2]
  have h1' : k < 1 := by exact_mod_cast h1
  have h2' : -1 < k := by exact_mod_cast h2
  have hk0 : k = 0 := by omega
  rw [hk0] at hk
  simp at hk
  linarith

theorem circle_exists_angle (L : Lollipop) {x : Point} (hx : x ∈ L.circle) :
    ∃ θ ∈ Ico 0 (2 * Real.pi), x = circlePt L θ := by
  have hρ : 0 < L.radial 0 ^ 2 + L.radial 1 ^ 2 := by
    have : 0 < ‖L.radial‖ := norm_pos_iff.2 L.radial_ne_zero
    have h2 := point_norm_sq L.radial
    nlinarith [sq_nonneg (L.radial 0), sq_nonneg (L.radial 1)]
  have hxn : ‖x - L.center‖ ^ 2 = ‖L.radial‖ ^ 2 := by
    have : ‖x - L.center‖ = ‖L.radial‖ := hx
    rw [this]
  rw [point_norm_sq, point_norm_sq] at hxn
  simp only [PiLp.sub_apply] at hxn
  set u0 := x 0 - L.center 0 with hu0
  set u1 := x 1 - L.center 1 with hu1
  set ρ2 := L.radial 0 ^ 2 + L.radial 1 ^ 2 with hρ2
  set a := (u0 * L.radial 0 + u1 * L.radial 1) / ρ2 with ha
  set b := (u1 * L.radial 0 - u0 * L.radial 1) / ρ2 with hb
  have hab : a ^ 2 + b ^ 2 = 1 := by
    have : a ^ 2 + b ^ 2 = (u0 ^ 2 + u1 ^ 2) * ρ2 / ρ2 ^ 2 := by
      rw [ha, hb]; field_simp; rw [hρ2]; ring
    rw [this]
    have h3 : u0 ^ 2 + u1 ^ 2 = ρ2 := by rw [hρ2]; exact hxn
    rw [h3]; field_simp
  set z : ℂ := ⟨a, b⟩ with hz
  have hznorm : ‖z‖ = 1 := by
    have : ‖z‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [hz]; nlinarith
    nlinarith [norm_nonneg z]
  have hz0 : z ≠ 0 := by
    intro h; rw [h] at hznorm; simp at hznorm
  have hcos : Real.cos (Complex.arg z) = a := by
    rw [Complex.cos_arg hz0, hznorm]; simp [hz]
  have hsin : Real.sin (Complex.arg z) = b := by
    rw [Complex.sin_arg, hznorm]; simp [hz]
  have harg1 := Complex.neg_pi_lt_arg z
  have harg2 := Complex.arg_le_pi z
  have hpi := Real.pi_pos
  have key : ∀ θ : ℝ, Real.cos θ = a → Real.sin θ = b → x = circlePt L θ := by
    intro θ hc hs
    refine PiLp.ext (fun i => ?_)
    rw [circlePt_comp, hc, hs]
    fin_cases i
    · simp [perp, ha, hb, hu0, hu1]
      field_simp
      ring
    · simp [perp, ha, hb, hu0, hu1]
      field_simp
      ring
  by_cases hneg : Complex.arg z < 0
  · refine ⟨Complex.arg z + 2 * Real.pi, ⟨by linarith, by linarith⟩, key _ ?_ ?_⟩
    · rw [Real.cos_add_two_pi, hcos]
    · rw [Real.sin_add_two_pi, hsin]
  · exact ⟨Complex.arg z, ⟨not_lt.1 hneg, by linarith⟩, key _ hcos hsin⟩

theorem isSimpleArcEnd_circlePt (L : Lollipop) {θ : ℝ} (h0 : 0 < θ) (h2 : θ < 2 * Real.pi) :
    IsSimpleArcEnd (circlePt L '' Icc 0 θ) (circlePt L θ) (circlePt L 0) := by
  refine ⟨fun t => circlePt L (θ * (1 - t)), ?_, ?_, ?_, ?_, ?_⟩
  · ext p
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      refine ⟨1 - φ / θ, ⟨?_, ?_⟩, ?_⟩
      · have : φ / θ ≤ 1 := (div_le_one h0).2 hφ.2
        linarith
      · have : 0 ≤ φ / θ := div_nonneg hφ.1 h0.le
        linarith
      · simp only
        congr 1
        field_simp
        ring
    · rintro ⟨t, ht, rfl⟩
      exact ⟨θ * (1 - t), ⟨by nlinarith [ht.1, ht.2], by nlinarith [ht.1, ht.2]⟩, rfl⟩
  · exact (continuous_circlePt L).comp (by fun_prop)
  · intro a ha b hb hab
    have := circlePt_injOn L ⟨by nlinarith [ha.1, ha.2], by nlinarith [ha.1, ha.2]⟩
      ⟨by nlinarith [hb.1, hb.2], by nlinarith [hb.1, hb.2]⟩ hab
    nlinarith
  · simp
  · simp

/-! ### Main theorem -/

theorem raySet_subset_carrier (L : Lollipop) {s : ℝ} (hs : 1 ≤ s) :
    raySet L s ⊆ L.carrier := by
  rintro _ ⟨τ, hτ, rfl⟩
  exact Or.inr ⟨τ, le_trans hs hτ, rfl⟩

theorem hatCarrier_arc_to_infinity (L : Lollipop) :
    ∀ p ∈ hatCarrier L, p = infinity ∨
      ∃ P ⊆ hatCarrier L, IsSphereArc P p infinity := by
  have hray : ∀ s : ℝ, 1 ≤ s → finiteLift (raySet L s) ∪ {infinity} ⊆ hatCarrier L := by
    intro s hs
    rintro q (hq | hq)
    · exact Or.inl (Set.image_mono (raySet_subset_carrier L hs) hq)
    · exact Or.inr hq
  intro p hp
  rcases hp with ⟨x, hx, rfl⟩ | hp
  · right
    rcases hx with hcirc | ⟨τ, hτ, rfl⟩
    · obtain ⟨θ, hθ, rfl⟩ := circle_exists_angle L hcirc
      by_cases hθ0 : θ = 0
      · subst hθ0
        rw [circlePt_zero_eq_stemPt]
        exact ⟨_, hray 1 le_rfl, raySet_isSphereArc L le_rfl⟩
      · have hθpos : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm hθ0)
        have hA := IsSphereArc.of_planar (isSimpleArcEnd_circlePt L hθpos hθ.2)
        have hB := raySet_isSphereArc L (le_refl (1:ℝ))
        rw [← circlePt_zero_eq_stemPt] at hB
        have hAB : finiteLift (circlePt L '' Icc 0 θ) ∩
            (finiteLift (raySet L 1) ∪ {infinity}) = {finitePoint (circlePt L 0)} := by
          ext q
          constructor
          · rintro ⟨⟨y, ⟨φ, hφ, rfl⟩, rfl⟩, hq | hq⟩
            · have hy : circlePt L φ ∈ raySet L 1 := mem_finiteLift_iff.1 hq
              obtain ⟨τ, hτ, hτy⟩ := hy
              have hτ' : (1:ℝ) ≤ τ := hτ
              have h1 : ‖circlePt L φ - L.center‖ = ‖L.radial‖ := norm_circlePt_sub L φ
              rw [← hτy, norm_stemPt_sub, abs_of_nonneg (by linarith)] at h1
              have hρ : 0 < ‖L.radial‖ := norm_pos_iff.2 L.radial_ne_zero
              have hτ1 : τ = 1 := by
                have : (τ - 1) * ‖L.radial‖ = 0 := by linarith
                rcases mul_eq_zero.1 this with h | h
                · linarith
                · exact absurd h hρ.ne'
              rw [hτ1] at hτy
              rw [← circlePt_zero_eq_stemPt] at hτy
              rw [Set.mem_singleton_iff, ← hτy]
            · exact absurd (Set.mem_singleton_iff.1 hq) (finitePoint_ne_infinity _)
          · intro hq
            rw [Set.mem_singleton_iff] at hq
            subst hq
            refine ⟨⟨circlePt L 0, ⟨0, ⟨le_rfl, hθpos.le⟩, rfl⟩, rfl⟩, Or.inl ?_⟩
            refine ⟨stemPt L 1, ⟨1, Set.mem_Ici.2 le_rfl, rfl⟩, ?_⟩
            rw [circlePt_zero_eq_stemPt]
        have hT := IsSphereArc.trans hA hB hAB
        refine ⟨_, ?_, hT⟩
        rintro q (⟨y, ⟨φ, hφ, rfl⟩, rfl⟩ | hq)
        · exact Or.inl ⟨_, Or.inl (circlePt_mem_circle L φ), rfl⟩
        · exact hray 1 le_rfl hq
    · exact ⟨_, hray τ hτ, raySet_isSphereArc L hτ⟩
  · left
    exact hp

#print axioms IsSphereArc.symm
#print axioms IsSphereArc.trans
#print axioms IsSphereArc.of_planar
#print axioms raySet_isSphereArc
#print axioms hatCarrier_arc_to_infinity


end HatAux
export HatAux (raySet_isSphereArc hatCarrier_arc_to_infinity)

end Pieces
end EndToEnd
end Concrete
end Lollipop
