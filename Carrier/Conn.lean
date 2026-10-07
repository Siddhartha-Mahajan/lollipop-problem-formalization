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

namespace ConnAux

theorem hatSet_eq_compl (D : Set Point) : hatSet D = ((↑) '' Dᶜ : Set Sphere2)ᶜ := by
  ext x
  induction x using OnePoint.rec with
  | infty => simp [hatSet, infinity]
  | coe p =>
    simp only [hatSet, mem_union, mem_compl_iff, mem_singleton_iff]
    constructor
    · rintro (h | h)
      · rintro ⟨q, hq, hqp⟩
        have : q = p := OnePoint.coe_injective hqp
        subst this
        exact hq (mem_finiteLift_iff.1 h)
      · exact absurd h (OnePoint.coe_ne_infty p)
    · intro h
      left
      by_contra h'
      exact h ⟨p, fun hp => h' ⟨p, hp, rfl⟩, rfl⟩

theorem norm_stemPt_sub (L : Lollipop) (t : ℝ) :
    ‖stemPt L t - L.center‖ = |t| * ‖L.radial‖ := HatAux.norm_stemPt_sub L t

theorem stem_mem_iff (L : Lollipop) (p : Point) :
    p ∈ L.stem ↔ ∃ t : ℝ, 1 ≤ t ∧ p = stemPt L t := Iff.rfl

/-- Capped radial coordinate; `∞ ↦ M`. -/
def gfun (L : Lollipop) (M : ℝ) : Sphere2 → ℝ :=
  fun x => x.elim M (fun p => min M (‖p - L.center‖ / ‖L.radial‖))

theorem gfun_coe (L : Lollipop) (M : ℝ) (p : Point) :
    gfun L M (finitePoint p) = min M (‖p - L.center‖ / ‖L.radial‖) := rfl

theorem gfun_infty (L : Lollipop) (M : ℝ) : gfun L M infinity = M := rfl

theorem continuous_gfun (L : Lollipop) (M : ℝ) : Continuous (gfun L M) := by
  rw [OnePoint.continuous_iff]
  have hρ : 0 < ‖L.radial‖ := norm_pos_iff.2 L.radial_ne_zero
  constructor
  · rw [Filter.coclosedCompact_eq_cocompact]
    have h1 : Filter.Tendsto (fun p : Point => ‖p - L.center‖) (Filter.cocompact Point)
        Filter.atTop := by
      have := (tendsto_dist_right_cocompact_atTop L.center)
      simpa [dist_eq_norm] using this
    have h2 := h1.atTop_div_const hρ
    have h3 : ∀ᶠ p : Point in Filter.cocompact Point, M ≤ ‖p - L.center‖ / ‖L.radial‖ :=
      h2.eventually_ge_atTop M
    show Filter.Tendsto (fun x : Point => gfun L M (finitePoint x)) _ (nhds M)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [h3] with p hp
    rw [gfun_coe]
    exact (min_eq_left hp).symm
  · show Continuous (fun p : Point => min M (‖p - L.center‖ / ‖L.radial‖))
    fun_prop

theorem gfun_stemPt (L : Lollipop) {M t : ℝ} (ht : 0 ≤ t) (htM : t ≤ M) :
    gfun L M (finitePoint (stemPt L t)) = t := by
  have hρ : 0 < ‖L.radial‖ := norm_pos_iff.2 L.radial_ne_zero
  rw [gfun_coe, norm_stemPt_sub, abs_of_nonneg ht, mul_div_cancel_right₀ _ hρ.ne']
  exact min_eq_right htM

theorem stem_core (L : Lollipop) {Z : Set Sphere2} (hZc : IsPreconnected Z)
    (hZX : Z ⊆ hatCarrier L) {M s τ : ℝ} {b : Sphere2} (hs : 1 ≤ s) (hsτ : s ≤ τ)
    (hτM : τ < M) (hsZ : finitePoint (stemPt L s) ∈ Z) (hbZ : b ∈ Z)
    (hb : τ ≤ gfun L M b) : finitePoint (stemPt L τ) ∈ Z := by
  have hρ : 0 < ‖L.radial‖ := norm_pos_iff.2 L.radial_ne_zero
  have ha : gfun L M (finitePoint (stemPt L s)) = s :=
    gfun_stemPt L (by linarith) (by linarith)
  have hI := (hZc.image _ (continuous_gfun L M).continuousOn).Icc_subset
    (a := gfun L M (finitePoint (stemPt L s))) (b := gfun L M b) ⟨_, hsZ, rfl⟩ ⟨b, hbZ, rfl⟩
  obtain ⟨z, hzZ, hz⟩ := hI ⟨by rw [ha]; exact hsτ, hb⟩
  have hzX := hZX hzZ
  induction z using OnePoint.rec with
  | infty => exact absurd hz (by rw [show OnePoint.infty = infinity from rfl, gfun_infty]; linarith)
  | coe p =>
    change gfun L M (finitePoint p) = τ at hz
    rw [gfun_coe] at hz
    have hn : ‖p - L.center‖ / ‖L.radial‖ = τ := by
      rcases min_choice M (‖p - L.center‖ / ‖L.radial‖) with h | h
      · rw [h] at hz; linarith
      · rw [h] at hz; exact hz
    have hp : p ∈ L.carrier := (finitePoint_mem_hatCarrier_iff L p).1 hzX
    rcases hp with hc | ⟨t, ht, hpt⟩
    · have h1 : ‖p - L.center‖ = ‖L.radial‖ := hc
      rw [h1, div_self hρ.ne'] at hn
      have : s = τ := by linarith
      subst this
      exact hsZ
    · have hpt' : p = stemPt L t := hpt
      subst hpt'
      rw [norm_stemPt_sub, abs_of_nonneg (by linarith), mul_div_cancel_right₀ _ hρ.ne'] at hn
      subst hn
      exact hzZ

theorem hatCarrier_isConnected_aux (L : Lollipop) : IsConnected (hatCarrier L) := by
  have h1 : IsConnected (finiteLift L.carrier) :=
    L.isConnected_carrier.image finitePoint OnePoint.continuous_coe.continuousOn
  have h2 : IsConnected (finiteLift (raySet L 1) ∪ {infinity}) := by
    obtain ⟨f, hP, hc, -, -, -⟩ := HatAux.raySet_isSphereArc L (le_refl (1:ℝ))
    rw [hP]
    exact isConnected_Icc (zero_le_one) |>.image f hc.continuousOn
  have hmem : finitePoint (stemPt L 1) ∈ finiteLift L.carrier :=
    ⟨stemPt L 1, Or.inr ⟨1, le_rfl, rfl⟩, rfl⟩
  have hmem2 : finitePoint (stemPt L 1) ∈ finiteLift (raySet L 1) ∪ {infinity} :=
    Or.inl ⟨stemPt L 1, ⟨1, Set.mem_Ici.2 le_rfl, rfl⟩, rfl⟩
  have h3 := h1.union ⟨_, hmem, hmem2⟩ h2
  have heq : finiteLift L.carrier ∪ (finiteLift (raySet L 1) ∪ {infinity}) = hatCarrier L := by
    apply Subset.antisymm
    · rintro x (hx | hx | hx)
      · exact Or.inl hx
      · exact Or.inl (Set.image_mono (HatAux.raySet_subset_carrier L (le_refl (1:ℝ))) hx)
      · exact Or.inr hx
    · rintro x (hx | hx)
      · exact Or.inl hx
      · exact Or.inr (Or.inr hx)
  rw [heq] at h3
  exact h3


theorem circlePt_add_int_mul_two_pi (L : Lollipop) (θ : ℝ) (k : ℤ) :
    circlePt L (θ + k * (2 * Real.pi)) = circlePt L θ := by
  unfold circlePt
  rw [Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

theorem circle_sep (L : Lollipop) {G : Set Point} (hG : IsPreconnected G)
    (hGc : G ⊆ L.circle) {α β θ1 θ2 : ℝ} (h1 : α < θ1) (h2 : θ1 < β) (h3 : β < θ2)
    (h4 : θ2 < α + 2 * Real.pi) (hP : circlePt L α ∈ G) (hQ : circlePt L β ∈ G)
    (hX : circlePt L θ1 ∉ G) (hY : circlePt L θ2 ∉ G) : False := by
  have hpi := Real.pi_pos
  have hρ2 : 0 < L.radial 0 ^ 2 + L.radial 1 ^ 2 := by
    have : 0 < ‖L.radial‖ := norm_pos_iff.2 L.radial_ne_zero
    have h2 := HatAux.point_norm_sq L.radial
    nlinarith [sq_nonneg (L.radial 0), sq_nonneg (L.radial 1)]
  set ρ2 := L.radial 0 ^ 2 + L.radial 1 ^ 2 with hρ2def
  set m : ℝ := (θ1 + θ2) / 2 with hm
  set δ : ℝ := (θ2 - θ1) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hδπ : δ < Real.pi := by rw [hδ]; linarith
  set w0 : ℝ := Real.cos m * L.radial 0 - Real.sin m * L.radial 1 with hw0
  set w1 : ℝ := Real.cos m * L.radial 1 + Real.sin m * L.radial 0 with hw1
  let ℓ : Point → ℝ := fun p =>
    (p 0 - L.center 0) * w0 + (p 1 - L.center 1) * w1 - ρ2 * Real.cos δ
  have hℓc : Continuous ℓ := by
    have h0 : Continuous (fun p : Point => p 0) := (EuclideanSpace.proj 0).continuous
    have h1 : Continuous (fun p : Point => p 1) := (EuclideanSpace.proj 1).continuous
    simp only [ℓ]
    fun_prop
  have hℓ : ∀ φ, ℓ (circlePt L φ) = ρ2 * (Real.cos (φ - m) - Real.cos δ) := by
    intro φ
    simp only [ℓ, HatAux.circlePt_comp, perp, hw0, hw1, hρ2def]
    simp
    rw [Real.cos_sub]
    ring
  -- values at P and Q
  have hQpos : 0 < ℓ (circlePt L β) := by
    rw [hℓ]
    apply mul_pos hρ2
    have habs : |β - m| < δ := by
      rw [abs_lt]; constructor <;> (rw [hm, hδ]; linarith)
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg (β - m)) hδπ.le habs
    rw [Real.cos_abs] at this
    linarith
  have hPneg : ℓ (circlePt L α) < 0 := by
    rw [← circlePt_add_int_mul_two_pi L α 1, hℓ]
    have : ((1 : ℤ) : ℝ) = 1 := by norm_num
    rw [this, one_mul]
    have hu1 : δ < α + 2 * Real.pi - m := by rw [hm, hδ]; linarith
    have hu2 : α + 2 * Real.pi - m < 2 * Real.pi - δ := by rw [hm, hδ]; linarith
    have : Real.cos (α + 2 * Real.pi - m) < Real.cos δ := by
      by_cases hle : α + 2 * Real.pi - m ≤ Real.pi
      · exact Real.cos_lt_cos_of_nonneg_of_le_pi hδ0.le hle hu1
      · push Not at hle
        have := Real.cos_lt_cos_of_nonneg_of_le_pi hδ0.le (show 2 * Real.pi - (α + 2 * Real.pi - m) ≤ Real.pi by linarith)
          (show δ < 2 * Real.pi - (α + 2 * Real.pi - m) by linarith)
        rwa [Real.cos_two_pi_sub] at this
    nlinarith
  -- IVT
  have hIm : IsPreconnected (ℓ '' G) := hG.image ℓ hℓc.continuousOn
  have h0mem : (0:ℝ) ∈ ℓ '' G :=
    hIm.Icc_subset ⟨_, hP, rfl⟩ ⟨_, hQ, rfl⟩ ⟨hPneg.le, hQpos.le⟩
  obtain ⟨p, hpG, hp0⟩ := h0mem
  obtain ⟨φ, -, rfl⟩ := HatAux.circle_exists_angle L (hGc hpG)
  rw [hℓ] at hp0
  have hc : Real.cos (φ - m) = Real.cos δ := by
    rcases mul_eq_zero.1 hp0 with h | h
    · exact absurd h hρ2.ne'
    · linarith
  obtain ⟨k, hk | hk⟩ := Real.cos_eq_cos_iff.1 hc.symm
  · -- δ = 2kπ + (φ - m)
    apply hY
    have : φ = θ2 + (k : ℤ) * (2 * Real.pi) := by
      rw [hδ, hm] at hk; nlinarith
    rw [← circlePt_add_int_mul_two_pi L θ2 k, ← this]
    exact hpG
  · apply hX
    have : φ = θ1 + (k : ℤ) * (2 * Real.pi) := by
      rw [hδ, hm] at hk; nlinarith
    rw [← circlePt_add_int_mul_two_pi L θ1 k, ← this]
    exact hpG

/-! ### Retraction onto the circle -/

def CC (L : Lollipop) : Set Sphere2 := finiteLift L.circle
def RR (L : Lollipop) : Set Sphere2 := finiteLift (raySet L 1) ∪ {infinity}

open Classical in
def rho (L : Lollipop) : Sphere2 → Point :=
  fun x => if x ∈ RR L then L.anchor else x.elim L.anchor id

theorem anchor_eq (L : Lollipop) : L.anchor = stemPt L 1 := by
  show L.center + L.radial = L.center + (1:ℝ) • L.radial
  rw [one_smul]

theorem circle_inter_ray (L : Lollipop) {p : Point} (hc : p ∈ L.circle)
    (hr : p ∈ raySet L 1) : p = L.anchor := by
  obtain ⟨τ, hτ, rfl⟩ := hr
  have hτ' : (1:ℝ) ≤ τ := hτ
  have h1 : ‖stemPt L τ - L.center‖ = ‖L.radial‖ := hc
  rw [HatAux.norm_stemPt_sub, abs_of_nonneg (by linarith)] at h1
  have hρ : 0 < ‖L.radial‖ := norm_pos_iff.2 L.radial_ne_zero
  have : τ = 1 := by
    have : (τ - 1) * ‖L.radial‖ = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h hρ.ne'
  rw [this, anchor_eq]

theorem mem_RR_coe (L : Lollipop) (p : Point) : finitePoint p ∈ RR L ↔ p ∈ raySet L 1 := by
  constructor
  · rintro (h | h)
    · exact mem_finiteLift_iff.1 h
    · exact absurd (Set.mem_singleton_iff.1 h) (finitePoint_ne_infinity _)
  · intro h; exact Or.inl (mem_finiteLift_iff.2 h)

theorem hat_eq (L : Lollipop) : hatCarrier L = CC L ∪ RR L := by
  ext x
  induction x using OnePoint.rec with
  | infty =>
    change infinity ∈ hatCarrier L ↔ infinity ∈ CC L ∪ RR L
    exact ⟨fun _ => Or.inr (Or.inr rfl), fun _ => infinity_mem_hatCarrier L⟩
  | coe p =>
    change finitePoint p ∈ hatCarrier L ↔ _
    rw [finitePoint_mem_hatCarrier_iff]
    constructor
    · rintro (h | ⟨t, ht, hpt⟩)
      · exact Or.inl (mem_finiteLift_iff.2 h)
      · exact Or.inr ((mem_RR_coe L p).2 ⟨t, ht, hpt.symm⟩)
    · rintro (h | h)
      · exact Or.inl (mem_finiteLift_iff.1 h)
      · obtain ⟨t, ht, rfl⟩ := (mem_RR_coe L p).1 h
        exact Or.inr ⟨t, ht, rfl⟩

theorem isClosed_CC (L : Lollipop) : IsClosed (CC L) := by
  unfold CC finiteLift
  refine OnePoint.isClosed_image_coe.2 ⟨L.isClosed_circle, ?_⟩
  rw [Lollipop.circle_eq_sphere]
  exact isCompact_sphere _ _

theorem isClosed_RR (L : Lollipop) : IsClosed (RR L) := by
  obtain ⟨f, hP, hc, -, -, -⟩ := HatAux.raySet_isSphereArc L (le_refl (1:ℝ))
  have : RR L = f '' Icc 0 1 := hP
  rw [this]
  exact (isCompact_Icc.image hc).isClosed

theorem rho_of_circle (L : Lollipop) {p : Point} (hp : p ∈ L.circle) :
    rho L (finitePoint p) = p := by
  unfold rho
  split_ifs with h
  · exact (circle_inter_ray L hp ((mem_RR_coe L p).1 h)).symm
  · rfl

theorem rho_of_RR (L : Lollipop) {x : Sphere2} (hx : x ∈ RR L) : rho L x = L.anchor := by
  unfold rho
  rw [if_pos hx]

theorem rho_mem_circle (L : Lollipop) {x : Sphere2} (hx : x ∈ hatCarrier L) :
    rho L x ∈ L.circle := by
  rw [hat_eq] at hx
  by_cases h : x ∈ RR L
  · rw [rho_of_RR L h]; exact L.anchor_mem_circle
  · obtain h' | h' := hx
    · obtain ⟨p, hp, rfl⟩ := h'
      rw [rho_of_circle L hp]; exact hp
    · exact absurd h' h

theorem continuousOn_rho (L : Lollipop) : ContinuousOn (rho L) (hatCarrier L) := by
  rw [hat_eq]
  refine ContinuousOn.union_of_isClosed ?_ ?_ (isClosed_CC L) (isClosed_RR L)
  · have hc : ContinuousOn (fun x : Sphere2 => x.elim L.anchor id) (CC L) := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := hx
      refine ContinuousAt.continuousWithinAt ?_
      rw [show ((finitePoint p : Sphere2)) = ((p : Point) : Sphere2) from rfl,
        OnePoint.continuousAt_coe]
      exact continuousAt_id
    refine hc.congr ?_
    intro x hx
    obtain ⟨p, hp, rfl⟩ := hx
    rw [rho_of_circle L hp]
    rfl
  · exact continuousOn_const.congr (fun x hx => rho_of_RR L hx)

theorem anchor_or_subset (L : Lollipop) {Z : Set Sphere2} (hZc : IsPreconnected Z)
    (hZX : Z ⊆ hatCarrier L) {z0 : Sphere2} (hz0Z : z0 ∈ Z) (hz0 : z0 ∈ CC L) :
    finitePoint L.anchor ∈ Z ∨ Z ⊆ CC L := by
  by_cases hZC : Z ⊆ CC L
  · exact Or.inr hZC
  · left
    obtain ⟨z, hzZ, hzC⟩ := Set.not_subset.1 hZC
    have hzR : z ∈ RR L := by
      have := hZX hzZ
      rw [hat_eq] at this
      exact this.resolve_left hzC
    have := (isPreconnected_closed_iff.1 hZc) (CC L) (RR L) (isClosed_CC L) (isClosed_RR L)
      (by rw [← hat_eq]; exact hZX) ⟨z0, hz0Z, hz0⟩ ⟨z, hzZ, hzR⟩
    obtain ⟨w, hwZ, hwC, hwR⟩ := this
    obtain ⟨p, hp, rfl⟩ := hwC
    have := circle_inter_ray L hp ((mem_RR_coe L p).1 hwR)
    rw [this] at hwZ
    exact hwZ

theorem transfer (L : Lollipop) {Z : Set Sphere2} (hZc : IsPreconnected Z)
    (hZX : Z ⊆ hatCarrier L) {θ0 : ℝ} (h0 : finitePoint (circlePt L θ0) ∈ Z) {θ : ℝ}
    (h : circlePt L θ ∈ rho L '' Z) : finitePoint (circlePt L θ) ∈ Z := by
  obtain ⟨z, hzZ, hz⟩ := h
  have hA := anchor_or_subset L hZc hZX h0 ⟨_, HatAux.circlePt_mem_circle L θ0, rfl⟩
  by_cases hzC : z ∈ CC L
  · obtain ⟨p, hp, rfl⟩ := hzC
    rw [rho_of_circle L hp] at hz
    rw [← hz]; exact hzZ
  · have hzR : z ∈ RR L := by
      have := hZX hzZ
      rw [hat_eq] at this
      exact this.resolve_left hzC
    rw [rho_of_RR L hzR] at hz
    rcases hA with hA | hA
    · rw [← hz]; exact hA
    · exact absurd (hA hzZ) hzC


end ConnAux

/-- Closed connected subsets of the compactified lollipop containing two stem
points contain the stem segment between them. -/
theorem conn_stem (L : Lollipop) {Z : Set Sphere2} (hZ : IsClosed Z)
    (hZc : IsPreconnected Z) (hZX : Z ⊆ hatCarrier L) {s t : ℝ} (hs : 1 ≤ s)
    (hst : s ≤ t) (hsZ : finitePoint (stemPt L s) ∈ Z)
    (htZ : finitePoint (stemPt L t) ∈ Z) :
    ∀ τ ∈ Icc s t, finitePoint (stemPt L τ) ∈ Z := by
  intro τ hτ
  refine ConnAux.stem_core L hZc hZX (M := t + 1) hs hτ.1 (by linarith [hτ.2]) hsZ htZ ?_
  rw [ConnAux.gfun_stemPt L (by linarith) (by linarith)]
  exact hτ.2

/-- ... and a stem point together with `∞` gives the whole ray. -/
theorem conn_ray (L : Lollipop) {Z : Set Sphere2} (hZ : IsClosed Z)
    (hZc : IsPreconnected Z) (hZX : Z ⊆ hatCarrier L) {s : ℝ} (hs : 1 ≤ s)
    (hsZ : finitePoint (stemPt L s) ∈ Z) (hinf : infinity ∈ Z) :
    ∀ τ, s ≤ τ → finitePoint (stemPt L τ) ∈ Z := by
  intro τ hτ
  refine ConnAux.stem_core L hZc hZX (M := τ + 1) hs hτ (by linarith) hsZ hinf ?_
  rw [ConnAux.gfun_infty]
  linarith

/-- Closed connected subsets containing two circle points contain one of the two
circle arcs between them. -/
theorem conn_circle (L : Lollipop) {Z : Set Sphere2} (hZ : IsClosed Z)
    (hZc : IsPreconnected Z) (hZX : Z ⊆ hatCarrier L) {α β : ℝ} (hαβ : α < β)
    (hβ : β ≤ α + 2 * Real.pi)
    (hαZ : finitePoint (circlePt L α) ∈ Z) (hβZ : finitePoint (circlePt L β) ∈ Z) :
    (∀ θ ∈ Icc α β, finitePoint (circlePt L θ) ∈ Z) ∨
      (∀ θ ∈ Icc β (α + 2 * Real.pi), finitePoint (circlePt L θ) ∈ Z) := by
  by_contra hcon
  obtain ⟨hA, hB⟩ := not_or.1 hcon
  simp only [not_forall] at hA hB
  obtain ⟨θ1, hθ1, hX⟩ := hA
  obtain ⟨θ2, hθ2, hY⟩ := hB
  have h1 : α < θ1 := lt_of_le_of_ne hθ1.1 (fun h => hX (h ▸ hαZ))
  have h2 : θ1 < β := lt_of_le_of_ne hθ1.2 (fun h => hX (h ▸ hβZ))
  have h3 : β < θ2 := lt_of_le_of_ne hθ2.1 (fun h => hY (h ▸ hβZ))
  have h4 : θ2 < α + 2 * Real.pi := by
    refine lt_of_le_of_ne hθ2.2 (fun h => hY ?_)
    have := ConnAux.circlePt_add_int_mul_two_pi L α 1
    simp only [Int.cast_one, one_mul] at this
    rw [h, this]
    exact hαZ
  have hGc : ConnAux.rho L '' Z ⊆ L.circle := by
    rintro _ ⟨z, hz, rfl⟩
    exact ConnAux.rho_mem_circle L (hZX hz)
  have hG : IsPreconnected (ConnAux.rho L '' Z) :=
    hZc.image _ ((ConnAux.continuousOn_rho L).mono hZX)
  refine ConnAux.circle_sep L hG hGc h1 h2 h3 h4 ?_ ?_ ?_ ?_
  · exact ⟨_, hαZ, ConnAux.rho_of_circle L (HatAux.circlePt_mem_circle L α)⟩
  · exact ⟨_, hβZ, ConnAux.rho_of_circle L (HatAux.circlePt_mem_circle L β)⟩
  · exact fun h => hX (ConnAux.transfer L hZc hZX hαZ h)
  · exact fun h => hY (ConnAux.transfer L hZc hZX hαZ h)

/-- The compactified lollipop is connected. -/
theorem hatCarrier_isConnected (L : Lollipop) : IsConnected (hatCarrier L) :=
  ConnAux.hatCarrier_isConnected_aux L

theorem componentCount_hatCarrier (L : Lollipop) : componentCount (hatCarrier L) = 1 := by
  haveI : ConnectedSpace (hatCarrier L) := isConnected_iff_connectedSpace.1 (hatCarrier_isConnected L)
  unfold componentCount
  exact Nat.card_eq_one_iff_unique.2 ⟨inferInstance, inferInstance⟩

/-- The compactified closed set is closed in the sphere. -/
theorem isClosed_hatSet {D : Set Point} (hD : IsClosed D) : IsClosed (hatSet D) := by
  rw [ConnAux.hatSet_eq_compl, isClosed_compl_iff]
  exact OnePoint.isOpen_image_coe.2 hD.isOpen_compl

theorem isClosed_hatCarrier (L : Lollipop) : IsClosed (hatCarrier L) := by
  have h := isClosed_hatSet L.isClosed_carrier
  exact h


end Pieces
end EndToEnd
end Concrete
end Lollipop
