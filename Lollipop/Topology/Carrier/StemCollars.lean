import Lollipop.Lemma_8_5.Proof
import Lollipop.Topology.Carrier.Defs

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace Pieces

open Set

namespace StemAux

/-- The strip map `(τ, u) ↦ c + τ v + (u * w τ) n`. -/
def tubeMap (L : Lollipop) (w : ℝ → ℝ) (p : ℝ × ℝ) : Point :=
  L.center + p.1 • L.radial + (p.2 * w p.1) • perp L.radial

theorem continuous_stemPt (L : Lollipop) : Continuous (stemPt L) :=
  L.continuous_stemMap

theorem tubeMap_continuous (L : Lollipop) {w : ℝ → ℝ} (hw : Continuous w) :
    Continuous (tubeMap L w) := by
  unfold tubeMap
  fun_prop

theorem stemPt_eq_tubeMap (L : Lollipop) (w : ℝ → ℝ) (τ : ℝ) :
    stemPt L τ = tubeMap L w (τ, 0) := by
  simp [stemPt, Lollipop.stemMap, tubeMap]

theorem radial_sq_pos (L : Lollipop) : 0 < L.radial 0 ^ 2 + L.radial 1 ^ 2 := by
  by_contra h
  have h0 : L.radial 0 = 0 := by nlinarith [sq_nonneg (L.radial 0), sq_nonneg (L.radial 1)]
  have h1 : L.radial 1 = 0 := by nlinarith [sq_nonneg (L.radial 0), sq_nonneg (L.radial 1)]
  apply L.radial_ne_zero
  refine PiLp.ext (fun i => ?_)
  fin_cases i <;> simp [h0, h1]

theorem perp_ne_zero (L : Lollipop) : perp L.radial ≠ 0 := by
  intro h
  have h0 := congrArg (fun x : Point => x 0) h
  have h1 := congrArg (fun x : Point => x 1) h
  simp [perp] at h0 h1
  have := radial_sq_pos L
  rw [h0, h1] at this
  simp at this

theorem tubeMap_eq_tubeMap (L : Lollipop) (w : ℝ → ℝ) {p q : ℝ × ℝ}
    (h : tubeMap L w p = tubeMap L w q) : p.1 = q.1 ∧ p.2 * w p.1 = q.2 * w q.1 := by
  have h0 := congrArg (fun x : Point => x 0) h
  have h1 := congrArg (fun x : Point => x 1) h
  simp [tubeMap, perp] at h0 h1
  have hpos := radial_sq_pos L
  set a := L.radial 0
  set b := L.radial 1
  have e1 : (p.1 - q.1) * a - (p.2 * w p.1 - q.2 * w q.1) * b = 0 := by linarith
  have e2 : (p.1 - q.1) * b + (p.2 * w p.1 - q.2 * w q.1) * a = 0 := by linarith
  have k1 : (p.1 - q.1) * (a ^ 2 + b ^ 2) = 0 := by linear_combination a * e1 + b * e2
  have k2 : (p.2 * w p.1 - q.2 * w q.1) * (a ^ 2 + b ^ 2) = 0 := by
    linear_combination (-b) * e1 + a * e2
  have k1' := (mul_eq_zero.mp k1).resolve_right hpos.ne'
  have k2' := (mul_eq_zero.mp k2).resolve_right hpos.ne'
  constructor <;> linarith

theorem stemPt_injective (L : Lollipop) : Function.Injective (stemPt L) := by
  intro a b h
  have := tubeMap_eq_tubeMap L (fun _ => 1)
    (p := (a, 0)) (q := (b, 0)) (by rw [← stemPt_eq_tubeMap, ← stemPt_eq_tubeMap]; exact h)
  exact this.1

theorem tubeMap_mem_E_iff (L : Lollipop) {w : ℝ → ℝ} {E : Set Point}
    (hline : ∀ z ∈ E, ∃ τ, z = stemPt L τ) {τ u : ℝ} (hw : w τ ≠ 0) :
    tubeMap L w (τ, u) ∈ E ↔ u = 0 ∧ stemPt L τ ∈ E := by
  constructor
  · intro hz
    obtain ⟨τ', hτ'⟩ := hline _ hz
    rw [stemPt_eq_tubeMap L w τ'] at hτ'
    have := tubeMap_eq_tubeMap L w hτ'
    simp only at this
    obtain ⟨h1, h2⟩ := this
    have hu : u = 0 := by
      have : u * w τ = 0 := by simpa using h2
      exact (mul_eq_zero.mp this).resolve_right hw
    refine ⟨hu, ?_⟩
    rw [stemPt_eq_tubeMap L w τ, ← hu]
    exact hz
  · rintro ⟨rfl, hz⟩
    rw [stemPt_eq_tubeMap L w τ] at hz
    exact hz

theorem exists_width (L : Lollipop) {D : Set Point} (hD : IsClosed D) (I : Set ℝ)
    (hI : ∀ τ ∈ I, stemPt L τ ∉ D) :
    ∃ w : ℝ → ℝ, Continuous w ∧ (∀ τ ∈ I, 0 < w τ) ∧
      ∀ τ ∈ I, ∀ u : ℝ, |u| < 1 → tubeMap L w (τ, u) ∉ D := by
  by_cases hDe : D = ∅
  · refine ⟨fun _ => 1, continuous_const, fun _ _ => one_pos, ?_⟩
    intro τ _ u _
    rw [hDe]; simp
  · have hne : D.Nonempty := Set.nonempty_iff_ne_empty.mpr hDe
    have hn : 0 < ‖perp L.radial‖ := norm_pos_iff.mpr (perp_ne_zero L)
    refine ⟨fun τ => Metric.infDist (stemPt L τ) D / (2 * ‖perp L.radial‖), ?_, ?_, ?_⟩
    · exact ((Metric.continuous_infDist_pt D).comp (continuous_stemPt L)).div_const _
    · intro τ hτ
      have := (hD.notMem_iff_infDist_pos hne).mp (hI τ hτ)
      positivity
    · intro τ hτ u hu hmem
      have hd := (hD.notMem_iff_infDist_pos hne).mp (hI τ hτ)
      set d := Metric.infDist (stemPt L τ) D with hd_def
      have hle : d ≤ dist (stemPt L τ) (tubeMap L (fun τ => Metric.infDist (stemPt L τ) D / (2 * ‖perp L.radial‖)) (τ, u)) :=
        Metric.infDist_le_dist_of_mem hmem
      have hdist : dist (stemPt L τ) (tubeMap L (fun τ => Metric.infDist (stemPt L τ) D / (2 * ‖perp L.radial‖)) (τ, u))
          = |u| * (d / 2) := by
        rw [dist_eq_norm]
        have : stemPt L τ - tubeMap L (fun τ => Metric.infDist (stemPt L τ) D / (2 * ‖perp L.radial‖)) (τ, u)
            = (-(u * (d / (2 * ‖perp L.radial‖)))) • perp L.radial := by
          show L.center + τ • L.radial - (L.center + τ • L.radial +
            (u * (d / (2 * ‖perp L.radial‖))) • perp L.radial) = _
          module
        rw [this, norm_smul, Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos (by positivity : 0 < d / (2 * ‖perp L.radial‖))]
        field_simp
      rw [hdist] at hle
      have : |u| * (d / 2) < d := by nlinarith [abs_nonneg u]
      linarith

/-- Coordinates of a plane point with respect to the frame `(v, n)`. -/
def tubePsi (L : Lollipop) (x : Point) : ℝ × ℝ :=
  (((x 0 - L.center 0) * L.radial 0 + (x 1 - L.center 1) * L.radial 1) /
      (L.radial 0 ^ 2 + L.radial 1 ^ 2),
   ((x 1 - L.center 1) * L.radial 0 - (x 0 - L.center 0) * L.radial 1) /
      (L.radial 0 ^ 2 + L.radial 1 ^ 2))

def tubePhi (L : Lollipop) (q : ℝ × ℝ) : Point :=
  L.center + q.1 • L.radial + q.2 • perp L.radial

theorem tubePsi_continuous (L : Lollipop) : Continuous (tubePsi L) := by
  unfold tubePsi
  have h0 : Continuous fun x : Point => x 0 := by fun_prop
  have h1 : Continuous fun x : Point => x 1 := by fun_prop
  refine Continuous.prodMk ?_ ?_
  · exact (((h0.sub continuous_const).mul continuous_const).add
      ((h1.sub continuous_const).mul continuous_const)).div_const _
  · exact (((h1.sub continuous_const).mul continuous_const).sub
      ((h0.sub continuous_const).mul continuous_const)).div_const _

theorem tubePsi_phi (L : Lollipop) (q : ℝ × ℝ) : tubePsi L (tubePhi L q) = q := by
  have hpos := radial_sq_pos L
  ext
  · simp [tubePsi, tubePhi, perp]
    field_simp
    ring
  · simp [tubePsi, tubePhi, perp]
    field_simp
    ring

theorem tubePhi_psi (L : Lollipop) (x : Point) : tubePhi L (tubePsi L x) = x := by
  have hpos := radial_sq_pos L
  refine PiLp.ext (fun i => ?_)
  fin_cases i
  · simp [tubePsi, tubePhi, perp]
    field_simp
    ring
  · simp [tubePsi, tubePhi, perp]
    field_simp
    ring

theorem tubeMap_eq_phi (L : Lollipop) (w : ℝ → ℝ) (p : ℝ × ℝ) :
    tubeMap L w p = tubePhi L (p.1, p.2 * w p.1) := rfl

theorem tubeMap_image_isOpen (L : Lollipop) {w : ℝ → ℝ} (hw : Continuous w) {I : Set ℝ}
    (hI : IsOpen I) (hwpos : ∀ τ ∈ I, 0 < w τ) {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hVI : ∀ p ∈ V, p.1 ∈ I) : IsOpen (tubeMap L w '' V) := by
  let sh : ℝ × ℝ → ℝ × ℝ := fun p => (p.1, p.2 * w p.1)
  let g : ℝ × ℝ → ℝ × ℝ := fun q => (q.1, q.2 / w q.1)
  have hsh : sh '' V = {q : ℝ × ℝ | q.1 ∈ I} ∩ g ⁻¹' V := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      have h1 := hVI p hp
      have h2 := (hwpos _ h1).ne'
      refine ⟨h1, ?_⟩
      show (p.1, p.2 * w p.1 / w p.1) ∈ V
      rw [mul_div_assoc, div_self h2, mul_one]
      exact hp
    · rintro ⟨h1, h2⟩
      have hq := (hwpos _ h1).ne'
      refine ⟨g q, h2, ?_⟩
      show (q.1, q.2 / w q.1 * w q.1) = q
      rw [div_mul_cancel₀ _ hq]
  have hopen : IsOpen (sh '' V) := by
    rw [hsh]
    have hg : ContinuousOn g {q : ℝ × ℝ | q.1 ∈ I} := by
      refine ContinuousOn.prodMk continuous_fst.continuousOn ?_
      exact continuous_snd.continuousOn.div (hw.comp continuous_fst).continuousOn
        (fun q hq => (hwpos q.1 hq).ne')
    exact hg.isOpen_inter_preimage (hI.preimage continuous_fst) hV
  have key : tubeMap L w '' V = tubePsi L ⁻¹' (sh '' V) := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p, hp, ?_⟩
      rw [tubeMap_eq_phi, tubePsi_phi]
    · rintro ⟨p, hp, hpx⟩
      refine ⟨p, hp, ?_⟩
      rw [tubeMap_eq_phi, ← tubePhi_psi L x]
      congr 1
  rw [key]
  exact hopen.preimage (tubePsi_continuous L)

theorem stemTube_collars (L : Lollipop) {D : Set Point} (hD : IsClosed D) (E : Set Point)
    (I : Set ℝ) (hIo : IsOpen I) (hIc : I.OrdConnected) (hIne : I.Nonempty)
    (hIE : ∀ τ ∈ I, stemPt L τ ∈ E) (hline : ∀ z ∈ E, ∃ τ, z = stemPt L τ)
    (hnew : ∀ z ∈ E, z ∉ D → ∃ τ ∈ I, z = stemPt L τ)
    (hID : ∀ τ ∈ I, stemPt L τ ∉ D) :
    ∃ U S₁ S₂ : Set Point, Collars D E S₁ S₂ U ∧
      ∀ J : Set ℝ, IsOpen J → J.OrdConnected → J.Nonempty → J ⊆ I →
        Germ E S₁ S₂ U (stemPt L '' J) := by
  obtain ⟨w, hwc, hwpos, hwD⟩ := exists_width L hD I hID
  have hTc : Continuous (tubeMap L w) := tubeMap_continuous L hwc
  have hopenI : ∀ A B : Set ℝ, IsOpen A → IsOpen B → A ⊆ I → IsOpen (tubeMap L w '' (A ×ˢ B)) := by
    intro A B hA hB hAI
    refine tubeMap_image_isOpen L hwc hIo hwpos (hA.prod hB) ?_
    intro p hp
    exact hAI hp.1
  have hpre : ∀ A B : Set ℝ, A.OrdConnected → B.OrdConnected →
      IsPreconnected (tubeMap L w '' (A ×ˢ B)) := by
    intro A B hA hB
    exact (hA.isPreconnected.prod hB.isPreconnected).image _ hTc.continuousOn
  -- membership in E
  have hmemE : ∀ τ ∈ I, ∀ u : ℝ, tubeMap L w (τ, u) ∈ E ↔ u = 0 := by
    intro τ hτ u
    rw [tubeMap_mem_E_iff L hline (hwpos τ hτ).ne']
    exact ⟨fun h => h.1, fun h => ⟨h, hIE τ hτ⟩⟩
  have hsub : ∀ A : Set ℝ, A ⊆ I → ∀ B : Set ℝ, B ⊆ Ioo (-1 : ℝ) 1 →
      tubeMap L w '' (A ×ˢ B) ⊆ Dᶜ := by
    rintro A hA B hB _ ⟨⟨τ, u⟩, hp, rfl⟩
    exact hwD τ (hA hp.1) u (abs_lt.mpr ⟨(hB hp.2).1, (hB hp.2).2⟩)
  have hncov : ∀ A : Set ℝ, A ⊆ I → ∀ x ∈ tubeMap L w '' (A ×ˢ Ioo (-1 : ℝ) 1), x ∉ E →
      x ∈ tubeMap L w '' (A ×ˢ Ioo (-1 : ℝ) 0) ∨ x ∈ tubeMap L w '' (A ×ˢ Ioo (0 : ℝ) 1) := by
    rintro A hA _ ⟨⟨τ, u⟩, hp, rfl⟩ hx
    rcases lt_trichotomy u 0 with h | h | h
    · exact Or.inl ⟨(τ, u), ⟨hp.1, hp.2.1, h⟩, rfl⟩
    · exact absurd ((hmemE τ (hA hp.1) u).mpr h) hx
    · exact Or.inr ⟨(τ, u), ⟨hp.1, h, hp.2.2⟩, rfl⟩
  have hnotE : ∀ A : Set ℝ, A ⊆ I → ∀ B : Set ℝ, (∀ u ∈ B, u ≠ 0) →
      ∀ x ∈ tubeMap L w '' (A ×ˢ B), x ∉ E := by
    rintro A hA B hB _ ⟨⟨τ, u⟩, hp, rfl⟩ hx
    exact hB u hp.2 ((hmemE τ (hA hp.1) u).mp hx)
  have hmono : ∀ A A' B B' : Set ℝ, A ⊆ A' → B ⊆ B' →
      tubeMap L w '' (A ×ˢ B) ⊆ tubeMap L w '' (A' ×ˢ B') := by
    intro A A' B B' hA hB
    exact image_mono (prod_mono hA hB)
  have hIo' : (Ioo (-1 : ℝ) 1).OrdConnected := ordConnected_Ioo
  have hn1 : ∀ u ∈ Ioo (-1 : ℝ) 0, u ≠ 0 := fun u hu => hu.2.ne
  have hn2 : ∀ u ∈ Ioo (0 : ℝ) 1, u ≠ 0 := fun u hu => hu.1.ne'
  have h01 : Ioo (-1 : ℝ) 0 ⊆ Ioo (-1 : ℝ) 1 := Ioo_subset_Ioo_right (by norm_num)
  have h02 : Ioo (0 : ℝ) 1 ⊆ Ioo (-1 : ℝ) 1 := Ioo_subset_Ioo_left (by norm_num)
  obtain ⟨τ₁, hτ₁⟩ := hIne
  refine ⟨tubeMap L w '' (I ×ˢ Ioo (-1 : ℝ) 1), tubeMap L w '' (I ×ˢ Ioo (-1 : ℝ) 0),
    tubeMap L w '' (I ×ˢ Ioo (0 : ℝ) 1), ?_, ?_⟩
  · refine ⟨hopenI _ _ hIo isOpen_Ioo subset_rfl, ?_, hsub I subset_rfl _ subset_rfl,
      hpre _ _ hIc ordConnected_Ioo, hpre _ _ hIc ordConnected_Ioo, ?_, ?_, ?_,
      ⟨tubeMap L w (τ₁, -(1/2)), (τ₁, -(1/2)), ⟨hτ₁, by norm_num, by norm_num⟩, rfl⟩,
      ⟨tubeMap L w (τ₁, 1/2), (τ₁, 1/2), ⟨hτ₁, by norm_num, by norm_num⟩, rfl⟩⟩
    · intro z hz hzD
      obtain ⟨τ, hτ, rfl⟩ := hnew z hz hzD
      exact ⟨(τ, 0), ⟨hτ, by norm_num, by norm_num⟩, (stemPt_eq_tubeMap L w τ).symm⟩
    · exact fun x hx => ⟨hmono _ _ _ _ subset_rfl h01 hx,
        hnotE I subset_rfl _ hn1 x hx⟩
    · exact fun x hx => ⟨hmono _ _ _ _ subset_rfl h02 hx,
        hnotE I subset_rfl _ hn2 x hx⟩
    · exact fun x hx hxE => hncov I subset_rfl x hx hxE
  · intro J hJo hJc hJne hJI
    refine ⟨?_⟩
    refine ⟨tubeMap L w '' (J ×ˢ Ioo (-1 : ℝ) 1), tubeMap L w '' (J ×ˢ Ioo (-1 : ℝ) 0),
      tubeMap L w '' (J ×ˢ Ioo (0 : ℝ) 1), hopenI _ _ hJo isOpen_Ioo hJI,
      hmono _ _ _ _ hJI subset_rfl, ?_, hpre _ _ hJc ordConnected_Ioo,
      hpre _ _ hJc ordConnected_Ioo, ?_, ?_, hmono _ _ _ _ hJI subset_rfl,
      hmono _ _ _ _ hJI subset_rfl, ?_⟩
    · ext x
      constructor
      · rintro ⟨⟨⟨τ, u⟩, hp, rfl⟩, hx⟩
        have hu := (hmemE τ (hJI hp.1) u).mp hx
        subst hu
        exact ⟨τ, hp.1, stemPt_eq_tubeMap L w τ⟩
      · rintro ⟨τ, hτ, rfl⟩
        exact ⟨⟨(τ, 0), ⟨hτ, by norm_num, by norm_num⟩, (stemPt_eq_tubeMap L w τ).symm⟩,
          hIE τ (hJI hτ)⟩
    · obtain ⟨τ₂, hτ₂⟩ := hJne
      exact ⟨_, ⟨(τ₂, -(1/2)), ⟨hτ₂, by norm_num, by norm_num⟩, rfl⟩⟩
    · obtain ⟨τ₂, hτ₂⟩ := hJne
      exact ⟨_, ⟨(τ₂, 1/2), ⟨hτ₂, by norm_num, by norm_num⟩, rfl⟩⟩
    · intro x hx
      exact hncov J hJI x hx.1 hx.2

theorem stemTube_leaf (L : Lollipop) {D : Set Point} (hD : IsClosed D) (E : Set Point)
    (I : Set ℝ) (s : ℝ) (hIo : IsOpen I) (hIc : I.OrdConnected) (hsI : s ∈ I)
    (hlt : ∃ τ ∈ I, τ < s)
    (hIE : ∀ τ ∈ I, (stemPt L τ ∈ E ↔ s ≤ τ)) (hline : ∀ z ∈ E, ∃ τ, z = stemPt L τ)
    (hnew : ∀ z ∈ E, z ∉ D → ∃ τ ∈ I, z = stemPt L τ)
    (hID : ∀ τ ∈ I, stemPt L τ ∉ D) :
    ∃ U S : Set Point, OneCollar D E S U := by
  obtain ⟨w, hwc, hwpos, hwD⟩ := exists_width L hD I hID
  have hTc : Continuous (tubeMap L w) := tubeMap_continuous L hwc
  have hmemE : ∀ τ ∈ I, ∀ u : ℝ, tubeMap L w (τ, u) ∈ E ↔ (u = 0 ∧ s ≤ τ) := by
    intro τ hτ u
    rw [tubeMap_mem_E_iff L hline (hwpos τ hτ).ne', hIE τ hτ]
  obtain ⟨τ₁, hτ₁, hτ₁s⟩ := hlt
  let Z : Set (ℝ × ℝ) := {p | p ∈ I ×ˢ Ioo (-1 : ℝ) 1 ∧ (p.2 ≠ 0 ∨ p.1 < s)}
  have hZ : Z = ((I ×ˢ Ioo (0 : ℝ) 1) ∪ ((I ∩ Iio s) ×ˢ Ioo (-1 : ℝ) 1)) ∪
      (I ×ˢ Ioo (-1 : ℝ) 0) := by
    ext ⟨τ, u⟩
    simp only [Z, mem_setOf_eq, mem_union, mem_prod, mem_inter_iff, mem_Ioo, mem_Iio]
    constructor
    · rintro ⟨⟨hτ, h1, h2⟩, h | h⟩
      · rcases lt_or_gt_of_ne h with h' | h'
        · exact Or.inr ⟨hτ, h1, h'⟩
        · exact Or.inl (Or.inl ⟨hτ, h', h2⟩)
      · exact Or.inl (Or.inr ⟨⟨hτ, h⟩, h1, h2⟩)
    · rintro ((⟨hτ, h1, h2⟩ | ⟨⟨hτ, hs⟩, h1, h2⟩) | ⟨hτ, h1, h2⟩)
      · exact ⟨⟨hτ, by linarith, h2⟩, Or.inl h1.ne'⟩
      · exact ⟨⟨hτ, h1, h2⟩, Or.inr hs⟩
      · exact ⟨⟨hτ, h1, by linarith⟩, Or.inl h2.ne⟩
  have hZpre : IsPreconnected Z := by
    rw [hZ]
    have hA : IsPreconnected (I ×ˢ Ioo (0 : ℝ) 1) :=
      hIc.isPreconnected.prod isPreconnected_Ioo
    have hB : IsPreconnected ((I ∩ Iio s) ×ˢ Ioo (-1 : ℝ) 1) :=
      (hIc.inter ordConnected_Iio).isPreconnected.prod isPreconnected_Ioo
    have hC : IsPreconnected (I ×ˢ Ioo (-1 : ℝ) 0) :=
      hIc.isPreconnected.prod isPreconnected_Ioo
    refine IsPreconnected.union (τ₁, -(1/2)) (Or.inr ⟨⟨hτ₁, hτ₁s⟩, by norm_num, by norm_num⟩)
      ⟨hτ₁, by norm_num, by norm_num⟩ ?_ hC
    exact IsPreconnected.union (τ₁, 1/2) ⟨hτ₁, by norm_num, by norm_num⟩
      ⟨⟨hτ₁, hτ₁s⟩, by norm_num, by norm_num⟩ hA hB
  refine ⟨tubeMap L w '' (I ×ˢ Ioo (-1 : ℝ) 1), tubeMap L w '' Z, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine tubeMap_image_isOpen L hwc hIo hwpos (hIo.prod isOpen_Ioo) ?_
    intro p hp
    exact hp.1
  · intro z hz hzD
    obtain ⟨τ, hτ, rfl⟩ := hnew z hz hzD
    exact ⟨(τ, 0), ⟨hτ, by norm_num, by norm_num⟩, (stemPt_eq_tubeMap L w τ).symm⟩
  · rintro _ ⟨⟨τ, u⟩, hp, rfl⟩
    exact hwD τ hp.1 u (abs_lt.mpr ⟨hp.2.1, hp.2.2⟩)
  · exact hZpre.image _ hTc.continuousOn
  · rintro _ ⟨⟨τ, u⟩, hp, rfl⟩
    refine ⟨⟨(τ, u), hp.1, rfl⟩, ?_⟩
    intro hx
    have := (hmemE τ hp.1.1 u).mp hx
    rcases hp.2 with h | h
    · exact h this.1
    · exact absurd this.2 (not_le.mpr h)
  · rintro _ ⟨⟨τ, u⟩, hp, rfl⟩ hx
    refine ⟨(τ, u), ⟨hp, ?_⟩, rfl⟩
    by_contra hcon
    have h1 : u = 0 := by
      by_contra h; exact hcon (Or.inl h)
    have h2 : s ≤ τ := by
      by_contra h; exact hcon (Or.inr (not_le.mp h))
    exact hx ((hmemE τ hp.1 u).mpr ⟨h1, h2⟩)
  · refine ⟨tubeMap L w (s, 1/2), (s, 1/2), ⟨⟨hsI, by norm_num, by norm_num⟩, Or.inl (by norm_num)⟩, rfl⟩

theorem seg_collars (L : Lollipop) {D : Set Point} (hD : IsClosed D)
    {s t : ℝ} (hs : 1 ≤ s) (hst : s < t)
    (hopen : ∀ τ ∈ Ioo s t, stemPt L τ ∉ D)
    (hend : stemPt L s ∈ D ∧ stemPt L t ∈ D) :
    ∃ U S₁ S₂ : Set Point,
      Collars D (segSet L s t) S₁ S₂ U ∧
      ∀ τ₀ ∈ Ioo s t, ∀ δ : ℝ, 0 < δ → Icc (τ₀ - δ) (τ₀ + δ) ⊆ Ioo s t →
        Germ (segSet L s t) S₁ S₂ U (stemPt L '' Ioo (τ₀ - δ) (τ₀ + δ)) := by
  obtain ⟨U, S₁, S₂, hC, hG⟩ := stemTube_collars L hD (segSet L s t) (Ioo s t) isOpen_Ioo
    ordConnected_Ioo ⟨(s + t) / 2, by constructor <;> linarith⟩
    (fun τ hτ => ⟨τ, Ioo_subset_Icc_self hτ, rfl⟩)
    (fun z hz => by obtain ⟨τ, _, rfl⟩ := hz; exact ⟨τ, rfl⟩)
    (by
      rintro z ⟨τ, hτ, rfl⟩ hzD
      refine ⟨τ, ⟨lt_of_le_of_ne hτ.1 ?_, lt_of_le_of_ne hτ.2 ?_⟩, rfl⟩
      · rintro rfl; exact hzD hend.1
      · rintro rfl; exact hzD hend.2)
    hopen
  refine ⟨U, S₁, S₂, hC, ?_⟩
  intro τ₀ hτ₀ δ hδ hsub
  exact hG _ isOpen_Ioo ordConnected_Ioo ⟨τ₀, by constructor <;> linarith⟩
    (fun x hx => hsub ⟨hx.1.le, hx.2.le⟩)

theorem ray_collars (L : Lollipop) {D : Set Point} (hD : IsClosed D)
    {s : ℝ} (hs : 1 ≤ s)
    (hopen : ∀ τ, s < τ → stemPt L τ ∉ D)
    (hend : stemPt L s ∈ D) :
    ∃ U S₁ S₂ : Set Point,
      Collars D (raySet L s) S₁ S₂ U ∧
      ∀ τ₀, s < τ₀ → ∀ δ : ℝ, 0 < δ → s < τ₀ - δ →
        Germ (raySet L s) S₁ S₂ U (stemPt L '' Ioo (τ₀ - δ) (τ₀ + δ)) := by
  obtain ⟨U, S₁, S₂, hC, hG⟩ := stemTube_collars L hD (raySet L s) (Ioi s) isOpen_Ioi
    ordConnected_Ioi ⟨s + 1, by simp⟩
    (fun τ hτ => ⟨τ, Ioi_subset_Ici_self hτ, rfl⟩)
    (fun z hz => by obtain ⟨τ, _, rfl⟩ := hz; exact ⟨τ, rfl⟩)
    (by
      rintro z ⟨τ, hτ, rfl⟩ hzD
      refine ⟨τ, (show s < τ from lt_of_le_of_ne hτ ?_), rfl⟩
      rintro rfl; exact hzD hend)
    (fun τ hτ => hopen τ hτ)
  refine ⟨U, S₁, S₂, hC, ?_⟩
  intro τ₀ hτ₀ δ hδ hsub
  exact hG _ isOpen_Ioo ordConnected_Ioo ⟨τ₀, by constructor <;> linarith⟩
    (fun x hx => lt_trans hsub hx.1)

/-- A free end has a neighbourhood missing `D`. -/
theorem exists_free_nbhd (L : Lollipop) {D : Set Point} (hD : IsClosed D) {s : ℝ}
    (hfree : stemPt L s ∉ D) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ τ, s - ε < τ → τ < s + ε → stemPt L τ ∉ D := by
  have hopen : IsOpen (stemPt L ⁻¹' Dᶜ) := hD.isOpen_compl.preimage (continuous_stemPt L)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen s hfree
  refine ⟨ε, hε, fun τ h1 h2 => ?_⟩
  have : τ ∈ Metric.ball s ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith
  exact hball this

theorem seg_leaf_collar (L : Lollipop) {D : Set Point} (hD : IsClosed D)
    {s t : ℝ} (hs : 1 ≤ s) (hst : s < t)
    (hfree : stemPt L s ∉ D) (hopen : ∀ τ ∈ Ioo s t, stemPt L τ ∉ D)
    (hend : stemPt L t ∈ D) :
    ∃ U S : Set Point, OneCollar D (segSet L s t) S U := by
  obtain ⟨ε, hε, hfn⟩ := exists_free_nbhd L hD hfree
  refine stemTube_leaf L hD (segSet L s t) (Ioo (s - ε) t) s isOpen_Ioo ordConnected_Ioo
    ⟨by linarith, hst⟩ ⟨s - ε / 2, ⟨by linarith, by linarith⟩, by linarith⟩ ?_ ?_ ?_ ?_
  · intro τ hτ
    constructor
    · rintro ⟨τ', hτ', h⟩
      have := stemPt_injective L h
      subst this
      exact hτ'.1
    · intro h
      exact ⟨τ, ⟨h, hτ.2.le⟩, rfl⟩
  · intro z hz; obtain ⟨τ, _, rfl⟩ := hz; exact ⟨τ, rfl⟩
  · rintro z ⟨τ, hτ, rfl⟩ hzD
    refine ⟨τ, ⟨by linarith [hτ.1], lt_of_le_of_ne hτ.2 ?_⟩, rfl⟩
    rintro rfl; exact hzD hend
  · intro τ hτ
    rcases lt_trichotomy τ s with h | h | h
    · exact hfn τ hτ.1 (by linarith)
    · subst h; exact hfree
    · exact hopen τ ⟨h, hτ.2⟩

theorem ray_leaf_collar (L : Lollipop) {D : Set Point} (hD : IsClosed D)
    {s : ℝ} (hs : 1 ≤ s)
    (hfree : stemPt L s ∉ D) (hopen : ∀ τ, s < τ → stemPt L τ ∉ D) :
    ∃ U S : Set Point, OneCollar D (raySet L s) S U := by
  obtain ⟨ε, hε, hfn⟩ := exists_free_nbhd L hD hfree
  refine stemTube_leaf L hD (raySet L s) (Ioi (s - ε)) s isOpen_Ioi ordConnected_Ioi
    (by simp [hε]) ⟨s - ε / 2, by simp; linarith, by linarith⟩ ?_ ?_ ?_ ?_
  · intro τ hτ
    constructor
    · rintro ⟨τ', hτ', h⟩
      have := stemPt_injective L h
      subst this
      exact hτ'
    · intro h
      exact ⟨τ, h, rfl⟩
  · intro z hz; obtain ⟨τ, _, rfl⟩ := hz; exact ⟨τ, rfl⟩
  · rintro z ⟨τ, hτ, rfl⟩ hzD
    have hτ' : s ≤ τ := hτ
    exact ⟨τ, (show s - ε < τ by linarith), rfl⟩
  · intro τ hτ
    rcases lt_trichotomy τ s with h | h | h
    · exact hfn τ hτ (by linarith)
    · subst h; exact hfree
    · exact hopen τ h

#print axioms seg_collars
#print axioms ray_collars
#print axioms seg_leaf_collar
#print axioms ray_leaf_collar


end StemAux
export StemAux (seg_collars ray_collars seg_leaf_collar ray_leaf_collar)

end Pieces
end EndToEnd
end Concrete
end Lollipop
