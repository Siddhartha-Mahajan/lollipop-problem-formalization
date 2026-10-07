import Lollipop.Lemma_8_5.Proof
import Lollipop.Topology.Carrier.Defs
import Lollipop.Topology.Carrier.Defs2
import Lollipop.Topology.Carrier.CircleCollars
import Lollipop.Topology.Carrier.StemCollars
import Lollipop.Topology.Carrier.LocalSides
import Lollipop.Topology.Carrier.SphereArcs
import Lollipop.Topology.Carrier.SphereSides
import Lollipop.Topology.Carrier.HatArcs
import Lollipop.Topology.Carrier.Collar
import Lollipop.Topology.Carrier.Gap
import Lollipop.Topology.Carrier.TM
import Lollipop.Topology.Carrier.Conn
import Mathlib.Tactic

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace Pieces

open Set

namespace PotAux

theorem arc_isConnected {P : Set Sphere2} {x y : Sphere2} (h : IsSphereArc P x y) :
    IsConnected P := by
  obtain ⟨f, rfl, hc, -, -, -⟩ := h
  exact (isConnected_Icc zero_le_one).image f hc.continuousOn

theorem finite_mem_hatSet {D : Set Point} {x : Point} :
    finitePoint x ∈ hatSet D ↔ x ∈ D := by
  simp [hatSet]

theorem kset_union (L : Lollipop) (D E : Set Point) (hE : E ⊆ L.carrier) :
    Kset L (D ∪ E) = Kset L D ∪ finiteLift E := by
  have h1 : ∀ p, p ∈ finitePoint '' E → p ∈ finitePoint '' L.carrier :=
    fun p hp => image_mono hE hp
  ext p
  simp only [Kset, hatSet, hatCarrier, finiteLift, image_union, mem_inter_iff, mem_union,
    mem_singleton_iff] at *
  have := h1 p
  tauto

theorem isClosed_kset (L : Lollipop) {D : Set Point} (hD : IsClosed D) :
    IsClosed (Kset L D) :=
  (isClosed_hatCarrier L).inter (isClosed_hatSet hD)

theorem kset_subset_hatCarrier (L : Lollipop) (D : Set Point) : Kset L D ⊆ hatCarrier L :=
  inter_subset_left

theorem isClosed_cc {K : Set Sphere2} (hK : IsClosed K) {b : Sphere2} (hb : b ∈ K) :
    IsClosed (connectedComponentIn K b) := by
  rw [← closure_subset_iff_isClosed]
  have hpre : IsPreconnected (closure (connectedComponentIn K b)) :=
    isPreconnected_connectedComponentIn.closure
  have hsub : closure (connectedComponentIn K b) ⊆ K :=
    closure_minimal (connectedComponentIn_subset _ _) hK
  exact hpre.subset_connectedComponentIn (subset_closure (mem_connectedComponentIn hb)) hsub

/-- The dichotomy for gap pieces. -/
theorem gap_dichotomy (L : Lollipop) {D : Set Point} (hD : IsClosed D)
    (hfin : Finite (ConnectedComponents (Kset L D))) {E : Set Point} (hE : E ⊆ L.carrier)
    {Ehat : Set Sphere2} (hEq : Kset L D ∪ Ehat = Kset L D ∪ finiteLift E)
    (hc : IsClosed Ehat) (hcn : IsConnected Ehat) {a b : Sphere2}
    (ha : a ∈ Kset L D ∩ Ehat) (hb : b ∈ Kset L D ∩ Ehat) (hKE : Kset L D ∩ Ehat ⊆ {a, b})
    (hsame : a ∈ connectedComponentIn (Kset L D) b →
      L.circle ⊆ D ∪ E ∧ ¬ L.circle ⊆ D)
    (hnot : a ∉ connectedComponentIn (Kset L D) b →
      (L.circle ⊆ D ∪ E ↔ L.circle ⊆ D)) :
    Finite (ConnectedComponents (Kset L (D ∪ E))) ∧ Psi L (D ∪ E) + 1 = Psi L D := by
  have hK := isClosed_kset L hD
  simp only [Psi]
  rw [kset_union L D E hE, ← hEq]
  classical
  by_cases hab : a ∈ connectedComponentIn (Kset L D) b
  · obtain ⟨hf, hcnt⟩ := componentCount_union_of_same hK hc hcn ha hb hKE hab hfin
    obtain ⟨h1, h2⟩ := hsame hab
    refine ⟨hf, ?_⟩
    rw [if_pos h1, if_neg h2, hcnt]
  · obtain ⟨hf, hcnt⟩ := componentCount_union_of_not_same hK hc hcn ha hb hKE hab hfin
    have h := hnot hab
    refine ⟨hf, ?_⟩
    by_cases h1 : L.circle ⊆ D
    · rw [if_pos (h.2 h1), if_pos h1]; omega
    · rw [if_neg (fun h' => h1 (h.1 h')), if_neg h1]; omega

/-- The dichotomy for leaf pieces. -/
theorem leaf_dichotomy (L : Lollipop) {D : Set Point} (hD : IsClosed D)
    (hfin : Finite (ConnectedComponents (Kset L D))) {E : Set Point} (hE : E ⊆ L.carrier)
    {Ehat : Set Sphere2} (hEq : Kset L D ∪ Ehat = Kset L D ∪ finiteLift E)
    (hc : IsClosed Ehat) (hcn : IsConnected Ehat) {b : Sphere2}
    (hb : b ∈ Kset L D ∩ Ehat) (hKE : Kset L D ∩ Ehat ⊆ {b})
    (hcirc : L.circle ⊆ D ∪ E ↔ L.circle ⊆ D) :
    Finite (ConnectedComponents (Kset L (D ∪ E))) ∧ Psi L (D ∪ E) = Psi L D := by
  have hK := isClosed_kset L hD
  simp only [Psi]
  rw [kset_union L D E hE, ← hEq]
  classical
  have hKE' : Kset L D ∩ Ehat ⊆ {b, b} := by
    intro x hx; simp [hKE hx]
  obtain ⟨hf, hcnt⟩ := componentCount_union_of_same hK hc hcn hb hb hKE'
    (mem_connectedComponentIn hb.1) hfin
  refine ⟨hf, ?_⟩
  by_cases h1 : L.circle ⊆ D
  · rw [if_pos (hcirc.2 h1), if_pos h1, hcnt]
  · rw [if_neg (fun h' => h1 (hcirc.1 h')), if_neg h1, hcnt]

/-! ### Circle and stem helpers -/

theorem circlePt_add_int (L : Lollipop) (θ : ℝ) (k : ℤ) :
    circlePt L (θ + k * (2 * Real.pi)) = circlePt L θ := by
  simp [circlePt, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

theorem circlePt_add_two_pi (L : Lollipop) (θ : ℝ) :
    circlePt L (θ + 2 * Real.pi) = circlePt L θ := by
  simpa using circlePt_add_int L θ 1

theorem exists_angle_Ico (L : Lollipop) {x : Point} (hx : x ∈ L.circle) (α : ℝ) :
    ∃ θ ∈ Ico α (α + 2 * Real.pi), x = circlePt L θ := by
  obtain ⟨θ0, -, rfl⟩ := HatAux.circle_exists_angle L hx
  have hpi := Real.pi_pos
  obtain ⟨k, hk⟩ : ∃ k : ℤ, α ≤ θ0 + k * (2 * Real.pi) ∧ θ0 + k * (2 * Real.pi) < α + 2 * Real.pi := by
    refine ⟨⌈(α - θ0) / (2 * Real.pi)⌉, ?_, ?_⟩
    · have := Int.le_ceil ((α - θ0) / (2 * Real.pi))
      rw [div_le_iff₀ (by positivity)] at this
      linarith
    · have := Int.ceil_lt_add_one ((α - θ0) / (2 * Real.pi))
      have h2 : (⌈(α - θ0) / (2 * Real.pi)⌉ : ℝ) * (2 * Real.pi) <
          ((α - θ0) / (2 * Real.pi) + 1) * (2 * Real.pi) :=
        mul_lt_mul_of_pos_right this (by positivity)
      have h3 : ((α - θ0) / (2 * Real.pi) + 1) * (2 * Real.pi) = α - θ0 + 2 * Real.pi := by
        field_simp
      linarith
  exact ⟨θ0 + k * (2 * Real.pi), ⟨hk.1, hk.2⟩, (circlePt_add_int L θ0 k).symm⟩

theorem circlePt_eq_iff (L : Lollipop) {a b : ℝ} (hab : circlePt L a = circlePt L b) :
    ∃ k : ℤ, a - b = 2 * Real.pi * k := by
  have hr : L.radial 0 ^ 2 + L.radial 1 ^ 2 ≠ 0 := by
    intro h
    apply L.radial_ne_zero
    have h0 : L.radial 0 = 0 := by nlinarith [sq_nonneg (L.radial 0), sq_nonneg (L.radial 1)]
    have h1 : L.radial 1 = 0 := by nlinarith [sq_nonneg (L.radial 0), sq_nonneg (L.radial 1)]
    refine PiLp.ext (fun i => ?_); fin_cases i <;> simp [h0, h1]
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
  exact Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 (Real.Angle.cos_sin_inj hc hs)

/-- Two angles in `[x, x + 2π)`... if the circle points agree and the angles differ by a number
in `(0, 2π)`, contradiction. -/
theorem circlePt_ne_of_lt (L : Lollipop) {a b : ℝ} (h1 : 0 < a - b) (h2 : a - b < 2 * Real.pi) :
    circlePt L a ≠ circlePt L b := by
  intro h
  obtain ⟨k, hk⟩ := circlePt_eq_iff L h
  have hpi := Real.pi_pos
  have h3 : (0 : ℝ) < k := by nlinarith
  have h4 : (k : ℝ) < 1 := by nlinarith
  have h3' : 0 < k := by exact_mod_cast h3
  have h4' : k < 1 := by exact_mod_cast h4
  omega

theorem anchor_eq_stemPt (L : Lollipop) : L.anchor = stemPt L 1 := by
  simp [Lollipop.anchor, HatAux.stemPt_def]

theorem stem_circle {L : Lollipop} {τ : ℝ} (hτ : 1 ≤ τ) (h : stemPt L τ ∈ L.circle) : τ = 1 := by
  have h1 : ‖stemPt L τ - L.center‖ = L.radius := h
  rw [HatAux.norm_stemPt_sub, abs_of_nonneg (by linarith)] at h1
  have h2 : L.radius = 1 * ‖L.radial‖ := by simp [Lollipop.radius]
  have h3 : 0 < ‖L.radial‖ := norm_pos_iff.2 L.radial_ne_zero
  have : τ * ‖L.radial‖ = 1 * ‖L.radial‖ := by rw [h1, h2]
  exact mul_right_cancel₀ h3.ne' this

theorem stemPt_mem_carrier (L : Lollipop) {τ : ℝ} (hτ : 1 ≤ τ) : stemPt L τ ∈ L.carrier :=
  Or.inr ⟨τ, hτ, rfl⟩

theorem circlePt_mem_carrier (L : Lollipop) (θ : ℝ) : circlePt L θ ∈ L.carrier :=
  Or.inl (HatAux.circlePt_mem_circle L θ)

theorem continuous_stemPt (L : Lollipop) : Continuous (stemPt L) := by
  have : stemPt L = fun t => L.center + t • L.radial := funext fun t => HatAux.stemPt_def L t
  rw [this]; fun_prop

/-! ### Circle gap piece -/

theorem gap_circle (L : Lollipop) {D : Set Point} (hD : IsClosed D)
    (hfin : Finite (ConnectedComponents (Kset L D))) {α β : ℝ} (hαβ : α < β)
    (hβ : β ≤ α + 2 * Real.pi) (hopen : ∀ θ ∈ Ioo α β, circlePt L θ ∉ D)
    (hend : circlePt L α ∈ D ∧ circlePt L β ∈ D) (hnsub : ¬ circleArcSet L α β ⊆ D) :
    Finite (ConnectedComponents (Kset L (D ∪ circleArcSet L α β))) ∧
      Psi L (D ∪ circleArcSet L α β) + 1 = Psi L D := by
  have hEc : circleArcSet L α β ⊆ L.carrier := by
    rintro _ ⟨θ, -, rfl⟩; exact circlePt_mem_carrier L θ
  have hcirc : circleArcSet L α β ⊆ L.circle := by
    rintro _ ⟨θ, -, rfl⟩; exact HatAux.circlePt_mem_circle L θ
  have hnc : ¬ L.circle ⊆ D := fun h => hnsub (hcirc.trans h)
  have hcont : Continuous (fun θ => finitePoint (circlePt L θ)) :=
    HatAux.continuous_finitePoint.comp (HatAux.continuous_circlePt L)
  have hlift : finiteLift (circleArcSet L α β) =
      (fun θ => finitePoint (circlePt L θ)) '' Icc α β := by
    simp [finiteLift, circleArcSet, image_image]
  have hcl : IsClosed (finiteLift (circleArcSet L α β)) := by
    rw [hlift]; exact (isCompact_Icc.image hcont).isClosed
  have hcn : IsConnected (finiteLift (circleArcSet L α β)) := by
    rw [hlift]; exact (isConnected_Icc hαβ.le).image _ hcont.continuousOn
  have hmemK : ∀ θ, circlePt L θ ∈ D → finitePoint (circlePt L θ) ∈ Kset L D :=
    fun θ h => ⟨(finitePoint_mem_hatCarrier_iff L _).2 (circlePt_mem_carrier L θ),
      finite_mem_hatSet.2 h⟩
  have hmemE : ∀ θ ∈ Icc α β, finitePoint (circlePt L θ) ∈ finiteLift (circleArcSet L α β) :=
    fun θ hθ => ⟨circlePt L θ, ⟨θ, hθ, rfl⟩, rfl⟩
  have haK := hmemK α hend.1
  have hbK := hmemK β hend.2
  have haE := hmemE α ⟨le_rfl, hαβ.le⟩
  have hbE := hmemE β ⟨hαβ.le, le_rfl⟩
  have hKD : IsClosed (Kset L D) := isClosed_kset L hD
  refine gap_dichotomy L hD hfin hEc rfl hcl hcn (a := finitePoint (circlePt L α))
    (b := finitePoint (circlePt L β)) ⟨haK, haE⟩ ⟨hbK, hbE⟩ ?_ ?_ ?_
  · rintro p ⟨hpK, ⟨x, ⟨θ, hθ, rfl⟩, rfl⟩⟩
    have hD' : circlePt L θ ∈ D := finite_mem_hatSet.1 hpK.2
    rcases hθ.1.eq_or_lt with h1 | h1
    · left; rw [h1]
    rcases hθ.2.eq_or_lt with h2 | h2
    · right; rw [h2]; exact mem_singleton _
    · exact absurd hD' (hopen θ ⟨h1, h2⟩)
  · intro hab
    refine ⟨?_, hnc⟩
    have hZcl := isClosed_cc hKD hbK
    have hZpre : IsPreconnected (connectedComponentIn (Kset L D) (finitePoint (circlePt L β))) :=
      isPreconnected_connectedComponentIn
    have hZX : connectedComponentIn (Kset L D) (finitePoint (circlePt L β)) ⊆ hatCarrier L :=
      (connectedComponentIn_subset _ _).trans (kset_subset_hatCarrier L D)
    have hbZ := mem_connectedComponentIn hbK
    rcases conn_circle L hZcl hZpre hZX hαβ hβ hab hbZ with h | h
    · exfalso
      have hm : (α + β) / 2 ∈ Icc α β := ⟨by linarith, by linarith⟩
      have := h _ hm
      have hD' := finite_mem_hatSet.1 (connectedComponentIn_subset _ _ this).2
      exact hopen _ ⟨by linarith, by linarith⟩ hD'
    · intro x hx
      obtain ⟨θ, hθ, rfl⟩ := exists_angle_Ico L hx α
      by_cases h' : θ ≤ β
      · right; exact ⟨θ, ⟨hθ.1, h'⟩, rfl⟩
      · left
        have := h θ ⟨(not_le.1 h').le, hθ.2.le⟩
        exact finite_mem_hatSet.1 (connectedComponentIn_subset _ _ this).2
  · intro hab
    refine iff_of_false ?_ hnc
    intro hsub
    apply hab
    have hβlt : β < α + 2 * Real.pi := by
      refine lt_of_le_of_ne hβ ?_
      intro h
      apply hab
      have : circlePt L α = circlePt L β := by rw [h, circlePt_add_two_pi]
      rw [this]
      exact mem_connectedComponentIn hbK
    have hZ'K : (fun θ => finitePoint (circlePt L θ)) '' Icc β (α + 2 * Real.pi) ⊆ Kset L D := by
      rintro _ ⟨θ, hθ, rfl⟩
      refine hmemK θ ?_
      rcases hθ.1.eq_or_lt with h1 | h1
      · rw [← h1]; exact hend.2
      rcases hθ.2.eq_or_lt with h2 | h2
      · rw [h2, circlePt_add_two_pi]; exact hend.1
      · rcases hsub (HatAux.circlePt_mem_circle L θ) with hD' | ⟨θ', hθ', hθ'eq⟩
        · exact hD'
        · exfalso
          refine circlePt_ne_of_lt L (a := θ) (b := θ') (by linarith [hθ'.2]) ?_ hθ'eq.symm
          linarith [hθ'.1]
    have hZ'pre : IsPreconnected ((fun θ => finitePoint (circlePt L θ)) '' Icc β (α + 2 * Real.pi)) :=
      isPreconnected_Icc.image _ hcont.continuousOn
    have hbmem : finitePoint (circlePt L β) ∈
        (fun θ => finitePoint (circlePt L θ)) '' Icc β (α + 2 * Real.pi) :=
      ⟨β, ⟨le_rfl, hβ⟩, rfl⟩
    refine hZ'pre.subset_connectedComponentIn hbmem hZ'K ?_
    exact ⟨α + 2 * Real.pi, ⟨hβ, le_rfl⟩, by simp [circlePt_add_two_pi]⟩

/-! ### Stem pieces -/

theorem stem_piece_iff (L : Lollipop) {D E : Set Point} (hanchor : L.anchor ∈ D)
    (hE : ∀ x ∈ E, x ∈ L.circle → x ∈ D) : L.circle ⊆ D ∪ E ↔ L.circle ⊆ D := by
  constructor
  · intro h x hx
    rcases h hx with h1 | h1
    · exact h1
    · exact hE x h1 hx
  · intro h x hx
    exact Or.inl (h hx)

theorem ray_eq (L : Lollipop) (D E : Set Point) :
    Kset L D ∪ hatSet E = Kset L D ∪ finiteLift E := by
  have hinf : infinity ∈ Kset L D := ⟨infinity_mem_hatCarrier L, Or.inr rfl⟩
  ext p
  simp only [hatSet, mem_union, mem_singleton_iff]
  constructor
  · rintro (h | h | rfl)
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inl hinf
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

theorem gap_seg (L : Lollipop) {D : Set Point} (hD : IsClosed D) (hanchor : L.anchor ∈ D)
    (hfin : Finite (ConnectedComponents (Kset L D))) {s t : ℝ} (hs : 1 ≤ s) (hst : s < t)
    (hopen : ∀ τ ∈ Ioo s t, stemPt L τ ∉ D) (hend : stemPt L s ∈ D ∧ stemPt L t ∈ D) :
    Finite (ConnectedComponents (Kset L (D ∪ segSet L s t))) ∧
      Psi L (D ∪ segSet L s t) + 1 = Psi L D := by
  have hEc : segSet L s t ⊆ L.carrier := by
    rintro _ ⟨τ, hτ, rfl⟩; exact stemPt_mem_carrier L (hs.trans hτ.1)
  have hcont : Continuous (fun τ => finitePoint (stemPt L τ)) :=
    HatAux.continuous_finitePoint.comp (continuous_stemPt L)
  have hlift : finiteLift (segSet L s t) = (fun τ => finitePoint (stemPt L τ)) '' Icc s t := by
    simp [finiteLift, segSet, image_image]
  have hcl : IsClosed (finiteLift (segSet L s t)) := by
    rw [hlift]; exact (isCompact_Icc.image hcont).isClosed
  have hcn : IsConnected (finiteLift (segSet L s t)) := by
    rw [hlift]; exact (isConnected_Icc hst.le).image _ hcont.continuousOn
  have hmemK : ∀ τ, 1 ≤ τ → stemPt L τ ∈ D → finitePoint (stemPt L τ) ∈ Kset L D :=
    fun τ hτ h => ⟨(finitePoint_mem_hatCarrier_iff L _).2 (stemPt_mem_carrier L hτ),
      finite_mem_hatSet.2 h⟩
  have hmemE : ∀ τ ∈ Icc s t, finitePoint (stemPt L τ) ∈ finiteLift (segSet L s t) :=
    fun τ hτ => ⟨stemPt L τ, ⟨τ, hτ, rfl⟩, rfl⟩
  have haK := hmemK s hs hend.1
  have hbK := hmemK t (hs.trans hst.le) hend.2
  have haE := hmemE s ⟨le_rfl, hst.le⟩
  have hbE := hmemE t ⟨hst.le, le_rfl⟩
  have hKD : IsClosed (Kset L D) := isClosed_kset L hD
  refine gap_dichotomy L hD hfin hEc rfl hcl hcn (a := finitePoint (stemPt L s))
    (b := finitePoint (stemPt L t)) ⟨haK, haE⟩ ⟨hbK, hbE⟩ ?_ ?_ ?_
  · rintro p ⟨hpK, ⟨x, ⟨τ, hτ, rfl⟩, rfl⟩⟩
    have hD' : stemPt L τ ∈ D := finite_mem_hatSet.1 hpK.2
    rcases hτ.1.eq_or_lt with h1 | h1
    · left; rw [h1]
    rcases hτ.2.eq_or_lt with h2 | h2
    · right; rw [h2]; exact mem_singleton _
    · exact absurd hD' (hopen τ ⟨h1, h2⟩)
  · intro hab
    exfalso
    have hZcl := isClosed_cc hKD hbK
    have hZpre : IsPreconnected (connectedComponentIn (Kset L D) (finitePoint (stemPt L t))) :=
      isPreconnected_connectedComponentIn
    have hZX : connectedComponentIn (Kset L D) (finitePoint (stemPt L t)) ⊆ hatCarrier L :=
      (connectedComponentIn_subset _ _).trans (kset_subset_hatCarrier L D)
    have hbZ := mem_connectedComponentIn hbK
    have := conn_stem L hZcl hZpre hZX hs hst.le hab hbZ ((s + t) / 2)
      ⟨by linarith, by linarith⟩
    have hD' := finite_mem_hatSet.1 (connectedComponentIn_subset _ _ this).2
    exact hopen _ ⟨by linarith, by linarith⟩ hD'
  · intro _
    refine stem_piece_iff L hanchor ?_
    rintro _ ⟨τ, hτ, rfl⟩ hc
    have h1 := stem_circle (hs.trans hτ.1) hc
    rw [h1, ← anchor_eq_stemPt]; exact hanchor

theorem gap_ray (L : Lollipop) {D : Set Point} (hD : IsClosed D) (hanchor : L.anchor ∈ D)
    (hfin : Finite (ConnectedComponents (Kset L D))) {s : ℝ} (hs : 1 ≤ s)
    (hopen : ∀ τ, s < τ → stemPt L τ ∉ D) (hend : stemPt L s ∈ D) :
    Finite (ConnectedComponents (Kset L (D ∪ raySet L s))) ∧
      Psi L (D ∪ raySet L s) + 1 = Psi L D := by
  have hEc : raySet L s ⊆ L.carrier := by
    rintro _ ⟨τ, hτ, rfl⟩; exact stemPt_mem_carrier L (hs.trans hτ)
  have hcl : IsClosed (hatSet (raySet L s)) :=
    isClosed_hatSet (IsGapPiece.ray hs hopen hend).isClosed
  have hcn : IsConnected (hatSet (raySet L s)) := arc_isConnected (HatAux.raySet_isSphereArc L hs)
  have hmemK : ∀ τ, 1 ≤ τ → stemPt L τ ∈ D → finitePoint (stemPt L τ) ∈ Kset L D :=
    fun τ hτ h => ⟨(finitePoint_mem_hatCarrier_iff L _).2 (stemPt_mem_carrier L hτ),
      finite_mem_hatSet.2 h⟩
  have hinfK : infinity ∈ Kset L D := ⟨infinity_mem_hatCarrier L, Or.inr rfl⟩
  have haK := hmemK s hs hend
  have haE : finitePoint (stemPt L s) ∈ hatSet (raySet L s) :=
    Or.inl ⟨stemPt L s, ⟨s, self_mem_Ici, rfl⟩, rfl⟩
  have hbE : infinity ∈ hatSet (raySet L s) := Or.inr rfl
  have hKD : IsClosed (Kset L D) := isClosed_kset L hD
  refine gap_dichotomy L hD hfin hEc (ray_eq L D _) hcl hcn (a := finitePoint (stemPt L s))
    (b := infinity) ⟨haK, haE⟩ ⟨hinfK, hbE⟩ ?_ ?_ ?_
  · rintro p ⟨hpK, hpE⟩
    rcases hpE with ⟨x, ⟨τ, hτ, rfl⟩, rfl⟩ | hp
    · have hD' : stemPt L τ ∈ D := finite_mem_hatSet.1 hpK.2
      rcases (show s ≤ τ from hτ).eq_or_lt with h1 | h1
      · left; rw [h1]
      · exact absurd hD' (hopen τ h1)
    · right; exact hp
  · intro hab
    exfalso
    have hZcl := isClosed_cc hKD hinfK
    have hZpre : IsPreconnected (connectedComponentIn (Kset L D) infinity) :=
      isPreconnected_connectedComponentIn
    have hZX : connectedComponentIn (Kset L D) infinity ⊆ hatCarrier L :=
      (connectedComponentIn_subset _ _).trans (kset_subset_hatCarrier L D)
    have hbZ := mem_connectedComponentIn hinfK
    have := conn_ray L hZcl hZpre hZX hs hab hbZ (s + 1) (by linarith)
    have hD' := finite_mem_hatSet.1 (connectedComponentIn_subset _ _ this).2
    exact hopen _ (by linarith) hD'
  · intro _
    refine stem_piece_iff L hanchor ?_
    rintro _ ⟨τ, hτ, rfl⟩ hc
    have h1 := stem_circle (hs.trans hτ) hc
    rw [h1, ← anchor_eq_stemPt]; exact hanchor

/-! ### Leaf pieces -/

theorem leaf_circle_iff (L : Lollipop) {D E : Set Point} (hD : IsClosed D)
    (hfree : stemPt L 1 ∉ D) (hE : ∀ x ∈ E, x ∈ L.circle → x = stemPt L 1) :
    L.circle ⊆ D ∪ E ↔ L.circle ⊆ D := by
  have hnc : ¬ L.circle ⊆ D := by
    intro h
    apply hfree
    rw [← anchor_eq_stemPt]
    exact h (Lollipop.anchor_mem_circle L)
  refine iff_of_false ?_ hnc
  intro hsub
  have hpi := Real.pi_pos
  have hIoo : ∀ θ ∈ Ioo 0 (2 * Real.pi), circlePt L θ ∈ D := by
    intro θ hθ
    rcases hsub (HatAux.circlePt_mem_circle L θ) with h | h
    · exact h
    · exfalso
      have h1 := hE _ h (HatAux.circlePt_mem_circle L θ)
      rw [← HatAux.circlePt_zero_eq_stemPt] at h1
      have := HatAux.circlePt_injOn L ⟨hθ.1.le, hθ.2⟩ ⟨le_rfl, by linarith⟩ h1
      linarith [hθ.1]
  have h0 : (0 : ℝ) ∈ closure (Ioo 0 (2 * Real.pi)) := by
    rw [closure_Ioo (by positivity)]
    exact ⟨le_rfl, by linarith⟩
  have := (Set.MapsTo.closure_left (fun θ hθ => hIoo θ hθ) (HatAux.continuous_circlePt L) hD) h0
  apply hfree
  rw [← HatAux.circlePt_zero_eq_stemPt]
  exact this

theorem leaf_seg (L : Lollipop) {D : Set Point} (hD : IsClosed D)
    (hfin : Finite (ConnectedComponents (Kset L D))) {t : ℝ} (ht : 1 < t)
    (hfree : stemPt L 1 ∉ D) (hopen : ∀ τ ∈ Ioo 1 t, stemPt L τ ∉ D) (hend : stemPt L t ∈ D) :
    Finite (ConnectedComponents (Kset L (D ∪ segSet L 1 t))) ∧
      Psi L (D ∪ segSet L 1 t) = Psi L D := by
  have hEc : segSet L 1 t ⊆ L.carrier := by
    rintro _ ⟨τ, hτ, rfl⟩; exact stemPt_mem_carrier L hτ.1
  have hcont : Continuous (fun τ => finitePoint (stemPt L τ)) :=
    HatAux.continuous_finitePoint.comp (continuous_stemPt L)
  have hlift : finiteLift (segSet L 1 t) = (fun τ => finitePoint (stemPt L τ)) '' Icc 1 t := by
    simp [finiteLift, segSet, image_image]
  have hcl : IsClosed (finiteLift (segSet L 1 t)) := by
    rw [hlift]; exact (isCompact_Icc.image hcont).isClosed
  have hcn : IsConnected (finiteLift (segSet L 1 t)) := by
    rw [hlift]; exact (isConnected_Icc ht.le).image _ hcont.continuousOn
  have hbK : finitePoint (stemPt L t) ∈ Kset L D :=
    ⟨(finitePoint_mem_hatCarrier_iff L _).2 (stemPt_mem_carrier L ht.le),
      finite_mem_hatSet.2 hend⟩
  have hbE : finitePoint (stemPt L t) ∈ finiteLift (segSet L 1 t) :=
    ⟨stemPt L t, ⟨t, ⟨ht.le, le_rfl⟩, rfl⟩, rfl⟩
  refine leaf_dichotomy L hD hfin hEc rfl hcl hcn (b := finitePoint (stemPt L t)) ⟨hbK, hbE⟩ ?_ ?_
  · rintro p ⟨hpK, ⟨x, ⟨τ, hτ, rfl⟩, rfl⟩⟩
    have hD' : stemPt L τ ∈ D := finite_mem_hatSet.1 hpK.2
    rcases hτ.1.eq_or_lt with h1 | h1
    · exact absurd (h1 ▸ hD') hfree
    rcases hτ.2.eq_or_lt with h2 | h2
    · rw [h2]; exact mem_singleton _
    · exact absurd hD' (hopen τ ⟨h1, h2⟩)
  · refine leaf_circle_iff L hD hfree ?_
    rintro _ ⟨τ, hτ, rfl⟩ hc
    rw [stem_circle hτ.1 hc]

theorem leaf_ray (L : Lollipop) {D : Set Point} (hD : IsClosed D)
    (hfin : Finite (ConnectedComponents (Kset L D)))
    (hfree : stemPt L 1 ∉ D) (hopen : ∀ τ, 1 < τ → stemPt L τ ∉ D) :
    Finite (ConnectedComponents (Kset L (D ∪ raySet L 1))) ∧
      Psi L (D ∪ raySet L 1) = Psi L D := by
  have hEc : raySet L 1 ⊆ L.carrier := by
    rintro _ ⟨τ, hτ, rfl⟩; exact stemPt_mem_carrier L hτ
  have hcl : IsClosed (hatSet (raySet L 1)) :=
    isClosed_hatSet (IsLeafPiece.ray hfree hopen).isClosed
  have hcn : IsConnected (hatSet (raySet L 1)) :=
    arc_isConnected (HatAux.raySet_isSphereArc L le_rfl)
  have hinfK : infinity ∈ Kset L D := ⟨infinity_mem_hatCarrier L, Or.inr rfl⟩
  have hbE : infinity ∈ hatSet (raySet L 1) := Or.inr rfl
  refine leaf_dichotomy L hD hfin hEc (ray_eq L D _) hcl hcn (b := infinity) ⟨hinfK, hbE⟩ ?_ ?_
  · rintro p ⟨hpK, hpE⟩
    rcases hpE with ⟨x, ⟨τ, hτ, rfl⟩, rfl⟩ | hp
    · exfalso
      have hD' : stemPt L τ ∈ D := finite_mem_hatSet.1 hpK.2
      rcases (show 1 ≤ τ from hτ).eq_or_lt with h1 | h1
      · exact hfree (h1 ▸ hD')
      · exact hopen τ h1 hD'
    · exact hp
  · refine leaf_circle_iff L hD hfree ?_
    rintro _ ⟨τ, hτ, rfl⟩ hc
    rw [stem_circle hτ hc]

end PotAux

theorem gap_potential (L : Lollipop) {D : Set Point} (hD : IsClosed D)
    (hanchor : L.anchor ∈ D) (hfin : Finite (ConnectedComponents (Kset L D)))
    {E : Set Point} (hE : IsGapPiece L D E) :
    Finite (ConnectedComponents (Kset L (D ∪ E))) ∧
      Psi L (D ∪ E) + 1 = Psi L D := by
  have hns := hE.not_subset
  cases hE with
  | circle hαβ hβ hopen hend => exact PotAux.gap_circle L hD hfin hαβ hβ hopen hend hns
  | seg hs hst hopen hend => exact PotAux.gap_seg L hD hanchor hfin hs hst hopen hend
  | ray hs hopen hend => exact PotAux.gap_ray L hD hanchor hfin hs hopen hend

theorem leaf_potential (L : Lollipop) {D : Set Point} (hD : IsClosed D)
    (hfin : Finite (ConnectedComponents (Kset L D))) {E : Set Point}
    (hE : IsLeafPiece L D E) :
    Finite (ConnectedComponents (Kset L (D ∪ E))) ∧ Psi L (D ∪ E) = Psi L D := by
  cases hE with
  | seg ht hfree hopen hend => exact PotAux.leaf_seg L hD hfin ht hfree hopen hend
  | ray hfree hopen => exact PotAux.leaf_ray L hD hfin hfree hopen


end Pieces
end EndToEnd
end Concrete
end Lollipop
