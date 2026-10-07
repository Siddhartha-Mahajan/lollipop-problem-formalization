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
import Lollipop.Topology.Carrier.Zarc
import Lollipop.Topology.Carrier.Core
import Mathlib.Tactic

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace Pieces

open Set

namespace GapSplitAux

/-- Assembly: collars + preconnected `U` + separated germ pieces give exact split data. -/
theorem assemble (L : Lollipop) {D E U S₁ S₂ : Set Point} (hELp : E ⊆ L.carrier)
    (hD : IsClosed D) (hE : IsClosed E)
    {z₀ : Point} (hz₀E : z₀ ∈ E) (hz₀D : z₀ ∉ D)
    (hC : Collars D E S₁ S₂ U) (hUpre : IsPreconnected U)
    (hgerm : ∃ N₁ N₂ : Set Point, N₁ ⊆ S₁ ∧ N₂ ⊆ S₂ ∧ N₁.Nonempty ∧ N₂.Nonempty ∧
      ∀ n₁ ∈ N₁, ∀ n₂ ∈ N₂, n₂ ∉ connectedComponentIn (D ∪ E)ᶜ n₁) :
    Nonempty (ComponentFibers.ExactOneComponentSplitData
      (ComponentSurjectivity.complementSubset
        (LocalInsertion.old_subset_carrierExtension D E))) := by
  have hUD : U ⊆ Dᶜ := hC.U_sub
  have hz₀U : z₀ ∈ U := hC.new_sub z₀ hz₀E hz₀D
  have hUO : U ⊆ connectedComponentIn Dᶜ z₀ := hUpre.subset_connectedComponentIn hz₀U hUD
  have hS₁K : S₁ ⊆ (D ∪ E)ᶜ := fun x hx h => by
    rcases h with h | h
    · exact hUD (hC.sub₁ hx).1 h
    · exact (hC.sub₁ hx).2 h
  have hS₂K : S₂ ⊆ (D ∪ E)ᶜ := fun x hx h => by
    rcases h with h | h
    · exact hUD (hC.sub₂ hx).1 h
    · exact (hC.sub₂ hx).2 h
  have hS₁O : S₁ ⊆ connectedComponentIn Dᶜ z₀ := fun x hx => hUO (hC.sub₁ hx).1
  have hS₂O : S₂ ⊆ connectedComponentIn Dᶜ z₀ := fun x hx => hUO (hC.sub₂ hx).1
  have hloc : ∀ z ∈ E, z ∉ D → z ∈ connectedComponentIn Dᶜ z₀ :=
    fun z hzE hzD => hUO (hC.new_sub z hzE hzD)
  have hEU : ∀ z ∈ E, z ∈ connectedComponentIn Dᶜ z₀ → z ∈ U :=
    fun z hzE hzO => hC.new_sub z hzE (connectedComponentIn_subset Dᶜ z₀ hzO)
  have hcover : ∀ x ∈ U, x ∈ connectedComponentIn Dᶜ z₀ → x ∉ E → x ∈ S₁ ∨ x ∈ S₂ :=
    fun x hxU _ hxE => hC.cover x hxU hxE
  obtain ⟨N₁, N₂, hN₁S, hN₂S, ⟨n₁, hn₁⟩, ⟨n₂, hn₂⟩, hsepN⟩ := hgerm
  have hsep' : ∀ (s s' : Point) (hs : s ∈ S₁) (hs' : s' ∈ S₂),
      ConnectedComponents.mk
        (⟨s, hS₁K hs⟩ : ((LocalInsertion.carrierExtension D E)ᶜ : Set Point)) ≠
      ConnectedComponents.mk
        (⟨s', hS₂K hs'⟩ : ((LocalInsertion.carrierExtension D E)ᶜ : Set Point)) := by
    intro s s' hs hs' heq
    have h1 := ComponentLifting.mem_connectedComponentIn_of_connectedComponents_mk_eq _ _ heq
    -- h1 : s' ∈ connectedComponentIn (D ∪ E)ᶜ s
    have h2 : n₁ ∈ connectedComponentIn (D ∪ E)ᶜ s :=
      (hC.pre₁.subset_connectedComponentIn hs hS₁K) (hN₁S hn₁)
    have h3 : n₂ ∈ connectedComponentIn (D ∪ E)ᶜ s' :=
      (hC.pre₂.subset_connectedComponentIn hs' hS₂K) (hN₂S hn₂)
    have h4 : connectedComponentIn (D ∪ E)ᶜ s' = connectedComponentIn (D ∪ E)ᶜ s :=
      (connectedComponentIn_eq h1).symm
    have h5 : connectedComponentIn (D ∪ E)ᶜ n₁ = connectedComponentIn (D ∪ E)ᶜ s :=
      (connectedComponentIn_eq h2).symm
    apply hsepN n₁ hn₁ n₂ hn₂
    rw [h5, ← h4]
    exact h3
  have hs₁ : n₁ ∈ S₁ := hN₁S hn₁
  have hs₂ : n₂ ∈ S₂ := hN₂S hn₂
  exact ⟨LocalInsertion.exactOneComponentSplitDataOfLocalizedEdge hD L hELp _
    (Collar.localizedExactEdgeStepOfCollars L hELp hD hE hz₀E hz₀D hloc hC.isOpen_U hEU
      hC.pre₁ hC.pre₂ hS₁K hS₂K hS₁O hS₂O hcover hs₁ hs₂ (hsep' _ _ hs₁ hs₂) hsep').localized
    (Collar.localizedExactEdgeStepOfCollars L hELp hD hE hz₀E hz₀D hloc hC.isOpen_U hEU
      hC.pre₁ hC.pre₂ hS₁K hS₂K hS₁O hS₂O hcover hs₁ hs₂ (hsep' _ _ hs₁ hs₂) hsep').activeClassifier
    (Collar.localizedExactEdgeStepOfCollars L hELp hD hE hz₀E hz₀D hloc hC.isOpen_U hEU
      hC.pre₁ hC.pre₂ hS₁K hS₂K hS₁O hS₂O hcover hs₁ hs₂ (hsep' _ _ hs₁ hs₂) hsep').active_injective
    (Collar.localizedExactEdgeStepOfCollars L hELp hD hE hz₀E hz₀D hloc hC.isOpen_U hEU
      hC.pre₁ hC.pre₂ hS₁K hS₂K hS₁O hS₂O hcover hs₁ hs₂ (hsep' _ _ hs₁ hs₂) hsep').active_surjective⟩



/-- Germ with the extra information `N₁ ⊆ N`, `N₂ ⊆ N`. -/
structure Germ' (E S₁ S₂ U γ : Set Point) : Prop where
  ex : ∃ N N₁ N₂ : Set Point, IsOpen N ∧ N ⊆ U ∧ N ∩ E = γ ∧
    IsPreconnected N₁ ∧ IsPreconnected N₂ ∧ N₁.Nonempty ∧ N₂.Nonempty ∧
    N₁ ⊆ S₁ ∧ N₂ ⊆ S₂ ∧ N \ E ⊆ N₁ ∪ N₂ ∧ N₁ ⊆ N ∧ N₂ ⊆ N

section CircleSec
open CircleAux

theorem circle_collars' (L : Lollipop) {D : Set Point} (hD : IsClosed D)
    {α β : ℝ} (hαβ : α < β) (hβ : β ≤ α + 2 * Real.pi)
    (hopen : ∀ θ ∈ Ioo α β, circlePt L θ ∉ D)
    (hend : circlePt L α ∈ D ∧ circlePt L β ∈ D) :
    ∃ U S₁ S₂ : Set Point, IsPreconnected U ∧
      Collars D (circleArcSet L α β) S₁ S₂ U ∧
      ∀ θ₀ ∈ Ioo α β, ∀ δ : ℝ, 0 < δ → Icc (θ₀ - δ) (θ₀ + δ) ⊆ Ioo α β →
        Germ' (circleArcSet L α β) S₁ S₂ U (circlePt L '' Ioo (θ₀ - δ) (θ₀ + δ)) := by
  obtain ⟨w, hw, hwle, hwpos, hwdist⟩ := exists_width L hD hopen
  have hΩ : IsOpen (Ioo α β ×ˢ Ioo (-1 : ℝ) 1) := isOpen_Ioo.prod isOpen_Ioo
  have hmid : (α + β) / 2 ∈ Ioo α β := ⟨by linarith, by linarith⟩
  refine ⟨tube L w '' (Ioo α β ×ˢ Ioo (-1 : ℝ) 1),
    tube L w '' (Ioo α β ×ˢ Ioo (-1 : ℝ) 0), tube L w '' (Ioo α β ×ˢ Ioo (0 : ℝ) 1), preconnected_tube_image L hw, ?_, ?_⟩
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
      image_mono (prod_mono hI subset_rfl), image_mono (prod_mono hI subset_rfl), ?_,
      image_mono (prod_mono subset_rfl (Ioo_subset_Ioo_right (by norm_num))),
      image_mono (prod_mono subset_rfl (Ioo_subset_Ioo_left (by norm_num)))⟩
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


end CircleSec

section StemSec
open StemAux

theorem stemTube_collars' (L : Lollipop) {D : Set Point} (hD : IsClosed D) (E : Set Point)
    (I : Set ℝ) (hIo : IsOpen I) (hIc : I.OrdConnected) (hIne : I.Nonempty)
    (hIE : ∀ τ ∈ I, stemPt L τ ∈ E) (hline : ∀ z ∈ E, ∃ τ, z = stemPt L τ)
    (hnew : ∀ z ∈ E, z ∉ D → ∃ τ ∈ I, z = stemPt L τ)
    (hID : ∀ τ ∈ I, stemPt L τ ∉ D) :
    ∃ U S₁ S₂ : Set Point, IsPreconnected U ∧ Collars D E S₁ S₂ U ∧
      ∀ J : Set ℝ, IsOpen J → J.OrdConnected → J.Nonempty → J ⊆ I →
        Germ' E S₁ S₂ U (stemPt L '' J) := by
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
    tubeMap L w '' (I ×ˢ Ioo (0 : ℝ) 1), hpre _ _ hIc ordConnected_Ioo, ?_, ?_⟩
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
      hmono _ _ _ _ hJI subset_rfl, ?_, hmono _ _ _ _ subset_rfl h01,
      hmono _ _ _ _ subset_rfl h02⟩
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

theorem seg_collars' (L : Lollipop) {D : Set Point} (hD : IsClosed D)
    {s t : ℝ} (hs : 1 ≤ s) (hst : s < t)
    (hopen : ∀ τ ∈ Ioo s t, stemPt L τ ∉ D)
    (hend : stemPt L s ∈ D ∧ stemPt L t ∈ D) :
    ∃ U S₁ S₂ : Set Point, IsPreconnected U ∧
      Collars D (segSet L s t) S₁ S₂ U ∧
      ∀ τ₀ ∈ Ioo s t, ∀ δ : ℝ, 0 < δ → Icc (τ₀ - δ) (τ₀ + δ) ⊆ Ioo s t →
        Germ' (segSet L s t) S₁ S₂ U (stemPt L '' Ioo (τ₀ - δ) (τ₀ + δ)) := by
  obtain ⟨U, S₁, S₂, hU, hC, hG⟩ := stemTube_collars' L hD (segSet L s t) (Ioo s t) isOpen_Ioo
    ordConnected_Ioo ⟨(s + t) / 2, by constructor <;> linarith⟩
    (fun τ hτ => ⟨τ, Ioo_subset_Icc_self hτ, rfl⟩)
    (fun z hz => by obtain ⟨τ, _, rfl⟩ := hz; exact ⟨τ, rfl⟩)
    (by
      rintro z ⟨τ, hτ, rfl⟩ hzD
      refine ⟨τ, ⟨lt_of_le_of_ne hτ.1 ?_, lt_of_le_of_ne hτ.2 ?_⟩, rfl⟩
      · rintro rfl; exact hzD hend.1
      · rintro rfl; exact hzD hend.2)
    hopen
  refine ⟨U, S₁, S₂, hU, hC, ?_⟩
  intro τ₀ hτ₀ δ hδ hsub
  exact hG _ isOpen_Ioo ordConnected_Ioo ⟨τ₀, by constructor <;> linarith⟩
    (fun x hx => hsub ⟨hx.1.le, hx.2.le⟩)

theorem ray_collars' (L : Lollipop) {D : Set Point} (hD : IsClosed D)
    {s : ℝ} (hs : 1 ≤ s)
    (hopen : ∀ τ, s < τ → stemPt L τ ∉ D)
    (hend : stemPt L s ∈ D) :
    ∃ U S₁ S₂ : Set Point, IsPreconnected U ∧
      Collars D (raySet L s) S₁ S₂ U ∧
      ∀ τ₀, s < τ₀ → ∀ δ : ℝ, 0 < δ → s < τ₀ - δ →
        Germ' (raySet L s) S₁ S₂ U (stemPt L '' Ioo (τ₀ - δ) (τ₀ + δ)) := by
  obtain ⟨U, S₁, S₂, hU, hC, hG⟩ := stemTube_collars' L hD (raySet L s) (Ioi s) isOpen_Ioi
    ordConnected_Ioi ⟨s + 1, by simp⟩
    (fun τ hτ => ⟨τ, Ioi_subset_Ici_self hτ, rfl⟩)
    (fun z hz => by obtain ⟨τ, _, rfl⟩ := hz; exact ⟨τ, rfl⟩)
    (by
      rintro z ⟨τ, hτ, rfl⟩ hzD
      refine ⟨τ, (show s < τ from lt_of_le_of_ne hτ ?_), rfl⟩
      rintro rfl; exact hzD hend)
    (fun τ hτ => hopen τ hτ)
  refine ⟨U, S₁, S₂, hU, hC, ?_⟩
  intro τ₀ hτ₀ δ hδ hsub
  exact hG _ isOpen_Ioo ordConnected_Ioo ⟨τ₀, by constructor <;> linarith⟩
    (fun x hx => lt_trans hsub hx.1)


end StemSec



/-! ### Lifting helpers -/

lemma lift_inter {φ : ℝ → Point} {T S₁ S₂ : Set ℝ} (hinj : InjOn φ T) (h1 : S₁ ⊆ T)
    (h2 : S₂ ⊆ T) :
    finiteLift (φ '' S₁) ∩ finiteLift (φ '' S₂) = finiteLift (φ '' (S₁ ∩ S₂)) := by
  unfold finiteLift
  rw [← Set.image_inter finitePoint_injective, ← hinj.image_inter h1 h2]

lemma lift_diff_pair (S : Set Point) (x y : Point) :
    finiteLift S \ {finitePoint x, finitePoint y} = finiteLift (S \ {x, y}) := by
  unfold finiteLift
  rw [Set.image_diff finitePoint_injective, Set.image_pair]

lemma lift_union (S T : Set Point) : finiteLift (S ∪ T) = finiteLift S ∪ finiteLift T := by
  unfold finiteLift; rw [Set.image_union]

lemma lift_inter' (S T : Set Point) : finiteLift S ∩ finiteLift T = finiteLift (S ∩ T) := by
  unfold finiteLift; rw [Set.image_inter finitePoint_injective]

lemma setOf_lift (S : Set Point) : {x | finitePoint x ∈ finiteLift S} = S := by
  ext x; simp

lemma setOf_lift_inf (S : Set Point) : {x | finitePoint x ∈ finiteLift S ∪ {infinity}} = S := by
  ext x; simp

lemma image_diff_pair {φ : ℝ → Point} {T : Set ℝ} (hinj : InjOn φ T) {p q : ℝ}
    (hpq : p ≤ q) (hT : Icc p q ⊆ T) :
    φ '' Icc p q \ {φ p, φ q} = φ '' Ioo p q := by
  ext x
  constructor
  · rintro ⟨⟨θ, hθ, rfl⟩, hx⟩
    have h1 : θ ≠ p := by
      rintro rfl; exact hx (Or.inl rfl)
    have h2 : θ ≠ q := by
      rintro rfl; exact hx (Or.inr rfl)
    exact ⟨θ, ⟨lt_of_le_of_ne hθ.1 (Ne.symm h1), lt_of_le_of_ne hθ.2 h2⟩, rfl⟩
  · rintro ⟨θ, hθ, rfl⟩
    refine ⟨⟨θ, Ioo_subset_Icc_self hθ, rfl⟩, ?_⟩
    rintro (h | h)
    · have := hinj (hT (Ioo_subset_Icc_self hθ)) (hT ⟨le_rfl, hpq⟩) h
      linarith [hθ.1]
    · have := hinj (hT (Ioo_subset_Icc_self hθ)) (hT ⟨hpq, le_rfl⟩) h
      linarith [hθ.2]

/-! ### Arc core: finite arcs -/

theorem arc_core {D : Set Point} (hD : IsClosed D) (hArc : ArcConn D) {M : Lollipop}
    (hM : M.circle ⊆ D) {φ : ℝ → Point} {a p q b : ℝ} (hap : a < p) (hpq : p < q)
    (hqb : q < b) (hinj : InjOn φ (Icc a b))
    (hA₁ : IsSphereArc (finiteLift (φ '' Icc a p)) (finitePoint (φ a)) (finitePoint (φ p)))
    (hG : IsSphereArc (finiteLift (φ '' Icc p q)) (finitePoint (φ p)) (finitePoint (φ q)))
    (hA₂ : IsSphereArc (finiteLift (φ '' Icc q b)) (finitePoint (φ q)) (finitePoint (φ b)))
    (hopen : ∀ θ ∈ Ioo a b, φ θ ∉ D) (hend : φ a ∈ D ∧ φ b ∈ D)
    {N N₁ N₂ : Set Point} (hN : IsOpen N) (hND : N ⊆ Dᶜ)
    (hNE : N ∩ φ '' Icc a b = φ '' Ioo p q)
    (hN₁ : IsPreconnected N₁) (hN₂ : IsPreconnected N₂)
    (hne₁ : N₁.Nonempty) (hne₂ : N₂.Nonempty) (hN₁N : N₁ ⊆ N) (hN₂N : N₂ ⊆ N)
    (hN₁E : ∀ x ∈ N₁, x ∉ φ '' Icc a b) (hN₂E : ∀ x ∈ N₂, x ∉ φ '' Icc a b)
    (hcov : ∀ x ∈ N, x ∉ φ '' Icc a b → x ∈ N₁ ∨ x ∈ N₂) :
    ∀ n₁ ∈ N₁, ∀ n₂ ∈ N₂, n₂ ∉ connectedComponentIn (D ∪ φ '' Icc a b)ᶜ n₁ := by
  have hsub1 : Icc a p ⊆ Icc a b := Icc_subset_Icc le_rfl (by linarith)
  have hsub2 : Icc p q ⊆ Icc a b := Icc_subset_Icc (by linarith) (by linarith)
  have hsub3 : Icc q b ⊆ Icc a b := Icc_subset_Icc (by linarith) le_rfl
  have hab : finitePoint (φ a) ≠ finitePoint (φ b) := by
    intro h
    have := hinj ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (finitePoint_injective h)
    linarith
  have hI : Icc a p ∪ Icc p q ∪ Icc q b = Icc a b := by
    rw [Icc_union_Icc_eq_Icc hap.le hpq.le, Icc_union_Icc_eq_Icc (by linarith) hqb.le]
  have hEhat : finiteLift (φ '' Icc a b) =
      finiteLift (φ '' Icc a p) ∪ finiteLift (φ '' Icc p q) ∪ finiteLift (φ '' Icc q b) := by
    have : φ '' Icc a b = φ '' Icc a p ∪ φ '' Icc p q ∪ φ '' Icc q b := by
      rw [← hI]; simp only [Set.image_union]
    rw [this, lift_union, lift_union]
  have hA₁G : finiteLift (φ '' Icc a p) ∩ finiteLift (φ '' Icc p q) = {finitePoint (φ p)} := by
    rw [lift_inter hinj hsub1 hsub2]
    have : Icc a p ∩ Icc p q = {p} := by
      rw [Icc_inter_Icc, max_eq_right hap.le, min_eq_left hpq.le, Icc_self]
    rw [this]; simp [finiteLift]
  have hGA₂ : finiteLift (φ '' Icc p q) ∩ finiteLift (φ '' Icc q b) = {finitePoint (φ q)} := by
    rw [lift_inter hinj hsub2 hsub3]
    have : Icc p q ∩ Icc q b = {q} := by
      rw [Icc_inter_Icc, max_eq_right hpq.le, min_eq_left hqb.le, Icc_self]
    rw [this]; simp [finiteLift]
  have hA₁A₂ : finiteLift (φ '' Icc a p) ∩ finiteLift (φ '' Icc q b) = ∅ := by
    rw [lift_inter hinj hsub1 hsub3]
    have : Icc a p ∩ Icc q b = ∅ := by
      rw [Icc_inter_Icc, Icc_eq_empty]
      rw [max_eq_right (by linarith), min_eq_left (by linarith)]
      linarith
    rw [this]; simp [finiteLift]
  have hED : finiteLift (φ '' Icc a b) ∩ hatSet D = {finitePoint (φ a), finitePoint (φ b)} := by
    ext x
    constructor
    · rintro ⟨⟨y, ⟨θ, hθ, rfl⟩, rfl⟩, hxD⟩
      rcases hxD with hxD | hxD
      · have hφD : φ θ ∈ D := mem_finiteLift_iff.mp hxD
        by_cases hθa : θ = a
        · left; simp [hθa]
        by_cases hθb : θ = b
        · right; simp [hθb]
        exact absurd hφD (hopen θ ⟨lt_of_le_of_ne hθ.1 (Ne.symm hθa),
          lt_of_le_of_ne hθ.2 hθb⟩)
      · exact absurd hxD (finitePoint_ne_infinity _)
    · rintro (rfl | rfl)
      · exact ⟨⟨φ a, ⟨a, ⟨le_rfl, by linarith⟩, rfl⟩, rfl⟩, Or.inl ⟨_, hend.1, rfl⟩⟩
      · exact ⟨⟨φ b, ⟨b, ⟨by linarith, le_rfl⟩, rfl⟩, rfl⟩, Or.inl ⟨_, hend.2, rfl⟩⟩
  have hNE' : finiteLift N ∩ finiteLift (φ '' Icc a b) =
      finiteLift (φ '' Icc p q) \ {finitePoint (φ p), finitePoint (φ q)} := by
    rw [lift_inter', hNE, lift_diff_pair, image_diff_pair hinj hpq.le hsub2]
  have key := exact_sides_core (D := D) hD hArc hM
    (Ehat := finiteLift (φ '' Icc a b)) hA₁ hG hA₂ hab hEhat hA₁G hGA₂ hA₁A₂ hED hN hND hNE'
    hN₁ hN₂ hne₁ hne₂ hN₁N hN₂N (fun x hx h => hN₁E x hx (mem_finiteLift_iff.mp h))
    (fun x hx h => hN₂E x hx (mem_finiteLift_iff.mp h))
    (fun x hx hxE => hcov x hx (fun h => hxE (mem_finiteLift_iff.mpr h)))
  rw [setOf_lift] at key
  exact key

/-! ### Ray core -/

theorem ray_core (L : Lollipop) {D : Set Point} (hD : IsClosed D) (hArc : ArcConn D)
    {M : Lollipop} (hM : M.circle ⊆ D) {s p q : ℝ} (hs : 1 ≤ s) (hsp : s < p) (hpq : p < q)
    (hopen : ∀ τ, s < τ → stemPt L τ ∉ D) (hend : stemPt L s ∈ D)
    {N N₁ N₂ : Set Point} (hN : IsOpen N) (hND : N ⊆ Dᶜ)
    (hNE : N ∩ raySet L s = stemPt L '' Ioo p q)
    (hN₁ : IsPreconnected N₁) (hN₂ : IsPreconnected N₂)
    (hne₁ : N₁.Nonempty) (hne₂ : N₂.Nonempty) (hN₁N : N₁ ⊆ N) (hN₂N : N₂ ⊆ N)
    (hN₁E : ∀ x ∈ N₁, x ∉ raySet L s) (hN₂E : ∀ x ∈ N₂, x ∉ raySet L s)
    (hcov : ∀ x ∈ N, x ∉ raySet L s → x ∈ N₁ ∨ x ∈ N₂) :
    ∀ n₁ ∈ N₁, ∀ n₂ ∈ N₂, n₂ ∉ connectedComponentIn (D ∪ raySet L s)ᶜ n₁ := by
  have hinj : InjOn (stemPt L) univ := (HatAux.stemPt_injective L).injOn
  have hq1 : 1 ≤ q := by linarith
  have hp1 : 1 ≤ p := by linarith
  have hA₁ := segSubArc L hs hsp
  have hG := segSubArc L hp1 hpq
  have hA₂ := raySet_isSphereArc L hq1
  have hab : finitePoint (stemPt L s) ≠ infinity := finitePoint_ne_infinity _
  have hray : raySet L s = segSet L s p ∪ segSet L p q ∪ raySet L q := by
    unfold raySet segSet
    rw [← Set.image_union, ← Set.image_union, Icc_union_Icc_eq_Icc hsp.le hpq.le,
      Icc_union_Ici_eq_Ici (by linarith)]
  have hEhat : finiteLift (raySet L s) ∪ {infinity} =
      finiteLift (segSet L s p) ∪ finiteLift (segSet L p q) ∪
        (finiteLift (raySet L q) ∪ {infinity}) := by
    rw [hray, lift_union, lift_union]
    ext x; simp only [mem_union, mem_singleton_iff]; tauto
  have hA₁G : finiteLift (segSet L s p) ∩ finiteLift (segSet L p q) =
      {finitePoint (stemPt L p)} := by
    unfold segSet
    rw [lift_inter hinj (subset_univ _) (subset_univ _)]
    have : Icc s p ∩ Icc p q = {p} := by
      rw [Icc_inter_Icc, max_eq_right hsp.le, min_eq_left hpq.le, Icc_self]
    rw [this]; simp [finiteLift]
  have hGR : finiteLift (segSet L p q) ∩ finiteLift (raySet L q) = {finitePoint (stemPt L q)} := by
    unfold segSet raySet
    rw [lift_inter hinj (subset_univ _) (subset_univ _)]
    have : Icc p q ∩ Ici q = {q} := by
      ext x; simp only [mem_inter_iff, mem_Icc, mem_Ici, mem_singleton_iff]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩; linarith
      · rintro rfl; exact ⟨⟨hpq.le, le_rfl⟩, le_rfl⟩
    rw [this]; simp [finiteLift]
  have hGA₂ : finiteLift (segSet L p q) ∩ (finiteLift (raySet L q) ∪ {infinity}) =
      {finitePoint (stemPt L q)} := by
    rw [inter_union_distrib_left, hGR, (inter_singleton_eq_empty.mpr
      (infinity_not_mem_finiteLift _)), union_empty]
  have hA₁R : finiteLift (segSet L s p) ∩ finiteLift (raySet L q) = ∅ := by
    unfold segSet raySet
    rw [lift_inter hinj (subset_univ _) (subset_univ _)]
    have : Icc s p ∩ Ici q = ∅ := by
      ext x; simp only [mem_inter_iff, mem_Icc, mem_Ici, mem_empty_iff_false, iff_false]
      rintro ⟨⟨_, h2⟩, h3⟩; linarith
    rw [this]; simp [finiteLift]
  have hA₁A₂ : finiteLift (segSet L s p) ∩ (finiteLift (raySet L q) ∪ {infinity}) = ∅ := by
    rw [inter_union_distrib_left, hA₁R, (inter_singleton_eq_empty.mpr
      (infinity_not_mem_finiteLift _)), union_empty]
  have hED : (finiteLift (raySet L s) ∪ {infinity}) ∩ hatSet D =
      {finitePoint (stemPt L s), infinity} := by
    ext x
    constructor
    · rintro ⟨hxE, hxD⟩
      rcases hxE with ⟨y, ⟨τ, hτ, rfl⟩, rfl⟩ | hx
      · rcases hxD with hxD | hxD
        · have hφD : stemPt L τ ∈ D := mem_finiteLift_iff.mp hxD
          by_cases hτs : τ = s
          · left; simp [hτs]
          · exact absurd hφD (hopen τ (lt_of_le_of_ne hτ (Ne.symm hτs)))
        · exact absurd hxD (finitePoint_ne_infinity _)
      · right; exact hx
    · rintro (rfl | rfl)
      · exact ⟨Or.inl ⟨_, ⟨s, Set.mem_Ici.mpr le_rfl, rfl⟩, rfl⟩, Or.inl ⟨_, hend, rfl⟩⟩
      · exact ⟨Or.inr rfl, Or.inr rfl⟩
  have hNE' : finiteLift N ∩ (finiteLift (raySet L s) ∪ {infinity}) =
      finiteLift (segSet L p q) \ {finitePoint (stemPt L p), finitePoint (stemPt L q)} := by
    rw [inter_union_distrib_left, lift_inter', hNE, inter_singleton_eq_empty.mpr
      (infinity_not_mem_finiteLift _), union_empty, lift_diff_pair]
    unfold segSet
    rw [image_diff_pair hinj hpq.le (subset_univ _)]
  have key := exact_sides_core (D := D) hD hArc hM
    (Ehat := finiteLift (raySet L s) ∪ {infinity}) hA₁ hG hA₂ hab hEhat hA₁G hGA₂ hA₁A₂ hED
    hN hND hNE' hN₁ hN₂ hne₁ hne₂ hN₁N hN₂N
    (fun x hx h => hN₁E x hx (by simpa using h))
    (fun x hx h => hN₂E x hx (by simpa using h))
    (fun x hx hxE => hcov x hx (fun h => hxE (by simpa using h)))
  rw [setOf_lift_inf] at key
  exact key


/-! ### Circle periodicity helpers -/

lemma circlePt_sub_int_mul (L : Lollipop) (n : ℤ) (θ : ℝ) :
    circlePt L (θ - n * (2 * Real.pi)) = circlePt L θ := by
  unfold circlePt
  rw [Real.cos_sub_int_mul_two_pi, Real.sin_sub_int_mul_two_pi]

lemma circlePt_add_two_pi (L : Lollipop) (θ : ℝ) :
    circlePt L (θ + 2 * Real.pi) = circlePt L θ := by
  unfold circlePt
  rw [Real.cos_add_two_pi, Real.sin_add_two_pi]

lemma circlePt_sub_two_pi (L : Lollipop) (θ : ℝ) :
    circlePt L (θ - 2 * Real.pi) = circlePt L θ := by
  have := circlePt_add_two_pi L (θ - 2 * Real.pi)
  rw [sub_add_cancel] at this
  exact this.symm

lemma circlePt_toIcoMod (L : Lollipop) (x y : ℝ) :
    circlePt L (toIcoMod Real.two_pi_pos x y) = circlePt L y := by
  have h := self_sub_toIcoMod Real.two_pi_pos x y
  rw [zsmul_eq_mul] at h
  have : toIcoMod Real.two_pi_pos x y = y - (toIcoDiv Real.two_pi_pos x y : ℝ) * (2 * Real.pi) := by
    linarith
  rw [this, circlePt_sub_int_mul]

lemma circlePt_injOn_Ico (L : Lollipop) (x : ℝ) :
    InjOn (circlePt L) (Ico x (x + 2 * Real.pi)) := by
  intro θ₁ h₁ θ₂ h₂ heq
  have hr₁ := toIcoMod_mem_Ico Real.two_pi_pos 0 θ₁
  have hr₂ := toIcoMod_mem_Ico Real.two_pi_pos 0 θ₂
  simp only [zero_add] at hr₁ hr₂
  have hr : toIcoMod Real.two_pi_pos 0 θ₁ = toIcoMod Real.two_pi_pos 0 θ₂ := by
    apply HatAux.circlePt_injOn L hr₁ hr₂
    rw [circlePt_toIcoMod, circlePt_toIcoMod]; exact heq
  obtain ⟨n, hn⟩ := (toIcoMod_eq_toIcoMod Real.two_pi_pos).mp hr
  rw [zsmul_eq_mul] at hn
  have hpi := Real.pi_pos
  have hn1 : (n : ℝ) < 1 := by
    by_contra h
    push Not at h
    nlinarith [h₁.1, h₁.2, h₂.1, h₂.2]
  have hn2 : (-1 : ℝ) < n := by
    by_contra h
    push Not at h
    nlinarith [h₁.1, h₁.2, h₂.1, h₂.2]
  have hn1' : n < 1 := by exact_mod_cast hn1
  have hn2' : -1 < n := by exact_mod_cast hn2
  have : n = 0 := by omega
  subst this
  simp at hn
  linarith

/-! ### Loop core -/

theorem loop_core (L : Lollipop) {D : Set Point} (hD : IsClosed D) {M : Lollipop}
    (hM : M.circle ⊆ D) {α p q : ℝ} (hαp : α < p) (hpq : p < q) (hqα : q < α + 2 * Real.pi)
    (hopen : ∀ θ ∈ Ioo α (α + 2 * Real.pi), circlePt L θ ∉ D) (hend : circlePt L α ∈ D)
    {N N₁ N₂ : Set Point} (hN : IsOpen N) (hND : N ⊆ Dᶜ)
    (hNE : N ∩ circleArcSet L α (α + 2 * Real.pi) = circlePt L '' Ioo p q)
    (hN₁ : IsPreconnected N₁) (hN₂ : IsPreconnected N₂)
    (hne₁ : N₁.Nonempty) (hne₂ : N₂.Nonempty) (hN₁N : N₁ ⊆ N) (hN₂N : N₂ ⊆ N)
    (hN₁E : ∀ x ∈ N₁, x ∉ circleArcSet L α (α + 2 * Real.pi))
    (hN₂E : ∀ x ∈ N₂, x ∉ circleArcSet L α (α + 2 * Real.pi))
    (hcov : ∀ x ∈ N, x ∉ circleArcSet L α (α + 2 * Real.pi) → x ∈ N₁ ∨ x ∈ N₂) :
    ∀ n₁ ∈ N₁, ∀ n₂ ∈ N₂,
      n₂ ∉ connectedComponentIn (D ∪ circleArcSet L α (α + 2 * Real.pi))ᶜ n₁ := by
  have hpi := Real.pi_pos
  have hinjw : InjOn (circlePt L) (Ico p (p + 2 * Real.pi)) := circlePt_injOn_Ico L p
  have hG : IsSphereArc (finiteLift (circlePt L '' Icc p q))
      (finitePoint (circlePt L p)) (finitePoint (circlePt L q)) :=
    circleSubArc L hpq (by linarith)
  have hR0 : IsSphereArc (finiteLift (circlePt L '' Icc q (p + 2 * Real.pi)))
      (finitePoint (circlePt L q)) (finitePoint (circlePt L (p + 2 * Real.pi))) :=
    circleSubArc L (x := q) (y := p + 2 * Real.pi) (by linarith) (by linarith)
  have hR : IsSphereArc (finiteLift (circlePt L '' Icc q (p + 2 * Real.pi)))
      (finitePoint (circlePt L p)) (finitePoint (circlePt L q)) := by
    have := hR0.symm
    rwa [circlePt_add_two_pi] at this
  have huv : finitePoint (circlePt L p) ≠ finitePoint (circlePt L q) := by
    intro h
    have := hinjw ⟨le_rfl, by linarith⟩ ⟨hpq.le, by linarith⟩ (finitePoint_injective h)
    linarith
  have hEset : circlePt L '' Icc α (α + 2 * Real.pi) =
      circlePt L '' Icc p q ∪ circlePt L '' Icc q (p + 2 * Real.pi) := by
    ext x
    constructor
    · rintro ⟨θ, hθ, rfl⟩
      rcases lt_or_ge θ p with h | h
      · right
        exact ⟨θ + 2 * Real.pi, ⟨by linarith [hθ.1], by linarith⟩, circlePt_add_two_pi L θ⟩
      · rcases le_or_gt θ q with h' | h'
        · left; exact ⟨θ, ⟨h, h'⟩, rfl⟩
        · right; exact ⟨θ, ⟨h'.le, by linarith [hθ.2]⟩, rfl⟩
    · rintro (⟨θ, hθ, rfl⟩ | ⟨θ, hθ, rfl⟩)
      · exact ⟨θ, ⟨by linarith [hθ.1], by linarith [hθ.2]⟩, rfl⟩
      · by_cases h : θ ≤ α + 2 * Real.pi
        · exact ⟨θ, ⟨by linarith [hθ.1], h⟩, rfl⟩
        · push Not at h
          exact ⟨θ - 2 * Real.pi, ⟨by linarith, by linarith [hθ.2]⟩, circlePt_sub_two_pi L θ⟩
  have hEhat : finiteLift (circlePt L '' Icc α (α + 2 * Real.pi)) =
      finiteLift (circlePt L '' Icc p q) ∪ finiteLift (circlePt L '' Icc q (p + 2 * Real.pi)) := by
    rw [hEset, lift_union]
  have hGR : finiteLift (circlePt L '' Icc p q) ∩ finiteLift (circlePt L '' Icc q (p + 2 * Real.pi)) =
      {finitePoint (circlePt L p), finitePoint (circlePt L q)} := by
    ext x
    simp only [mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨⟨y, ⟨θ, hθ, rfl⟩, rfl⟩, ⟨y', ⟨ψ, hψ, rfl⟩, hy⟩⟩
      have hy' := finitePoint_injective hy
      by_cases hψe : ψ = p + 2 * Real.pi
      · left
        rw [← hy', hψe, circlePt_add_two_pi]
      · right
        have hψlt : ψ < p + 2 * Real.pi := lt_of_le_of_ne hψ.2 hψe
        have := hinjw ⟨by linarith [hψ.1], hψlt⟩ ⟨hθ.1, by linarith [hθ.2]⟩ hy'
        have hθq : θ = q := by linarith [hθ.2, hψ.1]
        rw [hθq]
    · rintro (rfl | rfl)
      · exact ⟨⟨_, ⟨p, ⟨le_rfl, hpq.le⟩, rfl⟩, rfl⟩,
          ⟨_, ⟨p + 2 * Real.pi, ⟨by linarith, le_rfl⟩, rfl⟩, by rw [circlePt_add_two_pi]⟩⟩
      · exact ⟨⟨_, ⟨q, ⟨hpq.le, le_rfl⟩, rfl⟩, rfl⟩,
          ⟨_, ⟨q, ⟨le_rfl, by linarith⟩, rfl⟩, rfl⟩⟩
  have hED : finiteLift (circlePt L '' Icc α (α + 2 * Real.pi)) ∩ hatSet D =
      {finitePoint (circlePt L α)} := by
    ext x
    rw [mem_singleton_iff]
    constructor
    · rintro ⟨⟨y, ⟨θ, hθ, rfl⟩, rfl⟩, hxD⟩
      rcases hxD with hxD | hxD
      · have hφD := mem_finiteLift_iff.mp hxD
        have hθα : θ = α ∨ θ = α + 2 * Real.pi := by
          by_contra h
          push Not at h
          exact hopen θ ⟨lt_of_le_of_ne hθ.1 (Ne.symm h.1), lt_of_le_of_ne hθ.2 h.2⟩ hφD
        rcases hθα with h | h
        · rw [h]
        · rw [h, circlePt_add_two_pi]
      · exact absurd hxD (finitePoint_ne_infinity _)
    · intro hx
      subst hx
      exact ⟨⟨_, ⟨α, ⟨le_rfl, by linarith⟩, rfl⟩, rfl⟩, Or.inl ⟨_, hend, rfl⟩⟩
  have hNE' : finiteLift N ∩ finiteLift (circlePt L '' Icc α (α + 2 * Real.pi)) =
      finiteLift (circlePt L '' Icc p q) \ {finitePoint (circlePt L p), finitePoint (circlePt L q)} := by
    have hNE'' : N ∩ circlePt L '' Icc α (α + 2 * Real.pi) = circlePt L '' Ioo p q := hNE
    rw [lift_inter', hNE'', lift_diff_pair, image_diff_pair hinjw hpq.le
      (fun x hx => ⟨hx.1, by linarith [hx.2]⟩)]
  have key := exact_sides_loop_core (D := D) hD hM
    (Ehat := finiteLift (circlePt L '' Icc α (α + 2 * Real.pi))) hG hR huv hEhat hGR hED hN hND
    hNE' hN₁ hN₂ hne₁ hne₂ hN₁N hN₂N (fun x hx h => hN₁E x hx (mem_finiteLift_iff.mp h))
    (fun x hx h => hN₂E x hx (mem_finiteLift_iff.mp h))
    (fun x hx hxE => hcov x hx (fun h => hxE (mem_finiteLift_iff.mpr h)))
  rw [setOf_lift] at key
  exact key

/-! ### The three piece types -/

theorem gap_circle (L : Lollipop) {D : Set Point} (hD : IsClosed D) (hArc : ArcConn D)
    {M : Lollipop} (hM : M.circle ⊆ D) {α β : ℝ} (hαβ : α < β) (hβ : β ≤ α + 2 * Real.pi)
    (hopen : ∀ θ ∈ Ioo α β, circlePt L θ ∉ D) (hend : circlePt L α ∈ D ∧ circlePt L β ∈ D) :
    Nonempty (ComponentFibers.ExactOneComponentSplitData
      (ComponentSurjectivity.complementSubset
        (LocalInsertion.old_subset_carrierExtension D (circleArcSet L α β)))) := by
  obtain ⟨U, S₁, S₂, hUpre, hC, hGerm⟩ := circle_collars' L hD hαβ hβ hopen hend
  have hpi := Real.pi_pos
  have hmid : (α + β) / 2 ∈ Ioo α β := ⟨by linarith, by linarith⟩
  obtain ⟨N, N₁, N₂, hNo, hNU, hNE, hpre₁, hpre₂, hne₁, hne₂, hN₁S, hN₂S, hcov, hN₁N, hN₂N⟩ :=
    (hGerm ((α + β) / 2) hmid ((β - α) / 4) (by linarith)
      (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)).ex
  have hND : N ⊆ Dᶜ := hNU.trans hC.U_sub
  have hN₁E : ∀ x ∈ N₁, x ∉ circleArcSet L α β := fun x hx => (hC.sub₁ (hN₁S hx)).2
  have hN₂E : ∀ x ∈ N₂, x ∉ circleArcSet L α β := fun x hx => (hC.sub₂ (hN₂S hx)).2
  have hcov' : ∀ x ∈ N, x ∉ circleArcSet L α β → x ∈ N₁ ∨ x ∈ N₂ :=
    fun x hx hxE => hcov ⟨hx, hxE⟩
  have hz₀E : circlePt L ((α + β) / 2) ∈ circleArcSet L α β := ⟨_, ⟨hmid.1.le, hmid.2.le⟩, rfl⟩
  have hEcl : IsClosed (circleArcSet L α β) :=
    (isCompact_Icc.image (HatAux.continuous_circlePt L)).isClosed
  have hELp : circleArcSet L α β ⊆ L.carrier := by
    rintro _ ⟨θ, _, rfl⟩
    exact Or.inl (HatAux.circlePt_mem_circle L θ)
  refine assemble L hELp hD hEcl hz₀E (hopen _ hmid) hC hUpre
    ⟨N₁, N₂, hN₁S, hN₂S, hne₁, hne₂, ?_⟩
  rcases hβ.lt_or_eq with hlt | heq
  · have hinj : InjOn (circlePt L) (Icc α β) :=
      (circlePt_injOn_Ico L α).mono (fun x (hx : x ∈ Icc α β) =>
        (⟨hx.1, by linarith [hx.2]⟩ : x ∈ Ico α (α + 2 * Real.pi)))
    have hA₁ : IsSphereArc (finiteLift (circlePt L '' Icc α ((α + β) / 2 - (β - α) / 4)))
        (finitePoint (circlePt L α))
        (finitePoint (circlePt L ((α + β) / 2 - (β - α) / 4))) :=
      circleSubArc L (by linarith) (by linarith)
    have hG : IsSphereArc
        (finiteLift (circlePt L '' Icc ((α + β) / 2 - (β - α) / 4) ((α + β) / 2 + (β - α) / 4)))
        (finitePoint (circlePt L ((α + β) / 2 - (β - α) / 4)))
        (finitePoint (circlePt L ((α + β) / 2 + (β - α) / 4))) :=
      circleSubArc L (by linarith) (by linarith)
    have hA₂ : IsSphereArc (finiteLift (circlePt L '' Icc ((α + β) / 2 + (β - α) / 4) β))
        (finitePoint (circlePt L ((α + β) / 2 + (β - α) / 4)))
        (finitePoint (circlePt L β)) :=
      circleSubArc L (by linarith) (by linarith)
    exact arc_core hD hArc hM (φ := circlePt L) (a := α) (b := β)
      (p := (α + β) / 2 - (β - α) / 4) (q := (α + β) / 2 + (β - α) / 4)
      (by linarith) (by linarith) (by linarith) hinj hA₁ hG hA₂ hopen hend hNo hND hNE
      hpre₁ hpre₂ hne₁ hne₂ hN₁N hN₂N hN₁E hN₂E hcov'
  · subst heq
    exact loop_core L hD hM (α := α) (p := (α + (α + 2 * Real.pi)) / 2 - (α + 2 * Real.pi - α) / 4)
      (q := (α + (α + 2 * Real.pi)) / 2 + (α + 2 * Real.pi - α) / 4)
      (by linarith) (by linarith) (by linarith) hopen hend.1 hNo hND hNE
      hpre₁ hpre₂ hne₁ hne₂ hN₁N hN₂N hN₁E hN₂E hcov'

theorem gap_seg (L : Lollipop) {D : Set Point} (hD : IsClosed D) (hArc : ArcConn D)
    {M : Lollipop} (hM : M.circle ⊆ D) {s t : ℝ} (hs : 1 ≤ s) (hst : s < t)
    (hopen : ∀ τ ∈ Ioo s t, stemPt L τ ∉ D) (hend : stemPt L s ∈ D ∧ stemPt L t ∈ D) :
    Nonempty (ComponentFibers.ExactOneComponentSplitData
      (ComponentSurjectivity.complementSubset
        (LocalInsertion.old_subset_carrierExtension D (segSet L s t)))) := by
  obtain ⟨U, S₁, S₂, hUpre, hC, hGerm⟩ := seg_collars' L hD hs hst hopen hend
  have hmid : (s + t) / 2 ∈ Ioo s t := ⟨by linarith, by linarith⟩
  obtain ⟨N, N₁, N₂, hNo, hNU, hNE, hpre₁, hpre₂, hne₁, hne₂, hN₁S, hN₂S, hcov, hN₁N, hN₂N⟩ :=
    (hGerm ((s + t) / 2) hmid ((t - s) / 4) (by linarith)
      (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)).ex
  have hND : N ⊆ Dᶜ := hNU.trans hC.U_sub
  have hN₁E : ∀ x ∈ N₁, x ∉ segSet L s t := fun x hx => (hC.sub₁ (hN₁S hx)).2
  have hN₂E : ∀ x ∈ N₂, x ∉ segSet L s t := fun x hx => (hC.sub₂ (hN₂S hx)).2
  have hcov' : ∀ x ∈ N, x ∉ segSet L s t → x ∈ N₁ ∨ x ∈ N₂ :=
    fun x hx hxE => hcov ⟨hx, hxE⟩
  have hz₀E : stemPt L ((s + t) / 2) ∈ segSet L s t := ⟨_, ⟨hmid.1.le, hmid.2.le⟩, rfl⟩
  have hEcl : IsClosed (segSet L s t) :=
    (isCompact_Icc.image (StemAux.continuous_stemPt L)).isClosed
  have hELp : segSet L s t ⊆ L.carrier := by
    rintro _ ⟨τ, hτ, rfl⟩
    exact Or.inr ⟨τ, le_trans hs hτ.1, rfl⟩
  refine assemble L hELp hD hEcl hz₀E (hopen _ hmid) hC hUpre
    ⟨N₁, N₂, hN₁S, hN₂S, hne₁, hne₂, ?_⟩
  have hinj : InjOn (stemPt L) (Icc s t) := (HatAux.stemPt_injective L).injOn
  have hA₁ : IsSphereArc (finiteLift (stemPt L '' Icc s ((s + t) / 2 - (t - s) / 4)))
      (finitePoint (stemPt L s)) (finitePoint (stemPt L ((s + t) / 2 - (t - s) / 4))) :=
    segSubArc L hs (by linarith)
  have hG : IsSphereArc
      (finiteLift (stemPt L '' Icc ((s + t) / 2 - (t - s) / 4) ((s + t) / 2 + (t - s) / 4)))
      (finitePoint (stemPt L ((s + t) / 2 - (t - s) / 4)))
      (finitePoint (stemPt L ((s + t) / 2 + (t - s) / 4))) :=
    segSubArc L (by linarith) (by linarith)
  have hA₂ : IsSphereArc (finiteLift (stemPt L '' Icc ((s + t) / 2 + (t - s) / 4) t))
      (finitePoint (stemPt L ((s + t) / 2 + (t - s) / 4))) (finitePoint (stemPt L t)) :=
    segSubArc L (by linarith) (by linarith)
  exact arc_core hD hArc hM (φ := stemPt L) (a := s) (b := t)
    (p := (s + t) / 2 - (t - s) / 4) (q := (s + t) / 2 + (t - s) / 4)
    (by linarith) (by linarith) (by linarith) hinj hA₁ hG hA₂ hopen hend hNo hND hNE
    hpre₁ hpre₂ hne₁ hne₂ hN₁N hN₂N hN₁E hN₂E hcov'

theorem gap_ray (L : Lollipop) {D : Set Point} (hD : IsClosed D) (hArc : ArcConn D)
    {M : Lollipop} (hM : M.circle ⊆ D) {s : ℝ} (hs : 1 ≤ s)
    (hopen : ∀ τ, s < τ → stemPt L τ ∉ D) (hend : stemPt L s ∈ D) :
    Nonempty (ComponentFibers.ExactOneComponentSplitData
      (ComponentSurjectivity.complementSubset
        (LocalInsertion.old_subset_carrierExtension D (raySet L s)))) := by
  obtain ⟨U, S₁, S₂, hUpre, hC, hGerm⟩ := ray_collars' L hD hs hopen hend
  obtain ⟨N, N₁, N₂, hNo, hNU, hNE, hpre₁, hpre₂, hne₁, hne₂, hN₁S, hN₂S, hcov, hN₁N, hN₂N⟩ :=
    (hGerm (s + 2) (by linarith) 1 one_pos (by linarith)).ex
  have hND : N ⊆ Dᶜ := hNU.trans hC.U_sub
  have hN₁E : ∀ x ∈ N₁, x ∉ raySet L s := fun x hx => (hC.sub₁ (hN₁S hx)).2
  have hN₂E : ∀ x ∈ N₂, x ∉ raySet L s := fun x hx => (hC.sub₂ (hN₂S hx)).2
  have hcov' : ∀ x ∈ N, x ∉ raySet L s → x ∈ N₁ ∨ x ∈ N₂ :=
    fun x hx hxE => hcov ⟨hx, hxE⟩
  have hz₀E : stemPt L (s + 2) ∈ raySet L s := ⟨s + 2, Set.mem_Ici.mpr (by linarith), rfl⟩
  have hEcl : IsClosed (raySet L s) := (IsGapPiece.ray hs hopen hend).isClosed
  have hELp : raySet L s ⊆ L.carrier := HatAux.raySet_subset_carrier L hs
  refine assemble L hELp hD hEcl hz₀E (hopen _ (by linarith)) hC hUpre
    ⟨N₁, N₂, hN₁S, hN₂S, hne₁, hne₂, ?_⟩
  exact ray_core L hD hArc hM hs (p := s + 2 - 1) (q := s + 2 + 1) (by linarith) (by linarith)
    hopen hend hNo hND hNE hpre₁ hpre₂ hne₁ hne₂ hN₁N hN₂N hN₁E hN₂E hcov'

end GapSplitAux

/-- **Exact split of one gap piece.**  Adding a gap piece `E` to a closed set `D`
that is arc connected to `∞` and contains a full circle splits exactly one face
of `D` into exactly two. -/
theorem gap_exact_split (L : Lollipop) {D : Set Point} (hD : IsClosed D)
    (hArc : ArcConn D) {M : Lollipop} (hM : M.circle ⊆ D) {E : Set Point}
    (hE : IsGapPiece L D E) :
    Nonempty (ComponentFibers.ExactOneComponentSplitData
      (ComponentSurjectivity.complementSubset
        (LocalInsertion.old_subset_carrierExtension D E))) := by
  cases hE with
  | circle hαβ hβ hopen hend => exact GapSplitAux.gap_circle L hD hArc hM hαβ hβ hopen hend
  | seg hs hst hopen hend => exact GapSplitAux.gap_seg L hD hArc hM hs hst hopen hend
  | ray hs hopen hend => exact GapSplitAux.gap_ray L hD hArc hM hs hopen hend


end Pieces
end EndToEnd
end Concrete
end Lollipop
