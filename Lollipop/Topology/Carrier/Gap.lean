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
import Mathlib.Tactic

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace Pieces

open Set

namespace GapAux

theorem stemPt_eq (L : Lollipop) (t : ℝ) : stemPt L t = L.center + t • L.radial := rfl

theorem stemPt_one (L : Lollipop) : stemPt L 1 = L.anchor := by
  simp [stemPt_eq, Lollipop.anchor]

theorem stemPt_closedEmbedding (L : Lollipop) : Topology.IsClosedEmbedding (stemPt L) := by
  have h1 : Topology.IsClosedEmbedding (fun t : ℝ => t • L.radial) :=
    isClosedEmbedding_smul_left L.radial_ne_zero
  have h2 : Topology.IsClosedEmbedding (fun x : Point => L.center + x) :=
    (Homeomorph.addLeft L.center).isClosedEmbedding
  exact h2.comp h1

theorem circlePt_two_pi (L : Lollipop) : circlePt L (2 * Real.pi) = L.anchor := by
  rw [← stemPt_one, ← HatAux.circlePt_zero_eq_stemPt]
  simp [circlePt]

theorem circlePt_mem_carrier (L : Lollipop) (θ : ℝ) : circlePt L θ ∈ L.carrier :=
  Or.inl (HatAux.circlePt_mem_circle L θ)

theorem stemPt_mem_carrier (L : Lollipop) {τ : ℝ} (hτ : 1 ≤ τ) : stemPt L τ ∈ L.carrier :=
  Or.inr ⟨τ, hτ, rfl⟩

theorem isClosed_circleArcSet (L : Lollipop) (α β : ℝ) : IsClosed (circleArcSet L α β) :=
  (isCompact_Icc.image (HatAux.continuous_circlePt L)).isClosed

theorem isClosed_segSet (L : Lollipop) (s t : ℝ) : IsClosed (segSet L s t) :=
  (isCompact_Icc.image L.continuous_stemMap).isClosed

theorem isClosed_raySet (L : Lollipop) (s : ℝ) : IsClosed (raySet L s) :=
  (stemPt_closedEmbedding L).isClosedMap _ isClosed_Ici

theorem circleArcSet_subset (L : Lollipop) (α β : ℝ) : circleArcSet L α β ⊆ L.carrier := by
  rintro _ ⟨θ, -, rfl⟩
  exact circlePt_mem_carrier L θ

theorem segSet_subset (L : Lollipop) {s t : ℝ} (hs : 1 ≤ s) : segSet L s t ⊆ L.carrier := by
  rintro _ ⟨τ, hτ, rfl⟩
  exact stemPt_mem_carrier L (hs.trans hτ.1)

theorem raySet_subset (L : Lollipop) {s : ℝ} (hs : 1 ≤ s) : raySet L s ⊆ L.carrier := by
  rintro _ ⟨τ, hτ, rfl⟩
  exact stemPt_mem_carrier L (hs.trans hτ)

/-- Closed set of reals: the gap to the left of a point outside. -/
theorem gap_left {P : Set ℝ} (hP : IsClosed P) {a x : ℝ} (ha : a ∈ P) (hax : a ≤ x)
    (hx : x ∉ P) :
    ∃ α, a ≤ α ∧ α < x ∧ α ∈ P ∧ ∀ y ∈ Ioc α x, y ∉ P := by
  set A : Set ℝ := P ∩ Icc a x with hA
  have hAc : IsClosed A := hP.inter isClosed_Icc
  have hAne : A.Nonempty := ⟨a, ha, le_rfl, hax⟩
  have hAb : BddAbove A := ⟨x, fun y hy => hy.2.2⟩
  have hmem : sSup A ∈ A := hAc.csSup_mem hAne hAb
  refine ⟨sSup A, hmem.2.1, ?_, hmem.1, ?_⟩
  · rcases lt_or_eq_of_le hmem.2.2 with h | h
    · exact h
    · exact absurd (h ▸ hmem.1) hx
  · rintro y ⟨hy1, hy2⟩ hyP
    have : y ∈ A := ⟨hyP, by linarith [hmem.2.1], hy2⟩
    exact absurd (le_csSup hAb this) (not_le.2 hy1)

/-- Closed set of reals: the gap to the right of a point outside, if the set is hit. -/
theorem gap_right {P : Set ℝ} (hP : IsClosed P) {x b : ℝ} (hb : b ∈ P) (hxb : x ≤ b)
    (hx : x ∉ P) :
    ∃ β, x < β ∧ β ≤ b ∧ β ∈ P ∧ ∀ y ∈ Ico x β, y ∉ P := by
  set B : Set ℝ := P ∩ Icc x b with hB
  have hBc : IsClosed B := hP.inter isClosed_Icc
  have hBne : B.Nonempty := ⟨b, hb, hxb, le_rfl⟩
  have hBb : BddBelow B := ⟨x, fun y hy => hy.2.1⟩
  have hmem : sInf B ∈ B := hBc.csInf_mem hBne hBb
  refine ⟨sInf B, ?_, hmem.2.2, hmem.1, ?_⟩
  · rcases lt_or_eq_of_le hmem.2.1 with h | h
    · exact h
    · exact absurd (h ▸ hmem.1) hx
  · rintro y ⟨hy1, hy2⟩ hyP
    have : y ∈ B := ⟨hyP, hy1, by linarith [hmem.2.2]⟩
    exact absurd (csInf_le hBb this) (not_le.2 hy2)

end GapAux

open GapAux

theorem IsGapPiece.isClosed {L : Lollipop} {D E : Set Point} (h : IsGapPiece L D E) :
    IsClosed E := by
  cases h with
  | circle _ _ _ _ => exact isClosed_circleArcSet L _ _
  | seg _ _ _ _ => exact isClosed_segSet L _ _
  | ray _ _ _ => exact isClosed_raySet L _
theorem IsGapPiece.subset_carrier {L : Lollipop} {D E : Set Point} (h : IsGapPiece L D E) :
    E ⊆ L.carrier := by
  cases h with
  | circle _ _ _ _ => exact circleArcSet_subset L _ _
  | seg hs _ _ _ => exact segSet_subset L hs
  | ray hs _ _ => exact raySet_subset L hs
/-- A gap piece has points outside `D`. -/
theorem IsGapPiece.not_subset {L : Lollipop} {D E : Set Point} (h : IsGapPiece L D E) :
    ¬ E ⊆ D := by
  intro hsub
  cases h with
  | @circle α β hαβ _ hopen _ =>
    have hm : circlePt L ((α + β) / 2) ∈ circleArcSet L α β :=
      ⟨(α + β) / 2, ⟨by linarith, by linarith⟩, rfl⟩
    exact hopen ((α + β) / 2) ⟨by linarith, by linarith⟩ (hsub hm)
  | @seg s t hs hst hopen _ =>
    have hm : stemPt L ((s + t) / 2) ∈ segSet L s t :=
      ⟨(s + t) / 2, ⟨by linarith, by linarith⟩, rfl⟩
    exact hopen ((s + t) / 2) ⟨by linarith, by linarith⟩ (hsub hm)
  | @ray s hs hopen _ =>
    have hm : stemPt L (s + 1) ∈ raySet L s :=
      ⟨s + 1, by simp, rfl⟩
    exact hopen (s + 1) (by linarith) (hsub hm)
theorem IsLeafPiece.isClosed {L : Lollipop} {D E : Set Point} (h : IsLeafPiece L D E) :
    IsClosed E := by
  cases h with
  | seg _ _ _ _ => exact isClosed_segSet L _ _
  | ray _ _ => exact isClosed_raySet L _
theorem IsLeafPiece.subset_carrier {L : Lollipop} {D E : Set Point} (h : IsLeafPiece L D E) :
    E ⊆ L.carrier := by
  cases h with
  | seg _ _ _ _ => exact segSet_subset L le_rfl
  | ray _ _ => exact raySet_subset L le_rfl
theorem IsLeafPiece.anchor_mem {L : Lollipop} {D E : Set Point} (h : IsLeafPiece L D E) :
    L.anchor ∈ E := by
  rw [← stemPt_one]
  cases h with
  | seg ht _ _ _ => exact ⟨1, ⟨le_rfl, ht.le⟩, rfl⟩
  | ray _ _ => exact ⟨1, Set.self_mem_Ici, rfl⟩
/-- `IsGapPiece` implies the edge is a connected set. -/
theorem IsGapPiece.isConnected {L : Lollipop} {D E : Set Point} (h : IsGapPiece L D E) :
    IsConnected E := by
  cases h with
  | circle hαβ _ _ _ =>
    exact (isConnected_Icc hαβ.le).image _ (HatAux.continuous_circlePt L).continuousOn
  | seg hs hst _ _ =>
    exact (isConnected_Icc hst.le).image _ L.continuous_stemMap.continuousOn
  | ray _ _ _ =>
    exact isConnected_Ici.image _ L.continuous_stemMap.continuousOn

/-- If the anchor is already in `D` and the carrier of `L` is not inside `D`,
there is a gap piece. -/
theorem exists_gapPiece (L : Lollipop) {D : Set Point} (hD : IsClosed D)
    (hanchor : L.anchor ∈ D) (hX : ¬ L.carrier ⊆ D) : ∃ E, IsGapPiece L D E := by
  obtain ⟨x, hxC, hxD⟩ := not_subset.1 hX
  rcases hxC with hxc | ⟨τ, hτ, rfl⟩
  · -- circle case
    obtain ⟨θ, hθ, rfl⟩ := HatAux.circle_exists_angle L hxc
    have hP : IsClosed (circlePt L ⁻¹' D) := hD.preimage (HatAux.continuous_circlePt L)
    have h0 : (0 : ℝ) ∈ circlePt L ⁻¹' D := by
      show circlePt L 0 ∈ D
      rw [HatAux.circlePt_zero_eq_stemPt, stemPt_one]; exact hanchor
    have h2 : 2 * Real.pi ∈ circlePt L ⁻¹' D := by
      show circlePt L (2 * Real.pi) ∈ D
      rw [circlePt_two_pi]; exact hanchor
    obtain ⟨α, hα0, hαθ, hαP, hαgap⟩ := gap_left hP h0 hθ.1 hxD
    obtain ⟨β, hθβ, hβ2, hβP, hβgap⟩ := gap_right hP h2 hθ.2.le hxD
    refine ⟨_, IsGapPiece.circle (α := α) (β := β) (by linarith) (by linarith [hθ.1]) ?_
      ⟨hαP, hβP⟩⟩
    intro y hy hyD
    rcases le_or_gt y θ with h | h
    · exact hαgap y ⟨hy.1, h⟩ hyD
    · exact hβgap y ⟨h.le, hy.2⟩ hyD
  · -- stem case
    change stemPt L τ ∉ D at hxD
    have hτ1 : 1 < τ := by
      rcases lt_or_eq_of_le hτ with h | h
      · exact h
      · exfalso; apply hxD; rw [← h, stemPt_one]; exact hanchor
    have hP : IsClosed (stemPt L ⁻¹' D) := hD.preimage L.continuous_stemMap
    have h1 : (1 : ℝ) ∈ stemPt L ⁻¹' D := by
      show stemPt L 1 ∈ D
      rw [stemPt_one]; exact hanchor
    obtain ⟨s, hs1, hsτ, hsP, hsgap⟩ := gap_left hP h1 hτ hxD
    by_cases hex : ∃ σ ∈ stemPt L ⁻¹' D, τ ≤ σ
    · obtain ⟨b, hbP, hτb⟩ := hex
      obtain ⟨t, hτt, -, htP, htgap⟩ := gap_right hP hbP hτb hxD
      refine ⟨_, IsGapPiece.seg (s := s) (t := t) hs1 (by linarith) ?_ ⟨hsP, htP⟩⟩
      intro y hy hyD
      rcases le_or_gt y τ with h | h
      · exact hsgap y ⟨hy.1, h⟩ hyD
      · exact htgap y ⟨h.le, hy.2⟩ hyD
    · push Not at hex
      refine ⟨_, IsGapPiece.ray (s := s) hs1 ?_ hsP⟩
      intro y hy hyD
      rcases le_or_gt y τ with h | h
      · exact hsgap y ⟨hy, h⟩ hyD
      · exact absurd (hex y hyD) (not_lt.2 h.le)

/-- If the anchor is not in `D` there is a leaf piece. -/
theorem exists_leafPiece (L : Lollipop) {D : Set Point} (hD : IsClosed D)
    (hfree : L.anchor ∉ D) : ∃ E, IsLeafPiece L D E := by
  have hP : IsClosed (stemPt L ⁻¹' D) := hD.preimage L.continuous_stemMap
  have h1 : (1 : ℝ) ∉ stemPt L ⁻¹' D := by
    show stemPt L 1 ∉ D
    rw [stemPt_one]; exact hfree
  have hfree' : stemPt L 1 ∉ D := h1
  by_cases hex : ∃ σ ∈ stemPt L ⁻¹' D, 1 ≤ σ
  · obtain ⟨b, hbP, hb1⟩ := hex
    obtain ⟨t, h1t, -, htP, htgap⟩ := gap_right hP hbP hb1 h1
    exact ⟨_, IsLeafPiece.seg (t := t) h1t hfree'
      (fun y hy hyD => htgap y ⟨hy.1.le, hy.2⟩ hyD) htP⟩
  · push Not at hex
    exact ⟨_, IsLeafPiece.ray hfree' (fun y hy hyD => absurd hy.le (not_le.2 (hex y hyD)))⟩

namespace GapAux

theorem mk_eq_of_mem_cc {F : Set Point} {x y : Point} (hx : x ∈ F)
    (hy : y ∈ connectedComponentIn F x) :
    ConnectedComponents.mk (⟨x, hx⟩ : F) =
      ConnectedComponents.mk (⟨y, connectedComponentIn_subset F x hy⟩ : F) := by
  have hconn : IsConnected (connectedComponentIn F x) :=
    ⟨⟨x, mem_connectedComponentIn hx⟩, isPreconnected_connectedComponentIn⟩
  exact ComponentLifting.connectedComponents_mk_eq_of_isConnected_subset hconn
    (connectedComponentIn_subset F x) (mem_connectedComponentIn hx) hy

end GapAux

/-- A leaf piece adds no face and splits none: the component map is a bijection. -/
theorem leaf_bijective (L : Lollipop) {D : Set Point} (hD : IsClosed D)
    {E : Set Point} (hE : IsLeafPiece L D E) :
    Function.Bijective
      (ComponentFibers.inclusionMap
        (ComponentSurjectivity.complementSubset
          (LocalInsertion.old_subset_carrierExtension D E))) := by
  have hEc : IsClosed E := hE.isClosed
  have hKsub := LocalInsertion.carrierExtension_subset_union_carrier
    (C := D) hE.subset_carrier
  refine ⟨?_, ComponentSurjectivity.componentMap_surjective_of_closed_of_subset_union_carrier
    (LocalInsertion.old_subset_carrierExtension D E) hD L hKsub⟩
  obtain ⟨U, S, hC⟩ : ∃ U S : Set Point, OneCollar D E S U := by
    cases hE with
    | seg ht hfree hopen hend => exact seg_leaf_collar L hD le_rfl ht hfree hopen hend
    | ray hfree hopen => exact ray_leaf_collar L hD le_rfl hfree hopen
  have hSK : S ⊆ (LocalInsertion.carrierExtension D E)ᶜ := by
    intro x hx hxK
    have := hC.sub hx
    rcases hxK with h | h
    · exact hC.U_sub this.1 h
    · exact this.2 h
  intro c c'
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c
  obtain ⟨y', rfl⟩ := ConnectedComponents.surjective_coe c'
  intro hcc
  simp only [ComponentFibers.inclusionMap_mk] at hcc
  have hyD : y.1 ∈ Dᶜ := fun h => y.2 (Or.inl h)
  have hmem : y'.1 ∈ connectedComponentIn Dᶜ y.1 :=
    ComponentLifting.mem_connectedComponentIn_of_connectedComponents_mk_eq
      (⟨y.1, hyD⟩ : (Dᶜ : Set Point)) ⟨y'.1, fun h => y'.2 (Or.inl h)⟩ (by
        simpa [ComponentFibers.inclusion, ComponentSurjectivity.complementSubset] using hcc)
  set O : Set Point := connectedComponentIn Dᶜ y.1 with hO
  by_cases hex : ∃ z₀ ∈ E, z₀ ∈ O
  · obtain ⟨z₀, hz₀E, hz₀O⟩ := hex
    have hz₀D : z₀ ∉ D := connectedComponentIn_subset Dᶜ y.1 hz₀O
    have hcompeq : connectedComponentIn Dᶜ z₀ = O := (connectedComponentIn_eq hz₀O).symm
    have key : ∀ w : ((LocalInsertion.carrierExtension D E)ᶜ : Set Point), w.1 ∈ O →
        ∃ s ∈ S, ∃ hs : s ∈ (LocalInsertion.carrierExtension D E)ᶜ,
          ConnectedComponents.mk w = ConnectedComponents.mk (⟨s, hs⟩ :
            ((LocalInsertion.carrierExtension D E)ᶜ : Set Point)) := by
      intro w hwO
      have hwE : w.1 ∉ E := fun h => w.2 (Or.inr h)
      obtain ⟨s, hs, hsw⟩ := Collar.exists_collar_point_in_component hD hEc hz₀E hz₀D
        hC.isOpen_U (fun z hz _ => hC.new_sub z hz (fun hzD =>
          connectedComponentIn_subset Dᶜ z₀ (hcompeq ▸ ‹z ∈ connectedComponentIn Dᶜ z₀›) hzD))
        hC.pre hC.pre hSK hSK
        (fun x hx _ hxE => Or.inl (hC.cover x hx hxE))
        (hcompeq ▸ hwO : w.1 ∈ connectedComponentIn Dᶜ z₀) hwE |>.elim
        (fun h => h) (fun h => h)
      exact ⟨s, hs, hSK hs, GapAux.mk_eq_of_mem_cc w.2 hsw⟩
    obtain ⟨s, hs, hsK, h1⟩ := key y (mem_connectedComponentIn hyD)
    obtain ⟨s', hs', hsK', h2⟩ := key y' hmem
    have h3 : ConnectedComponents.mk (⟨s, hsK⟩ : ((LocalInsertion.carrierExtension D E)ᶜ : Set Point)) =
        ConnectedComponents.mk (⟨s', hsK'⟩ : ((LocalInsertion.carrierExtension D E)ᶜ : Set Point)) :=
      ComponentLifting.connectedComponents_mk_eq_of_isConnected_subset
        ⟨⟨s, hs⟩, hC.pre⟩ hSK hs hs'
    rw [h1, h2, h3]
  · push Not at hex
    have hOK : O ⊆ (LocalInsertion.carrierExtension D E)ᶜ := by
      intro x hx hxK
      rcases hxK with h | h
      · exact connectedComponentIn_subset Dᶜ y.1 hx h
      · exact hex x h hx
    have hOconn : IsConnected O :=
      ⟨⟨y.1, mem_connectedComponentIn hyD⟩, isPreconnected_connectedComponentIn⟩
    exact ComponentLifting.connectedComponents_mk_eq_of_isConnected_subset hOconn hOK
      (mem_connectedComponentIn hyD) hmem


end Pieces
end EndToEnd
end Concrete
end Lollipop
