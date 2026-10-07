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
namespace TMAux

open Set

section Abstract

variable {T : Type*} [TopologicalSpace T]

theorem mk_eq_iff {S : Set T} (x y : S) :
    (ConnectedComponents.mk x = ConnectedComponents.mk y) ↔
      (y : T) ∈ connectedComponentIn S (x : T) := by
  rw [eq_comm, ConnectedComponents.coe_eq_coe', connectedComponentIn_eq_image x.2]
  exact (Subtype.val_injective.mem_set_image).symm

theorem cc_symm {S : Set T} {x y : T} (h : y ∈ connectedComponentIn S x) :
    x ∈ connectedComponentIn S y := by
  have hx : x ∈ S := connectedComponentIn_nonempty_iff.mp ⟨y, h⟩
  rw [← connectedComponentIn_eq h]
  exact mem_connectedComponentIn hx

theorem exists_clopen_sep [CompactSpace T] [T2Space T] {K : Set T} (hK : IsClosed K)
    {x p : T} (hx : x ∈ K) (hp : p ∈ K) (h : p ∉ connectedComponentIn K x) :
    ∃ V : Set T, V ⊆ K ∧ x ∈ V ∧ p ∉ V ∧ IsClosed V ∧ IsClosed (K \ V) := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK.isCompact
  have hp' : (⟨p, hp⟩ : K) ∉ connectedComponent (⟨x, hx⟩ : K) := by
    intro hm
    apply h
    rw [connectedComponentIn_eq_image hx]
    exact ⟨_, hm, rfl⟩
  rw [connectedComponent_eq_iInter_isClopen, Set.mem_iInter] at hp'
  push Not at hp'
  obtain ⟨⟨s, hs, hxs⟩, hps⟩ := hp'
  refine ⟨(↑) '' s, ?_, ⟨_, hxs, rfl⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨z, _, rfl⟩
    exact z.2
  · rintro ⟨z, hz, hzp⟩
    have : z = ⟨p, hp⟩ := Subtype.ext hzp
    exact hps (this ▸ hz)
  · exact hK.isClosedEmbedding_subtypeVal.isClosedMap _ hs.isClosed
  · have : K \ ((↑) '' s) = (↑) '' sᶜ := by
      ext z
      constructor
      · rintro ⟨hzK, hzs⟩
        exact ⟨⟨z, hzK⟩, fun h => hzs ⟨_, h, rfl⟩, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        refine ⟨w.2, ?_⟩
        rintro ⟨w', hw', e⟩
        exact hw (by rwa [← Subtype.ext e])
    rw [this]
    exact hK.isClosedEmbedding_subtypeVal.isClosedMap _ hs.compl.isClosed

theorem key_lemma [CompactSpace T] [T2Space T] {K E : Set T} (hK : IsClosed K)
    (hE : IsClosed E) {a b : T} (ha : a ∈ K) (hb : b ∈ K) (hKE : K ∩ E ⊆ {a, b})
    {x y : T} (hx : x ∈ K)
    (hxa : x ∉ connectedComponentIn K a) (hxb : x ∉ connectedComponentIn K b)
    (hy : y ∈ connectedComponentIn (K ∪ E) x) : y ∈ connectedComponentIn K x := by
  have hpa : a ∉ connectedComponentIn K x := fun h => hxa (cc_symm h)
  have hpb : b ∉ connectedComponentIn K x := fun h => hxb (cc_symm h)
  obtain ⟨V1, hV1K, hxV1, haV1, hV1c, hV1d⟩ := exists_clopen_sep hK hx ha hpa
  obtain ⟨V2, hV2K, hxV2, hbV2, hV2c, hV2d⟩ := exists_clopen_sep hK hx hb hpb
  have hVc : IsClosed (V1 ∩ V2) := hV1c.inter hV2c
  have hVd : IsClosed (K \ (V1 ∩ V2)) := by
    have : K \ (V1 ∩ V2) = (K \ V1) ∪ (K \ V2) := by
      ext z; simp only [mem_diff, mem_inter_iff, mem_union]; tauto
    rw [this]; exact hV1d.union hV2d
  have hW : IsClosed ((K \ (V1 ∩ V2)) ∪ E) := hVd.union hE
  have hVW : ∀ z, z ∈ V1 ∩ V2 → z ∉ (K \ (V1 ∩ V2)) ∪ E := by
    intro z hz hzW
    rcases hzW with h | h
    · exact h.2 hz
    · have hzK : z ∈ K := hV1K hz.1
      rcases hKE ⟨hzK, h⟩ with rfl | rfl
      · exact haV1 hz.1
      · exact hbV2 hz.2
  have hcov : connectedComponentIn (K ∪ E) x ⊆ (V1 ∩ V2) ∪ ((K \ (V1 ∩ V2)) ∪ E) := by
    intro z hz
    have : z ∈ K ∪ E := connectedComponentIn_subset _ _ hz
    by_cases hzV : z ∈ V1 ∩ V2
    · exact Or.inl hzV
    · rcases this with h | h
      · exact Or.inr (Or.inl ⟨h, hzV⟩)
      · exact Or.inr (Or.inr h)
  have hdis : connectedComponentIn (K ∪ E) x ∩ ((V1 ∩ V2) ∩ ((K \ (V1 ∩ V2)) ∪ E)) = ∅ := by
    apply eq_empty_of_forall_notMem
    rintro z ⟨_, hz1, hz2⟩
    exact hVW z hz1 hz2
  have hxKE : x ∈ K ∪ E := Or.inl hx
  have hsub : connectedComponentIn (K ∪ E) x ⊆ V1 ∩ V2 := by
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp
      isPreconnected_connectedComponentIn) _ _ hVc hW hcov hdis with h | h
    · exact h
    · exact absurd (h (mem_connectedComponentIn hxKE)) (hVW x ⟨hxV1, hxV2⟩)
  have hsubK : connectedComponentIn (K ∪ E) x ⊆ K := fun z hz => hV1K (hsub hz).1
  exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
    (mem_connectedComponentIn hxKE) hsubK hy

section Merge

variable [CompactSpace T] [T2Space T] {K E : Set T} (hK : IsClosed K) (hE : IsClosed E)
  (hEc : IsConnected E) {a b : T} (ha : a ∈ K ∩ E) (hb : b ∈ K ∩ E) (hKE : K ∩ E ⊆ {a, b})

omit [CompactSpace T] [T2Space T] in
include hEc in
theorem E_sub_cc {z : T} (hz : z ∈ E) :
    E ⊆ connectedComponentIn (K ∪ E) z :=
  hEc.isPreconnected.subset_connectedComponentIn hz subset_union_right

include hK hE ha hb hKE in
theorem fib_lemma (x : K)
    (h : ComponentFibers.inclusionMap (Set.subset_union_left : K ⊆ K ∪ E)
        (ConnectedComponents.mk x) =
      ComponentFibers.inclusionMap (Set.subset_union_left : K ⊆ K ∪ E)
        (ConnectedComponents.mk (⟨a, ha.1⟩ : K))) :
    ConnectedComponents.mk x = ConnectedComponents.mk (⟨a, ha.1⟩ : K) ∨
      ConnectedComponents.mk x = ConnectedComponents.mk (⟨b, hb.1⟩ : K) := by
  rw [ComponentFibers.inclusionMap_mk, ComponentFibers.inclusionMap_mk, mk_eq_iff] at h
  rw [mk_eq_iff, mk_eq_iff]
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have h1' : (x : T) ∉ connectedComponentIn K a := fun hh => h1 (cc_symm hh)
  have h2' : (x : T) ∉ connectedComponentIn K b := fun hh => h2 (cc_symm hh)
  have := key_lemma hK hE ha.1 hb.1 hKE x.2 h1' h2' (y := a) h
  exact h1 this

include hK hE hEc ha hb hKE in
theorem sub_lemma (x y : K)
    (h : ComponentFibers.inclusionMap (Set.subset_union_left : K ⊆ K ∪ E)
        (ConnectedComponents.mk x) =
      ComponentFibers.inclusionMap (Set.subset_union_left : K ⊆ K ∪ E)
        (ConnectedComponents.mk y))
    (hne : ComponentFibers.inclusionMap (Set.subset_union_left : K ⊆ K ∪ E)
        (ConnectedComponents.mk x) ≠
      ComponentFibers.inclusionMap (Set.subset_union_left : K ⊆ K ∪ E)
        (ConnectedComponents.mk (⟨a, ha.1⟩ : K))) :
    ConnectedComponents.mk x = ConnectedComponents.mk y := by
  have hxa : (x : T) ∉ connectedComponentIn K a := by
    intro hxa
    apply hne
    rw [ComponentFibers.inclusionMap_mk, ComponentFibers.inclusionMap_mk, mk_eq_iff]
    exact cc_symm (connectedComponentIn_mono a subset_union_left hxa)
  have hxb : (x : T) ∉ connectedComponentIn K b := by
    intro hxb
    apply hne
    rw [ComponentFibers.inclusionMap_mk, ComponentFibers.inclusionMap_mk, mk_eq_iff]
    have h1 : (x : T) ∈ connectedComponentIn (K ∪ E) b :=
      connectedComponentIn_mono b subset_union_left hxb
    have h2 : b ∈ connectedComponentIn (K ∪ E) a := E_sub_cc hEc ha.2 hb.2
    have h3 : (x : T) ∈ connectedComponentIn (K ∪ E) a := by
      rw [connectedComponentIn_eq h2]; exact h1
    exact cc_symm h3
  rw [ComponentFibers.inclusionMap_mk, ComponentFibers.inclusionMap_mk, mk_eq_iff] at h
  rw [mk_eq_iff]
  exact key_lemma hK hE ha.1 hb.1 hKE x.2 hxa hxb h

include hK hE hEc ha hb hKE in
theorem merge_abstract :
    Function.Surjective
        (ComponentFibers.inclusionMap (Set.subset_union_left : K ⊆ K ∪ E)) ∧
      (a ∉ connectedComponentIn K b →
        Nonempty (ComponentFibers.ExactOneComponentSplitData
          (Set.subset_union_left : K ⊆ K ∪ E))) ∧
      (a ∈ connectedComponentIn K b →
        Function.Bijective
          (ComponentFibers.inclusionMap (Set.subset_union_left : K ⊆ K ∪ E))) := by
  classical
  set f := ComponentFibers.inclusionMap (Set.subset_union_left : K ⊆ K ∪ E) with hf
  set ka : ConnectedComponents K := ConnectedComponents.mk (⟨a, ha.1⟩ : K) with hka
  set kb : ConnectedComponents K := ConnectedComponents.mk (⟨b, hb.1⟩ : K) with hkb
  have hfb : f kb = f ka := by
    rw [hf, hka, hkb, ComponentFibers.inclusionMap_mk, ComponentFibers.inclusionMap_mk,
      mk_eq_iff]
    exact cc_symm (E_sub_cc hEc ha.2 hb.2)
  have hfib : ∀ u : ConnectedComponents K, f u = f ka → u = ka ∨ u = kb := by
    intro u hu
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe u
    exact fib_lemma hK hE ha hb hKE x hu
  have hsub : ∀ u v : ConnectedComponents K, f u = f v → f u ≠ f ka → u = v := by
    intro u v h hne
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe u
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe v
    exact sub_lemma hK hE hEc ha hb hKE x y h hne
  have hsurj : Function.Surjective f := by
    intro c
    obtain ⟨z, rfl⟩ := ConnectedComponents.surjective_coe c
    rcases z.2 with hz | hz
    · exact ⟨ConnectedComponents.mk (⟨z.1, hz⟩ : K), by
        rw [hf, ComponentFibers.inclusionMap_mk]; rfl⟩
    · refine ⟨ka, ?_⟩
      rw [hf, hka, ComponentFibers.inclusionMap_mk, mk_eq_iff]
      exact E_sub_cc hEc ha.2 hz
  refine ⟨hsurj, ?_, ?_⟩
  · intro hab
    have hne : kb ≠ ka := by
      intro h
      apply hab
      rw [hka, hkb, mk_eq_iff] at h
      exact h
    refine ⟨{ active := f ka
              activeClassifier := fun u => if u.1 = ka then 0 else 1
              active_injective := ?_
              inactive_subsingleton := ?_
              componentMap_surjective := hsurj
              activeSide_surjective := ?_ }⟩
    · intro u v h
      apply Subtype.ext
      by_cases hu : u.1 = ka <;> by_cases hv : v.1 = ka
      · rw [hu, hv]
      · simp [hu, hv] at h
      · simp [hu, hv] at h
      · rcases hfib u.1 u.2 with h1 | h1
        · exact absurd h1 hu
        rcases hfib v.1 v.2 with h2 | h2
        · exact absurd h2 hv
        rw [h1, h2]
    · intro c hc
      exact ⟨fun u v => Subtype.ext (hsub u.1 v.1 (u.2.trans v.2.symm)
        (by have h := u.2; change f u.1 = c at h; rw [h]; exact hc))⟩
    · intro i
      fin_cases i
      · exact ⟨⟨ka, rfl⟩, by simp⟩
      · exact ⟨⟨kb, hfb⟩, by simp [hne]⟩
  · intro hab
    have hkk : kb = ka := by
      rw [hka, hkb, mk_eq_iff]
      exact hab
    refine ⟨?_, hsurj⟩
    intro u v h
    by_cases hA : f u = f ka
    · rcases hfib u hA with h1 | h1 <;> rcases hfib v (h.symm.trans hA) with h2 | h2 <;>
        simp [h1, h2, hkk]
    · exact hsub u v h hA

end Merge

end Abstract

end TMAux

/-- **Merging a connected closed set into a closed set.**  Let `K` and `E` be
closed in the sphere, `E` connected, and `K ∩ E ⊆ {a, b}` with `a b ∈ K ∩ E`.
Then every component of `K ∪ E` contains a component of `K`; if `a, b` lie in
different components of `K` the inclusion of component spaces is exact one-split
data, and if they lie in the same component it is a bijection. -/
theorem merge_components {K E : Set Sphere2} (hK : IsClosed K) (hE : IsClosed E)
    (hEc : IsConnected E) {a b : Sphere2} (ha : a ∈ K ∩ E) (hb : b ∈ K ∩ E)
    (hKE : K ∩ E ⊆ {a, b}) :
    Function.Surjective
        (ComponentFibers.inclusionMap (Set.subset_union_left : K ⊆ K ∪ E)) ∧
      (a ∉ connectedComponentIn K b →
        Nonempty (ComponentFibers.ExactOneComponentSplitData
          (Set.subset_union_left : K ⊆ K ∪ E))) ∧
      (a ∈ connectedComponentIn K b →
        Function.Bijective
          (ComponentFibers.inclusionMap (Set.subset_union_left : K ⊆ K ∪ E))) :=
  TMAux.merge_abstract hK hE hEc ha hb hKE

/-- Component count when the two attachment points are in different components. -/
theorem componentCount_union_of_not_same {K E : Set Sphere2} (hK : IsClosed K)
    (hE : IsClosed E) (hEc : IsConnected E) {a b : Sphere2} (ha : a ∈ K ∩ E)
    (hb : b ∈ K ∩ E) (hKE : K ∩ E ⊆ {a, b}) (hab : a ∉ connectedComponentIn K b)
    (hfin : Finite (ConnectedComponents K)) :
    Finite (ConnectedComponents (K ∪ E : Set Sphere2)) ∧
      componentCount K = componentCount (K ∪ E : Set Sphere2) + 1 := by
  obtain ⟨hsurj, hsplit, -⟩ := merge_components hK hE hEc ha hb hKE
  have hfin' : Finite (ConnectedComponents (K ∪ E : Set Sphere2)) :=
    Finite.of_surjective _ hsurj
  obtain ⟨d⟩ := hsplit hab
  exact ⟨hfin', ComponentFibers.componentCount_eq_add_one_of_exactOneComponentSplit _ d⟩

/-- Component count when the two attachment points are in the same component. -/
theorem componentCount_union_of_same {K E : Set Sphere2} (hK : IsClosed K)
    (hE : IsClosed E) (hEc : IsConnected E) {a b : Sphere2} (ha : a ∈ K ∩ E)
    (hb : b ∈ K ∩ E) (hKE : K ∩ E ⊆ {a, b}) (hab : a ∈ connectedComponentIn K b)
    (hfin : Finite (ConnectedComponents K)) :
    Finite (ConnectedComponents (K ∪ E : Set Sphere2)) ∧
      componentCount (K ∪ E : Set Sphere2) = componentCount K := by
  obtain ⟨hsurj, -, hbij⟩ := merge_components hK hE hEc ha hb hKE
  have hfin' : Finite (ConnectedComponents (K ∪ E : Set Sphere2)) :=
    Finite.of_surjective _ hsurj
  refine ⟨hfin', ?_⟩
  exact (Nat.card_eq_of_bijective _ (hbij hab)).symm

end Pieces
end EndToEnd
end Concrete
end Lollipop

