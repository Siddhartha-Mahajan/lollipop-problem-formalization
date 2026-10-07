import Carrier.Defs
import Carrier.Defs2
import Carrier.CircleCollars
import Carrier.StemCollars
import Carrier.LocalSides
import Carrier.SphereArcs
import Carrier.SphereSides
import Carrier.HatArcs
import Carrier.Collar
import Carrier.Gap
import Carrier.GapSplit
import Carrier.Potential
import Carrier.ArcPres
import Carrier.Conn
import old_lean_folder.Concrete.EndToEnd.InsertionFan
import old_lean_folder.Concrete.EndToEnd.PlanarInsertion
import old_lean_folder.Concrete.EndToEnd.OccupiedTopology
import old_lean_folder.Concrete.EndToEnd.MainTheorem.PositiveInsertionSubdivision
import Mathlib.Tactic

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace Pieces

open Set Function ComponentFibers

namespace DriverAux

variable {X : Type*} [TopologicalSpace X]

theorem inclusionMap_trans {S T U : Set X} (hST : S ⊆ T) (hTU : T ⊆ U) (x : ConnectedComponents S) :
    inclusionMap (hST.trans hTU) x = inclusionMap hTU (inclusionMap hST x) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe x
  simp [inclusionMap_mk, ComponentFibers.inclusion]

def fiberEquiv {S T U : Set X} (hST : S ⊆ T) (hTU : T ⊆ U)
    (hg : Injective (inclusionMap hTU)) (b : ConnectedComponents T) :
    Fiber (inclusionMap (hST.trans hTU)) (inclusionMap hTU b) ≃ Fiber (inclusionMap hST) b where
  toFun x := ⟨x.1, hg (by rw [← inclusionMap_trans hST hTU]; exact x.2)⟩
  invFun y := ⟨y.1, by rw [inclusionMap_trans hST hTU, y.2]⟩
  left_inv x := Subtype.ext rfl
  right_inv y := Subtype.ext rfl

/-- Composing exact one-component split data with a bijective (free) component map. -/
def compFree {S T U : Set X}
    {hST : S ⊆ T} (d : ExactOneComponentSplitData hST) (hTU : T ⊆ U)
    (hf : Bijective (inclusionMap hTU)) :
    ExactOneComponentSplitData (hST.trans hTU) where
  active := inclusionMap hTU d.active
  activeClassifier := d.activeClassifier ∘ (fiberEquiv hST hTU hf.1 d.active)
  active_injective := d.active_injective.comp (fiberEquiv hST hTU hf.1 d.active).injective
  inactive_subsingleton := by
    intro b hb
    obtain ⟨b', rfl⟩ := hf.2 b
    have hb' : b' ≠ d.active := fun h => hb (by rw [h])
    haveI := d.inactive_subsingleton b' hb'
    exact (fiberEquiv hST hTU hf.1 b').subsingleton
  componentMap_surjective := by
    intro c
    obtain ⟨b, rfl⟩ := hf.2 c
    obtain ⟨a, rfl⟩ := d.componentMap_surjective b
    exact ⟨a, inclusionMap_trans hST hTU a⟩
  activeSide_surjective :=
    d.activeSide_surjective.comp (fiberEquiv hST hTU hf.1 d.active).surjective

/-- The last step of a nonempty exact chain may be followed by a free inclusion. -/
def extendFree :
    ∀ {m : ℕ} {S T U : Set X}, ComponentSplitChain.ExactChain (m + 1) S T → ∀ (hTU : T ⊆ U),
      Bijective (inclusionMap hTU) → ComponentSplitChain.ExactChain (m + 1) S U
  | _, _, _, _, .snoc head hT'T split, hTU, hf =>
      .snoc head (hT'T.trans hTU) (compFree split hTU hf)

end DriverAux

open DriverAux

theorem kset_eq_of_carrier_subset (L : Lollipop) {D : Set Point} (h : L.carrier ⊆ D) :
    Kset L D = hatCarrier L := by
  ext x
  constructor
  · exact fun hx => hx.1
  · intro hx
    refine ⟨hx, ?_⟩
    rcases hx with ⟨p, hp, rfl⟩ | rfl
    · exact Or.inl ⟨p, h hp, rfl⟩
    · exact Or.inr rfl

theorem psi_eq_one_of_carrier_subset (L : Lollipop) {D : Set Point} (h : L.carrier ⊆ D) :
    Psi L D = 1 := by
  have hc : L.circle ⊆ D := fun x hx => h (Or.inl hx)
  unfold Psi
  rw [if_pos hc, kset_eq_of_carrier_subset L h, componentCount_hatCarrier]

theorem psi_pos (L : Lollipop) {D : Set Point}
    (hfin : Finite (ConnectedComponents (Kset L D))) : 1 ≤ Psi L D := by
  have hne : Nonempty (Kset L D) := ⟨⟨infinity, Or.inr rfl, Or.inr rfl⟩⟩
  haveI : Nonempty (ConnectedComponents (Kset L D)) :=
    ConnectedComponents.nonempty_iff_nonempty.mpr hne
  have : 0 < componentCount (Kset L D) := Nat.card_pos
  unfold Psi
  omega

/-- Chains for the case where the anchor already lies in the carrier. -/
theorem exists_exactChain_of_anchor (L : Lollipop) {M : Lollipop} :
    ∀ (N : ℕ) (D : Set Point), Psi L D = N → IsClosed D → L.anchor ∈ D → ArcConn D →
      M.circle ⊆ D → Finite (ConnectedComponents (Kset L D)) →
      ∃ m, Nonempty (ComponentSplitChain.ExactChain m ((D ∪ L.carrier)ᶜ) (Dᶜ)) ∧ m + 1 = Psi L D := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro D hN hD hanchor hArc hM hfin
    by_cases hsub : L.carrier ⊆ D
    · refine ⟨0, ?_, ?_⟩
      · have : D ∪ L.carrier = D := Set.union_eq_left.mpr hsub
        rw [this]
        exact ⟨ComponentSplitChain.ExactChain.nil _⟩
      · simp [psi_eq_one_of_carrier_subset L hsub]
    · obtain ⟨E, hE⟩ := exists_gapPiece L hD hanchor hsub
      have hEcl := hE.isClosed
      have hEsub := hE.subset_carrier
      obtain ⟨hfin', hpsi⟩ := gap_potential L hD hanchor hfin hE
      have hD' : IsClosed (D ∪ E) := hD.union hEcl
      have hanchor' : L.anchor ∈ D ∪ E := Or.inl hanchor
      have hArc' := arcConn_union_gap L hD hArc hE
      have hM' : M.circle ⊆ D ∪ E := hM.trans Set.subset_union_left
      have hlt : Psi L (D ∪ E) < N := by omega
      obtain ⟨m', ⟨chain'⟩, hm'⟩ :=
        ih _ hlt (D ∪ E) rfl hD' hanchor' hArc' hM' hfin'
      obtain ⟨d⟩ := gap_exact_split L hD hArc hM hE
      have hU : (D ∪ E) ∪ L.carrier = D ∪ L.carrier := by
        ext x; constructor
        · rintro ((h | h) | h)
          · exact Or.inl h
          · exact Or.inr (hEsub h)
          · exact Or.inr h
        · rintro (h | h)
          · exact Or.inl (Or.inl h)
          · exact Or.inr h
      rw [hU] at chain'
      exact ⟨m' + 1, ⟨ComponentSplitChain.ExactChain.snoc chain'
        (ComponentSurjectivity.complementSubset (LocalInsertion.old_subset_carrierExtension D E)) d⟩,
        by omega⟩

/-- The exact chain for adding the whole carrier of `L` to a closed set `D`. -/
theorem exists_exactChain (L : Lollipop) {D : Set Point} (hD : IsClosed D) (hArc : ArcConn D)
    {M : Lollipop} (hM : M.circle ⊆ D)
    (hfin : Finite (ConnectedComponents (Kset L D))) :
    ∃ m, Nonempty (ComponentSplitChain.ExactChain m ((D ∪ L.carrier)ᶜ) (Dᶜ)) ∧
      m + 1 = Psi L D := by
  by_cases hanchor : L.anchor ∈ D
  · exact exists_exactChain_of_anchor L _ D rfl hD hanchor hArc hM hfin
  · obtain ⟨E, hE⟩ := exists_leafPiece L hD hanchor
    have hEcl := hE.isClosed
    have hEsub := hE.subset_carrier
    obtain ⟨hfin', hpsi⟩ := leaf_potential L hD hfin hE
    have hD' : IsClosed (D ∪ E) := hD.union hEcl
    have hanchor' : L.anchor ∈ D ∪ E := Or.inr hE.anchor_mem
    have hArc' := arcConn_union_leaf L hD hArc hE
    have hM' : M.circle ⊆ D ∪ E := hM.trans Set.subset_union_left
    obtain ⟨m, ⟨chain⟩, hm⟩ :=
      exists_exactChain_of_anchor L _ (D ∪ E) rfl hD' hanchor' hArc' hM' hfin'
    -- the circle is not inside `D`, so `Psi ≥ 2`
    have hcirc : ¬ L.circle ⊆ D := fun h => hanchor (h (Lollipop.anchor_mem_circle L))
    have hpos := psi_pos L hfin
    have hψ : 2 ≤ Psi L D := by
      have hc : 1 ≤ componentCount (Kset L D) := by
        have hne : Nonempty (Kset L D) := ⟨⟨infinity, Or.inr rfl, Or.inr rfl⟩⟩
        haveI : Finite (ConnectedComponents (Kset L D)) := hfin
        haveI : Nonempty (ConnectedComponents (Kset L D)) :=
          ConnectedComponents.nonempty_iff_nonempty.mpr hne
        exact Nat.card_pos
      unfold Psi
      rw [if_neg hcirc]
      omega
    obtain ⟨m₀, rfl⟩ : ∃ m₀, m = m₀ + 1 := ⟨m - 1, by omega⟩
    have hU : (D ∪ E) ∪ L.carrier = D ∪ L.carrier := by
      ext x; constructor
      · rintro ((h | h) | h)
        · exact Or.inl h
        · exact Or.inr (hEsub h)
        · exact Or.inr h
      · rintro (h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
    rw [hU] at chain
    refine ⟨m₀ + 1, ⟨extendFree chain
      (ComponentSurjectivity.complementSubset (LocalInsertion.old_subset_carrierExtension D E))
      (leaf_bijective L hD hE)⟩, by omega⟩

/-! ### Plug-in to the insertion split-chain interface -/

open InsertionFan PlanarInsertion

theorem mem_previousIndices {n : ℕ} {k : ℕ} (hk : k < n) (i : Fin n) :
    i ∈ previousIndices (⟨k, hk⟩ : Fin n) ↔ i.1 < k := by
  simp [previousIndices, Fin.lt_def]

theorem hatSet_prefix_eq {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n) :
    hatSet (occupied (prefixArrangement A k (Nat.le_of_lt hk))) =
      pointedFinsetUnion infinity (previousIndices (⟨k, hk⟩ : Fin n))
        (fun i => hatCarrier (A i)) := by
  ext x
  constructor
  · rintro (⟨p, hp, rfl⟩ | rfl)
    · obtain ⟨i, hi⟩ := mem_occupied_iff.mp hp
      refine Or.inr (Set.mem_iUnion.mpr ⟨⟨⟨i.1, i.2.trans_le (Nat.le_of_lt hk)⟩,
        (mem_previousIndices hk _).mpr i.2⟩, ?_⟩)
      exact Or.inl ⟨p, hi, rfl⟩
    · exact Or.inl rfl
  · rintro (rfl | hx)
    · exact Or.inr rfl
    · obtain ⟨⟨i, hi⟩, hx⟩ := Set.mem_iUnion.mp hx
      rcases hx with ⟨p, hp, rfl⟩ | rfl
      · refine Or.inl ⟨p, mem_occupied_iff.mpr ⟨⟨i.1, (mem_previousIndices hk i).mp hi⟩, hp⟩, rfl⟩
      · exact Or.inr rfl

theorem kset_prefix_eq_fan {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n) :
    Kset (A ⟨k, hk⟩) (occupied (prefixArrangement A k (Nat.le_of_lt hk))) =
      insertionFan A k hk := by
  unfold Kset insertionFan
  rw [hatSet_prefix_eq, pairIntersectionFan_eq_inter_pointedCarrierUnion]

theorem arcConn_prefix {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n) :
    ArcConn (occupied (prefixArrangement A k (Nat.le_of_lt hk))) := by
  intro p hp
  rw [hatSet_prefix_eq A k hk] at hp
  rcases hp with rfl | hp
  · exact Or.inl rfl
  · obtain ⟨⟨i, hi⟩, hx⟩ := Set.mem_iUnion.mp hp
    rcases HatAux.hatCarrier_arc_to_infinity (A i) p hx with h | ⟨P, hP, hPa⟩
    · exact Or.inl h
    · refine Or.inr ⟨P, fun y hy => ?_, hPa⟩
      rw [hatSet_prefix_eq A k hk]
      exact Or.inr (Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hP hy⟩)

theorem prefix_chain_bound {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n) (hk0 : 0 < k) :
    ∃ h : Insertion.InsertionSplitChain (prefixArrangement A k (Nat.le_of_lt hk)) (A ⟨k, hk⟩),
      (h.edgeCount : ℚ) ≤ (componentCount (insertionFan A k hk) : ℚ) := by
  set C := occupied (prefixArrangement A k (Nat.le_of_lt hk)) with hC
  have hCc : IsClosed C := OccupiedTopology.isClosed_occupied _
  have hfin : Finite (ConnectedComponents (Kset (A ⟨k, hk⟩) C)) := by
    rw [hC, kset_prefix_eq_fan]
    exact MainTheorem.finite_connectedComponents_insertionFan A k hk
  have hM : (A ⟨0, hk0.trans hk⟩).circle ⊆ C := fun x hx =>
    mem_occupied_iff.mpr ⟨⟨0, hk0⟩, Or.inl hx⟩
  obtain ⟨m, ⟨chain⟩, hm⟩ :=
    exists_exactChain (A ⟨k, hk⟩) hCc (arcConn_prefix A k hk) hM hfin
  refine ⟨⟨m, chain.toChain⟩, ?_⟩
  have hle : m ≤ componentCount (insertionFan A k hk) := by
    by_cases hc : (A ⟨k, hk⟩).circle ⊆ C
    · have : Psi (A ⟨k, hk⟩) C = componentCount (insertionFan A k hk) := by
        unfold Psi; rw [hC, kset_prefix_eq_fan, if_pos (hC ▸ hc)]; rfl
      omega
    · have : Psi (A ⟨k, hk⟩) C = componentCount (insertionFan A k hk) + 1 := by
        unfold Psi; rw [hC, kset_prefix_eq_fan, if_neg (hC ▸ hc)]
      omega
  exact_mod_cast hle

theorem circle_not_subset_prefix {n : ℕ} {A : Arrangement n} (hA : IsGeneric A) (k : ℕ)
    (hk : k < n) :
    ¬ (A ⟨k, hk⟩).circle ⊆ occupied (prefixArrangement A k (Nat.le_of_lt hk)) := by
  intro hsub
  have hfinite : ((A ⟨k, hk⟩).circle).Finite := by
    have hU : (⋃ i ∈ previousIndices (⟨k, hk⟩ : Fin n),
        pairCrossingSet (A i) (A ⟨k, hk⟩)).Finite :=
      Set.Finite.biUnion (Finset.finite_toSet (previousIndices (⟨k, hk⟩ : Fin n)))
        (fun i hi => previous_pair_finite_of_isGeneric hA k hk i hi)
    refine Set.Finite.subset hU ?_
    intro x hx
    obtain ⟨i, hi⟩ := mem_occupied_iff.mp (hsub hx)
    have hi' : x ∈ (A ⟨i.1, i.2.trans_le (Nat.le_of_lt hk)⟩).carrier := hi
    have hmem : (⟨i.1, i.2.trans_le (Nat.le_of_lt hk)⟩ : Fin n) ∈
        previousIndices (⟨k, hk⟩ : Fin n) := (mem_previousIndices hk _).mpr i.2
    have hx' : x ∈ pairCrossingSet (A ⟨i.1, i.2.trans_le (Nat.le_of_lt hk)⟩) (A ⟨k, hk⟩) :=
      ⟨hi', Or.inl hx⟩
    exact Set.mem_biUnion hmem hx'
  have hinf : ((A ⟨k, hk⟩).circle).Infinite := by
    have h1 : (Set.Ico (0 : ℝ) (2 * Real.pi)).Infinite :=
      Set.Ico_infinite (by have := Real.pi_pos; linarith)
    have h2 := h1.image (HatAux.circlePt_injOn (A ⟨k, hk⟩))
    refine Set.Infinite.mono ?_ h2
    rintro _ ⟨θ, -, rfl⟩
    exact HatAux.circlePt_mem_circle _ θ
  exact hinf hfinite

theorem prefix_chain_exact {n : ℕ} {A : Arrangement n} (hA : IsGeneric A) (k : ℕ) (hk : k < n)
    (hk0 : 0 < k) :
    ∃ h : Insertion.ExactInsertionSplitChain (prefixArrangement A k (Nat.le_of_lt hk)) (A ⟨k, hk⟩),
      h.edgeCount = componentCount (insertionFan A k hk) := by
  set C := occupied (prefixArrangement A k (Nat.le_of_lt hk)) with hC
  have hCc : IsClosed C := OccupiedTopology.isClosed_occupied _
  have hfin : Finite (ConnectedComponents (Kset (A ⟨k, hk⟩) C)) := by
    rw [hC, kset_prefix_eq_fan]
    exact MainTheorem.finite_connectedComponents_insertionFan A k hk
  have hM : (A ⟨0, hk0.trans hk⟩).circle ⊆ C := fun x hx =>
    mem_occupied_iff.mpr ⟨⟨0, hk0⟩, Or.inl hx⟩
  obtain ⟨m, ⟨chain⟩, hm⟩ :=
    exists_exactChain (A ⟨k, hk⟩) hCc (arcConn_prefix A k hk) hM hfin
  refine ⟨⟨m, chain⟩, ?_⟩
  have hcirc := circle_not_subset_prefix hA k hk
  have : Psi (A ⟨k, hk⟩) C = componentCount (insertionFan A k hk) + 1 := by
    unfold Psi; rw [hC, kset_prefix_eq_fan, if_neg hcirc]
  show m = _
  omega

end Pieces
end EndToEnd
end Concrete
end Lollipop
