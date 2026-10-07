import Lollipop.Lemma_8_5.Proof
import Lollipop.Topology.Carrier.Defs

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace Pieces

open Set


theorem local_sides_separated
    {J R γ N N₁ N₂ : Set Point} {u v : Point}
    (hJ : IsSimpleClosedCurve J)
    (hR : IsSimpleArcEnd R u v)
    (hJR : J = R ∪ γ) (hRγ : Disjoint R γ)
    (hN : IsOpen N) (hNJ : N ∩ J = γ)
    (hN₁ : IsPreconnected N₁) (hN₂ : IsPreconnected N₂)
    (hne₁ : N₁.Nonempty) (hne₂ : N₂.Nonempty)
    (hN₁sub : N₁ ⊆ N \ J) (hN₂sub : N₂ ⊆ N \ J)
    (hcov : N \ J ⊆ N₁ ∪ N₂) :
    ∀ n₁ ∈ N₁, ∀ n₂ ∈ N₂, n₂ ∉ connectedComponentIn Jᶜ n₁ := by
  intro n₁ hn₁ n₂ hn₂ hcomp
  obtain ⟨A, B, hAo, hBo, hAc, hBc, hAB, hAJ, hBJ, hcover⟩ :=
    JordanCurveTheorem.jordan_curve_theorem hJ
  -- every off-J point is in A or B
  have hoff : ∀ x, x ∉ J → x ∈ A ∨ x ∈ B := by
    intro x hx
    have : x ∈ A ∪ B ∪ J := by rw [hcover]; trivial
    rcases this with (h | h) | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hx
  have hAoff : ∀ x ∈ A, x ∉ J := fun x hx hxJ => Set.disjoint_left.mp hAJ hx hxJ
  have hBoff : ∀ x ∈ B, x ∉ J := fun x hx hxJ => Set.disjoint_left.mp hBJ hx hxJ
  -- a preconnected subset of Jᶜ lies in A or B
  have side : ∀ S : Set Point, IsPreconnected S → S ⊆ Jᶜ → S ⊆ A ∨ S ⊆ B := by
    intro S hS hSJ
    have hsub : S ⊆ A ∪ B := fun x hx => hoff x (hSJ hx)
    have hdisj : S ∩ (A ∩ B) = ∅ := by
      rw [Set.disjoint_iff_inter_eq_empty.mp hAB]; simp
    exact (isPreconnected_iff_subset_of_disjoint.mp hS) A B hAo hBo hsub hdisj
  have h1 := side N₁ hN₁ (fun x hx => (hN₁sub hx).2)
  have h2 := side N₂ hN₂ (fun x hx => (hN₂sub hx).2)
  -- component lies in one side
  have hcompside : connectedComponentIn Jᶜ n₁ ⊆ A ∨ connectedComponentIn Jᶜ n₁ ⊆ B := by
    apply side
    · exact isPreconnected_connectedComponentIn
    · exact connectedComponentIn_subset _ _
  have hn₁J : n₁ ∈ Jᶜ := (hN₁sub hn₁).2
  have hn₁mem : n₁ ∈ connectedComponentIn Jᶜ n₁ := mem_connectedComponentIn hn₁J
  -- Case analysis
  have key : ∀ (S T : Set Point), IsOpen S → IsOpen T → IsConnected T → Disjoint S T →
      (∀ x ∈ S, x ∉ J) → (∀ x ∈ T, x ∉ J) → (∀ x, x ∉ J → x ∈ S ∨ x ∈ T) →
      N₁ ⊆ S → N₂ ⊆ S → False := by
    intro S T hSo hTo hTc hST hSJ hTJ hoffST hS₁ hS₂
    have hNT : N ∩ T = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hxN, hxT⟩
      have : x ∈ N₁ ∪ N₂ := hcov ⟨hxN, hTJ x hxT⟩
      rcases this with h | h
      · exact Set.disjoint_left.mp hST (hS₁ h) hxT
      · exact Set.disjoint_left.mp hST (hS₂ h) hxT
    have hNsub : N ⊆ S ∪ γ := by
      intro x hxN
      by_cases hxJ : x ∈ J
      · right; rw [← hNJ]; exact ⟨hxN, hxJ⟩
      · left
        have : x ∈ N₁ ∪ N₂ := hcov ⟨hxN, hxJ⟩
        rcases this with h | h
        · exact hS₁ h
        · exact hS₂ h
    have hγN : γ ⊆ N := by rw [← hNJ]; exact Set.inter_subset_left
    have hγJ : γ ⊆ J := by rw [← hNJ]; exact Set.inter_subset_right
    have hVo : IsOpen (S ∪ γ) := by
      rw [isOpen_iff_mem_nhds]
      intro x hx
      rcases hx with hx | hx
      · exact Filter.mem_of_superset (hSo.mem_nhds hx) subset_union_left
      · exact Filter.mem_of_superset (hN.mem_nhds (hγN hx)) hNsub
    have hRc : Rᶜ = (S ∪ γ) ∪ T := by
      ext x
      simp only [mem_compl_iff, mem_union]
      constructor
      · intro hxR
        by_cases hxJ : x ∈ J
        · left; right
          rw [hJR] at hxJ
          rcases hxJ with h | h
          · exact absurd h hxR
          · exact h
        · rcases hoffST x hxJ with h | h
          · left; left; exact h
          · right; exact h
      · intro h hxR
        have hxJ : x ∈ J := by rw [hJR]; left; exact hxR
        rcases h with (h | h) | h
        · exact hSJ x h hxJ
        · exact Set.disjoint_left.mp hRγ hxR h
        · exact hTJ x h hxJ
    have hSne : (S ∪ γ).Nonempty := ⟨n₁, Or.inl (hS₁ hn₁)⟩
    have hconn : IsPreconnected Rᶜ :=
      (SimpleArcComplement.isConnected_compl_simpleArc
        (isSimpleArcEnd_isSimpleArc hR)).isPreconnected
    have hdis : Rᶜ ∩ ((S ∪ γ) ∩ T) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨-, ⟨hxV, hxT⟩⟩
      rcases hxV with h | h
      · exact Set.disjoint_left.mp hST h hxT
      · exact hTJ x hxT (hγJ h)
    rcases (isPreconnected_iff_subset_of_disjoint.mp hconn) (S ∪ γ) T hVo hTo
        (by rw [hRc]) hdis with h | h
    · -- Rᶜ ⊆ S ∪ γ, but T ⊆ Rᶜ nonempty and disjoint from S ∪ γ
      obtain ⟨t, ht⟩ := hTc.nonempty
      have : t ∈ Rᶜ := by rw [hRc]; exact Or.inr ht
      have := h this
      rcases this with h' | h'
      · exact Set.disjoint_left.mp hST h' ht
      · exact hTJ t ht (hγJ h')
    · obtain ⟨s, hs⟩ := hSne
      have : s ∈ Rᶜ := by rw [hRc]; exact Or.inl hs
      have := h this
      rcases hs with h' | h'
      · exact Set.disjoint_left.mp hST h' this
      · exact hTJ s this (hγJ h')
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact key A B hAo hBo hBc hAB hAoff hBoff hoff h1 h2
  · -- N₁ ⊆ A, N₂ ⊆ B
    have : connectedComponentIn Jᶜ n₁ ⊆ A := by
      rcases hcompside with h | h
      · exact h
      · exact absurd (h hn₁mem) (fun hb => Set.disjoint_left.mp hAB (h1 hn₁) hb)
    exact Set.disjoint_left.mp hAB (this hcomp) (h2 hn₂)
  · have : connectedComponentIn Jᶜ n₁ ⊆ B := by
      rcases hcompside with h | h
      · exact absurd (h hn₁mem) (fun hb => Set.disjoint_left.mp hAB hb (h1 hn₁))
      · exact h
    exact Set.disjoint_left.mp hAB (h2 hn₂) (this hcomp)
  · exact key B A hBo hAo hAc hAB.symm hBoff hAoff
      (fun x hx => (hoff x hx).symm) h1 h2

#print axioms local_sides_separated


end Pieces
end EndToEnd
end Concrete
end Lollipop
