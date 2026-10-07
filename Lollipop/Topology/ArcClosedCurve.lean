import Lollipop.Lemma_8_5.Proof
import Lollipop.Topology.JordanBridge
import JordanCurveTheorem.SectionJ_PathConnectivity
import Mathlib.Tactic

/-!
# Closing two simple arcs into a Jordan curve

For the local crosscut topology step, the Jordan curve is usually obtained by
joining an inserted carrier edge to an old carrier arc with the same two
endpoints.  This file proves the reusable topological fact needed for that
construction: two simple arcs with the same distinct endpoints and no
intersection except those endpoints form a simple closed curve.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace ArcClosedCurve

open Set Function
open JordanCurveTheorem

/-- Two oppositely traversed simple arcs with only their endpoints in common
form a simple closed curve. -/
theorem isSimpleClosedCurve_union_of_two_arcs
    {A B : Set Point} {x z : Point}
    (hA : IsSimpleArcEnd A x z)
    (hB : IsSimpleArcEnd B x z)
    (_hxz : x ≠ z)
    (hinter : A ∩ B ⊆ {x, z}) :
    IsSimpleClosedCurve (A ∪ B) := by
  obtain ⟨f, rfl, hfcont, hfinj, hf0, hf1⟩ := hA
  obtain ⟨g, rfl, hgcont, hginj, hg0, hg1⟩ := hB
  let h : ℝ → Point := fun t =>
    if 2 * t ≤ 1 then f (2 * t) else g (2 - 2 * t)
  refine ⟨h, ?_, ?_, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · rintro y (hyf | hyg)
      · rcases hyf with ⟨s, hs, rfl⟩
        refine ⟨s / 2, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
        simp only [h]
        rw [show (2 : ℝ) * (s / 2) = s by ring, if_pos hs.2]
      · rcases hyg with ⟨s, hs, rfl⟩
        by_cases hs1 : s = 1
        · subst s
          refine ⟨(1 : ℝ) / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
          simp only [h]
          rw [show (2 : ℝ) * ((1 : ℝ) / 2) = 1 by ring,
            if_pos le_rfl, hf1, hg1]
        · refine ⟨(2 - s) / 2,
            ⟨by linarith [hs.2], by linarith [hs.1]⟩, ?_⟩
          have hslt : s < 1 := lt_of_le_of_ne hs.2 hs1
          simp only [h]
          rw [show (2 : ℝ) * ((2 - s) / 2) = 2 - s by ring,
            if_neg (by linarith : ¬(2 - s ≤ 1))]
          congr 1
          ring
    · rintro y ⟨t, ht, rfl⟩
      simp only [h]
      split_ifs with hleft
      · exact Or.inl ⟨2 * t, ⟨by linarith [ht.1], hleft⟩, rfl⟩
      · push Not at hleft
        exact Or.inr ⟨2 - 2 * t,
          ⟨by linarith [ht.2], by linarith⟩, rfl⟩
  · apply continuous_if_le
      (by fun_prop : Continuous fun (t : ℝ) => 2 * t)
      continuous_const
    · exact (hfcont.comp
        (by fun_prop : Continuous fun (t : ℝ) => 2 * t)).continuousOn
    · exact (hgcont.comp
        (by fun_prop : Continuous fun (t : ℝ) => 2 - 2 * t)).continuousOn
    · intro t ht
      show f (2 * t) = g (2 - 2 * t)
      have h2t : 2 * t = 1 := ht
      rw [h2t, hf1, show 2 - 1 = (1 : ℝ) by norm_num, hg1]
  · intro t₁ ht₁ t₂ ht₂ hht
    simp only [h] at hht
    by_cases h₁ : 2 * t₁ ≤ 1 <;> by_cases h₂ : 2 * t₂ ≤ 1
    · rw [if_pos h₁, if_pos h₂] at hht
      have heq := hfinj
        ⟨by linarith [ht₁.1], h₁⟩
        ⟨by linarith [ht₂.1], h₂⟩ hht
      linarith
    · rw [if_pos h₁, if_neg h₂] at hht
      push Not at h₂
      have hmemA : f (2 * t₁) ∈ f '' Icc (0 : ℝ) 1 :=
        ⟨2 * t₁, ⟨by linarith [ht₁.1], h₁⟩, rfl⟩
      have hmemB : f (2 * t₁) ∈ g '' Icc (0 : ℝ) 1 := by
        rw [hht]
        exact ⟨2 - 2 * t₂,
          ⟨by linarith [ht₂.2], by linarith⟩, rfl⟩
      have hend := hinter ⟨hmemA, hmemB⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hend
      rcases hend with hend | hend
      · have ht₁zero : 2 * t₁ = 0 :=
          hfinj ⟨by linarith [ht₁.1], h₁⟩
            (left_mem_Icc.mpr zero_le_one) (hend.trans hf0.symm)
        have ht₂one : 2 - 2 * t₂ = 0 :=
          hginj ⟨by linarith [ht₂.2], by linarith⟩
            (left_mem_Icc.mpr zero_le_one)
            (by rw [← hht, hend, hg0])
        linarith [ht₂.2]
      · have ht₁half : 2 * t₁ = 1 :=
          hfinj ⟨by linarith [ht₁.1], h₁⟩
            (right_mem_Icc.mpr zero_le_one) (hend.trans hf1.symm)
        have ht₂half : 2 - 2 * t₂ = 1 :=
          hginj ⟨by linarith [ht₂.2], by linarith⟩
            (right_mem_Icc.mpr zero_le_one)
            (by rw [← hht, hend, hg1])
        linarith
    · rw [if_neg h₁, if_pos h₂] at hht
      push Not at h₁
      have hmemB : g (2 - 2 * t₁) ∈ g '' Icc (0 : ℝ) 1 :=
        ⟨2 - 2 * t₁, ⟨by linarith [ht₁.2], by linarith⟩, rfl⟩
      have hmemA : g (2 - 2 * t₁) ∈ f '' Icc (0 : ℝ) 1 := by
        rw [hht]
        exact ⟨2 * t₂, ⟨by linarith [ht₂.1], h₂⟩, rfl⟩
      have hend := hinter ⟨hmemA, hmemB⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hend
      rcases hend with hend | hend
      · have ht₁one : 2 - 2 * t₁ = 0 :=
          hginj ⟨by linarith [ht₁.2], by linarith⟩
            (left_mem_Icc.mpr zero_le_one) (hend.trans hg0.symm)
        have ht₂zero : 2 * t₂ = 0 :=
          hfinj ⟨by linarith [ht₂.1], h₂⟩
            (left_mem_Icc.mpr zero_le_one)
            (by rw [← hht, hend, hf0])
        linarith [ht₁.2]
      · have ht₁half : 2 - 2 * t₁ = 1 :=
          hginj ⟨by linarith [ht₁.2], by linarith⟩
            (right_mem_Icc.mpr zero_le_one) (hend.trans hg1.symm)
        have ht₂half : 2 * t₂ = 1 :=
          hfinj ⟨by linarith [ht₂.1], h₂⟩
            (right_mem_Icc.mpr zero_le_one)
            (by rw [← hht, hend, hf1])
        linarith
    · rw [if_neg h₁, if_neg h₂] at hht
      push Not at h₁ h₂
      have heq := hginj
        ⟨by linarith [ht₁.2], by linarith⟩
        ⟨by linarith [ht₂.2], by linarith⟩ hht
      linarith
  · simp only [h]
    norm_num [hf0, hg0]

/-- The union in the preceding theorem has exactly two complementary
components. -/
theorem complement_componentCount_eq_two_of_two_arcs
    {A B : Set Point} {x z : Point}
    (hA : IsSimpleArcEnd A x z)
    (hB : IsSimpleArcEnd B x z)
    (hxz : x ≠ z)
    (hinter : A ∩ B ⊆ {x, z}) :
    componentCount ((A ∪ B)ᶜ) = 2 :=
  JordanBridge.jordan_complement_componentCount_eq_two
    (isSimpleClosedCurve_union_of_two_arcs hA hB hxz hinter)

end ArcClosedCurve
end EndToEnd
end Concrete
end Lollipop
