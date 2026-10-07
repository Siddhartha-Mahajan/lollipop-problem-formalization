import Carrier.Defs
import Carrier.Defs2
import Carrier.CircleCollars
import Carrier.StemCollars
import Carrier.LocalSides
import Carrier.SphereArcs
import Carrier.SphereSides
import Carrier.HatArcs
import Carrier.Collar
import Carrier.Zarc
import Mathlib.Tactic

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace Pieces

open Set

namespace CoreAux

theorem arc_ne {A : Set Sphere2} {x y : Sphere2} (h : IsSphereArc A x y) : x ≠ y := by
  obtain ⟨f, rfl, _, hi, h0, h1⟩ := h
  intro hxy
  have := hi (⟨le_rfl, zero_le_one⟩ : (0:ℝ) ∈ Icc (0:ℝ) 1) (⟨zero_le_one, le_rfl⟩ : (1:ℝ) ∈ Icc (0:ℝ) 1)
    (h0.trans (hxy.trans h1.symm))
  norm_num at this

theorem arc_left_mem {A : Set Sphere2} {x y : Sphere2} (h : IsSphereArc A x y) : x ∈ A := by
  obtain ⟨f, rfl, _, _, h0, _⟩ := h
  exact ⟨0, ⟨le_rfl, zero_le_one⟩, h0⟩

theorem arc_right_mem {A : Set Sphere2} {x y : Sphere2} (h : IsSphereArc A x y) : y ∈ A := by
  obtain ⟨f, rfl, _, _, _, h1⟩ := h
  exact ⟨1, ⟨zero_le_one, le_rfl⟩, h1⟩

/-- Generic reduction to `sphere_local_sides_separated`. -/
theorem core_gen {D : Set Point} {Ehat R G : Set Sphere2} {u v : Sphere2} (huv : u ≠ v)
    (hR : IsSphereArc R u v) (hG : IsSphereArc G u v) (hRG : R ∩ G = {u, v})
    {q : Point} (hqD : q ∈ D) (hqJ : finitePoint q ∉ R ∪ G)
    (hJ : ∀ p : Point, finitePoint p ∈ R ∪ G → p ∈ D ∨ finitePoint p ∈ Ehat)
    (hEJ : ∀ p : Point, finitePoint p ∈ Ehat → finitePoint p ∈ R ∪ G)
    {N N₁ N₂ : Set Point} (hN : IsOpen N) (hND : N ⊆ Dᶜ)
    (hNJ : finiteLift N ∩ (R ∪ G) = G \ {u, v})
    (hN₁ : IsPreconnected N₁) (hN₂ : IsPreconnected N₂)
    (hne₁ : N₁.Nonempty) (hne₂ : N₂.Nonempty)
    (hN₁N : N₁ ⊆ N) (hN₂N : N₂ ⊆ N)
    (hN₁E : ∀ p ∈ N₁, finitePoint p ∉ Ehat)
    (hN₂E : ∀ p ∈ N₂, finitePoint p ∉ Ehat)
    (hcov : ∀ p ∈ N, finitePoint p ∉ Ehat → p ∈ N₁ ∨ p ∈ N₂) :
    ∀ n₁ ∈ N₁, ∀ n₂ ∈ N₂,
      n₂ ∉ connectedComponentIn ((D ∪ {x | finitePoint x ∈ Ehat})ᶜ) n₁ := by
  intro n₁ hn₁ n₂ hn₂ hmem
  have hqN : q ∉ N := fun h => hND h hqD
  have hqR : finitePoint q ∉ R := fun h => hqJ (Or.inl h)
  have hqG : finitePoint q ∉ G := fun h => hqJ (Or.inr h)
  have hNJ' : ∀ p ∈ N, ∀ _ : finitePoint p ∉ Ehat, finitePoint p ∉ R ∪ G := by
    intro p hp hpE hpJ
    rcases hJ p hpJ with h | h
    · exact hND hp h
    · exact hpE h
  have hN₁J : ∀ p ∈ N₁, finitePoint p ∉ R ∪ G := fun p hp => hNJ' p (hN₁N hp) (hN₁E p hp)
  have hN₂J : ∀ p ∈ N₂, finitePoint p ∉ R ∪ G := fun p hp => hNJ' p (hN₂N hp) (hN₂E p hp)
  have hcovJ : ∀ p ∈ N, finitePoint p ∉ R ∪ G → p ∈ N₁ ∨ p ∈ N₂ := by
    intro p hp hpJ
    exact hcov p hp (fun h => hpJ (hEJ p h))
  have key := sphere_local_sides_separated q huv hR hG hRG hqR hqG hN hqN hNJ hN₁ hN₂ hne₁ hne₂
    hN₁N hN₂N hN₁J hN₂J hcovJ
  set S : Set Point := (D ∪ {x | finitePoint x ∈ Ehat})ᶜ with hS
  have hn₁S : n₁ ∈ S := by
    intro h
    rcases h with h | h
    · exact hND (hN₁N hn₁) h
    · exact hN₁E n₁ hn₁ h
  have hWsub : connectedComponentIn S n₁ ⊆ S := connectedComponentIn_subset _ _
  refine key (connectedComponentIn S n₁) isPreconnected_connectedComponentIn ?_ ?_ n₁ hn₁ n₂ hn₂
    ⟨mem_connectedComponentIn hn₁S, hmem⟩
  · intro h
    exact hWsub h (Or.inl hqD)
  · intro p hp hpJ
    have hpS := hWsub hp
    rcases hJ p hpJ with h | h
    · exact hpS (Or.inl h)
    · exact hpS (Or.inr h)

end CoreAux

open CoreAux in
theorem exact_sides_core
    {D : Set Point} (hD : IsClosed D) (hArc : ArcConn D) {M : Lollipop}
    (hM : M.circle ⊆ D)
    {Ehat A₁ G A₂ : Set Sphere2} {a u v b : Sphere2}
    (hA₁ : IsSphereArc A₁ a u) (hG : IsSphereArc G u v) (hA₂ : IsSphereArc A₂ v b)
    (hab : a ≠ b)
    (hEhat : Ehat = A₁ ∪ G ∪ A₂)
    (hA₁G : A₁ ∩ G = {u}) (hGA₂ : G ∩ A₂ = {v}) (hA₁A₂ : A₁ ∩ A₂ = ∅)
    (hED : Ehat ∩ hatSet D = {a, b})
    {N N₁ N₂ : Set Point} (hN : IsOpen N) (hND : N ⊆ Dᶜ)
    (hNE : finiteLift N ∩ Ehat = G \ {u, v})
    (hN₁ : IsPreconnected N₁) (hN₂ : IsPreconnected N₂)
    (hne₁ : N₁.Nonempty) (hne₂ : N₂.Nonempty)
    (hN₁N : N₁ ⊆ N) (hN₂N : N₂ ⊆ N)
    (hN₁E : ∀ p ∈ N₁, finitePoint p ∉ Ehat)
    (hN₂E : ∀ p ∈ N₂, finitePoint p ∉ Ehat)
    (hcov : ∀ p ∈ N, finitePoint p ∉ Ehat → p ∈ N₁ ∨ p ∈ N₂) :
    ∀ n₁ ∈ N₁, ∀ n₂ ∈ N₂,
      n₂ ∉ connectedComponentIn ((D ∪ {x | finitePoint x ∈ Ehat})ᶜ) n₁ := by
  have huv : u ≠ v := arc_ne hG
  have hau : a ≠ u := arc_ne hA₁
  have hvb : v ≠ b := arc_ne hA₂
  have haA₁ : a ∈ A₁ := arc_left_mem hA₁
  have huA₁ : u ∈ A₁ := arc_right_mem hA₁
  have hvA₂ : v ∈ A₂ := arc_left_mem hA₂
  have hbA₂ : b ∈ A₂ := arc_right_mem hA₂
  have huG : u ∈ G := arc_left_mem hG
  have hvG : v ∈ G := arc_right_mem hG
  have hA₁E : A₁ ⊆ Ehat := by
    intro x hx; rw [hEhat]; exact Or.inl (Or.inl hx)
  have hGE : G ⊆ Ehat := by
    intro x hx; rw [hEhat]; exact Or.inl (Or.inr hx)
  have hA₂E : A₂ ⊆ Ehat := by
    intro x hx; rw [hEhat]; exact Or.inr hx
  have hinfD : infinity ∈ hatSet D := Or.inr rfl
  have haED : a ∈ Ehat ∩ hatSet D := by rw [hED]; exact Or.inl rfl
  have hbED : b ∈ Ehat ∩ hatSet D := by rw [hED]; exact Or.inr rfl
  have haD : a ∈ hatSet D := haED.2
  have hbD : b ∈ hatSet D := hbED.2
  have haA₂ : a ∉ A₂ := fun h => by
    have : a ∈ A₁ ∩ A₂ := ⟨haA₁, h⟩
    rw [hA₁A₂] at this; exact this
  have hbA₁ : b ∉ A₁ := fun h => by
    have : b ∈ A₁ ∩ A₂ := ⟨h, hbA₂⟩
    rw [hA₁A₂] at this; exact this
  obtain ⟨P, hPD, hP⟩ := sphereArc_merge (X := hatSet D) hArc hinfD hbD haD hab.symm
  have hPE : ∀ x ∈ P, x ∈ Ehat → x = a ∨ x = b := by
    intro x hx hxE
    have : x ∈ Ehat ∩ hatSet D := ⟨hxE, hPD hx⟩
    rw [hED] at this
    rcases this with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hbP : b ∈ P := arc_left_mem hP
  have haP : a ∈ P := arc_right_mem hP
  have h1 : A₂ ∩ P = {b} := by
    ext x
    constructor
    · rintro ⟨hx2, hxP⟩
      rcases hPE x hxP (hA₂E hx2) with h | h
      · subst h; exact absurd hx2 haA₂
      · exact h
    · intro h
      rw [mem_singleton_iff] at h; subst h
      exact ⟨hbA₂, hbP⟩
  have hAP : IsSphereArc (A₂ ∪ P) v a := hA₂.trans hP h1
  have h2 : (A₂ ∪ P) ∩ A₁ = {a} := by
    ext x
    constructor
    · rintro ⟨hx | hx, hx1⟩
      · exfalso
        have : x ∈ A₁ ∩ A₂ := ⟨hx1, hx⟩
        rw [hA₁A₂] at this; exact this
      · rcases hPE x hx (hA₁E hx1) with h | h
        · exact h
        · subst h; exact absurd hx1 hbA₁
    · intro h
      rw [mem_singleton_iff] at h; subst h
      exact ⟨Or.inr haP, haA₁⟩
  have hRv : IsSphereArc ((A₂ ∪ P) ∪ A₁) v u := hAP.trans hA₁ h2
  have hR : IsSphereArc ((A₂ ∪ P) ∪ A₁) u v := hRv.symm
  have hRG : ((A₂ ∪ P) ∪ A₁) ∩ G = {u, v} := by
    ext x
    constructor
    · rintro ⟨(hx | hx) | hx, hxG⟩
      · right
        have : x ∈ G ∩ A₂ := ⟨hxG, hx⟩
        rw [hGA₂] at this; exact this
      · exfalso
        rcases hPE x hx (hGE hxG) with h | h
        · subst h
          have : x ∈ A₁ ∩ G := ⟨haA₁, hxG⟩
          rw [hA₁G] at this
          exact hau this
        · subst h
          have : x ∈ G ∩ A₂ := ⟨hxG, hbA₂⟩
          rw [hGA₂] at this
          exact hvb this.symm
      · left
        have : x ∈ A₁ ∩ G := ⟨hx, hxG⟩
        rw [hA₁G] at this; exact this
    · rintro (h | h)
      · subst h; exact ⟨Or.inr huA₁, huG⟩
      · subst h; exact ⟨Or.inl (Or.inl hvA₂), hvG⟩
  -- choose q
  have hnc := sphereArc_not_contains_circle hP M
  obtain ⟨q, hqC, hqP⟩ : ∃ q ∈ M.circle, finitePoint q ∉ P := by
    by_contra hcon
    push Not at hcon
    exact hnc (by rintro x ⟨q, hq, rfl⟩; exact hcon q hq)
  have hqD : q ∈ D := hM hqC
  have hqhat : finitePoint q ∈ hatSet D := Or.inl ⟨q, hqD, rfl⟩
  have hqE : finitePoint q ∉ Ehat := by
    intro h
    have : finitePoint q ∈ Ehat ∩ hatSet D := ⟨h, hqhat⟩
    rw [hED] at this
    rcases this with h | h
    · exact hqP (h ▸ haP)
    · exact hqP (h ▸ hbP)
  have hqJ : finitePoint q ∉ ((A₂ ∪ P) ∪ A₁) ∪ G := by
    rintro (((h | h) | h) | h)
    · exact hqE (hA₂E h)
    · exact hqP h
    · exact hqE (hA₁E h)
    · exact hqE (hGE h)
  have hPfin : ∀ p : Point, finitePoint p ∈ P → p ∈ D := by
    intro p hp
    rcases hPD hp with ⟨y, hy, hyp⟩ | h
    · exact finitePoint_injective hyp ▸ hy
    · exact absurd h (finitePoint_ne_infinity p)
  refine core_gen huv hR hG hRG hqD hqJ ?_ ?_ hN hND ?_ hN₁ hN₂ hne₁ hne₂ hN₁N hN₂N hN₁E hN₂E hcov
  · intro p hp
    rcases hp with ((h | h) | h) | h
    · exact Or.inr (hA₂E h)
    · exact Or.inl (hPfin p h)
    · exact Or.inr (hA₁E h)
    · exact Or.inr (hGE h)
  · intro p hp
    rw [hEhat] at hp
    rcases hp with (h | h) | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
    · exact Or.inl (Or.inl (Or.inl h))
  · rw [← hNE]
    ext x
    constructor
    · rintro ⟨hxN, hxJ⟩
      refine ⟨hxN, ?_⟩
      obtain ⟨n, hn, rfl⟩ := hxN
      rcases hxJ with ((h | h) | h) | h
      · exact hA₂E h
      · exact absurd (hPfin n h) (hND hn)
      · exact hA₁E h
      · exact hGE h
    · rintro ⟨hxN, hxE⟩
      refine ⟨hxN, ?_⟩
      rw [hEhat] at hxE
      rcases hxE with (h | h) | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
      · exact Or.inl (Or.inl (Or.inl h))

theorem exact_sides_loop_core
    {D : Set Point} (hD : IsClosed D) {M : Lollipop} (hM : M.circle ⊆ D)
    {Ehat G R : Set Sphere2} {a u v : Sphere2}
    (hG : IsSphereArc G u v) (hR : IsSphereArc R u v) (huv : u ≠ v)
    (hEhat : Ehat = G ∪ R) (hGR : G ∩ R = {u, v})
    (hED : Ehat ∩ hatSet D = {a})
    {N N₁ N₂ : Set Point} (hN : IsOpen N) (hND : N ⊆ Dᶜ)
    (hNE : finiteLift N ∩ Ehat = G \ {u, v})
    (hN₁ : IsPreconnected N₁) (hN₂ : IsPreconnected N₂)
    (hne₁ : N₁.Nonempty) (hne₂ : N₂.Nonempty)
    (hN₁N : N₁ ⊆ N) (hN₂N : N₂ ⊆ N)
    (hN₁E : ∀ p ∈ N₁, finitePoint p ∉ Ehat)
    (hN₂E : ∀ p ∈ N₂, finitePoint p ∉ Ehat)
    (hcov : ∀ p ∈ N, finitePoint p ∉ Ehat → p ∈ N₁ ∨ p ∈ N₂) :
    ∀ n₁ ∈ N₁, ∀ n₂ ∈ N₂,
      n₂ ∉ connectedComponentIn ((D ∪ {x | finitePoint x ∈ Ehat})ᶜ) n₁ := by
  have hRG : R ∩ G = {u, v} := by rw [inter_comm]; exact hGR
  -- a circle point different from `a`
  obtain ⟨q, hqC, hqa⟩ : ∃ q ∈ M.circle, finitePoint q ≠ a := by
    have hr : M.radial ≠ 0 := M.radial_ne_zero
    have h1 : M.center + M.radial ∈ M.circle := by
      simp [Lollipop.circle, Lollipop.radius]
    have h2 : M.center - M.radial ∈ M.circle := by
      simp [Lollipop.circle, Lollipop.radius]
    by_cases h : finitePoint (M.center + M.radial) = a
    · refine ⟨M.center - M.radial, h2, fun h' => ?_⟩
      have h3 := finitePoint_injective (h.trans h'.symm)
      have h4 : M.radial = -M.radial :=
        add_left_cancel (a := M.center) (h3.trans (sub_eq_add_neg _ _))
      have h5 : (2:ℝ) • M.radial = 0 := by
        rw [two_smul]; nth_rewrite 2 [h4]; exact add_neg_cancel _
      rcases smul_eq_zero.mp h5 with h6 | h6
      · norm_num at h6
      · exact hr h6
    · exact ⟨_, h1, h⟩
  have hqD : q ∈ D := hM hqC
  have hqhat : finitePoint q ∈ hatSet D := Or.inl ⟨q, hqD, rfl⟩
  have hqE : finitePoint q ∉ Ehat := by
    intro h
    have : finitePoint q ∈ Ehat ∩ hatSet D := ⟨h, hqhat⟩
    rw [hED] at this
    exact hqa this
  have hqJ : finitePoint q ∉ R ∪ G := by
    rintro (h | h)
    · exact hqE (by rw [hEhat]; exact Or.inr h)
    · exact hqE (by rw [hEhat]; exact Or.inl h)
  refine CoreAux.core_gen huv hR hG hRG hqD hqJ ?_ ?_ hN hND ?_ hN₁ hN₂ hne₁ hne₂ hN₁N hN₂N hN₁E hN₂E hcov
  · intro p hp
    right
    rw [hEhat]
    rcases hp with h | h
    · exact Or.inr h
    · exact Or.inl h
  · intro p hp
    rw [hEhat] at hp
    rcases hp with h | h
    · exact Or.inr h
    · exact Or.inl h
  · rw [← hNE, hEhat, union_comm]


end Pieces
end EndToEnd
end Concrete
end Lollipop
