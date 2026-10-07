import Carrier.LocalSides
import Mathlib.Geometry.Euclidean.Inversion.Calculus

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace Pieces

open Set

/-- Statement of Task B1 (`local_sides_separated`), proved elsewhere. -/
def LocalSidesStmt : Prop :=
  ∀ {J R γ N N₁ N₂ : Set Point} {u v : Point},
    IsSimpleClosedCurve J → IsSimpleArcEnd R u v → J = R ∪ γ → Disjoint R γ →
    IsOpen N → N ∩ J = γ → IsPreconnected N₁ → IsPreconnected N₂ →
    N₁.Nonempty → N₂.Nonempty → N₁ ⊆ N \ J → N₂ ⊆ N \ J → N \ J ⊆ N₁ ∪ N₂ →
    ∀ n₁ ∈ N₁, ∀ n₂ ∈ N₂, n₂ ∉ connectedComponentIn Jᶜ n₁

namespace SphereSidesAux

/-- Inversion in the unit circle around `q`. -/
def ψ (q : Point) : Point → Point := EuclideanGeometry.inversion q 1

/-- Extension to the sphere, `∞ ↦ q`. -/
def Ψ (q : Point) (x : Sphere2) : Point := OnePoint.elim x q (ψ q)

lemma Ψ_infty (q : Point) : Ψ q infinity = q := rfl
lemma Ψ_fin (q p : Point) : Ψ q (finitePoint p) = ψ q p := rfl

lemma ψ_ψ (q x : Point) : ψ q (ψ q x) = x :=
  EuclideanGeometry.inversion_inversion q one_ne_zero x

lemma ψ_ne {q x : Point} (hx : x ≠ q) : ψ q x ≠ q := by
  intro h
  exact hx ((EuclideanGeometry.inversion_eq_center one_ne_zero).1 h)

lemma ψ_injOn (q : Point) : InjOn (ψ q) {q}ᶜ := by
  intro x _ y _ h
  have := congrArg (ψ q) h
  rwa [ψ_ψ, ψ_ψ] at this

lemma ψ_continuousAt {q x : Point} (hx : x ≠ q) : ContinuousAt (ψ q) x :=
  (continuousAt_const.inversion continuousAt_const continuousAt_id hx :
    ContinuousAt (fun a => EuclideanGeometry.inversion q (1:ℝ) a) x)

lemma ψ_continuousOn (q : Point) : ContinuousOn (ψ q) {q}ᶜ :=
  fun x hx => (ψ_continuousAt (q := q) hx).continuousWithinAt

lemma ψ_tendsto (q : Point) : Filter.Tendsto (ψ q) (Filter.cocompact Point) (nhds q) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have h1 : Filter.Tendsto (fun x : Point => dist x q) (Filter.cocompact Point) Filter.atTop :=
    tendsto_dist_right_cocompact_atTop q
  have h2 := tendsto_inv_atTop_zero.comp h1
  refine h2.congr (fun x => ?_)
  simp only [Function.comp, ψ]
  rw [EuclideanGeometry.dist_inversion_center]
  simp

lemma Ψ_continuousAt {q : Point} {x : Sphere2} (hx : x ≠ finitePoint q) :
    ContinuousAt (Ψ q) x := by
  induction x using OnePoint.rec with
  | infty =>
    rw [OnePoint.continuousAt_infty', Filter.coclosedCompact_eq_cocompact]
    exact ψ_tendsto q
  | coe p =>
    rw [OnePoint.continuousAt_coe]
    have hp : p ≠ q := fun h => hx (by rw [h]; rfl)
    exact ψ_continuousAt hp

lemma Ψ_injOn (q : Point) : InjOn (Ψ q) {finitePoint q}ᶜ := by
  intro x hx y hy h
  have hx' : x ≠ finitePoint q := hx
  have hy' : y ≠ finitePoint q := hy
  induction x using OnePoint.rec with
  | infty =>
    induction y using OnePoint.rec with
    | infty => rfl
    | coe b =>
      exfalso
      have hb : b ≠ q := fun h => hy' (by rw [h]; rfl)
      exact ψ_ne hb h.symm
  | coe a =>
    have ha : a ≠ q := fun h => hx' (by rw [h]; rfl)
    induction y using OnePoint.rec with
    | infty => exact absurd h (ψ_ne ha)
    | coe b =>
      have hb : b ≠ q := fun h => hy' (by rw [h]; rfl)
      exact congrArg _ (ψ_injOn q ha hb h)

lemma arc_image {q : Point} {A : Set Sphere2} {u v : Sphere2} (h : IsSphereArc A u v)
    (hq : finitePoint q ∉ A) : IsSimpleArcEnd (Ψ q '' A) (Ψ q u) (Ψ q v) := by
  obtain ⟨f, rfl, hc, hi, h0, h1⟩ := h
  let c : ℝ → ℝ := fun t => max 0 (min 1 t)
  have hcc : Continuous c := by fun_prop
  have hcmem : ∀ t, c t ∈ Icc (0:ℝ) 1 := fun t =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hcid : ∀ t ∈ Icc (0:ℝ) 1, c t = t := by
    intro t ht
    simp only [c]
    rw [min_eq_right ht.2, max_eq_right ht.1]
  have hne : ∀ t, f (c t) ≠ finitePoint q := fun t h' =>
    hq (h' ▸ ⟨c t, hcmem t, rfl⟩)
  refine ⟨fun t => Ψ q (f (c t)), ?_, ?_, ?_, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨t, ht, by simp only [hcid t ht]⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨f (c t), ⟨c t, hcmem t, rfl⟩, by simp only [hcid t ht]⟩
  · rw [continuous_iff_continuousAt]
    intro t
    exact ContinuousAt.comp (g := Ψ q) (f := fun t => f (c t)) (Ψ_continuousAt (hne t))
      (hc.comp hcc).continuousAt
  · intro a ha b hb hab
    have : f (c a) = f (c b) := Ψ_injOn q (hne a) (hne b) hab
    rw [hcid a ha, hcid b hb] at this
    exact hi ha hb this
  · show Ψ q (f (c 0)) = Ψ q u
    rw [hcid 0 ⟨le_rfl, zero_le_one⟩, h0]
  · show Ψ q (f (c 1)) = Ψ q v
    rw [hcid 1 ⟨zero_le_one, le_rfl⟩, h1]

end SphereSidesAux

open SphereSidesAux in
theorem sphere_local_sides_separated_of (hB1 : LocalSidesStmt)
    (q : Point) {R G : Set Sphere2} {u v : Sphere2} (huv : u ≠ v)
    (hR : IsSphereArc R u v) (hG : IsSphereArc G u v) (hRG : R ∩ G = {u, v})
    (hqR : finitePoint q ∉ R) (hqG : finitePoint q ∉ G)
    {N N₁ N₂ : Set Point} (hN : IsOpen N) (hqN : q ∉ N)
    (hNJ : finiteLift N ∩ (R ∪ G) = G \ {u, v})
    (hN₁ : IsPreconnected N₁) (hN₂ : IsPreconnected N₂)
    (hne₁ : N₁.Nonempty) (hne₂ : N₂.Nonempty)
    (hN₁N : N₁ ⊆ N) (hN₂N : N₂ ⊆ N)
    (hN₁J : ∀ p ∈ N₁, finitePoint p ∉ R ∪ G)
    (hN₂J : ∀ p ∈ N₂, finitePoint p ∉ R ∪ G)
    (hcov : ∀ p ∈ N, finitePoint p ∉ R ∪ G → p ∈ N₁ ∨ p ∈ N₂) :
    ∀ W : Set Point, IsPreconnected W → q ∉ W →
      (∀ p ∈ W, finitePoint p ∉ R ∪ G) →
      ∀ n₁ ∈ N₁, ∀ n₂ ∈ N₂, ¬ (n₁ ∈ W ∧ n₂ ∈ W) := by
  have huR : u ∈ R := by
    obtain ⟨f, rfl, _, _, h0, _⟩ := hR
    exact ⟨0, ⟨le_rfl, zero_le_one⟩, h0⟩
  have hvR : v ∈ R := by
    obtain ⟨f, rfl, _, _, _, h1⟩ := hR
    exact ⟨1, ⟨zero_le_one, le_rfl⟩, h1⟩
  have huG : u ∈ G := by
    obtain ⟨f, rfl, _, _, h0, _⟩ := hG
    exact ⟨0, ⟨le_rfl, zero_le_one⟩, h0⟩
  have hvG : v ∈ G := by
    obtain ⟨f, rfl, _, _, _, h1⟩ := hG
    exact ⟨1, ⟨zero_le_one, le_rfl⟩, h1⟩
  have hneRG : ∀ a ∈ R ∪ G, a ≠ finitePoint q := by
    intro a ha h
    rcases ha with ha | ha
    · exact hqR (h ▸ ha)
    · exact hqG (h ▸ ha)
  have hinj : ∀ a ∈ R ∪ G, ∀ b ∈ R ∪ G, Ψ q a = Ψ q b → a = b :=
    fun a ha b hb h => Ψ_injOn q (hneRG a ha) (hneRG b hb) h
  have hfin : ∀ p : Point, p ≠ q → finitePoint p ≠ finitePoint q :=
    fun p hp h => hp (finitePoint_injective h)
  -- the curve J'
  set J' : Set Point := Ψ q '' R ∪ Ψ q '' G with hJ'
  have hJ'mem : ∀ a ∈ R ∪ G, Ψ q a ∈ J' := by
    intro a ha
    rcases ha with ha | ha
    · exact Or.inl ⟨a, ha, rfl⟩
    · exact Or.inr ⟨a, ha, rfl⟩
  have hinJ : ∀ p : Point, p ≠ q → ψ q p ∈ J' → finitePoint p ∈ R ∪ G := by
    intro p hp hpJ
    have : ∃ a ∈ R ∪ G, Ψ q a = ψ q p := by
      rcases hpJ with ⟨a, ha, h⟩ | ⟨a, ha, h⟩
      · exact ⟨a, Or.inl ha, h⟩
      · exact ⟨a, Or.inr ha, h⟩
    obtain ⟨a, ha, h⟩ := this
    have : a = finitePoint p :=
      Ψ_injOn q (hneRG a ha) (hfin p hp) (by rw [h]; rfl)
    exact this ▸ ha
  have hΨuv : Ψ q u ≠ Ψ q v := fun h => huv (hinj u (Or.inl huR) v (Or.inl hvR) h)
  have hArcR := arc_image hR hqR
  have hArcG := arc_image hG hqG
  have hint : Ψ q '' R ∩ Ψ q '' G ⊆ {Ψ q u, Ψ q v} := by
    rintro y ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
    have : b = a := hinj b (Or.inr hb) a (Or.inl ha) hab
    subst this
    have hmem : b ∈ R ∩ G := ⟨ha, hb⟩
    rw [hRG] at hmem
    rcases hmem with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hJcurve : IsSimpleClosedCurve J' :=
    ArcClosedCurve.isSimpleClosedCurve_union_of_two_arcs hArcR hArcG hΨuv hint
  set γ' : Set Point := Ψ q '' (G \ {u, v}) with hγ'
  have hJγ : J' = Ψ q '' R ∪ γ' := by
    ext y
    constructor
    · rintro (h | ⟨b, hb, rfl⟩)
      · exact Or.inl h
      · by_cases hbuv : b ∈ ({u, v} : Set Sphere2)
        · rcases hbuv with rfl | rfl
          · exact Or.inl ⟨b, huR, rfl⟩
          · exact Or.inl ⟨b, hvR, rfl⟩
        · exact Or.inr ⟨b, ⟨hb, hbuv⟩, rfl⟩
    · rintro (h | ⟨b, hb, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨b, hb.1, rfl⟩
  have hdisj : Disjoint (Ψ q '' R) γ' := by
    rw [Set.disjoint_left]
    rintro y ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    have : b = a := hinj b (Or.inr hb.1) a (Or.inl ha) hab
    subst this
    have hmem : b ∈ R ∩ G := ⟨ha, hb.1⟩
    rw [hRG] at hmem
    exact hb.2 hmem
  -- inversion on open sets
  have hNq : ∀ S : Set Point, S ⊆ N → S ⊆ {q}ᶜ := fun S hS x hx h => hqN (h ▸ hS hx)
  have hcont : ∀ S : Set Point, S ⊆ N → ContinuousOn (ψ q) S :=
    fun S hS => (ψ_continuousOn q).mono (hNq S hS)
  have hopen : IsOpen (ψ q '' N) := by
    have : ψ q '' N = {q}ᶜ ∩ ψ q ⁻¹' N := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨ψ_ne (hNq N subset_rfl hx), ?_⟩
        show ψ q (ψ q x) ∈ N
        rw [ψ_ψ]; exact hx
      · rintro ⟨hy, hyN⟩
        exact ⟨ψ q y, hyN, ψ_ψ q y⟩
    rw [this]
    exact (ψ_continuousOn q).isOpen_inter_preimage isOpen_compl_singleton hN
  have hNJ' : ψ q '' N ∩ J' = γ' := by
    apply Set.Subset.antisymm
    · rintro y ⟨⟨p, hp, rfl⟩, hJy⟩
      have hpq : p ≠ q := hNq N subset_rfl hp
      have hfp := hinJ p hpq hJy
      have : finitePoint p ∈ G \ {u, v} := by
        rw [← hNJ]
        exact ⟨⟨p, hp, rfl⟩, hfp⟩
      exact ⟨finitePoint p, this, rfl⟩
    · rintro y ⟨b, hb, rfl⟩
      have hb' := hb
      rw [← hNJ] at hb'
      obtain ⟨⟨p, hp, rfl⟩, hbJ⟩ := hb'
      exact ⟨⟨p, hp, rfl⟩, hJ'mem _ hbJ⟩
  have hsub : ∀ (S : Set Point), S ⊆ N → (∀ p ∈ S, finitePoint p ∉ R ∪ G) →
      ψ q '' S ⊆ ψ q '' N \ J' := by
    intro S hS hSJ y ⟨p, hp, hpy⟩
    subst hpy
    refine ⟨⟨p, hS hp, rfl⟩, fun hJy => hSJ p hp (hinJ p (hNq N subset_rfl (hS hp)) hJy)⟩
  have hcov' : ψ q '' N \ J' ⊆ ψ q '' N₁ ∪ ψ q '' N₂ := by
    rintro y ⟨⟨p, hp, rfl⟩, hnJ⟩
    have hfp : finitePoint p ∉ R ∪ G := fun h => hnJ (hJ'mem _ h)
    rcases hcov p hp hfp with h | h
    · exact Or.inl ⟨p, h, rfl⟩
    · exact Or.inr ⟨p, h, rfl⟩
  unfold LocalSidesStmt at hB1
  have hmain := @hB1 J' (Ψ q '' R) γ' (ψ q '' N) (ψ q '' N₁) (ψ q '' N₂) (Ψ q u) (Ψ q v)
    hJcurve hArcR hJγ hdisj hopen hNJ'
    (hN₁.image _ (hcont N₁ hN₁N)) (hN₂.image _ (hcont N₂ hN₂N))
    (hne₁.image _) (hne₂.image _)
    (hsub N₁ hN₁N hN₁J) (hsub N₂ hN₂N hN₂J) hcov'
  rintro W hW hqW hWJ n₁ hn₁ n₂ hn₂ ⟨h1W, h2W⟩
  have hWq : W ⊆ {q}ᶜ := fun x hx h => hqW (h ▸ hx)
  have hWsub : ψ q '' W ⊆ J'ᶜ := by
    rintro y ⟨p, hp, rfl⟩ hJy
    exact hWJ p hp (hinJ p (hWq hp) hJy)
  have hWc : IsPreconnected (ψ q '' W) := hW.image _ ((ψ_continuousOn q).mono hWq)
  exact hmain (ψ q n₁) ⟨n₁, hn₁, rfl⟩ (ψ q n₂) ⟨n₂, hn₂, rfl⟩
    (hWc.subset_connectedComponentIn ⟨n₁, h1W, rfl⟩ hWsub ⟨n₂, h2W, rfl⟩)


theorem sphere_local_sides_separated
    (q : Point) {R G : Set Sphere2} {u v : Sphere2} (huv : u ≠ v)
    (hR : IsSphereArc R u v) (hG : IsSphereArc G u v) (hRG : R ∩ G = {u, v})
    (hqR : finitePoint q ∉ R) (hqG : finitePoint q ∉ G)
    {N N₁ N₂ : Set Point} (hN : IsOpen N) (hqN : q ∉ N)
    (hNJ : finiteLift N ∩ (R ∪ G) = G \ {u, v})
    (hN₁ : IsPreconnected N₁) (hN₂ : IsPreconnected N₂)
    (hne₁ : N₁.Nonempty) (hne₂ : N₂.Nonempty)
    (hN₁N : N₁ ⊆ N) (hN₂N : N₂ ⊆ N)
    (hN₁J : ∀ p ∈ N₁, finitePoint p ∉ R ∪ G)
    (hN₂J : ∀ p ∈ N₂, finitePoint p ∉ R ∪ G)
    (hcov : ∀ p ∈ N, finitePoint p ∉ R ∪ G → p ∈ N₁ ∨ p ∈ N₂) :
    ∀ W : Set Point, IsPreconnected W → q ∉ W →
      (∀ p ∈ W, finitePoint p ∉ R ∪ G) →
      ∀ n₁ ∈ N₁, ∀ n₂ ∈ N₂, ¬ (n₁ ∈ W ∧ n₂ ∈ W) :=
  sphere_local_sides_separated_of
    (fun {J R γ N N₁ N₂ u v} => local_sides_separated (J := J) (R := R) (γ := γ) (N := N) (N₁ := N₁) (N₂ := N₂) (u := u) (v := v))
    q huv hR hG hRG hqR hqG hN hqN hNJ hN₁ hN₂ hne₁ hne₂ hN₁N hN₂N hN₁J hN₂J hcov

end Pieces
end EndToEnd
end Concrete
end Lollipop
