import old_lean_folder.Concrete.EndToEnd.LocalFiltration
import Mathlib.Tactic

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace Collar

open Set Function

/-- **Two-collar lemma.**  Let `O` be a face of the closed set `D`, `E` closed,
and suppose a point of `E` lies in `O`.  If an open set `U` contains `E ∩ O`
and `U ∩ O \ E` is covered by two preconnected sets `S₁ S₂` avoiding `D ∪ E`,
then every point of `O \ E` lies in the same component of `(D ∪ E)ᶜ` as a point
of `S₁` or of `S₂`. -/
theorem exists_collar_point_in_component
    {D E U S₁ S₂ : Set Point} (hD : IsClosed D) (hE : IsClosed E)
    {z₀ : Point} (hz₀E : z₀ ∈ E) (hz₀D : z₀ ∉ D)
    (hU : IsOpen U)
    (hEU : ∀ z ∈ E, z ∈ connectedComponentIn Dᶜ z₀ → z ∈ U)
    (hS₁ : IsPreconnected S₁) (hS₂ : IsPreconnected S₂)
    (hS₁K : S₁ ⊆ (D ∪ E)ᶜ) (hS₂K : S₂ ⊆ (D ∪ E)ᶜ)
    (hcover : ∀ x ∈ U, x ∈ connectedComponentIn Dᶜ z₀ → x ∉ E →
      x ∈ S₁ ∨ x ∈ S₂)
    {y : Point} (hyO : y ∈ connectedComponentIn Dᶜ z₀) (hyE : y ∉ E) :
    (∃ s ∈ S₁, s ∈ connectedComponentIn (D ∪ E)ᶜ y) ∨
      (∃ s ∈ S₂, s ∈ connectedComponentIn (D ∪ E)ᶜ y) := by
  set O : Set Point := connectedComponentIn Dᶜ z₀ with hOdef
  set K : Set Point := D ∪ E with hKdef
  have hKclosed : IsClosed K := hD.union hE
  have hKopen : IsOpen Kᶜ := hKclosed.isOpen_compl
  have hDopen : IsOpen Dᶜ := hD.isOpen_compl
  have hOopen : IsOpen O := IsOpen.connectedComponentIn hDopen
  have hOpre : IsPreconnected O := isPreconnected_connectedComponentIn
  have hz₀O : z₀ ∈ O := mem_connectedComponentIn (by simpa using hz₀D)
  have hyD : y ∉ D := fun h => (connectedComponentIn_subset Dᶜ z₀ hyO) h
  have hyK : y ∈ Kᶜ := by
    intro h
    rcases h with h | h
    · exact hyD h
    · exact hyE h
  set W : Set Point := connectedComponentIn Kᶜ y with hWdef
  have hWopen : IsOpen W := IsOpen.connectedComponentIn hKopen
  have hWpre : IsPreconnected W := isPreconnected_connectedComponentIn
  have hyW : y ∈ W := mem_connectedComponentIn hyK
  have hWK : W ⊆ Kᶜ := connectedComponentIn_subset Kᶜ y
  have hKD : Kᶜ ⊆ Dᶜ := fun x hx hxD => hx (Or.inl hxD)
  -- W lies in O
  have hWO : W ⊆ O := by
    have h1 : W ⊆ connectedComponentIn Dᶜ y :=
      hWpre.subset_connectedComponentIn hyW (hWK.trans hKD)
    have h2 : connectedComponentIn Dᶜ z₀ = connectedComponentIn Dᶜ y :=
      connectedComponentIn_eq hyO
    rw [hOdef, h2]
    exact h1
  -- a boundary point of W inside E ∩ O
  have hbdry : ∃ y' ∈ E, y' ∈ closure W ∧ y' ∈ O := by
    by_contra hnone
    push Not at hnone
    have hcl : closure W ∩ O ⊆ W := by
      intro y' hy'
      obtain ⟨hy'cl, hy'O⟩ := hy'
      have hy'E : y' ∉ E := fun hE' => by
        have := hnone y' hE' hy'cl
        exact this hy'O
      have hy'D : y' ∉ D := fun h => (connectedComponentIn_subset Dᶜ z₀ hy'O) h
      have hy'K : y' ∈ Kᶜ := by
        intro h
        rcases h with h | h
        · exact hy'D h
        · exact hy'E h
      set W' : Set Point := connectedComponentIn Kᶜ y' with hW'
      have hW'open : IsOpen W' := IsOpen.connectedComponentIn hKopen
      have hy'W' : y' ∈ W' := mem_connectedComponentIn hy'K
      obtain ⟨w, hwW', hwW⟩ := mem_closure_iff.mp hy'cl W' hW'open hy'W'
      have hweq : connectedComponentIn Kᶜ y = connectedComponentIn Kᶜ w :=
        connectedComponentIn_eq hwW
      have hweq' : connectedComponentIn Kᶜ y' = connectedComponentIn Kᶜ w :=
        connectedComponentIn_eq hwW'
      have : W' = W := by rw [hW', hWdef, hweq', hweq]
      rw [← this]
      exact hy'W'
    have hOW : O ⊆ W :=
      hOpre.subset_of_closure_inter_subset hWopen ⟨y, hWO hyW, hyW⟩ hcl
    have hz₀W : z₀ ∈ W := hOW hz₀O
    exact (hWK hz₀W) (Or.inr hz₀E)
  obtain ⟨y', hy'E, hy'cl, hy'O⟩ := hbdry
  have hy'U : y' ∈ U := hEU y' hy'E hy'O
  obtain ⟨w, hwU, hwW⟩ := mem_closure_iff.mp hy'cl U hU hy'U
  have hwO : w ∈ O := hWO hwW
  have hwE : w ∉ E := fun h => (hWK hwW) (Or.inr h)
  rcases hcover w hwU hwO hwE with h1 | h2
  · exact Or.inl ⟨w, h1, hwW⟩
  · exact Or.inr ⟨w, h2, hwW⟩


/-- Membership in a relative connected component gives equality in the
connected-component quotient of the subtype. -/
theorem mk_eq_of_mem_connectedComponentIn {F : Set Point} {x y : Point}
    (hx : x ∈ F) (hy : y ∈ connectedComponentIn F x) :
    ConnectedComponents.mk (⟨y, connectedComponentIn_subset F x hy⟩ : F) =
      ConnectedComponents.mk (⟨x, hx⟩ : F) := by
  rw [connectedComponentIn_eq_image hx] at hy
  obtain ⟨w, hw, hwy⟩ := hy
  have hw' : w = ⟨y, connectedComponentIn_subset F x
      (by rw [connectedComponentIn_eq_image hx]; exact ⟨w, hw, hwy⟩)⟩ :=
    Subtype.ext hwy
  rw [← hw']
  exact ConnectedComponents.coe_eq_coe'.mpr hw

/-- Two-valued classifier: `0` on the component containing the first collar. -/
def collarClassifier {D E S₁ : Set Point}
    (hS₁K : S₁ ⊆ (D ∪ E)ᶜ) (active : ConnectedComponents (Dᶜ : Set Point)) :
    LocalFiltration.ActiveFiber D E active → Fin 2 := by
  classical
  exact fun c =>
    if ∃ (s : Point) (hs : s ∈ S₁),
        ConnectedComponents.mk
          (⟨s, hS₁K hs⟩ : ((LocalInsertion.carrierExtension D E)ᶜ : Set Point)) = c.1
    then 0 else 1

/-- Every active-fibre element contains a point of `S₁` or of `S₂`. -/
theorem active_fiber_meets_collar
    {D E U S₁ S₂ : Set Point} (hD : IsClosed D) (hE : IsClosed E)
    {z₀ : Point} (hz₀E : z₀ ∈ E) (hz₀D : z₀ ∉ D)
    (hU : IsOpen U)
    (hEU : ∀ z ∈ E, z ∈ connectedComponentIn Dᶜ z₀ → z ∈ U)
    (hS₁ : IsPreconnected S₁) (hS₂ : IsPreconnected S₂)
    (hS₁K : S₁ ⊆ (D ∪ E)ᶜ) (hS₂K : S₂ ⊆ (D ∪ E)ᶜ)
    (hcover : ∀ x ∈ U, x ∈ connectedComponentIn Dᶜ z₀ → x ∉ E →
      x ∈ S₁ ∨ x ∈ S₂)
    (d : LocalFiltration.ActiveFiber D E
      (ConnectedComponents.mk (⟨z₀, hz₀D⟩ : (Dᶜ : Set Point)))) :
    (∃ (s : Point) (hs : s ∈ S₁),
      ConnectedComponents.mk
        (⟨s, hS₁K hs⟩ : ((LocalInsertion.carrierExtension D E)ᶜ : Set Point)) = d.1) ∨
    (∃ (s : Point) (hs : s ∈ S₂),
      ConnectedComponents.mk
        (⟨s, hS₂K hs⟩ : ((LocalInsertion.carrierExtension D E)ᶜ : Set Point)) = d.1) := by
  have hz₀Dc : z₀ ∈ Dᶜ := hz₀D
  obtain ⟨dv, hd⟩ := d
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe dv
  have hyD : y.1 ∉ D := fun h => y.2 (Or.inl h)
  have hyO : y.1 ∈ connectedComponentIn Dᶜ z₀ := by
    have hmk :
        ConnectedComponents.mk (⟨z₀, hz₀Dc⟩ : (Dᶜ : Set Point)) =
          ConnectedComponents.mk (⟨y.1, hyD⟩ : (Dᶜ : Set Point)) := by
      simpa [ComponentFibers.inclusionMap_mk, ComponentFibers.inclusion,
        ComponentSurjectivity.complementSubset] using hd.symm
    exact ComponentLifting.mem_connectedComponentIn_of_connectedComponents_mk_eq
      _ _ hmk
  have hyE : y.1 ∉ E := fun h => y.2 (Or.inr h)
  rcases exists_collar_point_in_component hD hE hz₀E hz₀D hU hEU hS₁ hS₂
      hS₁K hS₂K hcover hyO hyE with ⟨s, hs, hsy⟩ | ⟨s, hs, hsy⟩
  · left
    exact ⟨s, hs, mk_eq_of_mem_connectedComponentIn y.2 hsy⟩
  · right
    exact ⟨s, hs, mk_eq_of_mem_connectedComponentIn y.2 hsy⟩

theorem collarClassifier_injective
    {D E U S₁ S₂ : Set Point} (hD : IsClosed D) (hE : IsClosed E)
    {z₀ : Point} (hz₀E : z₀ ∈ E) (hz₀D : z₀ ∉ D)
    (hU : IsOpen U)
    (hEU : ∀ z ∈ E, z ∈ connectedComponentIn Dᶜ z₀ → z ∈ U)
    (hS₁ : IsPreconnected S₁) (hS₂ : IsPreconnected S₂)
    (hS₁K : S₁ ⊆ (D ∪ E)ᶜ) (hS₂K : S₂ ⊆ (D ∪ E)ᶜ)
    (hcover : ∀ x ∈ U, x ∈ connectedComponentIn Dᶜ z₀ → x ∉ E →
      x ∈ S₁ ∨ x ∈ S₂) :
    Injective (collarClassifier (D := D) (E := E) hS₁K
      (ConnectedComponents.mk (⟨z₀, hz₀D⟩ : (Dᶜ : Set Point)))) := by
  classical
  intro c c' hcc'
  have key := active_fiber_meets_collar hD hE hz₀E hz₀D hU hEU hS₁ hS₂
    hS₁K hS₂K hcover
  have hS₁eq : ∀ (s s' : Point) (hs : s ∈ S₁) (hs' : s' ∈ S₁),
      ConnectedComponents.mk
          (⟨s, hS₁K hs⟩ : ((LocalInsertion.carrierExtension D E)ᶜ : Set Point)) =
        ConnectedComponents.mk
          (⟨s', hS₁K hs'⟩ : ((LocalInsertion.carrierExtension D E)ᶜ : Set Point)) := by
    intro s s' hs hs'
    exact ComponentLifting.connectedComponents_mk_eq_of_isConnected_subset
      ⟨⟨s, hs⟩, hS₁⟩ hS₁K hs hs'
  have hS₂eq : ∀ (s s' : Point) (hs : s ∈ S₂) (hs' : s' ∈ S₂),
      ConnectedComponents.mk
          (⟨s, hS₂K hs⟩ : ((LocalInsertion.carrierExtension D E)ᶜ : Set Point)) =
        ConnectedComponents.mk
          (⟨s', hS₂K hs'⟩ : ((LocalInsertion.carrierExtension D E)ᶜ : Set Point)) := by
    intro s s' hs hs'
    exact ComponentLifting.connectedComponents_mk_eq_of_isConnected_subset
      ⟨⟨s, hs⟩, hS₂⟩ hS₂K hs hs'
  apply Subtype.ext
  unfold collarClassifier at hcc'
  by_cases h1 : ∃ (s : Point) (hs : s ∈ S₁),
      ConnectedComponents.mk
        (⟨s, hS₁K hs⟩ : ((LocalInsertion.carrierExtension D E)ᶜ : Set Point)) = c.1
  · have h1' : ∃ (s : Point) (hs : s ∈ S₁),
        ConnectedComponents.mk
          (⟨s, hS₁K hs⟩ : ((LocalInsertion.carrierExtension D E)ᶜ : Set Point)) = c'.1 := by
      by_contra hn
      simp only [h1, hn, if_true, if_false] at hcc'
      exact absurd hcc' (by decide)
    obtain ⟨s, hs, hsc⟩ := h1
    obtain ⟨s', hs', hsc'⟩ := h1'
    rw [← hsc, ← hsc']
    exact hS₁eq s s' hs hs'
  · have h1' : ¬ ∃ (s : Point) (hs : s ∈ S₁),
        ConnectedComponents.mk
          (⟨s, hS₁K hs⟩ : ((LocalInsertion.carrierExtension D E)ᶜ : Set Point)) = c'.1 := by
      intro hn
      simp only [h1, hn, if_true, if_false] at hcc'
      exact absurd hcc' (by decide)
    rcases key c with h | ⟨s, hs, hsc⟩
    · exact absurd h h1
    rcases key c' with h | ⟨s', hs', hsc'⟩
    · exact absurd h h1'
    rw [← hsc, ← hsc']
    exact hS₂eq s s' hs hs'

/-- Bounded one-edge step from two collars. -/
def localizedEdgeStepOfCollars
    {D E U S₁ S₂ : Set Point} (hD : IsClosed D) (hE : IsClosed E)
    {z₀ : Point} (hz₀E : z₀ ∈ E) (hz₀D : z₀ ∉ D)
    (hloc : ∀ z ∈ E, z ∉ D → z ∈ connectedComponentIn Dᶜ z₀)
    (hU : IsOpen U)
    (hEU : ∀ z ∈ E, z ∈ connectedComponentIn Dᶜ z₀ → z ∈ U)
    (hS₁ : IsPreconnected S₁) (hS₂ : IsPreconnected S₂)
    (hS₁K : S₁ ⊆ (D ∪ E)ᶜ) (hS₂K : S₂ ⊆ (D ∪ E)ᶜ)
    (hcover : ∀ x ∈ U, x ∈ connectedComponentIn Dᶜ z₀ → x ∉ E →
      x ∈ S₁ ∨ x ∈ S₂) :
    LocalFiltration.LocalizedEdgeStep D E where
  active := ConnectedComponents.mk (⟨z₀, hz₀D⟩ : (Dᶜ : Set Point))
  localized := fun z hzE hzD =>
    mk_eq_of_mem_connectedComponentIn hz₀D (hloc z hzE hzD)
  activeClassifier := collarClassifier hS₁K _
  active_injective := collarClassifier_injective hD hE hz₀E hz₀D hU hEU hS₁ hS₂
    hS₁K hS₂K hcover

/-- Exact one-edge step from two collars that lie in different components of
the enlarged complement. -/
def localizedExactEdgeStepOfCollars
    {D E U S₁ S₂ : Set Point} (L : Lollipop) (hELp : E ⊆ L.carrier)
    (hD : IsClosed D) (hE : IsClosed E)
    {z₀ : Point} (hz₀E : z₀ ∈ E) (hz₀D : z₀ ∉ D)
    (hloc : ∀ z ∈ E, z ∉ D → z ∈ connectedComponentIn Dᶜ z₀)
    (hU : IsOpen U)
    (hEU : ∀ z ∈ E, z ∈ connectedComponentIn Dᶜ z₀ → z ∈ U)
    (hS₁ : IsPreconnected S₁) (hS₂ : IsPreconnected S₂)
    (hS₁K : S₁ ⊆ (D ∪ E)ᶜ) (hS₂K : S₂ ⊆ (D ∪ E)ᶜ)
    (hS₁O : S₁ ⊆ connectedComponentIn Dᶜ z₀)
    (hS₂O : S₂ ⊆ connectedComponentIn Dᶜ z₀)
    (hcover : ∀ x ∈ U, x ∈ connectedComponentIn Dᶜ z₀ → x ∉ E →
      x ∈ S₁ ∨ x ∈ S₂)
    {s₁ s₂ : Point} (hs₁ : s₁ ∈ S₁) (hs₂ : s₂ ∈ S₂)
    (hsep : ConnectedComponents.mk
        (⟨s₁, hS₁K hs₁⟩ : ((LocalInsertion.carrierExtension D E)ᶜ : Set Point)) ≠
      ConnectedComponents.mk
        (⟨s₂, hS₂K hs₂⟩ : ((LocalInsertion.carrierExtension D E)ᶜ : Set Point)))
    (hsep' : ∀ (s s' : Point) (hs : s ∈ S₁) (hs' : s' ∈ S₂),
      ConnectedComponents.mk
        (⟨s, hS₁K hs⟩ : ((LocalInsertion.carrierExtension D E)ᶜ : Set Point)) ≠
      ConnectedComponents.mk
        (⟨s', hS₂K hs'⟩ : ((LocalInsertion.carrierExtension D E)ᶜ : Set Point))) :
    LocalFiltration.LocalizedExactEdgeStep L D E where
  old_closed := hD
  edge_subset_carrier := hELp
  active := ConnectedComponents.mk (⟨z₀, hz₀D⟩ : (Dᶜ : Set Point))
  localized := fun z hzE hzD =>
    mk_eq_of_mem_connectedComponentIn hz₀D (hloc z hzE hzD)
  activeClassifier := collarClassifier hS₁K _
  active_injective := collarClassifier_injective hD hE hz₀E hz₀D hU hEU hS₁ hS₂
    hS₁K hS₂K hcover
  active_surjective := by
    classical
    have hz₀Dc : z₀ ∈ Dᶜ := hz₀D
    -- a fibre element for each collar
    have hfib : ∀ (s : Point) (hsK : s ∈ (D ∪ E)ᶜ),
        s ∈ connectedComponentIn Dᶜ z₀ →
        ComponentFibers.inclusionMap
          (ComponentSurjectivity.complementSubset
            (LocalInsertion.old_subset_carrierExtension D E))
          (ConnectedComponents.mk
            (⟨s, hsK⟩ : ((LocalInsertion.carrierExtension D E)ᶜ : Set Point))) =
        ConnectedComponents.mk (⟨z₀, hz₀Dc⟩ : (Dᶜ : Set Point)) := by
      intro s hsK hsO
      simp only [ComponentFibers.inclusionMap_mk, ComponentFibers.inclusion,
        ComponentSurjectivity.complementSubset]
      exact mk_eq_of_mem_connectedComponentIn hz₀Dc hsO
    intro i
    fin_cases i
    · refine ⟨⟨ConnectedComponents.mk
        (⟨s₁, hS₁K hs₁⟩ : ((LocalInsertion.carrierExtension D E)ᶜ : Set Point)),
        hfib s₁ (hS₁K hs₁) (hS₁O hs₁)⟩, ?_⟩
      unfold collarClassifier
      have : ∃ (s : Point) (hs : s ∈ S₁),
          ConnectedComponents.mk
            (⟨s, hS₁K hs⟩ : ((LocalInsertion.carrierExtension D E)ᶜ : Set Point)) =
          ConnectedComponents.mk
            (⟨s₁, hS₁K hs₁⟩ : ((LocalInsertion.carrierExtension D E)ᶜ : Set Point)) :=
        ⟨s₁, hs₁, rfl⟩
      exact if_pos this
    · refine ⟨⟨ConnectedComponents.mk
        (⟨s₂, hS₂K hs₂⟩ : ((LocalInsertion.carrierExtension D E)ᶜ : Set Point)),
        hfib s₂ (hS₂K hs₂) (hS₂O hs₂)⟩, ?_⟩
      unfold collarClassifier
      have : ¬ ∃ (s : Point) (hs : s ∈ S₁),
          ConnectedComponents.mk
            (⟨s, hS₁K hs⟩ : ((LocalInsertion.carrierExtension D E)ᶜ : Set Point)) =
          ConnectedComponents.mk
            (⟨s₂, hS₂K hs₂⟩ : ((LocalInsertion.carrierExtension D E)ᶜ : Set Point)) := by
        rintro ⟨s, hs, h⟩
        exact hsep' s s₂ hs hs₂ h
      exact if_neg this

end Collar
end EndToEnd
end Concrete
end Lollipop
