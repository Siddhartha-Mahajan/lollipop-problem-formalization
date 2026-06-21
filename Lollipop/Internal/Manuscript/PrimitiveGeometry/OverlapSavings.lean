import Lollipop.Internal.Manuscript.PrimitiveGeometry.CarrierSavings

/-!
Direct savings from component overlap.

The generic component count gives `2 + 2 + 2 + 1 = 7`.  For direct
whole-carrier savings, overlap between components can be exploited without
forcing any one component to be empty.  This file proves the strongest simple
overlap case needed for shared-anchor audits: if one point lies in all four
circle/ray components, the whole carrier intersection has at most four
points under the usual noncoincidence assumptions.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace PrimitiveGeometry

/-- If a component already contains a point `q` outside a finite witness,
then inserting `q` improves the component-cardinality estimate by one. -/
theorem finset_card_add_one_le_of_forall_mem_of_mem_of_not_mem
    {α : Type*} [DecidableEq α] {component : Set α}
    {q : α} {bound : Nat} {S : Finset α}
    (hq_component : q ∈ component)
    (hqS : q ∉ S)
    (hS : ∀ p ∈ S, p ∈ component)
    (hbound :
      ∀ T : Finset α,
        (∀ p ∈ T, p ∈ component) → T.card ≤ bound) :
    S.card + 1 ≤ bound := by
  have hinsert :=
    hbound (insert q S)
      (by
        intro p hp
        rcases Finset.mem_insert.1 hp with rfl | hpS
        · exact hq_component
        · exact hS p hpS)
  simpa [Finset.card_insert_of_notMem hqS] using hinsert

/-- Abstract finite-set overlap saving.  If a point belongs to three of four
components, then deleting it improves three component-cardinality estimates by
one. -/
theorem finset_card_le_of_common_three_components
    {α : Type*} [DecidableEq α] {C₀ C₁ C₂ C₃ : Set α}
    {q : α} {b₀ b₁ b₂ b₃ : Nat} {S : Finset α}
    (hq₀ : q ∈ C₀)
    (hq₁ : q ∈ C₁)
    (hq₂ : q ∈ C₂)
    (hS : ∀ p ∈ S, p ∈ C₀ ∨ p ∈ C₁ ∨ p ∈ C₂ ∨ p ∈ C₃)
    (hbound₀ :
      ∀ T : Finset α, (∀ p ∈ T, p ∈ C₀) → T.card ≤ b₀)
    (hbound₁ :
      ∀ T : Finset α, (∀ p ∈ T, p ∈ C₁) → T.card ≤ b₁)
    (hbound₂ :
      ∀ T : Finset α, (∀ p ∈ T, p ∈ C₂) → T.card ≤ b₂)
    (hbound₃ :
      ∀ T : Finset α, (∀ p ∈ T, p ∈ C₃) → T.card ≤ b₃) :
    S.card ≤ b₀ + b₁ + b₂ + b₃ - 2 := by
  classical
  let S' : Finset α := S.erase q
  let F₀ : Finset α := S'.filter fun p => p ∈ C₀
  let F₁ : Finset α := S'.filter fun p => p ∈ C₁
  let F₂ : Finset α := S'.filter fun p => p ∈ C₂
  let F₃ : Finset α := S'.filter fun p => p ∈ C₃
  let U₀₁ : Finset α := F₀ ∪ F₁
  let U₀₁₂ : Finset α := U₀₁ ∪ F₂
  let Uall : Finset α := U₀₁₂ ∪ F₃
  have hcover : S' ⊆ Uall := by
    intro p hpS'
    have hpS : p ∈ S := (Finset.mem_erase.1 hpS').2
    rcases hS p hpS with hp₀ | hp₁ | hp₂ | hp₃
    · simp [Uall, U₀₁₂, U₀₁, F₀, hpS', hp₀]
    · simp [Uall, U₀₁₂, U₀₁, F₁, hpS', hp₁]
    · simp [Uall, U₀₁₂, F₂, hpS', hp₂]
    · simp [Uall, F₃, hpS', hp₃]
  have hqS' : q ∉ S' := by
    simp [S']
  have hcard₀ : F₀.card + 1 ≤ b₀ :=
    finset_card_add_one_le_of_forall_mem_of_mem_of_not_mem
      (component := C₀) hq₀
      (by
        intro hqF
        exact hqS' ((Finset.mem_filter.1 hqF).1))
      (by
        intro p hp
        exact (Finset.mem_filter.1 hp).2)
      hbound₀
  have hcard₁ : F₁.card + 1 ≤ b₁ :=
    finset_card_add_one_le_of_forall_mem_of_mem_of_not_mem
      (component := C₁) hq₁
      (by
        intro hqF
        exact hqS' ((Finset.mem_filter.1 hqF).1))
      (by
        intro p hp
        exact (Finset.mem_filter.1 hp).2)
      hbound₁
  have hcard₂ : F₂.card + 1 ≤ b₂ :=
    finset_card_add_one_le_of_forall_mem_of_mem_of_not_mem
      (component := C₂) hq₂
      (by
        intro hqF
        exact hqS' ((Finset.mem_filter.1 hqF).1))
      (by
        intro p hp
        exact (Finset.mem_filter.1 hp).2)
      hbound₂
  have hcard₃ : F₃.card ≤ b₃ :=
    hbound₃ F₃ (by
      intro p hp
      exact (Finset.mem_filter.1 hp).2)
  have hSle : S'.card ≤ Uall.card := Finset.card_le_card hcover
  have hUall : Uall.card ≤ U₀₁₂.card + F₃.card :=
    Finset.card_union_le U₀₁₂ F₃
  have hU₀₁₂ : U₀₁₂.card ≤ U₀₁.card + F₂.card :=
    Finset.card_union_le U₀₁ F₂
  have hU₀₁ : U₀₁.card ≤ F₀.card + F₁.card :=
    Finset.card_union_le F₀ F₁
  have hS'le : S'.card ≤ b₀ + b₁ + b₂ + b₃ - 3 := by
    omega
  by_cases hqS : q ∈ S
  · have hcard : S'.card + 1 = S.card := by
      simpa [S'] using Finset.card_erase_add_one hqS
    omega
  · have hcard : S'.card = S.card := by
      simp [S', Finset.erase_eq_of_notMem hqS]
    omega

/-- Abstract finite-set overlap saving from two overlap witnesses.  The first
witness belongs to the first two components and the second witness belongs to
the last two components, improving all four component estimates by one after
deleting the witnesses.  The two witnesses need not be distinct; if they
coincide, this is the weaker form of the all-four-overlap saving. -/
theorem finset_card_le_of_two_double_component_overlaps
    {α : Type*} [DecidableEq α] {C₀ C₁ C₂ C₃ : Set α}
    {q r : α} {b₀ b₁ b₂ b₃ : Nat} {S : Finset α}
    (hq₀ : q ∈ C₀)
    (hq₁ : q ∈ C₁)
    (hr₂ : r ∈ C₂)
    (hr₃ : r ∈ C₃)
    (hS : ∀ p ∈ S, p ∈ C₀ ∨ p ∈ C₁ ∨ p ∈ C₂ ∨ p ∈ C₃)
    (hbound₀ :
      ∀ T : Finset α, (∀ p ∈ T, p ∈ C₀) → T.card ≤ b₀)
    (hbound₁ :
      ∀ T : Finset α, (∀ p ∈ T, p ∈ C₁) → T.card ≤ b₁)
    (hbound₂ :
      ∀ T : Finset α, (∀ p ∈ T, p ∈ C₂) → T.card ≤ b₂)
    (hbound₃ :
      ∀ T : Finset α, (∀ p ∈ T, p ∈ C₃) → T.card ≤ b₃) :
    S.card ≤ b₀ + b₁ + b₂ + b₃ - 2 := by
  classical
  let S₁ : Finset α := S.erase q
  let S' : Finset α := S₁.erase r
  let F₀ : Finset α := S'.filter fun p => p ∈ C₀
  let F₁ : Finset α := S'.filter fun p => p ∈ C₁
  let F₂ : Finset α := S'.filter fun p => p ∈ C₂
  let F₃ : Finset α := S'.filter fun p => p ∈ C₃
  let U₀₁ : Finset α := F₀ ∪ F₁
  let U₀₁₂ : Finset α := U₀₁ ∪ F₂
  let Uall : Finset α := U₀₁₂ ∪ F₃
  have hcover : S' ⊆ Uall := by
    intro p hpS'
    have hpS₁ : p ∈ S₁ := (Finset.mem_erase.1 hpS').2
    have hpS : p ∈ S := (Finset.mem_erase.1 hpS₁).2
    rcases hS p hpS with hp₀ | hp₁ | hp₂ | hp₃
    · simp [Uall, U₀₁₂, U₀₁, F₀, hpS', hp₀]
    · simp [Uall, U₀₁₂, U₀₁, F₁, hpS', hp₁]
    · simp [Uall, U₀₁₂, F₂, hpS', hp₂]
    · simp [Uall, F₃, hpS', hp₃]
  have hqS' : q ∉ S' := by
    intro hqS'
    have hqS₁ : q ∈ S₁ := (Finset.mem_erase.1 hqS').2
    exact (Finset.mem_erase.1 hqS₁).1 rfl
  have hrS' : r ∉ S' := by
    simp [S']
  have hcard₀ : F₀.card + 1 ≤ b₀ :=
    finset_card_add_one_le_of_forall_mem_of_mem_of_not_mem
      (component := C₀) hq₀
      (by
        intro hqF
        exact hqS' ((Finset.mem_filter.1 hqF).1))
      (by
        intro p hp
        exact (Finset.mem_filter.1 hp).2)
      hbound₀
  have hcard₁ : F₁.card + 1 ≤ b₁ :=
    finset_card_add_one_le_of_forall_mem_of_mem_of_not_mem
      (component := C₁) hq₁
      (by
        intro hqF
        exact hqS' ((Finset.mem_filter.1 hqF).1))
      (by
        intro p hp
        exact (Finset.mem_filter.1 hp).2)
      hbound₁
  have hcard₂ : F₂.card + 1 ≤ b₂ :=
    finset_card_add_one_le_of_forall_mem_of_mem_of_not_mem
      (component := C₂) hr₂
      (by
        intro hrF
        exact hrS' ((Finset.mem_filter.1 hrF).1))
      (by
        intro p hp
        exact (Finset.mem_filter.1 hp).2)
      hbound₂
  have hcard₃ : F₃.card + 1 ≤ b₃ :=
    finset_card_add_one_le_of_forall_mem_of_mem_of_not_mem
      (component := C₃) hr₃
      (by
        intro hrF
        exact hrS' ((Finset.mem_filter.1 hrF).1))
      (by
        intro p hp
        exact (Finset.mem_filter.1 hp).2)
      hbound₃
  have hSle : S'.card ≤ Uall.card := Finset.card_le_card hcover
  have hUall : Uall.card ≤ U₀₁₂.card + F₃.card :=
    Finset.card_union_le U₀₁₂ F₃
  have hU₀₁₂ : U₀₁₂.card ≤ U₀₁.card + F₂.card :=
    Finset.card_union_le U₀₁ F₂
  have hU₀₁ : U₀₁.card ≤ F₀.card + F₁.card :=
    Finset.card_union_le F₀ F₁
  have hS'le : S'.card ≤ b₀ + b₁ + b₂ + b₃ - 4 := by
    omega
  have hS₁le : S.card ≤ S₁.card + 1 := by
    by_cases hqS : q ∈ S
    · have hcard : S₁.card + 1 = S.card := by
        simpa [S₁] using Finset.card_erase_add_one hqS
      omega
    · have hcard : S₁.card = S.card := by
        simp [S₁, Finset.erase_eq_of_notMem hqS]
      omega
  have hS'card_step : S₁.card ≤ S'.card + 1 := by
    by_cases hrS₁ : r ∈ S₁
    · have hcard : S'.card + 1 = S₁.card := by
        simpa [S'] using Finset.card_erase_add_one hrS₁
      omega
    · have hcard : S'.card = S₁.card := by
        simp [S', Finset.erase_eq_of_notMem hrS₁]
      omega
  omega

/-- If the four circle/ray components share one common point, the generic
`2,2,2,1` component bounds collapse to a direct whole-carrier `<= 4` bound. -/
theorem finset_card_le_four_of_common_all_components
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    {q : EuclideanR2}
    (hqcc : q ∈ euclideanCircleCircleSet L M)
    (hqcr : q ∈ euclideanCircleRaySet L M)
    (hqrc : q ∈ euclideanRayCircleSet L M)
    (hqrr : q ∈ euclideanRayRaySet L M)
    (S : Finset EuclideanR2)
    (hS : ∀ p ∈ S, p ∈ euclideanPairIntersectionSet L M) :
    S.card ≤ 4 := by
  classical
  let S' : Finset EuclideanR2 := S.erase q
  let cc : Finset EuclideanR2 :=
    S'.filter fun p => p ∈ euclideanCircleCircleSet L M
  let cr : Finset EuclideanR2 :=
    S'.filter fun p => p ∈ euclideanCircleRaySet L M
  let rc : Finset EuclideanR2 :=
    S'.filter fun p => p ∈ euclideanRayCircleSet L M
  let rr : Finset EuclideanR2 :=
    S'.filter fun p => p ∈ euclideanRayRaySet L M
  let u12 : Finset EuclideanR2 := cc ∪ cr
  let u123 : Finset EuclideanR2 := u12 ∪ rc
  let uall : Finset EuclideanR2 := u123 ∪ rr
  have hcover : S' ⊆ uall := by
    intro p hpS'
    have hpS : p ∈ S := (Finset.mem_erase.1 hpS').2
    rcases (mem_euclideanPairIntersectionSet_iff.1 (hS p hpS)) with
      hcc | hcr | hrc | hrr
    · simp [uall, u123, u12, cc, hpS', hcc]
    · simp [uall, u123, u12, cr, hpS', hcr]
    · simp [uall, u123, rc, hpS', hrc]
    · simp [uall, rr, hpS', hrr]
  have hqS' : q ∉ S' := by
    simp [S']
  have hccard : cc.card + 1 ≤ 2 :=
    finset_card_add_one_le_of_forall_mem_of_mem_of_not_mem
      (component := euclideanCircleCircleSet L M) hqcc
      (by
        intro hqcc_filter
        exact hqS' ((Finset.mem_filter.1 hqcc_filter).1))
      (by
        intro p hp
        exact (Finset.mem_filter.1 hp).2)
      (finset_card_le_two_of_forall_mem_euclideanCircleCircleSet hLM)
  have hcrcard : cr.card + 1 ≤ 2 :=
    finset_card_add_one_le_of_forall_mem_of_mem_of_not_mem
      (component := euclideanCircleRaySet L M) hqcr
      (by
        intro hqcr_filter
        exact hqS' ((Finset.mem_filter.1 hqcr_filter).1))
      (by
        intro p hp
        exact (Finset.mem_filter.1 hp).2)
      finset_card_le_two_of_forall_mem_euclideanCircleRaySet
  have hrccard : rc.card + 1 ≤ 2 :=
    finset_card_add_one_le_of_forall_mem_of_mem_of_not_mem
      (component := euclideanRayCircleSet L M) hqrc
      (by
        intro hqrc_filter
        exact hqS' ((Finset.mem_filter.1 hqrc_filter).1))
      (by
        intro p hp
        exact (Finset.mem_filter.1 hp).2)
      finset_card_le_two_of_forall_mem_euclideanRayCircleSet
  have hrrcard : rr.card + 1 ≤ 1 :=
    finset_card_add_one_le_of_forall_mem_of_mem_of_not_mem
      (component := euclideanRayRaySet L M) hqrr
      (by
        intro hqrr_filter
        exact hqS' ((Finset.mem_filter.1 hqrr_filter).1))
      (by
        intro p hp
        exact (Finset.mem_filter.1 hp).2)
      (finset_card_le_one_of_forall_mem_euclideanRayRaySet hline)
  have hSle : S'.card ≤ uall.card := Finset.card_le_card hcover
  have huall : uall.card ≤ u123.card + rr.card :=
    Finset.card_union_le u123 rr
  have hu123 : u123.card ≤ u12.card + rc.card :=
    Finset.card_union_le u12 rc
  have hu12 : u12.card ≤ cc.card + cr.card :=
    Finset.card_union_le cc cr
  have hS'le : S'.card ≤ 3 := by
    omega
  by_cases hqS : q ∈ S
  · have hcard : S'.card + 1 = S.card := by
      simpa [S'] using Finset.card_erase_add_one hqS
    omega
  · have hcard : S'.card = S.card := by
      simp [S', Finset.erase_eq_of_notMem hqS]
    omega

/-- Direct whole-carrier savings from one point common to all four
circle/ray components. -/
def pairCarrierSavingsFourOfCommonAllComponents
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    {q : EuclideanR2}
    (hqcc : q ∈ euclideanCircleCircleSet L M)
    (hqcr : q ∈ euclideanCircleRaySet L M)
    (hqrc : q ∈ euclideanRayCircleSet L M)
    (hqrr : q ∈ euclideanRayRaySet L M) :
    PairCarrierSavings L M 4 where
  carrier_card_le :=
    finset_card_le_four_of_common_all_components
      hLM hline hqcc hqcr hqrc hqrr

/-- A witness that one point lies in at least three of the four circle/ray
components of the carrier intersection. -/
inductive PairComponentTripleOverlap
    (L M : EuclideanLollipop) (q : EuclideanR2) : Prop where
  | withoutCircleCircle
      (hqcr : q ∈ euclideanCircleRaySet L M)
      (hqrc : q ∈ euclideanRayCircleSet L M)
      (hqrr : q ∈ euclideanRayRaySet L M)
  | withoutCircleRay
      (hqcc : q ∈ euclideanCircleCircleSet L M)
      (hqrc : q ∈ euclideanRayCircleSet L M)
      (hqrr : q ∈ euclideanRayRaySet L M)
  | withoutRayCircle
      (hqcc : q ∈ euclideanCircleCircleSet L M)
      (hqcr : q ∈ euclideanCircleRaySet L M)
      (hqrr : q ∈ euclideanRayRaySet L M)
  | withoutRayRay
      (hqcc : q ∈ euclideanCircleCircleSet L M)
      (hqcr : q ∈ euclideanCircleRaySet L M)
      (hqrc : q ∈ euclideanRayCircleSet L M)

/-- For these four product-type components, a single point in any three
components automatically lies in the fourth component too. -/
theorem pairComponentTripleOverlap_all_four
    {L M : EuclideanLollipop} {q : EuclideanR2}
    (H : PairComponentTripleOverlap L M q) :
    q ∈ euclideanCircleCircleSet L M ∧
      q ∈ euclideanCircleRaySet L M ∧
        q ∈ euclideanRayCircleSet L M ∧
          q ∈ euclideanRayRaySet L M := by
  cases H with
  | withoutCircleCircle hqcr hqrc hqrr =>
      exact ⟨⟨hqcr.1, hqrc.2⟩, hqcr, hqrc, hqrr⟩
  | withoutCircleRay hqcc hqrc hqrr =>
      exact ⟨hqcc, ⟨hqcc.1, hqrr.2⟩, hqrc, hqrr⟩
  | withoutRayCircle hqcc hqcr hqrr =>
      exact ⟨hqcc, hqcr, ⟨hqrr.1, hqcc.2⟩, hqrr⟩
  | withoutRayRay hqcc hqcr hqrc =>
      exact ⟨hqcc, hqcr, hqrc, ⟨hqrc.1, hqcr.2⟩⟩

/-- If one point lies in any three of the four circle/ray components, it
actually gives the stronger direct whole-carrier `<= 4` bound. -/
theorem finset_card_le_four_of_triple_component_overlap
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    {q : EuclideanR2}
    (H : PairComponentTripleOverlap L M q)
    (S : Finset EuclideanR2)
    (hS : ∀ p ∈ S, p ∈ euclideanPairIntersectionSet L M) :
    S.card ≤ 4 := by
  rcases pairComponentTripleOverlap_all_four H with
    ⟨hqcc, hqcr, hqrc, hqrr⟩
  exact
    finset_card_le_four_of_common_all_components
      hLM hline hqcc hqcr hqrc hqrr S hS

/-- Direct whole-carrier `<= 4` savings from a point common to any three
circle/ray components. -/
def pairCarrierSavingsFourOfTripleComponentOverlap
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    {q : EuclideanR2}
    (H : PairComponentTripleOverlap L M q) :
    PairCarrierSavings L M 4 where
  carrier_card_le :=
    finset_card_le_four_of_triple_component_overlap hLM hline H

/-- If one point lies in any three of the four circle/ray components, the
generic component bounds collapse to a direct whole-carrier `<= 5` bound. -/
theorem finset_card_le_five_of_triple_component_overlap
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    {q : EuclideanR2}
    (H : PairComponentTripleOverlap L M q)
    (S : Finset EuclideanR2)
    (hS : ∀ p ∈ S, p ∈ euclideanPairIntersectionSet L M) :
    S.card ≤ 5 := by
  have hcover₀ :
      ∀ p ∈ S,
        p ∈ euclideanCircleCircleSet L M ∨
        p ∈ euclideanCircleRaySet L M ∨
        p ∈ euclideanRayCircleSet L M ∨
        p ∈ euclideanRayRaySet L M := by
    intro p hp
    exact mem_euclideanPairIntersectionSet_iff.1 (hS p hp)
  cases H with
  | withoutCircleCircle hqcr hqrc hqrr =>
    have hcover :
        ∀ p ∈ S,
          p ∈ euclideanCircleRaySet L M ∨
          p ∈ euclideanRayCircleSet L M ∨
          p ∈ euclideanRayRaySet L M ∨
          p ∈ euclideanCircleCircleSet L M := by
      intro p hp
      rcases hcover₀ p hp with hcc | hcr | hrc | hrr
      · exact Or.inr (Or.inr (Or.inr hcc))
      · exact Or.inl hcr
      · exact Or.inr (Or.inl hrc)
      · exact Or.inr (Or.inr (Or.inl hrr))
    have h :=
      finset_card_le_of_common_three_components
        (C₀ := euclideanCircleRaySet L M)
        (C₁ := euclideanRayCircleSet L M)
        (C₂ := euclideanRayRaySet L M)
        (C₃ := euclideanCircleCircleSet L M)
        hqcr hqrc hqrr hcover
        finset_card_le_two_of_forall_mem_euclideanCircleRaySet
        finset_card_le_two_of_forall_mem_euclideanRayCircleSet
        (finset_card_le_one_of_forall_mem_euclideanRayRaySet hline)
        (finset_card_le_two_of_forall_mem_euclideanCircleCircleSet hLM)
    norm_num at h
    exact h
  | withoutCircleRay hqcc hqrc hqrr =>
    have hcover :
        ∀ p ∈ S,
          p ∈ euclideanCircleCircleSet L M ∨
          p ∈ euclideanRayCircleSet L M ∨
          p ∈ euclideanRayRaySet L M ∨
          p ∈ euclideanCircleRaySet L M := by
      intro p hp
      rcases hcover₀ p hp with hcc | hcr | hrc | hrr
      · exact Or.inl hcc
      · exact Or.inr (Or.inr (Or.inr hcr))
      · exact Or.inr (Or.inl hrc)
      · exact Or.inr (Or.inr (Or.inl hrr))
    have h :=
      finset_card_le_of_common_three_components
        (C₀ := euclideanCircleCircleSet L M)
        (C₁ := euclideanRayCircleSet L M)
        (C₂ := euclideanRayRaySet L M)
        (C₃ := euclideanCircleRaySet L M)
        hqcc hqrc hqrr hcover
        (finset_card_le_two_of_forall_mem_euclideanCircleCircleSet hLM)
        finset_card_le_two_of_forall_mem_euclideanRayCircleSet
        (finset_card_le_one_of_forall_mem_euclideanRayRaySet hline)
        finset_card_le_two_of_forall_mem_euclideanCircleRaySet
    norm_num at h
    exact h
  | withoutRayCircle hqcc hqcr hqrr =>
    have hcover :
        ∀ p ∈ S,
          p ∈ euclideanCircleCircleSet L M ∨
          p ∈ euclideanCircleRaySet L M ∨
          p ∈ euclideanRayRaySet L M ∨
          p ∈ euclideanRayCircleSet L M := by
      intro p hp
      rcases hcover₀ p hp with hcc | hcr | hrc | hrr
      · exact Or.inl hcc
      · exact Or.inr (Or.inl hcr)
      · exact Or.inr (Or.inr (Or.inr hrc))
      · exact Or.inr (Or.inr (Or.inl hrr))
    have h :=
      finset_card_le_of_common_three_components
        (C₀ := euclideanCircleCircleSet L M)
        (C₁ := euclideanCircleRaySet L M)
        (C₂ := euclideanRayRaySet L M)
        (C₃ := euclideanRayCircleSet L M)
        hqcc hqcr hqrr hcover
        (finset_card_le_two_of_forall_mem_euclideanCircleCircleSet hLM)
        finset_card_le_two_of_forall_mem_euclideanCircleRaySet
        (finset_card_le_one_of_forall_mem_euclideanRayRaySet hline)
        finset_card_le_two_of_forall_mem_euclideanRayCircleSet
    norm_num at h
    exact h
  | withoutRayRay hqcc hqcr hqrc =>
    have hcover :
        ∀ p ∈ S,
          p ∈ euclideanCircleCircleSet L M ∨
          p ∈ euclideanCircleRaySet L M ∨
          p ∈ euclideanRayCircleSet L M ∨
          p ∈ euclideanRayRaySet L M := by
      exact hcover₀
    have h :=
      finset_card_le_of_common_three_components
        (C₀ := euclideanCircleCircleSet L M)
        (C₁ := euclideanCircleRaySet L M)
        (C₂ := euclideanRayCircleSet L M)
        (C₃ := euclideanRayRaySet L M)
        hqcc hqcr hqrc hcover
        (finset_card_le_two_of_forall_mem_euclideanCircleCircleSet hLM)
        finset_card_le_two_of_forall_mem_euclideanCircleRaySet
        finset_card_le_two_of_forall_mem_euclideanRayCircleSet
        (finset_card_le_one_of_forall_mem_euclideanRayRaySet hline)
    norm_num at h
    exact h

/-- Direct whole-carrier savings from a point common to any three circle/ray
components. -/
def pairCarrierSavingsFiveOfTripleComponentOverlap
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    {q : EuclideanR2}
    (H : PairComponentTripleOverlap L M q) :
    PairCarrierSavings L M 5 where
  carrier_card_le :=
    finset_card_le_five_of_triple_component_overlap hLM hline H

/-- Two overlap witnesses that together improve all four component estimates.
The witnesses may coincide. -/
inductive PairComponentTwoDoubleOverlap
    (L M : EuclideanLollipop) (q r : EuclideanR2) : Prop where
  | circleCircle_circleRay__rayCircle_rayRay
      (hqcc : q ∈ euclideanCircleCircleSet L M)
      (hqcr : q ∈ euclideanCircleRaySet L M)
      (hrrc : r ∈ euclideanRayCircleSet L M)
      (hrrr : r ∈ euclideanRayRaySet L M)
  | circleCircle_rayCircle__circleRay_rayRay
      (hqcc : q ∈ euclideanCircleCircleSet L M)
      (hqrc : q ∈ euclideanRayCircleSet L M)
      (hrcr : r ∈ euclideanCircleRaySet L M)
      (hrrr : r ∈ euclideanRayRaySet L M)
  | circleCircle_rayRay__circleRay_rayCircle
      (hqcc : q ∈ euclideanCircleCircleSet L M)
      (hqrr : q ∈ euclideanRayRaySet L M)
      (hrcr : r ∈ euclideanCircleRaySet L M)
      (hrrc : r ∈ euclideanRayCircleSet L M)

/-- If the two witnesses in a two-double overlap coincide, the data actually
give a point lying in all four circle/ray components. -/
theorem pairComponentTwoDoubleOverlap_all_four_of_same_point
    {L M : EuclideanLollipop} {q : EuclideanR2}
    (H : PairComponentTwoDoubleOverlap L M q q) :
    q ∈ euclideanCircleCircleSet L M ∧
      q ∈ euclideanCircleRaySet L M ∧
        q ∈ euclideanRayCircleSet L M ∧
          q ∈ euclideanRayRaySet L M := by
  cases H with
  | circleCircle_circleRay__rayCircle_rayRay hqcc hqcr hqrc hqrr =>
      exact ⟨hqcc, hqcr, hqrc, hqrr⟩
  | circleCircle_rayCircle__circleRay_rayRay hqcc hqrc hqcr hqrr =>
      exact ⟨hqcc, hqcr, hqrc, hqrr⟩
  | circleCircle_rayRay__circleRay_rayCircle hqcc hqrr hqcr hqrc =>
      exact ⟨hqcc, hqcr, hqrc, hqrr⟩

/-- Coincident two-double overlap witnesses give the stronger direct
whole-carrier `<= 4` bound. -/
theorem finset_card_le_four_of_two_double_component_overlap_same_point
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    {q : EuclideanR2}
    (H : PairComponentTwoDoubleOverlap L M q q)
    (S : Finset EuclideanR2)
    (hS : ∀ p ∈ S, p ∈ euclideanPairIntersectionSet L M) :
    S.card ≤ 4 := by
  rcases pairComponentTwoDoubleOverlap_all_four_of_same_point H with
    ⟨hqcc, hqcr, hqrc, hqrr⟩
  exact
    finset_card_le_four_of_common_all_components
      hLM hline hqcc hqcr hqrc hqrr S hS

/-- Direct whole-carrier `<= 4` savings from coincident two-double overlap
witnesses. -/
def pairCarrierSavingsFourOfTwoDoubleComponentOverlapSamePoint
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    {q : EuclideanR2}
    (H : PairComponentTwoDoubleOverlap L M q q) :
    PairCarrierSavings L M 4 where
  carrier_card_le :=
    finset_card_le_four_of_two_double_component_overlap_same_point
      hLM hline H

/-- If two overlap witnesses together improve all four circle/ray component
estimates, the whole carrier intersection has at most five points. -/
theorem finset_card_le_five_of_two_double_component_overlap
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    {q r : EuclideanR2}
    (H : PairComponentTwoDoubleOverlap L M q r)
    (S : Finset EuclideanR2)
    (hS : ∀ p ∈ S, p ∈ euclideanPairIntersectionSet L M) :
    S.card ≤ 5 := by
  have hcover₀ :
      ∀ p ∈ S,
        p ∈ euclideanCircleCircleSet L M ∨
        p ∈ euclideanCircleRaySet L M ∨
        p ∈ euclideanRayCircleSet L M ∨
        p ∈ euclideanRayRaySet L M := by
    intro p hp
    exact mem_euclideanPairIntersectionSet_iff.1 (hS p hp)
  cases H with
  | circleCircle_circleRay__rayCircle_rayRay hqcc hqcr hrrc hrrr =>
    have h :=
      finset_card_le_of_two_double_component_overlaps
        (C₀ := euclideanCircleCircleSet L M)
        (C₁ := euclideanCircleRaySet L M)
        (C₂ := euclideanRayCircleSet L M)
        (C₃ := euclideanRayRaySet L M)
        hqcc hqcr hrrc hrrr hcover₀
        (finset_card_le_two_of_forall_mem_euclideanCircleCircleSet hLM)
        finset_card_le_two_of_forall_mem_euclideanCircleRaySet
        finset_card_le_two_of_forall_mem_euclideanRayCircleSet
        (finset_card_le_one_of_forall_mem_euclideanRayRaySet hline)
    norm_num at h
    exact h
  | circleCircle_rayCircle__circleRay_rayRay hqcc hqrc hrcr hrrr =>
    have hcover :
        ∀ p ∈ S,
          p ∈ euclideanCircleCircleSet L M ∨
          p ∈ euclideanRayCircleSet L M ∨
          p ∈ euclideanCircleRaySet L M ∨
          p ∈ euclideanRayRaySet L M := by
      intro p hp
      rcases hcover₀ p hp with hcc | hcr | hrc | hrr
      · exact Or.inl hcc
      · exact Or.inr (Or.inr (Or.inl hcr))
      · exact Or.inr (Or.inl hrc)
      · exact Or.inr (Or.inr (Or.inr hrr))
    have h :=
      finset_card_le_of_two_double_component_overlaps
        (C₀ := euclideanCircleCircleSet L M)
        (C₁ := euclideanRayCircleSet L M)
        (C₂ := euclideanCircleRaySet L M)
        (C₃ := euclideanRayRaySet L M)
        hqcc hqrc hrcr hrrr hcover
        (finset_card_le_two_of_forall_mem_euclideanCircleCircleSet hLM)
        finset_card_le_two_of_forall_mem_euclideanRayCircleSet
        finset_card_le_two_of_forall_mem_euclideanCircleRaySet
        (finset_card_le_one_of_forall_mem_euclideanRayRaySet hline)
    norm_num at h
    exact h
  | circleCircle_rayRay__circleRay_rayCircle hqcc hqrr hrcr hrrc =>
    have hcover :
        ∀ p ∈ S,
          p ∈ euclideanCircleCircleSet L M ∨
          p ∈ euclideanRayRaySet L M ∨
          p ∈ euclideanCircleRaySet L M ∨
          p ∈ euclideanRayCircleSet L M := by
      intro p hp
      rcases hcover₀ p hp with hcc | hcr | hrc | hrr
      · exact Or.inl hcc
      · exact Or.inr (Or.inr (Or.inl hcr))
      · exact Or.inr (Or.inr (Or.inr hrc))
      · exact Or.inr (Or.inl hrr)
    have h :=
      finset_card_le_of_two_double_component_overlaps
        (C₀ := euclideanCircleCircleSet L M)
        (C₁ := euclideanRayRaySet L M)
        (C₂ := euclideanCircleRaySet L M)
        (C₃ := euclideanRayCircleSet L M)
        hqcc hqrr hrcr hrrc hcover
        (finset_card_le_two_of_forall_mem_euclideanCircleCircleSet hLM)
        (finset_card_le_one_of_forall_mem_euclideanRayRaySet hline)
        finset_card_le_two_of_forall_mem_euclideanCircleRaySet
        finset_card_le_two_of_forall_mem_euclideanRayCircleSet
    norm_num at h
    exact h

/-- Direct whole-carrier savings from two overlap witnesses that together
improve all four component estimates. -/
def pairCarrierSavingsFiveOfTwoDoubleComponentOverlap
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    {q r : EuclideanR2}
    (H : PairComponentTwoDoubleOverlap L M q r) :
    PairCarrierSavings L M 5 where
  carrier_card_le :=
    finset_card_le_five_of_two_double_component_overlap hLM hline H

end PrimitiveGeometry
end TheoremOneManuscript
end Lollipop
