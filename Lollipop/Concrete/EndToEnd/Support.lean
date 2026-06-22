import Lollipop.Concrete.EndToEnd.Compactification
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Convex.Segment
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Equiv.Set
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Shared geometric and finite-component support

This module isolates low-level Euclidean facts used by both the arbitrary
upper bound and the generic lower construction.  The declarations in
`EuclideanPort` are narrow API ports: their proofs are elementary coordinate
arguments (linear equations for rays and quadratic equations for circles).
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd

open Set BigOperators
open scoped Topology

/-- Determinant and dot product in displayed coordinates. -/
def detPoint (u v : Point) : ℝ := u 0 * v 1 - u 1 * v 0

def dotPoint (u v : Point) : ℝ := u 0 * v 0 + u 1 * v 1

@[simp] theorem detPoint_skew (u v : Point) :
    detPoint v u = -detPoint u v := by
  unfold detPoint
  ring

@[simp] theorem dotPoint_comm (u v : Point) :
    dotPoint v u = dotPoint u v := by
  unfold dotPoint
  ring

/-- Primitive crossing sets. -/
def cc (L M : Lollipop) : Set Point := L.circle ∩ M.circle
def cr (L M : Lollipop) : Set Point := L.circle ∩ M.stem
def rc (L M : Lollipop) : Set Point := L.stem ∩ M.circle
def rr (L M : Lollipop) : Set Point := L.stem ∩ M.stem

def pairCrossingSet (L M : Lollipop) : Set Point := L.carrier ∩ M.carrier

def pairCrossingCount (L M : Lollipop) : ℕ :=
  (pairCrossingSet L M).ncard

/-- The bundled Euclidean sphere underlying a concrete lollipop circle. -/
def concreteSphere (L : Lollipop) : EuclideanGeometry.Sphere Point where
  center := L.center
  radius := L.radius

/-- The supporting affine line of a concrete lollipop stem. -/
def stemLine (L : Lollipop) : AffineSubspace ℝ Point :=
  line[ℝ, L.center, L.center + L.radial]

/-- The concrete point space has finrank two. -/
theorem point_finrank : Module.finrank ℝ Point = 2 := by
  simp [Point]

/-- A stem point lies on the stem's supporting affine line. -/
theorem mem_stemLine_of_mem_stem
    {L : Lollipop} {x : Point} (hx : x ∈ L.stem) :
    x ∈ stemLine L := by
  rcases hx with ⟨t, _ht, rfl⟩
  have hmk :
      stemLine L =
        AffineSubspace.mk' L.center (ℝ ∙ L.radial) := by
    rw [stemLine]
    rw [← AffineSubspace.mk'_eq (left_mem_affineSpan_pair ℝ L.center (L.center + L.radial))]
    rw [direction_affineSpan, vectorSpan_pair_rev]
    simp [vsub_eq_sub]
  rw [hmk, AffineSubspace.mem_mk']
  simpa [vsub_eq_sub] using
    Submodule.smul_mem (ℝ ∙ L.radial) t
      (Submodule.mem_span_singleton_self L.radial)

theorem stemLine_direction (L : Lollipop) :
    (stemLine L).direction = ℝ ∙ L.radial := by
  rw [stemLine]
  rw [direction_affineSpan, vectorSpan_pair_rev]
  simp [vsub_eq_sub]

theorem stemLine_ne_of_detPoint_ne_zero
    {L M : Lollipop} (hdet : detPoint L.radial M.radial ≠ 0) :
    stemLine L ≠ stemLine M := by
  intro hline
  have hdir :
      ℝ ∙ L.radial = ℝ ∙ M.radial := by
    have hcongr := congrArg AffineSubspace.direction hline
    simpa [stemLine_direction] using hcongr
  have hmem : M.radial ∈ ℝ ∙ L.radial := by
    rw [hdir]
    exact Submodule.mem_span_singleton_self M.radial
  rcases Submodule.mem_span_singleton.mp hmem with ⟨c, hc⟩
  have hzero : detPoint L.radial M.radial = 0 := by
    rw [← hc]
    unfold detPoint
    simp
    ring
  exact hdet hzero

/-- A point that is topologically isolated inside a set. -/
def IsolatedPoint {X : Type*} [TopologicalSpace X] (S : Set X) (x : X) : Prop :=
  x ∈ S ∧ ∃ U ∈ 𝓝 x, U ∩ S ⊆ {x}

theorem finite_of_subsingleton_of_mem
    {α : Type*} {S : Set α} {x : α}
    (hsub : S.Subsingleton) (hx : x ∈ S) :
    S.Finite :=
  (finite_singleton x).subset (by
    intro y hy
    exact hsub hy hx)

theorem isolatedPoint_of_mem_finite
    {X : Type*} [TopologicalSpace X] [T1Space X]
    {S : Set X} (hS : S.Finite) {x : X} (hx : x ∈ S) :
    IsolatedPoint S x := by
  refine ⟨hx, ?_⟩
  let U : Set X := (S \ {x})ᶜ
  have hclosed : IsClosed (S \ {x}) := hS.diff.isClosed
  have hopen : IsOpen U := isOpen_compl_iff.2 hclosed
  have hxU : x ∈ U := by
    simp [U]
  refine ⟨U, hopen.mem_nhds hxU, ?_⟩
  intro y hy
  have hyS : y ∈ S := hy.2
  have hy_not : y ∉ S \ {x} := by simpa [U] using hy.1
  have hyx : y = x := by
    by_contra hne
    exact hy_not ⟨hyS, by simp [hne]⟩
  simp [hyx]

theorem finite_of_forall_mem_eq_left_or_right
    {α : Type*} {s : Set α}
    (h :
      ∀ ⦃a b x : α⦄, a ∈ s → b ∈ s → x ∈ s → a ≠ b →
        x = a ∨ x = b) :
    s.Finite := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · exact finite_empty
  · by_cases hsingle : ∀ x ∈ s, x = a
    · exact (finite_singleton a).subset (by
        intro x hx
        simp [hsingle x hx])
    · push Not at hsingle
      rcases hsingle with ⟨b, hb, hba⟩
      exact ((finite_singleton b).insert a).subset (by
        intro x hx
        rcases h ha hb hx hba.symm with hx_eq | hx_eq
        · simp [hx_eq]
        · simp [hx_eq])

theorem ncard_le_two_of_forall_mem_eq_left_or_right
    {α : Type*} {s : Set α}
    (h :
      ∀ ⦃a b x : α⦄, a ∈ s → b ∈ s → x ∈ s → a ≠ b →
        x = a ∨ x = b) :
    s.ncard ≤ 2 := by
  classical
  have hs : s.Finite := finite_of_forall_mem_eq_left_or_right h
  by_contra hle
  have hlt : 2 < s.ncard := Nat.lt_of_not_ge hle
  rcases (Set.two_lt_ncard_iff hs).1 hlt with
    ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩
  rcases h ha hb hc hab with hc_eq | hc_eq
  · exact hac hc_eq.symm
  · exact hbc hc_eq.symm

theorem componentCount_union_singleton_sub_one_le_one
    {X : Type*} [TopologicalSpace X] {S : Set X} {a : X}
    (hS : IsConnected S) :
    componentCount (S ∪ {a}) - 1 ≤ 1 := by
  let U : Set X := S ∪ {a}
  let base : U := ⟨hS.nonempty.some, Or.inl hS.nonempty.some_mem⟩
  let apex : U := ⟨a, Or.inr rfl⟩
  let f : Option Unit → ConnectedComponents U := fun o =>
    match o with
    | none => ConnectedComponents.mk apex
    | some _ => ConnectedComponents.mk base
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨u, rfl⟩ := ConnectedComponents.surjective_coe q
    rcases u.property with huS | hua
    · refine ⟨some (), ?_⟩
      dsimp [f]
      rw [ConnectedComponents.coe_eq_coe]
      apply connectedComponent_eq_iff_mem.2
      let SU : Set U := {z | (z : X) ∈ S}
      have hSU_conn : IsConnected SU := by
        let incl : S → U := fun z => ⟨z, Or.inl z.property⟩
        haveI : ConnectedSpace S := isConnected_iff_connectedSpace.mp hS
        have hrange : Set.range incl = SU := by
          ext z
          constructor
          · rintro ⟨w, rfl⟩
            exact w.property
          · intro hz
            exact ⟨⟨z, hz⟩, rfl⟩
        rw [← hrange]
        exact isConnected_range (by continuity : Continuous incl)
      have hbase : base ∈ SU := hS.nonempty.some_mem
      have hu : u ∈ SU := huS
      exact hSU_conn.subset_connectedComponent hu hbase
    · refine ⟨none, ?_⟩
      dsimp [f]
      congr
      ext
      have hu_eq : (u : X) = a := by simpa using hua
      exact hu_eq.symm
  haveI : Finite (ConnectedComponents U) := Finite.of_surjective f hsurj
  have hcard : Nat.card (ConnectedComponents U) ≤ Nat.card (Option Unit) :=
    Nat.card_le_card_of_surjective f hsurj
  unfold componentCount
  dsimp [U] at hcard
  have hopt : Nat.card (Option Unit) = 2 := by
    simp
  omega

theorem component_excess_union_infinity_le_one
    {S : Set Sphere2} (hS : IsConnected S) :
    componentCount (S ∪ {infinity}) - 1 ≤ 1 :=
  componentCount_union_singleton_sub_one_le_one hS

theorem concreteSphere_ne_of_circle_ne
    {L M : Lollipop} (hcircle : L.circle ≠ M.circle) :
    concreteSphere L ≠ concreteSphere M := by
  intro hsphere
  apply hcircle
  rw [L.circle_eq_sphere, M.circle_eq_sphere]
  simpa [concreteSphere] using
    congrArg (fun s : EuclideanGeometry.Sphere Point => (s : Set Point)) hsphere

theorem eq_or_eq_of_mem_cc_of_two_witnesses
    {L M : Lollipop}
    (hsphere : concreteSphere L ≠ concreteSphere M)
    {p₁ p₂ p : Point}
    (hp₁₂ : p₁ ≠ p₂)
    (hp₁ : p₁ ∈ cc L M)
    (hp₂ : p₂ ∈ cc L M)
    (hp : p ∈ cc L M) :
    p = p₁ ∨ p = p₂ := by
  exact
    EuclideanGeometry.eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two
      (V := Point) (P := Point)
      (s₁ := concreteSphere L)
      (s₂ := concreteSphere M)
      point_finrank hsphere hp₁₂ hp₁.1 hp₂.1 hp.1 hp₁.2 hp₂.2 hp.2

theorem finite_circle_intersection_of_ne
    {L M : Lollipop} (hcircle : L.circle ≠ M.circle) :
    (cc L M).Finite := by
  have hsphere : concreteSphere L ≠ concreteSphere M :=
    concreteSphere_ne_of_circle_ne hcircle
  apply finite_of_forall_mem_eq_left_or_right
  intro a b x ha hb hx hab
  exact eq_or_eq_of_mem_cc_of_two_witnesses hsphere hab ha hb hx

theorem circle_intersection_ncard_le_two
    (L M : Lollipop) (hcircle : L.circle ≠ M.circle) :
    (cc L M).ncard ≤ 2 := by
  have hsphere : concreteSphere L ≠ concreteSphere M :=
    concreteSphere_ne_of_circle_ne hcircle
  apply ncard_le_two_of_forall_mem_eq_left_or_right
  intro a b x ha hb hx hab
  exact eq_or_eq_of_mem_cc_of_two_witnesses hsphere hab ha hb hx

theorem eq_or_eq_of_mem_sphere_of_mem_stemLine_of_two_witnesses
    {s : EuclideanGeometry.Sphere Point} {L : Lollipop}
    {p₁ p₂ p : Point}
    (hp₁₂ : p₁ ≠ p₂)
    (hp₁_sphere : p₁ ∈ s)
    (hp₂_sphere : p₂ ∈ s)
    (hp_sphere : p ∈ s)
    (hp₁_line : p₁ ∈ stemLine L)
    (hp₂_line : p₂ ∈ stemLine L)
    (hp_line : p ∈ stemLine L) :
    p = p₁ ∨ p = p₂ := by
  have hline : line[ℝ, p₁, p₂] = stemLine L :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne hp₁_line hp₂_line hp₁₂
  have hp_line_pair : p ∈ line[ℝ, p₁, p₂] := by
    rwa [hline]
  have hp₂_cases :
      p₂ = p₁ ∨ p₂ = s.secondInter p₁ (p₂ -ᵥ p₁) := by
    exact
      ((s.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
        hp₁_sphere (right_mem_affineSpan_pair ℝ p₁ p₂)).2 hp₂_sphere)
  have hsecond : s.secondInter p₁ (p₂ -ᵥ p₁) = p₂ := by
    rcases hp₂_cases with hp₂_eq | hp₂_eq
    · exact False.elim (hp₁₂ hp₂_eq.symm)
    · exact hp₂_eq.symm
  have hp_cases : p = p₁ ∨ p = s.secondInter p₁ (p₂ -ᵥ p₁) := by
    exact
      ((s.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
        hp₁_sphere hp_line_pair).2 hp_sphere)
  rcases hp_cases with hp_eq | hp_eq
  · exact Or.inl hp_eq
  · exact Or.inr (hp_eq.trans hsecond)

theorem finite_circle_ray_intersection (L M : Lollipop) :
    (cr L M).Finite := by
  apply finite_of_forall_mem_eq_left_or_right
  intro a b x ha hb hx hab
  exact eq_or_eq_of_mem_sphere_of_mem_stemLine_of_two_witnesses
    (s := concreteSphere L) (L := M) hab
    ha.1 hb.1 hx.1
    (mem_stemLine_of_mem_stem ha.2)
    (mem_stemLine_of_mem_stem hb.2)
    (mem_stemLine_of_mem_stem hx.2)

theorem circle_ray_intersection_ncard_le_two (L M : Lollipop) :
    (cr L M).ncard ≤ 2 := by
  apply ncard_le_two_of_forall_mem_eq_left_or_right
  intro a b x ha hb hx hab
  exact eq_or_eq_of_mem_sphere_of_mem_stemLine_of_two_witnesses
    (s := concreteSphere L) (L := M) hab
    ha.1 hb.1 hx.1
    (mem_stemLine_of_mem_stem ha.2)
    (mem_stemLine_of_mem_stem hb.2)
    (mem_stemLine_of_mem_stem hx.2)

theorem finite_ray_circle_intersection (L M : Lollipop) :
    (rc L M).Finite := by
  simpa [rc, cr, inter_comm] using finite_circle_ray_intersection M L

theorem totallyDisconnectedSpace_of_discrete
    {X : Type*} [TopologicalSpace X] [DiscreteTopology X] :
    TotallyDisconnectedSpace X := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_singleton]
  intro x
  apply subset_antisymm
  · intro y hy
    exact (isClopen_discrete ({x} : Set X)).connectedComponent_subset (by simp) hy
  · intro y hy
    simpa using hy

noncomputable def connectedComponentsEquivSelfOfTotallyDisconnected
    (X : Type*) [TopologicalSpace X] [TotallyDisconnectedSpace X] :
    ConnectedComponents X ≃ X where
  toFun q := Quotient.out q
  invFun x := ConnectedComponents.mk x
  left_inv q := Quotient.out_eq q
  right_inv x := by
    have hq : ConnectedComponents.mk (Quotient.out (ConnectedComponents.mk x)) =
        ConnectedComponents.mk x :=
      Quotient.out_eq (ConnectedComponents.mk x)
    rw [ConnectedComponents.coe_eq_coe] at hq
    rw [connectedComponent_eq_singleton, connectedComponent_eq_singleton] at hq
    simpa using hq

@[simp] theorem pairCrossingSet_decompose (L M : Lollipop) :
    pairCrossingSet L M = cc L M ∪ rc L M ∪ cr L M ∪ rr L M := by
  ext x
  simp only [pairCrossingSet, cc, cr, rc, rr, Lollipop.carrier,
    mem_inter_iff, mem_union]
  tauto

/-- Transversality predicates in coordinates. -/
def CircleCircleTransverseAt (L M : Lollipop) (x : Point) : Prop :=
  detPoint (x - L.center) (x - M.center) ≠ 0

def StemCircleTransverseAt (L M : Lollipop) (x : Point) : Prop :=
  dotPoint L.radial (x - M.center) ≠ 0

def StemStemTransverse (L M : Lollipop) : Prop :=
  detPoint L.radial M.radial ≠ 0

theorem rr_subsingleton_of_transverse
    {L M : Lollipop} (hdet : StemStemTransverse L M) :
    (rr L M).Subsingleton := by
  intro p hp q hq
  by_contra hpq
  have hlineL : line[ℝ, p, q] = stemLine L :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne
      (mem_stemLine_of_mem_stem hp.1)
      (mem_stemLine_of_mem_stem hq.1) hpq
  have hlineM : line[ℝ, p, q] = stemLine M :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne
      (mem_stemLine_of_mem_stem hp.2)
      (mem_stemLine_of_mem_stem hq.2) hpq
  exact stemLine_ne_of_detPoint_ne_zero hdet (hlineL.symm.trans hlineM)

structure PrimitivePairwiseTransverse (L M : Lollipop) : Prop where
  cc : ∀ x, x ∈ cc L M → CircleCircleTransverseAt L M x
  cr : ∀ x, x ∈ cr L M → StemCircleTransverseAt M L x
  rc : ∀ x, x ∈ rc L M → StemCircleTransverseAt L M x
  rr : (rr L M).Nonempty → StemStemTransverse L M

/-- The stem is convex. -/
theorem stem_convex (L : Lollipop) : Convex ℝ L.stem := by
  rw [L.stem_eq_image_Ici]
  have hlin : Convex ℝ ((fun t : ℝ => t • L.radial) '' Ici (1 : ℝ)) :=
    (convex_Ici (1 : ℝ)).linear_image (LinearMap.id.smulRight L.radial)
  simpa [Lollipop.stemMap, image_image, Function.comp_def] using
    hlin.translate L.center

/-- Every compactified carrier is compact. -/
theorem isCompact_hatCarrier (L : Lollipop) : IsCompact (hatCarrier L) := by
  have hclosed : IsClosed (hatCarrier L) := by
    rw [OnePoint.isClosed_iff_of_mem (infinity_mem_hatCarrier L)]
    convert L.isClosed_carrier using 1
    ext x
    simp [hatCarrier, finiteLift, finitePoint, infinity]
  exact hclosed.isCompact

/-- Every finite compactified arrangement union is compact. -/
theorem isCompact_hatOccupied {n : ℕ} (A : Arrangement n) :
    IsCompact (hatOccupied A) := by
  classical
  exact (isCompact_iUnion fun i : Fin n => isCompact_hatCarrier (A i)).union
    isCompact_singleton

noncomputable def finiteLiftUnionInfinityEquivOption (S : Set Point) :
    ((finiteLift S ∪ ({infinity} : Set Sphere2)) : Set Sphere2) ≃ Option S := by
  classical
  let e : S ≃ finiteLift S :=
    { toFun := fun x => ⟨finitePoint x, ⟨x, x.property, rfl⟩⟩
      invFun := fun y => by
        exact ⟨Classical.choose y.property,
          (Classical.choose_spec y.property).1⟩
      left_inv := by
        intro x
        apply Subtype.ext
        let hx : finitePoint ↑x ∈ finiteLift S := ⟨↑x, x.property, rfl⟩
        exact finitePoint_injective (Classical.choose_spec hx).2
      right_inv := by
        intro y
        rcases y with ⟨y, hy⟩
        dsimp
        rcases Classical.choose_spec hy with ⟨hx, hxy⟩
        ext
        exact hxy }
  have hdisj : Disjoint (finiteLift S) ({infinity} : Set Sphere2) := by
    rw [Set.disjoint_iff]
    intro x hx
    have hxinf : x = infinity := by simpa using hx.2
    exact False.elim (infinity_not_mem_finiteLift S (hxinf ▸ hx.1))
  let singletonToOption : S ⊕ ({infinity} : Set Sphere2) ≃ Option S :=
    { toFun := fun x =>
        match x with
        | Sum.inl s => some s
        | Sum.inr _ => none
      invFun := fun x =>
        match x with
        | none => Sum.inr ⟨infinity, rfl⟩
        | some s => Sum.inl s
      left_inv := by
        intro x
        cases x with
        | inl s => rfl
        | inr y =>
            apply congrArg Sum.inr
            ext
            simpa using y.property.symm
      right_inv := by
        intro x
        cases x <;> rfl }
  exact (Equiv.Set.union hdisj).trans
    ((Equiv.sumCongr e.symm (Equiv.refl ({infinity} : Set Sphere2))).trans
      singletonToOption)

/-- A finite set plus infinity has one component per finite point and one at
infinity. -/
theorem componentCount_finiteLift_union_infinity_sub_one
    {S : Set Point} (hS : S.Finite) :
    componentCount (finiteLift S ∪ {infinity}) - 1 = S.ncard := by
  let U : Set Sphere2 := finiteLift S ∪ {infinity}
  let eU : U ≃ Option S := finiteLiftUnionInfinityEquivOption S
  haveI : Finite S := hS.to_subtype
  haveI : Finite U := Finite.of_equiv (Option S) eU.symm
  haveI : DiscreteTopology U := inferInstance
  haveI : TotallyDisconnectedSpace U := totallyDisconnectedSpace_of_discrete
  have hcomponents : ConnectedComponents U ≃ Option S :=
    (connectedComponentsEquivSelfOfTotallyDisconnected U).trans eU
  unfold componentCount
  rw [Nat.card_congr hcomponents]
  simp [Nat.card_coe_set_eq]

theorem component_excess_of_convex_finite_chart_le_one
    {S : Set Point} (hconv : Convex ℝ S) :
    componentCount (finiteLift S ∪ {infinity}) - 1 ≤ 1 := by
  by_cases hne : S.Nonempty
  · have hconn : IsConnected (finiteLift S) :=
      (hconv.isConnected hne).image finitePoint OnePoint.continuous_coe.continuousOn
    exact component_excess_union_infinity_le_one hconn
  · have hempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hfinite : S.Finite := by simp [hempty]
    rw [componentCount_finiteLift_union_infinity_sub_one hfinite]
    simp [hempty]


namespace EuclideanPort

/-- Two distinct planar circles meet in at most two points; equal circles form
one connected primitive component. -/
theorem circle_circle_components_le_two (L M : Lollipop) :
    componentCount (finiteLift (cc L M) ∪ {infinity}) - 1 ≤ 2 := by
  by_cases hsame : L.circle = M.circle
  · have hconn : IsConnected (finiteLift (cc L M)) := by
      simpa [cc, hsame, finiteLift] using
        L.isConnected_circle.image finitePoint OnePoint.continuous_coe.continuousOn
    exact (component_excess_union_infinity_le_one hconn).trans (by norm_num)
  · have hfinite : (cc L M).Finite := by
      exact finite_circle_intersection_of_ne hsame
    have hcard : (cc L M).ncard ≤ 2 :=
      circle_intersection_ncard_le_two L M hsame
    rw [componentCount_finiteLift_union_infinity_sub_one hfinite]
    exact hcard

/-- A circle and a radial ray meet in at most two connected components. -/
theorem circle_ray_components_le_two (L M : Lollipop) :
    componentCount (finiteLift (cr L M) ∪ {infinity}) - 1 ≤ 2 := by
  have hfinite : (cr L M).Finite :=
    finite_circle_ray_intersection L M
  have hcard : (cr L M).ncard ≤ 2 :=
    circle_ray_intersection_ncard_le_two L M
  rw [componentCount_finiteLift_union_infinity_sub_one hfinite]
  exact hcard

/-- Symmetric mixed bound. -/
theorem ray_circle_components_le_two (L M : Lollipop) :
    componentCount (finiteLift (rc L M) ∪ {infinity}) - 1 ≤ 2 := by
  simpa [rc, cr, inter_comm] using circle_ray_components_le_two M L

/-- Two rays have at most one finite connected component after removing the
common infinity component, including overlapping collinear rays. -/
theorem ray_ray_components_le_one (L M : Lollipop) :
    componentCount (finiteLift (rr L M) ∪ {infinity}) - 1 ≤ 1 := by
  have hconv : Convex ℝ (rr L M) := (stem_convex L).inter (stem_convex M)
  exact component_excess_of_convex_finite_chart_le_one hconv

/-- A finite transverse primitive pair has one connected component for every
finite crossing, plus infinity. -/
theorem pairExcess_eq_ncard_of_transverse
    {L M : Lollipop}
    (hfinite : (pairCrossingSet L M).Finite)
    (_htrans : PrimitivePairwiseTransverse L M)
    (_hnoTriple :
      (Set.univ : Set (Fin 4)).PairwiseDisjoint (fun k : Fin 4 =>
        match k with
        | 0 => cc L M
        | 1 => rc L M
        | 2 => cr L M
        | 3 => rr L M)) :
    pairExcessNat L M = pairCrossingCount L M := by
  have hhat : hatPairIntersection L M =
      finiteLift (pairCrossingSet L M) ∪ {infinity} := by
    ext x
    cases x using OnePoint.rec with
    | infty =>
        simp [hatPairIntersection, hatCarrier, finiteLift, finitePoint, infinity]
    | coe p =>
        simp [hatPairIntersection, hatCarrier, pairCrossingSet, finiteLift,
          finitePoint, infinity]
  rw [pairExcessNat, hhat,
    componentCount_finiteLift_union_infinity_sub_one hfinite]
  rfl

/-- A transverse circle--circle intersection is isolated. -/
theorem isolated_cc_of_transverse
    {L M : Lollipop} {x : Point}
    (hx : x ∈ cc L M) (h : CircleCircleTransverseAt L M x) :
    IsolatedPoint (cc L M) x := by
  have hsphere : concreteSphere L ≠ concreteSphere M := by
    intro hsphere
    have hcenter : L.center = M.center :=
      congrArg EuclideanGeometry.Sphere.center hsphere
    have hzero : detPoint (x - L.center) (x - M.center) = 0 := by
      rw [hcenter]
      unfold detPoint
      ring
    exact h hzero
  have hfinite : (cc L M).Finite := by
    apply finite_of_forall_mem_eq_left_or_right
    intro a b y ha hb hy hab
    exact eq_or_eq_of_mem_cc_of_two_witnesses hsphere hab ha hb hy
  exact isolatedPoint_of_mem_finite hfinite hx

/-- A transverse mixed intersection is isolated. -/
theorem isolated_rc_of_transverse
    {L M : Lollipop} {x : Point}
    (hx : x ∈ rc L M) (_h : StemCircleTransverseAt L M x) :
    IsolatedPoint (rc L M) x := by
  exact isolatedPoint_of_mem_finite (finite_ray_circle_intersection L M) hx

/-- A transverse ray--ray point is isolated. -/
theorem isolated_rr_of_transverse
    {L M : Lollipop} {x : Point}
    (hx : x ∈ rr L M) (h : StemStemTransverse L M) :
    IsolatedPoint (rr L M) x := by
  exact isolatedPoint_of_mem_finite
    (finite_of_subsingleton_of_mem (rr_subsingleton_of_transverse h) hx) hx

end EuclideanPort

/-- Finite unions of connected sets sharing a common point are connected. -/
theorem isConnected_iUnion_of_common
    {ι X : Type*} [Fintype ι] [TopologicalSpace X]
    {S : ι → Set X}
    (hS : ∀ i, IsConnected (S i))
    (p : X) (hp : ∀ i, p ∈ S i) (i0 : ι) :
    IsConnected (⋃ i, S i) := by
  have hInter : (⋂ i : ι, S i).Nonempty := by
    refine ⟨p, ?_⟩
    simpa using hp
  refine ⟨⟨p, Set.mem_iUnion_of_mem i0 (hp i0)⟩, ?_⟩
  exact isPreconnected_iUnion (s := S) hInter (fun i => (hS i).isPreconnected)

end EndToEnd
end Concrete
end Lollipop
