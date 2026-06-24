import Lollipop.Concrete.EndToEnd.CircleInsertion
import Lollipop.Concrete.EndToEnd.CircleJordan
import Lollipop.Concrete.EndToEnd.JordanClassifier
import Lollipop.Concrete.EndToEnd.LocalizedTopology

/-!
# Main theorem spine: topology

This file states the concrete topology theorems needed by the final
certificate-free endpoint.

The missing topology is intentionally exposed as named `sorry`s here.  Future
supporting lemmas should be added only to remove these theorem-body `sorry`s.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace MainTheorem
namespace Topology

/-- At the first insertion there are no previous indices. -/
theorem previousIndices_zero_eq_empty {n : ℕ} (hk : 0 < n) :
    InsertionFan.previousIndices (⟨0, hk⟩ : Fin n) = ∅ := by
  ext i
  constructor
  · intro hi
    have hlt : i < (⟨0, hk⟩ : Fin n) := by
      simpa [InsertionFan.previousIndices] using hi
    change i.1 < 0 at hlt
    omega
  · intro hi
    simp at hi

/-- The first insertion fan is just the distinguished point at infinity. -/
theorem insertionFan_zero_eq_singleton_infinity
    {n : ℕ} (A : Arrangement n) (hk : 0 < n) :
    InsertionFan.insertionFan A 0 hk = ({infinity} : Set Sphere2) := by
  unfold InsertionFan.insertionFan
  rw [previousIndices_zero_eq_empty hk]
  ext z
  simp [InsertionFan.pairIntersectionFan, pointedFinsetUnion]

/-- The first insertion fan has component count one. -/
theorem componentCount_insertionFan_zero
    {n : ℕ} (A : Arrangement n) (hk : 0 < n) :
    componentCount (InsertionFan.insertionFan A 0 hk) = 1 := by
  rw [insertionFan_zero_eq_singleton_infinity A hk]
  exact componentCount_singleton infinity

/-- The unique old complement component for an insertion over the empty
carrier. -/
noncomputable def firstLollipopActive (L : Lollipop) :
    ConnectedComponents (((∅ : Set Point)ᶜ) : Set Point) :=
  ConnectedComponents.mk
    (⟨L.center, by simp⟩ : (((∅ : Set Point)ᶜ) : Set Point))

/-- All points in the complement of the empty carrier lie in the same old
component. -/
theorem connectedComponents_empty_compl_eq
    (x y : (((∅ : Set Point)ᶜ) : Set Point)) :
    ConnectedComponents.mk x = ConnectedComponents.mk y := by
  have hconn : IsConnected (Set.univ : Set Point) := isConnected_univ
  exact ComponentLifting.connectedComponents_mk_eq_of_isConnected_subset
    (P := Set.univ) (S := ((∅ : Set Point)ᶜ))
    hconn (by intro z _hz; simp) (by simp) (by simp)

/-- The whole first lollipop carrier is localized in the unique old component
of the empty-carrier complement. -/
theorem firstLollipopEdgeLocalized (L : Lollipop) :
    LocalInsertion.EdgeLocalized (∅ : Set Point) L.carrier
      (firstLollipopActive L) := by
  intro z _hzCarrier hzOld
  exact connectedComponents_empty_compl_eq
    (⟨z, hzOld⟩ : (((∅ : Set Point)ᶜ) : Set Point))
    (⟨L.center, by simp⟩ : (((∅ : Set Point)ᶜ) : Set Point))

/-- The remaining bounded classifier for the complement of one full lollipop
carrier. -/
theorem firstLollipopCircle_subset_extension (L : Lollipop) :
    L.circle ⊆
      LocalInsertion.carrierExtension (∅ : Set Point) L.carrier := by
  intro x hx
  exact Or.inr (Lollipop.circle_subset_carrier L hx)

/-- The Boolean Jordan-side labels cover `Fin 2`. -/
theorem boolToFin2_surjective :
    Function.Surjective JordanClassifier.boolToFin2 := by
  intro b
  fin_cases b
  · exact ⟨false, by simp [JordanClassifier.boolToFin2]⟩
  · exact ⟨true, by simp [JordanClassifier.boolToFin2]⟩

/-- Passing from the full first-lollipop complement to the circle complement
does not lose either circle-complement component. -/
theorem firstLollipopCircleComponentMap_surjective (L : Lollipop) :
    Function.Surjective
      (ComponentFibers.inclusionMap
        (ComponentSurjectivity.complementSubset
          (firstLollipopCircle_subset_extension L))) := by
  exact
    ComponentSurjectivity.componentMap_surjective_of_closed_of_subset_union_carrier
      (firstLollipopCircle_subset_extension L)
      (CircleInsertion.isClosed_of_isSimpleClosedCurve
        (CircleJordan.isSimpleClosedCurve_circle L))
      L
      (by
        intro x hx
        rcases hx with hxEmpty | hxCarrier
        · exact False.elim hxEmpty
        · exact Or.inr hxCarrier)

/-- The inside of the metric circle, regarded as a subset of the circle
complement. -/
def circleComplementInside (L : Lollipop) :
    Set (L.circleᶜ : Set Point) :=
  {z | z.1 ∈ Metric.ball L.center L.radius}

/-- Inside/outside is clopen in the complement of the circle. -/
theorem circleComplementInside_isClopen (L : Lollipop) :
    IsClopen (circleComplementInside L) := by
  constructor
  · rw [← isOpen_compl_iff]
    have hcompl :
        (circleComplementInside L)ᶜ =
          {z : (L.circleᶜ : Set Point) | L.radius < dist z.1 L.center} := by
      ext z
      constructor
      · intro hz
        simp only [circleComplementInside, Set.mem_compl_iff,
          Set.mem_setOf_eq, Metric.mem_ball] at hz ⊢
        have hne : dist z.1 L.center ≠ L.radius := by
          intro hdist
          exact z.2 (by
            simpa [Lollipop.circle, dist_eq_norm] using hdist)
        exact lt_of_le_of_ne (le_of_not_gt hz) (Ne.symm hne)
      · intro hz
        simp only [circleComplementInside, Set.mem_compl_iff,
          Set.mem_setOf_eq, Metric.mem_ball]
        exact not_lt_of_ge (le_of_lt hz)
    rw [hcompl]
    exact isOpen_lt continuous_const
      (continuous_subtype_val.dist continuous_const)
  · exact Metric.isOpen_ball.preimage continuous_subtype_val

/-- Equal circle-complement components have the same inside/outside status. -/
theorem circleComponent_mem_ball_iff (L : Lollipop)
    {x y : (L.circleᶜ : Set Point)}
    (hxy : ConnectedComponents.mk x = ConnectedComponents.mk y) :
    x.1 ∈ Metric.ball L.center L.radius ↔
      y.1 ∈ Metric.ball L.center L.radius := by
  constructor
  · intro hx
    have hyComponent : y ∈ connectedComponent x := by
      have hcomp : connectedComponent x = connectedComponent y :=
        ConnectedComponents.coe_eq_coe.mp hxy
      rw [hcomp]
      exact mem_connectedComponent
    exact (circleComplementInside_isClopen L).connectedComponent_subset
      hx hyComponent
  · intro hy
    have hxComponent : x ∈ connectedComponent y := by
      have hcomp : connectedComponent y = connectedComponent x :=
        ConnectedComponents.coe_eq_coe.mp hxy.symm
      rw [hcomp]
      exact mem_connectedComponent
    exact (circleComplementInside_isClopen L).connectedComponent_subset
      hy hxComponent

/-- The open disk bounded by a lollipop circle is disjoint from the full
lollipop carrier. -/
theorem metricBall_disjoint_carrier (L : Lollipop) :
    Disjoint (Metric.ball L.center L.radius) L.carrier := by
  rw [Set.disjoint_left]
  intro z hzBall hzCarrier
  have hzDistLt : dist z L.center < L.radius := by
    simpa [Metric.mem_ball] using hzBall
  rcases hzCarrier with hzCircle | hzStem
  · have hzDistEq : dist z L.center = L.radius := by
      simpa [Lollipop.circle, dist_eq_norm] using hzCircle
    linarith
  · rcases hzStem with ⟨t, ht, rfl⟩
    have htNonneg : 0 ≤ t := le_trans zero_le_one ht
    have hdist :
        dist (L.center + t • L.radial) L.center = t * L.radius := by
      rw [dist_eq_norm]
      have hvec :
          L.center + t • L.radial - L.center = t • L.radial := by
        module
      rw [hvec, norm_smul, Real.norm_eq_abs, abs_of_nonneg htNonneg,
        Lollipop.radius]
    rw [hdist] at hzDistLt
    nlinarith [L.radius_pos, ht]

/-- The remaining first-lollipop exterior slit theorem.

Both points are in the complement of the full lollipop carrier and strictly
outside the metric circle.  The missing geometric content is that the exterior
of the circle remains connected after deleting the outward stem. -/
theorem firstLollipopExteriorStemSlit_component_eq (L : Lollipop)
    (x y :
      ((LocalInsertion.carrierExtension (∅ : Set Point) L.carrier)ᶜ :
        Set Point))
    (hxExterior : L.radius < dist x.1 L.center)
    (hyExterior : L.radius < dist y.1 L.center) :
    ConnectedComponents.mk x = ConnectedComponents.mk y := by
  sorry

/-- The first-lollipop arc-lifting theorem.

This is the concrete topology statement that the outward stem does not split
either Jordan side of the circle: if two points in the complement of the full
lollipop carrier map to the same circle-complement component, then they can be
joined by a simple arc avoiding the full carrier. -/
theorem firstLollipopActiveSideArcLifting (L : Lollipop) :
    JordanClassifier.ActiveSideArcLifting
      (LocalInsertion.old_subset_carrierExtension
        (∅ : Set Point) L.carrier)
      (firstLollipopCircle_subset_extension L)
      (CircleJordan.isSimpleClosedCurve_circle L)
      (firstLollipopActive L) := by
  intro x y _hxold _hyold hside hxy
  have hcircleComponent :
      ComponentFibers.inclusionMap
          (ComponentSurjectivity.complementSubset
            (firstLollipopCircle_subset_extension L))
          (ConnectedComponents.mk x) =
        ComponentFibers.inclusionMap
          (ComponentSurjectivity.complementSubset
            (firstLollipopCircle_subset_extension L))
          (ConnectedComponents.mk y) := by
    apply (JordanClassifier.jordanComplementComponentsEquivBool
      (CircleJordan.isSimpleClosedCurve_circle L)).injective
    apply JordanClassifier.boolToFin2_injective
    simpa [JordanClassifier.sideOfComponent] using hside
  have hKclosed :
      IsClosed (LocalInsertion.carrierExtension (∅ : Set Point) L.carrier) := by
    simpa [LocalInsertion.carrierExtension] using L.isClosed_carrier
  have hcarrierComponent :
      ConnectedComponents.mk x = ConnectedComponents.mk y := by
    have hcircleMk :
        ConnectedComponents.mk
            (ComponentFibers.inclusion
              (ComponentSurjectivity.complementSubset
                (firstLollipopCircle_subset_extension L)) x) =
          ConnectedComponents.mk
            (ComponentFibers.inclusion
              (ComponentSurjectivity.complementSubset
                (firstLollipopCircle_subset_extension L)) y) := by
      simpa using hcircleComponent
    by_cases hxInside : x.1 ∈ Metric.ball L.center L.radius
    · have hyInside : y.1 ∈ Metric.ball L.center L.radius :=
        (circleComponent_mem_ball_iff L hcircleMk).1 hxInside
      let P : Set Point := segment ℝ x.1 y.1
      have hP : IsSimpleArcEnd P x.1 y.1 := by
        exact segment_isSimpleArcEnd hxy
      have hPball : P ⊆ Metric.ball L.center L.radius := by
        exact (convex_ball L.center L.radius).segment_subset
          hxInside hyInside
      have hPdisj : Disjoint P
          (LocalInsertion.carrierExtension (∅ : Set Point) L.carrier) := by
        simpa [LocalInsertion.carrierExtension] using
          (metricBall_disjoint_carrier L).mono_left hPball
      exact JordanBridge.connectedComponents_mk_eq_of_simpleArcLifting
        x y hP hPdisj
    · -- Remaining exterior stem-slit step: the exterior of the circle minus
      -- the outward stem is connected.
      have hyOutsideBall : y.1 ∉ Metric.ball L.center L.radius := by
        intro hyInside
        exact hxInside ((circleComponent_mem_ball_iff L hcircleMk).2 hyInside)
      have hxExterior : L.radius < dist x.1 L.center := by
        simp only [Metric.mem_ball] at hxInside
        have hne : dist x.1 L.center ≠ L.radius := by
          intro hdist
          exact x.2 (by
            unfold LocalInsertion.carrierExtension Lollipop.carrier
            exact Or.inr (Or.inl (by
              simpa [Lollipop.circle, dist_eq_norm] using hdist)))
        exact lt_of_le_of_ne (le_of_not_gt hxInside) (Ne.symm hne)
      have hyExterior : L.radius < dist y.1 L.center := by
        simp only [Metric.mem_ball] at hyOutsideBall
        have hne : dist y.1 L.center ≠ L.radius := by
          intro hdist
          exact y.2 (by
            unfold LocalInsertion.carrierExtension Lollipop.carrier
            exact Or.inr (Or.inl (by
              simpa [Lollipop.circle, dist_eq_norm] using hdist)))
        exact lt_of_le_of_ne (le_of_not_gt hyOutsideBall) (Ne.symm hne)
      exact firstLollipopExteriorStemSlit_component_eq
        L x y hxExterior hyExterior
  exact JordanBridge.exists_simpleArcEnd_disjoint_of_connectedComponents_mk_eq
    hKclosed x y hcarrierComponent hxy

/-- The first-lollipop side-realization theorem.

This is the concrete topology statement that both Jordan sides of the circle
are represented by points avoiding the full lollipop carrier. -/
theorem firstLollipopActiveSideSurjective (L : Lollipop) :
    JordanClassifier.ActiveSideSurjective
      (LocalInsertion.old_subset_carrierExtension
        (∅ : Set Point) L.carrier)
      (firstLollipopCircle_subset_extension L)
      (CircleJordan.isSimpleClosedCurve_circle L)
      (firstLollipopActive L) := by
  intro target
  rcases boolToFin2_surjective target with ⟨side, hside⟩
  let circleComponent : ConnectedComponents (L.circleᶜ : Set Point) :=
    (JordanClassifier.jordanComplementComponentsEquivBool
      (CircleJordan.isSimpleClosedCurve_circle L)).symm side
  obtain ⟨carrierComponent, hcarrierComponent⟩ :=
    firstLollipopCircleComponentMap_surjective L circleComponent
  have hactive :
      ComponentFibers.inclusionMap
          (ComponentSurjectivity.complementSubset
            (LocalInsertion.old_subset_carrierExtension
              (∅ : Set Point) L.carrier))
          carrierComponent =
        firstLollipopActive L := by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe carrierComponent
    rw [ComponentFibers.inclusionMap_mk]
    exact connectedComponents_empty_compl_eq
      (ComponentFibers.inclusion
        (ComponentSurjectivity.complementSubset
          (LocalInsertion.old_subset_carrierExtension
            (∅ : Set Point) L.carrier)) x)
      (⟨L.center, by simp⟩ : (((∅ : Set Point)ᶜ) : Set Point))
  refine ⟨⟨carrierComponent, hactive⟩, ?_⟩
  simp [JordanClassifier.sideOfComponent, circleComponent,
    hcarrierComponent, hside]

/-- The bounded classifier for the complement of one full lollipop carrier. -/
noncomputable def firstLollipopActiveClassifier (L : Lollipop) :
    LocalFiltration.ActiveClassifier (∅ : Set Point) L.carrier
      (firstLollipopActive L) :=
  fun a =>
    JordanClassifier.sideOfComponent
      (firstLollipopCircle_subset_extension L)
      (CircleJordan.isSimpleClosedCurve_circle L)
      a.1

/-- The bounded classifier is injective: a single full lollipop carrier
creates at most two complementary components. -/
theorem firstLollipopActiveClassifier_injective (L : Lollipop) :
    Function.Injective (firstLollipopActiveClassifier L) := by
  exact JordanClassifier.activeSide_injective_of_arcLifting
    (LocalInsertion.old_subset_carrierExtension (∅ : Set Point) L.carrier)
    (firstLollipopCircle_subset_extension L)
    (CircleJordan.isSimpleClosedCurve_circle L)
    (firstLollipopActive L)
    (firstLollipopActiveSideArcLifting L)

/-- The bounded classifier is surjective: a single full lollipop carrier
really has both complementary sides. -/
theorem firstLollipopActiveClassifier_surjective (L : Lollipop) :
    Function.Surjective (firstLollipopActiveClassifier L) := by
  exact firstLollipopActiveSideSurjective L

/-- The bounded one-edge topology statement for a single lollipop over the
empty old carrier.

This is the real first-lollipop upper topology theorem: the complement of a
single lollipop carrier has at most two components. -/
noncomputable def firstLollipopLocalizedEdgeStep (L : Lollipop) :
    LocalFiltration.LocalizedEdgeStep (∅ : Set Point) L.carrier where
  active := firstLollipopActive L
  localized := firstLollipopEdgeLocalized L
  activeClassifier := firstLollipopActiveClassifier L
  active_injective := firstLollipopActiveClassifier_injective L

/-- The exact one-edge topology statement for a single lollipop over the
empty old carrier.

This is the real first-lollipop exact topology theorem: the complement of a
single lollipop carrier has exactly two components, witnessed by both sides
of the circle after accounting for the outward stem. -/
noncomputable def firstLollipopLocalizedExactEdgeStep (L : Lollipop) :
    LocalFiltration.LocalizedExactEdgeStep L (∅ : Set Point) L.carrier where
  old_closed := isClosed_empty
  edge_subset_carrier := fun _ hx => hx
  active := firstLollipopActive L
  localized := firstLollipopEdgeLocalized L
  activeClassifier := firstLollipopActiveClassifier L
  active_injective := firstLollipopActiveClassifier_injective L
  active_surjective := firstLollipopActiveClassifier_surjective L

/-- The remaining first-lollipop bounded topology theorem.

Mathematically, this says inserting one lollipop into the empty carrier is a
single localized split: the circle supplies the Jordan separation, while the
outward stem lies on the exterior side and creates no additional component. -/
noncomputable def firstInsertionLocalizedFiltration
    {n : ℕ} (A : Arrangement n) (hk : 0 < n) :
    InsertionFiltration.LocalizedInsertionFiltration
      (PlanarInsertion.prefixArrangement A 0 (Nat.le_of_lt hk))
      (A ⟨0, hk⟩) 1 := by
  let L := A ⟨0, hk⟩
  let f : LocalFiltration.LocalizedEdgeFiltration 1 (∅ : Set Point)
      (LocalInsertion.carrierExtension (∅ : Set Point) L.carrier) :=
    LocalFiltration.LocalizedEdgeFiltration.snoc
      (LocalFiltration.LocalizedEdgeFiltration.nil (∅ : Set Point))
      L.carrier
      (firstLollipopLocalizedEdgeStep L)
  simpa [InsertionFiltration.LocalizedInsertionFiltration, L,
    occupied_zero, LocalInsertion.carrierExtension] using f

/-- The exact first-lollipop topology theorem.

This strengthens `firstInsertionLocalizedFiltration` by proving that the two
Jordan sides are both realized, so the first insertion increases the region
count by exactly one. -/
noncomputable def firstInsertionLocalizedExactFiltration
    {n : ℕ} (A : Arrangement n) (hk : 0 < n) :
    InsertionFiltration.LocalizedExactInsertionFiltration
      (PlanarInsertion.prefixArrangement A 0 (Nat.le_of_lt hk))
      (A ⟨0, hk⟩) 1 := by
  let L := A ⟨0, hk⟩
  let f : LocalFiltration.LocalizedExactEdgeFiltration L 1
      (∅ : Set Point)
      (LocalInsertion.carrierExtension (∅ : Set Point) L.carrier) :=
    LocalFiltration.LocalizedExactEdgeFiltration.snoc
      (LocalFiltration.LocalizedExactEdgeFiltration.nil (L := L)
        (∅ : Set Point))
      L.carrier
      (firstLollipopLocalizedExactEdgeStep L)
  simpa [InsertionFiltration.LocalizedExactInsertionFiltration, L,
    occupied_zero, LocalInsertion.carrierExtension] using f

/-- Arbitrary bounded topology for the first ordered insertion. -/
theorem localizedInsertionFiltration_bound_zero
    {n : ℕ} (A : Arrangement n) (hk : 0 < n) :
    ∃ m : ℕ,
    ∃ _f : InsertionFiltration.LocalizedInsertionFiltration
        (PlanarInsertion.prefixArrangement A 0 (Nat.le_of_lt hk))
        (A ⟨0, hk⟩) m,
      (m : ℚ) ≤
        (componentCount (InsertionFan.insertionFan A 0 hk) : ℚ) := by
  refine ⟨1, firstInsertionLocalizedFiltration A hk, ?_⟩
  rw [componentCount_insertionFan_zero A hk]

/-- Generic exact topology for the first ordered insertion. -/
theorem localizedExactInsertionFiltration_zero
    {n : ℕ} (A : Arrangement n) (hk : 0 < n) :
    ∃ m : ℕ,
    ∃ _f : InsertionFiltration.LocalizedExactInsertionFiltration
        (PlanarInsertion.prefixArrangement A 0 (Nat.le_of_lt hk))
        (A ⟨0, hk⟩) m,
      m = componentCount (InsertionFan.insertionFan A 0 hk) := by
  refine ⟨1, firstInsertionLocalizedExactFiltration A hk, ?_⟩
  rw [componentCount_insertionFan_zero A hk]

/-- Remaining arbitrary topology theorem for non-first insertions. -/
theorem localizedInsertionFiltration_bound_positive
    {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n) (hkpos : 0 < k) :
    ∃ m : ℕ,
    ∃ _f : InsertionFiltration.LocalizedInsertionFiltration
        (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk))
        (A ⟨k, hk⟩) m,
      (m : ℚ) ≤
        (componentCount (InsertionFan.insertionFan A k hk) : ℚ) := by
  sorry

/-- Arbitrary localized filtration for one ordered insertion.

This is the exact topology object required for one insertion step: subdivide
the inserted lollipop relative to its old-new fan and build a localized edge
filtration whose length is bounded by the fan component count. -/
theorem localizedInsertionFiltration_bound
    {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n) :
    ∃ m : ℕ,
    ∃ _f : InsertionFiltration.LocalizedInsertionFiltration
        (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk))
        (A ⟨k, hk⟩) m,
      (m : ℚ) ≤
        (componentCount (InsertionFan.insertionFan A k hk) : ℚ) := by
  by_cases hzero : k = 0
  · subst k
    exact localizedInsertionFiltration_bound_zero A hk
  · exact localizedInsertionFiltration_bound_positive A k hk
      (Nat.pos_of_ne_zero hzero)

/-- Remaining exact topology theorem for non-first generic insertions. -/
theorem localizedExactInsertionFiltration_of_generic_positive
    {n : ℕ} {A : Arrangement n} (hA : IsGeneric A)
    (k : ℕ) (hk : k < n) (hkpos : 0 < k) :
    ∃ m : ℕ,
    ∃ _f : InsertionFiltration.LocalizedExactInsertionFiltration
        (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk))
        (A ⟨k, hk⟩) m,
      m = componentCount (InsertionFan.insertionFan A k hk) := by
  sorry

/-- Arbitrary-arrangement localized insertion topology.

This is the Lean replacement target for the manuscript's arbitrary
topological region inequality.  It must eventually be proved by finite
localized filtrations for every ordered lollipop insertion. -/
theorem arbitrary_localized_topology :
    ∀ {n : ℕ} (A : Arrangement n),
      LocalizedTopology.OrderedLocalizedFiltrationBound A := by
  intro n A k hk
  exact localizedInsertionFiltration_bound A k hk

/-- Exact localized filtration for one generic ordered insertion.

This is the exact topology object required for the manuscript's generic Euler
equality: in generic position the localized filtration length is exactly the
old-new insertion-fan component count. -/
theorem localizedExactInsertionFiltration_of_generic
    {n : ℕ} {A : Arrangement n} (hA : IsGeneric A)
    (k : ℕ) (hk : k < n) :
    ∃ m : ℕ,
    ∃ _f : InsertionFiltration.LocalizedExactInsertionFiltration
        (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk))
        (A ⟨k, hk⟩) m,
      m = componentCount (InsertionFan.insertionFan A k hk) := by
  by_cases hzero : k = 0
  · subst k
    exact localizedExactInsertionFiltration_zero A hk
  · exact localizedExactInsertionFiltration_of_generic_positive hA k hk
      (Nat.pos_of_ne_zero hzero)

/-- Generic exact localized insertion topology.

This is the Lean replacement target for the manuscript's generic Euler
region formula.  It must eventually be proved by exact localized filtrations
whose length is the insertion-fan component count. -/
theorem generic_exact_localized_topology :
    ∀ {n : ℕ} {A : Arrangement n}, IsGeneric A →
      LocalizedTopology.OrderedExactLocalizedFiltration A := by
  intro n A hA k hk
  exact localizedExactInsertionFiltration_of_generic hA k hk

/-- The fan-topology package obtained from the two main topology theorems. -/
def fanTopologyPorts : InsertionFan.FanTopologyPorts :=
  LocalizedTopology.fanTopologyPorts_of_localizedFiltrations
    arbitrary_localized_topology
    generic_exact_localized_topology

/-- The older planar-topology package consumed by upper and lower endpoints. -/
def planarTopologyPorts : PlanarTopologyPorts :=
  fanTopologyPorts.toPlanarTopologyPorts

/-- Finiteness of complement connected components, as supplied by topology. -/
theorem region_components_finite {n : ℕ} (A : Arrangement n) :
    Finite (ConnectedComponents (FreeSpace A)) :=
  planarTopologyPorts.region_components_finite A

/-- Concrete arbitrary topological region inequality. -/
theorem topological_region_inequality {n : ℕ} (A : Arrangement n) :
    regionCountRat A - (n : ℚ) - 1 ≤
      Lollipop.pairSum n (pairExcessTable A) :=
  planarTopologyPorts.crossing_excess_le_pairSum A

/-- Concrete generic Euler region equality. -/
theorem generic_euler_region_eq {n : ℕ} {A : Arrangement n}
    (hA : IsGeneric A) :
    regionCountRat A = ((totalCrossingsNat A : ℕ) : ℚ) + (n : ℚ) + 1 :=
  planarTopologyPorts.generic_region_eq hA

end Topology
end MainTheorem
end EndToEnd
end Concrete
end Lollipop
