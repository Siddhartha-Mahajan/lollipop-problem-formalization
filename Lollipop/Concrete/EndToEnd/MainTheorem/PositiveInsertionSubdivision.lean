import Lollipop.Concrete.EndToEnd.LocalizedTopology
import Lollipop.Concrete.EndToEnd.LocalCrosscut
import Lollipop.Concrete.EndToEnd.OccupiedTopology
import Lollipop.Concrete.EndToEnd.PrimitiveArcs
import Mathlib.Tactic

/-!
# Positive insertion subdivision target

This file isolates the remaining planar-subdivision construction for
non-first insertions.  The downstream API already knows how to turn localized
edge filtrations into insertion split chains; what is still missing is the
geometric construction of such filtrations by subdividing the inserted
lollipop against the previous carrier.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace MainTheorem

open Set

/-- Every insertion fan contains the compactification point at infinity. -/
theorem infinity_mem_insertionFan
    {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n) :
    infinity ∈ InsertionFan.insertionFan A k hk := by
  simp [InsertionFan.insertionFan, InsertionFan.pairIntersectionFan,
    pointedFinsetUnion]

/-- Every insertion fan is nonempty. -/
theorem insertionFan_nonempty
    {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n) :
    (InsertionFan.insertionFan A k hk).Nonempty :=
  ⟨infinity, infinity_mem_insertionFan A k hk⟩

/-- The component type of every insertion fan is nonempty. -/
theorem connectedComponents_insertionFan_nonempty
    {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n) :
    Nonempty
      (ConnectedComponents (InsertionFan.insertionFan A k hk)) :=
  ConnectedComponents.nonempty_iff_nonempty.mpr
    ⟨⟨infinity, infinity_mem_insertionFan A k hk⟩⟩

/-- The component type of every insertion fan is finite. -/
theorem finite_connectedComponents_insertionFan
    {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n) :
    Finite
      (ConnectedComponents (InsertionFan.insertionFan A k hk)) := by
  classical
  let s := InsertionFan.previousIndices (⟨k, hk⟩ : Fin n)
  let L := A ⟨k, hk⟩
  change Finite (ConnectedComponents
    (pointedFinsetUnion infinity s
      (fun i => hatPairIntersection (A i) L)))
  let Idx := {i // i ∈ s}
  let T : Option Idx → Set Sphere2
    | none => {infinity}
    | some i => hatPairIntersection (A i.1) L
  have hTfinite : ∀ o : Option Idx,
      Finite (ConnectedComponents (T o)) := by
    intro o
    cases o with
    | none =>
        dsimp [T]
        exact finite_connectedComponents_of_finite_set
          (finite_singleton infinity)
    | some i =>
        dsimp [T]
        exact PairGeometry.finite_connectedComponents_hatPairIntersection
          (A i.1) L
  haveI (o : Option Idx) : Finite (ConnectedComponents (T o)) :=
    hTfinite o
  have hunion :
      pointedFinsetUnion infinity s
          (fun i => hatPairIntersection (A i) L) =
        ⋃ o : Option Idx, T o := by
    ext z
    constructor
    · intro hz
      rcases hz with hz | hz
      · exact Set.mem_iUnion_of_mem none hz
      · rcases Set.mem_iUnion.mp hz with ⟨i, hi⟩
        exact Set.mem_iUnion_of_mem (some i) hi
    · intro hz
      rcases Set.mem_iUnion.mp hz with ⟨o, ho⟩
      cases o with
      | none => exact Or.inl ho
      | some i => exact Or.inr (Set.mem_iUnion_of_mem i ho)
  rw [hunion]
  exact finite_connectedComponents_iUnion

/-- Every insertion fan has positive component count. -/
theorem componentCount_insertionFan_pos
    {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n) :
    0 < componentCount (InsertionFan.insertionFan A k hk) := by
  haveI : Finite
      (ConnectedComponents (InsertionFan.insertionFan A k hk)) :=
    finite_connectedComponents_insertionFan A k hk
  haveI : Nonempty
      (ConnectedComponents (InsertionFan.insertionFan A k hk)) :=
    connectedComponents_insertionFan_nonempty A k hk
  exact Nat.card_pos

/-- Rational form of the universal one-edge insertion-fan budget. -/
theorem one_le_componentCount_insertionFan_cast
    {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n) :
    (1 : ℚ) ≤
      (componentCount (InsertionFan.insertionFan A k hk) : ℚ) := by
  exact_mod_cast
    (Nat.succ_le_of_lt (componentCount_insertionFan_pos A k hk))

/-- The old complement component containing a chosen point of a connected
edge outside the old carrier. -/
noncomputable def connectedEdgeActiveComponent
    (C E : Set Point) (x : Point) (hxE : x ∈ E) (hEC : E ⊆ Cᶜ) :
    ConnectedComponents (Cᶜ : Set Point) :=
  ConnectedComponents.mk (⟨x, hEC hxE⟩ : (Cᶜ : Set Point))

/-- A connected edge disjoint from the old carrier is localized in one old
complement component. -/
theorem edgeLocalized_of_isConnected_subset_compl
    {C E : Set Point} (hEconn : IsConnected E)
    {x : Point} (hxE : x ∈ E) (hEC : E ⊆ Cᶜ) :
    LocalInsertion.EdgeLocalized C E
      (connectedEdgeActiveComponent C E x hxE hEC) := by
  intro z hzE hzC
  have h :=
    ComponentLifting.connectedComponents_mk_eq_of_isConnected_subset
      (P := E) (S := Cᶜ) hEconn hEC hzE hxE
  simpa [connectedEdgeActiveComponent] using h

/-- A full lollipop carrier disjoint from the old carrier is localized in one
old complement component. -/
theorem carrier_edgeLocalized_of_subset_compl
    (C : Set Point) (L : Lollipop) {x : Point}
    (hx : x ∈ L.carrier) (hLC : L.carrier ⊆ Cᶜ) :
    LocalInsertion.EdgeLocalized C L.carrier
      (connectedEdgeActiveComponent C L.carrier x hx hLC) :=
  edgeLocalized_of_isConnected_subset_compl
    (Lollipop.isConnected_carrier L) hx hLC

/-- A finite stem subsegment disjoint from the old carrier is localized in one
old complement component. -/
theorem stemSegment_edgeLocalized_of_subset_compl
    (C : Set Point) (L : Lollipop) {a b : ℝ} (hab : a ≠ b)
    (hEC : PrimitiveArcs.stemSegment L a b ⊆ Cᶜ) :
    LocalInsertion.EdgeLocalized C (PrimitiveArcs.stemSegment L a b)
      (connectedEdgeActiveComponent C (PrimitiveArcs.stemSegment L a b)
        (L.stemMap a)
        (by
          exact left_mem_segment ℝ (L.stemMap a) (L.stemMap b))
        hEC) :=
  edgeLocalized_of_isConnected_subset_compl
    (PrimitiveArcs.stemSegment_isConnected L hab)
    (by exact left_mem_segment ℝ (L.stemMap a) (L.stemMap b))
    hEC

/-- A proper circle subarc disjoint from the old carrier is localized in one
old complement component. -/
theorem circleArc_edgeLocalized_of_subset_compl
    (C : Set Point) (L : Lollipop) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b < 1)
    (hEC : PrimitiveArcs.circleArc L a b ⊆ Cᶜ) :
    LocalInsertion.EdgeLocalized C (PrimitiveArcs.circleArc L a b)
      (connectedEdgeActiveComponent C (PrimitiveArcs.circleArc L a b)
        (CircleJordan.circleParam L a)
        (by
          exact ⟨a, ⟨le_rfl, le_of_lt hab⟩, rfl⟩)
        hEC) :=
  edgeLocalized_of_isConnected_subset_compl
    (PrimitiveArcs.circleArc_isConnected L ha hab hb)
    (by exact ⟨a, ⟨le_rfl, le_of_lt hab⟩, rfl⟩)
    hEC

/-- The old occupied carrier at an ordered insertion prefix is closed. -/
theorem isClosed_occupied_prefix
    {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n) :
    IsClosed
      (occupied (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk))) :=
  OccupiedTopology.isClosed_occupied
    (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk))

/-- A finite stem subsegment whose endpoints are on the outward stem is an
edge of the inserted lollipop carrier. -/
theorem stemSegment_subset_inserted_carrier
    (L : Lollipop) {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    PrimitiveArcs.stemSegment L a b ⊆ L.carrier :=
  PrimitiveArcs.stemSegment_subset_carrier L ha hb

/-- A proper circle subarc is an edge of the inserted lollipop carrier. -/
theorem circleArc_subset_inserted_carrier
    (L : Lollipop) (a b : ℝ) :
    PrimitiveArcs.circleArc L a b ⊆ L.carrier :=
  PrimitiveArcs.circleArc_subset_carrier L a b

/-- Connected-edge version of the bounded Jordan-crosscut constructor.

This is the local step used by a future carrier subdivision: after a
subdivision edge is known to be connected and to avoid the old carrier, the
only remaining geometric topology input is the same-side arc-lifting
statement for the Jordan crosscut. -/
def localizedEdgeStepOfConnectedJordanCrosscut
    {C E J : Set Point} (hEconn : IsConnected E)
    {p : Point} (hpE : p ∈ E) (hEC : E ⊆ Cᶜ)
    (hJK : J ⊆ LocalInsertion.carrierExtension C E)
    (hJ : IsSimpleClosedCurve J)
    (hlift : JordanClassifier.ActiveSideArcLifting
      (LocalInsertion.old_subset_carrierExtension C E) hJK hJ
      (connectedEdgeActiveComponent C E p hpE hEC)) :
    LocalFiltration.LocalizedEdgeStep C E :=
  LocalCrosscut.localizedEdgeStepOfJordanCrosscut hJK hJ
    (connectedEdgeActiveComponent C E p hpE hEC)
    (edgeLocalized_of_isConnected_subset_compl hEconn hpE hEC)
    hlift

/-- Connected-edge version of the exact Jordan-crosscut constructor. -/
def localizedExactEdgeStepOfConnectedJordanCrosscut
    {C E J : Set Point} (hCclosed : IsClosed C) (L : Lollipop)
    (hE : E ⊆ L.carrier) (hEconn : IsConnected E)
    {p : Point} (hpE : p ∈ E) (hEC : E ⊆ Cᶜ)
    (hJK : J ⊆ LocalInsertion.carrierExtension C E)
    (hJ : IsSimpleClosedCurve J)
    (hlift : JordanClassifier.ActiveSideArcLifting
      (LocalInsertion.old_subset_carrierExtension C E) hJK hJ
      (connectedEdgeActiveComponent C E p hpE hEC))
    (hside : JordanClassifier.ActiveSideSurjective
      (LocalInsertion.old_subset_carrierExtension C E) hJK hJ
      (connectedEdgeActiveComponent C E p hpE hEC)) :
    LocalFiltration.LocalizedExactEdgeStep L C E :=
  LocalCrosscut.localizedExactEdgeStepOfJordanCrosscut hCclosed L hE
    hJK hJ (connectedEdgeActiveComponent C E p hpE hEC)
    (edgeLocalized_of_isConnected_subset_compl hEconn hpE hEC)
    hlift hside

/-- Full-carrier version of the bounded Jordan-crosscut constructor. -/
def localizedEdgeStepOfCarrierJordanCrosscut
    (C : Set Point) (L : Lollipop) {J : Set Point}
    (hLC : L.carrier ⊆ Cᶜ)
    (hJK : J ⊆ LocalInsertion.carrierExtension C L.carrier)
    (hJ : IsSimpleClosedCurve J)
    (hlift : JordanClassifier.ActiveSideArcLifting
      (LocalInsertion.old_subset_carrierExtension C L.carrier) hJK hJ
      (connectedEdgeActiveComponent C L.carrier L.anchor
        (L.anchor_mem_carrier) hLC)) :
    LocalFiltration.LocalizedEdgeStep C L.carrier :=
  localizedEdgeStepOfConnectedJordanCrosscut
    (Lollipop.isConnected_carrier L) (L.anchor_mem_carrier) hLC
    hJK hJ hlift

/-- Full-carrier version of the exact Jordan-crosscut constructor. -/
def localizedExactEdgeStepOfCarrierJordanCrosscut
    (C : Set Point) (L : Lollipop) {J : Set Point}
    (hCclosed : IsClosed C) (hLC : L.carrier ⊆ Cᶜ)
    (hJK : J ⊆ LocalInsertion.carrierExtension C L.carrier)
    (hJ : IsSimpleClosedCurve J)
    (hlift : JordanClassifier.ActiveSideArcLifting
      (LocalInsertion.old_subset_carrierExtension C L.carrier) hJK hJ
      (connectedEdgeActiveComponent C L.carrier L.anchor
        (L.anchor_mem_carrier) hLC))
    (hside : JordanClassifier.ActiveSideSurjective
      (LocalInsertion.old_subset_carrierExtension C L.carrier) hJK hJ
      (connectedEdgeActiveComponent C L.carrier L.anchor
        (L.anchor_mem_carrier) hLC)) :
    LocalFiltration.LocalizedExactEdgeStep L C L.carrier :=
  localizedExactEdgeStepOfConnectedJordanCrosscut hCclosed L
    (subset_rfl : L.carrier ⊆ L.carrier)
    (Lollipop.isConnected_carrier L) (L.anchor_mem_carrier) hLC
    hJK hJ hlift hside

/-- Connected-edge version of the bounded two-arc crosscut constructor. -/
def localizedEdgeStepOfConnectedTwoArcCrosscut
    {C E A B : Set Point} {x z p : Point}
    (hEconn : IsConnected E) (hpE : p ∈ E) (hEC : E ⊆ Cᶜ)
    (hAext : A ⊆ LocalInsertion.carrierExtension C E)
    (hBext : B ⊆ LocalInsertion.carrierExtension C E)
    (hA : IsSimpleArcEnd A x z) (hB : IsSimpleArcEnd B x z)
    (hxz : x ≠ z) (hinter : A ∩ B ⊆ {x, z})
    (hlift : JordanClassifier.ActiveSideArcLifting
      (LocalInsertion.old_subset_carrierExtension C E)
      (union_subset hAext hBext)
      (ArcClosedCurve.isSimpleClosedCurve_union_of_two_arcs hA hB hxz
        hinter)
      (connectedEdgeActiveComponent C E p hpE hEC)) :
    LocalFiltration.LocalizedEdgeStep C E :=
  LocalCrosscut.localizedEdgeStepOfTwoArcCrosscut hAext hBext hA hB
    hxz hinter (connectedEdgeActiveComponent C E p hpE hEC)
    (edgeLocalized_of_isConnected_subset_compl hEconn hpE hEC)
    hlift

/-- Connected-edge version of the exact two-arc crosscut constructor. -/
def localizedExactEdgeStepOfConnectedTwoArcCrosscut
    {C E A B : Set Point} {x z p : Point}
    (hCclosed : IsClosed C) (L : Lollipop) (hE : E ⊆ L.carrier)
    (hEconn : IsConnected E) (hpE : p ∈ E) (hEC : E ⊆ Cᶜ)
    (hAext : A ⊆ LocalInsertion.carrierExtension C E)
    (hBext : B ⊆ LocalInsertion.carrierExtension C E)
    (hA : IsSimpleArcEnd A x z) (hB : IsSimpleArcEnd B x z)
    (hxz : x ≠ z) (hinter : A ∩ B ⊆ {x, z})
    (hlift : JordanClassifier.ActiveSideArcLifting
      (LocalInsertion.old_subset_carrierExtension C E)
      (union_subset hAext hBext)
      (ArcClosedCurve.isSimpleClosedCurve_union_of_two_arcs hA hB hxz
        hinter)
      (connectedEdgeActiveComponent C E p hpE hEC))
    (hside : JordanClassifier.ActiveSideSurjective
      (LocalInsertion.old_subset_carrierExtension C E)
      (union_subset hAext hBext)
      (ArcClosedCurve.isSimpleClosedCurve_union_of_two_arcs hA hB hxz
        hinter)
      (connectedEdgeActiveComponent C E p hpE hEC)) :
    LocalFiltration.LocalizedExactEdgeStep L C E :=
  LocalCrosscut.localizedExactEdgeStepOfTwoArcCrosscut hCclosed L hE
    hAext hBext hA hB hxz hinter
    (connectedEdgeActiveComponent C E p hpE hEC)
    (edgeLocalized_of_isConnected_subset_compl hEconn hpE hEC)
    hlift hside

/-- Bounded subdivision data for one positive ordered insertion.

Mathematically this should be built by cutting the inserted lollipop carrier
at its old-new fan and ordering the resulting localized edges. -/
structure PositiveInsertionSubdivision
    {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n) where
  edgeCount : ℕ
  filtration :
    InsertionFiltration.LocalizedInsertionFiltration
      (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk))
      (A ⟨k, hk⟩) edgeCount
  edgeCount_le_fan :
    (edgeCount : ℚ) ≤
      (componentCount (InsertionFan.insertionFan A k hk) : ℚ)

/-- Exact subdivision data for one positive generic ordered insertion. -/
structure ExactPositiveInsertionSubdivision
    {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n) where
  edgeCount : ℕ
  filtration :
    InsertionFiltration.LocalizedExactInsertionFiltration
      (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk))
      (A ⟨k, hk⟩) edgeCount
  edgeCount_eq_fan :
    edgeCount = componentCount (InsertionFan.insertionFan A k hk)

/-- One localized whole-carrier edge gives bounded subdivision data.

This is the base case for later subdivision proofs: after proving that the
entire inserted carrier is localized in one old component, the fan budget is
automatic because every insertion fan has at least one component. -/
noncomputable def positiveInsertionSubdivision_of_singleEdgeStep
    {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n)
    (step :
      LocalFiltration.LocalizedEdgeStep
        (occupied
          (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk)))
        (A ⟨k, hk⟩).carrier) :
    PositiveInsertionSubdivision A k hk where
  edgeCount := 1
  filtration := by
    let C :=
      occupied (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk))
    let L := A ⟨k, hk⟩
    let f : LocalFiltration.LocalizedEdgeFiltration 1 C
        (LocalInsertion.carrierExtension C L.carrier) :=
      LocalFiltration.LocalizedEdgeFiltration.snoc
        (LocalFiltration.LocalizedEdgeFiltration.nil C)
        L.carrier
        (by simpa [C, L] using step)
    simpa [InsertionFiltration.LocalizedInsertionFiltration, C, L,
      LocalInsertion.carrierExtension] using f
  edgeCount_le_fan := by
    simpa using one_le_componentCount_insertionFan_cast A k hk

/-- A whole inserted carrier disjoint from the old carrier gives a one-edge
bounded subdivision once the Jordan crosscut side-lifting input is supplied. -/
noncomputable def positiveInsertionSubdivision_of_disjoint_carrier_jordanCrosscut
    {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n) {J : Set Point}
    (hLC :
      (A ⟨k, hk⟩).carrier ⊆
        (occupied
          (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk)))ᶜ)
    (hJK : J ⊆
      LocalInsertion.carrierExtension
        (occupied
          (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk)))
        (A ⟨k, hk⟩).carrier)
    (hJ : IsSimpleClosedCurve J)
    (hlift : JordanClassifier.ActiveSideArcLifting
      (LocalInsertion.old_subset_carrierExtension
        (occupied
          (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk)))
        (A ⟨k, hk⟩).carrier)
      hJK hJ
      (connectedEdgeActiveComponent
        (occupied
          (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk)))
        (A ⟨k, hk⟩).carrier (A ⟨k, hk⟩).anchor
        ((A ⟨k, hk⟩).anchor_mem_carrier) hLC)) :
    PositiveInsertionSubdivision A k hk :=
  positiveInsertionSubdivision_of_singleEdgeStep A k hk
    (localizedEdgeStepOfCarrierJordanCrosscut
      (occupied
        (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk)))
      (A ⟨k, hk⟩) hLC hJK hJ hlift)

/-- One exact localized whole-carrier edge gives exact subdivision data when
the insertion fan has component count one. -/
noncomputable def exactPositiveInsertionSubdivision_of_singleExactEdgeStep
    {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n)
    (hfan : componentCount (InsertionFan.insertionFan A k hk) = 1)
    (step :
      LocalFiltration.LocalizedExactEdgeStep (A ⟨k, hk⟩)
        (occupied
          (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk)))
        (A ⟨k, hk⟩).carrier) :
    ExactPositiveInsertionSubdivision A k hk where
  edgeCount := 1
  filtration := by
    let C :=
      occupied (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk))
    let L := A ⟨k, hk⟩
    let f : LocalFiltration.LocalizedExactEdgeFiltration L 1 C
        (LocalInsertion.carrierExtension C L.carrier) :=
      LocalFiltration.LocalizedExactEdgeFiltration.snoc
        (LocalFiltration.LocalizedExactEdgeFiltration.nil (L := L) C)
        L.carrier
        (by simpa [C, L] using step)
    simpa [InsertionFiltration.LocalizedExactInsertionFiltration, C, L,
      LocalInsertion.carrierExtension] using f
  edgeCount_eq_fan := hfan.symm

/-- If the inserted carrier is already contained in the old carrier, no
localized edge insertion is needed for the bounded upper-bound direction. -/
noncomputable def positiveInsertionSubdivision_of_carrier_subset_old
    {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n)
    (hsubset :
      (A ⟨k, hk⟩).carrier ⊆
        occupied
          (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk))) :
    PositiveInsertionSubdivision A k hk where
  edgeCount := 0
  filtration := by
    let C :=
      occupied (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk))
    let L := A ⟨k, hk⟩
    have hfinal : C ∪ L.carrier = C :=
      Set.union_eq_left.mpr (by simpa [C, L] using hsubset)
    simpa [InsertionFiltration.LocalizedInsertionFiltration, C, L,
      hfinal] using LocalFiltration.LocalizedEdgeFiltration.nil C
  edgeCount_le_fan := by
    exact_mod_cast
      (Nat.zero_le (componentCount (InsertionFan.insertionFan A k hk)))

/-- A bounded subdivision gives the existential localized-filtration theorem
used by `LocalizedTopology`. -/
theorem localizedInsertionFiltration_bound_positive_of_subdivision
    {n : ℕ} {A : Arrangement n} {k : ℕ} {hk : k < n}
    (d : PositiveInsertionSubdivision A k hk) :
    ∃ m : ℕ,
    ∃ _f : InsertionFiltration.LocalizedInsertionFiltration
        (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk))
        (A ⟨k, hk⟩) m,
      (m : ℚ) ≤
        (componentCount (InsertionFan.insertionFan A k hk) : ℚ) :=
  ⟨d.edgeCount, d.filtration, d.edgeCount_le_fan⟩

/-- Remaining effective-carrier bounded subdivision theorem.

The full-overlap case is already handled by
`positiveInsertionSubdivision_of_carrier_subset_old`; this is the precise
planar-topology construction still needed for genuinely new carrier pieces. -/
theorem positiveInsertionSubdivision_exists_of_effective_carrier
    {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n) (_hkpos : 0 < k)
    (_heffective :
      ¬ (A ⟨k, hk⟩).carrier ⊆
        occupied
          (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk))) :
    Nonempty (PositiveInsertionSubdivision A k hk) := by
  sorry

/-- An exact subdivision gives the existential exact localized-filtration
theorem used by `LocalizedTopology`. -/
theorem localizedExactInsertionFiltration_of_exactPositiveSubdivision
    {n : ℕ} {A : Arrangement n} {k : ℕ} {hk : k < n}
    (d : ExactPositiveInsertionSubdivision A k hk) :
    ∃ m : ℕ,
    ∃ _f : InsertionFiltration.LocalizedExactInsertionFiltration
        (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk))
        (A ⟨k, hk⟩) m,
      m = componentCount (InsertionFan.insertionFan A k hk) :=
  ⟨d.edgeCount, d.filtration, d.edgeCount_eq_fan⟩

/-- Remaining bounded positive-insertion subdivision theorem.

This is the concrete planar-topology construction still required for the
upper bound: for every non-first insertion, subdivide the inserted lollipop
into localized edge additions using at most the old-new fan component count. -/
theorem positiveInsertionSubdivision_exists
    {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k < n) (_hkpos : 0 < k) :
    Nonempty (PositiveInsertionSubdivision A k hk) := by
  by_cases hsubset :
      (A ⟨k, hk⟩).carrier ⊆
        occupied
          (PlanarInsertion.prefixArrangement A k (Nat.le_of_lt hk))
  · exact ⟨positiveInsertionSubdivision_of_carrier_subset_old
      A k hk hsubset⟩
  · exact positiveInsertionSubdivision_exists_of_effective_carrier
      A k hk _hkpos hsubset

/-- Remaining exact positive-insertion subdivision theorem in generic
position.

This is the concrete planar-topology construction still required for the
generic Euler equality: the same subdivision is exact and has length exactly
the old-new fan component count. -/
theorem exactPositiveInsertionSubdivision_exists
    {n : ℕ} {A : Arrangement n} (_hA : IsGeneric A)
    (k : ℕ) (hk : k < n) (_hkpos : 0 < k) :
    Nonempty (ExactPositiveInsertionSubdivision A k hk) := by
  sorry

end MainTheorem
end EndToEnd
end Concrete
end Lollipop
