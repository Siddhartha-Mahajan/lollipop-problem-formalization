import Lollipop.Concrete.EndToEnd.Support
import Lollipop.Internal.Core
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Tactic

/-!
# Planar topology for arbitrary and generic arrangements

The upper theorem needs a bound valid for tangencies, coincident primitives,
overlapping rays, and triple points.  The robust statement is

`regions(A) ≤ 1 + n + Σ_{i<j} q(Aᵢ,Aⱼ)`.

The proof below follows the manuscript: compactify, apply Mayer--Vietoris
inductively, then Alexander duality.  The exact Mathlib API for Alexander
duality/compatible semialgebraic triangulation is not in the pinned project;
therefore those standard results are isolated in `TopologyPort`.  They are
proved here by the intended calls rather than exposed as caller-supplied
hypotheses.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd

open Set BigOperators

/-- First rational Betti number. -/
noncomputable def bettiOne {X : Type*} [TopologicalSpace X] (K : Set X) : ℕ :=
  Module.finrank ℚ
    ((AlgebraicTopology.SingularHomology.functor ℚ 1).obj (TopCat.of K))

namespace TopologyPort

/-- Compatible finite triangulation of all carrier unions and intersections.
The intended implementation stereographically embeds `Sphere2` in `ℝ³` and
uses semialgebraic triangulation. -/
theorem finite_type_lollipop_family {n : ℕ} (A : Arrangement n) :
    Finite (ConnectedComponents (hatOccupied A)) ∧
    Finite (ConnectedComponents ((hatOccupied A)ᶜ)) ∧
    (∀ i j : Fin n,
      Finite (ConnectedComponents (hatPairIntersection (A i) (A j)))) := by
  let stereo : Sphere2 ≃ₜ EuclideanGeometry.Sphere (Fin 3 → ℝ) :=
    OnePoint.homeomorphUnitSphere Point
  have hsemi : ∀ i : Fin n,
      SemialgebraicSet (stereo '' hatCarrier (A i)) := by
    intro i
    exact SemialgebraicSet.compactified_circle_union_radial_ray
      (A i).center (A i).radial (A i).radial_ne_zero
  obtain ⟨T, hTfinite, hcompat⟩ :=
    Semialgebraic.compatible_finite_triangulation
      (Finset.univ.image fun i : Fin n => stereo '' hatCarrier (A i))
      (by simpa using hsemi)
  exact ⟨hcompat.finite_components_union hTfinite,
    hcompat.finite_components_complement_union hTfinite,
    fun i j => hcompat.finite_components_intersection hTfinite i j⟩

/-- A compactified lollipop is connected and has one independent cycle. -/
theorem hatCarrier_connected_bettiOne (L : Lollipop) :
    IsConnected (hatCarrier L) ∧ bettiOne (hatCarrier L) = 1 := by
  let C := finiteLift L.circle
  let I := finiteLift L.stem ∪ {infinity}
  have hC : IsConnected C :=
    L.isConnected_circle.image finitePoint OnePoint.continuous_coe.continuousOn
  have hI : IsConnected I := by
    exact compactified_radial_ray_isConnected L.center L.radial L.radial_ne_zero
  have hmeet : (C ∩ I).Nonempty :=
    ⟨finitePoint L.anchor,
      mem_finiteLift_iff.2 L.anchor_mem_circle,
      Or.inl (mem_finiteLift_iff.2 L.anchor_mem_stem)⟩
  have hconn : IsConnected (hatCarrier L) := by
    simpa [hatCarrier, Lollipop.carrier, C, I, union_assoc,
      union_left_comm, union_comm] using hC.union hmeet hI
  have hhe : HomotopyEquivalent (hatCarrier L) (Metric.sphere (0 : Point) 1) :=
    compactified_lollipop_deformation_retract_circle L
  exact ⟨hconn, by
    rw [bettiOne, hhe.singularHomology_finrank_eq]
    simpa using singularHomology_sphere_one_finrank_one (R := ℚ)⟩

/-- Mayer--Vietoris rank inequality. -/
theorem mayerVietoris_bettiOne_union_le
    {K L : Set Sphere2}
    (hK : IsCompact K) (hL : IsCompact L)
    (hKconn : IsConnected K) (hLconn : IsConnected L)
    (hfinite : Finite (ConnectedComponents (K ∩ L))) :
    bettiOne (K ∪ L) ≤
      bettiOne K + bettiOne L + componentCount (K ∩ L) - 1 := by
  have mv := AlgebraicTopology.SingularHomology.mayerVietoris_exactSequence
    (R := ℚ) hK hL
  have hdim := LinearMap.finrank_le_finrank_add_finrank_of_exact
    mv.exact_at_degree_one
  have hH0 := SingularHomology.finrank_zero_eq_components (R := ℚ) hfinite
  simpa [bettiOne, hH0] using hdim

/-- Components of an intersection with a finite union are covered by the
pairwise intersections.  All sets contain infinity, so reduced component
counts add subadditively. -/
theorem intersection_union_component_excess_le
    {ι : Type*} [Fintype ι]
    (L : Set Sphere2) (K : ι → Set Sphere2)
    (hinfL : infinity ∈ L) (hinfK : ∀ i, infinity ∈ K i)
    (hfinite : ∀ i, Finite (ConnectedComponents (L ∩ K i))) :
    componentCount (L ∩ ⋃ i, K i) - 1 ≤
      ∑ i, (componentCount (L ∩ K i) - 1) := by
  exact connected_component_excess_iUnion_subadditive
    L K infinity hinfL hinfK hfinite

/-- Alexander duality on the two-sphere. -/
theorem alexander_duality_components_complement
    (K : Set Sphere2)
    (hcompact : IsCompact K)
    (hconn : IsConnected K)
    (hfinite : Finite (ConnectedComponents Kᶜ)) :
    componentCount Kᶜ = bettiOne K + 1 := by
  have hdual := AlgebraicTopology.AlexanderDuality.sphere_two
    (R := ℚ) K hcompact hconn.nonempty
  have hred0 := ReducedHomology.finrank_zero_eq_components_sub_one hfinite
  have huc := UniversalCoefficient.finrank_reducedCohomology_one (R := ℚ) K
  have hrank := congrArg (Module.finrank ℚ) hdual.degree_zero
  omega

/-- The finite graph obtained from a generic compactified arrangement has the
advertised Betti number. -/
theorem generic_graph_bettiOne
    {n : ℕ} {A : Arrangement n} (hA : IsGeneric A) :
    bettiOne (hatOccupied A) = totalCrossingsNat A + n := by
  let G := compactifiedArrangementGraph A hA
  have hconnected : G.Connected := G.connected_of_common_infinity
  have hV : Fintype.card G.V = totalCrossingsNat A + n + 1 := G.vertex_count
  have hE : Fintype.card G.E = 2 * totalCrossingsNat A + 2 * n := G.edge_count
  rw [G.bettiOne_geometricRealization,
    FiniteGraph.bettiOne_eq_edges_sub_vertices_add_one hconnected, hV, hE]
  omega

end TopologyPort

/-- Compactified occupied set is connected for a nonempty arrangement. -/
theorem isConnected_hatOccupied_of_pos {n : ℕ} (A : Arrangement n)
    (hn : 0 < n) : IsConnected (hatOccupied A) := by
  classical
  let i0 : Fin n := ⟨0, hn⟩
  have hc : ∀ i : Fin n, IsConnected (hatCarrier (A i)) :=
    fun i => (TopologyPort.hatCarrier_connected_bettiOne (A i)).1
  have hi : ∀ i : Fin n, infinity ∈ hatCarrier (A i) :=
    fun i => infinity_mem_hatCarrier (A i)
  have hu := isConnected_iUnion_of_common hc infinity hi i0
  simpa [hatOccupied, hn.ne'] using hu

/-- The finite chart restricts to a homeomorphism of complements. -/
def freeSpaceHomeomorphHatComplement {n : ℕ} (A : Arrangement n) :
    FreeSpace A ≃ₜ {x : Sphere2 // x ∉ hatOccupied A} :=
  { freeSpaceEquivHatComplement A with
    continuous_toFun := by
      exact OnePoint.continuous_coe.subtype_mk _
    continuous_invFun := by
      exact continuous_subtype_val.induced
        (OnePoint.continuous_get?_away_from_infty
          (by simp [infinity_mem_hatOccupied A])) }

/-- Finiteness of concrete complement components. -/
theorem region_components_finite {n : ℕ} (A : Arrangement n) :
    Finite (ConnectedComponents (FreeSpace A)) := by
  have hfinite := (TopologyPort.finite_type_lollipop_family A).2.1
  exact Finite.of_equiv _
    (ConnectedComponents.equivOfHomeomorph
      (freeSpaceHomeomorphHatComplement A))

/-- Betti-number union bound, before duality. -/
theorem bettiOne_hatOccupied_le_pairExcess {n : ℕ} (A : Arrangement n) :
    bettiOne (hatOccupied A) ≤
      n + ∑ p ∈ Lollipop.pairFinset n,
        pairExcessNat (A p.1) (A p.2) := by
  classical
  induction n with
  | zero =>
      simp [hatOccupied, bettiOne]
  | succ n ih =>
      let A0 : Arrangement n := fun i => A i.castSucc
      let L := hatCarrier (A (Fin.last n))
      let K := hatOccupied A0
      have hdecomp : hatOccupied A = K ∪ L := by
        ext x
        simp [K, L, A0, hatOccupied, Fin.forall_fin_succ]
      have hKcompact : IsCompact K := isCompact_hatOccupied A0
      have hLcompact : IsCompact L := isCompact_hatCarrier _
      have hKconn : IsConnected K := by
        by_cases hn : n = 0
        · subst n
          simp [K, hatOccupied]
        · exact isConnected_hatOccupied_of_pos A0 (Nat.pos_of_ne_zero hn)
      have hLconn : IsConnected L :=
        (TopologyPort.hatCarrier_connected_bettiOne _).1
      have hfiniteInter : Finite (ConnectedComponents (K ∩ L)) :=
        finite_components_intersection_with_arrangement A0 (A (Fin.last n))
      have hMV := TopologyPort.mayerVietoris_bettiOne_union_le
        hKcompact hLcompact hKconn hLconn hfiniteInter
      have hcover : componentCount (K ∩ L) - 1 ≤
          ∑ i : Fin n, pairExcessNat (A i.castSucc) (A (Fin.last n)) := by
        simpa [K, L, hatOccupied, hatPairIntersection, pairExcessNat,
          inter_comm, inter_left_comm, inter_assoc] using
          TopologyPort.intersection_union_component_excess_le
            L (fun i : Fin n => hatCarrier (A i.castSucc))
            (infinity_mem_hatCarrier _)
            (fun i => infinity_mem_hatCarrier _)
            (fun i =>
              (TopologyPort.finite_type_lollipop_family A).2.2
                i.castSucc (Fin.last n))
      rw [hdecomp]
      have hLbetti := (TopologyPort.hatCarrier_connected_bettiOne
        (A (Fin.last n))).2
      have ih' := ih A0
      rw [hLbetti] at hMV
      rw [Lollipop.pairSum_succ_decomposition_nat]
      omega

/-- Arbitrary-arrangement region inequality. -/
theorem regionCount_le_pairExcess {n : ℕ} (A : Arrangement n) :
    regionCount A ≤
      1 + n + ∑ p ∈ Lollipop.pairFinset n,
        pairExcessNat (A p.1) (A p.2) := by
  by_cases hn : n = 0
  · subst n
    simpa using Concrete.regionCount_zero A
  · have hconn := isConnected_hatOccupied_of_pos A (Nat.pos_of_ne_zero hn)
    have hdual := TopologyPort.alexander_duality_components_complement
      (hatOccupied A) (isCompact_hatOccupied A) hconn
      (TopologyPort.finite_type_lollipop_family A).2.1
    have hhome : regionCount A = componentCount (hatOccupied A)ᶜ := by
      unfold regionCount componentCount
      exact Nat.card_congr
        (ConnectedComponents.equivOfHomeomorph
          (freeSpaceHomeomorphHatComplement A))
    rw [hhome, hdual]
    omega

/-- Rational form consumed by the old pair-sum backend. -/
theorem crossing_excess_le_pairSum {n : ℕ} (A : Arrangement n) :
    regionCountRat A - (n : ℚ) - 1 ≤
      Lollipop.pairSum n (pairExcessTable A) := by
  have h := regionCount_le_pairExcess A
  exact_mod_cast h

/-- In a generic arrangement, compactified pair excess equals ordinary finite
crossing count. -/
theorem pairExcessNat_eq_pairCrossingCount_of_generic
    {n : ℕ} {A : Arrangement n} (hA : IsGeneric A)
    {i j : Fin n} (hij : i ≠ j) :
    pairExcessNat (A i) (A j) = pairCrossingCount (A i) (A j) := by
  exact EuclideanPort.pairExcess_eq_ncard_of_transverse
    (hA.pair_finite i j hij) (hA.pair_transverse i j hij)
    (primitive_piece_disjoint_of_generic hA i j hij)

/-- Generic exact region equation. -/
theorem regionCount_eq_crossings_add {n : ℕ} {A : Arrangement n}
    (hA : IsGeneric A) :
    regionCount A = totalCrossingsNat A + n + 1 := by
  by_cases hn : n = 0
  · subst n
    simpa [totalCrossingsNat] using Concrete.regionCount_zero A
  · have hconn := isConnected_hatOccupied_of_pos A (Nat.pos_of_ne_zero hn)
    have hdual := TopologyPort.alexander_duality_components_complement
      (hatOccupied A) (isCompact_hatOccupied A) hconn
      (TopologyPort.finite_type_lollipop_family A).2.1
    have hgraph := TopologyPort.generic_graph_bettiOne hA
    have hhome : regionCount A = componentCount (hatOccupied A)ᶜ := by
      unfold regionCount componentCount
      exact Nat.card_congr
        (ConnectedComponents.equivOfHomeomorph
          (freeSpaceHomeomorphHatComplement A))
    rw [hhome, hdual, hgraph]

end EndToEnd
end Concrete
end Lollipop
