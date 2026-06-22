import Lollipop.Concrete.EndToEnd.PlanarTopology
import Lollipop.Internal.ColoredTuran.PaulsenLinearAlgebra
import Mathlib.Tactic

/-!
# Concrete pair geometry

This file proves the four robust pair-excess bounds used by the colored Turán
backend.  The proofs count connected components, not intersection
multiplicity, so every statement remains valid for tangencies, coincident
circles, and overlapping stems.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace PairGeometry

open Set

/-- Compactify one primitive intersection together with infinity. -/
def hatPiece (S : Set Point) : Set Sphere2 := finiteLift S ∪ {infinity}

def pieceExcess (S : Set Point) : ℕ := componentCount (hatPiece S) - 1

/-- The four primitive pieces of a pair intersection. -/
def pairPiece (L M : Lollipop) (k : Fin 4) : Set Sphere2 :=
  match k.1 with
  | 0 => hatPiece (cc L M)
  | 1 => hatPiece (rc L M)
  | 2 => hatPiece (cr L M)
  | _ => hatPiece (rr L M)

@[simp] theorem infinity_mem_hatPiece (S : Set Point) :
    infinity ∈ hatPiece S := by
  simp [hatPiece]

/-- The compactified pair intersection is the union of the four compactified
primitive intersections. -/
theorem hatPairIntersection_decompose (L M : Lollipop) :
    hatPairIntersection L M =
      hatPiece (cc L M) ∪ hatPiece (rc L M) ∪
        hatPiece (cr L M) ∪ hatPiece (rr L M) := by
  ext x
  cases x using OnePoint.rec with
  | infty =>
      change infinity ∈ hatPairIntersection L M ↔
        infinity ∈
          hatPiece (cc L M) ∪ hatPiece (rc L M) ∪
            hatPiece (cr L M) ∪ hatPiece (rr L M)
      constructor
      · intro _h
        simp [hatPiece]
      · intro _h
        exact infinity_mem_hatPairIntersection L M
  | coe p =>
      change finitePoint p ∈ hatPairIntersection L M ↔
        finitePoint p ∈
          hatPiece (cc L M) ∪ hatPiece (rc L M) ∪
            hatPiece (cr L M) ∪ hatPiece (rr L M)
      simp [hatPairIntersection, hatPiece, cc, rc, cr, rr, Lollipop.carrier]
      tauto

theorem hatPairIntersection_eq_iUnion_pairPiece (L M : Lollipop) :
    hatPairIntersection L M = ⋃ k : Fin 4, pairPiece L M k := by
  rw [hatPairIntersection_decompose]
  ext x
  constructor
  · intro hx
    rcases hx with ((hcc | hrc) | hcr) | hrr
    · exact Set.mem_iUnion.mpr ⟨0, by simpa [pairPiece] using hcc⟩
    · exact Set.mem_iUnion.mpr ⟨1, by simpa [pairPiece] using hrc⟩
    · exact Set.mem_iUnion.mpr ⟨2, by simpa [pairPiece] using hcr⟩
    · exact Set.mem_iUnion.mpr ⟨3, by simpa [pairPiece] using hrr⟩
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨k, hk⟩
    fin_cases k <;> simp [pairPiece] at hk ⊢ <;> tauto

/-- Close means the smaller angle between actual stem directions is at most a
right angle. -/
def Close (L M : Lollipop) : Prop :=
  0 ≤ TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2
    (R2.ofPoint L.unitRadial) (R2.ofPoint M.unitRadial)

/-- The manuscript's intriguing-circle relation.  A pair is intriguing when
the two circle curves are disjoint, or when their squared center distance is at
most the sum of the squared radii.  In particular, an **external tangency is
not** intriguing: the circles meet, while the second inequality is false.

This boundary convention is essential.  The canonical Paulsen relation in the
older backend is the complement of an *open* obtuse interval and therefore
classifies an external tangency as intriguing.  That broader relation does not
satisfy the required five-component pair bound.  `Upper.lean` instead applies
the Paulsen obstruction after one uniform infinitesimal enlargement of all
radii, exactly as in the manuscript. -/
def Intriguing (L M : Lollipop) : Prop :=
  ¬ (cc L M).Nonempty ∨
    TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
      (R2.ofPoint L.center) (R2.ofPoint M.center) ≤
        L.radius ^ 2 + M.radius ^ 2

@[simp] theorem close_symm (L M : Lollipop) : Close L M ↔ Close M L := by
  unfold Close TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2
  constructor <;> intro h <;> nlinarith

@[simp] theorem intriguing_symm (L M : Lollipop) :
    Intriguing L M ↔ Intriguing M L := by
  unfold Intriguing
  rw [TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2_symm]
  have hcc : (cc M L).Nonempty ↔ (cc L M).Nonempty := by
    simp [cc, inter_comm]
  rw [hcc]
  constructor <;> rintro (hdisj | hnear)
  · exact Or.inl hdisj
  · exact Or.inr (by nlinarith)
  · exact Or.inl hdisj
  · exact Or.inr (by nlinarith)

private theorem finite_components_hatPiece_cc (L M : Lollipop) :
    Finite (ConnectedComponents (hatPiece (cc L M))) := by
  unfold hatPiece
  by_cases hsame : L.circle = M.circle
  · have hconn : IsConnected (finiteLift (cc L M)) := by
      simpa [cc, hsame, finiteLift] using
        L.isConnected_circle.image finitePoint OnePoint.continuous_coe.continuousOn
    exact finite_connectedComponents_union_singleton_of_connected hconn
  · exact finite_connectedComponents_finiteLift_union_infinity
      (finite_circle_intersection_of_ne hsame)

private theorem finite_components_hatPiece_rc (L M : Lollipop) :
    Finite (ConnectedComponents (hatPiece (rc L M))) := by
  unfold hatPiece
  exact finite_connectedComponents_finiteLift_union_infinity
    (finite_ray_circle_intersection L M)

private theorem finite_components_hatPiece_cr (L M : Lollipop) :
    Finite (ConnectedComponents (hatPiece (cr L M))) := by
  unfold hatPiece
  exact finite_connectedComponents_finiteLift_union_infinity
    (finite_circle_ray_intersection L M)

private theorem finite_components_hatPiece_rr (L M : Lollipop) :
    Finite (ConnectedComponents (hatPiece (rr L M))) := by
  unfold hatPiece
  have hconv : Convex ℝ (rr L M) := (stem_convex L).inter (stem_convex M)
  by_cases hne : (rr L M).Nonempty
  · have hconn : IsConnected (finiteLift (rr L M)) :=
      (hconv.isConnected hne).image finitePoint
        OnePoint.continuous_coe.continuousOn
    exact finite_connectedComponents_union_singleton_of_connected hconn
  · have hempty : rr L M = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [hempty]
    exact finite_connectedComponents_finiteLift_union_infinity finite_empty

private theorem finite_components_pairPiece (L M : Lollipop) (k : Fin 4) :
    Finite (ConnectedComponents (pairPiece L M k)) := by
  fin_cases k
  · change Finite (ConnectedComponents (hatPiece (cc L M)))
    exact finite_components_hatPiece_cc L M
  · change Finite (ConnectedComponents (hatPiece (rc L M)))
    exact finite_components_hatPiece_rc L M
  · change Finite (ConnectedComponents (hatPiece (cr L M)))
    exact finite_components_hatPiece_cr L M
  · change Finite (ConnectedComponents (hatPiece (rr L M)))
    exact finite_components_hatPiece_rr L M

/-- Universal `2+2+2+1` pair bound at the natural-number level. -/
theorem pairExcessNat_le_seven (L M : Lollipop) :
    pairExcessNat L M ≤ 7 := by
  let S : Fin 4 → Set Sphere2 := pairPiece L M
  haveI (k : Fin 4) : Finite (ConnectedComponents (S k)) :=
    finite_components_pairPiece L M k
  have hcommon : ∀ k : Fin 4, infinity ∈ S k := by
    intro k
    fin_cases k <;> simp [S, pairPiece]
  have hunion :
      componentCount (⋃ k : Fin 4, S k) - 1 ≤
        ∑ k : Fin 4, (componentCount (S k) - 1) :=
    componentCount_iUnion_sub_one_le_sum_sub_one infinity hcommon
  have hcc := EuclideanPort.circle_circle_components_le_two L M
  have hrc := EuclideanPort.ray_circle_components_le_two L M
  have hcr := EuclideanPort.circle_ray_components_le_two L M
  have hrr := EuclideanPort.ray_ray_components_le_one L M
  have hccHat : componentCount (hatPiece (cc L M)) - 1 ≤ 2 := by
    simpa [hatPiece] using hcc
  have hrcHat : componentCount (hatPiece (rc L M)) - 1 ≤ 2 := by
    simpa [hatPiece] using hrc
  have hcrHat : componentCount (hatPiece (cr L M)) - 1 ≤ 2 := by
    simpa [hatPiece] using hcr
  have hrrHat : componentCount (hatPiece (rr L M)) - 1 ≤ 1 := by
    simpa [hatPiece] using hrr
  unfold pairExcessNat
  rw [hatPairIntersection_eq_iUnion_pairPiece]
  refine hunion.trans ?_
  rw [Fin.sum_univ_four]
  change
    (componentCount (hatPiece (cc L M)) - 1) +
      (componentCount (hatPiece (rc L M)) - 1) +
      (componentCount (hatPiece (cr L M)) - 1) +
      (componentCount (hatPiece (rr L M)) - 1) ≤ 7
  omega

/-- Remaining concrete pair-geometry theorem package.

These fields are the remaining robust pair-excess savings used by the colored
Turan backend.  They are stated for the concrete lollipop carrier/intersection
semantics, including degeneracies. -/
structure PairGeometryPorts : Prop where
  pairExcess_le_five_of_close :
    ∀ {L M : Lollipop}, Close L M → pairExcess L M ≤ 5
  pairExcess_le_five_of_intriguing :
    ∀ {L M : Lollipop}, Intriguing L M → pairExcess L M ≤ 5
  pairExcess_le_four_of_close_intriguing :
    ∀ {L M : Lollipop}, Close L M → Intriguing L M →
      pairExcess L M ≤ 4

/-- Universal `2+2+2+1` pair bound. -/
theorem pairExcess_le_seven (L M : Lollipop) : pairExcess L M ≤ 7 := by
  unfold pairExcess
  exact_mod_cast pairExcessNat_le_seven L M

/-- Close-pair saving. -/
theorem pairExcess_le_five_of_close (ports : PairGeometryPorts)
    {L M : Lollipop} (hclose : Close L M) : pairExcess L M ≤ 5 :=
  ports.pairExcess_le_five_of_close hclose

/-- Intriguing-pair saving. -/
theorem pairExcess_le_five_of_intriguing (ports : PairGeometryPorts)
    {L M : Lollipop} (hintr : Intriguing L M) : pairExcess L M ≤ 5 :=
  ports.pairExcess_le_five_of_intriguing hintr

/-- Combined close/intriguing saving. -/
theorem pairExcess_le_four_of_close_intriguing (ports : PairGeometryPorts)
    {L M : Lollipop} (hclose : Close L M) (hintr : Intriguing L M) :
    pairExcess L M ≤ 4 :=
  ports.pairExcess_le_four_of_close_intriguing hclose hintr

end PairGeometry
end EndToEnd
end Concrete
end Lollipop
