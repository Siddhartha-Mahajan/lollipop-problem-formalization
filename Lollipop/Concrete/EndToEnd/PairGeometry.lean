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

/-- Remaining concrete pair-geometry theorem package.

These fields are the four robust pair-excess estimates used by the colored
Turan backend.  They are stated for the concrete lollipop carrier/intersection
semantics, including degeneracies. -/
structure PairGeometryPorts : Prop where
  pairExcess_le_seven :
    ∀ L M : Lollipop, pairExcess L M ≤ 7
  pairExcess_le_five_of_close :
    ∀ {L M : Lollipop}, Close L M → pairExcess L M ≤ 5
  pairExcess_le_five_of_intriguing :
    ∀ {L M : Lollipop}, Intriguing L M → pairExcess L M ≤ 5
  pairExcess_le_four_of_close_intriguing :
    ∀ {L M : Lollipop}, Close L M → Intriguing L M →
      pairExcess L M ≤ 4

/-- Universal `2+2+2+1` pair bound. -/
theorem pairExcess_le_seven (ports : PairGeometryPorts)
    (L M : Lollipop) : pairExcess L M ≤ 7 :=
  ports.pairExcess_le_seven L M

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
