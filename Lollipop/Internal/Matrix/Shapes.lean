import Lollipop.Internal.Matrix.Relabel
import Lollipop.Internal.Matrix.Support

/-!
Finite support-shape classification for star forests in `K_{3,4}`.

The support graph has only twelve possible edges.  Up to independent row and
column permutations, its star-forest supports fall into sixteen canonical
masks.  This file records that finite classification as a checked theorem.
-/

namespace Lollipop

/-- Relabel a support by row and column permutations. -/
def supportRelabel
    (er : Fin 3 ≃ Fin 3) (ec : Fin 4 ≃ Fin 4)
    (S : Finset MatrixEdge) : Finset MatrixEdge :=
  Finset.univ.filter fun e : MatrixEdge => (er.symm e.1, ec.symm e.2) ∈ S

/-- Relabeling a support and then relabeling back gives the original support. -/
theorem supportRelabel_symm_relabel
    (er : Fin 3 ≃ Fin 3) (ec : Fin 4 ≃ Fin 4)
    (S : Finset MatrixEdge) :
    supportRelabel er.symm ec.symm (supportRelabel er ec S) = S := by
  ext e
  simp [supportRelabel]

/-- The support of a relabeled natural matrix is the corresponding inverse
relabeling of its support. -/
theorem supportOfNat_relabelNatMatrix
    (er : Fin 3 ≃ Fin 3) (ec : Fin 4 ≃ Fin 4)
    (U : NatMatrix) :
    supportOfNat (relabelNatMatrix er ec U) =
      supportRelabel er.symm ec.symm (supportOfNat U) := by
  ext e
  simp [supportOfNat, supportRelabel, relabelNatMatrix]

/-- If the support of `U` is a relabeled canonical support, then relabeling
`U` puts the support into canonical coordinates. -/
theorem supportOfNat_relabelNatMatrix_eq_of_supportRelabel
    (er : Fin 3 ≃ Fin 3) (ec : Fin 4 ≃ Fin 4)
    (U : NatMatrix) (T : Finset MatrixEdge)
    (hU : supportOfNat U = supportRelabel er ec T) :
    supportOfNat (relabelNatMatrix er ec U) = T := by
  rw [supportOfNat_relabelNatMatrix, hU, supportRelabel_symm_relabel]

/-- The canonical empty support. -/
def shape0 : Finset MatrixEdge :=
  ∅

/-- Canonical one-edge support. -/
def shape1 : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4))}

/-- Canonical row-centered two-edge star. -/
def shape2_row : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4)), ((0 : Fin 3), (1 : Fin 4))}

/-- Canonical column-centered two-edge star. -/
def shape2_col : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4)), ((1 : Fin 3), (0 : Fin 4))}

/-- Canonical two disjoint singleton components. -/
def shape2_singletons : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4)), ((1 : Fin 3), (1 : Fin 4))}

/-- Canonical row-centered three-edge star. -/
def shape3_row : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4)), ((0 : Fin 3), (1 : Fin 4)),
    ((0 : Fin 3), (2 : Fin 4))}

/-- Canonical row-centered two-edge star plus a singleton. -/
def shape3_row_plus_singleton : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4)), ((0 : Fin 3), (1 : Fin 4)),
    ((1 : Fin 3), (2 : Fin 4))}

/-- Canonical column-centered three-edge star. -/
def shape3_col : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4)), ((1 : Fin 3), (0 : Fin 4)),
    ((2 : Fin 3), (0 : Fin 4))}

/-- Canonical column-centered two-edge star plus a singleton. -/
def shape3_col_plus_singleton : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4)), ((1 : Fin 3), (0 : Fin 4)),
    ((2 : Fin 3), (1 : Fin 4))}

/-- Canonical three singleton components. -/
def shape3_singletons : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4)), ((1 : Fin 3), (1 : Fin 4)),
    ((2 : Fin 3), (2 : Fin 4))}

/-- Canonical row-centered four-edge star. -/
def shape4_row : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4)), ((0 : Fin 3), (1 : Fin 4)),
    ((0 : Fin 3), (2 : Fin 4)), ((0 : Fin 3), (3 : Fin 4))}

/-- Canonical row-centered three-edge star plus a singleton. -/
def shape4_row3_plus_singleton : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4)), ((0 : Fin 3), (1 : Fin 4)),
    ((0 : Fin 3), (2 : Fin 4)), ((1 : Fin 3), (3 : Fin 4))}

/-- Canonical two disjoint row-centered two-edge stars. -/
def shape4_two_row2 : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4)), ((0 : Fin 3), (1 : Fin 4)),
    ((1 : Fin 3), (2 : Fin 4)), ((1 : Fin 3), (3 : Fin 4))}

/-- Canonical row-centered two-edge star and column-centered two-edge star. -/
def shape4_row2_col2 : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4)), ((0 : Fin 3), (1 : Fin 4)),
    ((1 : Fin 3), (2 : Fin 4)), ((2 : Fin 3), (2 : Fin 4))}

/-- Canonical exceptional `(2,1,1)` support. -/
def shape4_exceptional : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4)), ((0 : Fin 3), (1 : Fin 4)),
    ((1 : Fin 3), (2 : Fin 4)), ((2 : Fin 3), (3 : Fin 4))}

/-- Canonical five-edge `(3,2)` star forest. -/
def shape5_row3_col2 : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4)), ((0 : Fin 3), (1 : Fin 4)),
    ((0 : Fin 3), (2 : Fin 4)), ((1 : Fin 3), (3 : Fin 4)),
    ((2 : Fin 3), (3 : Fin 4))}

/-- Canonical support masks for star forests in `K_{3,4}`. -/
def canonicalStarForestSupports : Finset (Finset MatrixEdge) :=
  {shape0, shape1, shape2_row, shape2_col, shape2_singletons,
    shape3_row, shape3_row_plus_singleton, shape3_col,
    shape3_col_plus_singleton, shape3_singletons, shape4_row,
    shape4_row3_plus_singleton, shape4_two_row2, shape4_row2_col2,
    shape4_exceptional, shape5_row3_col2}

/-- A support is row/column relabel-equivalent to one of the canonical
star-forest masks. -/
def relabeledStarForestSupportsOf
    (T : Finset MatrixEdge) : Finset (Finset MatrixEdge) :=
  (Finset.univ : Finset (Fin 3 ≃ Fin 3)).biUnion fun er =>
    (Finset.univ : Finset (Fin 4 ≃ Fin 4)).image fun ec =>
      supportRelabel er ec T

/-- All supports obtained by row/column relabeling the canonical masks. -/
def allCanonicalStarForestShapes : Finset (Finset MatrixEdge) :=
  canonicalStarForestSupports.biUnion relabeledStarForestSupportsOf

/-- A support is row/column relabel-equivalent to one of the canonical
star-forest masks. -/
def IsCanonicalStarForestShape (S : Finset MatrixEdge) : Prop :=
  S ∈ allCanonicalStarForestShapes

instance (S : Finset MatrixEdge) : Decidable (IsCanonicalStarForestShape S) := by
  unfold IsCanonicalStarForestShape
  infer_instance

/-- Exhaustive finite classification of star-forest supports in `K_{3,4}`. -/
theorem isSupportStarForest_iff_canonicalShape :
    ∀ S : Finset MatrixEdge,
      IsSupportStarForest S ↔ IsCanonicalStarForestShape S := by
  native_decide

/-- Forward form of the finite classification. -/
theorem canonicalShape_of_isSupportStarForest
    {S : Finset MatrixEdge}
    (hS : IsSupportStarForest S) :
    IsCanonicalStarForestShape S :=
  (isSupportStarForest_iff_canonicalShape S).1 hS

end Lollipop
