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

theorem supportRelabel_eq_image
    (er : Fin 3 ≃ Fin 3) (ec : Fin 4 ≃ Fin 4)
    (S : Finset MatrixEdge) :
    supportRelabel er ec S =
      S.image (fun e : MatrixEdge => (er e.1, ec e.2)) := by
  ext e
  constructor
  · intro he
    refine Finset.mem_image.mpr ?_
    refine ⟨(er.symm e.1, ec.symm e.2), ?_, ?_⟩
    · simpa [supportRelabel] using he
    · simp
  · intro he
    rcases Finset.mem_image.mp he with ⟨a, ha, rfl⟩
    simp [supportRelabel, ha]

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

theorem canonicalShape_of_supportRelabel_eq
    {S T : Finset MatrixEdge}
    (hT : T ∈ canonicalStarForestSupports)
    (er : Fin 3 ≃ Fin 3) (ec : Fin 4 ≃ Fin 4)
    (hrel : supportRelabel er ec S = T) :
    IsCanonicalStarForestShape S := by
  unfold IsCanonicalStarForestShape allCanonicalStarForestShapes
  refine Finset.mem_biUnion.mpr ⟨T, hT, ?_⟩
  unfold relabeledStarForestSupportsOf
  refine Finset.mem_biUnion.mpr ⟨er.symm, Finset.mem_univ _, ?_⟩
  refine Finset.mem_image.mpr ⟨ec.symm, Finset.mem_univ _, ?_⟩
  rw [← hrel]
  exact supportRelabel_symm_relabel er ec S

theorem canonicalShape_of_card_eq_zero
    {S : Finset MatrixEdge} (hcard : S.card = 0) :
    IsCanonicalStarForestShape S := by
  have hS : S = ∅ := Finset.card_eq_zero.mp hcard
  exact canonicalShape_of_supportRelabel_eq
    (S := S) (T := shape0)
    (by simp [canonicalStarForestSupports, shape0])
    (Equiv.refl (Fin 3)) (Equiv.refl (Fin 4))
    (by simp [hS, supportRelabel, shape0])

theorem canonicalShape_of_card_eq_one
    {S : Finset MatrixEdge} (hcard : S.card = 1) :
    IsCanonicalStarForestShape S := by
  rcases Finset.card_eq_one.mp hcard with ⟨e, hS⟩
  rcases e with ⟨i, j⟩
  let er : Fin 3 ≃ Fin 3 := Equiv.swap i 0
  let ec : Fin 4 ≃ Fin 4 := Equiv.swap j 0
  exact canonicalShape_of_supportRelabel_eq
    (S := S) (T := shape1)
    (by simp [canonicalStarForestSupports, shape1])
    er ec
    (by
      rw [hS, supportRelabel_eq_image]
      simp [shape1, er, ec])

theorem canonicalShape_of_card_eq_two
    {S : Finset MatrixEdge} (hcard : S.card = 2) :
    IsCanonicalStarForestShape S := by
  rcases Finset.card_eq_two.mp hcard with ⟨e, f, hef, hS⟩
  rcases e with ⟨i, j⟩
  rcases f with ⟨k, l⟩
  by_cases hrow : i = k
  · subst k
    have hcol : j ≠ l := by
      intro h
      exact hef (by simp [h])
    let er : Fin 3 ≃ Fin 3 := Equiv.swap i 0
    let ec : Fin 4 ≃ Fin 4 :=
      permSendPairToZeroOne (0 : Fin 4) (1 : Fin 4) j l
    have her0 : er i = (0 : Fin 3) := by simp [er]
    have hec0 : ec j = (0 : Fin 4) :=
      permSendPairToZeroOne_apply_first (by decide) hcol
    have hec1 : ec l = (1 : Fin 4) :=
      permSendPairToZeroOne_apply_second (0 : Fin 4) (1 : Fin 4) j l
    exact canonicalShape_of_supportRelabel_eq
      (S := S) (T := shape2_row)
      (by simp [canonicalStarForestSupports, shape2_row])
      er ec
      (by
        rw [hS, supportRelabel_eq_image]
        simp [shape2_row, er, ec, her0, hec0, hec1])
  · by_cases hcol : j = l
    · subst l
      let er : Fin 3 ≃ Fin 3 :=
        permSendPairToZeroOne (0 : Fin 3) (1 : Fin 3) i k
      let ec : Fin 4 ≃ Fin 4 := Equiv.swap j 0
      have her0 : er i = (0 : Fin 3) :=
        permSendPairToZeroOne_apply_first (by decide) hrow
      have her1 : er k = (1 : Fin 3) :=
        permSendPairToZeroOne_apply_second (0 : Fin 3) (1 : Fin 3) i k
      have hec0 : ec j = (0 : Fin 4) := by simp [ec]
      exact canonicalShape_of_supportRelabel_eq
        (S := S) (T := shape2_col)
        (by simp [canonicalStarForestSupports, shape2_col])
        er ec
        (by
          rw [hS, supportRelabel_eq_image]
          simp [shape2_col, er, ec, her0, her1, hec0])
    · let er : Fin 3 ≃ Fin 3 :=
        permSendPairToZeroOne (0 : Fin 3) (1 : Fin 3) i k
      let ec : Fin 4 ≃ Fin 4 :=
        permSendPairToZeroOne (0 : Fin 4) (1 : Fin 4) j l
      have her0 : er i = (0 : Fin 3) :=
        permSendPairToZeroOne_apply_first (by decide) hrow
      have her1 : er k = (1 : Fin 3) :=
        permSendPairToZeroOne_apply_second (0 : Fin 3) (1 : Fin 3) i k
      have hec0 : ec j = (0 : Fin 4) :=
        permSendPairToZeroOne_apply_first (by decide) hcol
      have hec1 : ec l = (1 : Fin 4) :=
        permSendPairToZeroOne_apply_second (0 : Fin 4) (1 : Fin 4) j l
      exact canonicalShape_of_supportRelabel_eq
        (S := S) (T := shape2_singletons)
        (by simp [canonicalStarForestSupports, shape2_singletons])
        er ec
        (by
          rw [hS, supportRelabel_eq_image]
          simp [shape2_singletons, er, ec, her0, her1, hec0, hec1])

theorem canonicalShape_of_card_eq_three_of_rowNeighbors_card_eq_three
    {S : Finset MatrixEdge} {i : Fin 3}
    (hcard : S.card = 3) (hrow : (rowNeighbors S i).card = 3) :
    IsCanonicalStarForestShape S := by
  rcases Finset.card_eq_three.mp hrow with
    ⟨j0, j1, j2, hj01, hj02, hj12, hneighbors⟩
  have hfiber_card : (S.filter fun e : MatrixEdge => e.1 = i).card = 3 := by
    rw [rowFiber_card_eq_rowNeighbors_card, hrow]
  have hfiber_eq : (S.filter fun e : MatrixEdge => e.1 = i) = S :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      (by rw [hcard, hfiber_card])
  have hj0_mem : j0 ∈ rowNeighbors S i := by rw [hneighbors]; simp
  have hj1_mem : j1 ∈ rowNeighbors S i := by rw [hneighbors]; simp
  have hj2_mem : j2 ∈ rowNeighbors S i := by rw [hneighbors]; simp
  have hS :
      S = {((i, j0) : MatrixEdge), (i, j1), (i, j2)} := by
    ext e
    rcases e with ⟨r, c⟩
    constructor
    · intro he
      have hfilter : (r, c) ∈ S.filter (fun e : MatrixEdge => e.1 = i) := by
        simpa [hfiber_eq] using he
      have hri : r = i := (Finset.mem_filter.mp hfilter).2
      have hc : c ∈ rowNeighbors S i := by
        simpa [hri] using he
      rw [hneighbors] at hc
      simp at hc
      rcases hc with rfl | rfl | rfl <;> simp [hri]
    · intro he
      simp at he
      rcases he with h | h | h
      · rcases h with ⟨rfl, rfl⟩
        simpa using hj0_mem
      · rcases h with ⟨rfl, rfl⟩
        simpa using hj1_mem
      · rcases h with ⟨rfl, rfl⟩
        simpa using hj2_mem
  let er : Fin 3 ≃ Fin 3 := Equiv.swap i 0
  let ec : Fin 4 ≃ Fin 4 :=
    permSendTripleToZeroOneTwo (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) j0 j1 j2
  have her0 : er i = (0 : Fin 3) := by simp [er]
  have hec0 : ec j0 = (0 : Fin 4) :=
    permSendTripleToZeroOneTwo_apply_first (by decide) (by decide) hj01 hj02
  have hec1 : ec j1 = (1 : Fin 4) :=
    permSendTripleToZeroOneTwo_apply_second (by decide) hj12
  have hec2 : ec j2 = (2 : Fin 4) :=
    permSendTripleToZeroOneTwo_apply_third (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) j0 j1 j2
  exact canonicalShape_of_supportRelabel_eq
    (S := S) (T := shape3_row)
    (by simp [canonicalStarForestSupports, shape3_row])
    er ec
    (by
      rw [hS, supportRelabel_eq_image]
      simp [shape3_row, er, ec, her0, hec0, hec1, hec2])

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
