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

/-- Three edges all incident to one column are canonically the three-edge
column star. -/
theorem canonicalShape_of_card_eq_three_of_colNeighbors_card_eq_three
    {S : Finset MatrixEdge} {j : Fin 4}
    (hcard : S.card = 3) (hcol : (colNeighbors S j).card = 3) :
    IsCanonicalStarForestShape S := by
  rcases Finset.card_eq_three.mp hcol with
    ⟨i0, i1, i2, hi01, hi02, hi12, hneighbors⟩
  have hfiber_card : (S.filter fun e : MatrixEdge => e.2 = j).card = 3 := by
    rw [colFiber_card_eq_colNeighbors_card, hcol]
  have hfiber_eq : (S.filter fun e : MatrixEdge => e.2 = j) = S :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      (by rw [hcard, hfiber_card])
  have hi0_mem : i0 ∈ colNeighbors S j := by rw [hneighbors]; simp
  have hi1_mem : i1 ∈ colNeighbors S j := by rw [hneighbors]; simp
  have hi2_mem : i2 ∈ colNeighbors S j := by rw [hneighbors]; simp
  have hS :
      S = {((i0, j) : MatrixEdge), (i1, j), (i2, j)} := by
    ext e
    rcases e with ⟨r, c⟩
    constructor
    · intro he
      have hfilter : (r, c) ∈ S.filter (fun e : MatrixEdge => e.2 = j) := by
        simpa [hfiber_eq] using he
      have hcj : c = j := (Finset.mem_filter.mp hfilter).2
      have hr : r ∈ colNeighbors S j := by
        simpa [hcj] using he
      rw [hneighbors] at hr
      simp at hr
      rcases hr with rfl | rfl | rfl <;> simp [hcj]
    · intro he
      simp at he
      rcases he with h | h | h
      · rcases h with ⟨rfl, rfl⟩
        simpa using hi0_mem
      · rcases h with ⟨rfl, rfl⟩
        simpa using hi1_mem
      · rcases h with ⟨rfl, rfl⟩
        simpa using hi2_mem
  let er : Fin 3 ≃ Fin 3 :=
    permSendTripleToZeroOneTwo (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) i0 i1 i2
  let ec : Fin 4 ≃ Fin 4 := Equiv.swap j 0
  have her0 : er i0 = (0 : Fin 3) :=
    permSendTripleToZeroOneTwo_apply_first (by decide) (by decide) hi01 hi02
  have her1 : er i1 = (1 : Fin 3) :=
    permSendTripleToZeroOneTwo_apply_second (by decide) hi12
  have her2 : er i2 = (2 : Fin 3) :=
    permSendTripleToZeroOneTwo_apply_third (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) i0 i1 i2
  have hec0 : ec j = (0 : Fin 4) := by simp [ec]
  exact canonicalShape_of_supportRelabel_eq
    (S := S) (T := shape3_col)
    (by simp [canonicalStarForestSupports, shape3_col])
    er ec
    (by
      rw [hS, supportRelabel_eq_image]
      simp [shape3_col, er, ec, her0, her1, her2, hec0])

/-- A three-edge star forest with a degree-two row is a row-two star plus a
singleton after relabeling. -/
theorem canonicalShape_of_card_eq_three_of_rowNeighbors_card_eq_two
    {S : Finset MatrixEdge} {i : Fin 3}
    (hcard : S.card = 3) (hstar : IsSupportStarForest S)
    (hrow : (rowNeighbors S i).card = 2) :
    IsCanonicalStarForestShape S := by
  rcases Finset.card_eq_two.mp hrow with ⟨j0, j1, hj01, hneighbors⟩
  have hfiber_card : (S.filter fun e : MatrixEdge => e.1 = i).card = 2 := by
    rw [rowFiber_card_eq_rowNeighbors_card, hrow]
  obtain ⟨e, heS, he_not_fiber⟩ :
      ∃ e ∈ S, e ∉ S.filter (fun e : MatrixEdge => e.1 = i) :=
    Finset.exists_mem_notMem_of_card_lt_card (s := S.filter fun e : MatrixEdge => e.1 = i)
      (t := S) (by omega)
  rcases e with ⟨k, l⟩
  have hk_ne_i : k ≠ i := by
    intro hki
    have hil : (i, l) ∈ S := by simpa [hki] using heS
    exact he_not_fiber (by simp [hil, hki])
  have hi_ne_k : i ≠ k := fun hik => hk_ne_i hik.symm
  have hj0_mem : (i, j0) ∈ S := by
    have : j0 ∈ rowNeighbors S i := by rw [hneighbors]; simp
    simpa using this
  have hj1_mem : (i, j1) ∈ S := by
    have : j1 ∈ rowNeighbors S i := by rw [hneighbors]; simp
    simpa using this
  have hl_ne_j0 : l ≠ j0 := by
    intro hlj0
    have hcol : 1 < (colNeighbors S j0).card := by
      refine Finset.one_lt_card.mpr ?_
      refine ⟨i, ?_, k, ?_, ?_⟩
      · simpa using hj0_mem
      · simpa [hlj0] using heS
      · exact hi_ne_k
    exact hstar (hasSupportPath3_of_edge_one_lt_degrees
      hj0_mem (by omega) hcol)
  have hl_ne_j1 : l ≠ j1 := by
    intro hlj1
    have hcol : 1 < (colNeighbors S j1).card := by
      refine Finset.one_lt_card.mpr ?_
      refine ⟨i, ?_, k, ?_, ?_⟩
      · simpa using hj1_mem
      · simpa [hlj1] using heS
      · exact hi_ne_k
    exact hstar (hasSupportPath3_of_edge_one_lt_degrees
      hj1_mem (by omega) hcol)
  let T : Finset MatrixEdge := {((i, j0) : MatrixEdge), (i, j1), (k, l)}
  have hT_subset : T ⊆ S := by
    intro e he
    simp [T] at he
    rcases he with he | he | he
    · rcases he with ⟨rfl, rfl⟩
      exact hj0_mem
    · rcases he with ⟨rfl, rfl⟩
      exact hj1_mem
    · rcases he with ⟨rfl, rfl⟩
      exact heS
  have hT_card : T.card = 3 := by
    have h01 : ((i, j0) : MatrixEdge) ≠ (i, j1) := by
      intro h
      exact hj01 (congrArg Prod.snd h)
    have h02 : ((i, j0) : MatrixEdge) ≠ (k, l) := by
      intro h
      exact hk_ne_i (congrArg Prod.fst h).symm
    have h12 : ((i, j1) : MatrixEdge) ≠ (k, l) := by
      intro h
      exact hk_ne_i (congrArg Prod.fst h).symm
    simp [T, h01, h02, h12]
  have hS : S = T := by
    exact (Finset.eq_of_subset_of_card_le hT_subset (by omega)).symm
  let er : Fin 3 ≃ Fin 3 :=
    permSendPairToZeroOne (0 : Fin 3) (1 : Fin 3) i k
  let ec : Fin 4 ≃ Fin 4 :=
    permSendTripleToZeroOneTwo (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) j0 j1 l
  have her0 : er i = (0 : Fin 3) :=
    permSendPairToZeroOne_apply_first (by decide) hi_ne_k
  have her1 : er k = (1 : Fin 3) :=
    permSendPairToZeroOne_apply_second (0 : Fin 3) (1 : Fin 3) i k
  have hec0 : ec j0 = (0 : Fin 4) :=
    permSendTripleToZeroOneTwo_apply_first (by decide) (by decide) hj01
      (fun h => hl_ne_j0 h.symm)
  have hec1 : ec j1 = (1 : Fin 4) :=
    permSendTripleToZeroOneTwo_apply_second (by decide)
      (fun h => hl_ne_j1 h.symm)
  have hec2 : ec l = (2 : Fin 4) :=
    permSendTripleToZeroOneTwo_apply_third (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) j0 j1 l
  exact canonicalShape_of_supportRelabel_eq
    (S := S) (T := shape3_row_plus_singleton)
    (by simp [canonicalStarForestSupports, shape3_row_plus_singleton])
    er ec
    (by
      rw [hS, supportRelabel_eq_image]
      simp [T, shape3_row_plus_singleton, er, ec, her0, her1, hec0, hec1, hec2])

/-- A three-edge star forest with a degree-two column is a column-two star
plus a singleton after relabeling. -/
theorem canonicalShape_of_card_eq_three_of_colNeighbors_card_eq_two
    {S : Finset MatrixEdge} {j : Fin 4}
    (hcard : S.card = 3) (hstar : IsSupportStarForest S)
    (hcol : (colNeighbors S j).card = 2) :
    IsCanonicalStarForestShape S := by
  rcases Finset.card_eq_two.mp hcol with ⟨i0, i1, hi01, hneighbors⟩
  have hfiber_card : (S.filter fun e : MatrixEdge => e.2 = j).card = 2 := by
    rw [colFiber_card_eq_colNeighbors_card, hcol]
  obtain ⟨e, heS, he_not_fiber⟩ :
      ∃ e ∈ S, e ∉ S.filter (fun e : MatrixEdge => e.2 = j) :=
    Finset.exists_mem_notMem_of_card_lt_card (s := S.filter fun e : MatrixEdge => e.2 = j)
      (t := S) (by omega)
  rcases e with ⟨k, l⟩
  have hl_ne_j : l ≠ j := by
    intro hlj
    have hkj : (k, j) ∈ S := by simpa [hlj] using heS
    exact he_not_fiber (by simp [hkj, hlj])
  have hj_ne_l : j ≠ l := fun hjl => hl_ne_j hjl.symm
  have hi0_mem : (i0, j) ∈ S := by
    have : i0 ∈ colNeighbors S j := by rw [hneighbors]; simp
    simpa using this
  have hi1_mem : (i1, j) ∈ S := by
    have : i1 ∈ colNeighbors S j := by rw [hneighbors]; simp
    simpa using this
  have hk_ne_i0 : k ≠ i0 := by
    intro hki0
    have hrow : 1 < (rowNeighbors S i0).card := by
      refine Finset.one_lt_card.mpr ?_
      refine ⟨j, ?_, l, ?_, ?_⟩
      · simpa using hi0_mem
      · simpa [hki0] using heS
      · exact hj_ne_l
    exact hstar (hasSupportPath3_of_edge_one_lt_degrees
      hi0_mem hrow (by omega))
  have hk_ne_i1 : k ≠ i1 := by
    intro hki1
    have hrow : 1 < (rowNeighbors S i1).card := by
      refine Finset.one_lt_card.mpr ?_
      refine ⟨j, ?_, l, ?_, ?_⟩
      · simpa using hi1_mem
      · simpa [hki1] using heS
      · exact hj_ne_l
    exact hstar (hasSupportPath3_of_edge_one_lt_degrees
      hi1_mem hrow (by omega))
  let T : Finset MatrixEdge := {((i0, j) : MatrixEdge), (i1, j), (k, l)}
  have hT_subset : T ⊆ S := by
    intro e he
    simp [T] at he
    rcases he with he | he | he
    · rcases he with ⟨rfl, rfl⟩
      exact hi0_mem
    · rcases he with ⟨rfl, rfl⟩
      exact hi1_mem
    · rcases he with ⟨rfl, rfl⟩
      exact heS
  have hT_card : T.card = 3 := by
    have h01 : ((i0, j) : MatrixEdge) ≠ (i1, j) := by
      intro h
      exact hi01 (congrArg Prod.fst h)
    have h02 : ((i0, j) : MatrixEdge) ≠ (k, l) := by
      intro h
      exact hk_ne_i0 (congrArg Prod.fst h).symm
    have h12 : ((i1, j) : MatrixEdge) ≠ (k, l) := by
      intro h
      exact hk_ne_i1 (congrArg Prod.fst h).symm
    simp [T, h01, h02, h12]
  have hS : S = T := by
    exact (Finset.eq_of_subset_of_card_le hT_subset (by omega)).symm
  let er : Fin 3 ≃ Fin 3 :=
    permSendTripleToZeroOneTwo (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) i0 i1 k
  let ec : Fin 4 ≃ Fin 4 :=
    permSendPairToZeroOne (0 : Fin 4) (1 : Fin 4) j l
  have her0 : er i0 = (0 : Fin 3) :=
    permSendTripleToZeroOneTwo_apply_first (by decide) (by decide) hi01
      (fun h => hk_ne_i0 h.symm)
  have her1 : er i1 = (1 : Fin 3) :=
    permSendTripleToZeroOneTwo_apply_second (by decide)
      (fun h => hk_ne_i1 h.symm)
  have her2 : er k = (2 : Fin 3) :=
    permSendTripleToZeroOneTwo_apply_third (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) i0 i1 k
  have hec0 : ec j = (0 : Fin 4) :=
    permSendPairToZeroOne_apply_first (by decide) hj_ne_l
  have hec1 : ec l = (1 : Fin 4) :=
    permSendPairToZeroOne_apply_second (0 : Fin 4) (1 : Fin 4) j l
  exact canonicalShape_of_supportRelabel_eq
    (S := S) (T := shape3_col_plus_singleton)
    (by simp [canonicalStarForestSupports, shape3_col_plus_singleton])
    er ec
    (by
      rw [hS, supportRelabel_eq_image]
      simp [T, shape3_col_plus_singleton, er, ec, her0, her1, her2, hec0, hec1])

/-- Three edges with all row and column degrees at most one are the three
singleton components after relabeling. -/
theorem canonicalShape_of_card_eq_three_of_all_degrees_le_one
    {S : Finset MatrixEdge}
    (hcard : S.card = 3)
    (hrowle : ∀ i : Fin 3, (rowNeighbors S i).card ≤ 1)
    (hcolle : ∀ j : Fin 4, (colNeighbors S j).card ≤ 1) :
    IsCanonicalStarForestShape S := by
  rcases Finset.card_eq_three.mp hcard with
    ⟨e0, e1, e2, he01, he02, he12, hS⟩
  rcases e0 with ⟨i0, j0⟩
  rcases e1 with ⟨i1, j1⟩
  rcases e2 with ⟨i2, j2⟩
  have he0_mem : (i0, j0) ∈ S := by rw [hS]; simp
  have he1_mem : (i1, j1) ∈ S := by rw [hS]; simp
  have he2_mem : (i2, j2) ∈ S := by rw [hS]; simp
  have hi01 : i0 ≠ i1 := by
    intro h
    have hj : j0 ≠ j1 := by
      intro hj
      exact he01 (by simp [h, hj])
    have hrow : 1 < (rowNeighbors S i0).card := by
      refine Finset.one_lt_card.mpr ?_
      refine ⟨j0, ?_, j1, ?_, hj⟩
      · simpa using he0_mem
      · simpa [h] using he1_mem
    exact (not_lt_of_ge (hrowle i0)) hrow
  have hi02 : i0 ≠ i2 := by
    intro h
    have hj : j0 ≠ j2 := by
      intro hj
      exact he02 (by simp [h, hj])
    have hrow : 1 < (rowNeighbors S i0).card := by
      refine Finset.one_lt_card.mpr ?_
      refine ⟨j0, ?_, j2, ?_, hj⟩
      · simpa using he0_mem
      · simpa [h] using he2_mem
    exact (not_lt_of_ge (hrowle i0)) hrow
  have hi12 : i1 ≠ i2 := by
    intro h
    have hj : j1 ≠ j2 := by
      intro hj
      exact he12 (by simp [h, hj])
    have hrow : 1 < (rowNeighbors S i1).card := by
      refine Finset.one_lt_card.mpr ?_
      refine ⟨j1, ?_, j2, ?_, hj⟩
      · simpa using he1_mem
      · simpa [h] using he2_mem
    exact (not_lt_of_ge (hrowle i1)) hrow
  have hj01 : j0 ≠ j1 := by
    intro h
    have hi : i0 ≠ i1 := hi01
    have hcol : 1 < (colNeighbors S j0).card := by
      refine Finset.one_lt_card.mpr ?_
      refine ⟨i0, ?_, i1, ?_, hi⟩
      · simpa using he0_mem
      · simpa [h] using he1_mem
    exact (not_lt_of_ge (hcolle j0)) hcol
  have hj02 : j0 ≠ j2 := by
    intro h
    have hi : i0 ≠ i2 := hi02
    have hcol : 1 < (colNeighbors S j0).card := by
      refine Finset.one_lt_card.mpr ?_
      refine ⟨i0, ?_, i2, ?_, hi⟩
      · simpa using he0_mem
      · simpa [h] using he2_mem
    exact (not_lt_of_ge (hcolle j0)) hcol
  have hj12 : j1 ≠ j2 := by
    intro h
    have hi : i1 ≠ i2 := hi12
    have hcol : 1 < (colNeighbors S j1).card := by
      refine Finset.one_lt_card.mpr ?_
      refine ⟨i1, ?_, i2, ?_, hi⟩
      · simpa using he1_mem
      · simpa [h] using he2_mem
    exact (not_lt_of_ge (hcolle j1)) hcol
  let er : Fin 3 ≃ Fin 3 :=
    permSendTripleToZeroOneTwo (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) i0 i1 i2
  let ec : Fin 4 ≃ Fin 4 :=
    permSendTripleToZeroOneTwo (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) j0 j1 j2
  have her0 : er i0 = (0 : Fin 3) :=
    permSendTripleToZeroOneTwo_apply_first (by decide) (by decide) hi01 hi02
  have her1 : er i1 = (1 : Fin 3) :=
    permSendTripleToZeroOneTwo_apply_second (by decide) hi12
  have her2 : er i2 = (2 : Fin 3) :=
    permSendTripleToZeroOneTwo_apply_third (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) i0 i1 i2
  have hec0 : ec j0 = (0 : Fin 4) :=
    permSendTripleToZeroOneTwo_apply_first (by decide) (by decide) hj01 hj02
  have hec1 : ec j1 = (1 : Fin 4) :=
    permSendTripleToZeroOneTwo_apply_second (by decide) hj12
  have hec2 : ec j2 = (2 : Fin 4) :=
    permSendTripleToZeroOneTwo_apply_third (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) j0 j1 j2
  exact canonicalShape_of_supportRelabel_eq
    (S := S) (T := shape3_singletons)
    (by simp [canonicalStarForestSupports, shape3_singletons])
    er ec
    (by
      rw [hS, supportRelabel_eq_image]
      simp [shape3_singletons, er, ec, her0, her1, her2, hec0, hec1, hec2])

/-- Structural classification of every three-edge star-forest support. -/
theorem canonicalShape_of_card_eq_three_of_starForest
    {S : Finset MatrixEdge}
    (hcard : S.card = 3) (hstar : IsSupportStarForest S) :
    IsCanonicalStarForestShape S := by
  by_cases hrow3 : ∃ i : Fin 3, (rowNeighbors S i).card = 3
  · rcases hrow3 with ⟨i, hi⟩
    exact canonicalShape_of_card_eq_three_of_rowNeighbors_card_eq_three
      hcard hi
  by_cases hcol3 : ∃ j : Fin 4, (colNeighbors S j).card = 3
  · rcases hcol3 with ⟨j, hj⟩
    exact canonicalShape_of_card_eq_three_of_colNeighbors_card_eq_three
      hcard hj
  by_cases hrow2 : ∃ i : Fin 3, (rowNeighbors S i).card = 2
  · rcases hrow2 with ⟨i, hi⟩
    exact canonicalShape_of_card_eq_three_of_rowNeighbors_card_eq_two
      hcard hstar hi
  by_cases hcol2 : ∃ j : Fin 4, (colNeighbors S j).card = 2
  · rcases hcol2 with ⟨j, hj⟩
    exact canonicalShape_of_card_eq_three_of_colNeighbors_card_eq_two
      hcard hstar hj
  apply canonicalShape_of_card_eq_three_of_all_degrees_le_one hcard
  · intro i
    have hle : (rowNeighbors S i).card ≤ 3 := by
      have hfiber_le : (S.filter fun e : MatrixEdge => e.1 = i).card ≤ S.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      rwa [rowFiber_card_eq_rowNeighbors_card, hcard] at hfiber_le
    have hne2 : (rowNeighbors S i).card ≠ 2 := by
      intro h
      exact hrow2 ⟨i, h⟩
    have hne3 : (rowNeighbors S i).card ≠ 3 := by
      intro h
      exact hrow3 ⟨i, h⟩
    omega
  · intro j
    have hle : (colNeighbors S j).card ≤ 3 := by
      have hfiber_le : (S.filter fun e : MatrixEdge => e.2 = j).card ≤ S.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      rwa [colFiber_card_eq_colNeighbors_card, hcard] at hfiber_le
    have hne2 : (colNeighbors S j).card ≠ 2 := by
      intro h
      exact hcol2 ⟨j, h⟩
    have hne3 : (colNeighbors S j).card ≠ 3 := by
      intro h
      exact hcol3 ⟨j, h⟩
    omega

/-- Four edges all incident to one row are canonically the four-edge row
star. -/
theorem canonicalShape_of_card_eq_four_of_rowNeighbors_card_eq_four
    {S : Finset MatrixEdge} {i : Fin 3}
    (hcard : S.card = 4) (hrow : (rowNeighbors S i).card = 4) :
    IsCanonicalStarForestShape S := by
  have hfiber_card : (S.filter fun e : MatrixEdge => e.1 = i).card = 4 := by
    rw [rowFiber_card_eq_rowNeighbors_card, hrow]
  have hfiber_eq : (S.filter fun e : MatrixEdge => e.1 = i) = S :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      (by rw [hcard, hfiber_card])
  have hneigh : rowNeighbors S i = Finset.univ :=
    Finset.eq_univ_of_card (rowNeighbors S i)
      (by simpa [Fintype.card_fin] using hrow)
  have hS :
      S = {((i, 0) : MatrixEdge), (i, 1), (i, 2), (i, 3)} := by
    ext e
    rcases e with ⟨r, c⟩
    constructor
    · intro he
      have hfilter : (r, c) ∈ S.filter (fun e : MatrixEdge => e.1 = i) := by
        simpa [hfiber_eq] using he
      have hri : r = i := (Finset.mem_filter.mp hfilter).2
      fin_cases c <;> simp [hri]
    · intro he
      simp at he
      rcases he with h | h | h | h
      · rcases h with ⟨hr, hc⟩
        rw [hr, hc]
        have : (0 : Fin 4) ∈ rowNeighbors S i := by
          rw [hneigh]
          simp
        simpa using this
      · rcases h with ⟨hr, hc⟩
        rw [hr, hc]
        have : (1 : Fin 4) ∈ rowNeighbors S i := by
          rw [hneigh]
          simp
        simpa using this
      · rcases h with ⟨hr, hc⟩
        rw [hr, hc]
        have : (2 : Fin 4) ∈ rowNeighbors S i := by
          rw [hneigh]
          simp
        simpa using this
      · rcases h with ⟨hr, hc⟩
        rw [hr, hc]
        have : (3 : Fin 4) ∈ rowNeighbors S i := by
          rw [hneigh]
          simp
        simpa using this
  let er : Fin 3 ≃ Fin 3 := Equiv.swap i 0
  let ec : Fin 4 ≃ Fin 4 := Equiv.refl (Fin 4)
  have her0 : er i = (0 : Fin 3) := by simp [er]
  exact canonicalShape_of_supportRelabel_eq
    (S := S) (T := shape4_row)
    (by simp [canonicalStarForestSupports, shape4_row])
    er ec
    (by
      rw [hS, supportRelabel_eq_image]
      simp [shape4_row, er, ec, her0])

/-- A four-edge star forest with a degree-three row is a row-three star plus
a singleton after relabeling. -/
theorem canonicalShape_of_card_eq_four_of_rowNeighbors_card_eq_three
    {S : Finset MatrixEdge} {i : Fin 3}
    (hcard : S.card = 4) (hstar : IsSupportStarForest S)
    (hrow : (rowNeighbors S i).card = 3) :
    IsCanonicalStarForestShape S := by
  rcases Finset.card_eq_three.mp hrow with
    ⟨j0, j1, j2, hj01, hj02, hj12, hneighbors⟩
  have hfiber_card : (S.filter fun e : MatrixEdge => e.1 = i).card = 3 := by
    rw [rowFiber_card_eq_rowNeighbors_card, hrow]
  obtain ⟨e, heS, he_not_fiber⟩ :
      ∃ e ∈ S, e ∉ S.filter (fun e : MatrixEdge => e.1 = i) :=
    Finset.exists_mem_notMem_of_card_lt_card (s := S.filter fun e : MatrixEdge => e.1 = i)
      (t := S) (by omega)
  rcases e with ⟨k, l⟩
  have hk_ne_i : k ≠ i := by
    intro hki
    have hil : (i, l) ∈ S := by simpa [hki] using heS
    exact he_not_fiber (by simp [hil, hki])
  have hi_ne_k : i ≠ k := fun hik => hk_ne_i hik.symm
  have hj0_mem : (i, j0) ∈ S := by
    have : j0 ∈ rowNeighbors S i := by rw [hneighbors]; simp
    simpa using this
  have hj1_mem : (i, j1) ∈ S := by
    have : j1 ∈ rowNeighbors S i := by rw [hneighbors]; simp
    simpa using this
  have hj2_mem : (i, j2) ∈ S := by
    have : j2 ∈ rowNeighbors S i := by rw [hneighbors]; simp
    simpa using this
  have hl_ne_j0 : l ≠ j0 := by
    intro hlj0
    have hcol : 1 < (colNeighbors S j0).card := by
      refine Finset.one_lt_card.mpr ?_
      refine ⟨i, ?_, k, ?_, hi_ne_k⟩
      · simpa using hj0_mem
      · simpa [hlj0] using heS
    exact hstar (hasSupportPath3_of_edge_one_lt_degrees
      hj0_mem (by omega) hcol)
  have hl_ne_j1 : l ≠ j1 := by
    intro hlj1
    have hcol : 1 < (colNeighbors S j1).card := by
      refine Finset.one_lt_card.mpr ?_
      refine ⟨i, ?_, k, ?_, hi_ne_k⟩
      · simpa using hj1_mem
      · simpa [hlj1] using heS
    exact hstar (hasSupportPath3_of_edge_one_lt_degrees
      hj1_mem (by omega) hcol)
  have hl_ne_j2 : l ≠ j2 := by
    intro hlj2
    have hcol : 1 < (colNeighbors S j2).card := by
      refine Finset.one_lt_card.mpr ?_
      refine ⟨i, ?_, k, ?_, hi_ne_k⟩
      · simpa using hj2_mem
      · simpa [hlj2] using heS
    exact hstar (hasSupportPath3_of_edge_one_lt_degrees
      hj2_mem (by omega) hcol)
  let T : Finset MatrixEdge :=
    {((i, j0) : MatrixEdge), (i, j1), (i, j2), (k, l)}
  have hT_subset : T ⊆ S := by
    intro e he
    simp [T] at he
    rcases he with he | he | he | he
    · rcases he with ⟨rfl, rfl⟩
      exact hj0_mem
    · rcases he with ⟨rfl, rfl⟩
      exact hj1_mem
    · rcases he with ⟨rfl, rfl⟩
      exact hj2_mem
    · rcases he with ⟨rfl, rfl⟩
      exact heS
  have hT_card : T.card = 4 := by
    have h01 : ((i, j0) : MatrixEdge) ≠ (i, j1) := by
      intro h
      exact hj01 (congrArg Prod.snd h)
    have h02 : ((i, j0) : MatrixEdge) ≠ (i, j2) := by
      intro h
      exact hj02 (congrArg Prod.snd h)
    have h03 : ((i, j0) : MatrixEdge) ≠ (k, l) := by
      intro h
      exact hk_ne_i (congrArg Prod.fst h).symm
    have h12 : ((i, j1) : MatrixEdge) ≠ (i, j2) := by
      intro h
      exact hj12 (congrArg Prod.snd h)
    have h13 : ((i, j1) : MatrixEdge) ≠ (k, l) := by
      intro h
      exact hk_ne_i (congrArg Prod.fst h).symm
    have h23 : ((i, j2) : MatrixEdge) ≠ (k, l) := by
      intro h
      exact hk_ne_i (congrArg Prod.fst h).symm
    simp [T, h01, h02, h03, h12, h13, h23]
  have hS : S = T := by
    exact (Finset.eq_of_subset_of_card_le hT_subset (by omega)).symm
  let er : Fin 3 ≃ Fin 3 :=
    permSendPairToZeroOne (0 : Fin 3) (1 : Fin 3) i k
  let ec : Fin 4 ≃ Fin 4 :=
    permSendTripleToZeroOneTwo (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) j0 j1 j2
  have her0 : er i = (0 : Fin 3) :=
    permSendPairToZeroOne_apply_first (by decide) hi_ne_k
  have her1 : er k = (1 : Fin 3) :=
    permSendPairToZeroOne_apply_second (0 : Fin 3) (1 : Fin 3) i k
  have hec0 : ec j0 = (0 : Fin 4) :=
    permSendTripleToZeroOneTwo_apply_first (by decide) (by decide) hj01 hj02
  have hec1 : ec j1 = (1 : Fin 4) :=
    permSendTripleToZeroOneTwo_apply_second (by decide) hj12
  have hec2 : ec j2 = (2 : Fin 4) :=
    permSendTripleToZeroOneTwo_apply_third (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) j0 j1 j2
  have hec3 : ec l = (3 : Fin 4) := by
    have hne0 : ec l ≠ (0 : Fin 4) := by
      intro h
      have : ec l = ec j0 := by rw [h, hec0]
      exact hl_ne_j0 (ec.injective this)
    have hne1 : ec l ≠ (1 : Fin 4) := by
      intro h
      have : ec l = ec j1 := by rw [h, hec1]
      exact hl_ne_j1 (ec.injective this)
    have hne2 : ec l ≠ (2 : Fin 4) := by
      intro h
      have : ec l = ec j2 := by rw [h, hec2]
      exact hl_ne_j2 (ec.injective this)
    apply Fin.ext
    have hlt : (ec l).val < 4 := (ec l).isLt
    interval_cases h : (ec l).val
    · exfalso
      exact hne0 (Fin.ext (by simpa using h))
    · exfalso
      exact hne1 (Fin.ext (by simpa using h))
    · exfalso
      exact hne2 (Fin.ext (by simpa using h))
    · simp
  exact canonicalShape_of_supportRelabel_eq
    (S := S) (T := shape4_row3_plus_singleton)
    (by simp [canonicalStarForestSupports, shape4_row3_plus_singleton])
    er ec
    (by
      rw [hS, supportRelabel_eq_image]
      simp [T, shape4_row3_plus_singleton, er, ec, her0, her1, hec0, hec1, hec2, hec3])

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
