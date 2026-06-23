import Lollipop.Internal.Matrix.Basic
import Mathlib.Tactic

/-!
Finite support graph vocabulary for the `3 x 4` matrix theorem.

The support graph lives on seven vertices: three row vertices and four column
vertices.  A support is a finset of the twelve possible matrix cells.  A
support is a star forest exactly when it has no simple path of length three;
the forward use in the compression proof is that every non-star support
contains such a path, which must be handled by a cycle/path/double-star move.
-/

namespace Lollipop

open BigOperators

/-- Matrix support edges are matrix cells. -/
abbrev MatrixEdge := Fin 3 × Fin 4

/-- Matrix support graph vertices: rows or columns. -/
inductive MatrixVertex where
  | row : Fin 3 → MatrixVertex
  | col : Fin 4 → MatrixVertex
  deriving DecidableEq, Fintype, Repr

/-- The row endpoint of a matrix edge. -/
def MatrixEdge.rowVertex (e : MatrixEdge) : MatrixVertex :=
  MatrixVertex.row e.1

/-- The column endpoint of a matrix edge. -/
def MatrixEdge.colVertex (e : MatrixEdge) : MatrixVertex :=
  MatrixVertex.col e.2

/-- A matrix edge is incident to a support-graph vertex. -/
def MatrixEdge.Incident (e : MatrixEdge) (v : MatrixVertex) : Prop :=
  v = e.rowVertex ∨ v = e.colVertex

instance (e : MatrixEdge) (v : MatrixVertex) : Decidable (e.Incident v) := by
  unfold MatrixEdge.Incident
  infer_instance

/-- Finset support of a natural matrix. -/
def supportOfNat (U : NatMatrix) : Finset MatrixEdge :=
  Finset.univ.filter (fun e : MatrixEdge => 0 < U e.1 e.2)

/-- Support-cardinality descent measure. -/
def supportCardNat (U : NatMatrix) : ℕ :=
  (supportOfNat U).card

/-- Membership in the natural-matrix support is exactly positivity of the
corresponding entry. -/
theorem mem_supportOfNat_iff (U : NatMatrix) (e : MatrixEdge) :
    e ∈ supportOfNat U ↔ 0 < U e.1 e.2 := by
  simp [supportOfNat]

/-- A cell outside the support has zero mass. -/
theorem entry_eq_zero_of_not_mem_support
    (U : NatMatrix) {i : Fin 3} {j : Fin 4}
    (h : (i, j) ∉ supportOfNat U) :
    U i j = 0 := by
  rw [mem_supportOfNat_iff] at h
  exact Nat.eq_zero_of_not_pos h

/-- A cell outside a known support mask has zero mass. -/
theorem entry_eq_zero_of_support_eq
    (U : NatMatrix) {S : Finset MatrixEdge}
    (hU : supportOfNat U = S) {i : Fin 3} {j : Fin 4}
    (h : (i, j) ∉ S) :
    U i j = 0 := by
  exact entry_eq_zero_of_not_mem_support U (by rw [hU]; exact h)

/-- Adjacency in the support graph associated to a support finset. -/
def SupportAdj (S : Finset MatrixEdge) (v w : MatrixVertex) : Prop :=
  v ≠ w ∧ ∃ e ∈ S, e.Incident v ∧ e.Incident w

instance (S : Finset MatrixEdge) (v w : MatrixVertex) :
    Decidable (SupportAdj S v w) := by
  unfold SupportAdj
  infer_instance

/-- Column neighbors of a row in the support graph. -/
def rowNeighbors (S : Finset MatrixEdge) (i : Fin 3) : Finset (Fin 4) :=
  Finset.univ.filter fun j : Fin 4 => (i, j) ∈ S

/-- Row neighbors of a column in the support graph. -/
def colNeighbors (S : Finset MatrixEdge) (j : Fin 4) : Finset (Fin 3) :=
  Finset.univ.filter fun i : Fin 3 => (i, j) ∈ S

/-- Rows of degree at least two in the support graph. -/
def highRows (S : Finset MatrixEdge) : Finset (Fin 3) :=
  Finset.univ.filter fun i : Fin 3 => 1 < (rowNeighbors S i).card

/-- Columns of degree at least two in the support graph. -/
def highCols (S : Finset MatrixEdge) : Finset (Fin 4) :=
  Finset.univ.filter fun j : Fin 4 => 1 < (colNeighbors S j).card

@[simp] theorem mem_rowNeighbors_iff
    (S : Finset MatrixEdge) (i : Fin 3) (j : Fin 4) :
    j ∈ rowNeighbors S i ↔ (i, j) ∈ S := by
  simp [rowNeighbors]

@[simp] theorem mem_colNeighbors_iff
    (S : Finset MatrixEdge) (i : Fin 3) (j : Fin 4) :
    i ∈ colNeighbors S j ↔ (i, j) ∈ S := by
  simp [colNeighbors]

@[simp] theorem mem_highRows_iff
    (S : Finset MatrixEdge) (i : Fin 3) :
    i ∈ highRows S ↔ 1 < (rowNeighbors S i).card := by
  simp [highRows]

@[simp] theorem mem_highCols_iff
    (S : Finset MatrixEdge) (j : Fin 4) :
    j ∈ highCols S ↔ 1 < (colNeighbors S j).card := by
  simp [highCols]

private theorem sum_if_mem_finset_eq_card_mul_add_compl
    {α : Type*} [Fintype α] [DecidableEq α]
    (T : Finset α) (c : ℕ) :
    (∑ x : α, if x ∈ T then c else 1) =
      T.card * c + (Fintype.card α - T.card) := by
  classical
  have hfilter :
      ((Finset.univ : Finset α).filter fun x => x ∈ T) = T := by
    ext x
    simp
  have hcomp :
      ((Finset.univ : Finset α).filter fun x => x ∉ T).card =
        Fintype.card α - T.card := by
    have h :=
      Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset α)) (p := fun x => x ∈ T)
    rw [hfilter] at h
    simp only [Finset.card_univ] at h
    omega
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := (Finset.univ : Finset α)) (p := fun x => x ∈ T)
    (f := fun x => if x ∈ T then c else 1)]
  calc
    (((Finset.univ : Finset α).filter (fun x => x ∈ T)).sum
        fun x => if x ∈ T then c else 1) +
        (((Finset.univ : Finset α).filter (fun x => ¬x ∈ T)).sum
          fun x => if x ∈ T then c else 1)
        = (T.sum fun _ => c) +
            (((Finset.univ : Finset α).filter (fun x => x ∉ T)).sum
              fun _ => 1) := by
          congr 1
          · rw [hfilter]
            refine Finset.sum_congr rfl ?_
            intro x hx
            simp [hx]
          · refine Finset.sum_congr rfl ?_
            intro x hx
            have hxnot : x ∉ T := (Finset.mem_filter.mp hx).2
            simp [hxnot]
    _ = T.card * c + (Fintype.card α - T.card) := by
          simp [hcomp, Finset.sum_const]

theorem rowFiber_card_eq_rowNeighbors_card
    (S : Finset MatrixEdge) (i : Fin 3) :
    (S.filter fun e : MatrixEdge => e.1 = i).card =
      (rowNeighbors S i).card := by
  let f : MatrixEdge → Fin 4 := fun e => e.2
  have hf : Set.InjOn f (S.filter fun e : MatrixEdge => e.1 = i) := by
    intro a ha b hb hab
    rcases a with ⟨ar, ac⟩
    rcases b with ⟨br, bc⟩
    have har : ar = i := (Finset.mem_filter.mp ha).2
    have hbr : br = i := (Finset.mem_filter.mp hb).2
    have hbc : ac = bc := hab
    exact Prod.ext (by rw [har, hbr]) hbc
  have himage :
      (S.filter fun e : MatrixEdge => e.1 = i).image f =
        rowNeighbors S i := by
    ext j
    constructor
    · rintro hj
      rcases Finset.mem_image.mp hj with ⟨e, he, rfl⟩
      rcases e with ⟨r, c⟩
      have heS : (r, c) ∈ S := (Finset.mem_filter.mp he).1
      have hri : r = i := (Finset.mem_filter.mp he).2
      simpa [rowNeighbors, hri] using heS
    · intro hj
      have hij : (i, j) ∈ S := by simpa using hj
      exact Finset.mem_image.mpr
        ⟨(i, j), by simp [hij], rfl⟩
  rw [← himage]
  exact (Finset.card_image_of_injOn hf).symm

theorem colFiber_card_eq_colNeighbors_card
    (S : Finset MatrixEdge) (j : Fin 4) :
    (S.filter fun e : MatrixEdge => e.2 = j).card =
      (colNeighbors S j).card := by
  let f : MatrixEdge → Fin 3 := fun e => e.1
  have hf : Set.InjOn f (S.filter fun e : MatrixEdge => e.2 = j) := by
    intro a ha b hb hab
    rcases a with ⟨ar, ac⟩
    rcases b with ⟨br, bc⟩
    have hac : ac = j := (Finset.mem_filter.mp ha).2
    have hbc : bc = j := (Finset.mem_filter.mp hb).2
    have hbr : ar = br := hab
    exact Prod.ext hbr (by rw [hac, hbc])
  have himage :
      (S.filter fun e : MatrixEdge => e.2 = j).image f =
        colNeighbors S j := by
    ext i
    constructor
    · rintro hi
      rcases Finset.mem_image.mp hi with ⟨e, he, rfl⟩
      rcases e with ⟨r, c⟩
      have heS : (r, c) ∈ S := (Finset.mem_filter.mp he).1
      have hcj : c = j := (Finset.mem_filter.mp he).2
      simpa [colNeighbors, hcj] using heS
    · intro hi
      have hij : (i, j) ∈ S := by simpa using hi
      exact Finset.mem_image.mpr
        ⟨(i, j), by simp [hij], rfl⟩
  rw [← himage]
  exact (Finset.card_image_of_injOn hf).symm

theorem card_eq_sum_rowNeighbors_card (S : Finset MatrixEdge) :
    S.card = ∑ i : Fin 3, (rowNeighbors S i).card := by
  classical
  have hmaps :
      (S : Set MatrixEdge).MapsTo (fun e : MatrixEdge => e.1)
        ((Finset.univ : Finset (Fin 3)) : Set (Fin 3)) := by
    intro e he
    simp
  have h :=
    Finset.card_eq_sum_card_fiberwise
      (s := S) (t := (Finset.univ : Finset (Fin 3)))
      (f := fun e : MatrixEdge => e.1) hmaps
  simpa [rowFiber_card_eq_rowNeighbors_card] using h

theorem card_eq_sum_colNeighbors_card (S : Finset MatrixEdge) :
    S.card = ∑ j : Fin 4, (colNeighbors S j).card := by
  classical
  have hmaps :
      (S : Set MatrixEdge).MapsTo (fun e : MatrixEdge => e.2)
        ((Finset.univ : Finset (Fin 4)) : Set (Fin 4)) := by
    intro e he
    simp
  have h :=
    Finset.card_eq_sum_card_fiberwise
      (s := S) (t := (Finset.univ : Finset (Fin 4)))
      (f := fun e : MatrixEdge => e.2) hmaps
  simpa [colFiber_card_eq_colNeighbors_card] using h

theorem exists_one_lt_rowNeighbors_card_of_three_lt_card
    {S : Finset MatrixEdge} (hcard : 3 < S.card) :
    ∃ i : Fin 3, 1 < (rowNeighbors S i).card := by
  by_contra h
  have hle : ∀ i : Fin 3, (rowNeighbors S i).card ≤ 1 := by
    intro i
    exact Nat.le_of_not_gt (by
      intro hi
      exact h ⟨i, hi⟩)
  have hsum := card_eq_sum_rowNeighbors_card S
  rw [Fin.sum_univ_three] at hsum
  have h0 := hle 0
  have h1 := hle 1
  have h2 := hle 2
  omega

theorem exists_one_lt_colNeighbors_card_of_four_lt_card
    {S : Finset MatrixEdge} (hcard : 4 < S.card) :
    ∃ j : Fin 4, 1 < (colNeighbors S j).card := by
  by_contra h
  have hle : ∀ j : Fin 4, (colNeighbors S j).card ≤ 1 := by
    intro j
    exact Nat.le_of_not_gt (by
      intro hj
      exact h ⟨j, hj⟩)
  have hsum := card_eq_sum_colNeighbors_card S
  rw [Fin.sum_univ_four] at hsum
  have h0 := hle 0
  have h1 := hle 1
  have h2 := hle 2
  have h3 := hle 3
  omega

@[simp] theorem supportAdj_symm
    (S : Finset MatrixEdge) (v w : MatrixVertex) :
    SupportAdj S v w ↔ SupportAdj S w v := by
  unfold SupportAdj
  constructor
  · rintro ⟨hvw, e, he, hv, hw⟩
    exact ⟨hvw.symm, e, he, hw, hv⟩
  · rintro ⟨hwv, e, he, hw, hv⟩
    exact ⟨hwv.symm, e, he, hv, hw⟩

@[simp] theorem supportAdj_row_col_iff
    (S : Finset MatrixEdge) (i : Fin 3) (j : Fin 4) :
    SupportAdj S (MatrixVertex.row i) (MatrixVertex.col j) ↔
      (i, j) ∈ S := by
  constructor
  · rintro ⟨_hne, e, he, hi, hj⟩
    rcases e with ⟨r, c⟩
    simp [MatrixEdge.Incident, MatrixEdge.rowVertex,
      MatrixEdge.colVertex] at hi hj
    subst r
    subst c
    exact he
  · intro he
    refine ⟨by simp, ⟨(i, j), he, ?_, ?_⟩⟩
    · simp [MatrixEdge.Incident, MatrixEdge.rowVertex,
        MatrixEdge.colVertex]
    · simp [MatrixEdge.Incident, MatrixEdge.rowVertex,
        MatrixEdge.colVertex]

@[simp] theorem supportAdj_col_row_iff
    (S : Finset MatrixEdge) (j : Fin 4) (i : Fin 3) :
    SupportAdj S (MatrixVertex.col j) (MatrixVertex.row i) ↔
      (i, j) ∈ S := by
  rw [supportAdj_symm, supportAdj_row_col_iff]

@[simp] theorem supportAdj_row_row_iff
    (S : Finset MatrixEdge) (i k : Fin 3) :
    SupportAdj S (MatrixVertex.row i) (MatrixVertex.row k) ↔ False := by
  constructor
  · rintro ⟨hne, e, _he, hi, hk⟩
    rcases e with ⟨r, c⟩
    simp [MatrixEdge.Incident, MatrixEdge.rowVertex,
      MatrixEdge.colVertex] at hi hk
    subst i
    subst k
    exact hne rfl
  · intro h
    cases h

@[simp] theorem supportAdj_col_col_iff
    (S : Finset MatrixEdge) (j l : Fin 4) :
    SupportAdj S (MatrixVertex.col j) (MatrixVertex.col l) ↔ False := by
  constructor
  · rintro ⟨hne, e, _he, hj, hl⟩
    rcases e with ⟨r, c⟩
    simp [MatrixEdge.Incident, MatrixEdge.rowVertex,
      MatrixEdge.colVertex] at hj hl
    subst j
    subst l
    exact hne rfl
  · intro h
    cases h

/-- A simple path of length three in a support graph. -/
def HasSupportPath3 (S : Finset MatrixEdge) : Prop :=
  ∃ v0 v1 v2 v3 : MatrixVertex,
    v0 ≠ v1 ∧ v0 ≠ v2 ∧ v0 ≠ v3 ∧
    v1 ≠ v2 ∧ v1 ≠ v3 ∧ v2 ≠ v3 ∧
    SupportAdj S v0 v1 ∧ SupportAdj S v1 v2 ∧ SupportAdj S v2 v3

instance (S : Finset MatrixEdge) : Decidable (HasSupportPath3 S) := by
  unfold HasSupportPath3
  infer_instance

/-- A length-three support path is exactly a raw double-star core after
choosing the middle row/column of the path. -/
theorem exists_doubleStarCore_edges_of_hasSupportPath3
    {S : Finset MatrixEdge} (h : HasSupportPath3 S) :
    ∃ i0 i1 : Fin 3, ∃ j0 j1 : Fin 4,
      i0 ≠ i1 ∧ j0 ≠ j1 ∧
        (i0, j0) ∈ S ∧ (i0, j1) ∈ S ∧ (i1, j0) ∈ S := by
  rcases h with ⟨v0, v1, v2, v3, hne01, hne02, hne03,
    hne12, hne13, hne23, hadj01, hadj12, hadj23⟩
  rcases v0 with r0 | c0
  · rcases v1 with r1 | c1
    · exfalso
      simp at hadj01
    · rcases v2 with r2 | c2
      · rcases v3 with r3 | c3
        · exfalso
          simp at hadj23
        · refine ⟨r2, r0, c1, c3, ?_, ?_, ?_, ?_, ?_⟩
          · intro h
            exact hne02 (by simp [h])
          · intro h
            exact hne13 (by simp [h])
          · simpa using hadj12
          · simpa using hadj23
          · simpa using hadj01
      · exfalso
        simp at hadj12
  · rcases v1 with r1 | c1
    · rcases v2 with r2 | c2
      · exfalso
        simp at hadj12
      · rcases v3 with r3 | c3
        · refine ⟨r1, r3, c2, c0, ?_, ?_, ?_, ?_, ?_⟩
          · intro h
            exact hne13 (by simp [h])
          · intro h
            exact hne02 (by simp [h])
          · simpa using hadj12
          · simpa using hadj01
          · simpa using hadj23
        · exfalso
          simp at hadj23
    · exfalso
      simp at hadj01

/-- An edge with degree at least two at both endpoints immediately gives a
simple support path of length three. -/
theorem hasSupportPath3_of_edge_one_lt_degrees
    {S : Finset MatrixEdge} {i : Fin 3} {j : Fin 4}
    (hij : (i, j) ∈ S)
    (hrow : 1 < (rowNeighbors S i).card)
    (hcol : 1 < (colNeighbors S j).card) :
    HasSupportPath3 S := by
  rcases Finset.one_lt_card.mp hrow with ⟨a, ha, b, hb, hab⟩
  obtain ⟨j', hj', hj'ne⟩ :
      ∃ j' ∈ rowNeighbors S i, j' ≠ j := by
    by_cases haj : a = j
    · exact ⟨b, hb, by
        intro hbj
        exact hab (haj.trans hbj.symm)⟩
    · exact ⟨a, ha, haj⟩
  rcases Finset.one_lt_card.mp hcol with ⟨a, ha, b, hb, hab⟩
  obtain ⟨i', hi', hi'ne⟩ :
      ∃ i' ∈ colNeighbors S j, i' ≠ i := by
    by_cases hai : a = i
    · exact ⟨b, hb, by
        intro hbi
        exact hab (hai.trans hbi.symm)⟩
    · exact ⟨a, ha, hai⟩
  refine ⟨MatrixVertex.col j', MatrixVertex.row i,
    MatrixVertex.col j, MatrixVertex.row i', ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · simp
  · simpa using hj'ne
  · simp
  · simp
  · intro h
    exact hi'ne (by simpa using h.symm)
  · simp
  · simpa using hj'
  · simpa using hij
  · simpa using hi'

/-- Computational star-forest predicate for these bipartite supports.  For a
simple graph, having no simple path of length three is equivalent to every
component being a star or an isolated vertex. -/
def IsSupportStarForest (S : Finset MatrixEdge) : Prop :=
  ¬ HasSupportPath3 S

instance (S : Finset MatrixEdge) : Decidable (IsSupportStarForest S) := by
  unfold IsSupportStarForest
  infer_instance

/-- In a star-forest support, every present edge has a degree-one endpoint. -/
theorem rowNeighbors_card_le_one_or_colNeighbors_card_le_one_of_starForest
    {S : Finset MatrixEdge} (hstar : IsSupportStarForest S)
    {i : Fin 3} {j : Fin 4} (hij : (i, j) ∈ S) :
    (rowNeighbors S i).card ≤ 1 ∨ (colNeighbors S j).card ≤ 1 := by
  by_contra h
  have hrow_not : ¬ (rowNeighbors S i).card ≤ 1 := fun hrow =>
    h (Or.inl hrow)
  have hcol_not : ¬ (colNeighbors S j).card ≤ 1 := fun hcol =>
    h (Or.inr hcol)
  exact hstar (hasSupportPath3_of_edge_one_lt_degrees hij
    (Nat.lt_of_not_ge hrow_not) (Nat.lt_of_not_ge hcol_not))

theorem not_mem_of_one_lt_row_col_neighbors_of_starForest
    {S : Finset MatrixEdge} (hstar : IsSupportStarForest S)
    {i : Fin 3} {j : Fin 4}
    (hrow : 1 < (rowNeighbors S i).card)
    (hcol : 1 < (colNeighbors S j).card) :
    (i, j) ∉ S := by
  intro hij
  exact hstar (hasSupportPath3_of_edge_one_lt_degrees hij hrow hcol)

/-- A non-star support contains a raw double-star core. -/
theorem exists_doubleStarCore_edges_of_not_star
    {S : Finset MatrixEdge} (h : ¬ IsSupportStarForest S) :
    ∃ i0 i1 : Fin 3, ∃ j0 j1 : Fin 4,
      i0 ≠ i1 ∧ j0 ≠ j1 ∧
        (i0, j0) ∈ S ∧ (i0, j1) ∈ S ∧ (i1, j0) ∈ S := by
  apply exists_doubleStarCore_edges_of_hasSupportPath3
  by_contra hpath
  exact h hpath

/-- The number of low-degree rows, expressed as a complement count. -/
theorem lowRows_card_eq (S : Finset MatrixEdge) :
    ((Finset.univ : Finset (Fin 3)).filter fun i => i ∉ highRows S).card =
      3 - (highRows S).card := by
  classical
  have hfilter :
      ((Finset.univ : Finset (Fin 3)).filter fun i => i ∈ highRows S) =
        highRows S := by
    ext i
    simp
  have h :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin 3)))
      (p := fun i => i ∈ highRows S)
  rw [hfilter] at h
  simp only [Finset.card_univ, Fintype.card_fin] at h
  omega

/-- The number of low-degree columns, expressed as a complement count. -/
theorem lowCols_card_eq (S : Finset MatrixEdge) :
    ((Finset.univ : Finset (Fin 4)).filter fun j => j ∉ highCols S).card =
      4 - (highCols S).card := by
  classical
  have hfilter :
      ((Finset.univ : Finset (Fin 4)).filter fun j => j ∈ highCols S) =
        highCols S := by
    ext j
    simp
  have h :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin 4)))
      (p := fun j => j ∈ highCols S)
  rw [hfilter] at h
  simp only [Finset.card_univ, Fintype.card_fin] at h
  omega

theorem highRows_card_le_three (S : Finset MatrixEdge) :
    (highRows S).card ≤ 3 := by
  have h :=
    Finset.card_filter_le
      (s := (Finset.univ : Finset (Fin 3)))
      (p := fun i => 1 < (rowNeighbors S i).card)
  simpa [highRows, Fintype.card_fin] using h

theorem highCols_card_le_four (S : Finset MatrixEdge) :
    (highCols S).card ≤ 4 := by
  have h :=
    Finset.card_filter_le
      (s := (Finset.univ : Finset (Fin 4)))
      (p := fun j => 1 < (colNeighbors S j).card)
  simpa [highCols, Fintype.card_fin] using h

theorem rowNeighbors_card_le_lowCols_card_of_highRow_starForest
    {S : Finset MatrixEdge} (hstar : IsSupportStarForest S)
    {i : Fin 3} (hi : i ∈ highRows S) :
    (rowNeighbors S i).card ≤
      ((Finset.univ : Finset (Fin 4)).filter fun j => j ∉ highCols S).card := by
  refine Finset.card_le_card ?_
  intro j hj
  have hrow : 1 < (rowNeighbors S i).card := by
    simpa using hi
  have hij : (i, j) ∈ S := by
    simpa using hj
  have hjlow : j ∉ highCols S := by
    intro hjhigh
    have hcol : 1 < (colNeighbors S j).card := by
      simpa using hjhigh
    exact not_mem_of_one_lt_row_col_neighbors_of_starForest
      hstar hrow hcol hij
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjlow⟩

theorem colNeighbors_card_le_lowRows_card_of_highCol_starForest
    {S : Finset MatrixEdge} (hstar : IsSupportStarForest S)
    {j : Fin 4} (hj : j ∈ highCols S) :
    (colNeighbors S j).card ≤
      ((Finset.univ : Finset (Fin 3)).filter fun i => i ∉ highRows S).card := by
  refine Finset.card_le_card ?_
  intro i hi
  have hcol : 1 < (colNeighbors S j).card := by
    simpa using hj
  have hij : (i, j) ∈ S := by
    simpa using hi
  have hilow : i ∉ highRows S := by
    intro hihigh
    have hrow : 1 < (rowNeighbors S i).card := by
      simpa using hihigh
    exact not_mem_of_one_lt_row_col_neighbors_of_starForest
      hstar hrow hcol hij
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hilow⟩

theorem card_le_row_high_bound_of_starForest
    {S : Finset MatrixEdge} (hstar : IsSupportStarForest S) :
    S.card ≤
      (highRows S).card * (4 - (highCols S).card) +
        (3 - (highRows S).card) := by
  have hsum_le :
      (∑ i : Fin 3, (rowNeighbors S i).card) ≤
        ∑ i : Fin 3,
          if i ∈ highRows S then 4 - (highCols S).card else 1 := by
    refine Finset.sum_le_sum ?_
    intro i _hi
    by_cases hi : i ∈ highRows S
    · have hle :=
        rowNeighbors_card_le_lowCols_card_of_highRow_starForest
          hstar hi
      rw [lowCols_card_eq] at hle
      simpa [hi] using hle
    · have hle : (rowNeighbors S i).card ≤ 1 := by
        exact Nat.le_of_not_gt fun h =>
          hi ((mem_highRows_iff S i).2 h)
      simpa [hi] using hle
  have hsum_eq :
      (∑ i : Fin 3,
          if i ∈ highRows S then 4 - (highCols S).card else 1) =
        (highRows S).card * (4 - (highCols S).card) +
          (3 - (highRows S).card) := by
    simpa [Fintype.card_fin] using
      (sum_if_mem_finset_eq_card_mul_add_compl
        (T := highRows S) (c := 4 - (highCols S).card))
  calc
    S.card = ∑ i : Fin 3, (rowNeighbors S i).card :=
      card_eq_sum_rowNeighbors_card S
    _ ≤ ∑ i : Fin 3,
          if i ∈ highRows S then 4 - (highCols S).card else 1 :=
      hsum_le
    _ = (highRows S).card * (4 - (highCols S).card) +
          (3 - (highRows S).card) :=
      hsum_eq

theorem card_le_col_high_bound_of_starForest
    {S : Finset MatrixEdge} (hstar : IsSupportStarForest S) :
    S.card ≤
      (highCols S).card * (3 - (highRows S).card) +
        (4 - (highCols S).card) := by
  have hsum_le :
      (∑ j : Fin 4, (colNeighbors S j).card) ≤
        ∑ j : Fin 4,
          if j ∈ highCols S then 3 - (highRows S).card else 1 := by
    refine Finset.sum_le_sum ?_
    intro j _hj
    by_cases hj : j ∈ highCols S
    · have hle :=
        colNeighbors_card_le_lowRows_card_of_highCol_starForest
          hstar hj
      rw [lowRows_card_eq] at hle
      simpa [hj] using hle
    · have hle : (colNeighbors S j).card ≤ 1 := by
        exact Nat.le_of_not_gt fun h =>
          hj ((mem_highCols_iff S j).2 h)
      simpa [hj] using hle
  have hsum_eq :
      (∑ j : Fin 4,
          if j ∈ highCols S then 3 - (highRows S).card else 1) =
        (highCols S).card * (3 - (highRows S).card) +
          (4 - (highCols S).card) := by
    simpa [Fintype.card_fin] using
      (sum_if_mem_finset_eq_card_mul_add_compl
        (T := highCols S) (c := 3 - (highRows S).card))
  calc
    S.card = ∑ j : Fin 4, (colNeighbors S j).card :=
      card_eq_sum_colNeighbors_card S
    _ ≤ ∑ j : Fin 4,
          if j ∈ highCols S then 3 - (highRows S).card else 1 :=
      hsum_le
    _ = (highCols S).card * (3 - (highRows S).card) +
          (4 - (highCols S).card) :=
      hsum_eq

/-- The support of the zero matrix is a star forest. -/
theorem isSupportStarForest_empty :
    IsSupportStarForest (∅ : Finset MatrixEdge) := by
  intro h
  rcases h with ⟨v0, v1, v2, v3, hne01, hne02, hne03,
    hne12, hne13, hne23, hadj01, hadj12, hadj23⟩
  rcases hadj01.2 with ⟨e, he, _⟩
  simp at he

/-- A finite `K_{3,4}` support whose components are stars has at most five
edges. -/
theorem support_card_le_five_of_starForest :
    ∀ S : Finset MatrixEdge, IsSupportStarForest S → S.card ≤ 5 := by
  intro S hstar
  by_contra hle
  have hcard : 5 < S.card := Nat.lt_of_not_ge hle
  have hrow_exists :
      ∃ i : Fin 3, 1 < (rowNeighbors S i).card :=
    exists_one_lt_rowNeighbors_card_of_three_lt_card (by omega)
  have hcol_exists :
      ∃ j : Fin 4, 1 < (colNeighbors S j).card :=
    exists_one_lt_colNeighbors_card_of_four_lt_card (by omega)
  let a := (highRows S).card
  let b := (highCols S).card
  have ha_pos : 0 < a := by
    rcases hrow_exists with ⟨i, hi⟩
    exact Finset.card_pos.mpr ⟨i, by simpa [a] using hi⟩
  have hb_pos : 0 < b := by
    rcases hcol_exists with ⟨j, hj⟩
    exact Finset.card_pos.mpr ⟨j, by simpa [b] using hj⟩
  have ha_le : a ≤ 3 := by
    simpa [a] using highRows_card_le_three S
  have hb_le : b ≤ 4 := by
    simpa [b] using highCols_card_le_four S
  have hrow_bound : S.card ≤ a * (4 - b) + (3 - a) := by
    simpa [a, b] using card_le_row_high_bound_of_starForest
      (S := S) hstar
  have hcol_bound : S.card ≤ b * (3 - a) + (4 - b) := by
    simpa [a, b] using card_le_col_high_bound_of_starForest
      (S := S) hstar
  have hsmall :
      a * (4 - b) + (3 - a) ≤ 5 ∨
        b * (3 - a) + (4 - b) ≤ 5 := by
    interval_cases a <;> interval_cases b <;> omega
  rcases hsmall with hsmall | hsmall
  · have : S.card ≤ 5 := le_trans hrow_bound hsmall
    omega
  · have : S.card ≤ 5 := le_trans hcol_bound hsmall
    omega

/-- Star-forest supports of natural matrices have at most five positive
entries. -/
theorem supportCardNat_le_five_of_starForest
    (U : NatMatrix)
    (hstar : IsSupportStarForest (supportOfNat U)) :
    supportCardNat U ≤ 5 := by
  exact support_card_le_five_of_starForest (supportOfNat U) hstar

/-- A simple path of length four in a support graph.  This is the graph
configuration used by the four-edge path compression. -/
def HasSupportPath4 (S : Finset MatrixEdge) : Prop :=
  ∃ v0 v1 v2 v3 v4 : MatrixVertex,
    v0 ≠ v1 ∧ v0 ≠ v2 ∧ v0 ≠ v3 ∧ v0 ≠ v4 ∧
    v1 ≠ v2 ∧ v1 ≠ v3 ∧ v1 ≠ v4 ∧
    v2 ≠ v3 ∧ v2 ≠ v4 ∧ v3 ≠ v4 ∧
    SupportAdj S v0 v1 ∧ SupportAdj S v1 v2 ∧
    SupportAdj S v2 v3 ∧ SupportAdj S v3 v4

instance (S : Finset MatrixEdge) : Decidable (HasSupportPath4 S) := by
  unfold HasSupportPath4
  infer_instance

/-- A four-cycle in a support graph.  Four-cycles use the concave cycle
compression directly; longer cycles contain a simple four-edge path. -/
def HasSupportCycle4 (S : Finset MatrixEdge) : Prop :=
  ∃ v0 v1 v2 v3 : MatrixVertex,
    v0 ≠ v1 ∧ v0 ≠ v2 ∧ v0 ≠ v3 ∧
    v1 ≠ v2 ∧ v1 ≠ v3 ∧ v2 ≠ v3 ∧
    SupportAdj S v0 v1 ∧ SupportAdj S v1 v2 ∧
    SupportAdj S v2 v3 ∧ SupportAdj S v3 v0

instance (S : Finset MatrixEdge) : Decidable (HasSupportCycle4 S) := by
  unfold HasSupportCycle4
  infer_instance

end Lollipop
