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

@[simp] theorem mem_rowNeighbors_iff
    (S : Finset MatrixEdge) (i : Fin 3) (j : Fin 4) :
    j ∈ rowNeighbors S i ↔ (i, j) ∈ S := by
  simp [rowNeighbors]

@[simp] theorem mem_colNeighbors_iff
    (S : Finset MatrixEdge) (i : Fin 3) (j : Fin 4) :
    i ∈ colNeighbors S j ↔ (i, j) ∈ S := by
  simp [colNeighbors]

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

/-- A simple path of length three in a support graph. -/
def HasSupportPath3 (S : Finset MatrixEdge) : Prop :=
  ∃ v0 v1 v2 v3 : MatrixVertex,
    v0 ≠ v1 ∧ v0 ≠ v2 ∧ v0 ≠ v3 ∧
    v1 ≠ v2 ∧ v1 ≠ v3 ∧ v2 ≠ v3 ∧
    SupportAdj S v0 v1 ∧ SupportAdj S v1 v2 ∧ SupportAdj S v2 v3

instance (S : Finset MatrixEdge) : Decidable (HasSupportPath3 S) := by
  unfold HasSupportPath3
  infer_instance

/-- An edge with degree at least two at both endpoints immediately gives a
simple support path of length three. -/
theorem hasSupportPath3_of_edge_one_lt_degrees
    {S : Finset MatrixEdge} {i : Fin 3} {j : Fin 4}
    (hij : (i, j) ∈ S)
    (hrow : 1 < (rowNeighbors S i).card)
    (hcol : 1 < (colNeighbors S j).card) :
    HasSupportPath3 S := by
  have hj_mem : j ∈ rowNeighbors S i := by
    simpa using hij
  rcases Finset.one_lt_card.mp hrow with ⟨a, ha, b, hb, hab⟩
  obtain ⟨j', hj', hj'ne⟩ :
      ∃ j' ∈ rowNeighbors S i, j' ≠ j := by
    by_cases haj : a = j
    · exact ⟨b, hb, by
        intro hbj
        exact hab (haj.trans hbj.symm)⟩
    · exact ⟨a, ha, haj⟩
  have hi_mem : i ∈ colNeighbors S j := by
    simpa using hij
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

/-- The support of the zero matrix is a star forest. -/
theorem isSupportStarForest_empty :
    IsSupportStarForest (∅ : Finset MatrixEdge) := by
  intro h
  rcases h with ⟨v0, v1, v2, v3, hne01, hne02, hne03,
    hne12, hne13, hne23, hadj01, hadj12, hadj23⟩
  rcases hadj01.2 with ⟨e, he, _⟩
  simp at he

/-- A finite `K_{3,4}` support whose components are stars has at most five
edges.  This is a small exhaustive graph fact over the twelve possible matrix
cells. -/
theorem support_card_le_five_of_starForest :
    ∀ S : Finset MatrixEdge, IsSupportStarForest S → S.card ≤ 5 := by
  native_decide

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
