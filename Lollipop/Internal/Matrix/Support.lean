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

/-- A simple path of length three in a support graph. -/
def HasSupportPath3 (S : Finset MatrixEdge) : Prop :=
  ∃ v0 v1 v2 v3 : MatrixVertex,
    v0 ≠ v1 ∧ v0 ≠ v2 ∧ v0 ≠ v3 ∧
    v1 ≠ v2 ∧ v1 ≠ v3 ∧ v2 ≠ v3 ∧
    SupportAdj S v0 v1 ∧ SupportAdj S v1 v2 ∧ SupportAdj S v2 v3

instance (S : Finset MatrixEdge) : Decidable (HasSupportPath3 S) := by
  unfold HasSupportPath3
  infer_instance

/-- Computational star-forest predicate for these bipartite supports.  For a
simple graph, having no simple path of length three is equivalent to every
component being a star or an isolated vertex. -/
def IsSupportStarForest (S : Finset MatrixEdge) : Prop :=
  ¬ HasSupportPath3 S

instance (S : Finset MatrixEdge) : Decidable (IsSupportStarForest S) := by
  unfold IsSupportStarForest
  infer_instance

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
