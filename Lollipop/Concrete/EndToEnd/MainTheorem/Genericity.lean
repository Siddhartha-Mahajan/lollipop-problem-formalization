import Lollipop.Concrete.EndToEnd.Lower.Genericity

/-!
# Main theorem spine: lower genericity

This file states the concrete genericity-avoidance theorem needed by the final
certificate-free endpoint.

The theorem is not a caller-facing certificate.  It is the named target for
the finite bad-locus avoidance proof.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace MainTheorem
namespace Genericity

/-- There are no three pairwise-distinct indices in `Fin n` when `n < 3`. -/
theorem no_three_distinct_fin_of_lt_three {n : ℕ} (hn : n < 3) :
    ∀ i j k : Fin n, i ≠ j → i ≠ k → j ≠ k → False := by
  intro i j k hij hik hjk
  have hijv : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
  have hikv : i.1 ≠ k.1 := fun h => hik (Fin.ext h)
  have hjkv : j.1 ≠ k.1 := fun h => hjk (Fin.ext h)
  have hi3 : i.1 < 3 := lt_trans i.2 hn
  have hj3 : j.1 < 3 := lt_trans j.2 hn
  have hk3 : k.1 < 3 := lt_trans k.2 hn
  omega

/-- For `n < 3`, the triple-contact bad locus is empty and hence avoidable. -/
theorem dense_compl_tripleBadUnion_of_lt_three {n : ℕ} (hn : n < 3) :
    Dense
      ((Lower.GenericityPort.tripleBadUnion :
        Set (Lower.ArrangementParameter n))ᶜ) := by
  rw [Lower.GenericityPort.tripleBadUnion_eq_empty_of_no_three_distinct
    (no_three_distinct_fin_of_lt_three hn)]
  simp

/-- Ordered triples of pairwise-distinct indices.  This packages the index
and proof arguments in `Lower.GenericityPort.tripleBadUnion` into one finite
type, so the remaining density theorem can be reduced to finitely many fixed
triple-incidence loci. -/
abbrev OrderedTripleIndex (n : ℕ) :=
  {ijk : Fin n × Fin n × Fin n //
    ijk.1 ≠ ijk.2.1 ∧ ijk.1 ≠ ijk.2.2 ∧ ijk.2.1 ≠ ijk.2.2}

/-- The good locus for one ordered triple of pairwise-distinct indices. -/
def orderedTripleGood {n : ℕ} (t : OrderedTripleIndex n) :
    Set (Lower.ArrangementParameter n) :=
  (Lower.GenericityPort.tripleBadSet
    t.1.1 t.1.2.1 t.1.2.2 t.2.1 t.2.2.1 t.2.2.2)ᶜ

/-- The complement of the triple bad union is exactly the finite intersection
of the fixed ordered-triple good loci. -/
theorem compl_tripleBadUnion_eq_iInter_orderedTripleGood {n : ℕ} :
    ((Lower.GenericityPort.tripleBadUnion :
        Set (Lower.ArrangementParameter n))ᶜ) =
      ⋂ t : OrderedTripleIndex n, orderedTripleGood t := by
  ext p
  constructor
  · intro hp
    rw [Set.mem_iInter]
    intro t
    change p ∉
      Lower.GenericityPort.tripleBadSet
        t.1.1 t.1.2.1 t.1.2.2 t.2.1 t.2.2.1 t.2.2.2
    intro hbad
    apply hp
    unfold Lower.GenericityPort.tripleBadUnion
    exact Set.mem_iUnion.mpr ⟨t.1.1,
      Set.mem_iUnion.mpr ⟨t.1.2.1,
        Set.mem_iUnion.mpr ⟨t.1.2.2,
          Set.mem_iUnion.mpr ⟨t.2.1,
            Set.mem_iUnion.mpr ⟨t.2.2.1,
              Set.mem_iUnion.mpr ⟨t.2.2.2, hbad⟩⟩⟩⟩⟩⟩
  · intro hp hbad
    unfold Lower.GenericityPort.tripleBadUnion at hbad
    rcases Set.mem_iUnion.mp hbad with ⟨i, hbad⟩
    rcases Set.mem_iUnion.mp hbad with ⟨j, hbad⟩
    rcases Set.mem_iUnion.mp hbad with ⟨k, hbad⟩
    rcases Set.mem_iUnion.mp hbad with ⟨hij, hbad⟩
    rcases Set.mem_iUnion.mp hbad with ⟨hik, hbad⟩
    rcases Set.mem_iUnion.mp hbad with ⟨hjk, hbad⟩
    let t : OrderedTripleIndex n := ⟨(i, j, k), ⟨hij, hik, hjk⟩⟩
    have hgood : p ∈ orderedTripleGood t := Set.mem_iInter.mp hp t
    change p ∉ Lower.GenericityPort.tripleBadSet i j k hij hik hjk at hgood
    exact hgood hbad

/-- Finite-index reduction for the triple-contact density theorem.  It is
enough to prove that every fixed ordered-triple good locus is open dense. -/
theorem dense_compl_tripleBadUnion_of_orderedTriple_open_dense {n : ℕ}
    (hopen : ∀ t : OrderedTripleIndex n, IsOpen (orderedTripleGood t))
    (hdense : ∀ t : OrderedTripleIndex n, Dense (orderedTripleGood t)) :
    Dense
      ((Lower.GenericityPort.tripleBadUnion :
        Set (Lower.ArrangementParameter n))ᶜ) := by
  classical
  have hfinite :
      Dense (⋂ t : OrderedTripleIndex n, orderedTripleGood t) :=
    Lower.GenericityPort.dense_iInter_fintype_of_open_dense
      (orderedTripleGood (n := n)) hopen hdense
  rwa [compl_tripleBadUnion_eq_iInter_orderedTripleGood]

/-- Remaining triple-contact avoidance theorem for the only nontrivial range
`3 ≤ n`. -/
theorem dense_compl_tripleBadUnion_ge_three (n : ℕ) (hn : 3 ≤ n) :
    Dense
      ((Lower.GenericityPort.tripleBadUnion :
        Set (Lower.ArrangementParameter n))ᶜ) := by
  sorry

/-- The complement of the triple-contact bad locus is dense in every finite
arrangement parameter space.

This is the remaining concrete finite-avoidance fact needed for the lower
genericization argument.  The nonparallel-stem complement is already proved
open dense in `Lower.GenericityPort.dense_compl_parallelBadUnion`. -/
theorem dense_compl_tripleBadUnion (n : ℕ) :
    Dense
      ((Lower.GenericityPort.tripleBadUnion :
        Set (Lower.ArrangementParameter n))ᶜ) := by
  by_cases hn : n < 3
  · exact dense_compl_tripleBadUnion_of_lt_three hn
  · exact dense_compl_tripleBadUnion_ge_three n (by omega)

/-- The reduced chamber-bad locus is avoidable.

This combines the remaining triple-contact density target with the existing
open dense nonparallel-stem theorem. -/
theorem dense_compl_chamberBadUnion (n : ℕ) :
    Dense
      ((Lower.GenericityPort.chamberBadUnion :
        Set (Lower.ArrangementParameter n))ᶜ) := by
  have hparallelDense :
      Dense
        ((Lower.GenericityPort.parallelBadUnion :
          Set (Lower.ArrangementParameter n))ᶜ) :=
    Lower.GenericityPort.dense_compl_parallelBadUnion
  have hparallelOpen :
      IsOpen
        ((Lower.GenericityPort.parallelBadUnion :
          Set (Lower.ArrangementParameter n))ᶜ) :=
    Lower.GenericityPort.isOpen_compl_parallelBadUnion
  have htp :
      Dense
        (((Lower.GenericityPort.parallelBadUnion :
            Set (Lower.ArrangementParameter n))ᶜ) ∩
          ((Lower.GenericityPort.tripleBadUnion :
            Set (Lower.ArrangementParameter n))ᶜ)) :=
    hparallelDense.inter_of_isOpen_left
      (dense_compl_tripleBadUnion n) hparallelOpen
  simpa [Lower.GenericityPort.chamberBadUnion, Set.compl_union,
    Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using htp

/-- Every finite strict pair chamber contains a generic arrangement.

This is the all-`n` concrete finite-avoidance theorem needed by the lower
construction after topology supplies the generic Euler equality. -/
theorem chamberGenericityAvoidance_all :
    ∀ n : ℕ, Lower.GenericityPort.ChamberGenericityAvoidance n := by
  intro n
  exact { dense_good := dense_compl_chamberBadUnion n }

theorem chamberGenericityAvoidance (n : ℕ) :
    Lower.GenericityPort.ChamberGenericityAvoidance n :=
  chamberGenericityAvoidance_all n

end Genericity
end MainTheorem
end EndToEnd
end Concrete
end Lollipop
