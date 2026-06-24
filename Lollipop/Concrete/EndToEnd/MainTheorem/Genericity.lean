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
