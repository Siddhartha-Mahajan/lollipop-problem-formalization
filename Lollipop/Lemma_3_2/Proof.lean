import Lollipop.Lemma_3_1.Proof

/-!
This is the substantive proof compilation unit for `Lemma_3_2`.
All project proof components used below are integrated here or imported
directly from another manuscript-numbered `Proof.lean` file.
-/

/-!
The manuscript-facing proposition is repeated here as `CoreStatement` so
this proof module does not cyclically import its public statement module.
`Statement.lean` imports this file and exposes the same expression under the
public name `Statement`.
-/

/-!
Manuscript Lemma 3.2 (`lem:intr-mixed`): for an intersecting intriguing pair,
each outside mixed component has at most one point, and two such components
force the finite ray--ray intersection to be empty.
-/

namespace Lollipop.Manuscript.Lemma_3_2

open Concrete Concrete.EndToEnd

def CoreStatement : Prop :=
  forall (L M : Concrete.Lollipop),
    PairGeometry.normSqPoint (M.center - L.center) <=
      L.radius ^ 2 + M.radius ^ 2 ->
    (rc L M \ cc L M).ncard <= 1 /\
    (cr L M \ cc L M).ncard <= 1 /\
    (((rc L M \ cc L M).Nonempty /\ (cr L M \ cc L M).Nonempty) ->
      rr L M = ∅)

end Lollipop.Manuscript.Lemma_3_2

/-! The actual numbered proof. -/

namespace Lollipop.Manuscript.Lemma_3_2

open Concrete Concrete.EndToEnd Concrete.EndToEnd.PairGeometry

theorem proof : CoreStatement := by
  intro L M hnear
  refine ⟨rc_diff_cc_ncard_le_one_of_near hnear,
    cr_diff_cc_ncard_le_one_of_near hnear, ?_⟩
  rintro ⟨hleft, hright⟩
  exact rr_eq_empty_of_both_outside_mixed_of_near hnear hleft hright

end Lollipop.Manuscript.Lemma_3_2
