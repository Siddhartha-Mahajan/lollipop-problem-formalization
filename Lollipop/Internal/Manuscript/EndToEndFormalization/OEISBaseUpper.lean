import Lollipop.Internal.Manuscript.EndToEndFormalization.OEISBaseLower
import Lollipop.Internal.Manuscript.PrimitiveGeometry.CarrierSavings

/-!
Exact OEIS base upper table for the canonical all-ones relabeling.

The lower file proves that the automatic finite carriers contain the
Nat-valued Karlsson table for the canonical all-ones cluster witness.  This
file proves the matching upper side: the exceptional `0/1` base pair has the
concrete five-point direct-savings route, all other distinct base pairs have
the generic seven-point bound, and therefore the canonical automatic pair
table is exactly the Karlsson `5/7` table for the all-ones base.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace EndToEndFormalization
namespace OEISBaseUpper

open PrimitiveGeometry
open ExplicitInputs
open OEISBaseLower

noncomputable section

/-- The table predicate selecting the exceptional Karlsson `0/1` pair. -/
def zeroOneLabelPair (a b : Fin 4) : Prop :=
  ((a : Nat) = 0 ∧ (b : Nat) = 1) ∨
    ((a : Nat) = 1 ∧ (b : Nat) = 0)

/-- The concrete OEIS `(Q0,Q1)` route gives direct whole-carrier `<= 5`
savings. -/
noncomputable def base_zero_one_pairCarrierSavingsFive :
    PairCarrierSavings
      (karlssonOEISBaseArrangement.lollipop (0 : Fin 4))
      (karlssonOEISBaseArrangement.lollipop (1 : Fin 4)) 5 := by
  simpa using
    ExplicitInputs.karlssonOEISQ0_Q1_circleRayOutward_savings_route
      |>.toPairCarrierSavings

/-- The same concrete OEIS `0/1` savings in the reverse orientation. -/
noncomputable def base_one_zero_pairCarrierSavingsFive :
    PairCarrierSavings
      (karlssonOEISBaseArrangement.lollipop (1 : Fin 4))
      (karlssonOEISBaseArrangement.lollipop (0 : Fin 4)) 5 :=
  base_zero_one_pairCarrierSavingsFive.symm

/-- The exact OEIS base pair `(Q0,Q1)` is close. -/
theorem base_zero_one_cyclicClose :
    TheoremOneEndToEnd.CloseDirection.cyclicClose
      (fun k : Fin 4 => karlssonOEISBaseArrangement.normalizedDirection k)
      (0 : Fin 4) (1 : Fin 4) :=
  ExplicitInputs.karlssonOEISBase_zero_one_cyclicClose

/-- The exact OEIS base pair `(Q1,Q0)` is close by symmetry. -/
theorem base_one_zero_cyclicClose :
    TheoremOneEndToEnd.CloseDirection.cyclicClose
      (fun k : Fin 4 => karlssonOEISBaseArrangement.normalizedDirection k)
      (1 : Fin 4) (0 : Fin 4) :=
  (TheoremOneEndToEnd.CloseDirection.cyclicClose_symm
    (fun k : Fin 4 => karlssonOEISBaseArrangement.normalizedDirection k)
    (0 : Fin 4) (1 : Fin 4)).1 base_zero_one_cyclicClose

/-- The exact OEIS base pair `(Q0,Q1)` is not intriguing. -/
theorem base_zero_one_not_circleIntriguing :
    ¬ TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
      (fun k : Fin 4 => karlssonOEISBaseArrangement.center k)
      (fun k : Fin 4 => karlssonOEISBaseArrangement.radius k)
      (0 : Fin 4) (1 : Fin 4) :=
  ExplicitInputs.karlssonOEISBase_zero_one_not_circleIntriguing

/-- The exact OEIS base pair `(Q1,Q0)` is not intriguing by symmetry. -/
theorem base_one_zero_not_circleIntriguing :
    ¬ TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
      (fun k : Fin 4 => karlssonOEISBaseArrangement.center k)
      (fun k : Fin 4 => karlssonOEISBaseArrangement.radius k)
      (1 : Fin 4) (0 : Fin 4) := by
  intro h
  exact base_zero_one_not_circleIntriguing
    ((TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing_symm
      (fun k : Fin 4 => karlssonOEISBaseArrangement.center k)
      (fun k : Fin 4 => karlssonOEISBaseArrangement.radius k)
      (0 : Fin 4) (1 : Fin 4)).2 h)

/-- The exact OEIS base pair `(Q0,Q2)` is not intriguing. -/
theorem base_zero_two_not_circleIntriguing :
    ¬ TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
      (fun k : Fin 4 => karlssonOEISBaseArrangement.center k)
      (fun k : Fin 4 => karlssonOEISBaseArrangement.radius k)
      (0 : Fin 4) (2 : Fin 4) := by
  simpa [TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing,
    EuclideanLollipopArrangement.center, EuclideanLollipopArrangement.radius,
    karlssonOEISBaseArrangement] using
    CompleteFormalization.OEISPair02.q0q2_not_circleIntriguingPair

/-- The exact OEIS base pair `(Q2,Q0)` is not intriguing by symmetry. -/
theorem base_two_zero_not_circleIntriguing :
    ¬ TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
      (fun k : Fin 4 => karlssonOEISBaseArrangement.center k)
      (fun k : Fin 4 => karlssonOEISBaseArrangement.radius k)
      (2 : Fin 4) (0 : Fin 4) := by
  intro h
  exact base_zero_two_not_circleIntriguing
    ((TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing_symm
      (fun k : Fin 4 => karlssonOEISBaseArrangement.center k)
      (fun k : Fin 4 => karlssonOEISBaseArrangement.radius k)
      (0 : Fin 4) (2 : Fin 4)).2 h)

/-- The exact OEIS base pair `(Q0,Q3)` is not intriguing. -/
theorem base_zero_three_not_circleIntriguing :
    ¬ TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
      (fun k : Fin 4 => karlssonOEISBaseArrangement.center k)
      (fun k : Fin 4 => karlssonOEISBaseArrangement.radius k)
      (0 : Fin 4) (3 : Fin 4) := by
  simpa [TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing,
    EuclideanLollipopArrangement.center, EuclideanLollipopArrangement.radius,
    karlssonOEISBaseArrangement] using
    CompleteFormalization.OEISPair03.q0q3_not_circleIntriguingPair

/-- The exact OEIS base pair `(Q3,Q0)` is not intriguing by symmetry. -/
theorem base_three_zero_not_circleIntriguing :
    ¬ TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
      (fun k : Fin 4 => karlssonOEISBaseArrangement.center k)
      (fun k : Fin 4 => karlssonOEISBaseArrangement.radius k)
      (3 : Fin 4) (0 : Fin 4) := by
  intro h
  exact base_zero_three_not_circleIntriguing
    ((TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing_symm
      (fun k : Fin 4 => karlssonOEISBaseArrangement.center k)
      (fun k : Fin 4 => karlssonOEISBaseArrangement.radius k)
      (0 : Fin 4) (3 : Fin 4)).2 h)

/-- The exact OEIS base pair `(Q1,Q2)` is not intriguing. -/
theorem base_one_two_not_circleIntriguing :
    ¬ TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
      (fun k : Fin 4 => karlssonOEISBaseArrangement.center k)
      (fun k : Fin 4 => karlssonOEISBaseArrangement.radius k)
      (1 : Fin 4) (2 : Fin 4) := by
  simpa [TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing,
    EuclideanLollipopArrangement.center, EuclideanLollipopArrangement.radius,
    karlssonOEISBaseArrangement] using
    CompleteFormalization.OEISPair12.q1q2_not_circleIntriguingPair

/-- The exact OEIS base pair `(Q2,Q1)` is not intriguing by symmetry. -/
theorem base_two_one_not_circleIntriguing :
    ¬ TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
      (fun k : Fin 4 => karlssonOEISBaseArrangement.center k)
      (fun k : Fin 4 => karlssonOEISBaseArrangement.radius k)
      (2 : Fin 4) (1 : Fin 4) := by
  intro h
  exact base_one_two_not_circleIntriguing
    ((TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing_symm
      (fun k : Fin 4 => karlssonOEISBaseArrangement.center k)
      (fun k : Fin 4 => karlssonOEISBaseArrangement.radius k)
      (1 : Fin 4) (2 : Fin 4)).2 h)

/-- The exact OEIS base pair `(Q1,Q3)` is not intriguing. -/
theorem base_one_three_not_circleIntriguing :
    ¬ TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
      (fun k : Fin 4 => karlssonOEISBaseArrangement.center k)
      (fun k : Fin 4 => karlssonOEISBaseArrangement.radius k)
      (1 : Fin 4) (3 : Fin 4) := by
  simpa [TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing,
    EuclideanLollipopArrangement.center, EuclideanLollipopArrangement.radius,
    karlssonOEISBaseArrangement] using
    CompleteFormalization.OEISPair13.q1q3_not_circleIntriguingPair

/-- The exact OEIS base pair `(Q3,Q1)` is not intriguing by symmetry. -/
theorem base_three_one_not_circleIntriguing :
    ¬ TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
      (fun k : Fin 4 => karlssonOEISBaseArrangement.center k)
      (fun k : Fin 4 => karlssonOEISBaseArrangement.radius k)
      (3 : Fin 4) (1 : Fin 4) := by
  intro h
  exact base_one_three_not_circleIntriguing
    ((TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing_symm
      (fun k : Fin 4 => karlssonOEISBaseArrangement.center k)
      (fun k : Fin 4 => karlssonOEISBaseArrangement.radius k)
      (1 : Fin 4) (3 : Fin 4)).2 h)

/-- The exact OEIS base pair `(Q2,Q3)` is not intriguing. -/
theorem base_two_three_not_circleIntriguing :
    ¬ TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
      (fun k : Fin 4 => karlssonOEISBaseArrangement.center k)
      (fun k : Fin 4 => karlssonOEISBaseArrangement.radius k)
      (2 : Fin 4) (3 : Fin 4) := by
  simpa [TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing,
    EuclideanLollipopArrangement.center, EuclideanLollipopArrangement.radius,
    karlssonOEISBaseArrangement] using
    CompleteFormalization.OEISPair23.q2q3_not_circleIntriguingPair

/-- The exact OEIS base pair `(Q3,Q2)` is not intriguing by symmetry. -/
theorem base_three_two_not_circleIntriguing :
    ¬ TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
      (fun k : Fin 4 => karlssonOEISBaseArrangement.center k)
      (fun k : Fin 4 => karlssonOEISBaseArrangement.radius k)
      (3 : Fin 4) (2 : Fin 4) := by
  intro h
  exact base_two_three_not_circleIntriguing
    ((TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing_symm
      (fun k : Fin 4 => karlssonOEISBaseArrangement.center k)
      (fun k : Fin 4 => karlssonOEISBaseArrangement.radius k)
      (2 : Fin 4) (3 : Fin 4)).2 h)

/-- Every distinct pair in the exact OEIS base is not intriguing. -/
theorem base_not_circleIntriguing_of_ne
    {a b : Fin 4} (hab : a ≠ b) :
    ¬ TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
      (fun k : Fin 4 => karlssonOEISBaseArrangement.center k)
      (fun k : Fin 4 => karlssonOEISBaseArrangement.radius k)
      a b := by
  fin_cases a <;> fin_cases b
  · exact (hab rfl).elim
  · exact base_zero_one_not_circleIntriguing
  · exact base_zero_two_not_circleIntriguing
  · exact base_zero_three_not_circleIntriguing
  · exact base_one_zero_not_circleIntriguing
  · exact (hab rfl).elim
  · exact base_one_two_not_circleIntriguing
  · exact base_one_three_not_circleIntriguing
  · exact base_two_zero_not_circleIntriguing
  · exact base_two_one_not_circleIntriguing
  · exact (hab rfl).elim
  · exact base_two_three_not_circleIntriguing
  · exact base_three_zero_not_circleIntriguing
  · exact base_three_one_not_circleIntriguing
  · exact base_three_two_not_circleIntriguing
  · exact (hab rfl).elim

/-- Every distinct non-exceptional pair in the exact OEIS base is not close
in the cyclic normalized-direction relation. -/
theorem base_not_cyclicClose_of_not_zeroOne
    {a b : Fin 4} (hab : a ≠ b)
    (h01 : ¬ zeroOneLabelPair a b) :
    ¬ TheoremOneEndToEnd.CloseDirection.cyclicClose
      (fun k : Fin 4 => karlssonOEISBaseArrangement.normalizedDirection k)
      a b := by
  fin_cases a <;> fin_cases b
  · exact (hab rfl).elim
  · exfalso
    exact h01 (Or.inl ⟨rfl, rfl⟩)
  · exact ExplicitInputs.karlssonOEISBase_zero_two_not_cyclicClose
  · exact ExplicitInputs.karlssonOEISBase_zero_three_not_cyclicClose
  · exfalso
    exact h01 (Or.inr ⟨rfl, rfl⟩)
  · exact (hab rfl).elim
  · exact ExplicitInputs.karlssonOEISBase_one_two_not_cyclicClose
  · exact ExplicitInputs.karlssonOEISBase_one_three_not_cyclicClose
  · intro h
    exact ExplicitInputs.karlssonOEISBase_zero_two_not_cyclicClose
      ((TheoremOneEndToEnd.CloseDirection.cyclicClose_symm
        (fun k : Fin 4 => karlssonOEISBaseArrangement.normalizedDirection k)
        (0 : Fin 4) (2 : Fin 4)).2 h)
  · intro h
    exact ExplicitInputs.karlssonOEISBase_one_two_not_cyclicClose
      ((TheoremOneEndToEnd.CloseDirection.cyclicClose_symm
        (fun k : Fin 4 => karlssonOEISBaseArrangement.normalizedDirection k)
        (1 : Fin 4) (2 : Fin 4)).2 h)
  · exact (hab rfl).elim
  · exact ExplicitInputs.karlssonOEISBase_two_three_not_cyclicClose
  · intro h
    exact ExplicitInputs.karlssonOEISBase_zero_three_not_cyclicClose
      ((TheoremOneEndToEnd.CloseDirection.cyclicClose_symm
        (fun k : Fin 4 => karlssonOEISBaseArrangement.normalizedDirection k)
        (0 : Fin 4) (3 : Fin 4)).2 h)
  · intro h
    exact ExplicitInputs.karlssonOEISBase_one_three_not_cyclicClose
      ((TheoremOneEndToEnd.CloseDirection.cyclicClose_symm
        (fun k : Fin 4 => karlssonOEISBaseArrangement.normalizedDirection k)
        (1 : Fin 4) (3 : Fin 4)).2 h)
  · intro h
    exact ExplicitInputs.karlssonOEISBase_two_three_not_cyclicClose
      ((TheoremOneEndToEnd.CloseDirection.cyclicClose_symm
        (fun k : Fin 4 => karlssonOEISBaseArrangement.normalizedDirection k)
        (2 : Fin 4) (3 : Fin 4)).2 h)
  · exact (hab rfl).elim

/-- The canonical relabeled all-ones arrangement has direct `<= 5` savings
for any pair whose canonical cluster labels are `0` and `1`. -/
noncomputable def canonicalOneOneOneOne_zeroOnePairCarrierSavingsFive
    {i j : Fin 4}
    (h01 :
      zeroOneLabelPair
        (canonicalOneOneOneOneCluster i)
        (canonicalOneOneOneOneCluster j)) :
    PairCarrierSavings
      (canonicalOneOneOneOneArrangement.lollipop i)
      (canonicalOneOneOneOneArrangement.lollipop j) 5 := by
  rcases h01 with ⟨hiNat, hjNat⟩ | ⟨hiNat, hjNat⟩
  · have hi : canonicalOneOneOneOneCluster i = (0 : Fin 4) := Fin.ext hiNat
    have hj : canonicalOneOneOneOneCluster j = (1 : Fin 4) := Fin.ext hjNat
    simpa [canonicalOneOneOneOneArrangement, hi, hj] using
      base_zero_one_pairCarrierSavingsFive
  · have hi : canonicalOneOneOneOneCluster i = (1 : Fin 4) := Fin.ext hiNat
    have hj : canonicalOneOneOneOneCluster j = (0 : Fin 4) := Fin.ext hjNat
    simpa [canonicalOneOneOneOneArrangement, hi, hj] using
      base_one_zero_pairCarrierSavingsFive

/-- Canonical all-ones pairs whose labels are `0` and `1` are close. -/
theorem canonicalOneOneOneOne_zeroOne_cyclicClose
    {i j : Fin 4}
    (h01 :
      zeroOneLabelPair
        (canonicalOneOneOneOneCluster i)
        (canonicalOneOneOneOneCluster j)) :
    TheoremOneEndToEnd.CloseDirection.cyclicClose
      (fun k : Fin 4 =>
        canonicalOneOneOneOneArrangement.normalizedDirection k) i j := by
  rcases h01 with ⟨hiNat, hjNat⟩ | ⟨hiNat, hjNat⟩
  · have hi : canonicalOneOneOneOneCluster i = (0 : Fin 4) := Fin.ext hiNat
    have hj : canonicalOneOneOneOneCluster j = (1 : Fin 4) := Fin.ext hjNat
    simpa [TheoremOneEndToEnd.CloseDirection.cyclicClose,
      canonicalOneOneOneOneArrangement,
      EuclideanLollipopArrangement.normalizedDirection, hi, hj] using
      base_zero_one_cyclicClose
  · have hi : canonicalOneOneOneOneCluster i = (1 : Fin 4) := Fin.ext hiNat
    have hj : canonicalOneOneOneOneCluster j = (0 : Fin 4) := Fin.ext hjNat
    simpa [TheoremOneEndToEnd.CloseDirection.cyclicClose,
      canonicalOneOneOneOneArrangement,
      EuclideanLollipopArrangement.normalizedDirection, hi, hj] using
      base_one_zero_cyclicClose

/-- Canonical all-ones pairs whose labels are `0` and `1` are not intriguing. -/
theorem canonicalOneOneOneOne_zeroOne_not_circleIntriguing
    {i j : Fin 4}
    (h01 :
      zeroOneLabelPair
        (canonicalOneOneOneOneCluster i)
        (canonicalOneOneOneOneCluster j)) :
    ¬ TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
      (fun k : Fin 4 => canonicalOneOneOneOneArrangement.center k)
      (fun k : Fin 4 => canonicalOneOneOneOneArrangement.radius k) i j := by
  rcases h01 with ⟨hiNat, hjNat⟩ | ⟨hiNat, hjNat⟩
  · have hi : canonicalOneOneOneOneCluster i = (0 : Fin 4) := Fin.ext hiNat
    have hj : canonicalOneOneOneOneCluster j = (1 : Fin 4) := Fin.ext hjNat
    intro h
    exact base_zero_one_not_circleIntriguing
      (by
        simpa [TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing,
          canonicalOneOneOneOneArrangement,
          EuclideanLollipopArrangement.center,
          EuclideanLollipopArrangement.radius, hi, hj] using h)
  · have hi : canonicalOneOneOneOneCluster i = (1 : Fin 4) := Fin.ext hiNat
    have hj : canonicalOneOneOneOneCluster j = (0 : Fin 4) := Fin.ext hjNat
    intro h
    exact base_one_zero_not_circleIntriguing
      (by
        simpa [TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing,
          canonicalOneOneOneOneArrangement,
          EuclideanLollipopArrangement.center,
          EuclideanLollipopArrangement.radius, hi, hj] using h)

/-- Every distinct canonical all-ones base pair is not intriguing. -/
theorem canonicalOneOneOneOne_not_circleIntriguing
    {i j : Fin 4} (hij : i < j) :
    ¬ TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
      (fun k : Fin 4 => canonicalOneOneOneOneArrangement.center k)
      (fun k : Fin 4 => canonicalOneOneOneOneArrangement.radius k) i j := by
  have hbase :=
    base_not_circleIntriguing_of_ne
      (canonicalOneOneOneOneCluster_ne_of_lt hij)
  intro h
  exact hbase
    (by
      simpa [TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing,
        canonicalOneOneOneOneArrangement,
        EuclideanLollipopArrangement.center,
        EuclideanLollipopArrangement.radius] using h)

/-- Canonical all-ones pairs whose labels are not the exceptional `0/1` pair
are not close. -/
theorem canonicalOneOneOneOne_not_zeroOne_not_cyclicClose
    {i j : Fin 4} (hij : i < j)
    (h01 :
      ¬ zeroOneLabelPair
        (canonicalOneOneOneOneCluster i)
        (canonicalOneOneOneOneCluster j)) :
    ¬ TheoremOneEndToEnd.CloseDirection.cyclicClose
      (fun k : Fin 4 =>
        canonicalOneOneOneOneArrangement.normalizedDirection k) i j := by
  have hbase :=
    base_not_cyclicClose_of_not_zeroOne
      (canonicalOneOneOneOneCluster_ne_of_lt hij) h01
  intro hclose
  exact hbase
    (by
      simpa [TheoremOneEndToEnd.CloseDirection.cyclicClose,
        canonicalOneOneOneOneArrangement,
        EuclideanLollipopArrangement.normalizedDirection] using hclose)

/-- The canonical crossing case bound is exactly `5` for all canonical
all-ones pairs whose labels are `0` and `1`. -/
theorem canonicalOneOneOneOne_zeroOne_caseBound_eq_five
    {i j : Fin 4}
    (h01 :
      zeroOneLabelPair
        (canonicalOneOneOneOneCluster i)
        (canonicalOneOneOneOneCluster j)) :
    TheoremOneEndToEnd.canonicalCrossingCaseBound
      (fun k : Fin 4 =>
        canonicalOneOneOneOneArrangement.normalizedDirection k)
      (fun k : Fin 4 => canonicalOneOneOneOneArrangement.center k)
      (fun k : Fin 4 => canonicalOneOneOneOneArrangement.radius k)
      i j = 5 := by
  have hclose := canonicalOneOneOneOne_zeroOne_cyclicClose h01
  have hnot := canonicalOneOneOneOne_zeroOne_not_circleIntriguing h01
  simp [TheoremOneEndToEnd.canonicalCrossingCaseBound, hclose, hnot]

/-- A non-exceptional canonical all-ones pair has case bound `7` once its
circle pair is proved non-intriguing.  The non-close half is already proved
from the exact OEIS normalized directions. -/
theorem canonicalOneOneOneOne_not_zeroOne_caseBound_eq_seven_of_not_intriguing
    {i j : Fin 4} (hij : i < j)
    (h01 :
      ¬ zeroOneLabelPair
        (canonicalOneOneOneOneCluster i)
        (canonicalOneOneOneOneCluster j))
    (hnot :
      ¬ TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
        (fun k : Fin 4 => canonicalOneOneOneOneArrangement.center k)
        (fun k : Fin 4 => canonicalOneOneOneOneArrangement.radius k)
        i j) :
    TheoremOneEndToEnd.canonicalCrossingCaseBound
      (fun k : Fin 4 =>
        canonicalOneOneOneOneArrangement.normalizedDirection k)
      (fun k : Fin 4 => canonicalOneOneOneOneArrangement.center k)
      (fun k : Fin 4 => canonicalOneOneOneOneArrangement.radius k)
      i j = 7 := by
  have hnotclose :=
    canonicalOneOneOneOne_not_zeroOne_not_cyclicClose hij h01
  simp [TheoremOneEndToEnd.canonicalCrossingCaseBound, hnotclose, hnot]

/-- A non-exceptional canonical all-ones pair has case bound exactly `7`.
The non-close and non-intriguing halves are both proved from the exact OEIS
base geometry. -/
theorem canonicalOneOneOneOne_not_zeroOne_caseBound_eq_seven
    {i j : Fin 4} (hij : i < j)
    (h01 :
      ¬ zeroOneLabelPair
        (canonicalOneOneOneOneCluster i)
        (canonicalOneOneOneOneCluster j)) :
    TheoremOneEndToEnd.canonicalCrossingCaseBound
      (fun k : Fin 4 =>
        canonicalOneOneOneOneArrangement.normalizedDirection k)
      (fun k : Fin 4 => canonicalOneOneOneOneArrangement.center k)
      (fun k : Fin 4 => canonicalOneOneOneOneArrangement.radius k)
      i j = 7 :=
  canonicalOneOneOneOne_not_zeroOne_caseBound_eq_seven_of_not_intriguing
    hij h01 (canonicalOneOneOneOne_not_circleIntriguing hij)

/-- In a distinct non-exceptional canonical all-ones pair, the Nat-valued
Karlsson table entry is `7`. -/
theorem canonicalOneOneOneOne_karlssonNat_eq_seven_of_not_zeroOne
    {i j : Fin 4} (hij : i < j)
    (h01 :
      ¬ zeroOneLabelPair
        (canonicalOneOneOneOneCluster i)
        (canonicalOneOneOneOneCluster j)) :
    karlssonClusterPairCrossingNat
      (canonicalOneOneOneOneCluster i)
      (canonicalOneOneOneOneCluster j) = 7 := by
  have hne :
      canonicalOneOneOneOneCluster i ≠
        canonicalOneOneOneOneCluster j :=
    canonicalOneOneOneOneCluster_ne_of_lt hij
  simpa [karlssonClusterPairCrossingNat, zeroOneLabelPair, hne] using h01

/-- Every canonical all-ones base pair has direct carrier savings at exactly
the Nat-valued Karlsson `5/7` table entry. -/
noncomputable def canonicalOneOneOneOne_pairCarrierSavingsKarlssonNat
    {i j : Fin 4} (hij : i < j) :
    PairCarrierSavings
      (canonicalOneOneOneOneArrangement.lollipop i)
      (canonicalOneOneOneOneArrangement.lollipop j)
      (karlssonClusterPairCrossingNat
        (canonicalOneOneOneOneCluster i)
        (canonicalOneOneOneOneCluster j)) := by
  by_cases h01 :
      zeroOneLabelPair
        (canonicalOneOneOneOneCluster i)
        (canonicalOneOneOneOneCluster j)
  · rcases h01 with ⟨hiNat, hjNat⟩ | ⟨hiNat, hjNat⟩
    · have hi : canonicalOneOneOneOneCluster i = (0 : Fin 4) := Fin.ext hiNat
      have hj : canonicalOneOneOneOneCluster j = (1 : Fin 4) := Fin.ext hjNat
      simpa [karlssonClusterPairCrossingNat, zeroOneLabelPair, hi, hj]
        using canonicalOneOneOneOne_zeroOnePairCarrierSavingsFive
          (i := i) (j := j) (Or.inl ⟨hiNat, hjNat⟩)
    · have hi : canonicalOneOneOneOneCluster i = (1 : Fin 4) := Fin.ext hiNat
      have hj : canonicalOneOneOneOneCluster j = (0 : Fin 4) := Fin.ext hjNat
      simpa [karlssonClusterPairCrossingNat, zeroOneLabelPair, hi, hj]
        using canonicalOneOneOneOne_zeroOnePairCarrierSavingsFive
          (i := i) (j := j) (Or.inr ⟨hiNat, hjNat⟩)
  · have htable :=
      canonicalOneOneOneOne_karlssonNat_eq_seven_of_not_zeroOne
        (i := i) (j := j) hij h01
    have hseven :
        PairCarrierSavings
          (canonicalOneOneOneOneArrangement.lollipop i)
          (canonicalOneOneOneOneArrangement.lollipop j) 7 :=
      pairCarrierSavingsGenericSeven
        (canonicalOneOneOneOne_spheres_distinct hij)
        (canonicalOneOneOneOne_rayLines_distinct hij)
    simpa [htable] using hseven

/-- Upper inequality for the canonical relabeled exact base automatic pair
table. -/
theorem canonicalOneOneOneOne_pairCross_le_karlssonNat
    {i j : Fin 4} (hij : i < j) :
    canonicalOneOneOneOnePairCross i j ≤
      (karlssonClusterPairCrossingNat
        (canonicalOneOneOneOneCluster i)
        (canonicalOneOneOneOneCluster j) : Rat) :=
  localPairCarrierCrossingData_cross_le_of_pairCarrierSavings
    (canonicalOneOneOneOne_localCarrierCrossingData hij)
    (canonicalOneOneOneOne_pairCarrierSavingsKarlssonNat hij)

/-- Exact equality between the canonical all-ones automatic pair table and
the rational Karlsson cluster table. -/
theorem canonicalOneOneOneOne_pairCross_eq_cluster
    {i j : Fin 4} (hij : i < j) :
    canonicalOneOneOneOnePairCross i j =
      karlssonClusterPairCrossing
        (canonicalOneOneOneOneCluster i)
        (canonicalOneOneOneOneCluster j) := by
  apply le_antisymm
  · rw [karlssonClusterPairCrossing_eq_nat]
    exact canonicalOneOneOneOne_pairCross_le_karlssonNat hij
  · exact canonicalOneOneOneOne_pairCross_ge_cluster hij

/-- The exceptional canonical all-ones pair has automatic pair-table value
exactly `5`. -/
theorem canonicalOneOneOneOne_pairCross_eq_five_of_zeroOne
    {i j : Fin 4} (hij : i < j)
    (h01 :
      zeroOneLabelPair
        (canonicalOneOneOneOneCluster i)
        (canonicalOneOneOneOneCluster j)) :
    canonicalOneOneOneOnePairCross i j = 5 := by
  rw [canonicalOneOneOneOne_pairCross_eq_cluster hij]
  rcases h01 with ⟨hiNat, hjNat⟩ | ⟨hiNat, hjNat⟩
  · have hi : canonicalOneOneOneOneCluster i = (0 : Fin 4) := Fin.ext hiNat
    have hj : canonicalOneOneOneOneCluster j = (1 : Fin 4) := Fin.ext hjNat
    simp [karlssonClusterPairCrossing, hi, hj]
  · have hi : canonicalOneOneOneOneCluster i = (1 : Fin 4) := Fin.ext hiNat
    have hj : canonicalOneOneOneOneCluster j = (0 : Fin 4) := Fin.ext hjNat
    simp [karlssonClusterPairCrossing, hi, hj]

/-- For canonical all-ones pairs with labels `0` and `1`, the exact automatic
pair table satisfies the canonical crossing case bound. -/
theorem canonicalOneOneOneOne_pairCross_le_caseBound_of_zeroOne
    {i j : Fin 4} (hij : i < j)
    (h01 :
      zeroOneLabelPair
        (canonicalOneOneOneOneCluster i)
        (canonicalOneOneOneOneCluster j)) :
    canonicalOneOneOneOnePairCross i j ≤
      TheoremOneEndToEnd.canonicalCrossingCaseBound
        (fun k : Fin 4 =>
          canonicalOneOneOneOneArrangement.normalizedDirection k)
        (fun k : Fin 4 => canonicalOneOneOneOneArrangement.center k)
        (fun k : Fin 4 => canonicalOneOneOneOneArrangement.radius k)
        i j := by
  rw [canonicalOneOneOneOne_zeroOne_caseBound_eq_five h01]
  rw [canonicalOneOneOneOne_pairCross_eq_five_of_zeroOne hij h01]

/-- For non-exceptional canonical all-ones pairs, the exact automatic pair
table satisfies the canonical crossing case bound. -/
theorem canonicalOneOneOneOne_pairCross_le_caseBound_of_not_zeroOne
    {i j : Fin 4} (hij : i < j)
    (h01 :
      ¬ zeroOneLabelPair
        (canonicalOneOneOneOneCluster i)
        (canonicalOneOneOneOneCluster j)) :
    canonicalOneOneOneOnePairCross i j ≤
      TheoremOneEndToEnd.canonicalCrossingCaseBound
        (fun k : Fin 4 =>
          canonicalOneOneOneOneArrangement.normalizedDirection k)
        (fun k : Fin 4 => canonicalOneOneOneOneArrangement.center k)
        (fun k : Fin 4 => canonicalOneOneOneOneArrangement.radius k)
        i j := by
  rw [canonicalOneOneOneOne_not_zeroOne_caseBound_eq_seven hij h01]
  rw [canonicalOneOneOneOne_pairCross_eq_cluster hij]
  rw [karlssonClusterPairCrossing_eq_nat]
  rw [canonicalOneOneOneOne_karlssonNat_eq_seven_of_not_zeroOne hij h01]
  norm_num

/-- For every canonical all-ones pair, the exact automatic pair table
satisfies the manuscript's canonical crossing case bound. -/
theorem canonicalOneOneOneOne_pairCross_le_caseBound
    {i j : Fin 4} (hij : i < j) :
    canonicalOneOneOneOnePairCross i j ≤
      TheoremOneEndToEnd.canonicalCrossingCaseBound
        (fun k : Fin 4 =>
          canonicalOneOneOneOneArrangement.normalizedDirection k)
        (fun k : Fin 4 => canonicalOneOneOneOneArrangement.center k)
        (fun k : Fin 4 => canonicalOneOneOneOneArrangement.radius k)
        i j := by
  by_cases h01 :
      zeroOneLabelPair
        (canonicalOneOneOneOneCluster i)
        (canonicalOneOneOneOneCluster j)
  · exact canonicalOneOneOneOne_pairCross_le_caseBound_of_zeroOne hij h01
  · exact canonicalOneOneOneOne_pairCross_le_caseBound_of_not_zeroOne hij h01

/-- A non-exceptional canonical all-ones pair has automatic pair-table value
exactly `7`. -/
theorem canonicalOneOneOneOne_pairCross_eq_seven_of_not_zeroOne
    {i j : Fin 4} (hij : i < j)
    (h01 :
      ¬ zeroOneLabelPair
        (canonicalOneOneOneOneCluster i)
        (canonicalOneOneOneOneCluster j)) :
    canonicalOneOneOneOnePairCross i j = 7 := by
  rw [canonicalOneOneOneOne_pairCross_eq_cluster hij]
  have hne :
      canonicalOneOneOneOneCluster i ≠
        canonicalOneOneOneOneCluster j :=
    canonicalOneOneOneOneCluster_ne_of_lt hij
  simpa [karlssonClusterPairCrossing, zeroOneLabelPair, hne] using h01

/-- The exact canonical all-ones automatic pair table has the same unordered
pair sum as the canonical cluster table. -/
theorem canonicalOneOneOneOne_pairSum_eq_clustered :
    pairSum 4 canonicalOneOneOneOnePairCross =
      clusteredKarlssonPairTableCrossings canonicalOneOneOneOneCluster := by
  classical
  unfold pairSum clusteredKarlssonPairTableCrossings
  apply Finset.sum_congr rfl
  intro p hp
  have hp_lt : p.1 < p.2 := by
    rw [pairFinset, Finset.mem_filter] at hp
    exact hp.2
  exact canonicalOneOneOneOne_pairCross_eq_cluster hp_lt

/-- The exact canonical all-ones automatic pair table has pair sum equal to
the lower-crossing polynomial for the all-ones quadruple. -/
theorem canonicalOneOneOneOne_pairSum_eq_lowerCrossingsOfQuad :
    pairSum 4 canonicalOneOneOneOnePairCross =
      lowerCrossingsOfQuad oneOneOneOneQuad := by
  calc
    pairSum 4 canonicalOneOneOneOnePairCross =
        clusteredKarlssonPairTableCrossings canonicalOneOneOneOneCluster :=
      canonicalOneOneOneOne_pairSum_eq_clustered
    _ = karlssonClusterTableCrossingsOfQuad oneOneOneOneQuad := by
      simpa [canonicalOneOneOneOneCluster] using
        (CardinalityClusteredKarlssonTableWitness.pairSum_eq_table
          canonicalOneOneOneOneWitness)
    _ = lowerCrossingsOfQuad oneOneOneOneQuad :=
      karlssonClusterTableCrossingsOfQuad_eq_lowerCrossingsOfQuad
        oneOneOneOneQuad

/-- The exact canonical all-ones automatic pair table has total crossing sum
`40`. -/
theorem canonicalOneOneOneOne_pairSum_eq_forty :
    pairSum 4 canonicalOneOneOneOnePairCross = 40 := by
  rw [canonicalOneOneOneOne_pairSum_eq_lowerCrossingsOfQuad]
  norm_num [lowerCrossingsOfQuad, lowerCrossingsQ, binomTwoQ,
    clusterExcess, oneOneOneOneQuad, quadEntry]

/-- Region-equation form of the exact canonical all-ones automatic base
table: the base pair sum gives `45 = 40 + 4 + 1`. -/
theorem canonicalOneOneOneOne_region_eq_pairSum_add :
    (45 : Rat) =
      pairSum 4 canonicalOneOneOneOnePairCross + (4 : Rat) + 1 := by
  rw [canonicalOneOneOneOne_pairSum_eq_forty]
  norm_num

end

end OEISBaseUpper
end EndToEndFormalization
end TheoremOneManuscript
end Lollipop
