import Lollipop.Concrete.Topology

/-!
# Empty concrete arrangement

The obstruction note points out that the abstract certificate interface can
misrepresent the `n = 0` case.  In the concrete Euclidean model, the empty
arrangement has the whole plane as free space, hence exactly one connected
component.
-/

noncomputable section

namespace Lollipop
namespace Concrete

open Set

/-- The manuscript extremum has value `0` at size `0`. -/
theorem manuscriptS_zero :
    TheoremOneManuscript.manuscriptS 0 = 0 := by
  rw [TheoremOneManuscript.manuscriptS_eq_concreteS]
  rw [Lollipop.concreteS_eq_concreteM, Lollipop.concreteM_zero]
  norm_num

/-- The concrete target formula has value `1` at size `0`. -/
theorem candidate_zero : candidate 0 = 1 := by
  simp [candidate, manuscriptS_zero]

/-- The unique empty arrangement, named for use as the `n = 0` lower witness. -/
def emptyArrangement : Arrangement 0 :=
  fun i => nomatch i

theorem occupied_zero (A : Arrangement 0) : occupied A = ∅ := by
  ext x
  simp [occupied]

theorem freeSpace_zero_nonempty (A : Arrangement 0) : Nonempty (FreeSpace A) :=
  ⟨⟨0, by simp [occupied_zero A]⟩⟩

/-- The empty arrangement has exactly one complementary region. -/
theorem regionCount_zero (A : Arrangement 0) : regionCount A = 1 := by
  have hset : {x : Point | x ∉ occupied A} = univ := by
    ext x
    simp [occupied_zero A]
  have hpre : IsPreconnected ({x : Point | x ∉ occupied A}) := by
    rw [hset]
    exact isPreconnected_univ
  haveI : PreconnectedSpace (FreeSpace A) := Subtype.preconnectedSpace hpre
  have hsub : Subsingleton (ConnectedComponents (FreeSpace A)) := inferInstance
  have hnon : Nonempty (ConnectedComponents (FreeSpace A)) :=
    ConnectedComponents.nonempty_iff_nonempty.mpr (freeSpace_zero_nonempty A)
  unfold regionCount
  exact Nat.card_eq_one_iff_unique.mpr ⟨hsub, hnon⟩

theorem regionCountRat_zero (A : Arrangement 0) : regionCountRat A = 1 := by
  simp [regionCountRat, regionCount_zero A]

theorem regionUpperStatement_zero : RegionUpperStatement 0 := by
  intro A
  rw [regionCountRat_zero A, candidate_zero]

theorem regionLowerStatement_zero : RegionLowerStatement 0 :=
  ⟨emptyArrangement, by rw [regionCountRat_zero, candidate_zero]⟩

/-- Concrete certificate-free maximum theorem for the empty arrangement. -/
theorem lollipopMaximum_zero : LollipopMaximumStatement 0 :=
  lollipopMaximum_of_upper_lower regionUpperStatement_zero regionLowerStatement_zero

end Concrete
end Lollipop
