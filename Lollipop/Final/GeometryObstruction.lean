import Lollipop.Final.TheoremOne

/-!
Obstruction to a universal geometry certificate.

`GeometryCertificates P` is intentionally a concrete-model boundary.  It
cannot be constructed for every abstract `MaxProblemFamily`: an abstract
family may have no relationship to Euclidean lollipops at all.
-/

namespace Lollipop
namespace Final

noncomputable section

/-- A degenerate abstract maximum family with one arrangement of every size
and zero regions.  This is not the lollipop problem; it is a sanity check
showing that the final geometry boundary cannot be filled polymorphically for
all abstract problem families. -/
def zeroRegionMaxProblemFamily : TheoremOne.MaxProblemFamily where
  Arrangement := fun _ => Unit
  region := fun _ _ => 0
  aLop := fun _ => 0
  aLop_spec := by
    intro n
    constructor
    · exact ⟨(), rfl⟩
    · intro y hy
      rcases hy with ⟨_A, rfl⟩
      norm_num

/-- The manuscript extremum has value `0` at size `0`. -/
theorem manuscriptS_zero :
    TheoremOneManuscript.manuscriptS 0 = 0 := by
  rw [TheoremOneManuscript.manuscriptS_eq_concreteS]
  native_decide

/-- Therefore the displayed formula evaluates to `1` at size `0`. -/
theorem displayed_formula_rhs_zero :
    4 * (((0 : Nat).choose 2 : Nat) : Rat) +
        TheoremOneManuscript.manuscriptS 0 + (0 : Rat) + 1 = 1 := by
  rw [manuscriptS_zero]
  norm_num

/-- No geometry certificate can exist for the degenerate zero-region family.

This records the main interface fact: the missing geometric producer cannot
have type `∀ P, GeometryCertificates P`.  It must either target the intended
concrete lollipop family or take genuine Euclidean realization hypotheses. -/
theorem no_geometryCertificates_zeroRegionMaxProblemFamily :
    GeometryCertificates zeroRegionMaxProblemFamily → False := by
  intro h
  have hformula := displayed_formula zeroRegionMaxProblemFamily h 0
  norm_num [zeroRegionMaxProblemFamily, manuscriptS_zero] at hformula

/-- Typeclass form of `no_geometryCertificates_zeroRegionMaxProblemFamily`. -/
instance isEmpty_geometryCertificates_zeroRegionMaxProblemFamily :
    IsEmpty (GeometryCertificates zeroRegionMaxProblemFamily) where
  false := no_geometryCertificates_zeroRegionMaxProblemFamily

end

end Final
end Lollipop
