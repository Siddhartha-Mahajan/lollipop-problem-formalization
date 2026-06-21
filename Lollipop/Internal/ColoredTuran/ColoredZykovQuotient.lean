import Lollipop.Internal.ColoredTuran.ColoredZykov
import Lollipop.Internal.SectionFive.PartitionMatrix

/-!
Colored Zykov quotient construction.

This module isolates the quotient step after the Zykov symmetrization has
reached a configuration whose color-zero classes are twin classes.  From that
property, Lean constructs the quotient colored graph, proves that the quotient
has no off-diagonal zero color, and proves that the derived `D` and `E`
clique-free hypotheses descend to the quotient.
-/

namespace Lollipop
namespace TheoremOneEndToEnd

universe u

set_option linter.unusedSectionVars false

variable {V : Type u} [Fintype V] [DecidableEq V]

namespace ColoredGraph

/-- The state needed after the tie-breaker part of colored Zykov: color zero is
transitive, and color-zero pairs are twins with identical color rows.  Reflexivity
and symmetry come from the `ColoredGraph` fields. -/
structure ZeroTwinQuotientReady (C : ColoredGraph V) : Prop where
  zero_trans :
    ∀ ⦃a b c : V⦄,
      C.color a b = PairColor.zero →
      C.color b c = PairColor.zero →
      C.color a c = PairColor.zero
  zero_twins :
    ∀ ⦃a b : V⦄,
      C.color a b = PairColor.zero →
      ∀ z : V, C.color a z = C.color b z

/-- The full finite colored Zykov tie-breaker supplies exactly the
zero-twin condition needed for quotienting: every color-zero pair is a twin
pair, hence color zero is transitive. -/
theorem zeroTwinQuotientReady_of_zykov_extremal
    (C : ColoredGraph V) (hC : C.IsColoredZykovExtremal) :
    C.ZeroTwinQuotientReady where
  zero_trans := by
    intro a b c hab hbc
    have habrow := sameRow_of_zero_of_zykov_extremal C hC hab
    exact (habrow c).trans hbc
  zero_twins := by
    intro a b hab z
    exact sameRow_of_zero_of_zykov_extremal C hC hab z

/-- The setoid whose classes are the color-zero twin classes. -/
def zeroSetoid (C : ColoredGraph V) (h : C.ZeroTwinQuotientReady) :
    Setoid V where
  r v w := C.color v w = PairColor.zero
  iseqv := by
    constructor
    · intro v
      exact C.color_self v
    · intro v w hvw
      rw [← C.color_symm v w, hvw]
    · intro a b c hab hbc
      exact h.zero_trans hab hbc

instance zeroSetoid_decidableRel
    (C : ColoredGraph V) (h : C.ZeroTwinQuotientReady) :
    DecidableRel (C.zeroSetoid h).r := by
  intro v w
  change Decidable (C.color v w = PairColor.zero)
  infer_instance

/-- The quotient vertex type of zero twin classes. -/
abbrev ZeroQuotient (C : ColoredGraph V) (h : C.ZeroTwinQuotientReady) :
    Type u :=
  Quotient (C.zeroSetoid h)

noncomputable instance zeroQuotient_fintype
    (C : ColoredGraph V) (h : C.ZeroTwinQuotientReady) :
    Fintype (C.ZeroQuotient h) :=
  Quotient.fintype (C.zeroSetoid h)

/-- The quotient color is well-defined because zero-equivalent vertices are
twins. -/
noncomputable def quotientColor
    (C : ColoredGraph V) (h : C.ZeroTwinQuotientReady) :
    C.ZeroQuotient h → C.ZeroQuotient h → PairColor :=
  fun q r =>
    Quotient.liftOn₂
      (s₁ := C.zeroSetoid h) (s₂ := C.zeroSetoid h)
      q r
      (fun v w : V => C.color v w)
      (by
        intro a₁ b₁ a₂ b₂ ha hb
        calc
          C.color a₁ b₁ = C.color a₂ b₁ := h.zero_twins ha b₁
          _ = C.color b₁ a₂ := C.color_symm a₂ b₁
          _ = C.color b₂ a₂ := h.zero_twins hb a₂
          _ = C.color a₂ b₂ := C.color_symm b₂ a₂)

theorem quotientColor_mk
    (C : ColoredGraph V) (h : C.ZeroTwinQuotientReady)
    (v w : V) :
    C.quotientColor h ⟦v⟧ ⟦w⟧ = C.color v w := by
  rfl

theorem quotientColor_out
    (C : ColoredGraph V) (h : C.ZeroTwinQuotientReady)
    (q r : C.ZeroQuotient h) :
    C.quotientColor h q r =
      C.color (Quotient.out q) (Quotient.out r) := by
  calc
    C.quotientColor h q r =
        C.quotientColor h ⟦Quotient.out q⟧ ⟦Quotient.out r⟧ := by
          rw [Quotient.out_eq q, Quotient.out_eq r]
    _ = C.color (Quotient.out q) (Quotient.out r) := rfl

/-- The quotient colored graph on zero twin classes. -/
noncomputable def zeroQuotientColoredGraph
    (C : ColoredGraph V) (h : C.ZeroTwinQuotientReady) :
    ColoredGraph (C.ZeroQuotient h) where
  color := C.quotientColor h
  color_symm := by
    intro q r
    refine Quotient.inductionOn₂ q r ?_
    intro v w
    simp [quotientColor_mk, C.color_symm]
  color_self := by
    intro q
    refine Quotient.inductionOn q ?_
    intro v
    simp [quotientColor_mk, C.color_self]

/-- The representative choice for quotient classes is injective as a map out of
the quotient type. -/
theorem quotient_out_injective
    (C : ColoredGraph V) (h : C.ZeroTwinQuotientReady) :
    Function.Injective (Quotient.out : C.ZeroQuotient h → V) := by
  intro q r hqr
  rw [← Quotient.out_eq q, ← Quotient.out_eq r, hqr]

/-- Weight of a quotient class: the number of original vertices in that
color-zero class. -/
noncomputable def zeroClassWeight
    (C : ColoredGraph V) (h : C.ZeroTwinQuotientReady) :
    C.ZeroQuotient h → Nat :=
  fun q =>
    ((Finset.univ : Finset V).filter
      (fun v : V => (Quotient.mk'' v : C.ZeroQuotient h) = q)).card

/-- The quotient class weights sum to the original number of vertices. -/
theorem totalWeightNat_zeroClassWeight
    (C : ColoredGraph V) (h : C.ZeroTwinQuotientReady) :
    totalWeightNat (C.zeroClassWeight h) = Fintype.card V := by
  classical
  let f : V → C.ZeroQuotient h := Quotient.mk''
  have hf : Function.Surjective f := Quotient.mk''_surjective
  have hcard :=
    Finset.card_eq_sum_card_image (f := f) (s := (Finset.univ : Finset V))
  have himage : (Finset.univ.image f : Finset (C.ZeroQuotient h)) = Finset.univ :=
    Finset.image_univ_of_surjective hf
  rw [himage] at hcard
  simpa [totalWeightNat, zeroClassWeight, f] using hcard.symm

/-- In the zero-twin quotient, no distinct classes have color zero. -/
theorem zeroQuotient_noZeroOffDiag
    (C : ColoredGraph V) (h : C.ZeroTwinQuotientReady) :
    (C.zeroQuotientColoredGraph h).NoZeroOffDiag := by
  intro q r hqr hzero
  have hrep : C.color (Quotient.out q) (Quotient.out r) = PairColor.zero := by
    simpa [zeroQuotientColoredGraph, quotientColor_out]
      using hzero
  have hclasses :
      (⟦Quotient.out q⟧ : C.ZeroQuotient h) =
        ⟦Quotient.out r⟧ :=
    Quotient.sound hrep
  apply hqr
  calc
    q = (⟦Quotient.out q⟧ : C.ZeroQuotient h) :=
      (Quotient.out_eq q).symm
    _ = ⟦Quotient.out r⟧ := hclasses
    _ = r := Quotient.out_eq r

/-- The quotient `D` graph injects back into the original `D` graph by choosing
one representative from each zero class. -/
noncomputable def zeroQuotientDGraphHom
    (C : ColoredGraph V) (h : C.ZeroTwinQuotientReady) :
    (C.zeroQuotientColoredGraph h).DGraph →g C.DGraph where
  toFun := Quotient.out
  map_rel' := by
    intro q r hqr
    unfold DGraph at hqr ⊢
    simpa [zeroQuotientColoredGraph, quotientColor_out]
      using hqr

/-- The quotient `E` graph injects back into the original `E` graph by choosing
one representative from each zero class. -/
noncomputable def zeroQuotientEGraphHom
    (C : ColoredGraph V) (h : C.ZeroTwinQuotientReady) :
    (C.zeroQuotientColoredGraph h).EGraph →g C.EGraph where
  toFun := Quotient.out
  map_rel' := by
    intro q r hqr
    unfold EGraph at hqr ⊢
    simpa [zeroQuotientColoredGraph, quotientColor_out]
      using hqr

/-- Clique-freeness of `D` descends to the zero-twin quotient. -/
theorem zeroQuotient_DGraph_cliqueFree
    (C : ColoredGraph V) (h : C.ZeroTwinQuotientReady)
    {m : Nat} (hD : C.DGraph.CliqueFree m) :
    (C.zeroQuotientColoredGraph h).DGraph.CliqueFree m := by
  exact SimpleGraph.CliqueFree.comap
    ((C.zeroQuotientDGraphHom h).toCopy
      (C.quotient_out_injective h)).isContained
    hD

/-- Clique-freeness of `E` descends to the zero-twin quotient. -/
theorem zeroQuotient_EGraph_cliqueFree
    (C : ColoredGraph V) (h : C.ZeroTwinQuotientReady)
    {m : Nat} (hE : C.EGraph.CliqueFree m) :
    (C.zeroQuotientColoredGraph h).EGraph.CliqueFree m := by
  exact SimpleGraph.CliqueFree.comap
    ((C.zeroQuotientEGraphHom h).toCopy
      (C.quotient_out_injective h)).isContained
    hE

end ColoredGraph

end TheoremOneEndToEnd
end Lollipop
