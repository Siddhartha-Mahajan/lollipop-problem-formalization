import Lollipop.Concrete.EndToEnd.ComponentLifting
import Lollipop.Concrete.EndToEnd.CarrierAvoidance
import Mathlib.Tactic

/-!
# Component-map surjectivity for one lollipop insertion

This module proves one non-Jordan part of the local insertion topology.  If a
closed old carrier `C` is enlarged to a set `K` contained in `C` plus one
lollipop carrier, then every connected component of `Cᶜ` still contains a
point of `Kᶜ`.  Equivalently, the inclusion-induced map

`ConnectedComponents Kᶜ -> ConnectedComponents Cᶜ`

is surjective.

This is the exact-surjectivity field needed by
`ComponentFibers.ExactOneComponentSplitData`; the remaining hard work is the
two-side active-fibre classifier.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace ComponentSurjectivity

open Set Function

/-- Complement inclusion induced by `C ⊆ K`. -/
def complementSubset {C K : Set Point} (hCK : C ⊆ K) :
    Kᶜ ⊆ Cᶜ :=
  fun _ hxK hxC => hxK (hCK hxC)

/-- If the enlarged carrier differs from a closed old carrier by at most one
concrete lollipop, every old complementary component still contains a point
of the new complement. -/
theorem componentMap_surjective_of_closed_of_subset_union_carrier
    {C K : Set Point} (hCK : C ⊆ K) (hCclosed : IsClosed C)
    (L : Lollipop) (hKsub : K ⊆ C ∪ L.carrier) :
    Surjective
      (ComponentFibers.inclusionMap (complementSubset hCK)) := by
  intro c
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c
  let U : Set Point := connectedComponentIn Cᶜ y.1
  have hyU : y.1 ∈ U :=
    mem_connectedComponentIn y.2
  have hUopen : IsOpen U :=
    IsOpen.connectedComponentIn hCclosed.isOpen_compl
  obtain ⟨z, hzU, hzL⟩ :=
    Lollipop.Concrete.EndToEnd.Lollipop.exists_mem_open_not_mem_carrier
      L hUopen hyU
  have hzC : z ∉ C :=
    connectedComponentIn_subset Cᶜ y.1 hzU
  have hzK : z ∉ K := by
    intro hz
    exact (hKsub hz).elim hzC hzL
  let x : (Kᶜ : Set Point) := ⟨z, hzK⟩
  let zOld : (Cᶜ : Set Point) := ⟨z, hzC⟩
  have hzy :
      ConnectedComponents.mk zOld = ConnectedComponents.mk y := by
    let yU : U := ⟨y.1, hyU⟩
    let zU : U := ⟨z, hzU⟩
    let j : U → (Cᶜ : Set Point) := fun w =>
      ⟨w.1, connectedComponentIn_subset Cᶜ y.1 w.2⟩
    have hj : Continuous j :=
      Continuous.subtype_mk continuous_subtype_val
        (fun w => connectedComponentIn_subset Cᶜ y.1 w.2)
    letI : PreconnectedSpace U :=
      Subtype.preconnectedSpace isPreconnected_connectedComponentIn
    have hUcomp :
        ConnectedComponents.mk zU = ConnectedComponents.mk yU :=
      Subsingleton.elim _ _
    have hmap := congrArg hj.connectedComponentsMap hUcomp
    simpa [j, zU, yU, zOld] using hmap
  refine ⟨ConnectedComponents.mk x, ?_⟩
  rw [ComponentFibers.inclusionMap_mk]
  simpa [x, zOld, ComponentFibers.inclusion] using hzy

/-- Exact split data from the non-Jordan insertion ingredients already
available here, plus the still-hard active two-side classifier.  This is the
local target shape for each effective inserted carrier edge. -/
def exactOneComponentSplitDataOfConnectedLifting
    {C K : Set Point} (hCK : C ⊆ K) (hCclosed : IsClosed C)
    (L : Lollipop) (hKsub : K ⊆ C ∪ L.carrier)
    (active : ConnectedComponents (Cᶜ : Set Point))
    (activeClassifier :
      ComponentFibers.Fiber
        (ComponentFibers.inclusionMap (complementSubset hCK)) active →
          Fin 2)
    (active_injective : Injective activeClassifier)
    (hinactive :
      ComponentLifting.InactiveConnectedLifting
        (complementSubset hCK) active)
    (active_surjective : Surjective activeClassifier) :
    ComponentFibers.ExactOneComponentSplitData (complementSubset hCK) where
  toOneComponentSplitData :=
    ComponentLifting.oneComponentSplitDataOfConnectedLifting
      (complementSubset hCK) active activeClassifier active_injective
      hinactive
  componentMap_surjective :=
    componentMap_surjective_of_closed_of_subset_union_carrier
      hCK hCclosed L hKsub
  activeSide_surjective := active_surjective

end ComponentSurjectivity
end EndToEnd
end Concrete
end Lollipop
