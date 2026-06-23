import Lollipop.Concrete.EndToEnd.Support
import Lollipop.Concrete.EndToEnd.Insertion
import Lollipop.Concrete.Empty
import Lollipop.Internal.Core
import Mathlib.Tactic

/-!
# Planar topology boundary

The concrete upper and lower endpoints need two hard planar-topology facts:

1. the arbitrary-arrangement pair-excess bound
   `regions(A) - n - 1 ≤ Σ q(Aᵢ,Aⱼ)`;
2. the generic Euler equation
   `regions(A) = crossings(A) + n + 1`.

The previous version of this file sketched these proofs using unavailable
Mathlib APIs for Alexander duality, Mayer--Vietoris, semialgebraic
triangulation, and connected-component homeomorphisms.  This file records the
same obligations as explicit concrete theorem targets.  They are not abstract
`GeometryCertificates`: every field is stated for the concrete Euclidean
lollipop model and the concrete connected-component region count.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd

open Set

/-- Remaining planar-topology theorem package for the concrete model. -/
structure PlanarTopologyPorts : Prop where
  region_components_finite :
    ∀ {n : ℕ} (A : Arrangement n),
      Finite (ConnectedComponents (FreeSpace A))
  crossing_excess_le_pairSum :
    ∀ {n : ℕ} (A : Arrangement n),
      regionCountRat A - (n : ℚ) - 1 ≤
        Lollipop.pairSum n (pairExcessTable A)
  generic_region_eq :
    ∀ {n : ℕ} {A : Arrangement n}, IsGeneric A →
      regionCountRat A = ((totalCrossingsNat A : ℕ) : ℚ) + (n : ℚ) + 1

theorem region_components_finite_zero (A : Arrangement 0) :
    Finite (ConnectedComponents (FreeSpace A)) := by
  have hset : {x : Point | x ∉ occupied A} = univ := by
    ext x
    simp [occupied_zero A]
  have hpre : IsPreconnected ({x : Point | x ∉ occupied A}) := by
    rw [hset]
    exact isPreconnected_univ
  haveI : PreconnectedSpace (FreeSpace A) := Subtype.preconnectedSpace hpre
  exact .of_subsingleton

theorem crossing_excess_le_pairSum_zero (A : Arrangement 0) :
    regionCountRat A - (0 : ℚ) - 1 ≤
      Lollipop.pairSum 0 (pairExcessTable A) := by
  simp [regionCountRat_zero A, Lollipop.pairSum, Lollipop.pairFinset]

theorem regionCountRat_eq_crossings_add_zero
    {A : Arrangement 0} (_hA : IsGeneric A) :
    regionCountRat A = ((totalCrossingsNat A : ℕ) : ℚ) + (0 : ℚ) + 1 := by
  simp [regionCountRat_zero A, totalCrossingsNat, Lollipop.pairFinset]

/-- Finiteness of concrete complement components, from the planar topology
package. -/
theorem region_components_finite (ports : PlanarTopologyPorts)
    {n : ℕ} (A : Arrangement n) :
    Finite (ConnectedComponents (FreeSpace A)) :=
  ports.region_components_finite A

/-- Rational arbitrary-arrangement bound consumed by the colored Turan backend. -/
theorem crossing_excess_le_pairSum (ports : PlanarTopologyPorts)
    {n : ℕ} (A : Arrangement n) :
    regionCountRat A - (n : ℚ) - 1 ≤
      Lollipop.pairSum n (pairExcessTable A) :=
  ports.crossing_excess_le_pairSum A

/-- Generic exact region equation in rational form. -/
theorem regionCountRat_eq_crossings_add (ports : PlanarTopologyPorts)
    {n : ℕ} {A : Arrangement n} (hA : IsGeneric A) :
    regionCountRat A = ((totalCrossingsNat A : ℕ) : ℚ) + (n : ℚ) + 1 :=
  ports.generic_region_eq hA

end EndToEnd
end Concrete
end Lollipop
