import Lollipop.Concrete.EndToEnd.Lower.Genericity
import Lollipop.Concrete.EndToEnd.TranslationGenericity

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

/-- Parameter locus where one selected pair has finite carrier contact. -/
def pairFiniteGood {n : ℕ} (i j : Fin n) :
    Set (Lower.ArrangementParameter n) :=
  {p | ((p.toArrangement i).carrier ∩
    (p.toArrangement j).carrier).Finite}

/-- A stronger, elementary good locus for one pair: unequal circles and
nonparallel stems.  This is the explicit geometric condition currently used
as the next density target for pair-finiteness. -/
def pairRegularGood {n : ℕ} (i j : Fin n) :
    Set (Lower.ArrangementParameter n) :=
  {p |
    (p.toArrangement i).circle ≠ (p.toArrangement j).circle ∧
      detPoint (p.toArrangement i).radial
        (p.toArrangement j).radial ≠ 0}

/-- Distinct circles plus nonparallel stems imply finite carrier contact. -/
theorem pairCrossingSet_finite_of_circle_ne_of_nonparallel
    {L M : Lollipop} (hcircle : L.circle ≠ M.circle)
    (hdet : detPoint L.radial M.radial ≠ 0) :
    (pairCrossingSet L M).Finite := by
  have hccFin : (cc L M).Finite :=
    finite_circle_intersection_of_ne hcircle
  have hrcFin : (rc L M).Finite :=
    finite_ray_circle_intersection L M
  have hcrFin : (cr L M).Finite :=
    finite_circle_ray_intersection L M
  have hrrFin : (rr L M).Finite := by
    by_cases hrr : (rr L M).Nonempty
    · exact finite_of_subsingleton_of_mem
        (rr_subsingleton_of_transverse hdet) hrr.some_mem
    · rw [Set.not_nonempty_iff_eq_empty.mp hrr]
      exact Set.finite_empty
  rw [pairCrossingSet_decompose]
  exact ((hccFin.union hrcFin).union hcrFin).union hrrFin

/-- The elementary pair-regular locus is contained in the finite-contact
locus. -/
theorem pairRegularGood_subset_pairFiniteGood {n : ℕ} (i j : Fin n) :
    pairRegularGood i j ⊆ pairFiniteGood i j := by
  intro p hp
  exact pairCrossingSet_finite_of_circle_ne_of_nonparallel hp.1 hp.2

/-- Translate one parameter in an arrangement parameter vector. -/
def translateParameterAt {n : ℕ}
    (p : Lower.ArrangementParameter n) (k : Fin n) (v : Point) :
    Lower.ArrangementParameter n :=
  fun a =>
    if _h : a = k then
      ⟨((p a).1.1 + v, (p a).1.2), (p a).2⟩
    else p a

@[simp] theorem translateParameterAt_zero {n : ℕ}
    (p : Lower.ArrangementParameter n) (k : Fin n) :
    translateParameterAt p k 0 = p := by
  funext a
  by_cases ha : a = k
  · simp [translateParameterAt, ha]
  · simp [translateParameterAt, ha]

theorem translateParameterAt_apply_self {n : ℕ}
    (p : Lower.ArrangementParameter n) (k : Fin n) (v : Point) :
    (translateParameterAt p k v).toArrangement k =
      TranslationGenericity.translate (p.toArrangement k) v := by
  ext <;>
    simp [translateParameterAt, Lower.ArrangementParameter.toArrangement,
      Lower.LollipopParameter.toLollipop, TranslationGenericity.translate]

theorem translateParameterAt_apply_ne {n : ℕ}
    (p : Lower.ArrangementParameter n) {a k : Fin n} (v : Point)
    (hak : a ≠ k) :
    (translateParameterAt p k v).toArrangement a =
      p.toArrangement a := by
  simp [translateParameterAt, Lower.ArrangementParameter.toArrangement, hak]

/-- The one-parameter translation path is continuous in the raw center/radial
parameter space. -/
theorem continuous_translateParameterAt {n : ℕ}
    (p : Lower.ArrangementParameter n) (k : Fin n) :
    Continuous (fun v : Point => translateParameterAt p k v) := by
  apply continuous_pi
  intro a
  by_cases ha : a = k
  · rw [continuous_induced_rng]
    change Continuous (fun v : Point => (translateParameterAt p k v a).1)
    simp [translateParameterAt, ha]
    constructor <;> fun_prop
  · rw [show (fun v : Point => translateParameterAt p k v a) =
        fun _v : Point => p a by
      funext v
      simp [translateParameterAt, ha]]
    exact continuous_const

/-- Two-lollipop arrangement used to feed the translation-avoidance theorem
for a fixed old pair. -/
def twoArrangement (L M : Lollipop) : Arrangement 2 :=
  fun a => if a = (0 : Fin 2) then L else M

@[simp] theorem twoArrangement_zero (L M : Lollipop) :
    twoArrangement L M (0 : Fin 2) = L := by
  simp [twoArrangement]

@[simp] theorem twoArrangement_one (L M : Lollipop) :
    twoArrangement L M (1 : Fin 2) = M := by
  simp [twoArrangement]

theorem pairFinite_twoArrangement_of_finite {L M : Lollipop}
    (hfinite : (L.carrier ∩ M.carrier).Finite) :
    TranslationGenericity.PairFiniteArrangement (twoArrangement L M) := by
  intro a b hab
  fin_cases a <;> fin_cases b
  · exact False.elim (hab rfl)
  · simpa using hfinite
  · simpa [Set.inter_comm] using hfinite
  · exact False.elim (hab rfl)

/-- Local triple-contact avoidance for one ordered triple.

If the first two carriers already have finite contact, then translating the
third lollipop inside any open parameter neighborhood avoids common points of
the three selected carriers.  This is the bridge from the tracked
`TranslationGenericity` module to the remaining finite-avoidance theorem. -/
theorem exists_mem_open_not_tripleBadSet_of_pairFinite_at {n : ℕ}
    {p : Lower.ArrangementParameter n} {i j k : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hfinite :
      ((p.toArrangement i).carrier ∩
        (p.toArrangement j).carrier).Finite)
    {U : Set (Lower.ArrangementParameter n)} (hU : IsOpen U)
    (hpU : p ∈ U) :
    ∃ q : Lower.ArrangementParameter n,
      q ∈ U ∧
        q ∉ Lower.GenericityPort.tripleBadSet i j k hij hik hjk := by
  classical
  let Aij : Arrangement 2 :=
    twoArrangement (p.toArrangement i) (p.toArrangement j)
  have hAijFinite : TranslationGenericity.PairFiniteArrangement Aij := by
    simpa [Aij] using pairFinite_twoArrangement_of_finite hfinite
  let γ : Point → Lower.ArrangementParameter n :=
    fun v => translateParameterAt p k v
  have hγcont : Continuous γ :=
    continuous_translateParameterAt p k
  have hpreOpen : IsOpen (γ ⁻¹' U) := hU.preimage hγcont
  have hzero : (0 : Point) ∈ γ ⁻¹' U := by
    change γ 0 ∈ U
    simpa [γ] using hpU
  obtain ⟨v, hvU, havoid⟩ :=
    TranslationGenericity.exists_mem_open_noTripleContactWithInserted_translate
      Aij (p.toArrangement k) hAijFinite hpreOpen hzero
  refine ⟨γ v, hvU, ?_⟩
  intro hbad
  rcases hbad with ⟨x, hx⟩
  rcases hx with ⟨hxij, hxk⟩
  rcases hxij with ⟨hxi, hxj⟩
  have hxiOld : x ∈ (p.toArrangement i).carrier := by
    simpa [γ, Lower.ArrangementParameter.toArrangement, translateParameterAt,
      hik] using hxi
  have hxjOld : x ∈ (p.toArrangement j).carrier := by
    simpa [γ, Lower.ArrangementParameter.toArrangement, translateParameterAt,
      hjk] using hxj
  have hxkNew :
      x ∈ (TranslationGenericity.translate (p.toArrangement k) v).carrier := by
    simpa [γ, Lower.ArrangementParameter.toArrangement, translateParameterAt,
      Lower.LollipopParameter.toLollipop, TranslationGenericity.translate]
      using hxk
  have hdisj := havoid (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)
  exact Set.disjoint_left.mp hdisj
    (by simpa [Aij] using (show x ∈ (Aij (0 : Fin 2)).carrier ∩
        (TranslationGenericity.translate (p.toArrangement k) v).carrier from
        ⟨hxiOld, hxkNew⟩))
    (by simpa [Aij] using (show x ∈ (Aij (1 : Fin 2)).carrier ∩
        (TranslationGenericity.translate (p.toArrangement k) v).carrier from
        ⟨hxjOld, hxkNew⟩))

/-- Fixed-triple density is reduced to density of finite contact for the
first selected pair. -/
theorem dense_orderedTripleGood_of_pairFiniteGood_dense {n : ℕ}
    (t : OrderedTripleIndex n)
    (hdense : Dense (pairFiniteGood t.1.1 t.1.2.1)) :
    Dense (orderedTripleGood t) := by
  rw [dense_iff_inter_open]
  intro U hU hUne
  rcases hdense.exists_mem_open hU hUne with ⟨p, hpfinite, hpU⟩
  rcases
    exists_mem_open_not_tripleBadSet_of_pairFinite_at
      t.2.1 t.2.2.1 t.2.2.2 hpfinite hU hpU with
    ⟨q, hqU, hqgood⟩
  exact ⟨q, hqU, by simpa [orderedTripleGood] using hqgood⟩

/-- Fixed-triple density is also reduced to density of the stronger elementary
pair-regular locus. -/
theorem dense_orderedTripleGood_of_pairRegularGood_dense {n : ℕ}
    (t : OrderedTripleIndex n)
    (hdense : Dense (pairRegularGood t.1.1 t.1.2.1)) :
    Dense (orderedTripleGood t) :=
  dense_orderedTripleGood_of_pairFiniteGood_dense t
    (hdense.mono (pairRegularGood_subset_pairFiniteGood t.1.1 t.1.2.1))


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
