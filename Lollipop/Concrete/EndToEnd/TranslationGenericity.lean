import Lollipop.Concrete.EndToEnd.CarrierAvoidance
import Lollipop.Concrete.EndToEnd.InsertionFan
import Mathlib.Tactic

/-!
# Translation genericity

This module proves the finite-avoidance step used to remove triple contacts
when inserting one lollipop into an arrangement whose old pair-contact sets
are finite.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace TranslationGenericity

open Set

/-- Translate a concrete lollipop by moving its center and retaining its
radial vector. -/
def translate (L : Lollipop) (v : Point) : Lollipop where
  center := L.center + v
  radial := L.radial
  radial_ne_zero := L.radial_ne_zero

/-- The lollipop carrier in translation-parameter space forbidden by one
ambient point `p`. -/
def translationForbidden (L : Lollipop) (p : Point) : Lollipop where
  center := p - L.center
  radial := -L.radial
  radial_ne_zero := by
    intro h
    exact L.radial_ne_zero (neg_eq_zero.mp h)

@[simp] theorem translate_radius (L : Lollipop) (v : Point) :
    (translate L v).radius = L.radius := by
  rfl

@[simp] theorem translationForbidden_radius (L : Lollipop) (p : Point) :
    (translationForbidden L p).radius = L.radius := by
  simp [translationForbidden, Lollipop.radius]

theorem mem_translate_circle_iff (L : Lollipop) (v x : Point) :
    x ∈ (translate L v).circle ↔ x - v ∈ L.circle := by
  have hvec : x - (L.center + v) = (x - v) - L.center := by
    module
  change ‖x - (L.center + v)‖ = L.radius ↔
    ‖(x - v) - L.center‖ = L.radius
  rw [hvec]

theorem mem_translate_stem_iff (L : Lollipop) (v x : Point) :
    x ∈ (translate L v).stem ↔ x - v ∈ L.stem := by
  constructor
  · rintro ⟨t, ht, htx⟩
    refine ⟨t, ht, ?_⟩
    rw [htx]
    change L.center + v + t • L.radial - v =
      L.center + t • L.radial
    module
  · rintro ⟨t, ht, htx⟩
    refine ⟨t, ht, ?_⟩
    change x = L.center + v + t • L.radial
    calc
      x = (x - v) + v := by module
      _ = (L.center + t • L.radial) + v := by rw [htx]
      _ = L.center + v + t • L.radial := by module

theorem mem_translate_carrier_iff (L : Lollipop) (v x : Point) :
    x ∈ (translate L v).carrier ↔ x - v ∈ L.carrier := by
  simp only [Lollipop.carrier, mem_union,
    mem_translate_circle_iff, mem_translate_stem_iff]

theorem mem_translationForbidden_circle_iff
    (L : Lollipop) (p v : Point) :
    v ∈ (translationForbidden L p).circle ↔ p - v ∈ L.circle := by
  have hvec :
      v - (p - L.center) = -((p - v) - L.center) := by
    module
  unfold translationForbidden
  change ‖v - (p - L.center)‖ = ‖-L.radial‖ ↔
    ‖(p - v) - L.center‖ = L.radius
  rw [hvec, norm_neg]
  simp [Lollipop.radius]

theorem mem_translationForbidden_stem_iff
    (L : Lollipop) (p v : Point) :
    v ∈ (translationForbidden L p).stem ↔ p - v ∈ L.stem := by
  constructor
  · rintro ⟨t, ht, htv⟩
    refine ⟨t, ht, ?_⟩
    rw [htv]
    change p - (p - L.center + t • -L.radial) =
      L.center + t • L.radial
    module
  · rintro ⟨t, ht, htp⟩
    refine ⟨t, ht, ?_⟩
    change v = p - L.center + t • -L.radial
    calc
      v = p - (p - v) := by module
      _ = p - (L.center + t • L.radial) := by rw [htp]
      _ = p - L.center + t • -L.radial := by module

theorem mem_translationForbidden_carrier_iff
    (L : Lollipop) (p v : Point) :
    v ∈ (translationForbidden L p).carrier ↔ p - v ∈ L.carrier := by
  simp only [Lollipop.carrier, mem_union,
    mem_translationForbidden_circle_iff,
    mem_translationForbidden_stem_iff]

theorem mem_translate_carrier_iff_mem_translationForbidden
    (L : Lollipop) (p v : Point) :
    p ∈ (translate L v).carrier ↔
      v ∈ (translationForbidden L p).carrier := by
  rw [mem_translate_carrier_iff,
    mem_translationForbidden_carrier_iff]

/-- Avoid finitely many prescribed points on a translated carrier while
choosing the translation vector in an arbitrary nonempty open set. -/
theorem exists_mem_open_forall_not_mem_translate_carrier
    (L : Lollipop) (P : Finset Point)
    {U : Set Point} (hU : IsOpen U) {v₀ : Point} (hv₀ : v₀ ∈ U) :
    ∃ v : Point, v ∈ U ∧
      ∀ p : Point, p ∈ P → p ∉ (translate L v).carrier := by
  classical
  induction P using Finset.induction_on generalizing U v₀ with
  | empty =>
      exact ⟨v₀, hv₀, by simp⟩
  | insert p P hp ih =>
      obtain ⟨w, hwU, hwp⟩ :=
        EndToEnd.Lollipop.exists_mem_open_not_mem_carrier
          (translationForbidden L p) hU hv₀
      let V : Set Point := U ∩ (translationForbidden L p).carrierᶜ
      have hVopen : IsOpen V :=
        hU.inter ((translationForbidden L p).isClosed_carrier).isOpen_compl
      have hwV : w ∈ V := ⟨hwU, hwp⟩
      obtain ⟨v, hvV, havoid⟩ := ih hVopen hwV
      refine ⟨v, hvV.1, ?_⟩
      intro q hq
      rw [Finset.mem_insert] at hq
      rcases hq with rfl | hq
      · intro hpv
        exact hvV.2
          ((mem_translate_carrier_iff_mem_translationForbidden L q v).mp hpv)
      · exact havoid q hq

/-- Pairwise finiteness of old carrier intersections. -/
def PairFiniteArrangement {n : ℕ} (A : Arrangement n) : Prop :=
  ∀ i j : Fin n, i ≠ j → ((A i).carrier ∩ (A j).carrier).Finite

/-- No finite point of the inserted carrier lies on two distinct old
carriers. -/
def NoTripleContactWithInserted {n : ℕ}
    (A : Arrangement n) (L : Lollipop) : Prop :=
  ∀ ⦃i j : Fin n⦄, i ≠ j →
    Disjoint ((A i).carrier ∩ L.carrier)
      ((A j).carrier ∩ L.carrier)

/-- Contact finiteness between every old carrier and one inserted carrier. -/
def PairContactsFinite {n : ℕ} (A : Arrangement n) (L : Lollipop) : Prop :=
  ∀ i : Fin n, ((A i).carrier ∩ L.carrier).Finite

/-- No point lies on three pairwise-distinct carriers.  This unordered form is
the invariant used by the insertion-order genericization route. -/
def NoTripleCarrierPoints {n : ℕ} (A : Arrangement n) : Prop :=
  ∀ i j k : Fin n,
    i ≠ j → i ≠ k → j ≠ k →
      Disjoint
        ((A i).carrier ∩ (A k).carrier)
        ((A j).carrier ∩ (A k).carrier)

/-- Pairwise finiteness is preserved when the appended lollipop has finite
contact with every old carrier. -/
theorem pairFiniteArrangement_snoc
    {n : ℕ} {A : Arrangement n} {L : Lollipop}
    (hA : PairFiniteArrangement A)
    (hL : PairContactsFinite A L) :
    PairFiniteArrangement (Insertion.snocArrangement A L) := by
  intro i j hij
  by_cases hi : i.1 < n
  · by_cases hj : j.1 < n
    · have hijOld : (⟨i.1, hi⟩ : Fin n) ≠ ⟨j.1, hj⟩ := by
        intro h
        apply hij
        exact Fin.ext (congrArg (fun x : Fin n => x.1) h)
      simpa [Insertion.snocArrangement, hi, hj] using
        hA ⟨i.1, hi⟩ ⟨j.1, hj⟩ hijOld
    · simpa [Insertion.snocArrangement, hi, hj] using hL ⟨i.1, hi⟩
  · by_cases hj : j.1 < n
    · simpa [Insertion.snocArrangement, hi, hj, inter_comm] using
        hL ⟨j.1, hj⟩
    · have hieq := Insertion.fin_eq_last_of_not_lt hi
      have hjeq := Insertion.fin_eq_last_of_not_lt hj
      exact (hij (hieq.trans hjeq.symm)).elim

/-- Global no-triple position is preserved by appending a lollipop satisfying
the old/new no-triple contact condition. -/
theorem noTripleCarrierPoints_snoc
    {n : ℕ} {A : Arrangement n} {L : Lollipop}
    (hA : NoTripleCarrierPoints A)
    (hL : NoTripleContactWithInserted A L) :
    NoTripleCarrierPoints (Insertion.snocArrangement A L) := by
  intro i j k hij hik hjk
  rw [Set.disjoint_left]
  intro x hxi hxj
  by_cases hkOld : k.1 < n
  · by_cases hiOld : i.1 < n
    · by_cases hjOld : j.1 < n
      · have hijOld : (⟨i.1, hiOld⟩ : Fin n) ≠ ⟨j.1, hjOld⟩ := by
          intro h
          apply hij
          exact Fin.ext (congrArg (fun x : Fin n => x.1) h)
        have hikOld : (⟨i.1, hiOld⟩ : Fin n) ≠ ⟨k.1, hkOld⟩ := by
          intro h
          apply hik
          exact Fin.ext (congrArg (fun x : Fin n => x.1) h)
        have hjkOld : (⟨j.1, hjOld⟩ : Fin n) ≠ ⟨k.1, hkOld⟩ := by
          intro h
          apply hjk
          exact Fin.ext (congrArg (fun x : Fin n => x.1) h)
        have hd := hA ⟨i.1, hiOld⟩ ⟨j.1, hjOld⟩
          ⟨k.1, hkOld⟩ hijOld hikOld hjkOld
        exact Set.disjoint_left.mp hd
          ⟨by simpa [Insertion.snocArrangement, hiOld] using hxi.1,
            by simpa [Insertion.snocArrangement, hkOld] using hxi.2⟩
          ⟨by simpa [Insertion.snocArrangement, hjOld] using hxj.1,
            by simpa [Insertion.snocArrangement, hkOld] using hxj.2⟩
      · have hikOld : (⟨i.1, hiOld⟩ : Fin n) ≠ ⟨k.1, hkOld⟩ := by
          intro h
          apply hik
          exact Fin.ext (congrArg (fun x : Fin n => x.1) h)
        have hd := hL hikOld
        exact Set.disjoint_left.mp hd
          ⟨by simpa [Insertion.snocArrangement, hiOld] using hxi.1,
            by simpa [Insertion.snocArrangement, hjOld] using hxj.1⟩
          ⟨by simpa [Insertion.snocArrangement, hkOld] using hxi.2,
            by simpa [Insertion.snocArrangement, hjOld] using hxj.1⟩
    · have hiLast := Insertion.fin_eq_last_of_not_lt hiOld
      have hjOld : j.1 < n := by
        by_contra hjNotOld
        have hjLast := Insertion.fin_eq_last_of_not_lt hjNotOld
        exact hij (hiLast.trans hjLast.symm)
      have hjkOld : (⟨j.1, hjOld⟩ : Fin n) ≠ ⟨k.1, hkOld⟩ := by
        intro h
        apply hjk
        exact Fin.ext (congrArg (fun x : Fin n => x.1) h)
      have hd := hL hjkOld
      exact Set.disjoint_left.mp hd
        ⟨by simpa [Insertion.snocArrangement, hjOld] using hxj.1,
          by simpa [Insertion.snocArrangement, hiOld] using hxi.1⟩
        ⟨by simpa [Insertion.snocArrangement, hkOld] using hxi.2,
          by simpa [Insertion.snocArrangement, hiOld] using hxi.1⟩
  · have hkLast := Insertion.fin_eq_last_of_not_lt hkOld
    have hiOld : i.1 < n := by
      by_contra hiNotOld
      have hiLast := Insertion.fin_eq_last_of_not_lt hiNotOld
      exact hik (hiLast.trans hkLast.symm)
    have hjOld : j.1 < n := by
      by_contra hjNotOld
      have hjLast := Insertion.fin_eq_last_of_not_lt hjNotOld
      exact hjk (hjLast.trans hkLast.symm)
    have hijOld : (⟨i.1, hiOld⟩ : Fin n) ≠ ⟨j.1, hjOld⟩ := by
      intro h
      apply hij
      exact Fin.ext (congrArg (fun x : Fin n => x.1) h)
    have hd := hL hijOld
    exact Set.disjoint_left.mp hd
      ⟨by simpa [Insertion.snocArrangement, hiOld] using hxi.1,
        by simpa [Insertion.snocArrangement, hkOld] using hxi.2⟩
      ⟨by simpa [Insertion.snocArrangement, hjOld] using hxj.1,
        by simpa [Insertion.snocArrangement, hkOld] using hxj.2⟩

/-- Union of old pair-contact sets over a finite collection of index pairs. -/
def oldPairContactUnionOn {n : ℕ} (A : Arrangement n)
    (s : Finset (Fin n × Fin n)) : Set Point :=
  InsertionFan.finsetSetUnion s
    (fun p => (A p.1).carrier ∩ (A p.2).carrier)

/-- The finite set of all contacts between distinct old lollipops. -/
def oldDoublePointSet {n : ℕ} (A : Arrangement n) : Set Point :=
  oldPairContactUnionOn A (pairFinset n)

theorem oldPairContactUnionOn_finite
    {n : ℕ} {A : Arrangement n}
    (hfinite : PairFiniteArrangement A)
    (s : Finset (Fin n × Fin n))
    (hdiag : ∀ p ∈ s, p.1 ≠ p.2) :
    (oldPairContactUnionOn A s).Finite := by
  exact InsertionFan.finite_finsetSetUnion s
    (fun p => (A p.1).carrier ∩ (A p.2).carrier)
    (fun p hp => hfinite p.1 p.2 (hdiag p hp))

theorem oldDoublePointSet_finite
    {n : ℕ} {A : Arrangement n}
    (hfinite : PairFiniteArrangement A) :
    (oldDoublePointSet A).Finite := by
  apply oldPairContactUnionOn_finite hfinite
  intro p hp
  rw [pairFinset, Finset.mem_filter] at hp
  exact ne_of_lt hp.2

theorem pair_inter_subset_oldDoublePointSet
    {n : ℕ} (A : Arrangement n) {i j : Fin n} (hij : i ≠ j) :
    (A i).carrier ∩ (A j).carrier ⊆ oldDoublePointSet A := by
  intro x hx
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · apply (InsertionFan.mem_finsetSetUnion_iff (pairFinset n)
      (fun p => (A p.1).carrier ∩ (A p.2).carrier) x).2
    exact ⟨(i, j), by simp [pairFinset, hijlt], hx⟩
  · apply (InsertionFan.mem_finsetSetUnion_iff (pairFinset n)
      (fun p => (A p.1).carrier ∩ (A p.2).carrier) x).2
    exact ⟨(j, i), by simp [pairFinset, hjilt], ⟨hx.2, hx.1⟩⟩

theorem noTripleContactWithInserted_translate_of_disjoint_oldDoublePointSet
    {n : ℕ} (A : Arrangement n) (L : Lollipop) (v : Point)
    (hdisj : Disjoint (translate L v).carrier (oldDoublePointSet A)) :
    NoTripleContactWithInserted A (translate L v) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro x hxi hxj
  exact Set.disjoint_left.mp hdisj hxi.2
    (pair_inter_subset_oldDoublePointSet A hij ⟨hxi.1, hxj.1⟩)

/-- In every nonempty open neighborhood of translation space there is a
translation eliminating all triple contacts with a pairwise-finite old
arrangement. -/
theorem exists_mem_open_noTripleContactWithInserted_translate
    {n : ℕ} (A : Arrangement n) (L : Lollipop)
    (hfinite : PairFiniteArrangement A)
    {U : Set Point} (hU : IsOpen U) {v₀ : Point} (hv₀ : v₀ ∈ U) :
    ∃ v : Point, v ∈ U ∧
      NoTripleContactWithInserted A (translate L v) := by
  classical
  let P : Set Point := oldDoublePointSet A
  have hP : P.Finite := oldDoublePointSet_finite hfinite
  obtain ⟨v, hvU, havoid⟩ :=
    exists_mem_open_forall_not_mem_translate_carrier
      L hP.toFinset hU hv₀
  have hdisj : Disjoint (translate L v).carrier P := by
    rw [Set.disjoint_left]
    intro p hpL hpP
    exact havoid p (hP.mem_toFinset.mpr hpP) hpL
  exact ⟨v, hvU,
    noTripleContactWithInserted_translate_of_disjoint_oldDoublePointSet
      A L v hdisj⟩

/-- Metric form: the triple-removing translation can be chosen with
arbitrarily small norm. -/
theorem exists_norm_lt_noTripleContactWithInserted_translate
    {n : ℕ} (A : Arrangement n) (L : Lollipop)
    (hfinite : PairFiniteArrangement A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : Point, ‖v‖ < ε ∧
      NoTripleContactWithInserted A (translate L v) := by
  have hzero : (0 : Point) ∈ Metric.ball (0 : Point) ε := by
    simpa [Metric.mem_ball] using hε
  obtain ⟨v, hv, htriple⟩ :=
    exists_mem_open_noTripleContactWithInserted_translate
      A L hfinite Metric.isOpen_ball hzero
  refine ⟨v, ?_, htriple⟩
  simpa [Metric.mem_ball, dist_eq_norm] using hv

/-- The old/new pair profiles are constant throughout a prescribed open ball
of translation parameters.  This is the stability input needed when the lower
construction removes triple contacts without changing the extremal pair
table. -/
def PairProfilesStableInBall {n : ℕ} (A : Arrangement n) (L : Lollipop)
    (ε : ℝ) : Prop :=
  ∀ v : Point, ‖v‖ < ε → ∀ i : Fin n,
    pairExcess (A i) (translate L v) = pairExcess (A i) L

/-- One insertion-order genericization step.

If all sufficiently small translations retain finite contact with every old
carrier, then one can choose such a translation which simultaneously preserves
pairwise finiteness and extends global no-triple position. -/
theorem exists_norm_lt_pairFinite_noTriple_snoc_translate
    {n : ℕ} (A : Arrangement n) (L : Lollipop)
    (hfinite : PairFiniteArrangement A)
    (htriple : NoTripleCarrierPoints A)
    {ε : ℝ} (hε : 0 < ε)
    (hcontacts : ∀ v : Point, ‖v‖ < ε →
      PairContactsFinite A (translate L v)) :
    ∃ v : Point, ‖v‖ < ε ∧
      PairFiniteArrangement (Insertion.snocArrangement A (translate L v)) ∧
      NoTripleCarrierPoints (Insertion.snocArrangement A (translate L v)) := by
  obtain ⟨v, hv, hnewTriple⟩ :=
    exists_norm_lt_noTripleContactWithInserted_translate A L hfinite hε
  exact ⟨v, hv,
    pairFiniteArrangement_snoc hfinite (hcontacts v hv),
    noTripleCarrierPoints_snoc htriple hnewTriple⟩

/-- The same one-step choice can retain every old/new pair profile.

The stability hypothesis is deliberately explicit: this theorem supplies the
finite avoidance and append bookkeeping, while the analytic proof that a
suitable profile-stability ball exists remains a separate target. -/
theorem exists_norm_lt_preservePairProfiles_pairFinite_noTriple_snoc_translate
    {n : ℕ} (A : Arrangement n) (L : Lollipop)
    (hfinite : PairFiniteArrangement A)
    (htriple : NoTripleCarrierPoints A)
    {ε : ℝ} (hε : 0 < ε)
    (hcontacts : ∀ v : Point, ‖v‖ < ε →
      PairContactsFinite A (translate L v))
    (hprofiles : PairProfilesStableInBall A L ε) :
    ∃ v : Point, ‖v‖ < ε ∧
      (∀ i : Fin n,
        pairExcess (A i) (translate L v) = pairExcess (A i) L) ∧
      PairFiniteArrangement (Insertion.snocArrangement A (translate L v)) ∧
      NoTripleCarrierPoints (Insertion.snocArrangement A (translate L v)) := by
  obtain ⟨v, hv, hpair, hglobal⟩ :=
    exists_norm_lt_pairFinite_noTriple_snoc_translate
      A L hfinite htriple hε hcontacts
  exact ⟨v, hv, hprofiles v hv, hpair, hglobal⟩

end TranslationGenericity
end EndToEnd
end Concrete
end Lollipop
