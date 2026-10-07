# Plan: closing the last gap (carrier cutting) — working notes

Branch: `close-remaining-gaps`. Goal: remove the single remaining `sorry`
(`effectiveLocalizedCarrierSubdivisionData_exists`, archived in
`old_lean_folder/Concrete/EndToEnd/MainTheorem/PositiveInsertionSubdivision.lean`)
and make Proposition 2.1 and Theorem 1.1 unconditional in the numbered tree.

## What the sorry asks for
For an arrangement prefix with carrier `C = occupied (prefix k)` (closed) and new
lollipop `L`, with `0 < k` and `L.carrier ⊄ C`:

* a localized edge filtration `C = D_0 ⊆ D_1 ⊆ … ⊆ D_m = C ∪ L.carrier` with
  `m ≤ componentCount (insertionFan A k hk)`, every step an edge insertion that
  splits at most one old complementary component into two;
* if `A` is generic: an *exact* filtration of length exactly
  `componentCount (insertionFan A k hk)` (every step splits exactly one face).

## Proof strategy (replaces A397182's polygonal path surgery)

1. **Two-collar lemma** (pure point-set topology). Let `O` be a face of `D`
   (component of `Dᶜ`), `E` closed with `E ∩ O ≠ ∅` and `E ∩ O ⊆ U` for an open
   `U`, and let `S₁ S₂ ⊆ O \ E` be preconnected with `U \ E ∩ O ⊆ S₁ ∪ S₂`.
   Then `O \ E` has at most two components (every component `W` has a boundary
   point `z ∈ E ∩ O` because `O` is connected and `W ≠ O`; `W` then meets `U \ E`).
   This gives the injective `Fin 2` classifier of `LocalizedEdgeStep`.
2. **Exactness** via the Jordan curve theorem: `J = E ∪ P` with `P ⊆ D̂` an arc
   through `∞` if needed. The two collars at one point `z ∈ E` lie in different
   components of `J`ᶜ: if both lay in the same Jordan component `A`, then a small
   ball `N` around `z` satisfies `N ∩ B = ∅`, so `A ∪ (J ∩ N) ∪ B = ℝ² \ (J \ N)`
   would be disconnected, contradicting non-separation by the simple arc
   `J \ N` (A397182 `SimpleArcComplement`).  No frontier theorem is needed.
3. **Tubes** supply `U, S₁, S₂`: polar tubes around circle arcs, strip tubes
   around stem segments/rays (images of `Ioo × Ioo` under explicit continuous
   maps, so connectedness is free).
4. **Leaf steps** (free, count 0): a stem piece with a free end in the face adds
   no component (ball around the free end minus the segment is star-shaped).
5. **Counting** by representatives: choose one point per component of the
   compactified intersection `K̂ = L̂ ∩ Ĉ`, together with the anchor; cut the
   circle and the stem there.  Every counted arc `[p,p']` has `E \ D` a connected
   open arc because every component of `K̂` meeting the open arc contains `p`
   or `p'` and `Z ∩ arc` is an initial/final segment (`IsPreconnected.subset_or_subset`).
   Number of counted arcs = number of representatives (= `componentCount fan`,
   one less if the circle lies inside `K`).
6. Order: if `anchor ∉ C`, insert the first stem piece as a free leaf; then all
   circle arcs (anchor is now a vertex), then the remaining stem pieces.

## Order of work
M1 two-collar step lemma (+ exact variant)            [Lollipop/Topology/Collar.lean]
M2 tubes: circle arc, stem segment/ray                 [.../Tubes.lean]
M3 free-leaf lemma and chain `snocFree`                [.../Leaf.lean, ComponentSplitChain]
M4 1-D arc/representative lemmas                       [.../Arcs.lean]
M5 chain assembly: bounded filtration                  [.../Cutting.lean]
M6 sphere + Jordan separation, arc connectivity        [.../SphereSep.lean]
M7 exact filtration for generic arrangements           [.../CuttingExact.lean]
M8 port archived pipeline, remove sorry, restate Prop 2.1 / Thm 1.1, audit

Status log: see git history on `close-remaining-gaps`.
