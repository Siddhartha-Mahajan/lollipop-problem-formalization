# Main-Theorem-First Directive

Date: 2026-06-24

## User Directive

Verbatim instruction to preserve the project direction:

> dont work by adding supporting lemmas first, first create all the main theorem files we need for complete formalization and you can fill the ones we havent done with sorry. then slowlly slowly work on removing each sorry one by one. make sure you store this message of mine somewhere

## Operational Rule

From this point, new supporting lemmas should be added only when they remove
or directly prepare removal of a named `sorry` in the main theorem spine.

The theorem spine is:

1. `Lollipop/Concrete/EndToEnd/MainTheorem/Topology.lean`
2. `Lollipop/Concrete/EndToEnd/MainTheorem/Genericity.lean`
3. `Lollipop/Concrete/EndToEnd/MainTheorem/Assembly.lean`

The current intended `sorry` targets are:

1. `MainTheorem.Topology.firstInsertionLocalizedFiltration`
2. `MainTheorem.Topology.firstInsertionLocalizedExactFiltration`
3. `MainTheorem.Topology.localizedInsertionFiltration_bound_positive`
4. `MainTheorem.Topology.localizedExactInsertionFiltration_of_generic_positive`
5. `MainTheorem.Genericity.dense_compl_tripleBadUnion_ge_three`

Everything else in the final assembly should be ordinary wiring from those
named theorem targets into the existing concrete endpoint.
