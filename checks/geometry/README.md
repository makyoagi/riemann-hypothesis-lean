# Checking the divisor geometry experiment

The original divisor witness has a geometry field and a `LamAre` field. For
the geometry predicate used on the RH path, the closed witness at fixed rows
`t` and divisor `X` is equivalent to `PLift (LamAre t.r.Z X)`. The inverse
map supplies `GeoCl.base True.intro` and the same proof of `LamAre`.
The original equivalence and both inverse laws are in
`original/BaselineEquivalence.lean`.

On this branch, `OAt none t X` reduces to a record with just that `LamAre`
field. A caller with a geometric requirement can use `OAt (some P) t X`.
The following commands use the Lean and Mathlib versions pinned in the
checkout. Start in the repository root on the experiment branch.

```sh
geometry_checks="$PWD/checks/geometry"
lake exe cache get
lake build Main
lake env lean "$geometry_checks/AblatedWitness.lean"
lake env lean "$geometry_checks/CheckRH.lean"
lake env lean "$geometry_checks/CheckAblatedMain.lean"
lake env lean "$geometry_checks/StrongGeometry.lean"
```

`CheckRH.lean` spells out Mathlib's zero statement and checks definitional
equality by `rfl`. `CheckAblatedMain.lean` asserts that both deleted names
are absent from the environment imported by `Main` and that the axiom set of
`riemannHypothesis` is exactly `propext`, `Classical.choice` and `Quot.sound`.

`StrongGeometry.lean` checks a different claim. Requiring the repository's
`geoOf Q`, even under `GeoCl`, implies that the divisor's surface type is
inhabited. The explicit divisor used in the construction has surface type
`Empty`. The test proves the obstruction for this witness and every kit
class `Q`. A construction using a different witness is a separate question.

To run the baseline checks, continue in the same shell. The original
equivalence uses the declarations from the pinned mirror revision.

```sh
git worktree add --detach ../rh-geometry-base 7cbf7a0c32fca1badf05931879a37c3f8a2b03b4
(
  set -e
  cd ../rh-geometry-base
  lake exe cache get
  lake build Main
  lake env lean "$geometry_checks/CheckRH.lean"
  lake env lean "$geometry_checks/original/BaselineEquivalence.lean"
  lake env lean "$geometry_checks/StrongGeometry.lean"
)
```

The negative control in `original/StrongAttempt.lean` applies the original
`divEx_prov` construction to `geoOf Q`. To display its remaining goal, run
`(cd ../rh-geometry-base && lake env lean "$geometry_checks/original/StrongAttempt.lean")`.
This file is expected to exit with an error at `assumption` after Lean accepts
the `LamAre` field. The goal asks for a positive index, an `IsGeoOf` witness
and `HasTrueSurf O.X`.
