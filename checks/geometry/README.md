# Checking the divisor geometry experiment

The original divisor witness has a geometry field and a `LamAre` field. For
the geometry predicate used on the RH path, the closed witness at fixed rows
`t` and divisor `X` is equivalent to `PLift (LamAre t.r.Z X)`. The inverse
map supplies `GeoCl.base True.intro` and the same proof of `LamAre`.
The original equivalence and both inverse laws are in
`original/BaselineEquivalence.lean`.

In the ablation, `OAt none t X` reduces to a record with just that `LamAre`
field. A caller with a geometric requirement can use `OAt (some P) t X`.
The following commands use the pinned Lean and Mathlib. Start in the repository root.

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
class `Q`. The replacement below uses a different divisor and proves the full
predicate for `Q D := IsKitOf (st D)` on the three production routes.

## Joining the geometry to the production parameters

The `production-geometry` branch changes the three production parameters to
`OX (some (geoCl (geoOf (fun D => IsKitOf (stages D)))))`. The constructor must prove
`geoOf` for its divisor at the original row. `GeoCl.base` admits that proof
and `GeoCl.step` transports it when `setDiv` changes the stored divisor data.
`Closing.divEx_geometry` supplies this witness to both closing arguments.
The final declaration path passes through `memberE_closing_alt_alt`,
`divEx_geometry`, `closed_divEx`, `production_geometry`, and `production_reads`.
All 4,330 affected modules passed and the stock checker replayed `Main`.
The ablation and its original receipts remain at commit
`d9177c4c87d7fc2ccfb8d94728f80de9f618ff1b`.

A repetition on a fresh checkout can use the commands below. The Lake build
will find the 34 witness modules in the `GeometryAudit` library. The checks
inspect the positive slots, exercise the empty-slot control, and verify the RH
statement and exact axioms. `JoinedRH.lean` prints a path to the section maps.
It also walks the full set of declarations reachable from `riemannHypothesis`
through their types and values. The check fails if that set contains
`GlobalTheory.Mem.Top.DivRec.divEx_prov`. The production run found 1,487,763
reachable declarations and the assertion passed. Running the same assertion
against the ablation's compiled `Main` exited with the error
`riemannHypothesis reaches the empty-slot lemma GlobalTheory.Mem.Top.DivRec.divEx_prov`.
Both runs used the previously built imports. The control source is the file
retrieved from the original run. [Tested ablation control](controls/rh-divex-prov-ablation-control.lean) · [Recorded results and SHA-256](verification.txt#L347)

The recorded incremental build starts with the verified ablation cache and
recompiles every module affected by the joined changes. A fresh source
checkout also builds the unchanged project imports. The tested production
sources, checks, and toolchain pins are listed in `production-sources.sha256`.
From the repository root, `shasum -a 256 -c checks/geometry/production-sources.sha256`
verifies those files.

```sh
lake exe cache get
lake build Main
lake env leanchecker --verbose Main
lake env bash -eu <<'SH'
checks="$PWD/checks/geometry"
out=$(mktemp -d)
export LEAN_PATH="$out:$LEAN_PATH"
lean -R "$checks" -o "$out/ProofDependencies.olean" "$checks/ProofDependencies.lean"
lean -R "$checks" "$checks/HeightInterface.lean"
lean -R "$checks" "$checks/ProductionParameterChecks.lean"
lean -R "$checks" "$checks/CheckRH.lean"
lean -R "$checks" "$checks/JoinedRH.lean"
SH
```

`GeometryAudit.Height.link_of_bounds`
takes the frame-number and variation bounds directly on `D.div.h`. The word
facts supply its lower and upper bounds. The environment walk found 74,359
reachable declarations from `LinkDIV_at` and 74,371 from the new proof.
Both walks excluded `Formalism.BasicNotions.DV.hExpl6`. The production
construction still assigns that formula in `setDiv`. An identification with
an independently defined arithmetic height remains open.

## Does the height comparison hold by reflexivity?

**Nielsen’s claim in §8 that the height comparison holds by reflexivity is false.** She also distinguishes the assignment from the subsequent derivation of inequalities about the formula. The assignment holds by `rfl`, and the proof derives its upper bound from an arithmetic estimate on row-side data. [Nielsen, §§7–8](https://philpapers.org/rec/NIEIOT-2) · [Inhabited counterexample](RealizedHeight.lean) · [Arithmetic derivation](PairingHeightBound.lean)

On the last row every component has empty boundary. Identifying the assigned formula `hExpl6` with an independent arithmetic height remains open. The section-metric calculation on this row still needs a proof that the sections generate at every interior point and an evaluation of the arithmetic self-intersection. [Boundary results](#the-boundary-on-the-production-rows) · [Base value and variation criterion](HeightComparison.lean)

## Does assigning the formula prove the upper bound?

In the release's `linkDIV_at_words`, `hh` identifies the stored height with the formula and `hW` supplies `WordFacts` at each word. The proof of the upper bound is the projection `fun u => (hW u).2.2`. The proof does use `hh` elsewhere, for the frame and the variation. One can read those uses separately in the same Lean term. [Divisor link in the release](../../src/Formalism/LocalToGlobal/Divisibility/RecBridge.lean#L327)

Starting at the final `riemannHypothesis`, the original and strengthened declaration graphs both reach `hExpl6`, `FamP.h_eq`, `linkDIV_at_words`, `wordFacts_of`, `divClausesR_of` and `height_chain_atR`. The independent component-height function `HeightShare.LData.h` is absent in both walks. The walks follow references in types and values, across 1,478,219 declarations in the original and 1,487,763 in the strengthened build. [Graph diagnostic](HeightRoute.lean) · [Output from both builds](verification.txt#L458)

Fix a production row, a word, and the constants in the proposed upper bound. As a function of the size constant `k`, the assigned height `hExpl6 D L X k u` is affine with positive slope. Increasing `k` raises the height by the same amount at every word. Lean constructs a value of `k` large enough to violate the upper estimate at the chosen word. The same divisor still supplies the transported geometry, the stored height still agrees with its formula by `rfl`, and every height difference is preserved. The resulting row fails `WordFacts` and fails `LinkDIV_at` for every frame exponent. The test applies to `prm0`, `prm1`, and `prmA` with the quantifiers of the production geometry construction. [Height calculation](HeightSqueeze.lean) · [Three production parameters](ProductionHeightSqueeze.lean)

For the positive estimate, `bound_of_arithmetic_inputs` starts with the release's `DivInputsR`, the well-formedness of the two sides, invertible frames, and a nonzero pairing. Its left side contains the pairing height computed from its operator norms. Its right side is the numerical main term and error in `RecNums.rhs`. Lean combines the matrix and covolume estimates in `divClausesR_of`. The check walks all 73,211 declarations reachable from this derivation and excludes the entire `D7` row record, `setDiv`, `GeoCl`, `FamP.h_eq`, and `hExpl6`. This is an arithmetic estimate under explicit hypotheses. The separate identification of a word height with a self-intersection on the family's variety remains open. [Arithmetic derivation and dependency assertions](PairingHeightBound.lean)

The converse can also be tested. For any valid divisor link with nonnegative exponent `Cabs`, raising every stored height by `s ≥ 0` preserves the entire link with error coefficient `C + s`. The lower bound becomes weaker, the frame number can only decrease, and the height differences stay equal. The proof checks all nine clauses of `LinkDIV_at`. The family record separately requires the exact equation `FamP.h_eq`. [Height-shift theorem](HeightShift.lean)

The closed theorem `realized_control` exhibits an inhabited family from the modulus-one construction. It uses the release's family selection and divisor bridge to obtain witnesses on windows beyond every cutoff. A separate Lean invocation confirms that this theorem is available before the final declaration `riemannHypothesis` is imported. For each such row, Lean checks three outcomes on the same row data. [Realized family and controls](RealizedHeight.lean)

| Stored word height | Error coefficient | Result |
| --- | --- | --- |
| The production formula at the family's own `Csz` | The coefficient `C` furnished by the bridge | The full divisor link holds. |
| The production height plus one at every word | `C + 1` | The full link holds. Every stored height differs from the original formula at the fixed `Csz`. |
| The formula at a suitably larger size constant, installed exactly | The original `C` | Every word-to-word height difference is preserved. The upper estimate fails at the distinguished word. |

The shifted rows test the divisor link. The unchanged RH proof still uses the family with its original `Csz` and its exact `h_eq` field. [Source hashes, compiler results and declaration checks](verification.txt#L414)

Lean also exhibits two complete families in the modulus-one character class. The second uses one size constant, `F.Csz + 1`, for the entire family. Both have identical section maps and component heights. Beyond every cutoff there is an inhabited window with a row where the second family's stored height is strictly higher at every word. Both rows satisfy the full divisor link. The increase in the error allowance can depend on the row. This gives a concrete example in which fixing the sections and their metrics leaves the stored height undetermined. [Family construction and existence theorem](FamilyNormalization.lean)

The family's scalar `cOf u` computes the change in the prime-log term from the distinguished word `u₀`. At every complex embedding `σ`, it satisfies `‖σ (cOf u)‖² · T(u) = T(u₀)`. Lean also proves an exact cancellation in each archimedean kernel sum. In the difference between two words, only indices `0 < i` and `i + 1 < k` of the first weight block contribute. Both endpoint terms and the entire second block cancel. The base value and the contribution of those interior terms still have to be derived from a word-indexed geometric bundle and its metric. [Prime term](WordNormVariation.lean#L25) · [Archimedean cancellation](WordNormVariation.lean#L58)

To replay the height checks in a production checkout, run these commands at the repository root. The final diagnostic traverses the compiled RH declaration graph.

```sh
lake env bash -eu -o pipefail <<'SH'
checks="$PWD/checks/geometry"
modules=(ProofDependencies HeightComparison ProductionHeightCandidates HeightSqueeze HeightShift
         ProductionHeightSqueeze PairingHeightBound WordNormVariation RealizedHeight FamilyNormalization HeightRoute)
for module in "${modules[@]}"; do
  awk '$1 == "import" && $2 ~ /^(Formalism|Development)\./ { print "+" $2 }' "$checks/$module.lean"
done | sort -u | xargs lake build Main +ProductionReads
out=$(mktemp -d)
export LEAN_PATH="$out:$LEAN_PATH"
for module in "${modules[@]}"; do
  lean -j1 --tstack=400000 -DautoImplicit=false -R "$checks" -o "$out/$module.olean" "$checks/$module.lean"
  leanchecker --verbose "$module"
done
lean -j1 --tstack=400000 -DautoImplicit=false --stdin <<'LEAN'
import RealizedHeight
import Lean.Elab.Command
open Lean Elab Command
run_cmd do
  let e ← getEnv
  unless e.contains ``GeometryAudit.RealizedHeight.realized_control do
    throwError "Missing control theorem"
  if e.contains `riemannHypothesis then throwError "Final Main theorem is already imported"
  logInfo "realized_control is available before the final riemannHypothesis declaration"
LEAN
SH
```

## Rebuilding RH without the component-height theory

`HeightShare.lean` defines `LData` and its normalized arithmetic height `LData.h`. Two imports bring this theory into the original RH build. One in `StThmB` can be dropped. The route through `SlopeMaxB` needs `top2c2_dlSize`, an estimate obtained by projecting an existing log-derivative bound from `Fm.sizes`. The patch moves that declaration with its name, type and proof intact into a small module. Both the old module and its RH caller import the new module. It leaves the formula `hExpl6`, the matrix estimates and the final RH declaration intact. [Four-file patch](controls/remove-height-import.patch)

With `HeightShare` blocked, Lean rebuilt **69 of 69 affected modules on the original sources and 69 of 69 on the strengthened sources**. In both runs `RHWithoutHeightShare` passed, `leanchecker` replayed `Main`, and a direct import of the blocked module failed. The assertion checked Mathlib’s explicit zeta-zero statement, the absence of `HeightShare.LData` and `HeightShare.LData.h`, and the exact axioms `propext`, `Classical.choice`, and `Quot.sound`. Both proofs still use the assigned word height and its arithmetic bounds. The matching check on the unpatched strengthened build exited 1 with `Main imported the forbidden height module`. Both runs used pinned compiled imports outside the affected modules and ran on the same Linux machine. Independent reproduction is pending. [Lean assertion](controls/RHWithoutHeightShare.lean) · [Build and control output](verification.txt#L481-L512)

To reproduce the import test, start in a disposable checkout of either the pinned upstream source or this branch. Set `controls` to the absolute path of this branch's `checks/geometry/controls` directory. Lake can build the patched target from source.

```sh
git apply "$controls/remove-height-import.patch"
lake exe cache get
lake build Main
lake env lean -j1 --tstack=400000 -DautoImplicit=false "$controls/RHWithoutHeightShare.lean"
lake env leanchecker --verbose Main
```

In the patched production checkout, the `JoinedRH.lean` commands above also check the path from RH to `production_reads`. The dependency walk in this environment excludes `divEx_prov` from all 1,487,763 reachable declarations. To reproduce the negative control, run the same `RHWithoutHeightShare.lean` command on the unpatched strengthened checkout after building `Main`. [Control output](verification.txt#L511-L512)

## The boundary on the production rows

Fix the family's component divisor, Hermitian lattice and section map. If the sections generate the divisor's line bundle at every point, `model_formula_of_bpf` identifies the component height with the normalized arithmetic self-intersection of an induced model. The boundary determines where this argument can apply. [Component and model formula](FamilyComponentIntersection.lean)

| Production row | What Lean proves | Consequence for the section metric |
| --- | --- | --- |
| `1 ≤ j < m` | At least one flag component has a boundary point. The proof constructs an isotropic lattice vector and a degeneration whose closed point lies on the row's boundary. | On that component, `Reads` forces all sections to vanish at the point. They fail to generate there, the metric has no induced model, and the library assigns `B.h = 0` as its fallback. |
| `j = m` | The signature has `q = 0`. The open immersion covers the compactification, so every flag component has empty boundary. | Applying the model formula still requires proving that the sections generate at every interior point. |

`earlier_row_obstruction` rules out this self-intersection argument across all production rows with the given sections. Whether an independently defined arithmetic height equals the assigned word formula `hExpl6` remains open. [Row theorems](ProductionBoundary.lean) · [Compiler and kernel output](verification.txt#L356)

For a specified family of bundles `B` indexed by words, `geometric_height_iff` reduces equality with `hExpl6` to two calculations. The heights must agree at one word, and their differences from that base value must agree at every word. Applying the criterion to the production family still requires a geometric assignment for those words and proofs of both identities. [Height comparison](HeightComparison.lean)

Two related results in the release explain the remaining inputs. Given an induced model and a value satisfying `L.IsSelfInter a`, `arTop_of_induced` expresses the normalized arithmetic intersection in terms of `a` and finite-place corrections. In `SourceStatementOfSlope`, `slope_le` gives an inequality for a component volume slope. Applying either to this comparison would still require identifying the word's bundle and evaluating its height. [Induced-model formula](../../src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ArTopOfInduced.lean#L11) · [Component slope bound](../../src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SourceStatementOfSlope.lean#L257)

The original seed `DivRec.x0` has variety type `Empty`, so a function assigning a bundle to each word would give an element of `Empty` at the distinguished word. The explicit `divXFl` graft used in the original construction does have a row-1 component. Its arithmetic intersection operation is identically zero. Lean reduces agreement with the word formula on that graft to checking whether the formula vanishes at every word at the supplied size constant. The reverse implication uses the graft's own row-1 component and section metric. The criterion holds after the exact `setDiv` assignment as well, at the same size constant and with the supplied lattice. [Original bundle calculation](OriginalBundleHeight.lean)

On the strengthened branch, the zero-height component of each nonterminal row persists under every `GeoCl.step`. Starting with a certified row that satisfies the full divisor link and the formula, one can keep its section maps and all its component heights, raise the size constant, and increase the error coefficient so that the link still holds. Lean proves that the new stored height at the distinguished word exceeds every component height in rows 1 through `m`. The next test keeps the family's size constant fixed. [Transport and normalization theorems](SectionMetricObstruction.lean)

### A level-prime twist at the production normalization

Fix a component of the strengthened family. Start with its section metric and twist its finite metrics by the logarithms of the absolute values of the word's level prime, with multiplicity `W = ∑ t, L.aT t`. This choice uses the prime and the row multiplicities, and keeps the original archimedean metric. A walk from the definition of the candidate height checks 111,154 declarations and excludes `hExpl6`, `FamP.Csz`, `FamP.h_eq` and `setDiv`. If the component admits an arithmetic model and has nonzero geometric degree, its normalized height changes by exactly `−W · log T(u)`. On every nonterminal row at least one component lacks a model, and its twisted height is zero for every word under the library's fallback convention. [Definition and intersection calculation](LevelPrimeHeight.lean) · [Application to strengthened components](ProductionLevelHeight.lean) · [Dependency assertion](LevelHeightDependencies.lean)

At the original `F.Csz`, agreement on a modeled component of nonzero degree requires two equalities. The untwisted section bundle's arithmetic height must equal `hExpl6(u₀) + W · log T(u₀)` at the distinguished word, and the sum of `kerPlace` over rows and embeddings must have the same value at every word. The difference of those sums is exactly the word-to-word change in the error. [Fixed-normalization calculation](ProductionLevelHeight.lean)

**The finite level-prime twist fails on an inhabited production family at its own size constant.** The release accepts an injective code of the prescribed size. The construction chooses one containing the words `100…` and `010…`, uses the production family constructor `designS`, and obtains the strengthened geometric certificate on every in-range row. The theorem carries the production parameter record `κ` and the equality `F.Csz = κ.C.Csz`. The two words have equal total weight. Moving the single set bit changes the distribution of the positive integral weights and strictly changes the sum of the archimedean terms. No choice of the base self-intersection can remove that difference. [Family construction](ProductionSwapFamily.lean) · [Strict inequality](ArchWordSwap.lean) · [Exact weight formula](ArchWeightTest.lean)

On sufficiently large rows, every level prime exceeds every individual weight. Prime divisibility then shows that even unequal level primes cannot make the two **assigned** heights equal. The theorem `realized_obstruction` gives an inhabited window beyond every cutoff. On its certified divisor, every fixed section component misses the assigned height on at least one of the same two words. Row one contains an actual component whose twisted height is zero at a word with nonzero assigned height. This disproves a uniform identification for this bundle construction. The quantifier is existential over allowed codes. Which words the original opaque choice selects is unverified. Identifying a different bundle with an independently defined, word-dependent archimedean metric remains open. [Level-prime calculation](AssignedWordVariation.lean) · [Counterexample and quantifiers](ProductionHeightObstruction.lean) · [Compiler and kernel output](verification.txt#L605)

To reproduce the height comparison and boundary checks from the repository root, run the following with the pinned toolchain and Mathlib cache. Lake first builds the project imports. Lean then compiles the audit files in dependency order and replays each module.

```sh
lake env bash -eu -o pipefail <<'SH'
checks=checks/geometry
modules=(HeightComparison ProductionHeightCandidates HeightSqueeze HeightShift
         FamilyComponentIntersection ProductionBoundary OriginalBundleHeight SectionMetricObstruction
         WordNormVariation LevelPrimeHeight ProductionLevelHeight ArchWeightTest ArchWordSwap
         AssignedWordVariation ProductionSwapFamily ProductionHeightObstruction ProofDependencies)
for module in "${modules[@]}"; do
  awk '$1 == "import" && $2 ~ /^(Formalism|Development|GroundTheory|PositivityTheory|ReciprocityTheory)\./ {
    print "+" $2
  }' "$checks/$module.lean"
done | sort -u | xargs lake build +FamilySections +ReplacementGeometry
out=$(mktemp -d)
export LEAN_PATH="$out:$LEAN_PATH"
for module in "${modules[@]}"; do
  lean -j1 --tstack=400000 -DautoImplicit=false -R "$checks" -o "$out/$module.olean" "$checks/$module.lean"
  leanchecker --verbose "$module"
done
lean -j1 --tstack=400000 -DautoImplicit=false -R "$checks" "$checks/LevelHeightDependencies.lean"
lean -j1 --tstack=400000 -DautoImplicit=false --stdin <<'LEAN'
import ProductionHeightObstruction
import Lean.Elab.Command
open Lean Elab Command
run_cmd do
  let e ← getEnv
  unless e.contains ``GeometryAudit.ProductionHeightObstruction.realized_obstruction do
    throwError "Missing height counterexample"
  if e.contains `riemannHypothesis then throwError "Final Main theorem is already imported"
  logInfo "realized_obstruction is available before the final riemannHypothesis declaration"
LEAN
SH
```

## Replacement divisors and the fixed row core

`CoreLevel.lean` checks `A = 1` directly for the core in `prm0`, `prm1`
and `prmA`. The same file works on the original and ablated checkouts.
`ReplacementGeometry.lean` proves `DivEx` with the prescribed surfaces and
arithmetic different. Its two-level construction preserves the four original
row obligations, including `LamAre`. It fails the full geometric predicate
for every kit class. Its geometry declares all divisor classes nef, whereas
the negative hyperplane class on the projective line has degree −1.

`FixedCoreTie.lean` constructs a source family using the core's prescribed
`Dw j` and `Xo j` at every required signature and the base level.
`SourceFamily.lean` proves an equivalence on the RH row interface. There
exists a lawful extension of that core with an exponent-one pinned source
family satisfying the full `ParTie` exactly when `CurveOver` holds for the
core's host over the existing `fieldLL D` at level
`Nat.lcm (D.host.g 0 * D.host.g 1) 15`. `curve_of_closure` proves that
this same field condition is necessary even when a full geometric witness
uses a larger positive exponent or is transported through `GeoCl`.

`ProductionTie.lean` proves `StepW Pinned (tiedSourceRows slots)` whenever
`slots.Rx = RX`. This has the quantifier order used by the RH divisor
construction. For each preliminary base, the project supplies a finite
set of algebraic Weber values at the required level. The `large₂`
clause allows the coefficient field to be required to contain that set.
The resulting `CurveOver` gives a pinned source family. The signature
construction uses the row core's own `Dw j` and uses its `Xo j` at the
base level for every `j` in `InR`.
`production_parameters` instantiates the theorem for `prm0`, `prm1`,
and `prmA`.

`production_tie_without_family` gives a lawful
extension of that same row core satisfying the full tie for which every
`FamOver Q P h c` is empty. This extension accepts every level in
`P.G.P.levIn`. The `prov` equality in a family would identify this
test with divisibility by a positive integer `n` at each index, which
excludes `n + 1`. The example rules out that choice of `G`;
the strong geometry permits a different choice. The forms package
also has core-specific obligations: `FormsAre.base` equates its weight
families with `recB h.toLawsCore` and `FormsAre.cmp` compares their
evaluations via the prescribed `ParTie`.

## Building the top from the kits

`FamilyTop.lean` transports the same source family, with its pin and
tie, across any equality of lawful tops' cores. At the RH construction's
`StepW` quantifiers, `production_rowKits` supplies all kits on `ngTrue`
and their membership in the project's `IsKitOf st`. This holds for any
given system of stages `st`. The project supplies such systems via
`KitCheck.nonempty_stFams`.

The new top takes its provisional package and row indices from those
kits and retains the original tower. Lean checks that its core is the
original core and that it satisfies the entire `FamOver.prov` field,
including coverage of indefinite data. For this top, `familyTop_laws_iff`
reduces `LawsP` to one point-existence condition. For every algebraic
tower point in range, a point of the kit's local model must have the
same valued field and an isometry of its lattice preserving the period
pairing for every degeneration datum at the tower point. The same
condition is necessary for every choice of relation on these packages,
indices and towers.

`LocalPointLift.lean` supplies a kit point over exactly the same valued
field for every algebraic tower point in that statement. The construction
uses the full `ParTie.same` equality, the inclusion of coefficient fields,
and the selected kit's integral model at a place above the residue prime.
In `ModelComparison.lean`, the two integral models can have different
coefficient fields. The proof adjoins the second field inside the common
valued field, uses one semistable uniformisation, and identifies the two
period pairings. `FamilyLaws.family_points_and_lattices` applies this
comparison to a kit point chosen over the same generic moduli point.
It works for every degeneration datum there. `FamilyLaws.family_laws`
then proves the entire `LawsP` record for the family-derived top.

`FamilySections.family_iso` proves invariance under isomorphisms of the
input Hermitian spaces for this kit construction. `cusp_of_reads`
derives the divisor's cusp vanishing from the family's own `Reads` proof:
the row-lattice generators have cusp-form readings, they span the row,
and vanishing along the boundary is linear.

`ProductionGeometry.production_parameters` supplies these lawful family-derived
tops over the prescribed cores in all three RH parameter branches, at the
project's `StepW` quantifiers. Each indefinite row has an algebraic tower
point at every place of its coefficient field. Row one has such a place
and point by `first_row_has_point`.

For every in-range row and weight, `FormRegularity.regular_off_boundary`
proves that the actual comparison `cmpAt` of a core cusp form is regular
off the boundary. `FormBoundary.global_cusp_value` proves it is a global
section and vanishes on the boundary. The proof extends the core's own
uniformisation to the family's coefficient field. Multiplication by the
key section preserves analytic cuspidality, and the compactification
theorem extends that value over the boundary. Conversely, a tuple of global
sections of the prescribed weight determines a unique untwisted rule
over the family's coefficient field (`FormReconstruction.unique_untwisted_rule`).
For such a rule, boundary vanishing of the twisted values implies analytic
cuspidality in any lawful uniformisation under the dimension and weight
hypotheses in `FormDescent.reconstructed_cusp`. For every in-range row
and weight, `FormSpan.span_global_cusp` then proves the exact span
required by `FormsPkg.cmp_span` for this comparison over `D.what₂.LL`.
`FormMultiplication.multiplicative_comparison` proves the product identity
for this evaluation on all core rules at each in-range row.
`FormComparison.evaluated_eq` identifies the semilinear map with `cmpAt`.
`FormLaws.independent_comparison` proves that independent tuples in the
row cusp space stay independent after evaluation over the target field.
`FamilyForms.rowComparison` in `RowComparison.lean` supplies all three
comparison fields at every row, using the zero cusp space outside the range.

`FormPoints.kit_point_nonempty` supplies a point on the kit for every
in-range row and every coefficient-field place, including the last row.
`pointMap_img` identifies the map with the row's prescribed image whenever
`j < D.R.m`, exactly the range required by `FormsAre.pts`.
`FormRowData.theta_eq` identifies both theta spaces with the row's own.
`integral_iff` proves that testing nonnegativity at the constructed points
recovers the row's entire integral lattice, for every row and weight.
This is the lattice in `FormsAre.base`. The lattice comparison in
`Reads` concerns a separate map to `D.what₂.Mj j`.

`FormsAssembly.forms` constructs the full `FormsOver` package.
`forms_base` uses `integral_iff` to identify its valuation-defined lattice
with the core lattice. The weight spaces and both norms come from the row.
`FamilyForms.family` instantiates the comparison and gives a `FamOver`
for `IsKitOf st`. Its `production_parameters` theorem supplies such a
family over the production core for each of `prm0`, `prm1`, and `prmA`
under the project's `StepW Pinned` quantifiers.

## Constructing `Reads` and the stronger divisor

`ReadingRealisation.lean` lifts the analytic evaluation through the row
embedding on the subspace where its image lies in that embedding's range.
`ReadingLattice.lean` restricts this subspace to the prescribed level.
Its `core_cusp` theorem proves the project's `MjCusp` predicate. The
image contains the full row lattice and spans the complex row, core point
valuations characterize the preimage of the lattice, and `norm_jTop`
together with `MjTie.eW_norm` gives the norm identity with volume
`volRec`. The realization preserves linear independence after extension
to the complex numbers.

`ProductionReading.lean` obtains the required analytic inputs and
weight from each production row. `FamilyReading.family_sat` transports
the realization to the assembled family's `MjSat` predicate. The
cusp-form norm in this equality is the row's existing norm.

`ReadingSectionMaps.lean` selects a complex basis from the row lattice
generators and lifts those generators to the row and cusp spaces.
The common basis and dimension bounds make these lifts bases in their
respective spaces. Linear independence of the compared sections gives an
injective map into the product of section spaces. Each component is regular
because the comparison images lie in its space of regular sections. `ReadingRows.exists_reads` proves regularity and the
compatibility equation for every pair with `jM j x = φ f`. Both
injectivity and compatibility apply to rows in `InR`. Outside that range,
the construction chooses zero sections and proves their regularity.
`ProductionReads.production_reads` supplies these maps and the full
`FamOver.Reads` proof on the production core.

`ProductionReads.production_geometry` uses that family to construct a
divisor satisfying `DivT`, `MjAre`, the prescribed `kapR`, `LamAre`,
and `geoOf (fun D => IsKitOf (st D))` together. The witness uses
positive index `1`. `GeometryAudit.ProductionReads.strong_parameters` proves `DivEx`
for `prm0`, `prm1`, and `prmA` with the geometry slot set to
`OX (some (geoOf (fun D => IsKitOf (st D))))`. These statements
retain the project's `StepW Pinned` quantifiers. This raw-slot theorem and the transported slot used by the joined branch
are checked in `ProductionParameterChecks.lean`.

To reproduce the intermediate checks after building this branch, run the following
from the repository root.

```sh
lake env bash -eu <<'SH'
checks="$PWD/checks/geometry"
out=$(mktemp -d)
export LEAN_PATH="$out:$LEAN_PATH"
for module in CoreLevel ReplacementGeometry FixedCoreTie SourceFamily ProductionTie \
  FamilyTop LocalPointLift ModelComparison FamilyLaws FamilySections ProductionGeometry \
  FormRegularity FormBoundary FormReconstruction FormDescent FormSpan FlagEvaluation \
  FormMultiplication CoreEmbedding SemilinearEvaluation FormComparison FormLaws FormPoints \
  FormRowData RowComparison FormsAssembly FamilyForms ReadingRealisation ReadingLattice \
  ProductionReading FamilyReading ReadingSectionMaps ReadingRows ProductionReads StrongDivEx ProductionParameterChecks
do
  lean -j2 --tstack=400000 -DautoImplicit=false -DmaxHeartbeats=4000000 \
    -R "$checks" -o "$out/$module.olean" "$checks/$module.lean"
done
# Run each expected failure separately in this environment.
# lean "$checks/controls/FamilyPointAttempt.lean"
# lean "$checks/controls/FamilyLatticeAttempt.lean"
SH
```

The negative control can be run with
`lake env lean checks/geometry/controls/FixedFieldAttempt.lean`. It uses
the project's sufficient Weber-value criterion on the `prm0` rows. Lean
checks the host-root membership and level positivity, then leaves
`WeberIn` in the fixed coefficient field as the goal at `assumption`.
This attempt takes a coefficient field fixed in advance. Its failure is
consistent with the positive `StepW` result above, which constructs the
family and its section maps on a lawful extension of the RH core.

The second negative control, `controls/FamilyPointAttempt.lean`,
tries to use the old top's local point as the witness for the new top.
Lean reports a type mismatch between the two packages' point types
at `Exists.intro η`. The positive proof in `LocalPointLift.lean` constructs a
point in the new package. The third control, `controls/FamilyLatticeAttempt.lean`,
uses that proof and discharges the field equality. Lean then displays
the lattice isometry and its pairing identity as the unsolved goal at
`assumption`. `FamilyLaws.lean` proves both conditions together using the model comparison.

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
