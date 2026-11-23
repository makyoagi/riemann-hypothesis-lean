import Main

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for n in [`GlobalTheory.Mem.Top.Bl.anyGeometry, `GlobalTheory.Mem.Top.Bl.OAt.geo] do
    if env.contains n then
      throwError "Deleted declaration still present: {n}"
    logInfo m!"Absent from the Main environment: {n}"
  let axs ← collectAxioms `riemannHypothesis
  let expected := #[`propext, `Classical.choice, `Quot.sound]
  unless axs.size == expected.size && expected.all axs.contains do
    throwError "Unexpected axioms: {axs}"
  logInfo m!"Checked exact axiom set: {axs}"
