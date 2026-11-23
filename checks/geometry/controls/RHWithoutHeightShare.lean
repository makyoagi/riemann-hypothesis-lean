import Main
import Lean.Util.CollectAxioms

example : RiemannHypothesis = (∀ s : ℂ, riemannZeta s = 0 →
    (¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2) := rfl
example : RiemannHypothesis := riemannHypothesis

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let forbidden := `Formalism.SharpRestriction.Divisibility.HeightShare
  if env.header.moduleNames.contains forbidden then
    throwError "Main imported the forbidden height module"
  for n in [`Formalism.MainNotions.HeightShare.LData, `Formalism.MainNotions.HeightShare.LData.h] do
    if env.contains n then throwError "Unexpected independent-height declaration {n}"
  for n in [`Formalism.BasicNotions.DV.hExpl6, `Formalism.MainNotions.FamP.h_eq,
            `Formalism.L2.DIV.divClausesR_of, `Formalism.L2.DIV.height_chain_atR] do
    unless env.contains n do throwError "Missing arithmetic comparison declaration {n}"
  let actual ← collectAxioms ``riemannHypothesis
  let expected := #[`propext, `Classical.choice, `Quot.sound]
  unless actual.size == expected.size && expected.all actual.contains do
    throwError "Unexpected RH axioms {actual}"
  logInfo m!"{forbidden} absent from {env.header.moduleNames.size} imported modules"
  logInfo "HeightShare.LData and HeightShare.LData.h absent; arithmetic formula and estimate declarations present"
  logInfo m!"riemannHypothesis axioms: {actual}"
