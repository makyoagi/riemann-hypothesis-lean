import ProductionLevelHeight
import ProofDependencies

open Lean Elab Command in
run_cmd do
  let root := ``GeometryAudit.ProductionLevelHeight.height
  let used ← liftCoreM <| GeometryAudit.Dependencies.reachable (← getEnv) root
  for n in [``Formalism.BasicNotions.DV.hExpl6, ``Formalism.MainNotions.FamP.Csz,
            ``Formalism.MainNotions.FamP.h_eq, ``GlobalTheory.EX.OB.setDiv] do
    if used.contains n then throwError "{root} depends on {n}"
    logInfo m!"{n} absent from {used.size} declarations reachable from {root}"
