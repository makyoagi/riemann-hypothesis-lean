import Main
import ProofDependencies

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let root := ``riemannHypothesis
  let emptyLemma := ``GlobalTheory.Mem.Top.DivRec.divEx_prov
  let reachable ← liftCoreM <| GeometryAudit.Dependencies.reachable env root
  if reachable.contains emptyLemma then
    throwError "{root} reaches the empty-slot lemma {emptyLemma}"
  logInfo m!"{emptyLemma} is absent from all {reachable.size} declarations reachable from {root}"
