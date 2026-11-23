import Main
import ProofDependencies
import Formalism.SharpRestriction.Divisibility.HeightShare
import Formalism.LocalToGlobal.Divisibility.RecBridge

open Lean Elab Command

namespace GeometryAudit.HeightRoute

run_cmd do
  let env ← getEnv
  let reached ← liftCoreM <| GeometryAudit.Dependencies.reachable env ``riemannHypothesis
  for n in [``Formalism.BasicNotions.DV.hExpl6, ``Formalism.MainNotions.FamP.h_eq,
            ``Formalism.L2.DIV.linkDIV_at_words, ``Formalism.L2.DIV.wordFacts_of,
            ``Formalism.L2.DIV.divClausesR_of, ``Formalism.L2.DIV.height_chain_atR,
            ``Formalism.MainNotions.HeightShare.LData.h] do
    logInfo m!"{n}: {if reached.contains n then "reachable" else "absent"}"
  logInfo m!"{reached.size} declarations checked from riemannHypothesis"

end GeometryAudit.HeightRoute
