import Lean.Util.FoldConsts
import Lean.Elab.Command

namespace GeometryAudit.Dependencies

open Lean

/-- Walk declarations, following the constants in their types and values. -/
def reachable (env : Environment) (root : Name) : CoreM NameSet := do
  let kernel := env.checked.get
  let mut todo := [root]
  let mut seen : NameSet := {}
  repeat
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      unless seen.contains n do
        let some info := kernel.find? n | throwError "Missing dependency {n}"
        seen := seen.insert n
        for child in info.getUsedConstantsAsSet do
          unless seen.contains child do todo := child :: todo
  return seen

end GeometryAudit.Dependencies
