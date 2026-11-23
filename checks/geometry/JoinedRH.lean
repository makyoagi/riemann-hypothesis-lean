import Main
import Lean.Util.FoldConsts

open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl

example : RiemannHypothesis := riemannHypothesis
example : RiemannHypothesis = RiemannZetaZerosOnLine := rfl

namespace GeometryAudit.Joined

open Lean Elab Command

/-- Return a path of actual type/value references. A positive result can be
    checked edge by edge. Earlier imported modules can be skipped. -/
private def pathTo (env : Environment) (root target : Name) : CoreM (List Name) := do
  let kernel := env.checked.get
  let some cutoff := env.getModuleIdxFor? target | throwError "Unknown imported target {target}"
  let mut todo := [(root, ([] : List Name))]
  let mut seen : NameSet := {}
  repeat
    match todo with
    | [] => throwError "No declaration path from {root} to {target}"
    | (n, parents) :: rest =>
      todo := rest
      if n == target then return (n :: parents).reverse
      unless seen.contains n do
        seen := seen.insert n
        if let some idx := env.getModuleIdxFor? n then
          if idx.toNat < cutoff.toNat then continue
        let some info := kernel.find? n | throwError "Missing dependency {n}"
        for child in info.getUsedConstantsAsSet do
          unless seen.contains child do todo := (child, n :: parents) :: todo
  throwError "No declaration path from {root} to {target}"

run_cmd do
  let env ← getEnv
  let mut root := ``riemannHypothesis
  for target in [``Closing.divEx_geometry, ``GeometryAudit.ProductionReads.closed_divEx,
      ``GeometryAudit.ProductionReads.production_geometry, ``GeometryAudit.ProductionReads.production_reads] do
    let path ← liftCoreM <| pathTo env root target
    logInfo m!"Kernel declaration path of length {path.length - 1}: {String.intercalate " → " (path.map toString)}"
    root := target
  let axs ← collectAxioms ``riemannHypothesis
  let expected := #[`propext, `Classical.choice, `Quot.sound]
  unless axs.size == expected.size && expected.all axs.contains do
    throwError "Unexpected axioms: {axs}"
  logInfo m!"riemannHypothesis axioms: {axs}"

end GeometryAudit.Joined
