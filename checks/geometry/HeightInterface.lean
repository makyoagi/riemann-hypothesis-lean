import Formalism.LocalToGlobal.Divisibility.RecBridge
import ProofDependencies

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.DIV

namespace GeometryAudit.Height

theorem link_of_bounds {D : D7} (L : SizeData₂ D) (C Cabs CH : ℝ)
    (words : ∀ u, WordFacts L C Cabs u)
    (frame : sFrame D.div.Nu D.div.h + D.div.RR.muMax ≤ L.sc.x ^ CH * L.sc.b)
    (variation : ∀ u u', |(D.div.h u + (∑ t : D.host.TT, (L.aT t : ℝ)) * Real.log ((D.mem u).A.T : ℝ)) -
      (D.div.h u' + (∑ t : D.host.TT, (L.aT t : ℝ)) * Real.log ((D.mem u').A.T : ℝ))| ≤
      C * ((D.host.TT.card : ℝ) * L.sc.a * L.La + (D.R.m : ℝ) * L.B0))
    (h11 : LocalQuadraticParts.adm11 D L C) (h13 : LocalQuadraticParts.adm13 D)
    (hBR : D.BuRational) (hRR : D.RRFull) (hZ : L.ZeroAbove) : LinkDIV_at L C Cabs CH := by
  refine ⟨fun u => (words u).1, frame, hZ, ⟨hBR, h13⟩, hRR, fun u hu => (words u).2.1 hu,
    fun u => (words u).2.2, ?_, variation⟩
  intro u j hj
  have h := (h11 u j hj).1
  rwa [Formalism.MainNotions.DIV.prod_gTypes] at h

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let formula := ``hExpl6
  for root in [``LinkDIV_at, ``link_of_bounds] do
    let used ← liftCoreM <| GeometryAudit.Dependencies.reachable env root
    if used.contains formula then throwError "{root} depends on {formula}"
    logInfo m!"{root}: {used.size} reachable declarations, {formula} absent"

#print axioms link_of_bounds
end GeometryAudit.Height
