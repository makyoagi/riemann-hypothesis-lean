import Formalism.LocalToGlobal.Divisibility.RecBridge
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
import ProofDependencies

open Module NumberField IsDedekindDomain
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.L2.DIV

namespace GeometryAudit.PairingHeight

/-- Bound the height computed from the pairing's own operator norms using the
    arithmetic inputs of the released divisor estimate, before assigning a divisor height. -/
theorem bound_of_arithmetic_inputs {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    {Bs : DefBase K} {Df0 Df1 : DefSide Bs} {Dc : DefCols Df1} {Sp : SPer Dc} {N : IndefNum Bs}
    {Pl : Type} [Fintype Pl] [DecidableEq Pl] (wf0 : Df0.WF) (wf1 : Df1.WF)
    (P : IndefCoreR Df0 Df1 Dc Sp N) (R : RecNums Bs.J Pl) (u : Dc.Mem)
    (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K)) (sg : HeightOneSpectrum (𝓞 K) → ℝ)
    (inputs : DivInputsR P R u Nu sg)
    (hXc : ∀ v, IsUnit ((Dc.Xc u) v).det) (hXE : ∀ v, IsUnit (P.cols.XE v).det)
    (nonzero : P.cols.col.B u ≠ 0) :
    P.cols.muCC + Formalism.HN.htMap (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u)
      (Pi.basisFun K (Fin P.cols.D)).dualBasis (Formalism.HN.dualFrame P.cols.XE) (P.cols.col.B u)
      - 2 * FoOfR P ≤ R.rhs := by
  have clauses := divClausesR_of wf0 wf1 P R u Nu sg inputs
  have lower := htMap_le_of_bound (Dc.Xc u) P.cols.XE (P.cols.col.B u) R.hu (meanLog P.cols.κ)
    clauses.2.1 (opNormAt_pos_of _ _ _ hXc hXE nonzero)
  linarith only [lower, clauses.2.2.1]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let reached ← liftCoreM <| GeometryAudit.Dependencies.reachable env ``bound_of_arithmetic_inputs
  for n in [``divClausesR_of, ``height_chain_atR, ``htMap_le_of_bound] do
    unless reached.contains n do throwError "Missing expected arithmetic dependency {n}"
  for n in [``Formalism.BasicNotions.DV.hExpl6, ``Formalism.MainNotions.FamP.h_eq,
      ``GlobalTheory.EX.OB.setDiv, ``GlobalTheory.Mem.Top.Bl.GeoCl,
      ``Formalism.BasicNotions.D7] do
    if reached.contains n then throwError "Unexpected divisor dependency {n}"
  logInfo m!"Checked {reached.size} reachable declarations: arithmetic bounds present, divisor assignment and geometry gate absent"

#print axioms bound_of_arithmetic_inputs
end GeometryAudit.PairingHeight
