import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ParMem
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmCurveTorsionDefinedOverOfWeberValues

open Formalism.BasicNotions Formalism.MainNotions.Inhab GlobalTheory.Mem GlobalTheory.Mem.Col2
open GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl
open GlobalTheory.ShFam

-- Negative control. Specialize to the RH rows. Use the repository's Weber-value
-- route and print the remaining mathematical obligation in the fixed field.
example {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt}
    {hL : GlobalTheory.Published.LocalLanglandsGL} (l : Lv4 (prm0 hL).s K w Z)
    (_over : K.Over B.toPre) (_forced : Forced K B T) (_pin : ColPin w) :
    GlobalTheory.CompRat.CurveOver l.what₂.r.z.core.Q.H (fieldLL (w.D Z))
      (Nat.lcm ((w.D Z).host.g 0 * (w.D Z).host.g 1) 15) := by
  let D := w.D Z
  have hp := l.rx.laws.pins.1
  have hr : l.what₂.r.z.core.Q.H.rt0 ∈ fieldLL D :=
    ⟨D.embE D.host.sqrtMinusD, (RingHom.congr_fun D.embE_φ₀ _).trans hp.2.2.1.symm⟩
  have hn := Nat.lcm_pos (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos) (by decide : 0 < 15)
  apply (GlobalTheory.FinalJoin.CurveField.curveOver_of_weberIn _ _ _ _ hn).1 hr
  assumption
