import Formalism.LocalToGlobal.Divisibility.RecBridge
import Formalism.SharpRestriction.Divisibility.AdmissibleRank.LogDiscriminantLeSquareSizeFamily
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX.OB

namespace GeometryAudit.HeightShift

/-- The whole divisor link remains true after raising every stored height by
    the same amount and increasing the error coefficient by that amount. -/
theorem link_after_shift {D : D7} (L : SizeData₂ D) {C Cabs CH : ℝ}
    (link : LinkDIV_at L C Cabs CH) (exponent : 0 ≤ Cabs) (s : ℝ) (hs : 0 ≤ s) :
    let N := fun u => (D.div.Nu u).L
    let h := fun u => D.div.h u + s
    LinkDIV_at (ledTr N h L) (C + s) Cabs CH := by
  obtain ⟨integral, frame, zeroAbove, bessel, full, lower, upper, degree, variation⟩ := link
  have hL : 1 ≤ L.sc.x ^ L.sc.eps := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have hb : 1 ≤ L.sc.b := Real.one_le_exp (zero_le_one.trans hL)
  have ha : 1 ≤ L.sc.a := one_le_mul_of_one_le_of_one_le L.sc.one_lt_alt.le hb
  have hLa : 0 ≤ L.La := Real.log_nonneg (one_le_mul_of_one_le_of_one_le ha (DIV.one_le_rdE D))
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (show 1 ≤ D.R.m by have := D.R.two_le_m; omega)
  have hf : (1 : ℝ) ≤ D.R.f := by
    exact_mod_cast (show 1 ≤ D.R.f by unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega)
  have hB : 1 ≤ L.B0 :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hf hm) hb) hL
  have hNc := Formalism.MainNotions.Nc_nonneg L
  have hpow := Real.one_le_rpow L.sc.one_lt_alt.le (mul_nonneg exponent L.sc.eps_pos.le)
  have err₁ : 0 ≤ (D.host.TT.card : ℝ) * L.sc.a * L.La :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans ha)) hLa
  have err₂ : 1 ≤ (D.R.m : ℝ) * (L.B0 + L.Nc) * L.sc.x ^ (Cabs * L.sc.eps) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hm (by linarith)) hpow
  have extra : s ≤ s * ((D.host.TT.card : ℝ) * L.sc.a * L.La) +
      s * ((D.R.m : ℝ) * (L.B0 + L.Nc) * L.sc.x ^ (Cabs * L.sc.eps)) := by
    linarith only [mul_nonneg hs err₁, le_mul_of_one_le_right hs err₂]
  refine ⟨integral, ?_, zeroAbove, bessel, full, ?_, ?_, ?_, ?_⟩
  · have smaller : sFrame D.div.Nu (fun u => D.div.h u + s) ≤ sFrame D.div.Nu D.div.h := by
      unfold sFrame
      exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun u _ =>
        mul_le_mul_of_nonneg_left (sub_le_sub_left (le_add_of_nonneg_right hs) _) (Nat.cast_nonneg _))
        (Nat.cast_nonneg _)
    exact (add_le_add smaller le_rfl).trans frame
  · intro u hu
    exact (lower u hu).trans (le_add_of_nonneg_right hs)
  · intro u
    change D.div.RR.muDual + (D.div.h u + s) - L.Fo ≤ L.MAIN u +
      (C + s) * (D.host.TT.card : ℝ) * L.sc.a * L.La +
      (C + s) * (D.R.m : ℝ) * (L.B0 + L.Nc) * L.sc.x ^ (Cabs * L.sc.eps)
    linarith only [upper u, extra]
  · intro u j hj
    exact (degree u j hj).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hs) (zero_le_one.trans hB))
  · intro u v
    have hcost : 0 ≤ (D.host.TT.card : ℝ) * L.sc.a * L.La + (D.R.m : ℝ) * L.B0 :=
      add_nonneg err₁ (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hB))
    have h := (variation u v).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hs) hcost)
    let t := fun w => (∑ i : D.host.TT, (L.aT i : ℝ)) * Real.log ((D.mem w).A.T : ℝ)
    change |D.div.h u + s + t u - (D.div.h v + s + t v)| ≤ _
    rwa [show D.div.h u + s + t u - (D.div.h v + s + t v) =
      D.div.h u + t u - (D.div.h v + t v) by ring]

#print axioms link_after_shift
end GeometryAudit.HeightShift
