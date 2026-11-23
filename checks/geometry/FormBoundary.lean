import FormRegularity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormRankLeSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSecReadingDecreasingIntegerExponentsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCuspFormsAllEmbeddingsOfInclusionReading
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsEmbExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingFrameDeltaChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoMulCardPsi

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam GlobalTheory.TrueGeo GlobalTheory.Toroidal
open GlobalTheory.AllWt GeometryAudit.FamilyTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GeometryAudit.FormBoundary

private theorem key_holomorphic {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} (key : KeySec Xo c) {σ : c.F →+* ℂ} {r : ℕ}
    (U : Unf Xo c σ r) (hs : GoodEmb c σ) (hu : IsUnf U) (hr : 1 ≤ Dw.p + Dw.q) (m : ℕ) (k : U.Comp) :
    (U.X k).IsSec 0 (rdU U ((key.ρ : Rul Xo c) ^ m) k) := by
  let G : WTZ E := (fun _ => (m : ℤ), -2 * (m : ℤ))
  have exG : exZ Dw G = fun i => (m : ℤ) * keyEx Dw i := by
    funext i
    cases i <;> simp [exZ, G, keyEx, mul_comm]
  have wt : modelWt U G k = 0 := by
    funext τ i
    simp only [modelWt, G, Pi.zero_apply]
    split <;> omega
  have he : Even G.2 := ⟨-(m : ℤ), by dsimp [G]; ring⟩
  rw [← wt]
  apply GlobalTheory.T.isSec_reading_decreasing_integer_exponents _ _ _ _ _ _ _ _ U ⟨key⟩ hs hu hr G he (fun _ _ _ _ _ => le_rfl)
  rw [exG]
  exact key.pow_mem m

-- Use the core's own uniformisation after extension of coefficients. The
-- extension theorem for a flag component accepts that uniformisation directly.
private theorem tied_cusp_value {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {m m' : MD H} (tie : m = m')
    {c : Coeff m.1} {c' : Coeff m'.1} (le : c.F ≤ c'.F) {r : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Unf m.2.2 c σ r) (hu : IsUnf (U c.F.val.toRingHom))
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hn : Even n)
    (chi : ∀ k, ∀ γ ∈ ((U c.F.val.toRingHom).X k).Γ,
      ((U c.F.val.toRingHom).X k).χ (laU (U c.F.val.toRingHom) a n k) γ = 1)
    (hfE : 1 < Module.finrank ℚ E / 2) (hr : 1 ≤ m'.2.1.p + m'.2.1.q)
    {O : Type} [CommRing O] {β : O →+* c'.F} {Z : Model m'.2.2 c' β} {F : Type} [Field F]
    {e : F ≃+* c'.F} (C : FlagCpt Z e) (key : KeySec m'.2.2 c') {f : Rul m.2.2 c}
    (hf : f ∈ cusp m.2.2 c U a n) :
    let v := C.val (trRul tie (c := c) (c' := c') le f * (key.ρ : Rul m'.2.2 c') ^ (n / 2))
    let Δ := C.LEx (exKey m'.2.1 a n)
    v ∈ C.Y.H0 Δ ∧ C.Y.vanishOn Δ v C.Ybd := by
  subst m'
  let σ := c'.F.val.toRingHom
  have hs : GoodEmb c' σ := rfl
  let V := unfBC le U σ
  have hv : IsUnf V := GlobalTheory.OneMapAll.isUnf_unfExt le σ (fun _ => rfl) hu
  have b := ((GlobalTheory.FieldBC.rulBC_cusp _ _ _ _ _ c c' le r U a n f
    ((cusp_le_sec _ _ _ _ _) hf)).2).2 hf
  have bm := (mem_cusp _ _ _ _ _ _).1 b
  have hc : ∀ k, ∀ γ ∈ (V.X k).Γ, (V.X k).χ (laU V a n k) γ = 1 := by
    intro k γ hγ
    rw [show laU V a n = _ from laU_unfBC le U σ a n]
    exact chi k γ hγ
  apply GlobalTheory.CovHt.RankInj.val_mem_H0 C hs hv (laU V a n) hc (FlagCheck.exKey_none a hn)
    (key.mul_pow_mem bm.1)
  intro k
  rw [GlobalTheory.CuspAllEmb.rd_mul]
  have h1 := GlobalTheory.CuspSecFin.mem_SS_of_mem_holSub _ _ (bm.2 σ hs) k
  have h2 := key_holomorphic key V hs hv hr (n / 2) k
  simpa only [add_zero, Pi.mul_apply] using GlobalTheory.CuspAllEmb.ss_mul (V.X k) hfE h1 h2

theorem global_cusp_value {D : D7} {T : Top D} (h : LawsP T) {st : StFams D}
    (R : RowKits T h st) {j : ℕ} (hj : InR D j) (w : WeightFamilies.Wt D j)
    (f : (recB h.toLawsCore).Cusp j w) (k : (R.F.at (datW D R.F.κg j)).Comp) :
    let d := datW D R.F.κg j
    let C := (R.k.at d).Φ.C k
    let Δ := (R.F.at d).Lw R.L (R.k.at d).Φ k (wtOfN d.N w)
    let v := cmpAt h R.tie R.k hj w.n k f.1
    v ∈ C.Y.H0 Δ ∧ C.Y.vanishOn Δ v C.Ybd := by
  let d := datW D R.F.κg j
  let S := R.F.sig d.N d.j d.two_le d.j_le
  have hp : S.Dw.p = (D.R.sigW j).1 := S.p_eq.trans (datW_j D R.F.κg hj.1 hj.2)
  have hq : S.Dw.q = (D.R.sigW j).2 := by
    have e := S.rank_eq.trans (datW_N D R.F.κg j)
    exact Nat.add_left_cancel ((congrArg (· + S.Dw.q) hp.symm).trans (e.trans (sigW_sum D hj.1 hj.2).symm))
  have hr : 1 ≤ S.Dw.p + S.Dw.q := S.rank_eq.symm ▸ le_trans (by decide : 1 ≤ 2) S.two_le
  have he := (CmDim.cm_dim D (ambOf T.Q h.pins.1)).2.1
  dsimp only
  rw [AsmCheck.Lw_wtOfN (R.F.at d) R.L w hp hq]
  exact tied_cusp_value (R.tie.same j hj) (c := T.Q.c) (c' := R.F.κg.c) R.tie.le (T.U j)
    (h.unf j hj _ T.good_σ₀) (wtA w) w.n w.n_even (h.chiTriv j hj _ T.good_σ₀ _ _ (dom_wtA w))
    (by omega) hr ((R.k.at d).Φ.C k) (R.k.at d).key ((esec_mem_C h hj).mp f.2)

#print axioms global_cusp_value
end GeometryAudit.FormBoundary
