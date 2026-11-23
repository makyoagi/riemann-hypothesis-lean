import FamilyTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfAlgClosed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrPtOfEigFrame
import Formalism.LocalToGlobal.ProjectiveLattices.ESecPfA

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam GlobalTheory.TrueGeo GlobalTheory.Toroidal
open GeometryAudit.FamilyTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GeometryAudit.FormRegularity

private theorem transport_section {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {m m' : MD H} (tie : m = m')
    {c : Coeff m.1} {c' : Coeff m'.1} (le : c.F ≤ c'.F) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {f : Rul m.2.2 c} (hf : f ∈ sec m.2.2 c a n) :
    trRul tie (c := c) (c' := c') le f ∈ sec m'.2.2 c' a n := by
  subst m'
  rw [← GlobalTheory.AllWt.secZ_nat] at hf ⊢
  exact GlobalTheory.SlopeDesc.rulBC_mem_secZ le hf

-- The comparison of a core cusp form has the prescribed divisor on the open locus.
theorem regular_off_boundary {D : D7} {T : Top D} (h : LawsP T) {st : StFams D}
    (R : RowKits T h st) {j : ℕ} (hj : InR D j) (w : WeightFamilies.Wt D j)
    (f : (recB h.toLawsCore).Cusp j w) (k : (R.F.at (datW D R.F.κg j)).Comp) :
    let d := datW D R.F.κg j
    let s := R.F.at d
    let Φ := (R.k.at d).Φ
    ∀ y : (Φ.C k).Y.X, y ∉ (Φ.C k).Ybd →
      (s.Lw R.L Φ k (wtOfN d.N w)).RegularAt y (cmpAt h R.tie R.k hj w.n k f.1) := by
  let d := datW D R.F.κg j
  let S := R.F.sig d.N d.j d.two_le d.j_le
  have hp : S.Dw.p = (D.R.sigW j).1 := S.p_eq.trans (datW_j D R.F.κg hj.1 hj.2)
  have hq : S.Dw.q = (D.R.sigW j).2 := by
    have e := S.rank_eq.trans (datW_N D R.F.κg j)
    exact Nat.add_left_cancel ((congrArg (· + S.Dw.q) hp.symm).trans (e.trans (sigW_sum D hj.1 hj.2).symm))
  let C := (R.k.at d).Φ.C k
  dsimp only
  intro y hy
  rw [AsmCheck.Lw_wtOfN (R.F.at d) R.L w hp hq]
  have hf := (esec_mem_C h hj).mp f.2
  have hs := transport_section (R.tie.same j hj) (c := T.Q.c) (c' := R.F.κg.c) R.tie.le
    ((cusp_le_sec _ _ _ _ _) hf)
  exact OpenReg.regularAt_open _ _ _ _ _ _ _ _ _ _ _ C _ (FlagCheck.exKey_none _ w.n_even) _
    ((R.k.at d).key.mul_pow_mem hs) y (fun hb => hy ((C.bd_supp y).2 hb))

-- For this comparison the simultaneous global-section and cusp requirements
-- reduce exactly to vanishing at the boundary, since regularity elsewhere was proved.
theorem global_cusp_iff_boundary {D : D7} {T : Top D} (h : LawsP T) {st : StFams D}
    (R : RowKits T h st) {j : ℕ} (hj : InR D j) (w : WeightFamilies.Wt D j)
    (f : (recB h.toLawsCore).Cusp j w) (k : (R.F.at (datW D R.F.κg j)).Comp) :
    let d := datW D R.F.κg j
    let C := (R.k.at d).Φ.C k
    let Δ := (R.F.at d).Lw R.L (R.k.at d).Φ k (wtOfN d.N w)
    let v := cmpAt h R.tie R.k hj w.n k f.1
    (v ∈ C.Y.H0 Δ ∧ C.Y.vanishOn Δ v C.Ybd) ↔ C.Y.vanishOn Δ v C.Ybd := by
  dsimp only
  refine ⟨And.right, fun hv => ⟨?_, hv⟩⟩
  apply GlobalTheory.ProjVar.Var.mem_riemannRochSpace_iff_regularAt_everywhere.2
  intro y
  by_cases hy : y ∈ ((R.k.at _).Φ.C k).Ybd
  · exact (GlobalTheory.Cartier.CartierDiv.vanishesAt_iff.1 (hv y hy)).1
  · exact regular_off_boundary h R hj w f k y hy

#print axioms global_cusp_iff_boundary
#print axioms regular_off_boundary
end GeometryAudit.FormRegularity
