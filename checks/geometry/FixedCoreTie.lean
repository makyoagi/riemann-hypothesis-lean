import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LargeFor
import Formalism.LocalToGlobal.ProjectiveLattices.MapRingEquivTransApply

open Formalism.BasicNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.ShFam
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Level Moduli)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GeometryAudit.FixedCore

private theorem level_ext {D : D7} {P : Top D} {a b : Level P.Q.H}
    (hm : a.M = b.M) (hb : a.Mb = b.Mb) (ha : a.A = b.A) : a = b := by
  cases a; cases b
  dsimp only at hm hb ha
  subst_vars
  rfl

private theorem prescribed_signature {D : D7} (P : Top D) (h : LawsP P) (sys : SysExSt)
    (F : SrcFam (ambOf P.Q h.pins.1)) (N i : ℕ) (hN : 2 ≤ N) (hi : i ≤ N) :
    ∃ S : Sig (ambOf P.Q h.pins.1) N i, ∀ j, InR D j → N = D.R.r → i = (D.R.sigW j).1 →
      (⟨P.Q.l, P.Q.Dw j, P.Q.Xo j⟩ : MD P.Q.H) = ⟨P.Q.l, S.Dw, S.Xo P.Q.l⟩ := by
  classical
  by_cases hit : ∃ j, InR D j ∧ N = D.R.r ∧ i = (D.R.sigW j).1
  · obtain ⟨j, hj, hNr, hiw⟩ := hit
    obtain ⟨hp, hq, _⟩ := h.pins.2.2.2 j hj
    have hr : (P.Q.Dw j).p + (P.Q.Dw j).q = N := by rw [hp, hq, sigW_sum D hj.1 hj.2, hNr]
    let models (k : Level P.Q.H) : Moduli (P.Q.Dw j) k :=
      if e : P.Q.l = k then e ▸ P.Q.Xo j
      else (GlobalTheory.Moduli.moduli_scheme_exists _ P.Q.H (P.Q.Dw j) k (by omega)).some
    have atBase : models P.Q.l = P.Q.Xo j := by simp [models]
    obtain ⟨s, ⟨tor⟩⟩ := sys _ P.Q.H (P.Q.Dw j) (by omega) models
    refine ⟨⟨P.Q.Dw j, hp.trans hiw.symm, hr, hN, models, s, tor⟩, ?_⟩
    intro j' hj' _ eqi
    have e : j = j' := by
      have hj1 := hj.1
      have hj2 := hj'.1
      simp only [Ranks.sigW] at hiw eqi
      omega
    subst j'
    exact congrArg (fun m => (⟨P.Q.l, P.Q.Dw j, m⟩ : MD P.Q.H)) atBase.symm
  · exact ⟨F.sig N i hN hi, fun j hj e1 e2 => (hit ⟨j, hj, e1, e2⟩).elim⟩

-- The input family supplies levels and coefficient fields. Its signatures and
-- universal models may be replaced. The fixed P, its core, Dw and Xo are inputs.
theorem parTie_of_pinned_source {D : D7} (P : Top D) (h : LawsP P) (sys : SysExSt)
    {c : ℕ} (F : SrcFam (ambOf P.Q h.pins.1)) (pin : F.Pinned P.pb c) :
    ∃ F' : SrcFam (ambOf P.Q h.pins.1), F'.Pinned P.pb c ∧ ParTie P.Q h.pins.1 F' := by
  classical
  let A := ambOf P.Q h.pins.1
  have hlev : P.Q.l = F.κg.l := level_ext (P := P) (h.pins.2.1.1.trans F.κg_M.symm)
    (h.half.2.trans pin.1.symm) (h.pins.2.1.2.trans F.κg_A.symm)
  choose sig hsig using prescribed_signature P h sys F
  have key (j : ℕ) (hj : InR D j) := hsig _ _ (datW D F.κg j).two_le (datW D F.κg j).j_le
    j hj (datW_N D F.κg j) (datW_j D F.κg hj.1 hj.2)
  let F' : SrcFam A := { F with
    sig := sig
    src := fun N i hn hi κ => (nonempty_src_of_sig (sig N i hn hi) κ).some
    dat := fun j hj => Eq.mp (congrArg (fun m : MD P.Q.H => IsDatW D j m.2.1) (key j hj)) (h.pins.2.2.2 j hj)
    Us := fun j => (A.nonempty_unfFam _ F.cs
      ((sig _ _ (datW D F.κg j).two_le (datW D F.κg j).j_le).rank_eq.trans (datW_N D F.κg j))
      (one_le_two.trans (two_le_r D))).some }
  refine ⟨F', pin, ⟨fun j hj => ?_, (Par.F_le h.pins.2.2.1 F.pins.2.2.1).trans (F.cs_le _)⟩⟩
  let S := sig _ _ (datW D F.κg j).two_le (datW D F.κg j).j_le
  exact (key j hj).trans (congrArg (fun k => (⟨k, S.Dw, S.Xo k⟩ : MD P.Q.H)) hlev)

#print axioms parTie_of_pinned_source
end GeometryAudit.FixedCore
