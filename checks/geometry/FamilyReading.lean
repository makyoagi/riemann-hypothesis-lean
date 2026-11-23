import FamilyForms
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.RealGeo GlobalTheory.LocM
open GeometryAudit.FamilyTop GeometryAudit.FamilyForms
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GeometryAudit.ReadingRealisation
noncomputable section

-- Express the lattice and norm tests on the ambient core rules so equality
-- of cusp submodules transports the subspace, map and comparison together.
private def realisesOn {D : D7} {T : Core D} (h : LawsCore T) (j : ℕ)
    (w : WeightFamilies.Wt D j) (vol : ℝ) (U : Submodule T.Q.c.F (T.R j)) : Prop :=
  ∃ (s : Submodule T.Q.c.F U) (φ : s →ₛₗ[T.σ₀] D.what₂.Mj j),
    (∀ {n : ℕ} (v : Fin n → s), LinearIndependent T.Q.c.F v → LinearIndependent ℂ (φ ∘ v)) ∧
    Submodule.span ℂ (Set.range φ) = ⊤ ∧
    (D.what₂.MjLat j).carrier ⊆ Set.range φ ∧
    (∀ x : s, (∀ la (y : T.PtM j la), 0 ≤ y.val x.val.val) ↔ φ x ∈ (D.what₂.MjLat j).carrier) ∧
    (∀ x : s, ‖φ x‖ = Real.sqrt (vol * dimKap D j) * h.Nl j w T.σ₀ x.val.val)

theorem family_sat {D : D7} {T : Top D} (h : LawsP T) {st : StFams D} (R : RowKits T h st)
    {j : ℕ} (hj : InR D j) (w : WeightFamilies.Wt D j) (hn : w.n = D.R.nV)
    (hw : wtOf w = DV.kapW D j) (vol : ℝ) (realised : MjCusp h.toLawsCore j w vol) :
    (family h R).P.MjSat j vol := by
  let A := rowComparison h R
  let P := forms h R A
  let r := realisesOn h.toLawsCore j w vol
  have core : r (T.C j w) := realised
  obtain ⟨s, φ, hi, hs, hc, hl, hnrm⟩ := (congrArg r (cutR_eq T.C hj w)).mpr core
  have sig : P.sig0 = T.σ₀ :=
    RingHom.ext fun a => (forms_are h R A).kL a a (HEq.refl a)
  change P.MjSat j vol
  unfold FormsPkg.MjSat
  rw [sig]
  refine ⟨w, hn, hw, s, φ, hi, hs, hc, ?_, ?_⟩
  · intro x
    change x.val ∈ P.toWeightFamilies.Mlat j w ↔ _
    have ml : x.val ∈ P.Mlat j w ↔ x.val ∈ (recB h.toLawsCore).Mlat j w := by
      exact (FormRowData.integral_iff h R j w x.val).symm
    refine ml.trans (Iff.trans ?_ (hl x))
    exact ⟨fun ht la y => ht la y.1 y.2, fun ht la v hv => ht la ⟨v, hv⟩⟩
  · intro x
    change ‖φ x‖ = Real.sqrt (vol * dimKap D j) * cutN T.C h.Nl j w T.σ₀ x.val
    have e : cutN T.C h.Nl j w T.σ₀ x.val = h.Nl j w T.σ₀ x.val.val := if_pos hj
    exact (hnrm x).trans (congrArg (fun a : ℝ => Real.sqrt (vol * dimKap D j) * a) e).symm

end
#print axioms family_sat
end GeometryAudit.ReadingRealisation
