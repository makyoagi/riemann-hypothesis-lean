import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuotMeasureEqSmul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRangeMulVec

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions
open Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.RealGeo
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GeometryAudit.ReadingRealisation
noncomputable section

private theorem lift_on_range {K U M H : Type} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup M] [Module ℂ M] [AddCommGroup H] [Module ℂ H] {σ : K →+* ℂ}
    (J : U →ₛₗ[σ] H) (E : M →ₗ[ℂ] H) (inj : Function.Injective E) :
    ∃ φ : (LinearMap.range E).comap J →ₛₗ[σ] M, ∀ x, E (φ x) = J x.val := by
  let F := LinearEquiv.ofInjective E inj
  let g : (LinearMap.range E).comap J →ₛₗ[σ] LinearMap.range E :=
    (J.domRestrict _).codRestrict _ (fun x => x.property)
  exact ⟨F.symm.toLinearMap.comp g, fun x => congrArg Subtype.val (F.apply_symm_apply (g x))⟩

private theorem norm_from_scaled {a b d n u : ℝ} (ha : 0 < a) (hn : 0 ≤ n) (hu : 0 ≤ u)
    (scaled : u ^ 2 = a * n ^ 2) (l : ℝ) (arch : u = Real.sqrt (b * d) * l) :
    n = Real.sqrt (b / a * d) * l := by
  have hn' : n * Real.sqrt a = u := by
    have e : (n * Real.sqrt a) ^ 2 = u ^ 2 := by rw [mul_pow, Real.sq_sqrt ha.le, scaled, mul_comm]
    nlinarith [mul_nonneg hn (Real.sqrt_nonneg a), sq_nonneg (n * Real.sqrt a - u)]
  have e : b * d = (b / a * d) * a := by field_simp
  apply mul_right_cancel₀ (Real.sqrt_pos.mpr ha).ne'
  rw [hn', arch, e, Real.sqrt_mul' _ ha.le]
  ring

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type}
    {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL]
    (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

theorem normed_realisation (h : LawsCore T.toCore) (hK : DV.KapDef D) (hR : PreChar R)
    (tie : TieIn T R κ v₀) (ev : JEvExists T R κ v₀) {F : Face D A}
    (mj : MjTie R F) (i : Fin D.R.m) :
    let J := jTop T R κ v₀ i (sg0 D A)
    let s := (LinearMap.range (mj.eW i)).comap J
    ∃ φ : s →ₛₗ[T.σ₀] D.what₂.Mj ((i : ℕ) + 1), ∀ x : s,
      mj.eW i (φ x) = J x.val ∧
      ‖φ x‖ = Real.sqrt (volRec R F i * Formalism.L2.Geo.dimKap D ((i : ℕ) + 1)) *
        h.Nl ((i : ℕ) + 1) (κ i) T.σ₀ (x.val : T.R ((i : ℕ) + 1)) := by
  let J := jTop T R κ v₀ i (sg0 D A)
  have ha := RealDat.nP_pos (F := F) false
  have inj := GlobalTheory.Mem.LiftForms.inj_of_norm_sq (mj.eW i) ha (mj.eW_norm i)
  obtain ⟨g, hg⟩ := lift_on_range J (mj.eW i) inj
  have hs : res T (sg0 D A) = T.σ₀ :=
    (congrArg (res T) (sgAt_mk _ R.hv0)).trans (res_embLL T tie.alg tie.laws.pins.2.2.1)
  let φ : (LinearMap.range (mj.eW i)).comap J →ₛₗ[T.σ₀] D.what₂.Mj ((i : ℕ) + 1) :=
    { toFun := g, map_add' := g.map_add, map_smul' := fun a x => (g.map_smulₛₗ a x).trans
        (congrArg (fun f : T.Q.c.F →+* ℂ => f a • g x) hs) }
  refine ⟨φ, fun x => ⟨hg x, ?_⟩⟩
  apply norm_from_scaled ha (norm_nonneg _) (norm_nonneg (mj.eW i (g x))) (mj.eW_norm i (g x))
  rw [hg x]
  exact GlobalTheory.ReadingNorm.norm_jTop D G Pl0 T0 A T R κ v₀ h hK hR tie ev i x.val

end
#print axioms normed_realisation
end GeometryAudit.ReadingRealisation
