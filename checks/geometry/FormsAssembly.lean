import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports
import FormSpan
import RowComparison
import FormMultiplication
import FormRowData

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.ShFam GlobalTheory.TrueGeo GlobalTheory.LocM
open GeometryAudit.FamilyTop GeometryAudit.FamilyLaws GeometryAudit.FormComparison GeometryAudit.FormRowData
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GeometryAudit.FamilyForms
noncomputable section
open Classical

variable {D : D7} {T : Top D} (h : LawsP T) {st : StFams D} (R : RowKits T h st)

variable (A : RowComparison h R)

private theorem map_zero_of_eq (B : WeightFamilies.Prov D) {F : Type} [Field F]
    (i : B.KO →+* F) (j : ℕ) (w : WeightFamilies.Wt D j) (Y : GlobalTheory.ProjVar.Var F)
    (L : RowMap B i j w Y) (f : B.Cusp j w) (e : f = 0) : L f = 0 :=
  (congrArg L e).trans L.map_zero

private theorem outside_zero {j : ℕ} (hj : ¬ InR D j) (w : WeightFamilies.Wt D j) (k : (R.F.at (datW D R.F.κg j)).Comp) (f : (recB h.toLawsCore).Cusp j w) :
    A.cmp j w k f = 0 := map_zero_of_eq (recB h.toLawsCore) (coefficientMap h R) j w
      ((R.k.at (datW D R.F.κg j)).Φ.C k).Y (A.cmp j w k) f (cutR_zero T.C hj f)

private theorem comparison_section (j : ℕ) (w : WeightFamilies.Wt D j) (k : (R.F.at (datW D R.F.κg j)).Comp)
    (f : (recB h.toLawsCore).Cusp j w) :
    let d := datW D R.F.κg j
    let C := (R.k.at d).Φ.C k
    let Δ := (R.F.at d).Lw R.L (R.k.at d).Φ k (wtOfN d.N w)
    A.cmp j w k f ∈ C.Y.H0 Δ ∧ C.Y.vanishOn Δ (A.cmp j w k f) C.Ybd := by
  let d := datW D R.F.κg j
  let C := (R.k.at d).Φ.C k
  let Δ := (R.F.at d).Lw R.L (R.k.at d).Φ k (wtOfN d.N w)
  let good (v : C.Y.Fn) := v ∈ C.Y.H0 Δ ∧ C.Y.vanishOn Δ v C.Ybd
  change good (A.cmp j w k f)
  by_cases hj : InR D j
  · exact (congrArg good (A.agrees j hj w k f)).mpr (FormBoundary.global_cusp_value h R hj w f k)
  · exact (congrArg good (outside_zero h R A hj w k f)).mpr
      ⟨(C.Y.H0 Δ).zero_mem, fun y _ => Δ.vanishesAt_zero y⟩

private theorem comparison_mul (j : ℕ) (w w' : WeightFamilies.Wt D j)
    (k : (R.F.at (datW D R.F.κg j)).Comp) (f : (recB h.toLawsCore).Cusp j w) (g : (recB h.toLawsCore).Cusp j w') :
    A.cmp j (WeightAlgebra.wadd w w') k (product h f g) = A.cmp j w k f * A.cmp j w' k g := by
  by_cases hj : InR D j
  · have ep : product h f g = esecMul h hj f g := dif_pos hj
    have e1 := (congrArg (A.cmp j _ k) ep).trans (A.agrees j hj _ k (esecMul h hj f g))
    have e2 := FormMultiplication.multiplicative_comparison h R hj w w' f.1 g.1 k
    exact (e1.trans e2).trans (congrArg₂ (· * ·) (A.agrees j hj w k f) (A.agrees j hj w' k g)).symm
  · exact (outside_zero h R A hj _ k _).trans ((congrArg (· * A.cmp j w' k g)
      (outside_zero h R A hj w k f)).trans (zero_mul _)).symm

private theorem transfer_span {F S I : Type} [Field F] (Y : I → GlobalTheory.ProjVar.Var F)
    (P Q : S → ∀ k, (Y k).Fn) (same : ∀ f k, P f k = Q f k) (t : ∀ k, (Y k).Fn)
    (ht : t ∈ Submodule.span F (Set.range Q)) : t ∈ Submodule.span F (Set.range P) :=
  (congrArg (fun U => t ∈ Submodule.span F (Set.range U)) (funext fun f => funext (same f))).mpr ht

private theorem comparison_span (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (w : WeightFamilies.Wt D j) :
    let d := datW D R.F.κg j
    ∀ t : ∀ k : (R.F.at d).Comp, ((R.k.at d).Φ.C k).Y.Fn,
      (∀ k, let C := (R.k.at d).Φ.C k
            let Δ := (R.F.at d).Lw R.L (R.k.at d).Φ k (wtOfN d.N w)
            t k ∈ C.Y.H0 Δ ∧ C.Y.vanishOn Δ (t k) C.Ybd) →
      t ∈ Submodule.span D.what₂.LL (Set.range fun (f : (recB h.toLawsCore).Cusp j w) k => A.cmp j w k f) :=
  fun t ht => transfer_span (fun k => ((R.k.at (datW D R.F.κg j)).Φ.C k).Y)
    (fun f k => A.cmp j w k f) (fun f k => cmpAt h R.tie R.k ⟨h1, h2⟩ w.n k f.1)
    (fun f k => A.agrees j ⟨h1, h2⟩ w k f) t (FormSpan.span_global_cusp h R ⟨h1, h2⟩ w t ht)

def forms : FormsOver (cutSt _) (resSt _) R.k where
  KO := (recB h.toLawsCore).KO
  fKO := (recB h.toLawsCore).fKO
  nfKO := (recB h.toLawsCore).nfKO
  eO := (recB h.toLawsCore).eO
  kL := coefficientMap h R
  kL_eO := coefficientMap_pinned h R
  Cusp := (recB h.toLawsCore).Cusp
  acgC := (recB h.toLawsCore).acgC
  modC := (recB h.toLawsCore).modC
  fdC := (recB h.toLawsCore).fdC
  modOC := (recB h.toLawsCore).modOC
  towC := (recB h.toLawsCore).towC
  cmp := by kexactB A.cmp
  cmp_mem j w k f := by kexactB (comparison_section h R A j w k f).1
  cmp_cusp j w k f := by kexactB (comparison_section h R A j w k f).2
  cmp_span := by kexactB comparison_span h R A
  cmp_indep := by kexactB A.indep
  mulC := fun _ _ _ => product h
  cmp_mul := by kexactB comparison_mul h R A
  supN := (recB h.toLawsCore).supN
  supN_nonneg := (recB h.toLawsCore).supN_nonneg
  supN_eq_zero := (recB h.toLawsCore).supN_eq_zero
  supN_smul := (recB h.toLawsCore).supN_smul
  supN_add := (recB h.toLawsCore).supN_add
  l2NormAlt := (recB h.toLawsCore).l2NormAlt
  l2Norm_nonneg_bis := (recB h.toLawsCore).l2Norm_nonneg_bis
  l2Norm_eq_zero_iff := (recB h.toLawsCore).l2Norm_eq_zero_iff
  l2Norm_smul_alt := (recB h.toLawsCore).l2Norm_smul_alt
  l2Norm_add_le' := (recB h.toLawsCore).l2Norm_add_le'
  l2Norm_le_supNorm_alt := (recB h.toLawsCore).l2Norm_le_supNorm_alt
  Cu := (recB h.toLawsCore).Cu
  Xc := (recB h.toLawsCore).Xc
  Xc_lat := (recB h.toLawsCore).Xc_lat
  FJt := (recB h.toLawsCore).FJt
  acgF := (recB h.toLawsCore).acgF
  modF := (recB h.toLawsCore).modF
  sg := (recB h.toLawsCore).sg
  Pt := FormPoints.points h R
  pt66 := FormPoints.pointMap h R
  vAtC := fun _ _ x _ f => value h R x f
  vAtC_zero := fun _ _ x _ => vAtV_zero (rowPoint h R x)
  vAtC_ne_bot := fun _ _ x _ f => vAtV_ne_bot (rowPoint h R x) f.1
  vAtC_add := fun _ _ x _ f g => vAtV_add (rowPoint h R x) f.1 g.1
  vAtC_smul := fun _ _ x _ a f ha => vAtV_smul (rowPoint h R x) a f.1 ha
  vAtC_mul := fun _ _ x _ _ f g => value_mul h R x f g
  thAll := fun _ => theta h
  shortTh := fun _ => shortTheta h

theorem forms_base : (forms h R A).toWeightFamilies = recB h.toLawsCore := by
  let B := recB h.toLawsCore
  have lat : (forms h R A).Mlat = B.Mlat := by
    funext j w
    exact SetLike.ext fun f => (integral_iff h R j w f).symm
  exact congrArg (fun M => { B with Mlat := M }) lat

theorem forms_are : FormsAre (family_laws h R) R.tie (cutSt _) (resSt _) R.k (forms h R A) where
  base := forms_base h R A
  kL := by
    intro x x' hx
    change T.Q.c.F at x
    obtain rfl := eq_of_heq hx
    exact (R.F.κg.e_emb _).symm.trans (congrArg (fun a : R.F.κg.c.F => (a : ℂ)) (R.F.κg.e.apply_symm_apply _))
  cmp := by
    intro j hj w k f f' hf
    obtain rfl := eq_of_heq hf
    exact A.agrees j hj w k _
  pts := by
    intro j hj la la' e
    obtain rfl := eq_of_heq e
    refine ⟨FormPoints.rowEquiv h R hj _, fun x hm => FormPoints.pointMap_img h R hj hm _ x, ?_⟩
    intro x w f f' hf
    obtain rfl := eq_of_heq hf
    exact congrArg (fun y => vAtV y f.1) (show rowPoint h R x = FormPoints.rowEquiv h R hj _ x from dif_pos hj)
  th := by
    intro j hj w
    obtain ⟨a, b⟩ := theta_eq h R hj w
    exact ⟨heq_of_eq a, heq_of_eq b⟩

end
#print axioms forms_are
end GeometryAudit.FamilyForms
