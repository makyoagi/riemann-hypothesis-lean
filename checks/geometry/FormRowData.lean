import Formalism.LocalToGlobal.ProjectiveLattices.ESecPfA
import FormPoints

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.ShFam GlobalTheory.TrueGeo GlobalTheory.LocM
open GeometryAudit.FamilyTop GeometryAudit.FamilyLaws GeometryAudit.FormPoints
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GeometryAudit.FormRowData
noncomputable section
open Classical

variable {D : D7} {T : Top D} (h : LawsP T) {st : StFams D} (R : RowKits T h st)

def rowPoint {j : ℕ} {la : HeightOneSpectrum (𝓞 T.Q.c.F)} (x : points h R j la) : (familyTop h R.k).PtA j la :=
  if hj : InR D j then rowEquiv h R hj la x
  else (cast (show points h R j la = Empty from if_neg hj) x).elim

def value {j : ℕ} {la : HeightOneSpectrum (𝓞 T.Q.c.F)} (x : points h R j la)
    {w : WeightFamilies.Wt D j} (f : (recB h.toLawsCore).Cusp j w) : EReal :=
  vAtV (rowPoint h R x) f.1

def product {j : ℕ} {w w' : WeightFamilies.Wt D j}
    (f : (recB h.toLawsCore).Cusp j w) (g : (recB h.toLawsCore).Cusp j w') :
    (recB h.toLawsCore).Cusp j (WeightAlgebra.wadd w w') :=
  if hj : InR D j then esecMul h hj f g else 0

theorem value_mul {j : ℕ} {la : HeightOneSpectrum (𝓞 T.Q.c.F)} (x : points h R j la)
    {w w' : WeightFamilies.Wt D j} (f : (recB h.toLawsCore).Cusp j w) (g : (recB h.toLawsCore).Cusp j w') :
    value h R x (product h f g) = value h R x f + value h R x g := by
  by_cases hj : InR D j
  · rw [product, dif_pos hj]
    exact vAtV_mul (rowPoint h R x) f.1 g.1
  · exact (cast (show points h R j la = Empty from if_neg hj) x).elim

theorem integral_iff (j : ℕ) (w : WeightFamilies.Wt D j) (f : (recB h.toLawsCore).Cusp j w) :
    f ∈ (recB h.toLawsCore).Mlat j w ↔ ∀ la (x : points h R j la), 0 ≤ value h R x f := by
  by_cases hj : InR D j
  · let H := family_laws h R
    have e := (recPJ H j hj).Mlat_eq w f
    change f ∈ (recB h.toLawsCore).Mlat j w ↔ _ at e
    rw [e]
    constructor
    · intro hall la x
      have hv := hall la (rowEquiv h R hj la x)
      have E := recPJ_vAt_inc H j hj la (rowEquiv h R hj la x) w f
      exact (hv.trans_eq E).trans_eq (congrArg (fun p => vAtV p f.1) (show rowPoint h R x = rowEquiv h R hj la x from dif_pos hj)).symm
    · intro hall la y
      obtain ⟨x, rfl⟩ := (rowEquiv h R hj la).surjective y
      have E := recPJ_vAt_inc H j hj la (rowEquiv h R hj la x) w f
      exact ((hall la x).trans_eq (congrArg (fun p => vAtV p f.1) (show rowPoint h R x = rowEquiv h R hj la x from dif_pos hj))).trans_eq E.symm
  · have ef := cutR_zero T.C hj f
    rw [ef]
    exact ⟨fun _ la x => (cast (show points h R j la = Empty from if_neg hj) x).elim,
      fun _ => Submodule.zero_mem _⟩

def theta {j : ℕ} (w : WeightFamilies.Wt D j) : Submodule (𝓞 T.Q.c.F) ((recB h.toLawsCore).Cusp j w) :=
  spanIn T.C j w (T.th j w)

def shortTheta {j : ℕ} (w : WeightFamilies.Wt D j) : Submodule (𝓞 T.Q.c.F) ((recB h.toLawsCore).Cusp j w) :=
  spanIn T.C j w (T.sh j w)

theorem theta_eq {j : ℕ} (hj : InR D j) (w : WeightFamilies.Wt D j) :
    theta h w = (recPJ (family_laws h R) j hj).thAll w ∧
    shortTheta h w = (recPJ (family_laws h R) j hj).shortTh w := ⟨rfl, rfl⟩

end
#print axioms integral_iff
#print axioms value_mul
#print axioms theta_eq
end GeometryAudit.FormRowData
