import FormComparison
import FormLaws

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.ShFam GlobalTheory.TrueGeo GlobalTheory.LocM
open GeometryAudit.FamilyTop GeometryAudit.FormComparison
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GeometryAudit.FamilyForms
noncomputable section
open Classical

variable {D : D7} {T : Top D} (h : LawsP T) {st : StFams D} (R : RowKits T h st)

abbrev RowMap (B : WeightFamilies.Prov D) {K : Type} [Field K] (i : B.KO →+* K)
    (j : ℕ) (w : WeightFamilies.Wt D j) (Y : GlobalTheory.ProjVar.Var K) :=
  B.Cusp j w →ₛₗ[i] Y.Fn

abbrev IndependentForms (B : WeightFamilies.Prov D) (j : ℕ) (w : WeightFamilies.Wt D j)
    {q : ℕ} (v : Fin q → B.Cusp j w) := LinearIndependent B.KO v

abbrev IndependentSections {K ι : Type} [Field K] (Y : ι → GlobalTheory.ProjVar.Var K)
    {q : ℕ} (v : Fin q → ∀ k, (Y k).Fn) := LinearIndependent K v

structure ComparisonData (B : WeightFamilies.Prov D) {K : Type} [Field K] (i : B.KO →+* K)
    {I : ℕ → Type} (Y : ∀ j, I j → GlobalTheory.ProjVar.Var K)
    (ev : ∀ j, InR D j → ∀ (w : WeightFamilies.Wt D j) (k : I j), B.Cusp j w → (Y j k).Fn) where
  cmp : ∀ j (w : WeightFamilies.Wt D j) (k : I j), RowMap B i j w (Y j k)
  agrees : ∀ j (hj : InR D j) w k f, cmp j w k f = ev j hj w k f
  indep : ∀ j w {q : ℕ} (v : Fin q → B.Cusp j w), IndependentForms B j w v →
    IndependentSections (Y j) (fun i k => cmp j w k (v i))

abbrev RowComparison := ComparisonData (recB h.toLawsCore) (coefficientMap h R)
  (fun j k => ((R.k.at (datW D R.F.κg j)).Φ.C k).Y)
  (fun _ hj w k f => cmpAt h R.tie R.k hj w.n k f.1)

private abbrev restrictRule {K F V : Type} [Field K] [Field F] [AddCommGroup V] [Module K V]
    (p : Submodule K V) (Y : GlobalTheory.ProjVar.Var F) (i : K →+* F) (f : V →ₛₗ[i] Y.Fn) :
    p →ₛₗ[i] Y.Fn := f.domRestrict p

def compare (j : ℕ) (w : WeightFamilies.Wt D j) (k : (R.F.at (datW D R.F.κg j)).Comp) :
    RowMap (recB h.toLawsCore) (coefficientMap h R) j w ((R.k.at (datW D R.F.κg j)).Φ.C k).Y :=
  if hj : InR D j then restrictRule (cutR T.C j w) ((R.k.at (datW D R.F.κg j)).Φ.C k).Y
    (coefficientMap h R) (evaluated h R hj w.n k) else 0

theorem compare_eq {j : ℕ} (hj : InR D j) (w : WeightFamilies.Wt D j) (k : (R.F.at (datW D R.F.κg j)).Comp)
    (f : (recB h.toLawsCore).Cusp j w) : compare h R j w k f = cmpAt h R.tie R.k hj w.n k f.1 := by
  have e := evaluated_eq h R hj w.n k f.1
  exact (congrArg (fun L : RowMap (recB h.toLawsCore) (coefficientMap h R) j w _ => L f)
    (show compare h R j w k = _ from dif_pos hj)).trans e

private theorem empty_indices (B : WeightFamilies.Prov D) (j : ℕ) (w : WeightFamilies.Wt D j)
    {q : ℕ} (v : Fin q → B.Cusp j w) (hv : IndependentForms B j w v) (zero : ∀ i, v i = 0) :
    IsEmpty (Fin q) := ⟨fun i => hv.ne_zero i (zero i)⟩

def rowComparison : RowComparison h R where
  cmp := compare h R
  agrees := fun _ hj w k f => compare_eq h R hj w k f
  indep j w {q} v hv := by
    by_cases hj : InR D j
    · have eq : (fun i k => compare h R j w k (v i)) =
          (fun i k => cmpAt h R.tie R.k hj w.n k (v i).1) :=
        funext fun i => funext fun k => compare_eq h R hj w k (v i)
      exact eq.symm ▸ FormLaws.independent_comparison h R hj w v hv
    · have : IsEmpty (Fin q) := empty_indices (recB h.toLawsCore) j w v hv (fun i => cutR_zero T.C hj (v i))
      exact linearIndependent_empty_type

end
#print axioms rowComparison
end GeometryAudit.FamilyForms
