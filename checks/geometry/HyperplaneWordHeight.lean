import AssignedWordVariation
import ProductionSwapFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArithmeticNefModelOfAmpleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPow

open NumberField Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions GlobalTheory
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mem.Top.Bl
open GeometryAudit.ArchWeightTest GeometryAudit.ProductionLevelHeight GeometryAudit.LevelPrimeHeight
open UpperTheory.Top

namespace GeometryAudit.HyperplaneWordHeight

noncomputable section

variable {K : Type} [Field K] [NumberField K]

/-- A hyperplane of the given embedding that misses the generic point. -/
def hyperplane (Y : Var K) : Y.Dv := Y.hyp Y.exists_coord_ne_zero.choose_spec

/-- Fix the model and its Hermitian metric before using any word data. -/
structure HyperplaneModel (Y : Var K) where
  q : ℕ+
  Z : TrueGeo.Model Y
  L : HermLB Z.p
  r : (L.B.pull Z.j).ι → Y.Fnˣ
  presents : Presents ((q : ℕ) • hyperplane Y) (L.B.pull Z.j) r
  nef : ArInt.NefFib L

private theorem model_exists (Y : Var K) : Nonempty (HyperplaneModel Y) := by
  have ample : Y.ample (hyperplane Y) := Y.ample_hyp Y.exists_coord_ne_zero.choose_spec
  obtain ⟨q, Z, L, r, presents, nef, _⟩ := T.exists_arithmetic_nef_model_of_ample K Y _ ample
  exact ⟨⟨q, Z, L, r, presents, nef⟩⟩

def fixedModel (Y : Var K) : HyperplaneModel Y := Classical.choice (model_exists Y)

private theorem induced_power {Y : Var K} (B : HyperplaneModel Y) (n : ℕ) :
    ∃ A : Adl (cxSt K) Y, A.D = n • ((B.q : ℕ) • hyperplane Y) ∧
      A.n = 1 ∧ A.ci = 0 ∧ A.Induced B.Z (B.L.pow n) 1 0 :=
  OfModel.exists_induced K (cxSt K) Y B.Z (B.L.pow n) _ _
    (InducedPow.presents_pow B.L.B B.Z.j n B.L.isLB B.presents)

/-- Descend the actual n-th tensor power of one Hermitian model bundle.
    Dividing by the fixed model index q gives the hyperplane normalization. -/
def power {Y : Var K} (B : HyperplaneModel Y) (n : ℕ) : Adl (cxSt K) Y :=
  (induced_power B n).choose.divide B.q

theorem power_induced {Y : Var K} (B : HyperplaneModel Y) (n : ℕ) :
    (power B n).Induced B.Z (B.L.pow n) 1 0 := by
  unfold power
  have h := (induced_power B n).choose_spec.2.2.2.divide B.q
  convert h using 1
  funext v
  simp

theorem power_isModel {Y : Var K} (B : HyperplaneModel Y) (n : ℕ) : (power B n).IsModel :=
  ⟨B.Z, B.L.pow n, 1, 0, power_induced B n⟩

attribute [local instance] Host.cmStar

/-- Use only the word's total degree to select a tensor power on this component. -/
def bundle {D : D7} (X : DivX D) (geo : X.geo = geoTrue D.what₂.LL)
    (j : ℕ) (c : X.Comp j) (u : D.what₂.Word) :=
  power (fixedModel (sectionData X geo j c).Y) (totalWeight D u + 1)

/-- Two words on an inhabited strengthened row give the same modeled bundle
    and different assigned heights at the family's own size constant. -/
theorem realized_mismatch : ∃ (eps : ℝ) (F : FamP eps), 0 < eps ∧
    (GChi Formalism.HC.PChar.one).cls (3/2) F ∧
    (∃ κ : GlobalTheory.Fc.Par, GlobalTheory.Fc.Link κ F ∧ F.Csz = κ.C.Csz) ∧
    ∀ cutoff : ℝ, ∃ (x : ℝ) (i : F.Ix x), cutoff ≤ x ∧ x ∈ F.Win ∧
      ∃ (J : Formalism.L2.Pj.Core (F.D x i)) (g : GeoCl productionPredicate (F.D x i) J (F.X x i)),
        let D := F.D x i
        let X := F.X x i
        let geo := Replacement.geometry_of_closure g
        (∀ w, D.div.h w = hExpl6 D (F.L x i) X F.Csz w) ∧ Nonempty (X.Comp 1) ∧
        ∃ (u v : D.what₂.Word),
          totalWeight D u = totalWeight D v ∧ D.div.h u ≠ D.div.h v ∧
          ∀ (j : ℕ) (d : X.Comp j),
            let A := bundle X geo j d
            (A u).IsModel ∧ A u = A v ∧
              (normalized (A u) ≠ D.div.h u ∨ normalized (A v) ≠ D.div.h v) := by
  obtain ⟨eps, F, pos, member, constants, rows⟩ := ProductionSwapFamily.realized_family
  obtain ⟨cut, bound⟩ := AssignedWordVariation.weights_below_primes F pos
  refine ⟨eps, F, pos, member, constants, fun cutoff => ?_⟩
  obtain ⟨x, large, above, win, ⟨i⟩⟩ := F.toFamCore.exists_pt (max cutoff cut)
  obtain ⟨pair, J, g⟩ := rows x above i
  obtain ⟨u, v, same, distinct, _⟩ := AssignedWordVariation.assigned_differs_same_weight F above i
    pair (bound x ((le_max_right _ _).trans large) i)
  obtain ⟨c, _⟩ := obstructed_component g (F.L x i) 1 le_rfl
    (by have := (F.D x i).R.two_le_m; omega)
  refine ⟨x, i, (le_max_left _ _).trans large, win, J, g, F.h_eq x above i,
    ⟨c⟩, u, v, same, distinct, fun j d => ?_⟩
  let A := bundle (F.X x i) (Replacement.geometry_of_closure g) j d
  have eqn : A u = A v := by dsimp only [A, bundle]; rw [same]
  refine ⟨power_isModel _ _, eqn, ?_⟩
  by_contra! heq
  exact distinct (heq.1.symm.trans ((congrArg normalized eqn).trans heq.2))

#print axioms power_induced
#print axioms realized_mismatch

end
end GeometryAudit.HyperplaneWordHeight
