import LevelPrimeHeight
import ReplacementGeometry

open NumberField Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions
open Formalism.MainNotions.HeightShare GlobalTheory.Mem.Top.Bl GlobalTheory.TrueGeo
open GeometryAudit.LevelPrimeHeight GeometryAudit.FamilyComponentIntersection

namespace GeometryAudit.ProductionLevelHeight

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def sectionData {D : D7} (X : DivX D) (geo : X.geo = geoTrue D.what₂.LL)
    (j : ℕ) (c : X.Comp j) : LData (geoTrue D.what₂.LL) :=
  cast (congrArg (fun G => LData G) geo) (componentData X j c)

def height {D : D7} (L : SizeData₂ D) (X : DivX D) (geo : X.geo = geoTrue D.what₂.LL)
    (j : ℕ) (c : X.Comp j) (u : D.what₂.Word) : ℝ :=
  normalized (wordBundle L (sectionData X geo j c).Lbar u)

def arch {D : D7} (L : SizeData₂ D) (u : D.what₂.Word) : ℝ :=
  ∑ j ∈ SizeData₂.lifts D, ∑ τ : D.what₂.Tau, kerPlace D L u j τ

private theorem obstructed_model {Q : ∀ D : D7, GlobalTheory.ShFam.KitClass D}
    {D : D7} {J : Formalism.L2.Pj.Core D} {X : DivX D} (g : GeoCl (geoOf Q) D J X) :
    ∀ j, 1 ≤ j → j < D.R.m →
      ∃ c : X.Comp j, ¬ (sectionData X (Replacement.geometry_of_closure g) j c).Lbar.IsModel := by
  induction g with
  | base base =>
    intro j hj hm
    obtain ⟨⟨n, _, T, law, Φ, seed, iM, reg, _, rfl, reads, _⟩, _⟩ := base
    obtain ⟨c, _, bad, _⟩ := ProductionBoundary.earlier_row_obstruction Φ seed iM reg reads j hj hm
    exact ⟨c, bad⟩
  | step _ _ _ ih => exact ih

/-- A finite level twist leaves the divisor and its geometric degree unchanged.
    The normalization of the original section metric is exactly LData.h. -/
private theorem section_normalized {K : Type} [Field K] [NumberField K] [StarRing K]
    (B : LData (geoTrue K)) : normalized B.Lbar = B.h := by
  have eqn : (B.Lbar : Adl (cxSt K) B.Y).deg = B.del := by
    unfold Adl.deg
    rw [show ((B.Lbar.n : ℕ)) = 1 from rfl]
    simp only [Nat.cast_one, one_pow, div_one]
    rfl
  unfold normalized
  rw [eqn]
  rfl

/-- Substituting a word's Harish-Chandra parameter in the theta weight still
    gives the original weight. Its v and b entries are fixed across words. -/
theorem theta_weight_fixed (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (p q : ℕ) :
    Formalism.L2.NTheta.kapW (D.hcW u τ) p q = Formalism.L2.NTheta.kapW (D.hc τ) p q := by
  have same (n : ℕ) : Formalism.L2.NTheta.lamAt (D.hcW u τ) n =
      Formalism.L2.NTheta.lamAt (D.hc τ) n := by
    simp only [Formalism.L2.NTheta.lamAt, D.hcW_v u τ, D.hcW_b u τ]
  funext w
  cases w <;> simp [Formalism.L2.NTheta.kapW, Formalism.L2.NTheta.kapQ, same]

/-- The strengthened certificate supplies the section bundle. Even after its finite
    level twist, a component on each earlier row has height zero for every word. -/
theorem obstructed_component {Q : ∀ D : D7, GlobalTheory.ShFam.KitClass D}
    {D : D7} {J : Formalism.L2.Pj.Core D} {X : DivX D} (g : GeoCl (geoOf Q) D J X)
    (L : SizeData₂ D) (j : ℕ) (hj : 1 ≤ j) (hm : j < D.R.m) :
    ∃ c : X.Comp j, ∀ u, height L X (Replacement.geometry_of_closure g) j c u = 0 := by
  obtain ⟨c, bad⟩ := obstructed_model g j hj hm
  exact ⟨c, fun u => height_without_model L _ bad u⟩

section Fixed

variable {ε : ℝ} (F : FamP ε) (x : ℝ) (i : F.Ix x)
    (geo : (F.X x i).geo = geoTrue (F.D x i).what₂.LL) (j : ℕ) (c : (F.X x i).Comp j)

local notation "A" => LData.Lbar (sectionData (F.X x i) geo j c)
local notation "H" => height (F.L x i) (F.X x i) geo j c

/-- At the family's actual size constant, the finite-place variation cancels
    exactly. The difference of the errors is the difference of the archimedean sums. -/
theorem residual (hx : F.x1 < x) (model : (A).IsModel) (degree : (A).deg ≠ 0)
    (u : (F.D x i).what₂.Word) :
    ((F.D x i).div.h u - H u) - ((F.D x i).div.h (F.D x i).u₀ - H (F.D x i).u₀) =
      arch (F.L x i) u - arch (F.L x i) (F.D x i).u₀ := by
  have diff := GeometryAudit.HeightComparison.formula_difference
    (F.D x i) (F.L x i) (F.X x i) F.Csz u (F.D x i).u₀
  rw [← F.h_eq x hx i u, ← F.h_eq x hx i (F.D x i).u₀] at diff
  simp only [HeightComparison.wordTerm, ← Finset.sum_mul] at diff
  unfold height
  rw [height_on_model _ _ model degree u, height_on_model _ _ model degree (F.D x i).u₀]
  unfold arch
  linarith only [diff]

/-- For this specified metric, equality with the assigned height at all words
    requires the actual base self-intersection and constancy of the kernel sum. -/
theorem agreement_iff (hx : F.x1 < x) (model : (A).IsModel) (degree : (A).deg ≠ 0) :
    (∀ u, H u = (F.D x i).div.h u) ↔
      (sectionData (F.X x i) geo j c).h =
        hExpl6 (F.D x i) (F.L x i) (F.X x i) F.Csz (F.D x i).u₀ +
          (∑ t : (F.D x i).host.TT, ((F.L x i).aT t : ℝ)) *
            Real.log (((F.D x i).mem (F.D x i).u₀).A.T : ℝ) ∧
      ∀ u, arch (F.L x i) u = arch (F.L x i) (F.D x i).u₀ := by
  have hb := height_on_model (F.L x i) (A) model degree (F.D x i).u₀
  rw [section_normalized] at hb
  change H (F.D x i).u₀ = _ at hb
  have assigned := F.h_eq x hx i (F.D x i).u₀
  constructor
  · intro eqn
    refine ⟨by linarith only [eqn (F.D x i).u₀, assigned, hb], fun u => ?_⟩
    have h := residual F x i geo j c hx model degree u
    rw [eqn u, eqn (F.D x i).u₀] at h
    linarith only [h]
  · rintro ⟨base, fixed⟩ u
    linarith only [residual F x i geo j c hx model degree u, base, assigned, hb, fixed u]

end Fixed

#print axioms theta_weight_fixed
#print axioms obstructed_component
#print axioms residual
#print axioms agreement_iff

end
end GeometryAudit.ProductionLevelHeight
