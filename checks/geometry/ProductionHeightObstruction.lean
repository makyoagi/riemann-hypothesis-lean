import AssignedWordVariation
import ProductionSwapFamily

open NumberField Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions
open Formalism.MainNotions.HeightShare GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.Mem.Top.Bl UpperTheory.Top GeometryAudit.LevelPrimeHeight
open GeometryAudit.ProductionLevelHeight

namespace GeometryAudit.ProductionHeightObstruction

/-- On a given row, the same two words test every fixed base bundle with the
    prescribed finite metric twist. This includes zero degree and the fallback
    value for bundles without an arithmetic model. -/
theorem finite_twist_misses {eps : ℝ} (F : FamP eps) {x : ℝ} (hx : F.x1 < x) (i : F.Ix x)
    {u v : (F.D x i).what₂.Word} (distinct : (F.D x i).div.h u ≠ (F.D x i).div.h v)
    (strict : arch (F.L x i) u < arch (F.L x i) v)
    {C : CxSt (F.D x i).what₂.LL} {Y : Var (F.D x i).what₂.LL} (A : Adl C Y) :
    normalized (wordBundle (F.L x i) A u) ≠ (F.D x i).div.h u ∨
      normalized (wordBundle (F.L x i) A v) ≠ (F.D x i).div.h v := by
  by_contra! equal
  obtain ⟨hu, hv⟩ := equal
  by_cases model : A.IsModel
  · by_cases degree : A.deg = 0
    · have zero (w : (F.D x i).what₂.Word) : normalized (wordBundle (F.L x i) A w) = 0 := by
        change _ / (_ * A.deg) = 0
        rw [degree, mul_zero, div_zero]
      exact distinct (hu.symm.trans ((zero u).trans ((zero v).symm.trans hv)))
    · rw [height_on_model _ _ model degree] at hu hv
      have diff := HeightComparison.formula_difference (F.D x i) (F.L x i) (F.X x i) F.Csz u v
      rw [← F.h_eq x hx i u, ← F.h_eq x hx i v] at diff
      simp only [HeightComparison.wordTerm, ← Finset.sum_mul] at diff
      unfold arch at strict
      linarith only [hu, hv, strict, diff]
  · rw [height_without_model _ _ model] at hu hv
    exact distinct (hu.symm.trans hv)

/-- Beyond every cutoff an inhabited window of a single modulus-one family
    has a certified divisor and two words that rule out the finite level-prime
    twist on every section component, at the family's unchanged normalization.
    Row one has an actual component, on which even the fallback value fails. -/
theorem realized_obstruction : ∃ (eps : ℝ) (F : FamP eps), 0 < eps ∧
    (GChi Formalism.HC.PChar.one).cls (3/2) F ∧
    (∃ κ : GlobalTheory.Fc.Par, GlobalTheory.Fc.Link κ F ∧ F.Csz = κ.C.Csz) ∧
    ∀ cutoff : ℝ, ∃ (x : ℝ) (i : F.Ix x), cutoff ≤ x ∧ x ∈ F.Win ∧
      ∃ (J : Formalism.L2.Pj.Core (F.D x i)) (g : GeoCl productionPredicate (F.D x i) J (F.X x i)),
        let D := F.D x i
        let L := F.L x i
        let X := F.X x i
        let geo := Replacement.geometry_of_closure g
        (∀ w, D.div.h w = hExpl6 D L X F.Csz w) ∧
        ∃ u v, arch L u < arch L v ∧ D.div.h u ≠ D.div.h v ∧
          (∀ (j : ℕ) (c : X.Comp j),
            height L X geo j c u ≠ D.div.h u ∨ height L X geo j c v ≠ D.div.h v) ∧
          ∃ (c : X.Comp 1) (w : D.what₂.Word), height L X geo 1 c w = 0 ∧ D.div.h w ≠ 0 := by
  obtain ⟨eps, F, pos, character, constants, rows⟩ := ProductionSwapFamily.realized_family
  obtain ⟨threshold, bound⟩ := AssignedWordVariation.weights_below_primes F pos
  refine ⟨eps, F, pos, character, constants, fun cutoff => ?_⟩
  obtain ⟨x, hx, above, win, ⟨i⟩⟩ := F.toFamCore.exists_pt (max cutoff threshold)
  obtain ⟨pair, J, g⟩ := rows x above i
  obtain ⟨u, v, distinct, strict⟩ := AssignedWordVariation.assigned_differs F above i pair
    (bound x ((le_max_right _ _).trans hx) i)
  refine ⟨x, i, (le_max_left _ _).trans hx, win, J, g, F.h_eq x above i, u, v, strict, distinct, ?_, ?_⟩
  · exact fun j c => finite_twist_misses F above i distinct strict (sectionData _ _ j c).Lbar
  · obtain ⟨c, zero⟩ := obstructed_component g (F.L x i) 1 le_rfl (by have := (F.D x i).R.two_le_m; omega)
    by_cases h : (F.D x i).div.h u = 0
    · exact ⟨c, v, zero v, fun hv => distinct (h.trans hv.symm)⟩
    · exact ⟨c, u, zero u, h⟩

#print axioms finite_twist_misses
#print axioms realized_obstruction
end GeometryAudit.ProductionHeightObstruction
