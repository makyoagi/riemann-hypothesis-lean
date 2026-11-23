import HeightComparison
import ProductionHeightCandidates
import Formalism.LocalToGlobal.Divisibility.RecBridge

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions
open Formalism.L2.DIV GlobalTheory.Mem.Top.Bl GlobalTheory.EX.OB

namespace GeometryAudit.HeightSqueeze

noncomputable section

/-- At fixed row data the assigned height is affine in the size constant. -/
theorem formula_affine (D : D7) (L : SizeData₂ D) (X : DivX D)
    (u : D.what₂.Word) (k : ℝ) :
    hExpl6 D L X k u = hExpl6 D L X 0 u +
      k * (hExpl6 D L X 1 u - hExpl6 D L X 0 u) := by
  classical
  simp only [hExpl6, SZbP, kernelPlaceMeanBound, L6lo, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  ring

/-- Once the row and word are fixed, any prescribed base height determines
    exactly one real size constant. The production constant is already specified. -/
theorem existsUnique_constant (D : D7) (L : SizeData₂ D) (X : DivX D)
    (u : D.what₂.Word) (target : ℝ) : ∃! k : ℝ, hExpl6 D L X k u = target := by
  have mono := ProductionHeight.formula_strictMono D L X u
  have pos := sub_pos.mpr (mono zero_lt_one)
  refine ⟨(target - hExpl6 D L X 0 u) / (hExpl6 D L X 1 u - hExpl6 D L X 0 u), ?_, ?_⟩
  · dsimp only
    rw [formula_affine D L X u ((_ - _) / _), div_mul_cancel₀ _ pos.ne']
    ring
  · intro k hk
    apply (eq_div_iff pos.ne').2
    linarith only [hk, formula_affine D L X u k]

/-- Increasing the formula parameter adds the same constant at every word.
    In particular, all word-to-word variation estimates are unchanged. -/
theorem formula_shift (D : D7) (L : SizeData₂ D) (X : DivX D)
    (k k₀ : ℝ) (u v : D.what₂.Word) :
    hExpl6 D L X k v - hExpl6 D L X k₀ v =
      hExpl6 D L X k u - hExpl6 D L X k₀ u := by
  linarith only [HeightComparison.formula_difference D L X k v u,
    HeightComparison.formula_difference D L X k₀ v u]

/-- Even retaining every word-to-word variation and increasing the formula
    at every word, the installed formula and geometric certificate can coexist
    with a false upper bound. The row, lattices and comparison constants stay fixed. -/
theorem assignment_can_fail_upper {D : D7} (L : SizeData₂ D) (X : DivX D)
    {P : GeoP} {J : Formalism.L2.Pj.Core D} (base : P D J X)
    (u : D.what₂.Word) (C Cabs k₀ : ℝ) :
    ∃ k : ℝ, k₀ < k ∧
      let N := fun v => (D.div.Nu v).L
      let h := hExpl6 D L X k
      let D' := setDiv D N h
      let L' := ledTr N h L
      let X' := divTr N h X
      GeoCl P D' (coreS N h J) X' ∧
      (∀ v, D'.div.h v = hExpl6 D' L' X' k v) ∧
      (∀ v, hExpl6 D L X k₀ v < D'.div.h v) ∧
      (∀ v w, D'.div.h v - D'.div.h w = hExpl6 D L X k₀ v - hExpl6 D L X k₀ w) ∧
      (L'.MAIN u + C * (D'.host.TT.card : ℝ) * L'.sc.a * L'.La +
        C * (D'.R.m : ℝ) * (L'.B0 + L'.Nc) * L'.sc.x ^ (Cabs * L'.sc.eps)
        < D'.div.RR.muDual + D'.div.h u - L'.Fo) ∧
      ¬ WordFacts L' C Cabs u ∧ (∀ CH, ¬ LinkDIV_at L' C Cabs CH) := by
  let rhs := L.MAIN u + C * (D.host.TT.card : ℝ) * L.sc.a * L.La +
    C * (D.R.m : ℝ) * (L.B0 + L.Nc) * L.sc.x ^ (Cabs * L.sc.eps)
  let target := max (hExpl6 D L X k₀ u) (rhs - D.div.RR.muDual + L.Fo) + 1
  obtain ⟨k, hk, _⟩ := existsUnique_constant D L X u target
  have raised : k₀ < k := (ProductionHeight.formula_strictMono D L X u).lt_iff_lt.mp
    (by rw [hk]; exact lt_of_le_of_lt (le_max_left _ _) (lt_add_of_pos_right _ zero_lt_one))
  have bad : rhs < D.div.RR.muDual + hExpl6 D L X k u - L.Fo := by
    have hb := le_max_right (hExpl6 D L X k₀ u) (rhs - D.div.RR.muDual + L.Fo)
    dsimp [target] at hk
    linarith only [hk, hb]
  exact ⟨k, raised, GeoCl.step _ _ (GeoCl.base base), fun _ => rfl,
    fun v => ProductionHeight.formula_strictMono D L X v raised,
    fun v w => by linarith only [formula_shift D L X k k₀ w v], bad,
    fun w => (not_le_of_gt bad) w.2.2, fun _ link => (not_le_of_gt bad) (link.2.2.2.2.2.2.1 u)⟩

#print axioms formula_affine
#print axioms existsUnique_constant
#print axioms formula_shift
#print axioms assignment_can_fail_upper

end
end GeometryAudit.HeightSqueeze
