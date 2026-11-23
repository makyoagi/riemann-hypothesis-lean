import ProductionLevelHeight
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions

namespace GeometryAudit.ArchWeightTest

noncomputable section

variable (D : D7) (u : D.what₂.Word)

/-- All three indices range only over weights present in the production kernel sum. -/
abbrev Ix (D : D7) := (j : Fin D.R.m) × D.what₂.Tau × Fin (D.R.N j)

def weight (ix : Ix D) : ℕ := ⌊nuRow D u (ix.1.val + 1) ix.2.1 ix.2.2.val⌋₊

theorem weight_spec (ix : Ix D) : 0 < weight D u ix ∧
    (weight D u ix : ℝ) = nuRow D u (ix.1.val + 1) ix.2.1 ix.2.2.val := by
  obtain ⟨n, hn, eqn⟩ := nuRow_nat D u ix.1 ix.1.isLt ix.2.1 ix.2.2 ix.2.2.isLt
  simp only [weight, eqn, Nat.floor_natCast]
  exact ⟨hn, trivial⟩

def totalWeight : ℕ := ∑ ix : Ix D, weight D u ix

def weightProduct : ℕ := ∏ ix : Ix D, weight D u ix ^ weight D u ix

private theorem product_pos : 0 < weightProduct D u :=
  Finset.prod_pos fun ix _ => pow_pos (weight_spec D u ix).1 _

/-- The archimedean residual can be tested with two integers from the word's weights. -/
theorem arch_formula (L : SizeData₂ D) :
    ProductionLevelHeight.arch L u = Real.log (weightProduct D u : ℝ) -
      (totalWeight D u : ℝ) * (1 + L.logOm) := by
  classical
  have logP : Real.log (weightProduct D u : ℝ) =
      ∑ ix : Ix D, (weight D u ix : ℝ) * Real.log (weight D u ix : ℝ) := by
    unfold weightProduct
    push_cast
    rw [Real.log_prod (fun ix _ => pow_ne_zero _ (Nat.cast_ne_zero.2 (weight_spec D u ix).1.ne'))]
    simp only [Real.log_pow]
  rw [logP, totalWeight, Nat.cast_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp only [(weight_spec D u _).2]
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type]
  unfold ProductionLevelHeight.arch
  have sumLifts (f : ℕ → ℝ) : ∑ j ∈ SizeData₂.lifts D, f j =
      ∑ j : Fin D.R.m, f (j.val + 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun n => f (n + 1)) D.R.m,
      Finset.range_eq_Ico, Finset.sum_Ico_add' f 0 D.R.m 1]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext n
    simp only [SizeData₂.lifts, Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [sumLifts]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro τ _
  let ν := nuRow D u (j.val + 1) τ
  rw [Fin.sum_univ_eq_sum_range (fun n => ν n * Real.log (ν n) - ν n * (1 + L.logOm)) (D.R.N j)]
  dsimp only [ν]
  simp only [kerPlace, Nat.add_sub_cancel, phF, Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- For two words of equal total weight, equality of the archimedean sums is
    exactly equality of positive integers. No logarithmic derivative enters this test. -/
theorem eq_iff_product (L : SizeData₂ D) (v : D.what₂.Word)
    (same : totalWeight D u = totalWeight D v) :
    ProductionLevelHeight.arch L u = ProductionLevelHeight.arch L v ↔
      weightProduct D u = weightProduct D v := by
  rw [arch_formula, arch_formula, same, sub_left_inj]
  constructor
  · intro h
    have realEq := Real.log_injOn_pos (Set.mem_Ioi.2 (Nat.cast_pos.2 (product_pos D u)))
      (Set.mem_Ioi.2 (Nat.cast_pos.2 (product_pos D v))) h
    exact_mod_cast realEq
  · rintro e
    rw [e]

theorem eq_iff_logOm (L : SizeData₂ D) (v : D.what₂.Word)
    (different : totalWeight D u ≠ totalWeight D v) :
    ProductionLevelHeight.arch L u = ProductionLevelHeight.arch L v ↔
      L.logOm = (Real.log (weightProduct D u : ℝ) - Real.log (weightProduct D v : ℝ)) /
        ((totalWeight D u : ℝ) - (totalWeight D v : ℝ)) - 1 := by
  have ne : (totalWeight D u : ℝ) - (totalWeight D v : ℝ) ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast different)
  rw [arch_formula, arch_formula]
  conv_rhs => rw [eq_sub_iff_add_eq, eq_div_iff ne]
  constructor <;> intro h <;> linarith only [h]

#print axioms arch_formula
#print axioms eq_iff_product
#print axioms eq_iff_logOm

end
end GeometryAudit.ArchWeightTest
