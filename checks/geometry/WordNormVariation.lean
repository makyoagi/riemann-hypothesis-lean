import HeightComparison

open Formalism.BasicNotions Formalism.BasicNotions.DV

namespace GeometryAudit.WordNorm

/-- The family already carries a scalar for each word in its CM field.
    Its absolute value recovers the ratio of the two level primes at every embedding. -/
theorem prime_ratio (D : D7) (σ : D.host.E →+* ℂ) (u : D.what₂.Word) :
    ‖σ (D.cOf u)‖ ^ 2 * ((D.mem u).A.T : ℝ) = ((D.mem D.u₀).A.T : ℝ) := by
  have eq := congrArg (fun a : D.host.E => ‖σ a‖) (D.cOf_eq u)
  simpa [map_mul, norm_mul, D.host.conjE_apply σ, pow_two] using eq

theorem prime_log_variation (D : D7) (σ : D.host.E →+* ℂ) (u : D.what₂.Word) :
    Real.log ((D.mem D.u₀).A.T : ℝ) - Real.log ((D.mem u).A.T : ℝ) =
      2 * Real.log ‖σ (D.cOf u)‖ := by
  have norm_ne : ‖σ (D.cOf u)‖ ≠ 0 := norm_ne_zero_iff.mpr (by simpa using σ.injective.ne (D.cOf_ne u))
  have prime_ne : ((D.mem u).A.T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero
  have h := congrArg Real.log (prime_ratio D σ u)
  rw [Real.log_mul (pow_ne_zero _ norm_ne) prime_ne, Real.log_pow] at h
  exact sub_eq_iff_eq_add.mpr (by simpa using h.symm)

/-- Exact variation from the distinguished word: the CM scalar accounts
    for the prime term, leaving the difference of archimedean kernel terms. -/
theorem formula_variation (D : D7) (L : SizeData₂ D) (X : DivX D) (k : ℝ)
    (σ : D.host.E →+* ℂ) (u : D.what₂.Word) :
    hExpl6 D L X k u - hExpl6 D L X k D.u₀ =
      (∑ t : D.host.TT, (L.aT t : ℝ)) * (2 * Real.log ‖σ (D.cOf u)‖) +
      ((∑ j ∈ SizeData₂.lifts D, ∑ ρ : D.what₂.Tau, kerPlace D L u j ρ) -
       (∑ j ∈ SizeData₂.lifts D, ∑ ρ : D.what₂.Tau, kerPlace D L D.u₀ j ρ)) := by
  rw [HeightComparison.formula_difference, ← prime_log_variation D σ u]
  simp only [HeightComparison.wordTerm, ← Finset.sum_mul]
  ring

/-- Only interior weights of the first block can change the archimedean summand. -/
private theorem srcPar_fixed (D : D7) (u v : D.what₂.Word) (τ : D.what₂.Tau)
    (i : ℕ) (outside : ¬ (0 < i ∧ i + 1 < D.R.k)) :
    srcPar D u τ i = srcPar D v τ i := by
  by_cases hi : i < D.R.k
  · simp only [srcPar, dif_pos hi]
    by_cases zero : i = 0
    · subst i
      exact (D.hcW_first u τ hi).trans (D.hcW_first v τ hi).symm
    · have last : i = D.R.k - 1 := by omega
      subst i
      exact (D.hcW_last u τ (by omega)).trans (D.hcW_last v τ (by omega)).symm
  · simp only [srcPar, dif_neg hi]
    by_cases block : (i - D.R.k) / (D.R.t + 1) < D.R.m
    · simp only [dif_pos block, D.hcW_e u τ, D.hcW_e v τ]
    · simp only [dif_neg block]

noncomputable def archTerm (D : D7) (L : SizeData₂ D) (w : D.what₂.Word)
    (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℝ :=
  phF (nuRow D w j τ i) - nuRow D w j τ i * L.logOm

/-- In a difference between words every kernel term outside the interior
    cancels, including both endpoint weights and the entire second block. -/
theorem kernel_variation (D : D7) (L : SizeData₂ D) (u v : D.what₂.Word)
    (j : ℕ) (τ : D.what₂.Tau) :
    kerPlace D L u j τ - kerPlace D L v j τ =
      ∑ i ∈ (Finset.range (D.R.N (j - 1))).filter (fun i => 0 < i ∧ i + 1 < D.R.k),
        (archTerm D L u j τ i - archTerm D L v j τ i) := by
  have expand (w : D.what₂.Word) : kerPlace D L w j τ =
      ∑ i ∈ Finset.range (D.R.N (j - 1)), archTerm D L w j τ i := by
    simp only [kerPlace, archTerm, Finset.sum_sub_distrib, Finset.sum_mul]
  rw [expand u, expand v, ← Finset.sum_sub_distrib, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with interior
  · rfl
  · simp only [archTerm, nuRow, srcPar_fixed D u v τ i interior, sub_self]

#print axioms prime_ratio
#print axioms formula_variation
#print axioms kernel_variation
end GeometryAudit.WordNorm
