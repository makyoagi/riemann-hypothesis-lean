import Main
import Mathlib.NumberTheory.LSeries.RiemannZeta

example : RiemannHypothesis = (∀ s : ℂ, riemannZeta s = 0 →
    (¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2) := rfl
example : RiemannHypothesis := riemannHypothesis
example : RiemannHypothesis = RiemannZetaZerosOnLine := rfl
#print RiemannHypothesis
#check riemannHypothesis
#print axioms riemannHypothesis
