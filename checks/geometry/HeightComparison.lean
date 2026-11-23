import Formalism.SharpRestriction.Divisibility.HeightShare
import Formalism.LocalRingCardinality.KernelPlaceMeanBound
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.HeightShare
open GlobalTheory.Mem.Top.Bl GlobalTheory.EX.OB

namespace GeometryAudit.HeightComparison

noncomputable section

/-- The part of the formula that can vary with the word at fixed row data. -/
def wordTerm (D : D7) (L : SizeData₂ D) (u : D.what₂.Word) : ℝ :=
  -(∑ t : D.host.TT, (L.aT t : ℝ) * Real.log ((D.mem u).A.T : ℝ)) +
    ∑ j ∈ SizeData₂.lifts D, ∑ ρ : D.what₂.Tau, kerPlace D L u j ρ

theorem formula_difference (D : D7) (L : SizeData₂ D) (X : DivX D) (C : ℝ)
    (u v : D.what₂.Word) :
    hExpl6 D L X C u - hExpl6 D L X C v = wordTerm D L u - wordTerm D L v := by
  simp only [hExpl6, SZbP, kernelPlaceMeanBound, wordTerm, Finset.sum_add_distrib]
  ring

/-- The old and replacement divisors on a production row have this same prescribed kapR. -/
theorem formula_with_production_kap (D : D7) (L : SizeData₂ D) (X Y : DivX D)
    (hx : ∀ e, X.kapR e = kapSharp D) (hy : ∀ e, Y.kapR e = kapSharp D) (C : ℝ) :
    hExpl6 D L X C = hExpl6 D L Y C := by
  have same : X.kapR = Y.kapR := funext fun e => (hx e).trans (hy e).symm
  funext u
  unfold hExpl6
  rw [same]

theorem formula_after_setDiv (D : D7) (L : SizeData₂ D) (X : DivX D)
    (h : D.what₂.Word → ℝ) (C : ℝ) (u : D.what₂.Word) :
    let N := fun v => (D.div.Nu v).L
    hExpl6 (setDiv D N h) (ledTr N h L) (divTr N h X) C u = hExpl6 D L X C u := rfl

/-- An independent geometric assignment has the proposed height exactly when
    it has the correct height at one word and the correct variations. -/
theorem geometric_height_iff (D : D7) (L : SizeData₂ D) (X : DivX D) (C : ℝ)
    (B : D.what₂.Word → LData X.geo) (v : D.what₂.Word) :
    (∀ u, (B u).h = hExpl6 D L X C u) ↔
      (B v).h = hExpl6 D L X C v ∧
        ∀ u, (B u).h - (B v).h = wordTerm D L u - wordTerm D L v := by
  constructor
  · intro eq
    exact ⟨eq v, fun u => by rw [eq u, eq v, formula_difference]⟩
  · rintro ⟨base, differences⟩ u
    linarith only [base, differences u, formula_difference D L X C u v]

/-- The transported geometry slot accepts the same base witness when the
    stored word heights are one greater than a fixed geometric assignment.
    This assertion concerns the geometry slot alone. -/
theorem closure_allows_shift {D : D7} {J : Formalism.L2.Pj.Core D} {X : DivX D}
    {P : GeoP} (base : P D J X) (B : D.what₂.Word → LData X.geo) :
    let N := fun u => (D.div.Nu u).L
    let shifted := fun u => (B u).h + 1
    GeoCl P (setDiv D N shifted) (coreS N shifted J) (divTr N shifted X) ∧
      ∀ u, (setDiv D N shifted).div.h u ≠ (B u).h := by
  dsimp only
  refine ⟨GeoCl.step _ _ (GeoCl.base base), ?_⟩
  intro u
  linarith

#print axioms formula_with_production_kap
#print axioms formula_after_setDiv
#print axioms formula_difference
#print axioms geometric_height_iff
#print axioms closure_allows_shift

end
end GeometryAudit.HeightComparison
