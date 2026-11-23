import ProductionBoundary
import WordNormVariation
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.DV
open Formalism.MainNotions.HeightShare GlobalTheory GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.VarietyModelRecord GeometryAudit.FamilyComponentIntersection

namespace GeometryAudit.LevelPrimeHeight

noncomputable section

/-- At a finite place v the twist parameter is W times log |T(u)|_v,
    where W is the sum of the row multiplicities. The infinite metric is fixed. -/
def levelMetric {D : D7} (L : SizeData₂ D) (u : D.what₂.Word)
    (v : HeightOneSpectrum (𝓞 D.what₂.LL)) : ℝ :=
  (∑ t : D.host.TT, (L.aT t : ℝ)) *
    Real.log ((FinitePlace.equivHeightOneSpectrum.symm v) ((D.mem u).A.T : D.what₂.LL))

theorem levelMetric_finite {D : D7} (L : SizeData₂ D) (u : D.what₂.Word) :
    (Function.support (levelMetric L u)).Finite := by
  have hp : ((D.mem u).A.T : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero
  have fin := (CompHS.finite_support_log hp).preimage
    (FinitePlace.equivHeightOneSpectrum (K := D.what₂.LL)).symm.injective.injOn
  exact fin.subset fun v hv zero => hv (by simp [levelMetric] at zero ⊢; tauto)

theorem levelMetric_sum {D : D7} (L : SizeData₂ D) (u : D.what₂.Word) :
    (∑ᶠ v, levelMetric L u v) / (Module.finrank ℚ D.what₂.LL : ℝ) =
      -(∑ t : D.host.TT, (L.aT t : ℝ)) * Real.log ((D.mem u).A.T : ℝ) := by
  have rank : (Module.finrank ℚ D.what₂.LL : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  unfold levelMetric
  rw [← mul_finsum, finsum_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := D.what₂.LL)).symm
    (f := fun v => Real.log (v ((D.mem u).A.T : D.what₂.LL))),
    CompHS.finsum_log_natCast (D.mem u).A.T_prime.ne_zero]
  field_simp

section Intersection

variable {K : Type} [Field K] [NumberField K] {C : CxSt K} {Y : Var K} (A : Adl C Y)

def normalized (A : Adl C Y) : ℝ := A.arTop / (((Y.dim : ℝ) + 1) * A.deg)

private theorem finite_shift (model : A.IsModel) {c : HeightOneSpectrum (𝓞 K) → ℝ}
    (fin : (Function.support c).Finite) :
    (A.twist 0 c).arTop = A.arTop + ((Y.dim : ℝ) + 1) * A.deg *
      (∑ᶠ v, c v) / (Module.finrank ℚ K : ℝ) := by
  let arithmetic : Published.ArCalc := ArithmeticHeightTower.ArakelovDirectHeights.arCalc_direct
    PositivityTheory.Tls2.Pl.poincareLelong PositivityTheory.ResPlug.FromRes.resK
  let degree : Published.ArDegree := PositivityTheory.Prw.arDegree_of (Published.CycleHeights.heightProjection
    (ArithmeticHeightTower.ArakelovDirectHeights.cycleHeights_direct
      PositivityTheory.Tls2.Pl.poincareLelong PositivityTheory.ResPlug.FromRes.resK))
    PositivityTheory.Tls2.Chern2.chernDegreeComplex
  obtain ⟨M, L, k, cf, hI⟩ := model
  have := M.ar.isIntegral
  obtain ⟨H, hH⟩ := (arithmetic.arExists _ M.X M.p _ M.ar).1 L
  have inter : L.IsSelfInter (H (genericPoint M.X)) := ⟨H, hH, rfl⟩
  rw [(arTop_of_induced arithmetic degree _ _ _ _ _ _ _ _ (hI.twist_fin fin)).2 _ inter,
    (arTop_of_induced arithmetic degree _ _ _ _ _ _ _ _ hI).2 _ inter]
  simp only [Pi.add_apply, finsum_add_distrib hI.1 fin]
  rw [show (A.twist 0 c).n = A.n from rfl, show (A.twist 0 c).deg = A.deg from rfl]
  ring

private theorem no_model_twist (bad : ¬ A.IsModel) {c : HeightOneSpectrum (𝓞 K) → ℝ}
    (fin : (Function.support c).Finite) : ¬ (A.twist 0 c).IsModel := by
  rintro ⟨M, L, k, cf, hI⟩
  have minus : (Function.support (-c)).Finite := by rwa [Function.support_neg]
  have undo : (A.twist 0 c).twist 0 (-c) = A := by
    cases A
    simp [Adl.twist, sub_neg_eq_add]
  exact bad (undo ▸ (show ((A.twist 0 c).twist 0 (-c)).IsModel from
    ⟨M, L, k, cf + -c, hI.twist_fin minus⟩))

private theorem zero_without_model (bad : ¬ A.IsModel) : normalized A = 0 := by
  have empty : ¬ ∃ t, A.IsArTop t := by
    rintro ⟨_, M, L, k, cf, _, hI, _⟩
    exact bad ⟨M, L, k, cf, hI⟩
  simp [normalized, Adl.arTop, empty]

end Intersection

/-- This word-indexed candidate uses only the component's metric, the level
    ideal and the row multiplicities. It needs no assigned height or estimate constant. -/
def wordBundle {D : D7} (L : SizeData₂ D) {C : CxSt D.what₂.LL} {Y : Var D.what₂.LL}
    (A : Adl C Y) (u : D.what₂.Word) : Adl C Y := A.twist 0 (levelMetric L u)

variable {D : D7} (L : SizeData₂ D) {C : CxSt D.what₂.LL} {Y : Var D.what₂.LL}
    (A : Adl C Y)

theorem height_on_model (model : A.IsModel) (degree : A.deg ≠ 0) (u : D.what₂.Word) :
    normalized (wordBundle L A u) = normalized A -
      (∑ t : D.host.TT, (L.aT t : ℝ)) * Real.log ((D.mem u).A.T : ℝ) := by
  have dim : (Y.dim : ℝ) + 1 ≠ 0 := by positivity
  unfold normalized wordBundle
  rw [finite_shift A model (levelMetric_finite L u)]
  change (_ + _) / (_ * A.deg) = _
  rw [add_div]
  rw [mul_div_assoc (((Y.dim : ℝ) + 1) * A.deg),
    mul_div_cancel_left₀ _ (mul_ne_zero dim degree), levelMetric_sum]
  ring

theorem height_without_model (bad : ¬ A.IsModel) (u : D.what₂.Word) :
    normalized (wordBundle L A u) = 0 :=
  zero_without_model _ (no_model_twist A bad (levelMetric_finite L u))

#print axioms height_on_model
#print axioms height_without_model

end
end GeometryAudit.LevelPrimeHeight
