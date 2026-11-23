import HeightSqueeze
import ProductionReads
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions
open Formalism.MainNotions.Inhab GlobalTheory.Mem GlobalTheory.Mem.Col2
open GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Top.GroupRetwisting
open GlobalTheory.EX.OB GlobalTheory.Mem.LiteralAutomorphy GeometryAudit.ProductionReads

namespace GeometryAudit.HeightSqueeze

/-- Keep the divisor selected by the production construction. Test the upper
    bound with the same formula assignment and closure that the closing proof uses. -/
def testedRows (slots : Slots) : WP := fun K _ _ _ w =>
  ∀ (Z : w.Lt) (l : Lv4 slots K w Z), ∃ X : DivX (w.D Z),
    Nonempty (DivT l.n X) ∧ MjAre l.what₂.r.Z X ∧
    (∀ σ, X.kapR σ = kapSharp (w.D Z)) ∧ LamAre l.what₂.r.Z X ∧
    productionPredicate (w.D Z) l.what₂.r.z.core.toCore X ∧
    ∀ (L : SizeData₂ (w.D Z)) (u : (w.D Z).what₂.Word) (C Cabs k₀ : ℝ),
      ∃ k : ℝ, k₀ < k ∧
        let D := w.D Z
        let N := fun v => (D.div.Nu v).L
        let h := hExpl6 D L X k
        let D' := setDiv D N h
        let L' := ledTr N h L
        let X' := divTr N h X
        GeoCl productionPredicate D' (coreS N h l.what₂.r.z.core.toCore) X' ∧
        (∀ v, D'.div.h v = hExpl6 D' L' X' k v) ∧
        (∀ v w', D'.div.h v - D'.div.h w' = hExpl6 D L X k₀ v - hExpl6 D L X k₀ w') ∧
        ¬ Formalism.L2.DIV.WordFacts L' C Cabs u ∧ ∀ CH, ¬ LinkDIV_at L' C Cabs CH

theorem tested_production_rows (slots : Slots) (rx : slots.Rx = RX) : StepW Pinned (testedRows slots) := by
  apply (production_geometry slots rx ProductionGeometry.stages).trans (StepW.of_all ?_)
  intro _ _ _ _ _ _ _ rows Z l
  obtain ⟨X, hd, hm, hk, hl, hg⟩ := rows Z l
  refine ⟨X, hd, hm, hk, hl, hg, ?_⟩
  intro L u C Cabs k₀
  obtain ⟨k, hgt, geom, formula, _, varies, _, wordFails, linkFails⟩ :=
    assignment_can_fail_upper L X (P := productionPredicate) hg u C Cabs k₀
  exact ⟨k, hgt, geom, formula, varies, wordFails, linkFails⟩

theorem tested_parameters (hL : GlobalTheory.Published.LocalLanglandsGL) (d : ℝ) (a : AtP) :
    StepW Pinned (testedRows (prm0 hL).s) ∧ StepW Pinned (testedRows (prm1 hL d).s) ∧
      StepW Pinned (testedRows (prmA hL d a).s) :=
  ⟨tested_production_rows _ rfl, tested_production_rows _ rfl, tested_production_rows _ rfl⟩

#print axioms tested_parameters
end GeometryAudit.HeightSqueeze
