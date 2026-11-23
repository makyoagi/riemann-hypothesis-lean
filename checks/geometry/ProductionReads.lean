import ProductionReading
import FamilyReading
import ReadingRows

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TrueGeo
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl
open GeometryAudit.FamilyTop GeometryAudit.FamilyForms GeometryAudit.ReadingRealisation GeometryAudit.ReadingSections
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GeometryAudit.ProductionReads

private theorem transport_cusp {D : D7} {J J' : Core D} (eq : J = J') (h : LawsCore J) (h' : LawsCore J')
    {j : ℕ} {w : WeightFamilies.Wt D j} {vol : ℝ} (r : GlobalTheory.RealGeo.MjCusp h' j w vol) :
    GlobalTheory.RealGeo.MjCusp h j w vol := by cases eq; exact r

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {tw : TwDat B} {w : ColW B f tw} {Z : w.Lt}
    {slots : Slots} (rx : slots.Rx = RX) (l : Lv4 slots K w Z)
    {T : Formalism.L2.Pj.Top (w.D Z)} (h : LawsP T) (eq : T.toCore = l.what₂.r.z.core.toCore)
    {st : StFams (w.D Z)} (R : RowKits T h st)

include rx l eq in
theorem saturation (j : ℕ) (hj : InR (w.D Z) j) : ∃ vol, (family h R).P.MjSat j vol := by
  obtain ⟨hc, hcusp⟩ := production_core_cusp rx l
  cases j with
  | zero => exact (Nat.not_succ_le_zero 0 hj.1).elim
  | succ k =>
    let i : Fin (w.D Z).R.m := ⟨k, hj.2⟩
    obtain ⟨hn, hw⟩ := production_weight l i
    exact ⟨_, family_sat h R hj _ hn hw _ (transport_cusp eq h.toLawsCore hc (hcusp i))⟩

include rx l eq in
theorem production_reads (X : DivX (w.D Z)) :
    let Φ := family h R
    ∃ (ι : ∀ j (a : (Φ.fam.Uw j).Comp), (X.MjH j).V →ₗ[(w.D Z).what₂.LL]
        (geoTrue (w.D Z).what₂.LL).Fn ((Φ.fam.Uw j).alg.Yv a)),
      (∀ j c x, ι j c x ∈ (geoTrue (w.D Z).what₂.LL).H0 ((Φ.fam.Uw j).alg.Yv c) ((Φ.fam.Uw j).alg.Lw c
        (fun τ k => DV.kapW (w.D Z) j τ (Fin.cast (datW_N _ Φ.F.κg j) k)))) ∧ Φ.Reads X ι :=
  exists_reads (family h R) X (saturation rx l h eq R)

def geometricRows (slots : Slots) (stages : ∀ D, StFams D) : WP := fun K _ _ _ w =>
  ∀ (Z : w.Lt) (l : Lv4 slots K w Z), ∃ Y : DivX (w.D Z), Nonempty (DivT l.n Y) ∧ MjAre l.what₂.r.Z Y ∧
    (∀ σ, Y.kapR σ = kapSharp (w.D Z)) ∧ LamAre l.what₂.r.Z Y ∧
    GlobalTheory.Mem.Top.Bl.geoOf (fun D => IsKitOf (stages D)) (w.D Z) l.what₂.r.z.core.toCore Y

theorem production_geometry (slots : Slots) (rx : slots.Rx = RX) (stages : ∀ D, StFams D) :
    StepW Pinned (geometricRows slots stages) := by
  have keep : StepW Pinned Pinned := StepW.of_all fun _ _ _ _ _ _ _ p => p
  apply (keep.and (production_rowKits slots rx stages)).trans (StepW.of_all ?_)
  intro _ _ _ _ w _ _ rows Z l
  obtain ⟨T, h, eq, ⟨R⟩⟩ := rows.2 Z l
  obtain ⟨X, ⟨a⟩, hM, hk, hlam⟩ := DivRec.exists_divT w rows.1.some Z l
  let Φ := family h R
  obtain ⟨ι, reg, reads⟩ := production_reads rx l h eq R (Replacement.repair X)
  exact Replacement.genuine_replacement_of_family l (fun D => IsKitOf (stages D)) (familyTop h R.k)
    (FamilyLaws.family_laws h R) eq 1 Nat.zero_lt_one Φ X a hM hk hlam ι reg reads
    (FamilySections.cusp_of_reads Φ _ ι reg reads)
    (FamilySections.family_iso R (forms h R (rowComparison h R)))

open GlobalTheory.Mem.LiteralAutomorphy in
theorem production_parameters (hL : GlobalTheory.Published.LocalLanglandsGL) (d : ℝ) (a : AtP) :
    let st := ProductionGeometry.stages
    StepW Pinned (geometricRows (prm0 hL).s st) ∧ StepW Pinned (geometricRows (prm1 hL d).s st) ∧
      StepW Pinned (geometricRows (prmA hL d a).s st) :=
  ⟨production_geometry _ rfl _, production_geometry _ rfl _, production_geometry _ rfl _⟩

#print axioms saturation
#print axioms production_reads
#print axioms production_geometry
#print axioms production_parameters
end GeometryAudit.ProductionReads
