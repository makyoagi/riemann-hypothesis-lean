import FormsAssembly

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.ShFam GlobalTheory.TrueGeo GlobalTheory.LocM
open GeometryAudit.FamilyTop GeometryAudit.FamilyLaws GeometryAudit.FormComparison GeometryAudit.FormRowData
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GeometryAudit.FamilyForms
noncomputable section
open Classical

variable {D : D7} {T : Top D} (h : LawsP T) {st : StFams D} (R : RowKits T h st)

def family : FamOver (IsKitOf st) (familyTop h R.k) (family_laws h R) 1 :=
  ProductionGeometry.familyOfComparison h R (forms h R (rowComparison h R)) (forms_are h R (rowComparison h R))

open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl
open Formalism.MainNotions.Inhab

theorem geometry_of_reads (stages : ∀ D, StFams D) {D : D7} {T : Formalism.L2.Pj.Top D}
    (h : LawsP T) (R : RowKits T h (stages D)) (X : DivX D) (iM : _) (hiM : _)
    (reads : (family h R).Reads (Replacement.repair X) iM) :
    GlobalTheory.Mem.Top.Bl.geoOf (fun D => IsKitOf (stages D)) D T.toCore
      (GlobalTheory.VarietyModelRecord.record (Replacement.repair X) (family h R).fam iM hiM (family h R).dH) :=
  ⟨⟨1, Nat.zero_lt_one, familyTop h R.k, family_laws h R, family h R, Replacement.repair X, iM, hiM,
    rfl, rfl, reads, rfl⟩, rfl⟩

def familyRows (slots : Slots) (st : ∀ D, StFams D) : WP := fun K _ _ _ w =>
  ∀ (Z : w.Lt) (l : Lv4 slots K w Z),
    ∃ (P : Formalism.L2.Pj.Top (w.D Z)) (law : LawsP P), P.toCore = l.what₂.r.z.core.toCore ∧
      Nonempty (FamOver (IsKitOf (st _)) P law 1)

theorem production_family_rows (slots : Slots) (rx : slots.Rx = RX) (st : ∀ D, StFams D) :
    StepW Pinned (familyRows slots st) := by
  apply (production_rowKits slots rx st).trans (StepW.of_all ?_)
  intro _ _ _ _ _ _ _ row Z l
  obtain ⟨T, h, e, ⟨R⟩⟩ := row Z l
  exact ⟨familyTop h R.k, family_laws h R, e, ⟨family h R⟩⟩

end
#print axioms rowComparison
#print axioms family
#print axioms geometry_of_reads
end GeometryAudit.FamilyForms
