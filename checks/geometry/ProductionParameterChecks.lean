import StrongDivEx
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl
open GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.LiteralAutomorphy GlobalTheory.ShFam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GeometryAudit.Production
theorem production_parameters (hL : GlobalTheory.Published.LocalLanglandsGL) (d : ℝ) (a : AtP) :
    StepW Pinned (tiedSourceRows (prm0 hL).s) ∧
    StepW Pinned (tiedSourceRows (prm1 hL d).s) ∧
    StepW Pinned (tiedSourceRows (prmA hL d a).s) :=
  ⟨production_parTie _ rfl, production_parTie _ rfl, production_parTie _ rfl⟩
end GeometryAudit.Production

namespace GeometryAudit.ProductionGeometry
theorem production_parameters (hL : GlobalTheory.Published.LocalLanglandsGL) (d : ℝ) (a : AtP) :
    StepW Pinned (lawfulRows (prm0 hL).s stages) ∧
    StepW Pinned (lawfulRows (prm1 hL d).s stages) ∧
    StepW Pinned (lawfulRows (prmA hL d a).s stages) := by
  exact ⟨production_lawful_rows _ rfl _, production_lawful_rows _ rfl _, production_lawful_rows _ rfl _⟩
end GeometryAudit.ProductionGeometry

namespace GeometryAudit.FamilyForms
theorem production_parameters (hL : GlobalTheory.Published.LocalLanglandsGL) (d : ℝ) (a : AtP) :
    let st := ProductionGeometry.stages
    StepW Pinned (familyRows (prm0 hL).s st) ∧
    StepW Pinned (familyRows (prm1 hL d).s st) ∧
    StepW Pinned (familyRows (prmA hL d a).s st) :=
  ⟨production_family_rows _ rfl _, production_family_rows _ rfl _, production_family_rows _ rfl _⟩
end GeometryAudit.FamilyForms

namespace GeometryAudit.ProductionReads
theorem production_parameters (hL : GlobalTheory.Published.LocalLanglandsGL) (d : ℝ) (a : AtP) :
    let st := ProductionGeometry.stages
    StepW Pinned (geometricRows (prm0 hL).s st) ∧ StepW Pinned (geometricRows (prm1 hL d).s st) ∧
      StepW Pinned (geometricRows (prmA hL d a).s st) :=
  ⟨production_geometry _ rfl _, production_geometry _ rfl _, production_geometry _ rfl _⟩
end GeometryAudit.ProductionReads

namespace GeometryAudit.ProductionReads
theorem strong_parameters (hL : GlobalTheory.Published.LocalLanglandsGL) (d : ℝ) (a : AtP) :
    let st := ProductionGeometry.stages
    DivEx (strongSlots (prm0 hL).s st) ∧ DivEx (strongSlots (prm1 hL d).s st) ∧
      DivEx (strongSlots (prmA hL d a).s st) :=
  ⟨strong_divEx _ rfl _ rfl, strong_divEx _ rfl _ rfl, strong_divEx _ rfl _ rfl⟩
end GeometryAudit.ProductionReads

section
variable (hL : GlobalTheory.Published.LocalLanglandsGL) (d : ℝ) (a : AtP)

example : (prm0 hL).s.Ox =
    OX (some (geoCl (geoOf (fun D => IsKitOf (GeometryAudit.ProductionGeometry.stages D))))) := rfl
example : (prm1 hL d).s.Ox = OX (some (geoCl productionPredicate)) := rfl
example : (prmA hL d a).s.Ox = OX (some (geoCl productionPredicate)) := rfl

example : DivEx { (prm0 hL).s with Ox := OX none } := DivRec.divEx_prov _ rfl

example : DivEx (prm0 hL).s := by
  fail_if_success exact DivRec.divEx_prov _ rfl
  exact GeometryAudit.ProductionReads.closed_divEx _ rfl rfl
end
