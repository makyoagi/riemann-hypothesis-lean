import LocalPointLift

open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.ShFam
open GeometryAudit.FamilyTop GeometryAudit.LocalPoint

-- Expected failure after Lean accepts both the new point and its field.
example {D : D7} {T : Top D} (h : LawsP T) {st : StFams D} (R : RowKits T h st) :
    LawsP (familyTop h R.k) := by
  apply (familyTop_laws_iff h R.k).2
  intro j hj hm la z hz
  obtain ⟨η, sameField⟩ := family_point_same_field h R hj hm la z hz
  refine ⟨η, sameField, ?_⟩
  intro A
  assumption
