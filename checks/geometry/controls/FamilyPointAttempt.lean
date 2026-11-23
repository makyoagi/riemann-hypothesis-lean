import FamilyTop

open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.ShFam GeometryAudit.FamilyTop

-- Expected error: the old local point belongs to a different moduli package.
example {D : D7} {T : Top D} (h : LawsP T) {st : StFams D} (R : RowKits T h st) :
    LawsP (familyTop h R.k) := by
  apply (familyTop_laws_iff h R.k).2
  intro j hj hm la z hz
  obtain ⟨η, oldMatch⟩ := (h.points_condition j hj hm la z hz).1
  refine ⟨η, ?_⟩
