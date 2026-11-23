import FamilyLaws
import FamilySections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions
open Formalism.L2.Pj Formalism.L2.Geo Formalism.MainNotions.Inhab
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl
open GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad
open GeometryAudit.FamilyTop GeometryAudit.FamilyLaws
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GeometryAudit.ProductionGeometry

-- Each indefinite row and coefficient-field place has an algebraic tower point.
theorem has_algebraic_point {D : D7} {T : Formalism.L2.Pj.Top D} (h : LawsP T)
    (j : ℕ) (hj : 1 ≤ j) (hm : j < D.R.m) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) :
    ∃ z, T.G.IsAlgPt j la z := by
  obtain ⟨S, io, e, ho, y, hy⟩ := h.ptNe j ⟨hj, hm.le⟩ la
  obtain ⟨z, hz⟩ := h.bc66 j hj hm la S io e ho y hy
  exact ⟨z, S, io, e, y, ho, hy, hz⟩

-- Row one is indefinite, and its coefficient field has a finite place.
theorem first_row_has_point {D : D7} {T : Formalism.L2.Pj.Top D} (h : LawsP T) :
    ∃ la : HeightOneSpectrum (𝓞 T.Q.c.F), ∃ z, T.G.IsAlgPt 1 la z := by
  obtain ⟨P, hne, hP⟩ := (Ring.not_isField_iff_exists_prime (R := 𝓞 T.Q.c.F)).1
    (NumberField.RingOfIntegers.not_isField T.Q.c.F)
  let la : HeightOneSpectrum (𝓞 T.Q.c.F) := ⟨P, hP, hne⟩
  exact ⟨la, has_algebraic_point h 1 le_rfl (lt_of_lt_of_le Nat.one_lt_two D.R.two_le_m) la⟩

def lawfulRows (slots : Slots) (st : ∀ D, StFams D) : WP := fun K _ _ _ w =>
  ∀ (Z : w.Lt) (l : Lv4 slots K w Z),
    ∃ (T : Formalism.L2.Pj.Top (w.D Z)) (h : LawsP T) (R : RowKits T h (st _)),
      (familyTop h R.k).toCore = l.what₂.r.z.core.toCore ∧ LawsP (familyTop h R.k)

theorem production_lawful_rows (slots : Slots) (rx : slots.Rx = RX) (st : ∀ D, StFams D) :
    StepW Pinned (lawfulRows slots st) := by
  apply (production_rowKits slots rx st).trans (StepW.of_all ?_)
  intro _ _ _ _ _ _ _ row Z l
  obtain ⟨T, h, e, ⟨R⟩⟩ := row Z l
  exact ⟨T, h, R, e, family_laws h R⟩

def familyOfComparison {D : D7} {T : Formalism.L2.Pj.Top D} (h : LawsP T) {st : StFams D}
    (R : RowKits T h st) (P : FormsOver (cutSt _) (resSt _) R.k)
    (cmp : FormsAre (family_laws h R) R.tie (cutSt _) (resSt _) R.k P) :
    FamOver (IsKitOf st) (familyTop h R.k) (family_laws h R) 1 :=
  familyOfForms h R (family_points_and_lattices h R) P cmp

noncomputable def stages (D : D7) : StFams D := (KitCheck.nonempty_stFams D).some

open GlobalTheory.Mem.LiteralAutomorphy in
theorem production_parameters (hL : GlobalTheory.Published.LocalLanglandsGL) (d : ℝ) (a : AtP) :
    StepW Pinned (lawfulRows (prm0 hL).s stages) ∧
    StepW Pinned (lawfulRows (prm1 hL d).s stages) ∧
    StepW Pinned (lawfulRows (prmA hL d a).s stages) := by
  exact ⟨production_lawful_rows _ rfl _, production_lawful_rows _ rfl _, production_lawful_rows _ rfl _⟩

#print axioms familyOfComparison
#print axioms has_algebraic_point
#print axioms first_row_has_point
#print axioms production_lawful_rows
#print axioms production_parameters
end GeometryAudit.ProductionGeometry
