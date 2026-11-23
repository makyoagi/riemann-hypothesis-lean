import FamilyTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfAlgClosed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromTestAndValLaws

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ShFam GlobalTheory.TrueGeo GlobalTheory.Toroidal GlobalTheory.FieldBC GlobalTheory.LocM
open GeometryAudit.FamilyTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GeometryAudit.FormComparison
noncomputable section

section Flag

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {m : MD H}
    {c : Coeff m.1} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model m.2.2 c β}
    {F : Type} [Field F] {e : F ≃+* c.F}

def evaluateAdd (C : FlagCpt Z e) (u : Rul m.2.2 c) : Rul m.2.2 c →+ C.Y.Fn where
  toFun f := C.val (f * u)
  map_zero' := by
    rw [zero_mul]
    let := (constF e C.Y).toAlgebra
    exact evalAt_zero _ _ C.y0
  map_add' f g := by
    rw [add_mul]
    exact (FlagCpt.fromTest_and_val_laws _ _ _ _ _ _ _ _ _ _ _ C).2.2.2.1 _ _

theorem evaluate_smul (C : FlagCpt Z e) (u f : Rul m.2.2 c) (a : c.F) :
    C.val ((a • f) * u) = e.symm a • C.val (f * u) := by
  have hm : (a • f) * u = a • (f * u) := by
    funext p y
    exact smul_mul_assoc a (f p y) (u p y)
  rw [hm, (FlagCpt.fromTest_and_val_laws _ _ _ _ _ _ _ _ _ _ _ C).2.2.2.2, Algebra.smul_def]
  rfl

end Flag

section Transport

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {m m' : MD H} (tie : m = m')
    {c : Coeff m.1} {c' : Coeff m'.1} (le : c.F ≤ c'.F)

theorem tr_add (f g : Rul m.2.2 c) :
    trRul tie (c := c) (c' := c') le (f + g) = trRul tie (c := c) (c' := c') le f + trRul tie (c := c) (c' := c') le g := by
  subst m'
  exact (GlobalTheory.SlopeDesc.rulHom (Xo := m.2.2) (c := c) (c' := c') le).map_add f g

theorem tr_smul (a : c.F) (f : Rul m.2.2 c) :
    trRul tie (c := c) (c' := c') le (a • f) = IntermediateField.inclusion le a • trRul tie (c := c) (c' := c') le f := by
  subst m'
  exact GlobalTheory.SlopeDesc.rulBC_smul le a f

theorem tr_mul (f g : Rul m.2.2 c) :
    trRul tie (c := c) (c' := c') le (f * g) = trRul tie (c := c) (c' := c') le f * trRul tie (c := c) (c' := c') le g := by
  subst m'
  exact (GlobalTheory.SlopeDesc.rulHom (Xo := m.2.2) (c := c) (c' := c') le).map_mul f g

end Transport

end
end GeometryAudit.FormComparison
