import FamilyTop
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ShFam GlobalTheory.TrueGeo GlobalTheory.Toroidal GlobalTheory.FieldBC GlobalTheory.LocM
open GeometryAudit.FamilyTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GeometryAudit.FormComparison
noncomputable section

variable {D : D7} {T : Top D} (h : LawsP T) {st : StFams D} (R : RowKits T h st)

def coefficientMap : T.Q.c.F →+* D.what₂.LL :=
  R.F.κg.e.symm.toRingHom.comp (IntermediateField.inclusion R.tie.le).toRingHom

theorem coefficientMap_pinned (a : 𝓞 T.Q.c.F) :
    coefficientMap h R a.val = D.what₂.OtoLL (T.Q.eO a) := by
  apply D.what₂.embLL.injective
  have e := R.F.κg.e_emb (coefficientMap h R a.val)
  change (R.F.κg.e (R.F.κg.e.symm _) : ℂ) = _ at e
  rw [RingEquiv.apply_symm_apply] at e
  exact e.symm.trans (h.pins.2.2.1 a).symm

#print axioms coefficientMap_pinned
end
end GeometryAudit.FormComparison
