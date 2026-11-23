import FlagEvaluation
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ShFam GlobalTheory.TrueGeo GlobalTheory.Toroidal GlobalTheory.FieldBC GlobalTheory.LocM
open GeometryAudit.FamilyTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GeometryAudit.FormComparison
noncomputable section

def transportedEvaluation {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {m m' : MD H} (t : m = m')
    {c : Coeff m.1} {c' : Coeff m'.1} (hle : c.F ≤ c'.F)
    {O : Type} [CommRing O] {β : O →+* c'.F} {Z : Model m'.2.2 c' β}
    {F : Type} [Field F] {e : F ≃+* c'.F} (C : FlagCpt Z e) (u : Rul m'.2.2 c') :
    Rul m.2.2 c →ₛₗ[e.symm.toRingHom.comp (IntermediateField.inclusion hle).toRingHom] C.Y.Fn where
  toFun f := (evaluateAdd (m := m') C u) (trRul t (c := c) (c' := c') hle f)
  map_add' f g := by
    let L := evaluateAdd (m := m') C u
    exact (congrArg L (tr_add t (c := c) (c' := c') hle f g)).trans (L.map_add _ _)
  map_smul' a f := by
    let L := evaluateAdd (m := m') C u
    exact (congrArg L (tr_smul t (c := c) (c' := c') hle a f)).trans (evaluate_smul (m := m') C u _ _)


end
end GeometryAudit.FormComparison
