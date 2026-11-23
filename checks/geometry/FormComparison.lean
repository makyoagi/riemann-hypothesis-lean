import CoreEmbedding
import SemilinearEvaluation
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ShFam GlobalTheory.TrueGeo GlobalTheory.Toroidal GlobalTheory.FieldBC GlobalTheory.LocM
open GeometryAudit.FamilyTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GeometryAudit.FormComparison
noncomputable section

private abbrev ValueMap {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (m : MD H) (c : Coeff m.1)
    {K : Type} [Field K] (i : c.F →+* K) (Y : GlobalTheory.ProjVar.Var K) :=
  Rul m.2.2 c →ₛₗ[i] Y.Fn

private def powerEvaluation {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {m m' : MD H} (t : m = m')
    {c : Coeff m.1} {c' : Coeff m'.1} (hle : c.F ≤ c'.F)
    {O : Type} [CommRing O] {β : O →+* c'.F} {Z : Model m'.2.2 c' β}
    {F : Type} [Field F] {e : F ≃+* c'.F} (C : FlagCpt Z e) (key : KeySec m'.2.2 c') (n : ℕ) :
    ValueMap m c (e.symm.toRingHom.comp (IntermediateField.inclusion hle).toRingHom) C.Y :=
  transportedEvaluation t (c := c) (c' := c') hle C (key.ρ.val ^ (n / 2))

private theorem powerEvaluation_apply {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {m m' : MD H} (t : m = m')
    {c : Coeff m.1} {c' : Coeff m'.1} (hle : c.F ≤ c'.F)
    {O : Type} [CommRing O] {β : O →+* c'.F} {Z : Model m'.2.2 c' β}
    {F : Type} [Field F] {e : F ≃+* c'.F} (C : FlagCpt Z e) (key : KeySec m'.2.2 c') (n : ℕ) (f : Rul m.2.2 c) :
    powerEvaluation t (c := c) (c' := c') hle C key n f =
      C.val (trRul t (c := c) (c' := c') hle f * key.ρ.val ^ (n / 2)) := rfl

variable {D : D7} {T : Top D} (h : LawsP T) {st : StFams D} (R : RowKits T h st)

def evaluated {j : ℕ} (hj : InR D j) (n : ℕ) (k : (R.F.at (datW D R.F.κg j)).Comp) :
    ValueMap ⟨T.Q.l, T.Q.Dw j, T.Q.Xo j⟩ T.Q.c (coefficientMap h R) ((R.k.at (datW D R.F.κg j)).Φ.C k).Y :=
  let kit := R.k.at (datW D R.F.κg j)
  powerEvaluation (R.tie.same j hj) (c := T.Q.c) (c' := R.F.κg.c) R.tie.le (e := R.F.κg.e) (kit.Φ.C k) kit.key n

theorem evaluated_eq {j : ℕ} (hj : InR D j) (n : ℕ) (k : (R.F.at (datW D R.F.κg j)).Comp) (f : T.R j) :
    evaluated h R hj n k f = cmpAt h R.tie R.k hj n k f :=
  let kit := R.k.at (datW D R.F.κg j)
  powerEvaluation_apply (R.tie.same j hj) (c := T.Q.c) (c' := R.F.κg.c) R.tie.le (e := R.F.κg.e) (kit.Φ.C k) kit.key n f

#print axioms evaluated_eq
#print axioms coefficientMap_pinned
end
end GeometryAudit.FormComparison
