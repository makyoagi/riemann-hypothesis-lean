import Formalism.LocalToGlobal.ProjectiveLattices.ESecPfA
import FlagEvaluation

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam GlobalTheory.TrueGeo GlobalTheory.Toroidal
open GeometryAudit.FamilyTop GeometryAudit.FormComparison
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GeometryAudit.FormMultiplication

private theorem twist_product {A : Type*} [CommMonoid A] (f g u : A) (a b : ℕ) :
    (f * g) * u ^ (a + b) = (f * u ^ a) * (g * u ^ b) := by
  rw [pow_add, mul_mul_mul_comm]

private theorem flag_product {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {m m' : MD H} (t : m = m')
    {c : Coeff m.1} {c' : Coeff m'.1} (le : c.F ≤ c'.F)
    {O : Type} [CommRing O] {β : O →+* c'.F} {Z : Model m'.2.2 c' β}
    {F : Type} [Field F] {e : F ≃+* c'.F} (C : FlagCpt Z e) (u : Rul m'.2.2 c')
    (f g : Rul m.2.2 c) (a b n : ℕ) (hn : n = a + b) :
    let tr := trRul t (c := c) (c' := c') le
    C.val (tr (f * g) * u ^ n) = C.val (tr f * u ^ a) * C.val (tr g * u ^ b) := by
  subst n
  let tr := trRul t (c := c) (c' := c') le
  have first := congrArg (fun x : Rul m'.2.2 c' => x * u ^ (a + b)) (tr_mul t (c := c) (c' := c') le f g)
  exact (congrArg C.val (first.trans (twist_product (tr f) (tr g) u a b))).trans
    ((FlagCpt.fromTest_and_val_laws _ _ _ _ _ _ _ _ _ _ _ C).2.2.1 _ _)

variable {D : D7} {T : Top D} (h : LawsP T) {st : StFams D} (R : RowKits T h st)
    {j : ℕ} (hj : InR D j)

theorem multiplicative_comparison (w w' : WeightFamilies.Wt D j)
    (f g : T.R j) (k : (R.F.at (datW D R.F.κg j)).Comp) :
    cmpAt h R.tie R.k hj (WeightAlgebra.wadd w w').n k (f * g) =
      cmpAt h R.tie R.k hj w.n k f * cmpAt h R.tie R.k hj w'.n k g := by
  have hw : (w.n + w'.n) / 2 = w.n / 2 + w'.n / 2 := by
    obtain ⟨x, hx⟩ := w.n_even
    obtain ⟨y, hy⟩ := w'.n_even
    omega
  exact flag_product (R.tie.same j hj) (c := T.Q.c) (c' := R.F.κg.c) R.tie.le
    ((R.k.at (datW D R.F.κg j)).Φ.C k) (R.k.at (datW D R.F.κg j)).key.ρ.val f g _ _ _ hw

#print axioms multiplicative_comparison
end GeometryAudit.FormMultiplication
