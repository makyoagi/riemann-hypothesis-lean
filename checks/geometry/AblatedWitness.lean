import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem GlobalTheory.Mem.Top.Bl
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
open Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt}
  {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} (t : RowsT K w Z Wt p0) (X : DivX (w.D Z))

example : OAt none t X = LamAt t X := rfl
example : Nonempty (OAt none t X) ↔ LamAre t.r.Z X :=
  ⟨fun ⟨o⟩ => o.lam, fun h => ⟨⟨h⟩⟩⟩
example : OAt none t X ≃ PLift (LamAre t.r.Z X) where
  toFun o := ⟨o.lam⟩
  invFun h := ⟨h.down⟩
  left_inv o := by cases o; rfl
  right_inv h := by cases h; rfl
example : closeGeometry none = none := rfl

open Lean Elab Command in
run_cmd do
  if (← getEnv).contains `GlobalTheory.Mem.Top.Bl.anyGeometry then
    throwError "The deleted predicate is still present in the environment"
