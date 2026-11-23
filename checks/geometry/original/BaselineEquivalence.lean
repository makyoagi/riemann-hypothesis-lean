import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem GlobalTheory.Mem.Top.Bl
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
open Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt}
  {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} (t : RowsT K w Z Wt p0) (X : DivX (w.D Z))

example : Nonempty (OAt anyGeometry t X) ↔ LamAre t.r.Z X :=
  ⟨fun ⟨o⟩ => o.lam, fun h => ⟨⟨True.intro, h⟩⟩⟩
example : Nonempty (OAt (geoCl anyGeometry) t X) ↔ LamAre t.r.Z X :=
  ⟨fun ⟨o⟩ => o.lam, fun h => ⟨⟨GeoCl.base True.intro, h⟩⟩⟩

-- Preserve the witness type itself, including in data-dependent uses.
example : OAt (geoCl anyGeometry) t X ≃ PLift (LamAre t.r.Z X) where
  toFun o := ⟨o.lam⟩
  invFun h := ⟨GeoCl.base True.intro, h.down⟩
  left_inv o := by cases o; rfl
  right_inv h := by cases h; rfl
