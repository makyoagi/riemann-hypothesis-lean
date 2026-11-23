import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotLamAreShift
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupPinsOfMuIsW

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem GlobalTheory.Mem.Top.Bl
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
open Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GeometryAudit

theorem closure_has_surface {Q : ∀ D : D7, GlobalTheory.ShFam.KitClass D}
    {D : D7} {J : Formalism.L2.Pj.Core D} {X : DivX D} (h : GeoCl (geoOf Q) D J X) :
    Nonempty X.Surf := by
  induction h with
  | base h => exact (OXModel.geoOf_surf h).1
  | step _ _ _ ih => exact ih

theorem empty_surface_rejects_geometry {Q : ∀ D : D7, GlobalTheory.ShFam.KitClass D}
    {D : D7} {J : Formalism.L2.Pj.Core D} {X : DivX D} (h : X.Surf = Empty) :
    ¬ geoCl (geoOf Q) D J X := by
  intro hg
  have hs := closure_has_surface hg
  rw [h] at hs
  exact hs.elim Empty.elim

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt}
  {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)}

theorem x0_lam_and_no_geometry (Q : ∀ D : D7, GlobalTheory.ShFam.KitClass D)
    (t : RowsT K w Z Wt p0) :
    let X := DivRec.x0 t.r.Z t.r.z.pins t.r.intersectionNumber_baseChange
    LamAre t.r.Z X ∧ ¬ geoCl (geoOf Q) (w.D Z) t.r.z.core.toCore X :=
  ⟨DivRec.lamAre_x0 t, empty_surface_rejects_geometry rfl⟩

-- The explicitly exhibited model in geoOver_stages is divXFl applied to reQ of x0.
theorem model_rejects_geometry (Q : ∀ D : D7, GlobalTheory.ShFam.KitClass D)
    {slots : Slots} (w : ColW B f T) (pin : ColPin w) (Z : w.Lt) (l : Lv4 slots K w Z)
    (jc : GlobalTheory.ShFam.JC (w.D Z)) :
    let hp := DivRec.tupPins_of_muIsW (w.st Z) f T l.Wt w.I.xi l.what₂.mu l.n.tp l.n.xi
    let X₁ := DivRec.x0 l.what₂.r.Z l.what₂.r.z.pins l.what₂.r.intersectionNumber_baseChange
    let X₂ := GlobalTheory.Mem.HD.ReQ.reQ l.n.tp hp w.I.sel pin.above X₁
    let Xg := Formalism.L2.Geo.divXFl (w.D Z) jc X₂
    let Y := GlobalTheory.GeoGraft.graft Xg X₂ Xg.iMj Xg.iMj_mem
    ¬ geoCl (geoOf Q) (w.D Z) l.what₂.r.z.core.toCore Y :=
  empty_surface_rejects_geometry rfl

#print axioms model_rejects_geometry
#check OXModel.oAt_geoOf
end GeometryAudit
