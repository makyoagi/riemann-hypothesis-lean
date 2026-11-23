import ProductionReads

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl
open GlobalTheory.ShFam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GeometryAudit.ProductionReads

private theorem geometry_heq {K : Ctx} {B : Base} {f : Fr B.toPre} {tw : TwDat B}
    {w : ColW B f tw} {Z : w.Lt} {Wt : Set B.places.Pl} {p p' : BaseLevelRowSide (w.D Z)}
    {t : RowsT K w Z Wt p} {t' : RowsT K w Z Wt p'} (ep : p = p') (et : HEq t t')
    {P : GeoP} {X : DivX (w.D Z)} (hg : P (w.D Z) t'.r.z.core.toCore X) :
    P (w.D Z) t.r.z.core.toCore X := by
  subst ep
  obtain rfl := eq_of_heq et
  exact hg

theorem strong_divEx (slots : Slots) (rx : slots.Rx = RX) (st : ∀ D, StFams D)
    (ox : slots.Ox = OX (some (geoOf (fun D => IsKitOf (st D))))) : DivEx slots := by
  apply (production_geometry slots rx st).trans (StepW.of_all ?_)
  intro _ _ _ _ _ _ _ rows Z l
  obtain ⟨Y, hd, hm, hk, hl, hg⟩ := rows Z l
  refine ⟨Y, hd, hm, hk, fun O t hx hp ht => ?_⟩
  rw [ox]
  exact ⟨⟨geometry_heq (P := geoOf (fun D => IsKitOf (st D))) hp ht (hx ▸ hg),
    DivRec.lamAre_heq hp ht (hx ▸ hl)⟩⟩

/-- The slot used by the closing argument transports genuine geometry through setDiv. -/
theorem closed_divEx (slots : Slots) (rx : slots.Rx = RX)
    (ox : slots.Ox = OX productionGeometry) : DivEx slots := by
  apply (production_geometry slots rx ProductionGeometry.stages).trans (StepW.of_all ?_)
  intro _ _ _ _ _ _ _ rows Z l
  obtain ⟨Y, hd, hm, hk, hl, hg⟩ := rows Z l
  refine ⟨Y, hd, hm, hk, fun O t hx hp ht => ?_⟩
  rw [ox]
  exact ⟨⟨geoCl_of (geometry_heq (P := productionPredicate) hp ht (hx ▸ hg)),
    DivRec.lamAre_heq hp ht (hx ▸ hl)⟩⟩

def strongSlots (s : Slots) (st : ∀ D, StFams D) : Slots :=
  {s with Ox := OX (some (geoOf (fun D => IsKitOf (st D))))}

#print axioms strong_divEx
end GeometryAudit.ProductionReads
