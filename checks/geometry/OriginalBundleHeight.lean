import FamilyComponentIntersection
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupPinsOfMuIsW

open NumberField Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions
open Formalism.MainNotions.HeightShare Formalism.L2.Geo
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
open GlobalTheory.Mem.Top.Bl GlobalTheory.EX GlobalTheory.EX.OB Formalism.L2.Host
open GlobalTheory.Mem.Top.GroupRetwisting Formalism.MainNotions.Inhab
open GeometryAudit.FamilyComponentIntersection

namespace GeometryAudit.OriginalBundleHeight

/-- The seed cannot supply a word-indexed bundle. Its variety type is empty
    and the distinguished word furnishes an input even on a one-word row. -/
theorem no_bundle_on_seed {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}
    {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)}
    (t : RowsT K w Z Wt p0) :
    let X := DivRec.x0 t.r.Z t.r.z.pins t.r.intersectionNumber_baseChange
    ¬ Nonempty ((w.D Z).what₂.Word → LData X.geo) := by
  dsimp only
  rintro ⟨Bof⟩
  exact Empty.elim (Bof (w.D Z).u₀).Y

section Graft

variable (D : D7) (jc : GlobalTheory.ShFam.JC D) (seed : DivX D)

private noncomputable abbrev flagDiv : DivX D :=
  let Xg := divXFl D jc seed
  GlobalTheory.GeoGraft.graft Xg seed Xg.iMj Xg.iMj_mem

local notation "Y" => flagDiv D jc seed

/-- The explicit flag model used by geoOver_stages gives zero for every
    normalized arithmetic self-intersection, even with an arbitrary metric input. -/
theorem graft_height_zero (B : LData (Y).geo) : B.h = 0 := by
  change (0 : ℝ) / _ = 0
  exact zero_div _

/-- At the supplied size constant the zero criterion is exact. In the reverse
    direction the witness is the model's own row-1 component with its section metric. -/
theorem graft_agreement_iff (L : SizeData₂ D) (k : ℝ) :
    (∃ Bof : D.what₂.Word → LData (Y).geo, ∀ u, (Bof u).h = hExpl6 D L Y k u) ↔
      ∀ u, hExpl6 D L Y k u = 0 := by
  constructor
  · rintro ⟨Bof, eqn⟩ u
    exact (eqn u).symm.trans (graft_height_zero D jc seed (Bof u))
  · intro zeros
    let B := componentData Y 1 PUnit.unit
    exact ⟨fun _ => B, fun u => (graft_height_zero D jc seed B).trans (zeros u).symm⟩

/-- Install the formula exactly as in the release, with its specified size
    constant and any supplied lattice. The stored equation is reflexive.
    Agreement with a geometric bundle on the flag model still requires zero. -/
theorem stored_agreement_iff (L : SizeData₂ D) (k : ℝ)
    (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) :
    let h := hExpl6 D L Y k
    let D' := setDiv D N h
    let Y' := divTr N h Y
    (∀ u, D'.div.h u = hExpl6 D' (ledTr N h L) Y' k u) ∧
      ((∃ Bof : D'.what₂.Word → LData Y'.geo, ∀ u, (Bof u).h = D'.div.h u) ↔
        ∀ u, D'.div.h u = 0) :=
  ⟨fun _ => rfl, graft_agreement_iff D jc seed L k⟩

end Graft

#print axioms no_bundle_on_seed
#print axioms graft_height_zero
#print axioms graft_agreement_iff
#print axioms stored_agreement_iff
end GeometryAudit.OriginalBundleHeight
