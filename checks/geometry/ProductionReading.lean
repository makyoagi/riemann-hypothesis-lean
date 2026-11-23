import ReadingLattice
import ProductionTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AMiEqAMinusQ

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open Formalism.L2.Pj Formalism.IndefR.Links GlobalTheory.RealGeo
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GeometryAudit.ReadingRealisation

theorem production_weight {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}
    {w : ColW B f T} {Z : w.Lt} {slots : Slots} (l : Lv4 slots K w Z) (i : Fin (w.D Z).R.m) :
    let wt := l.what₂.r.z.geo.κ i
    wt.n = (w.D Z).R.nV ∧ Formalism.L2.Geo.wtOf wt = DV.kapW (w.D Z) ((i : ℕ) + 1) := by
  let D := w.D Z
  have e := congrFun (Formalism.IndefR.FWT.KapIs.eq l.what₂.r.z.geo.κ l.what₂.r.z.geo.fw.kap l.what₂.hX.nonempty_Tau) i
  dsimp only
  rw [e]
  exact GlobalTheory.RecordWeightVec.wtOf_kapTop D l.what₂.r.Y.kap i

theorem production_core_cusp {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}
    {w : ColW B f T} {Z : w.Lt} {slots : Slots} (rx : slots.Rx = RX) (l : Lv4 slots K w Z) :
    let z := l.what₂.r.z
    ∃ h : LawsCore z.core.toCore, ∀ i : Fin (w.D Z).R.m,
      MjCusp h ((i : ℕ) + 1) (z.geo.κ i) (volRec z.R.toRealDat z.F.lv2 i) := by
  have laws := l.rx
  rw [rx] at laws
  have b := l.what₂.r.z.pins.char.base
  have pc : PreChar l.what₂.r.z.R.toRealDat :=
    ⟨b.lev, b.grp.red_R, b.grp.red_L, b.grp.record, b.fam, b.models,
      RealDat.chain_of_weak b.chain l.what₂.exAt, RealDat.thP_of_weak b.thP l.what₂.exAt⟩
  exact ⟨laws.laws, fun i => core_cusp laws.laws l.what₂.r.Y.kap pc l.what₂.r.z.geo
    l.what₂.inGeo l.what₂.r.Y.mj i⟩

#print axioms production_core_cusp
#print axioms production_weight
end GeometryAudit.ReadingRealisation
