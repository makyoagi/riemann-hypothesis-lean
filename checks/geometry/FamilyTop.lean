import ProductionTie
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EmbeddingCompatHeq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotMemPlaceholder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmEx
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyPolarizationDataStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions
open Formalism.L2.Pj Formalism.L2.Geo Formalism.MainNotions.DIV.Cons
open GlobalTheory.ShFam GlobalTheory.TrueGeo GlobalTheory.LocM GlobalTheory.ShFam.Pad
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GeometryAudit.FamilyTop
noncomputable section
variable {D : D7}

theorem transfer_same_family {T T' : Top D} (e : T.toCore = T'.toCore)
    (h : LawsP T) (h' : LawsP T') {c : ℕ} (F : SrcFam (ambOf T.Q h.pins.1))
    (pin : F.Pinned T.pb c) (tie : ParTie T.Q h.pins.1 F) :
    ∃ F' : SrcFam (ambOf T'.Q h'.pins.1), HEq F F' ∧ F'.Pinned T'.pb c ∧ ParTie T'.Q h'.pins.1 F' := by
  cases T
  cases T'
  cases e
  exact ⟨F, HEq.rfl, pin, tie⟩

theorem kitClass_ex (st : StFams D) : (IsKitOf st).Ex := by
  intro A N j S κ s L jc hj
  exact KitCheck.exists_mem st s L hj (admEx S κ) fun Φ x =>
    GlobalTheory.T.nonempty_polarization_data D A N j S κ s Φ (metsOf x Φ) (refMet x Φ)

theorem kitClass_loc (st : StFams D) : (IsKitOf st).Loc := by
  rintro A N j S κ s L jc k d _ ⟨x, pol, cts, hj, hA, hm⟩
  exact ⟨st A N j S κ, cts, hm.ats, hm.pad ▸ rfl⟩

variable {T : Top D} (h : LawsP T) {F : SrcFam (ambOf T.Q h.pins.1)}
  {L : CmList (ambOf T.Q h.pins.1)} {jc : JC D}
  (k : Kits F L (cxSt D.what₂.LL) jc ngTrue)

private def shape {A : Amb D} (w : Dat D (Lv A)) := (w.N, w.j, w.κ)

-- FamOver.prov requires a small index type. A general datum can be large.
private abbrev Index (A : Amb D) :=
  {j : ℕ // 1 ≤ j ∧ j < D.R.m} ⊕
    {t : ℕ × ℕ × Lv A // ∃ w : Dat D (Lv A), w.Indef ∧ shape w = t}

private def dataAt {A : Amb D} (κ : Lv A) : Index A → Dat D (Lv A)
  | .inl j => datW D κ j
  | .inr t => t.property.choose

private theorem data_indef {A : Amb D} (κ : Lv A) : ∀ i, (dataAt κ i).Indef
  | .inl j => datW_indef D κ j.property.1 j.property.2
  | .inr t => t.property.choose_spec.1

private def rowIndex {A : Amb D} (_ : Lv A) (j : ℕ) : Index A :=
  .inl (if hi : 1 ≤ j ∧ j < D.R.m then ⟨j, hi⟩ else ⟨1, le_rfl, D.R.two_le_m⟩)

private theorem rowIndex_val {A : Amb D} (κ : Lv A) {j : ℕ} (hj : 1 ≤ j) (hm : j < D.R.m) :
    dataAt κ (rowIndex κ j) = datW D κ j := by simp [rowIndex, dataAt, hj, hm]

private theorem data_cover {A : Amb D} (κ : Lv A) (w : Dat D (Lv A)) (hw : w.Indef) :
    ∃ i, (dataAt κ i).N = w.N ∧ (dataAt κ i).j = w.j ∧ (dataAt κ i).κ = w.κ := by
  let t : {t : ℕ × ℕ × Lv A // ∃ v : Dat D (Lv A), v.Indef ∧ shape v = t} :=
    ⟨shape w, w, hw, rfl⟩
  have e := t.property.choose_spec.2
  exact ⟨.inr t, congrArg Prod.fst e, congrArg (fun q => q.2.1) e, congrArg (fun q => q.2.2) e⟩

private abbrev familyPkg := indefiniteDataFamily (shimOf (cutSt _) (resSt _) k)
  _ (dataAt F.κg) (data_indef F.κg)

def familyG : In66 T.Q where
  P := familyPkg h k
  dat := rowIndex F.κg
  Tw := T.G.Tw
  rel := fun j p η z =>
    ((familyPkg h k).loc (rowIndex F.κg j) p).fld η = PointsOfFlagModel.fld z ∧
    ∀ A : DatAt ((T.G.Tw j p).Y z.1) z.2.2.1,
      ∃ e : ((familyPkg h k).loc (rowIndex F.κg j) p).Ylat η ≃ₗ[𝓞 D.host.E] A.Ylat,
        ∀ a b, A.beta (e a) (e b) = ((familyPkg h k).loc (rowIndex F.κg j) p).be η a b

def familyTop : Top D := { T with G := familyG h k }

theorem familyG_indices {j : ℕ} (hj : 1 ≤ j) (hm : j < D.R.m) :
    (familyG h k).P.rk ((familyG h k).dat j) = (datW D F.κg j).N ∧
    (familyG h k).P.jj ((familyG h k).dat j) = (datW D F.κg j).j := by
  have e := rowIndex_val F.κg hj hm
  exact ⟨congrArg Dat.N e, congrArg Dat.j e⟩

theorem familyG_loc {j : ℕ} (hj : 1 ≤ j) (hm : j < D.R.m) (p : ℕ) :
    HEq ((familyG h k).P.loc ((familyG h k).dat j) p) ((k.at (datW D F.κg j)).pad.loc p) := by
  change HEq ((k.at (dataAt F.κg (rowIndex F.κg j))).pad.loc p) _
  rw [rowIndex_val _ hj hm]

theorem familyTop_core : (familyTop h k).toCore = T.toCore := rfl

theorem familyTop_prov :
    ∃ (I : Type) (dat : I → Dat D (Lv (ambOf T.Q h.pins.1))) (hI : ∀ i, (dat i).Indef) (iW : ℕ → I),
      (∀ w : Dat D (Lv (ambOf T.Q h.pins.1)), w.Indef → ∃ i, (dat i).N = w.N ∧ (dat i).j = w.j ∧ (dat i).κ = w.κ) ∧
      (∀ j, 1 ≤ j → j < D.R.m → dat (iW j) = datW D F.κg j) ∧
      (familyTop h k).G.P = indefiniteDataFamily (shimOf (cutSt _) (resSt _) k) I dat hI ∧
      ∀ j, 1 ≤ j → j < D.R.m → HEq ((familyTop h k).G.dat j) (iW j) :=
  ⟨_, dataAt F.κg, data_indef F.κg, rowIndex F.κg, data_cover F.κg,
    fun _ hj hm => rowIndex_val _ hj hm, rfl, fun _ _ _ => HEq.rfl⟩

def localPointsExist : Prop := ∀ j, 1 ≤ j → j < D.R.m → ∀ la z, T.G.IsAlgPt j la z →
  ∃ η, (familyG h k).rel j (WeightAlgebra.resCh la) η z

theorem familyTop_laws_iff : LawsP (familyTop h k) ↔ localPointsExist h k := by
  constructor
  · exact fun laws j hj hm la z hz => (laws.points_condition j hj hm la z hz).1
  · intro points
    have hd : (familyG h k).PinDat := by
      intro j hj hm
      have hi := familyG_indices h k hj hm
      exact ⟨hi.1.trans (datW_N _ _ _), hi.2.trans (datW_j _ _ hj hm.le)⟩
    exact ⟨h.toLawsCore, h.allTest, h.reg, hd, h.tower, h.hasData_condition,
      fun j hj hm la z hz => ⟨points j hj hm la z hz, fun _ r => r.1⟩,
      fun _ _ _ _ _ _ _ r => r.2, h.bc66, h.datIndep, h.nabPin, h.nabUniq, h.thTot, h.thCusp, h.thNe, h.kPsi⟩

-- Changing only the relation cannot avoid the field and lattice comparison.
theorem localPoints_of_other_relation
    (r : ∀ (j p : ℕ), (familyG h k).PY j p → PointsOfFlagModel.Pt (T.G.Tw j p) .yy → Prop)
    (laws : LawsP { familyTop h k with G := { familyG h k with rel := r } }) :
    localPointsExist h k := by
  intro j hj hm la z hz
  obtain ⟨η, he⟩ := (laws.points_condition j hj hm la z hz).1
  exact ⟨η, (laws.points_condition j hj hm la z hz).2 η he, laws.lattice_condition j hj hm la z hz η he⟩

structure RowKits (T : Top D) (h : LawsP T) (st : StFams D) : Type 1 where
  F : SrcFam (ambOf T.Q h.pins.1)
  pinned : F.Pinned T.pb 1
  tie : ParTie T.Q h.pins.1 F
  L : CmList (ambOf T.Q h.pins.1)
  jc : JC D
  pin : jc.Pinned
  k : Kits F L (cxSt D.what₂.LL) jc ngTrue
  d : ∀ N j hn hj κ, (F.src N j hn hj κ).Comp → D.what₂.Tau → ℝ
  mem : ∀ N j hn hj κ, IsKitOf st _ N j _ κ (F.src N j hn hj κ) L jc (k N j hn hj κ) (d N j hn hj κ)

theorem kits_of_tie (st : StFams D) (pin : F.Pinned T.pb 1) (tie : ParTie T.Q h.pins.1 F) :
    Nonempty (RowKits T h st) := by
  obtain ⟨M⟩ := AsmCheck.nonempty_cmList (ambOf T.Q h.pins.1)
  let jC : JC D := fun p _ v => (GlobalTheory.WittFracPlace.exists_jcPin D p v).choose
  have hjC : jC.Pinned := fun p _ v => (GlobalTheory.WittFracPlace.exists_jcPin D p v).choose_spec
  choose kit deg member using fun N j hn hj κ =>
    kitClass_ex st _ N j _ κ (F.src N j hn hj κ) M jC hjC
  exact ⟨F, pin, tie, M, jC, hjC, kit, deg, member⟩

open Formalism.MainNotions.Inhab GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Col2
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GeometryAudit.Production in
theorem production_rowKits (slots : Slots) (rx : slots.Rx = RX) (st : ∀ D, StFams D) :
    StepW Pinned (fun K _ _ _ w => ∀ (Z : w.Lt) (l : Lv4 slots K w Z),
      ∃ (T : Formalism.L2.Pj.Top (w.D Z)) (h : LawsP T), T.toCore = l.what₂.r.z.core.toCore ∧
        Nonempty (RowKits T h (st _))) := by
  apply (production_parTie slots rx).trans (StepW.of_all ?_)
  intro _ _ _ _ _ _ _ rows Z l
  obtain ⟨T, h, e, F, pin, tie⟩ := rows Z l
  exact ⟨T, h, e, kits_of_tie h (st _) pin tie⟩

-- These are the remaining fields of FamOver for this choice of top and kits.
def familyOfForms {st : StFams D} (R : RowKits T h st) (hp : localPointsExist h R.k)
    (forms : FormsOver (cutSt _) (resSt _) R.k)
    (cmp : FormsAre ((familyTop_laws_iff h R.k).2 hp) R.tie (cutSt _) (resSt _) R.k forms) :
    FamOver (IsKitOf st) (familyTop h R.k) ((familyTop_laws_iff h R.k).2 hp) 1 where
  F := R.F
  t := R.tie
  exp := R.pinned.2
  L := R.L
  jC := R.jc
  pin := R.pin
  k := R.k
  d := R.d
  mem := R.mem
  hg := AsmCheck.primes_first R.F
  P := forms
  forms := cmp
  prov := familyTop_prov h R.k

#print axioms transfer_same_family
#print axioms kitClass_ex
#print axioms kitClass_loc
#print axioms familyTop_prov
#print axioms familyTop_laws_iff
#print axioms localPoints_of_other_relation
#print axioms production_rowKits
#print axioms familyOfForms
end
end GeometryAudit.FamilyTop
