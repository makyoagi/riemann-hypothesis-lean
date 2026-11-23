import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotLamAreShift
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupPinsOfMuIsW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultiplicityDifferentEq
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsTopOfCore
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesTypeNormsPrincipal

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem GlobalTheory.Mem.Top.Bl
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
open Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.Mem.Top.GroupRetwisting
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GeometryAudit.Replacement

open Formalism.L2.Geo GlobalTheory.ProjVar

theorem geometry_of_closure {Q : ∀ D : D7, KitClass D} {D : D7} {J} {X : DivX D}
    (hg : GeoCl (geoOf Q) D J X) : X.geo = GlobalTheory.TrueGeo.geoTrue D.what₂.LL := by
  induction hg with
  | base h =>
    obtain ⟨⟨_, _, _, _, _, _, _, _, _, rfl, _, _⟩, _⟩ := h
    rfl
  | step _ _ _ ih => exact ih

-- The negative hyperplane class on the projective line has degree -1.
-- This distinguishes the geometry records regardless of their level or surface types.
theorem degenerate_rejects_closure {Q : ∀ D : D7, KitClass D} {D : D7} {J} {X : DivX D}
    (e : X.geo = geoDegenerate D.what₂.LL D.what₂.Tau) : ¬ geoCl (geoOf Q) D J X := by
  intro hg
  have allNef : ∀ V L, X.geo.nef V L := by rw [e]; exact fun _ _ => trivial
  rw [geometry_of_closure hg] at allNef
  have neg := (nef_zsmul_projHyp_line D.what₂.LL (-1)).mp
    (allNef (proj D.what₂.LL 1) ((-1 : ℤ) • projHyp D.what₂.LL 1))
  omega

noncomputable def repair {D : D7} (X : DivX D) : DivX D :=
  { surfSt.put X with
    vdd := fun p _ => vDiff D.host.E p
    vdd_unram := fun p _ => (vDiff_spec D p).2.1
    vdd_nonneg := fun p _ => (vDiff_spec D p).1 }

theorem two_levels_of_isGeoOf {D : D7} {Q : KitClass D} {J c} {X : DivX D}
    (hg : IsGeoOf Q J c X) : ∃ a b : X.Lev, a ≠ b := by
  obtain ⟨T, h, Φ, X₀, iM, hiM, _, rfl, _, _⟩ := hg
  refine ⟨Φ.F.κg, Φ.F.κs, fun e => ?_⟩
  obtain ⟨n, hn, hs⟩ := Φ.F.κs_A
  have hpow : 1 < (15 : ℕ) ^ n := one_lt_pow₀ (by decide) hn.ne'
  have hbase := Φ.F.κg_A
  rw [e, hs] at hbase
  omega

theorem two_levels_of_closure {Q : ∀ D : D7, KitClass D} {D : D7} {J} {X : DivX D}
    (hg : GeoCl (geoOf Q) D J X) : ∃ a b : X.Lev, a ≠ b := by
  induction hg with
  | base h => exact two_levels_of_isGeoOf h.1.choose_spec.2
  | step _ _ _ ih => exact ih

-- This ranges over every base divisor, even one whose surfaces have already been repaired.
theorem repaired_graft_rejects_closure {D : D7} (Q : ∀ D : D7, KitClass D)
    (J : Formalism.L2.Pj.Core D) (jc : JC D) (X : DivX D) :
    let G := Formalism.L2.Geo.divXFl D jc X
    let Y := surfSt.put (GlobalTheory.GeoGraft.graft G X G.iMj G.iMj_mem)
    HasTrueSurf Y ∧ ¬ geoCl (geoOf Q) D J Y := by
  refine ⟨rfl, fun hg => ?_⟩
  obtain ⟨a, b, hab⟩ := two_levels_of_closure hg
  exact hab (Subsingleton.elim (α := Unit) a b)

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt}
  {Wt : Set B.places.Pl} {nch : NChoice (w.D Z)}

def divT_repair {n : NchT w Z Wt nch} {X : DivX (w.D Z)} (a : DivT n X) :
    DivT n (repair X) where
  Qp := a.Qp
  chr := ⟨a.chr.Qp_iff, a.chr.eQPl, a.chr.qv_eq⟩
  loc := ⟨a.loc.1, a.loc.2.qv_eq, a.loc.2.deg1, a.loc.2.ram, a.loc.2.off_g,
    a.loc.2.nu_eq, a.loc.2.typeDim_eq, a.loc.2.ZQ_eq, a.loc.2.quotientLocalValueFirst_eq⟩
  inK := a.inK
  geo := by
    obtain ⟨F, ePl, eC, g, pin, cusp, iso, lev⟩ := a.geo
    exact ⟨F, ePl, eC, ⟨⟨g.shv.lev, g.shv.shv⟩,
      ⟨g.pl.wt, g.pl.jc, g.pl.mp, g.pl.md, g.pl.curveM, g.pl.degM, g.pl.htMdl, g.pl.htCurve⟩,
      ⟨g.geo.yv, g.geo.ybd, g.geo.lw⟩, g.lev_κg⟩, pin, cusp, iso, lev⟩

theorem exists_divT_true_surface {slots : Slots} (w : ColW B f T) (pin : ColPin w)
    (Z : w.Lt) (l : Lv4 slots K w Z) :
    ∃ Y : DivX (w.D Z), Nonempty (DivT l.n Y) ∧ MjAre l.what₂.r.Z Y ∧
      (∀ σ, Y.kapR σ = kapSharp (w.D Z)) ∧ LamAre l.what₂.r.Z Y ∧ HasTrueSurf Y ∧
      Y.vdd = (fun p _ => vDiff (w.D Z).host.E p) := by
  obtain ⟨X, ⟨a⟩, ⟨J, hJ⟩, hk, hl⟩ := DivRec.exists_divT w pin Z l
  exact ⟨repair X, ⟨divT_repair a⟩, ⟨⟨J.eW⟩, ⟨hJ.1, hJ.2⟩⟩, hk, hl, rfl, rfl⟩

def surfaceAndDifferent : GeoP := fun D _ X =>
  HasTrueSurf X ∧ X.vdd = (fun p _ => vDiff D.host.E p)

theorem divEx_surface_and_different (slots : Slots) (hOx : slots.Ox = OX (some surfaceAndDifferent)) :
    DivEx slots :=
  StepW.of_all fun _ _ _ _ w _ _ hpin Z l => by
    obtain ⟨Y, hD, hM, hk, hl, hs, hd⟩ := exists_divT_true_surface w hpin.some Z l
    refine ⟨Y, hD, hM, hk, fun O t hX hp ht => ?_⟩
    rw [hOx]
    exact ⟨⟨hX ▸ ⟨hs, hd⟩, DivRec.lamAre_heq hp ht (hX ▸ hl)⟩⟩

open GlobalTheory.VarietyModelRecord

-- Swap in a family of models while retaining all the character and local data.
def divT_record {n : NchT w Z Wt nch} {X : DivX (w.D Z)} (a : DivT n X)
    {G : DV.Geo (w.D Z).what₂.LL} {L : Type} (F : ShimFam (w.D Z) G L)
    (iM : _) (hiM : _) (dH : _) (pin : ComplexEmbeddingsCompatible F.jC)
    (cusp : CuspTieX (record (repair X) F iM hiM dH))
    (iso : IsoInv F) {inK : L → ℕ → Prop} (lev : LevInTie F inK) :
    DivT n (record (repair X) F iM hiM dH) where
  Qp := a.Qp
  chr := ⟨a.chr.Qp_iff, a.chr.eQPl, a.chr.qv_eq⟩
  loc := ⟨a.loc.1, a.loc.2.qv_eq, a.loc.2.deg1, a.loc.2.ram, a.loc.2.off_g,
    a.loc.2.nu_eq, a.loc.2.typeDim_eq, a.loc.2.ZQ_eq, a.loc.2.quotientLocalValueFirst_eq⟩
  inK := inK
  geo := ⟨F, _, _, record_tied _ F iM hiM dH, pin, cusp, iso, lev⟩

-- Unlike the one-level graft, this family has two levels and uses the model-record
-- constructor from IsGeoOf itself. Its geometry is still the degenerate geometry.
noncomputable def twoLevelFamily (s : Stages) (jc : JC s.toD7) :
    ShimFam s.toD7 (geoDegenerate s.toD7.what₂.LL s.toD7.what₂.Tau) Bool where
  levPr := fun _ => Finset.univ.image s.toD7.host.g
  levPr_prime := fun _ => prime_of_mem_image s.toD7 ()
  κg := false
  levPr_κg := rfl
  jC := jc
  ng := ng1
  U := shimUFl s.toD7 jc
  forms := formsFl s.toD7 s.B.Ks (RingEquiv.refl _) s.B.Ks.val.toRingHom
    (fun _ => rfl) _ _ _ (fun _ _ => true)

theorem twoLevelFamily_iso (s : Stages) (jc : JC s.toD7) : IsoInv (twoLevelFamily s jc) := by
  intro w w' hiso _ hj h h'
  exact (toShimX_fl _ jc w h _).trans ((shimXFl_congr _ jc _ _ _ _ hiso.rank_eq hj).trans
    (toShimX_fl _ jc w' h' _).symm)

theorem two_level_replacement {slots : Slots} (w : ColW B f T) (pin : ColPin w)
    (Z : w.Lt) (l : Lv4 slots K w Z) :
    ∃ Y : DivX (w.D Z), Nonempty (DivT l.n Y) ∧ MjAre l.what₂.r.Z Y ∧
      (∀ σ, Y.kapR σ = kapSharp (w.D Z)) ∧ LamAre l.what₂.r.Z Y ∧
      HasTrueSurf Y ∧ Y.vdd = (fun p _ => vDiff (w.D Z).host.E p) ∧
      (∃ a b : Y.Lev, a ≠ b) ∧
      ∀ Q : ∀ D : D7, KitClass D, ¬ geoCl (geoOf Q) (w.D Z) l.what₂.r.z.core.toCore Y := by
  classical
  obtain ⟨X, ⟨a⟩, ⟨J, hJ⟩, hk, hl⟩ := DivRec.exists_divT w pin Z l
  let jc : JC (w.D Z) := fun p _ v => (GlobalTheory.WittFracPlace.exists_jcPin (w.D Z) p v).choose
  have hjc : jc.Pinned := fun p _ v => (GlobalTheory.WittFracPlace.exists_jcPin (w.D Z) p v).choose_spec
  let F := twoLevelFamily (w.st Z) jc
  let Y := record (repair X) F (fun _ _ => 0) (fun _ _ _ => Submodule.zero_mem _) (fun _ _ _ => 0)
  have hD : DivT l.n Y := divT_record a F _ _ _ (PinPlace.pinned_tiedFor _ jc hjc)
    (fun _ _ _ _ _ => trivial) (twoLevelFamily_iso (w.st Z) jc) (inK := fun _ _ => True) (fun _ _ => Iff.rfl)
  exact ⟨Y, ⟨hD⟩, ⟨⟨J.eW⟩, ⟨hJ.1, hJ.2⟩⟩, hk, hl, rfl, rfl,
    ⟨false, true, Bool.false_ne_true⟩, fun _ => degenerate_rejects_closure rfl⟩

theorem lawful_top_at_rows {slots : Slots} (hRx : slots.Rx = RX)
    {w : ColW B f T} {Z : w.Lt} (l : Lv4 slots K w Z) :
    ∃ P : Formalism.L2.Pj.Top (w.D Z), Formalism.L2.Pj.LawsP P ∧ P.toCore = l.what₂.r.z.core.toCore := by
  have rx := l.rx
  rw [hRx] at rx
  exact GlobalTheory.FinalJoin.exists_top_of_core _ _ rx.laws rx.rank
    (GlobalTheory.Mem.TypeNormPin.hermitianCodeWordStages_typeNorms_principal (w.st Z))

-- For a genuine family, each index admits precisely the divisors of its level.
-- In particular every index excludes some positive integer.
theorem family_excludes_a_positive_level {D : D7} {Q : KitClass D}
    {P : Formalism.L2.Pj.Top D} {hP : Formalism.L2.Pj.LawsP P} {c}
    (Φ : FamOver Q P hP c) : ∀ i : P.G.P.Dat, ∃ m : ℕ, 0 < m ∧ ¬ P.G.P.levIn i m := by
  obtain ⟨I, dat, hI, _, _, _, hp, _⟩ := Φ.prov
  let R (pkg : ModuliIntegralCharts.Prov D) := ∀ i : pkg.Dat, ∃ m : ℕ, 0 < m ∧ ¬ pkg.levIn i m
  change R P.G.P
  rw [hp]
  intro i
  let n := (dat i).κ.l.M'
  have hn : 0 < n := Nat.lcm_pos (by have := (dat i).κ.l.three_le; omega) (dat i).κ.l.A_pos
  refine ⟨n + 1, Nat.succ_pos _, fun h => ?_⟩
  have hd : n + 1 ∣ n := ((Φ.k.at (dat i)).levIn _).mp h
  exact (Nat.not_succ_le_self n) (Nat.le_of_dvd hn hd)

noncomputable def allLevelsTop {D : D7} (P : Formalism.L2.Pj.Top D) : Formalism.L2.Pj.Top D :=
  { P with G := { P.G with P := { P.G.P with levIn := fun _ _ => True } } }

theorem allLevels_laws {D : D7} {P : Formalism.L2.Pj.Top D} (h : Formalism.L2.Pj.LawsP P) :
    Formalism.L2.Pj.LawsP (allLevelsTop P) :=
  ⟨h.toLawsCore, h.allTest, h.reg, h.datum_condition, h.tower, h.hasData_condition, h.points_condition,
    h.lattice_condition, h.bc66, h.datIndep, h.nabPin, h.nabUniq, h.thTot, h.thCusp, h.thNe, h.kPsi⟩

theorem lawful_top_without_family {slots : Slots} (hRx : slots.Rx = RX)
    {w : ColW B f T} {Z : w.Lt} (l : Lv4 slots K w Z) :
    ∃ (P : Formalism.L2.Pj.Top (w.D Z)) (h : Formalism.L2.Pj.LawsP P),
      P.toCore = l.what₂.r.z.core.toCore ∧ ∀ (Q : KitClass (w.D Z)) c, ¬ Nonempty (FamOver Q P h c) := by
  obtain ⟨P, hP, e⟩ := lawful_top_at_rows hRx l
  refine ⟨allLevelsTop P, allLevels_laws hP, e, fun _ _ ⟨Φ⟩ => ?_⟩
  obtain ⟨_, _, hm⟩ := family_excludes_a_positive_level Φ (P.G.dat 1)
  exact hm trivial

-- Assembly with the project's genuine family. All geometric inputs are explicit.
-- No IsGeoOf, geoOf, or GeoCl hypothesis is used.
theorem genuine_replacement_of_family {slots : Slots} {w : ColW B f T}
    {Z : w.Lt} (l : Lv4 slots K w Z) (Q : ∀ D : D7, KitClass D)
    (P : Formalism.L2.Pj.Top (w.D Z)) (hP : Formalism.L2.Pj.LawsP P)
    (core_eq : P.toCore = l.what₂.r.z.core.toCore) (c : ℕ) (hc : 0 < c)
    (Φ : FamOver (Q _) P hP c) (X : DivX (w.D Z)) (a : DivT l.n X)
    (hM : MjAre l.what₂.r.Z X) (hk : ∀ σ, X.kapR σ = kapSharp (w.D Z))
    (hl : LamAre l.what₂.r.Z X) (iM : _) (hiM : _)
    (reads : Φ.Reads (repair X) iM)
    (cusp : CuspTieX (record (repair X) Φ.fam iM hiM Φ.dH)) (iso : IsoInv Φ.fam) :
    ∃ Y : DivX (w.D Z), Nonempty (DivT l.n Y) ∧ MjAre l.what₂.r.Z Y ∧
      (∀ σ, Y.kapR σ = kapSharp (w.D Z)) ∧ LamAre l.what₂.r.Z Y ∧
      geoOf Q (w.D Z) l.what₂.r.z.core.toCore Y := by
  obtain ⟨J, hJ⟩ := hM
  exact ⟨_, ⟨divT_record a Φ.fam iM hiM Φ.dH (PinPlace.pinned_tiedFor _ Φ.jC Φ.pin)
    cusp iso (inK := Lv.inK) (fun w M => (Φ.k.at w).levIn M)⟩,
    ⟨⟨J.eW⟩, ⟨hJ.1, hJ.2⟩⟩, hk, hl, ⟨c, hc, P, hP, Φ, repair X, iM, hiM, core_eq, rfl, reads, rfl⟩, rfl⟩

#print axioms repaired_graft_rejects_closure
#print axioms exists_divT_true_surface
#print axioms degenerate_rejects_closure
#print axioms divEx_surface_and_different
#print axioms two_level_replacement
#print axioms genuine_replacement_of_family
#print axioms lawful_top_without_family

end GeometryAudit.Replacement
