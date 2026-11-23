import FamilyTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameOfFlagAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemBasesNonempty
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemRangeOfValVLeOne
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ClosedBallValuationSubringToSubring
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ChartCoverFOfSectionBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap

open AlgebraicGeometry CategoryTheory Limits NumberField Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.LocM GlobalTheory.LocM.Cht

namespace GeometryAudit.LocalPoint
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
  {H : Host E} {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l}
  {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

-- On a kit model, a frame on an underlying integral point gives a point above
-- that very point, over the same valued field. This applies in particular to YY.
theorem lift_to_model (Z : Mdl Y i₀) {C : SCF p} (P : PointsOfFlagModel.PtC (Y Z.i) C)
    (u : Vecs Dw (Y Z.i).t ↥C.S) (hu : IsFrame (Y Z.i).t P.fK P.x0 u) :
    ∃ q : PtAt Z C, q.P = P := by
  obtain ⟨g, ⟨hg, _⟩, _⟩ := Z.bij ↥C.S P.fK P.y P.y_over u hu
  have hr : Set.range g ⊆ Z.opn := by
    rintro _ ⟨s, rfl⟩
    exact ⟨P.y s, (congrArg (fun f => f s) hg).symm⟩
  have hs : g ≫ Z.s = spMap ((intO ↥C.S).subtype.comp P.alg) := by
    rw [← Z.π_s, ← Category.assoc, hg, P.compat]
    exact FamPf.x0_s P
  obtain ⟨q, hq⟩ := exists_ptAt_gen Z C g P.alg hr hs
  refine ⟨⟨P, q.z, ?_⟩, rfl⟩
  apply base_ext Z.i
  rw [← Category.assoc, P.ext]
  exact (congrArg (fun w => w ≫ Z.π) hq).trans hg

theorem lift_generic_frame (Z : Mdl Y i₀) (C : SCF p) [Algebra Z.i.c.F ↥C.S]
    (bounded : ∀ x : Z.i.c.V W, ‖algebraMap Z.i.c.F ↥C.S x‖ ≤ 1)
    (y : Sp ↥C.S ⟶ (Xo Z.i.l).XF Z.i.c)
    (hy : y ≫ pullback.snd _ _ = spMap (algebraMap Z.i.c.F ↥C.S))
    (v : FrPt (Xo Z.i.l) Z.i.c ↥C.S) (hv : v.x = y ≫ pullback.fst _ _) :
    ∃ q : PtAt Z C, q.P.fK = algebraMap Z.i.c.F ↥C.S ∧ q.P.y = y := by
  obtain ⟨P, hf, he⟩ := GlobalTheory.LocM.Tower.exists_ptC (Y Z.i) C _ bounded y hy
  obtain ⟨u, hu⟩ := BaseMdl.exists_frame_of_frPt (Y Z.i) y v hv
  have hframe : IsFrame (Y Z.i).t P.fK P.x0 u := by simpa [PointsOfFlagModel.PtC.x0, hf, he] using hu
  obtain ⟨q, hq⟩ := lift_to_model Z P u hframe
  exact ⟨q, hq ▸ hf, hq ▸ he⟩

#print axioms lift_to_model
#print axioms lift_generic_frame

open Formalism.BasicNotions Formalism.L2.Geo GlobalTheory.ShFam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem bounded_place {D : D7} {p : ℕ} [hp : Fact p.Prime] (C : SCF p)
    (f : D.what₂.LL →+* ↥C.S) : ∃ v : PlL D p, ∀ a : D.what₂.LL,
      v.1.valuation D.what₂.LL a ≤ 1 → ‖f a‖ ≤ 1 := by
  let W := (GlobalTheory.ClosedBallValuationSubring.closedBallValuationSubring ↥C.S).comap f
  obtain ⟨v, hv⟩ := GlobalTheory.RealisationValues.Proportional.exists_place_le W
  have hb (a : D.what₂.LL) (ha : v.valuation D.what₂.LL a ≤ 1) : ‖f a‖ ≤ 1 := hv ha
  refine ⟨⟨v, ?_⟩, hb⟩
  by_contra h
  have hu := (v.valuation_eq_one_iff_notMem (K := D.what₂.LL)).2 h
  have hu' : v.valuation D.what₂.LL (p : D.what₂.LL) = 1 := by simpa using hu
  have hb' := hb (p : D.what₂.LL)⁻¹ (by rw [map_inv₀, hu', inv_one])
  rw [map_inv₀, map_natCast, norm_inv, C.norm_p, inv_inv] at hb'
  exact (not_le_of_gt (show (1 : ℝ) < p by exact_mod_cast hp.out.one_lt)) hb'

-- The choice of a finite place is also available from the kit's hypotheses.
theorem kit_point_over_frame {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j}
    {κ : Lv A} {jc : JC D} (pin : jc.Pinned) (cts : Ats S κ) (hc : cts.Over jc)
    {p : ℕ} [Fact p.Prime] (C : SCF p) [Algebra κ.c.F ↥C.S]
    (fr : FrPt (S.Xo κ.l) κ.c ↥C.S) :
    ∃ (v : PlL D p) (q : PtAt (cts p v).YY C), HEq (q.P.y ≫ pullback.fst _ _) fr.x := by
  let f := algebraMap κ.c.F ↥C.S
  obtain ⟨v, bv⟩ := bounded_place C (f.comp κ.e.toRingHom)
  let ct := cts p v
  let i₀ : Idx A.H p := ⟨κ.l, κ.c, κ.good p ct.hp⟩
  let Ready (i : Idx A.H p) : Prop := ∃ (_ : Algebra i.c.F ↥C.S),
    (∀ x : i.c.V ct.W, ‖algebraMap i.c.F ↥C.S x‖ ≤ 1) ∧
    ∃ z : FrPt (S.Xo i.l) i.c ↥C.S, HEq z.x fr.x
  have hb : Ready i₀ := by
    refine ⟨inferInstanceAs (Algebra κ.c.F ↥C.S), ?_, fr, HEq.rfl⟩
    intro x
    have hx : ((κ.e (κ.e.symm x.val) : κ.c.F) : ℂ) ∈ ct.W := by
      rw [RingEquiv.apply_symm_apply]
      exact x.property
    have hb' := bv (κ.e.symm x.val) ((AllPrimesCheck.over_induces hc p v (pin p v) _).mp hx)
    simpa [f] using hb'
  have hi : ct.YY.i = i₀ := ct.isYY.1.trans (ct.B.lvl none)
  obtain ⟨inst, bounded, z, hz⟩ : Ready ct.YY.i := hi ▸ hb
  let := inst
  obtain ⟨y, hy, hyf⟩ := GlobalTheory.Frames.ChartCover.exists_lift z
  obtain ⟨q, _, eq⟩ := lift_generic_frame ct.YY C bounded y hyf z hy.symm
  exact ⟨v, q, (heq_of_eq (eq ▸ hy)).trans hz⟩

#print axioms kit_point_over_frame

theorem kit_point_over_tied_frame {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j}
    {κ : Lv A} {jc : JC D} (pin : jc.Pinned) (cts : Ats S κ) (hc : cts.Over jc)
    (m : MD A.H) (hm : m = ⟨κ.l, S.Dw, S.Xo κ.l⟩) (c : Coeff m.1) (hle : c.F ≤ κ.c.F)
    {p : ℕ} [Fact p.Prime] (C : SCF p) [Algebra c.F ↥C.S] (fr : FrPt m.2.2 c ↥C.S) :
    ∃ (v : PlL D p) (q : PtAt (cts p v).YY C), HEq (q.P.y ≫ pullback.fst _ _) fr.x := by
  subst m
  let : Algebra c.F κ.c.F := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  have : IsScalarTower ℚ c.F κ.c.F := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have := κ.c.fin
  have : FiniteDimensional c.F κ.c.F := Module.Finite.of_restrictScalars_finite ℚ c.F κ.c.F
  let f : κ.c.F →ₐ[c.F] ↥C.S := IsAlgClosed.lift
  let : Algebra κ.c.F ↥C.S := f.toRingHom.toAlgebra
  exact kit_point_over_frame pin cts hc C (fr.ext hle fun a => f.commutes a)

open Formalism.MainNotions GeometryAudit.FamilyTop

private def hasField {D : D7} {N j p : ℕ} (loc : ModuliIntegralCharts.Loc D N j p) (C : ModuliIntegralCharts.CF p) :=
  ∃ η : loc.Pt loc.YY, loc.fld η = C

private theorem hasField_of_heq {D : D7} {N j N' j' p : ℕ}
    {loc : ModuliIntegralCharts.Loc D N j p} {loc' : ModuliIntegralCharts.Loc D N' j' p} {C}
    (hN : N = N') (hj : j = j') (h : HEq loc loc') : hasField loc C ↔ hasField loc' C := by
  subst N'; subst j'; cases h
  rfl

-- For the actual family-derived top, every relevant algebraic tower point
-- has a kit point over exactly the same valued field.
theorem family_point_same_field {D : D7} {T : Top D} (h : LawsP T) {st : StFams D}
    (R : RowKits T h st) {j : ℕ} (hj : 1 ≤ j) (hm : j < D.R.m) (la)
    (z : PointsOfFlagModel.Pt (T.G.Tw j (WeightAlgebra.resCh la)) .yy) (hz : T.G.IsAlgPt j la z) :
    ∃ η : (familyG h R.k).PY j (WeightAlgebra.resCh la),
      ((familyG h R.k).P.loc ((familyG h R.k).dat j) _).fld η = PointsOfFlagModel.fld z := by
  let w := datW D R.F.κg j
  let p := WeightAlgebra.resCh la
  have : Fact p.Prime := ⟨resCh_prime la⟩
  have locEq := familyG_loc h R.k hj hm p
  have idx := familyG_indices h R.k hj hm
  apply (hasField_of_heq idx.1 idx.2 locEq).mpr
  · obtain ⟨_, _, cts, pin, _, kit⟩ := R.mem w.N w.j w.two_le w.j_le w.κ
    have leq : ((R.k.at w).pad.loc p) = (locStOf (st _ _ _ _ _) cts).loc p :=
      congrArg (fun pad => pad.loc p) kit.pad
    change hasField ((R.k.at w).pad.loc p) _
    rw [leq, locStOf_loc]
    obtain ⟨V, io, e, y, _, _, _, eF, _, _, _, _, _⟩ := hz
    let C := z.2.1
    let : Algebra T.Q.c.F V.Fr := io.toAlgebra
    let : Algebra T.Q.c.F ↥C.S := (eF.comp io).toAlgebra
    let φ : V.Fr →ₐ[T.Q.c.F] ↥C.S := ⟨eF, fun _ => rfl⟩
    obtain ⟨fr, _⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap
      GlobalTheory.firstFiveLaws.1.secBaseChange _ _ _ _ _ _ _ _ φ y.1
    obtain ⟨v, q, _⟩ := kit_point_over_tied_frame pin cts kit.ats _ (R.tie.same j ⟨hj, hm.le⟩)
      T.Q.c R.tie.le C fr
    exact ⟨⟨v, q.toPt⟩, rfl⟩

#print axioms family_point_same_field
end GeometryAudit.LocalPoint
