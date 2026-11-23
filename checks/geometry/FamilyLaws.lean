import ModelComparison
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToShimXEqShimXOfPkg

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.LocM
open GeometryAudit.FamilyTop GeometryAudit.LocalPoint
open Formalism.MainNotions.DIV.Cons (SCF)

namespace GeometryAudit.FamilyLaws

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem compare_tied {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {m m' : MD H} (tie : m = m')
    {c : Coeff m.1} {c' : Coeff m'.1} {O O' : Type} [CommRing O] [CommRing O']
    {β : O →+* c.F} {β' : O' →+* c'.F} {Y : Model m.2.2 c β} {Y' : Model m'.2.2 c' β'}
    {p : ℕ} (hp : p.Prime) {C : SCF p} (P : PointsOfFlagModel.PtC Y C) (P' : PointsOfFlagModel.PtC Y' C)
    (T : CDVR) (hT : T.FinRes) (io : c.F →+* T.Fr) (e : T.Fr →+* ↥C.S)
    (y : IntFr m.2.2 c T io) (ei : e.comp io = P.fK)
    (bound : ∀ a : T.V, ‖e (algebraMap T.V T.Fr a)‖ ≤ 1)
    (ex : letI := io.toAlgebra; P.y ≫ pullback.fst _ _ = spMap e ≫ y.1.x)
    (ex' : letI := io.toAlgebra; HEq (P'.y ≫ pullback.fst _ _) (spMap e ≫ y.1.x)) (A : DatAt Y P) (B : DatAt Y' P') :
    ∃ f : B.Ylat ≃ₗ[𝓞 E] A.Ylat, ∀ a b, A.beta (f a) (f b) = B.beta a b := by
  subst m'
  let : Algebra c.F T.Fr := io.toAlgebra
  obtain ⟨G, t, mx, mg, _⟩ := y.2.2
  obtain ⟨f, hf⟩ := ModelComparison.compare_at_point Y Y' hp P P' T hT io e y.1.x G t mx mg ei bound ex (eq_of_heq ex') A B
  exact ⟨f.symm, fun a b => by simpa using (hf (f.symm a) (f.symm b)).symm⟩

private def matchingPoint {D : D7} {T : Top D} {j p : ℕ}
    (z : PointsOfFlagModel.Pt (T.G.Tw j p) .yy) {N i : ℕ} (L : ModuliIntegralCharts.Loc D N i p) : Prop :=
  ∃ η : L.Pt L.YY, L.fld η = PointsOfFlagModel.fld z ∧
    ∀ A : DatAt ((T.G.Tw j p).Y z.1) z.2.2.1,
      ∃ e : L.Ylat η ≃ₗ[𝓞 D.host.E] A.Ylat, ∀ a b, A.beta (e a) (e b) = L.be η a b

private theorem matchingPoint_congr {D : D7} {T : Top D} {j p : ℕ}
    (z : PointsOfFlagModel.Pt (T.G.Tw j p) .yy) {N i N' i' : ℕ}
    {L : ModuliIntegralCharts.Loc D N i p} {L' : ModuliIntegralCharts.Loc D N' i' p}
    (hN : N = N') (hi : i = i') (h : HEq L L') : matchingPoint (T := T) z L ↔ matchingPoint (T := T) z L' := by
  subst N'; subst i'; cases h
  rfl

theorem family_points_and_lattices {D : D7} {T : Top D} (h : LawsP T) {st : StFams D}
    (R : RowKits T h st) : localPointsExist h R.k := by
  intro j hj hm la z hz
  let w := datW D R.F.κg j
  let p := WeightAlgebra.resCh la
  have : Fact p.Prime := ⟨resCh_prime la⟩
  have idx := familyG_indices h R.k hj hm
  apply (matchingPoint_congr (T := T) z idx.1 idx.2 (familyG_loc h R.k hj hm p)).mpr
  obtain ⟨_, _, cts, pin, _, kit⟩ := R.mem w.N w.j w.two_le w.j_le w.κ
  have leq : ((R.k.at w).pad.loc p) = (locStOf (st _ _ _ _ _) cts).loc p :=
    congrArg (fun pad => pad.loc p) kit.pad
  change matchingPoint (T := T) z ((R.k.at w).pad.loc p)
  rw [leq, locStOf_loc]
  obtain ⟨V, io, n, y, _, hV, _, e, ei, bound, _, ex, _⟩ := hz
  let C := z.2.1
  let : Algebra T.Q.c.F V.Fr := io.toAlgebra
  let : Algebra T.Q.c.F ↥C.S := (e.comp io).toAlgebra
  let φ : V.Fr →ₐ[T.Q.c.F] ↥C.S := ⟨e, fun _ => rfl⟩
  obtain ⟨fr, hfr⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap
    GlobalTheory.firstFiveLaws.1.secBaseChange _ _ _ _ _ _ _ _ φ y.1
  have tie := R.tie.same j ⟨hj, hm.le⟩
  obtain ⟨v, q, hq⟩ := kit_point_over_tied_frame pin cts kit.ats _ tie T.Q.c R.tie.le C fr
  let ct := cts p v
  let S := R.F.sig w.N w.j w.two_le w.j_le
  have hi : ct.YY.i = ⟨w.κ.l, w.κ.c, w.κ.good p ct.hp⟩ := ct.isYY.1.trans (ct.B.lvl none)
  have same : (⟨T.Q.l, T.Q.Dw j, T.Q.Xo j⟩ : MD T.Q.H) =
      ⟨ct.YY.i.l, S.Dw, S.Xo ct.YY.i.l⟩ := by rw [hi]; exact tie
  refine ⟨⟨v, q.toPt⟩, rfl, fun A => ?_⟩
  exact compare_tied same (resCh_prime la) z.2.2.1 q.P V hV io e y ei bound ex
    (hq.trans (heq_of_eq hfr.1)) A (ct.dat q.toPt)

theorem family_laws {D : D7} {T : Top D} (h : LawsP T) {st : StFams D} (R : RowKits T h st) :
    LawsP (familyTop h R.k) :=
  (familyTop_laws_iff h R.k).2 (family_points_and_lattices h R)

#print axioms family_points_and_lattices
#print axioms family_laws
end GeometryAudit.FamilyLaws
