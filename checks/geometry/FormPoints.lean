import ProductionGeometry
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFlagModelBaseChangeIntegralFramedPoint

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.ShFam GlobalTheory.TrueGeo GlobalTheory.LocM GlobalTheory.ShFam.Pad
open GeometryAudit.FamilyTop GeometryAudit.FamilyLaws GeometryAudit.LocalPoint
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GeometryAudit.FormPoints
noncomputable section
open Classical

variable {D : D7} {T : Top D} (h : LawsP T) {st : StFams D} (R : RowKits T h st)

abbrev KitPoint (j : ℕ) (p : ℕ) := ((R.k.at (datW D R.F.κg j)).pad.loc p).Pt ((R.k.at (datW D R.F.κg j)).pad.loc p).YY

theorem kit_point_nonempty {j : ℕ} (hj : InR D j) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) :
    Nonempty (KitPoint h R j (WeightAlgebra.resCh la)) := by
  let d := datW D R.F.κg j
  let p := WeightAlgebra.resCh la
  have : Fact p.Prime := ⟨resCh_prime la⟩
  obtain ⟨V, io, n, ho, y, hy⟩ := h.ptNe j hj la
  obtain ⟨C, eF, _, _⟩ := (GlobalTheory.T.exists_embedding_completeAlgClosed_fixedCarrier V p (resCh_prime la) hy
    (GlobalTheory.Exist.FlagBaseChange.resCh_mem_maximalIdeal la V io n ho)).1
  let : Algebra T.Q.c.F V.Fr := io.toAlgebra
  let : Algebra T.Q.c.F ↥C.S := (eF.comp io).toAlgebra
  let φ : V.Fr →ₐ[T.Q.c.F] ↥C.S := ⟨eF, fun _ => rfl⟩
  obtain ⟨fr, _⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap
    GlobalTheory.firstFiveLaws.1.secBaseChange _ _ _ _ _ _ _ _ φ y.1
  obtain ⟨_, _, cts, pin, _, kit⟩ := R.mem d.N d.j d.two_le d.j_le d.κ
  have eq : ((R.k.at d).pad.loc p) = (locStOf (st _ _ _ _ _) cts).loc p :=
    congrArg (fun pad => pad.loc p) kit.pad
  change Nonempty (((R.k.at d).pad.loc p).Pt ((R.k.at d).pad.loc p).YY)
  rw [eq, locStOf_loc]
  obtain ⟨v, q, _⟩ := kit_point_over_tied_frame pin cts kit.ats _ (R.tie.same j hj) T.Q.c R.tie.le C fr
  exact ⟨⟨v, q.toPt⟩⟩

theorem kit_points_eq {j : ℕ} (hj : InR D j) (hm : j < D.R.m) (p : ℕ) :
    (familyTop h R.k).G.PY j p = KitPoint h R j p :=
  LocTie.pts (h := family_laws h R) (k := R.k) (fun _ h1 h2 q => familyG_loc h R.k h1 h2 q) j hj.1 hm p

-- Empty out-of-range fibres match the row's zero cusp modules.
def points (j : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) : Type :=
  if InR D j then (familyTop h R.k).PtA j la else Empty

def rowEquiv {j : ℕ} (hj : InR D j) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) :
    points h R j la ≃ (familyTop h R.k).PtA j la := Equiv.cast (if_pos hj)

def pointMap (j : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (x : points h R j la) :
    KitPoint h R j (WeightAlgebra.resCh la) := by
  classical
  by_cases hj : InR D j
  · by_cases hm : j < D.R.m
    · exact cast (kit_points_eq h R hj hm _) (imgV (rowEquiv h R hj la x))
    · exact (kit_point_nonempty h R hj la).some
  · exact (cast (show points h R j la = Empty from if_neg hj) x).elim

theorem pointMap_img {j : ℕ} (hj : InR D j) (hm : j < D.R.m) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (x : points h R j la) :
    HEq (pointMap h R j la x) (imgV (rowEquiv h R hj la x)) := by
  simp only [pointMap, dif_pos hj, dif_pos hm]
  exact cast_heq _ _

end
#print axioms kit_point_nonempty
#print axioms pointMap_img
end GeometryAudit.FormPoints
