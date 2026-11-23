import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LargeFor
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesHasRootOfUnity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesRingOfIntegersFull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToroidalSystemOfSiegelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelToroidalIntegralHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidBoundaryChartsForFanUnitaryDatum
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsConstAlongConeZero
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.CyclotomicRootsOfUnity
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmCurveTorsionDefinedOverOfWeberValues
import FixedCoreTie
import ReplacementGeometry

open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.ShFam
open GlobalTheory.IndefiniteRowSideFullHecke.CyclotomicRootsOfUnity
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (zeta)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GeometryAudit.Source

def baseLevel (D : D7) := D.host.g 0 * D.host.g 1
def extendedLevel (D : D7) := Nat.lcm (baseLevel D) 15

theorem baseLevel_pos (D : D7) : 0 < baseLevel D := Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos

theorem roots_at_stages (s : Stages) :
    zeta (baseLevel s.toD7) ∈ fieldLL s.toD7 ∧ zeta (extendedLevel s.toD7) ∈ fieldLL s.toD7 := by
  obtain ⟨y, hy⟩ := s.B.exists_root_mul
  have hg : zeta (baseLevel s.toD7) ∈ fieldLL s.toD7 := ⟨s.B.OtoLL y, hy⟩
  obtain ⟨x, _, hx⟩ := s.B.roots_Ks (3 ^ 4) (by
    simp only [List.mem_cons]
    exact Or.inr (Or.inr (Or.inr (Or.inl trivial))))
  obtain ⟨y, _, hy⟩ := s.B.roots_Ks (5 ^ 4) (by
    simp only [List.mem_cons]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl trivial)))))
  have h3 : zeta 3 ∈ fieldLL s.toD7 :=
    zeta_mem_of_dvd (F := fieldLL s.toD7) (a := 3) (N := 3 ^ 4) (by decide) (by decide) ⟨x, hx⟩
  have h5 : zeta 5 ∈ fieldLL s.toD7 :=
    zeta_mem_of_dvd (F := fieldLL s.toD7) (a := 5) (N := 5 ^ 4) (by decide) (by decide) ⟨y, hy⟩
  have h15 := zeta_lcm_mem (a := 3) (b := 5) (by decide) (by decide) h3 h5
  rw [show Nat.lcm 3 5 = 15 by decide] at h15
  exact ⟨hg, zeta_lcm_mem (a := baseLevel s.toD7) (b := 15) (baseLevel_pos _).ne' (by decide) hg h15⟩

theorem sys_at_stages : SysExSt :=
  GlobalTheory.T.toroidal_system_of_siegel GlobalTheory.siegelToroidalIntegral_holds
    (GlobalTheory.RigChart.Model.toroidalChartsForFan GlobalTheory.RigChart.rigidForFan_holds)

-- The coefficient field is fixed by the row. The criterion is independent of the
-- choice of divisor, maps or kits. It concerns the source family inside FamOver.
theorem source_iff_curve (s : Stages) (P : Top s.toD7) (hP : LawsP P) :
    (∃ F : SrcFam (ambOf P.Q hP.pins.1), F.Pinned P.pb 1) ↔
      GlobalTheory.CompRat.CurveOver P.Q.H (fieldLL s.toD7) (extendedLevel s.toD7) := by
  let A := ambOf P.Q hP.pins.1
  have hpos : 0 < extendedLevel s.toD7 := Nat.lcm_pos (baseLevel_pos _) (by decide)
  constructor
  · rintro ⟨F, hf⟩
    have h := F.κs.curve
    rw [F.κs.F_eq] at h
    have e : F.κs.l.M' = extendedLevel s.toD7 := by
      change Nat.lcm _ _ = Nat.lcm _ _
      rw [F.κs_M.1, F.κg_M, hf.2, pow_one]
      rfl
    exact e ▸ h
  · intro hc
    have hg := (GlobalTheory.FinalJoin.CurveField.curveOver_of_weberIn _ P.Q.H
      (fieldLL s.toD7) _ hpos).2 _ (Nat.dvd_lcm_left _ _) hc
    obtain ⟨hroot, hext⟩ := roots_at_stages s
    apply exists_srcFam A (fun Dw hn => sys_at_stages _ _ Dw (by omega))
      (hermitianCodeWordStages_ringOfIntegers_full s) (hermitianCodeWordStages_has_rootOfUnity s)
      P.pb hP.half.1 1 (by decide) ⟨hroot, hg⟩
    rw [pow_one]
    exact ⟨hext, hc⟩

theorem tied_source_iff_curve (s : Stages) (P : Top s.toD7) (hP : LawsP P) :
    (∃ F : SrcFam (ambOf P.Q hP.pins.1), F.Pinned P.pb 1 ∧ ParTie P.Q hP.pins.1 F) ↔
      GlobalTheory.CompRat.CurveOver P.Q.H (fieldLL s.toD7) (extendedLevel s.toD7) := by
  constructor
  · rintro ⟨F, hf, _⟩
    exact (source_iff_curve s P hP).mp ⟨F, hf⟩
  · intro hc
    obtain ⟨F, pin⟩ := (source_iff_curve s P hP).mpr hc
    exact GeometryAudit.FixedCore.parTie_of_pinned_source P hP sys_at_stages F pin

open Formalism.MainNotions.Inhab GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Col2 in
theorem rh_rows_tied_iff {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}
    {w : ColW B f T} {Z : w.Lt} {slots : Slots} (hRx : slots.Rx = RX) (l : Lv4 slots K w Z) :
    (∃ (P : Formalism.L2.Pj.Top (w.D Z)) (h : LawsP P), P.toCore = l.what₂.r.z.core.toCore ∧
      ∃ F : SrcFam (ambOf P.Q h.pins.1), F.Pinned P.pb 1 ∧ ParTie P.Q h.pins.1 F) ↔
      GlobalTheory.CompRat.CurveOver l.what₂.r.z.core.Q.H (fieldLL (w.D Z)) (extendedLevel (w.D Z)) := by
  let C (J : Core (w.D Z)) := GlobalTheory.CompRat.CurveOver J.Q.H (fieldLL (w.D Z)) (extendedLevel (w.D Z))
  constructor
  · rintro ⟨P, hP, e, hf⟩
    exact (congrArg C e).mp ((tied_source_iff_curve (w.st Z) P hP).mp hf)
  · intro hc
    obtain ⟨P, hP, e⟩ := GeometryAudit.Replacement.lawful_top_at_rows hRx l
    exact ⟨P, hP, e, (tied_source_iff_curve (w.st Z) P hP).mpr ((congrArg C e).mpr hc)⟩

-- Even if the chosen positive exponent is larger than one, this same curve
-- condition is necessary.
theorem curve_of_family {D : D7} {Q : KitClass D} {P : Top D} {hP : LawsP P}
    {c : ℕ} (Φ : FamOver Q P hP c) (hc : 0 < c) :
    GlobalTheory.CompRat.CurveOver P.Q.H (fieldLL D) (extendedLevel D) := by
  have h := Φ.F.κs.curve
  rw [Φ.F.κs.F_eq] at h
  have e : Φ.F.κs.l.M' = Nat.lcm (baseLevel D) (15 ^ c) := by
    change Nat.lcm _ _ = _
    rw [Φ.F.κs_M.1, Φ.F.κg_M, Φ.exp]
    rfl
  rw [e] at h
  apply (GlobalTheory.FinalJoin.CurveField.curveOver_of_weberIn _ P.Q.H _ _
    (Nat.lcm_pos (baseLevel_pos D) (pow_pos (by decide) _))).2 _ _ h
  exact Nat.lcm_dvd (Nat.dvd_lcm_left _ _) ((dvd_pow_self 15 hc.ne').trans (Nat.dvd_lcm_right _ _))

open GlobalTheory.Mem.Top.Bl Formalism.MainNotions in
theorem curve_of_closure {Q : ∀ D : D7, KitClass D} {D : D7} {J : Core D} {X : DivX D}
    (h : GeoCl (geoOf Q) D J X) :
    GlobalTheory.CompRat.CurveOver J.Q.H (fieldLL D) (extendedLevel D) := by
  induction h with
  | base h =>
    obtain ⟨⟨c, hc, P, hP, Φ, _, _, _, rfl, _, _, _⟩, _⟩ := h
    exact curve_of_family Φ hc
  | step _ _ _ ih => exact ih

#print axioms source_iff_curve
#print axioms curve_of_family
#print axioms curve_of_closure
#print axioms tied_source_iff_curve
#print axioms rh_rows_tied_iff
end GeometryAudit.Source
