import SourceFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoverFieldOfWeberLev

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
open GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.Bl GlobalTheory.FinalJoin GlobalTheory.ShFam
open Formalism.L2.Pj GeometryAudit.Source
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GeometryAudit.Production

def requiredLevel (b : Pre) := Nat.lcm (b.host.g 0 * b.host.g 1) 15

private theorem requiredLevel_pos (b : Pre) : 0 < requiredLevel b :=
  Nat.lcm_pos (Nat.mul_pos (b.host.g_prime 0).pos (b.host.g_prime 1).pos) (by decide)

-- StepW, the interface of DivEx, already quantifies eventually over bases.
-- Its large₂ clause can request these finitely many algebraic Weber values.
def weberCondition (B : Base) (_ : Fr B.toPre) (_ : TwDat B) : Prop :=
  ∀ (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host B.host.E),
    H.rt0 = B.host.φ₀ B.host.sqrtMinusD → WeberIn H B.LLC (requiredLevel B.toPre)

theorem eventually_weber (K : Ctx) : large₂ K weberCondition := by
  classical
  choose S halg hmem using fun b : Pre => CoverAt.exists_finset_weberIn
    (b.host.φ₀ b.host.sqrtMinusD) (requiredLevel b) (requiredLevel_pos b).ne'
  exact ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅,
    fun b _ _ _ _ => S b, by simp, fun b _ _ _ _ => halg b,
    fun B _ _ _ hfield _ _ H he => hmem B.toPre _ H he _ hfield.2⟩

def tiedSourceRows (slots : Slots) : WP := fun K _ _ _ w => ∀ (Z : w.Lt) (l : Lv4 slots K w Z),
  ∃ (P : Formalism.L2.Pj.Top (w.D Z)) (h : LawsP P), P.toCore = l.what₂.r.z.core.toCore ∧
    ∃ F : SrcFam (ambOf P.Q h.pins.1), F.Pinned P.pb 1 ∧ ParTie P.Q h.pins.1 F

theorem production_parTie (slots : Slots) (hRx : slots.Rx = RX) : StepW Pinned (tiedSourceRows slots) := by
  have hw : Step KPx (fun _ _ _ _ => True) (fun _ => weberCondition) :=
    Step.of_evLgG (evG_all eventually_weber)
  apply hw.trans (Step.of_all ?_)
  intro K B f T _ _ _ hfield w _ Z l
  apply (rh_rows_tied_iff hRx l).mpr
  let D := w.D Z
  have rx := l.rx
  rw [hRx] at rx
  have hp := rx.laws.pins.1
  have hr : l.what₂.r.z.core.Q.H.rt0 ∈ fieldLL D :=
    ⟨D.embE D.host.sqrtMinusD, (RingHom.congr_fun D.embE_φ₀ _).trans hp.2.2.1.symm⟩
  exact (GlobalTheory.FinalJoin.CurveField.curveOver_of_weberIn _ _ _ _ (requiredLevel_pos B.toPre)).1
    hr (hfield _ hp.2.2.1)

#print axioms production_parTie


-- A change of G can preserve the entire tie while making prov impossible.
theorem production_tie_without_family (slots : Slots) (hRx : slots.Rx = RX) :
    StepW Pinned (fun K _ _ _ w => ∀ (Z : w.Lt) (l : Lv4 slots K w Z),
      ∃ (P : Formalism.L2.Pj.Top (w.D Z)) (h : LawsP P), P.toCore = l.what₂.r.z.core.toCore ∧
        (∃ F : SrcFam (ambOf P.Q h.pins.1), F.Pinned P.pb 1 ∧ ParTie P.Q h.pins.1 F) ∧
        ∀ (Q : KitClass (w.D Z)) c, ¬ Nonempty (FamOver Q P h c)) := by
  apply (production_parTie slots hRx).trans (StepW.of_all ?_)
  intro K B f T w _ _ rows Z l
  obtain ⟨P, hP, e, noFam⟩ := GeometryAudit.Replacement.lawful_top_without_family hRx l
  refine ⟨P, hP, e, (tied_source_iff_curve (w.st Z) P hP).mpr ?_, noFam⟩
  let C (J : Core (w.D Z)) := GlobalTheory.CompRat.CurveOver J.Q.H (fieldLL (w.D Z)) (extendedLevel (w.D Z))
  exact (congrArg C e).mpr ((rh_rows_tied_iff hRx l).mp (rows Z l))

#print axioms production_tie_without_family
end GeometryAudit.Production
