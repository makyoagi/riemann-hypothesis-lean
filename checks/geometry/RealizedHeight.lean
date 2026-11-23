import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EveryCharacterOfLiteratureOfVWin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VwinOfRow
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.RowSrc
import HeightSqueeze
import HeightShift

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions
open Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory
open Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4
open UpperTheory.Top GlobalTheory.EX

namespace GeometryAudit.RealizedHeight

/-- Keep the divisor link on the family selected in the character argument. -/
private def HasLink (E : FamClass) : Prop :=
  ∃ (eps : ℝ) (F : FamP eps) (CH : ℝ), 0 < eps ∧ E F ∧ LinkDIV F 2 CH

private def SuppliesLink : Prop :=
  ∀ (la : ℝ) (G : FReq), 1 < la → HostExW la G.req →
    (∀ {eps : ℝ} (F : FamP eps), G.cls la F → HypV F.toFamCore) → HasLink (G.cls la)

private theorem select_link (A A' E : FamClass) (ex : DesignExists (WithTw (WithSm A')) 3)
    (sub : ∀ {eps : ℝ} (F : FamP eps), A' F → A F)
    (mem : ∀ {eps : ℝ} (F : FamP eps), A' F → E F)
    (hv : ∀ {eps : ℝ} (F : FamP eps), E F → HypV F.toFamCore)
    (n : Closed (Des A 3) fun F _ => LinkN F)
    (eta : Closed (Des A 3) fun F _ => LinkEta F)
    (rank : Closed (Des A 3) fun F _ => SmallLevelRankEq F)
    (divisor : Closed (Des A 3) fun F CH => TuSize F → DGamSize F → LinkDIVt F 2 CH) : HasLink E := by
  obtain ⟨a, ha, ready⟩ := n.and (divisor.and (eta.and rank))
  obtain ⟨b, hb, families⟩ := ex
  let eps := min a b
  have pos : 0 < eps := lt_min ha hb
  obtain ⟨K, estimates⟩ := ready eps pos (min_le_left _ _)
  obtain ⟨F, CH, hc, _, large, chosen, tu, dg⟩ := families eps pos (min_le_right _ _) K
  have member := mem F hc.1.1
  obtain ⟨hn, hd, he, hr⟩ := estimates F CH
    ⟨⟨⟨sub F hc.1.1, hc.1.2⟩, hc.2⟩, ⟨CH, chosen⟩, tu, dg⟩ large
  exact ⟨eps, F, CH, pos, member, hd tu dg he (divinN_of_hypV F pos (hv F member) hn hr)⟩

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- The bridge inputs and family existence are those used by
    UpperTheory.Top.shape_closed_link_n_of_green. Retain the link they supply. -/
private theorem supplies_of_green : GlobalTheory.GLq.Green →
    GlobalTheory.Fc.TopShapeAlt True True (fun A => Closed A fun F _ => LinkN F) SuppliesLink := by
  intro hGreen 𝒜 cT hEx sel hduty selS selP selDH selC selB hRB hTw hPA hLamP hDivG hDcPtG hTu hn4 hLit hVC hWu hRF hTF c30 hc30 sTy sNG sM sLp sO h30 hInstR selJ jOn hMt rRows aPt0 aPtTw aPer0 aPerTw aP10 aAtG aC2 hServ nR nRest cIc hcI irrC zL tie hU hG la G hla hH hV
  have bRest := _root_.GlobalTheory.Top.link_brest_alt 𝒜 sel selS selP selDH selC selB hRB hPA hDivG hDcPtG rRows tie
  have hCsz : Closed (D3 3 𝒜) fun Fm _ => 0 ≤ Fm.Csz := Formalism.MainNotions.DIV.closed_Csz_ge_fn (D3 3 𝒜) fun _ => 0
  have oneMap : Closed (D3 3 𝒜) fun Fm _ => ∀ hc : D3 3 𝒜 Fm, _root_.Formalism.L2.Top4.EventuallyAlongSelection sel Fm (d3_a hc) ((_root_.Formalism.L2.Top4.SingleMapCondition selB) Fm (d3_a hc)) :=
    Closed.of_class fun Fm _ _ hc => ⟨0, fun x hx h _ i j => (hRB Fm (d3_a hc) x hx h i).oneMap j⟩
  have hA2 := _root_.GlobalTheory.Top.closed_family_admissible_twist_link_alt 𝒜 sel aPt0 aPtTw aPer0 aPerTw aP10 aAtG hServ
  have hC5 := _root_.GlobalTheory.Top.selection_closed_of_wu_decay_alt 𝒜 sel selS selP selDH selC selB hWu hRF selJ jOn rRows
  have hBR : Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, TuSize Fm → DGamSize Fm →
      _root_.Formalism.L2.DIV.DivisionKernelConstantBounds Fm (_root_.Formalism.L2.Top4.RankOfDivisionKernel sel selS selP selDH selC (_root_.Formalism.L2.Top4.kernelChoiceOfSelection selB) (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) hPA Fm hc) 2 CH :=
    (bRest.and ((Closed.of_class fun Fm _ hc => cut_of_stable (hMt Fm (d3_a hc))).and (rRows.and (oneMap.and (hCsz.and (hA2.and (aC2.and hC5))))))).imp
      fun Fm CH _ ⟨r, o, rr, om, cz, a, c, c5⟩ hc hT hD =>
        (r hc hT hD).toRows_alt (fun hN => _root_.GlobalTheory.Top.wire_sel_alt 𝒜 sel selS selP selDH selC selB hTw hPA hDivG hDcPtG Fm hc CH cz hD (rr hc) (om hc) (r hc hT hD).bu hN) o a (complement_two_of_items c) c5
  have hDIV := _root_.Formalism.L2.DIV.closed_linkDIVt_of_closed_bridge_kernel (D3 3 𝒜) 2 (_root_.Formalism.L2.Top4.RankOfDivisionKernel sel selS selP selDH selC (_root_.Formalism.L2.Top4.kernelChoiceOfSelection selB) (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) hPA) hBR
  have hsub : ∀ {eps : ℝ} (Fm : FamP eps), WithTw (WithSm (WithChN fun Fm => 𝒜 Fm ∧ G.cls la Fm)) Fm →
      WithTw (WithSm (WithChN 𝒜)) Fm := fun _ hc => ⟨⟨⟨hc.1.1.1.1, hc.1.1.2⟩, hc.1.2⟩, hc.2⟩
  have hE := _root_.GlobalTheory.Top.designExists_of_tuSize_aux4n_litThin (fun Fm => 𝒜 Fm ∧ G.cls la Fm) cT (fun hM => hEx hM la G hla hH) (fun Fm hc => sel Fm hc.1)
    (fun Fm hc => hduty Fm hc.1) (Pk.Closed.sub hTu hsub) (Pk.Closed.sub hn4 hsub) hLit
  exact select_link (WithChN 𝒜) (WithChN fun Fm => 𝒜 Fm ∧ G.cls la Fm) (G.cls la) hE
    (fun _ hc => ⟨hc.1.1, hc.2⟩) (fun _ hc => hc.1.2) hV nRest
    (_root_.GlobalTheory.Top.closed_linkEta_of_duty 𝒜 sel hduty)
    (_root_.GlobalTheory.Top.link_alt_alt_alt 𝒜 sel selS selP selDH selC selB hPA hLamP hDivG zL) hDIV

open UpperTheory.LiteratureTheorems in
private theorem modulus_one_link : HasLink ((GChi Formalism.HC.PChar.one).cls (3/2)) := by
  let row := UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter
  let literature : OpenLiteratureStatements := ⟨row, UpperTheory.Zero.LLC.recTExists, row⟩
  let P := published_results_eigen literature
  let matching := theta_integrals_agree_and_local_matching_of_literature literature
  have volume := SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt
    (resolution_char_zero_of_literature literature) (principalisation_char_zero_of_literature literature)
    (poincare_lelong_inv_of_literature literature) PositivityTheory.Pf1.HilbertSamuelMoriwaki.hsUse_outright
    PositivityTheory.Pf1.HilbertSamuelMoriwaki.moriwakiBig_outright (fargues_exact_of_literature literature)
    (zarhin_statement literature) (nef_rr_of_literature literature)
    (siegel_toroidal_integral_of_literature literature) (toroidal_for_fan_ks_of_literature literature)
    (semi_abelian_lie_seminegative_of_literature literature) (point_separation_pair_of_literature literature)
    (ar_degree_of_literature literature) (published_results_arithmetic literature)
    (grothendieck_deformation_of_literature literature)
  let localLanglands := local_langlands_gl_recT_exists_of_literature literature
  have hypotheses := UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound
    P (published_results_first literature) matching.1 matching.2 volume localLanglands
    fun c => UpperTheory.N.boundAtTwoThree_linked_of_recT P.nLink
      (GlobalTheory.Mem.Top.Bl.parametersOfDependence localLanglands c)
  obtain ⟨hyps⟩ := hypotheses
  have supplies := GlobalTheory.Fc.forall_goal_of_shape_of_hyps _ _ _ _
    (supplies_of_green (GlobalTheory.GreenBridge.green_of_regular P.greenRegularCharacters)) trivial trivial hyps
  let one := Formalism.HC.PChar.one
  exact supplies (3/2) (GChi one) (by norm_num) (supplyChi one (UpperTheory.One.vwin_of_row row one))
    (hypV_of_cls one _)

/-- On inhabited windows the production height passes. Raising that height
    and the error coefficient by one still passes. Raising the size constant
    alone can instead preserve the formula assignment while failing the bound. -/
theorem realized_control : ∃ (eps : ℝ) (F : FamP eps) (C CH : ℝ),
    0 < eps ∧ (GChi Formalism.HC.PChar.one).cls (3/2) F ∧
    ∀ cutoff : ℝ, ∃ (x : ℝ) (i : F.Ix x), cutoff ≤ x ∧ x ∈ F.Win ∧
      let D := F.D x i
      let L := F.L x i
      let X := F.X x i
      let N := fun v => (D.div.Nu v).L
      let plus := fun v => D.div.h v + 1
      LinkDIV_at L C 2 CH ∧ (∀ v, D.div.h v = hExpl6 D L X F.Csz v) ∧
      (LinkDIV_at (GlobalTheory.EX.OB.ledTr N plus L) (C + 1) 2 CH ∧
       ∀ v, (GlobalTheory.EX.OB.setDiv D N plus).div.h v ≠ hExpl6 D L X F.Csz v) ∧
      ∃ k : ℝ, F.Csz < k ∧
        let h := hExpl6 D L X k
        let D' := GlobalTheory.EX.OB.setDiv D N h
        let L' := GlobalTheory.EX.OB.ledTr N h L
        let X' := GlobalTheory.EX.OB.divTr N h X
        (∀ v, D'.div.h v = hExpl6 D' L' X' k v) ∧
        (∀ v w, D'.div.h v - D'.div.h w = D.div.h v - D.div.h w) ∧
        (L'.MAIN D.u₀ + C * (D'.host.TT.card : ℝ) * L'.sc.a * L'.La +
          C * (D'.R.m : ℝ) * (L'.B0 + L'.Nc) * L'.sc.x ^ (2 * L'.sc.eps)
          < D'.div.RR.muDual + D'.div.h D.u₀ - L'.Fo) ∧
        ¬ Formalism.L2.DIV.WordFacts L' C 2 D.u₀ := by
  obtain ⟨eps, F, CH, pos, member, C, threshold, allRows⟩ := modulus_one_link
  refine ⟨eps, F, C, CH, pos, member, ?_⟩
  intro cutoff
  obtain ⟨x, win, hx⟩ := F.Win_unb (max cutoff (max threshold (F.x1 + 1)))
  have hthr : threshold ≤ x := le_trans ((le_max_left _ _).trans (le_max_right _ _)) hx
  have hfamily : F.x1 < x := by
    have room : F.x1 + 1 ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
    linarith
  obtain ⟨i⟩ := F.Ix_win x win
  let D := F.D x i
  let L := F.L x i
  let X := F.X x i
  have original := F.h_eq x hfamily i
  let rhs := L.MAIN D.u₀ + C * (D.host.TT.card : ℝ) * L.sc.a * L.La +
    C * (D.R.m : ℝ) * (L.B0 + L.Nc) * L.sc.x ^ (2 * L.sc.eps)
  obtain ⟨k, hk, _⟩ := HeightSqueeze.existsUnique_constant D L X D.u₀
    (max (hExpl6 D L X F.Csz D.u₀) (rhs - D.div.RR.muDual + L.Fo) + 1)
  have higher : F.Csz < k := (ProductionHeight.formula_strictMono D L X D.u₀).lt_iff_lt.mp
    (by rw [hk]; exact lt_of_le_of_lt (le_max_left _ _) (lt_add_of_pos_right _ zero_lt_one))
  have fails : rhs < D.div.RR.muDual + hExpl6 D L X k D.u₀ - L.Fo := by
    linarith only [hk, le_max_right (hExpl6 D L X F.Csz D.u₀) (rhs - D.div.RR.muDual + L.Fo)]
  have good := allRows x hthr i
  refine ⟨x, i, (le_max_left _ _).trans hx, win, good, original,
    ⟨HeightShift.link_after_shift L good (by norm_num) 1 zero_le_one, ?_⟩,
    k, higher, fun _ => rfl, ?_, fails, fun facts => (not_le_of_gt fails) facts.2.2⟩
  · intro v
    change D.div.h v + 1 ≠ hExpl6 D L X F.Csz v
    rw [← original v]
    linarith
  · intro v w
    change hExpl6 D L X k v - hExpl6 D L X k w = D.div.h v - D.div.h w
    rw [original v, original w]
    linarith only [HeightSqueeze.formula_shift D L X k F.Csz w v]

#print axioms realized_control
end GeometryAudit.RealizedHeight
