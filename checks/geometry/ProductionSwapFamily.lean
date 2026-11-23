import ArchWordSwap
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EveryCharacterOfLiteratureOfVWin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VwinOfRow
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.RowSrc

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top
open GlobalTheory.Mem.Top.Bl GlobalTheory.Fc UpperTheory.Top
open GeometryAudit.ArchWordSwap

namespace GeometryAudit.ProductionSwapFamily

private def pairPt : PtProp := fun D _ _ _ _ _ _ _ _ => HasPair D

/-- A permutation of the binary cube places the two specified words in an
    existing code of the prescribed size. It preserves injectivity and size. -/
private theorem prescribe {M n : ℕ} (hm : 2 ≤ M) (hn : 2 ≤ n)
    (c : Fin M → Fin n → Bool) (hc : Function.Injective c) :
    ∃ e : Fin M → Fin n → Bool, Function.Injective e ∧
      (∃ i, ∀ l, e i l = decide (l.val = 0)) ∧ (∃ i, ∀ l, e i l = decide (l.val = 1)) := by
  classical
  let i : Fin M := ⟨0, by omega⟩
  let j : Fin M := ⟨1, by omega⟩
  let a : Fin n → Bool := fun l => decide (l.val = 0)
  let b : Fin n → Bool := fun l => decide (l.val = 1)
  let f := Equiv.swap (c i) a
  let g := Equiv.swap (f (c j)) b
  have hab : a ≠ b := fun eq => by have := congrFun eq ⟨0, by omega⟩; simp [a, b] at this
  have hi : f (c i) = a := Equiv.swap_apply_left _ _
  have hj : f (c j) ≠ a := hi ▸ fun eq => (by decide : (0 : ℕ) ≠ 1) (congrArg Fin.val (hc (f.injective eq)).symm)
  have ga : g a = a := Equiv.swap_apply_of_ne_of_ne hj.symm hab
  exact ⟨fun x => g (f (c x)), g.injective.comp (f.injective.comp hc),
    ⟨i, congrFun ((congrArg g hi).trans ga)⟩, ⟨j, congrFun (show g (f (c j)) = b from Equiv.swap_apply_left _ _)⟩⟩

private theorem pair_of_from {C : FC} (p : Pt C) {R : Ranks} {H : Host R} {a b : R.A → ℤ}
    {M u0 : ℕ} {c : Fin M → Fin (R.k - 2) → Bool} (h : p.From H a b c u0)
    (left : ∃ i, ∀ l, c i l = decide (l.val = 0)) (right : ∃ i, ∀ l, c i l = decide (l.val = 1)) : HasPair p.D := by
  obtain ⟨e, he⟩ := h.words
  obtain ⟨i, hi⟩ := left
  obtain ⟨j, hj⟩ := right
  have room : 2 ≤ R.k - 2 := by have := R.two_le_m; have := R.m_add_three_le_k; omega
  refine ⟨e.symm i, e.symm j, fun n => ?_, fun n => ?_⟩
  all_goals rw [he, e.apply_symm_apply]; split_ifs with bound
  · exact hi _
  · simp [show n ≠ 0 by omega]
  · exact hj _
  · simp [show n ≠ 1 by omega]

/-- The production kit construction with its injective code chosen to include both words. -/
private theorem kits : ∀ (Q : Par → PtProp) (la : ℝ) (G : FReq), DC.HostWW la G.req → ObjCP (fun κ => DC.withObj (Q κ)) →
    KitCPW la (fun κ => ((withDuty (DC.withObj ((Q κ).and pairPt))).and DC.WallPt).and G.pt) := by
  intro Q la G hHost hObj
  obtain ⟨εH, hεH, hHost⟩ := hHost
  obtain ⟨εO, hεO, hObj⟩ := hObj
  refine ⟨min εH εO, lt_min hεH hεO, fun eps he he0 he1 => ?_⟩
  obtain ⟨CT2, C8, C5, c6, Cb, KW, h8, h5, h6, hb, hHost⟩ := hHost eps he (he0.trans (min_le_left _ _)) he1
  obtain ⟨KO, hObj⟩ := hObj eps C8 C5 c6 Cb he (he0.trans (min_le_right _ _)) he1 h8
  refine ⟨CT2, C8, C5, c6, Cb, KW.sup KO, h8, h5, h6, hb, fun C hC hT hP hL => ?_⟩
  obtain ⟨hLW, hLO⟩ := GlobalTheory.EX.fc_large_of_sup hL
  obtain ⟨c1, hObj⟩ := hObj C hC hP hLO
  obtain ⟨c1', hHost⟩ := hHost C hC hT hP hLW
  refine ⟨max c1 c1', fun cD hcD => ?_⟩
  obtain ⟨c2, hObj⟩ := hObj cD ((le_max_left _ _).trans hcD)
  obtain ⟨c2', hHost⟩ := hHost cD ((le_max_right _ _).trans hcD)
  refine ⟨max c2 c2', fun ch hch => ?_⟩
  obtain ⟨xO, hObj⟩ := hObj ch ((le_max_left _ _).trans hch)
  obtain ⟨xH, S, hHost⟩ := hHost ch ((le_max_right _ _).trans hch)
  have hmid := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hG : 0 ≤ C.CGam := zero_le_one.trans (hmid _ (by simp [FC.cMid]))
  have hF : 0 ≤ C.P.CF := zero_le_one.trans (hmid _ (by simp [FC.cMid]))
  obtain ⟨xC, hCode⟩ := exists_injective_words eps C.CGam C.P.CF he he1 hG hF
  obtain ⟨xq, hq⟩ := small_prime_lt eps C8 he h8
  refine ⟨max (max xH xO) (max xC xq), S, fun s hs hx hmem => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hxH, hxO⟩, hxC, hxq⟩ := hx
  obtain ⟨R, H, q0, a, b, hRV, hHT, hH, hqH, h0, hWin, hW, hGq⟩ := hHost s hs hxH hmem
  obtain ⟨raw, hraw, _⟩ := hCode s R hs hxC hRV
  have bound : 1 ≤ Real.exp (C.CGam * (R.m : ℝ) ^ 5 * R.f * s.L) :=
    Real.one_le_exp (by have : 0 ≤ s.L := Real.rpow_nonneg (zero_lt_one.trans s.one_lt_alt).le _; positivity)
  have hxone := Real.one_le_rpow s.one_lt_alt.le hF
  have atLeast : (2 : ℕ) ≤ ⌈3 * Real.exp (C.CGam * (R.m : ℝ) ^ 5 * R.f * s.L) ^ 2 * s.x ^ C.P.CF⌉₊ := by
    have h2 : (2 : ℝ) ≤ 3 * Real.exp (C.CGam * (R.m : ℝ) ^ 5 * R.f * s.L) ^ 2 * s.x ^ C.P.CF :=
      (by norm_num : (2 : ℝ) ≤ 3 * 1 ^ 2 * 1).trans (by gcongr)
    exact_mod_cast h2.trans (Nat.le_ceil _)
  obtain ⟨c, hc, left, right⟩ := prescribe atLeast (by have := R.m_add_three_le_k; have := R.two_le_m; omega) raw hraw
  have hHT' : H.CT2 = C.CT2 := hHT.trans hT.symm
  have hn : 0 < R.n := R.toFrame.ord_pos
  have hq0 : (q0 : ℝ) < s.X' := by
    have hqp : (0 : ℝ) < H.q := by exact_mod_cast H.hyp.1.pos
    have hdp : (0 : ℝ) < H.d := by exact_mod_cast H.hyp.2.1.pos
    have hn' : (0 : ℝ) < H.QS := by exact_mod_cast H.QS_pos
    exact hq s _ q0 hs hxq (by positivity) hH.1.log_cond_le hH.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1
  choose pt hsc hval har hfrom hcan hhas using
    fun i : Fin R.n => hObj s R H q0 a b _ c i.1 hs hxO hRV hHT' (by show HostGood s C.P.Cpde C5 c6 Cb H q0; rw [hP]; exact hH) hqH hWin rfl hc i.2
  choose eW heW using fun i => (hfrom i).words
  refine ⟨⟨Fin R.n, ⟨⟨0, hn⟩⟩, pt, hsc, hval, har, fun i i' => ?_, _, eW, fun i i' u u' h => ?_, fun i0 u0 hu => ?_⟩,
    fun i => ?_⟩
  · exact GlobalTheory.EX.TieSame.same_of_from C cD ch (pt i) (pt i') R H a b _ c _ _ ((hsc i).trans (hsc i').symm) (hval i) (hval i')
      (hfrom i) (hfrom i') (hcan i) (hcan i')
  · funext l
    rw [heW i u l, heW i' u' l, h]
  · rw [(hfrom i0).1] at hu
    exact ⟨⟨u0, hu⟩, (hfrom ⟨u0, hu⟩).2.2.2.2.2.2.2.2.2.1⟩
  · have added : (pt i).Has (DC.withObj ((Q _).and pairPt)) :=
      ⟨⟨⟨(hhas i).1.1, pair_of_from _ (hfrom i) left right⟩, (hhas i).1.2⟩, (hhas i).2⟩
    have hd := DC.has_withDuty_wall_and_choices (C8 := C8) (c6 := c6) (q0 := q0) (pt i) hC hHT' (by rw [hsc i]; exact hH)
      (by rw [hsc i]; exact hq0) h0 (by rw [hsc i]; exact hW) (hval i) (hfrom i) (hcan i) added
    exact ⟨⟨hd.1, G.at_of_from (hfrom i) (by rw [hsc i]; exact hGq)⟩, hd.2⟩

/-- The certificate is carried by this point's divisor after height assignment. -/
private def geometric (D : D7) (O : Obj D) : Prop := ∃ J, GeoCl productionPredicate D J O.X

private def requested (κ : Par) : PtProp := ptO (fun D O => κ.Pos → geometric D O)

open Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory UpperTheory.LiteratureTheorems
open GlobalTheory GlobalTheory.Fc.S0 GlobalTheory.Mem.LiteralAutomorphy GlobalTheory.Mem.Top.GroupRetwisting

private theorem point_supply : ObjCP (fun κ => DC.withObj (requested κ)) := by
  let row := UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter
  let literature : OpenLiteratureStatements := ⟨row, UpperTheory.Zero.LLC.recTExists, row⟩
  let P := published_results_eigen literature
  let F := published_results_first literature
  let hL := local_langlands_gl_recT_exists_of_literature literature
  obtain ⟨hA, hM⟩ := theta_integrals_agree_and_local_matching_of_literature literature
  let C := P.litN
  have hS := UpperTheory.Lit.functionalsSeparate_of_howeUnram_of_siegelWeil F Hk3.howeUnram_holds P.siegelWeilUnitaryConvergent
  have hRat : S0.RowRat := rowRatW_of_rowTest (T.test_vector_assembly_holds F.siegelSetUnitary F.howeDualityReal
    P.greenCuspidal F C.join C.fe hA hM hS)
  have hFit := BigTop.Fun.Close.fourier_coefficient_fit_of_join_alt F C.join C.fe hA hM hS
    (S0.ontoX_and_lamLow_of_unitaryGroupHypotheses' P).2
  obtain ⟨CF1, hCF1⟩ := evaluation_grid_of_join F.howeDualityReal hM F C.join C.fe hA
    (WeilConv.twisted_weil_representation_convergence F.siegelSetUnitary F) (T.twisted_local_factors_match F.howeDualityReal F hA hM)
    (T.twisted_square_theta_integrals_eq F hA hM) hS
  obtain ⟨CF0, _⟩ := Fc.StageOne.rowFun_at_gridA_alt P.discreteSeriesCover P.harishChandraModules P.cuspRapidDecay
    P.casselmanWallach P.rayClassFieldSt hFit
  obtain ⟨mass, member, extra, large, linkage⟩ := T.large_unramified_exponent_bundles_exist_alt P hRat hL (max CF0 CF1)
    (GridA (max CF0 CF1)) (hCF1 _ (le_max_right _ _))
  obtain ⟨base, first, exportRows, second⟩ := member
  have strengthened := T.secondG_sAnd_of_largeBase _ _ _ extra base (evG_of_ev large) second
  have cert := EvP.mono (q := fun _ K => ∀ β : BPt K, β.Is _ → geometric β.D β.O) (fun κ K _ passes β hb => by
    obtain ⟨b, q, b', _, eqn⟩ := passes β hb 0
    have hq : geometric (q.w.D q.Z) q.O := ⟨_, q.x.ox.geo⟩
    exact (congrArg (fun z : (Σ (D : D7) (O : Obj D), Fc.BundleCondition D O 0) => geometric z.1 z.2.1) eqn).mpr hq) linkage
  have recs := memberTop_final_contextParameters mass (fun D => VolRatioFromSiegelWeil.volumeRatio P.siegelWeilUnitaryConvergent2 D)
    _ _ _ (fun _ => geometric) base first exportRows strengthened cert
  have supply := T.existsObjects_of_admissibleTwistDatum _ EX.normPrimes_and_levelPrime_unconditional.2 recs
  exact supply.imp fun κ p property => ⟨⟨property.1.1.1, property.1.2⟩, property.2⟩

/-- An inhabited full modulus-one family at the size constant chosen by the
    production design. The two prescribed words occur on every in-range row. -/
theorem realized_family : ∃ (eps : ℝ) (F : FamP eps), 0 < eps ∧
    (GChi Formalism.HC.PChar.one).cls (3/2) F ∧
    (∃ κ : Par, Link κ F ∧ F.Csz = κ.C.Csz) ∧
    ∀ x, F.x1 < x → ∀ i : F.Ix x, HasPair (F.D x i) ∧
      ∃ J, GeoCl productionPredicate (F.D x i) J (F.X x i) := by
  let G := GChi Formalism.HC.PChar.one
  have hosts := supplyChi Formalism.HC.PChar.one (UpperTheory.One.vwin_of_row
    UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter Formalism.HC.PChar.one)
  have small := EX.smallPrimeOne_of_primesRel GlobalTheory.Lin.primesRel_holds
  have host := UpperTheory.Top.hostWW _ (3/2) G.req (by norm_num) (hostQ small _ G hosts)
    (objC_true point_supply) T.windowShareRequirementClosedForm_proof
  have design := designS (fun κ => (requested κ).and pairPt) (fun _ y => Formalism.MainNotions.StandardLattice.HarishChandraReduction.cTmin y)
    (3/2) G (by norm_num) minkowski_bound_rat (kits requested _ G host point_supply)
  obtain ⟨eps, pos, all⟩ := design
  obtain ⟨F, _, _, _, member, _⟩ := all eps pos le_rfl ⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩
  obtain ⟨⟨⟨κ, link, belongs⟩, character⟩, _⟩ := member
  refine ⟨eps, F, pos, character, ⟨κ, link, link.csz⟩, fun x hx i => ?_⟩
  have both := DC.classOf_of_cls _ F belongs x hx i
  exact ⟨both.2, both.1 link.pos⟩

#print axioms realized_family
end GeometryAudit.ProductionSwapFamily
