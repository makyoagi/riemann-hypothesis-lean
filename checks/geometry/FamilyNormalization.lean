import RealizedHeight

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions
open GlobalTheory.EX.OB UpperTheory.Top

namespace GeometryAudit.FamilyNormalization

noncomputable section

variable {ε : ℝ} (F : FamP ε)

private abbrev N (x : ℝ) (i : F.Ix x) := fun u => ((F.D x i).div.Nu u).L

private abbrev H (k x : ℝ) (i : F.Ix x) := hExpl6 (F.D x i) (F.L x i) (F.X x i) k

private abbrev newCore (k : ℝ) : FamCore ε where
  x1 := F.x1
  one_lt_family_threshold := F.one_lt_family_threshold
  Ix := F.Ix
  Win := F.Win
  Win_unb := F.Win_unb
  Ix_win := F.Ix_win
  Ix_zero := F.Ix_zero
  D := fun x i => setDiv (F.D x i) (N F x i) (H F k x i)
  L := fun x i => ledTr (N F x i) (H F k x i) (F.L x i)
  L_x := F.L_x
  L_eps := F.L_eps
  J := F.J
  L_J := F.L_J
  R_eq := F.R_eq
  TTn := F.TTn
  TT_eq := F.TT_eq
  realisedChain_torus_eq := F.realisedChain_torus_eq
  q_eq := F.q_eq
  d_eq := F.d_eq
  QS_eq := F.QS_eq
  art_eq := F.art_eq
  rd_eq := F.rd_eq
  Co := F.Co
  o_le_Co := F.o_le_Co
  QS_le_Co := F.QS_le_Co
  g_eq := F.g_eq
  pde_eq := F.pde_eq
  W := F.W
  eW := F.eW
  eW_code := F.eW_code
  CGam := F.CGam
  CGam_eq := F.CGam_eq
  Cc := F.Cc
  Cc_eq := F.Cc_eq
  Ct := F.Ct
  Ct_eq := F.Ct_eq
  CT2 := F.CT2
  secondConstant_eq := F.secondConstant_eq
  bTop := F.bTop
  bTop_eq := F.bTop_eq
  bTop_ge := F.bTop_ge
  bT_le := F.bT_le
  coverS := F.coverS

/-- Reinstall the formula with one size constant for the whole family.
    The transport also recomputes the frame allowance in the divisor record. -/
def withSize (k : ℝ) : FamP ε where
  toFamCore := newCore F k
  params := fun x hx i => { F.params x hx i with }
  PK := F.PK
  params_K := F.params_K
  parT := fun x hx i => { F.parT x hx i with }
  PT := F.PT
  parT_K := F.parT_K
  CTu := F.CTu
  sizes := F.sizes
  ties := fun x i => { F.ties x i with }
  gatT := fun x i => gatTr (N F x i) (H F k x i) (F.gatT x i)
  X := fun x i => divTr (N F x i) (H F k x i) (F.X x i)
  Gx := fun x i => instTr (N F x i) (H F k x i) (F.Gx x i)
  Gy := fun x i => latTr (N F x i) (H F k x i) (F.Gy x i)
  GK := F.GK
  GK_nonneg := F.GK_nonneg
  supp_sat := F.supp_sat
  tw_supp := F.tw_supp
  fills := fun x hx i w => fills_tr (N F x i) (H F k x i) (F.Gx x i) F.GK w (F.fills x hx i w)
  lats0 := fun x hx i w u hv ne => F.lats0 x hx i w u (by rw [← VV_tr (N F x i) (H F k x i)]; exact hv) ne
  latTied := F.latTied
  Csz := k
  nuDef := F.nuDef
  nprimeDef := F.nprimeDef
  rrDef := F.rrDef
  h_eq := fun _ _ _ _ => rfl
  cX := F.cX
  ex := fun x hx i => extraTr (N F x i) (H F k x i) (F.ex x hx i)
  rho_le := F.rho_le
  Cr := F.Cr
  one_le_Cr := F.one_le_Cr
  drop_iff := F.drop_iff
  fixed := F.fixed
  eta_eq := F.eta_eq
  Sc_shared := F.Sc_shared
  hP_eq := F.hP_eq
  bs_eq := F.bs_eq
  off_eq := F.off_eq
  kapI_eq := F.kapI_eq
  ep_eq := F.ep_eq

theorem same_character_class (k : ℝ) (G : UpperTheory.Top.FReq) (la : ℝ) :
    G.cls la (withSize F k) ↔ G.cls la F := Iff.rfl

theorem same_component (k x : ℝ) (i : F.Ix x) (j : ℕ) (c : (F.X x i).Comp j) :
    ProductionHeight.componentHeight ((withSize F k).X x i) j c =
      ProductionHeight.componentHeight (F.X x i) j c := rfl

theorem same_sections (k x : ℝ) (i : F.Ix x) :
    HEq ((withSize F k).X x i).iMj (F.X x i).iMj := HEq.rfl

/-- A complete second family in the same modulus-one character class. Its
    single new size constant works on all rows. Each tested row has its own
    increased error allowance. Every word on that row sees the same shift. -/
theorem realized_two_normalizations :
    ∃ (eps : ℝ) (F : FamP eps) (C CH : ℝ), 0 < eps ∧
      (GChi Formalism.HC.PChar.one).cls (3/2) F ∧
      let F' := withSize F (F.Csz + 1)
      (GChi Formalism.HC.PChar.one).cls (3/2) F' ∧
      ∀ cutoff : ℝ, ∃ (x : ℝ) (i : F.Ix x), cutoff ≤ x ∧ x ∈ F.Win ∧
        LinkDIV_at (F.L x i) C 2 CH ∧ ∃ s : ℝ, 0 < s ∧
          LinkDIV_at (F'.L x i) (C + s) 2 CH ∧
          ∀ u, (F'.D x i).div.h u = (F.D x i).div.h u + s := by
  obtain ⟨eps, F, C, CH, pos, member, rows⟩ := RealizedHeight.realized_control
  refine ⟨eps, F, C, CH, pos, member, (same_character_class F _ _ _).2 member, ?_⟩
  intro cutoff
  obtain ⟨x, i, hx, win, link, formula, _⟩ := rows cutoff
  let D := F.D x i
  let L := F.L x i
  let X := F.X x i
  let k := F.Csz + 1
  let s := hExpl6 D L X k D.u₀ - hExpl6 D L X F.Csz D.u₀
  have posShift : 0 < s := sub_pos.mpr
    (ProductionHeight.formula_strictMono D L X D.u₀ (lt_add_of_pos_right _ zero_lt_one))
  have shifts : hExpl6 D L X k = fun v => D.div.h v + s := by
    funext v
    dsimp only [s]
    linarith only [HeightSqueeze.formula_shift D L X k F.Csz D.u₀ v, formula v]
  refine ⟨x, i, hx, win, link, s, posShift, ?_, congrFun shifts⟩
  change LinkDIV_at (ledTr (N F x i) (hExpl6 D L X k) L) (C + s) 2 CH
  rw [shifts]
  exact HeightShift.link_after_shift L link (by norm_num) s posShift.le

#print axioms same_sections
#print axioms same_component
#print axioms realized_two_normalizations

end
end GeometryAudit.FamilyNormalization
