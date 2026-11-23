import Formalism.SharpRestriction.Divisibility.HeightShare
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.Divisibility.AdmissibleRank.LogDiscriminantLeSquareSizeFamily
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate

open NumberField Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions
open Formalism.MainNotions.HeightShare GlobalTheory.EX.OB

namespace GeometryAudit.ProductionHeight

noncomputable section

/-- Normalized arithmetic self-intersection of the specified component, using
    the divisor, Hermitian lattice, and section map supplied by the row. -/
def componentHeight {D : D7} (X : DivX D) (j : ℕ) (c : X.Comp j) : ℝ :=
  let Y := X.Yv j c
  let L := X.Lw j c (kapW D j)
  X.geo.arTop Y (X.geo.ofW Y L (X.MjH j) (X.iMj j c)) /
    (((X.geo.dim Y : ℝ) + 1) * (X.geo.inter Y (fun _ => L) : ℝ))

/-- The component height is an instance of the project's geometric height.
    Its input sections generate the actual row lattice and are regular. -/
theorem component_presentation {D : D7} (X : DivX D) (j : ℕ) (c : X.Comp j) :
    ∃ B : LData X.geo, B.h = componentHeight X j c ∧ B.Y = X.Yv j c ∧
      B.W = X.MjH j ∧ B.W.Good ∧
      Submodule.span (𝓞 D.what₂.LL) (Set.range B.w) = B.W.L ∧
      (∀ x, B.ιW x ∈ X.geo.H0 B.Y B.L) ∧
      (∀ i v, nrm B.W v (B.w i) ≤ B.abelian₂) ∧ 1 ≤ B.abelian₂ := by
  classical
  obtain ⟨n, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (X.MjH_good j).2.1
  let normAt := fun iv : Fin n × NumberField.InfinitePlace D.what₂.LL =>
    nrm (X.MjH j) iv.2 (g iv.1)
  obtain ⟨M, hM⟩ := (Set.finite_range normAt).bddAbove
  let B : LData X.geo := {
    Y := X.Yv j c, bd := X.Ybd j c, L := X.Lw j c (kapW D j),
    W := X.MjH j, ιW := X.iMj j c, n := n, w := g, abelian₂ := max 1 M }
  exact ⟨B, rfl, rfl, rfl, X.MjH_good j, hg, X.iMj_mem j c,
    fun i v => (hM (Set.mem_range_self (i, v))).trans (le_max_right 1 M), le_max_left 1 M⟩

theorem component_height_after_setDiv {D : D7} (X : DivX D)
    (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ)
    (j : ℕ) (c : X.Comp j) :
    componentHeight (divTr N h X) j c = componentHeight X j c := rfl

/-- The independent height attached to a word in the divisor link is the
    height of its linear map between Hermitian lattices. -/
def wordMapHeight (D : D7) (u : D.what₂.Word) : ℝ :=
  Formalism.HN.htMap (D.div.Nu u).b (D.div.Nu u).X D.div.RR.dualB D.div.RR.dualX (D.div.Bk u)

theorem word_map_height_le_formula {eps : ℝ} (F : FamP eps) {x : ℝ} (hx : F.x1 < x)
    (i : F.Ix x) {C Cabs CH : ℝ} (link : LinkDIV_at (F.L x i) C Cabs CH)
    (u : (F.D x i).what₂.Word) (hn : (F.D x i).div.Bk u ≠ 0) :
    wordMapHeight (F.D x i) u ≤ hExpl6 (F.D x i) (F.L x i) (F.X x i) F.Csz u := by
  exact (link.2.2.2.2.2.1 u hn).trans_eq (F.h_eq x hx i u)

/-- At a fixed row, word and divisor, varying the estimate constant changes
    the proposed value strictly. The geometric component data stay fixed. -/
theorem formula_strictMono (D : D7) (L : SizeData₂ D) (X : DivX D) (u : D.what₂.Word) :
    StrictMono (fun C : ℝ => hExpl6 D L X C u) := by
  have hm := D.R.two_le_m
  have hk : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
  have hf : (0 : ℝ) < D.R.f := by
    exact_mod_cast (show 0 < D.R.f by unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega)
  have hN : (0 : ℝ) < D.R.N D.R.m := by
    exact_mod_cast (show 0 < D.R.N D.R.m by unfold Ranks.N; omega)
  have hL : 0 < L.sc.L := Real.rpow_pos_of_pos (zero_lt_one.trans L.sc.one_lt_alt) _
  have hb : 1 ≤ L.sc.b := Real.one_le_exp hL.le
  have ha : 1 < L.sc.a := lt_of_lt_of_le L.sc.one_lt_alt
    (le_mul_of_one_le_right (zero_lt_one.trans L.sc.one_lt_alt).le hb)
  have hrd := DIV.one_le_rdE D
  have hLa : 0 < L.La := Real.log_pos (ha.trans_le (le_mul_of_one_le_right (zero_le_one.trans ha.le) hrd))
  have hg (i : Fin 2) : (1 : ℝ) ≤ D.host.g i := by exact_mod_cast (D.host.g_prime i).one_lt.le
  have hnV : (1 : ℝ) ≤ D.R.nV := by
    exact_mod_cast (show 1 ≤ D.R.nV by unfold Ranks.nV Ranks.r; omega)
  have hp : 0 ≤ Lprime D L :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hb hrd)
        (one_le_mul_of_one_le_of_one_le (hg 0) (hg 1))) hnV)
  intro a b hab
  have hs : SZbP D L a u < SZbP D L b u := by
    have hb' : 0 < L.sc.b' := div_pos (zero_lt_one.trans ha) (Real.exp_pos _)
    have hη := L.etaSz_pos
    have hS := L.Sc_pos
    unfold SZbP
    apply add_lt_add_right
    apply mul_lt_mul_of_pos_right _ hLa
    exact mul_lt_mul_of_pos_right hab (by positivity)
  have hK (j : ℕ) : kernelPlaceMeanBound D L a u j ≤ kernelPlaceMeanBound D L b u j := by
    unfold kernelPlaceMeanBound
    gcongr
  have hlo (j : ℕ) : L6lo D L b j ≤ L6lo D L a j := by
    unfold L6lo
    gcongr
  unfold hExpl6
  apply sub_lt_sub_right
  exact (sub_lt_sub_right (add_lt_add_of_lt_of_le hs (Finset.sum_le_sum fun j _ => hK j)) _).trans_le
    (sub_le_sub_left (Finset.sum_le_sum fun j _ => hlo j) _)

theorem constant_unique_of_height_match {D : D7} (L : SizeData₂ D) (X : DivX D)
    (u : D.what₂.Word) (height : ℝ) {a b : ℝ}
    (ha : hExpl6 D L X a u = height) (hb : hExpl6 D L X b u = height) : a = b :=
  (formula_strictMono D L X u).injective (ha.trans hb.symm)

#print axioms component_presentation
#print axioms component_height_after_setDiv
#print axioms word_map_height_le_formula
#print axioms formula_strictMono
#print axioms constant_unique_of_height_match

end
end GeometryAudit.ProductionHeight
