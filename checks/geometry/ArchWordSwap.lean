import ArchWeightTest
import Formalism.SharpRestriction.Divisibility.HookProducts.AbsPhFSubLeOfLe

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions
open Formalism.MainNotions.DIV.HookProducts.RBCompl3

namespace GeometryAudit.ArchWordSwap

/-- The two words with just their first or their second bit set. -/
def HasPair (D : D7) : Prop := ∃ u v : D.what₂.Word,
  (∀ l, wordBits D u l = decide (l = 0)) ∧ (∀ l, wordBits D v l = decide (l = 1))

private theorem mid (D : D7) (w : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau)
    (l : ℕ) (hl : l < D.R.k - 2) :
    nuRow D w j τ (l + 1) = (((D.hc τ).v ⟨l, by omega⟩ : ℚ) : ℝ) - 1 / 2 -
      (if wordBits D w l then (D.s.Del : ℝ) else 0) + wSz D j τ -
      (((D.R.N (j - 1) : ℝ) + D.R.N j - 1 - 2 * ((l : ℝ) + 1)) / 2) := by
  rw [nuRow_head' D w j τ (l + 1) (by omega), D.s.u_letter w τ l hl, D.hcW_v]
  simp only [wordBits, dif_pos hl]
  split_ifs <;> push_cast <;> ring

private theorem place_comparison (D : D7) (L : SizeData₂ D) (u v : D.what₂.Word)
    (hu : ∀ l, wordBits D u l = decide (l = 0)) (hv : ∀ l, wordBits D v l = decide (l = 1))
    (j : ℕ) (hj : j < D.R.m) (τ : D.what₂.Tau) :
    kerPlace D L u (j+1) τ < kerPlace D L v (j+1) τ ∧
      (∑ r ∈ Finset.range (D.R.N j), nuRow D u (j+1) τ r) =
        ∑ r ∈ Finset.range (D.R.N j), nuRow D v (j+1) τ r := by
  classical
  have hk : 5 ≤ D.R.k := by have := D.R.two_le_m; have := D.R.m_add_three_le_k; omega
  have hn : D.R.k ≤ D.R.N j := Nat.le_add_right _ _
  let a := nuRow D u (j+1) τ
  let b := nuRow D v (j+1) τ
  let d : ℝ := D.s.Del
  have hd : 0 < d := by dsimp only [d]; exact_mod_cast D.s.Del_pos
  have middle (r : ℕ) (hr : r < D.R.k - 2) := mid D u (j+1) τ r hr
  have middle' (r : ℕ) (hr : r < D.R.k - 2) := mid D v (j+1) τ r hr
  have step1 : b 1 = a 1 + d := by
    dsimp only [a, b, d]; rw [middle 0 (by omega), middle' 0 (by omega), hu, hv]; norm_num; ring
  have step2 : a 2 = b 2 + d := by
    dsimp only [a, b, d]; rw [middle 1 (by omega), middle' 1 (by omega), hu, hv]; norm_num; ring
  have gap : a 1 - a 2 = 3 * d - 1 := by
    have h := D.s.cloud_gap u τ 0 (by omega)
    rw [D.hcW_v] at h
    have g := congrArg (fun x : ℚ => (x : ℝ)) h
    push_cast at g
    dsimp only [a, d]; rw [middle 0 (by omega), middle 1 (by omega), hu, hu]; norm_num; linarith only [g]
  have rest (r : ℕ) (h1 : r ≠ 1) (h2 : r ≠ 2) : a r = b r := by
    by_cases interior : 1 ≤ r ∧ r + 1 < D.R.k
    · obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
      have hl : l < D.R.k - 2 := by omega
      dsimp only [a, b]; rw [middle l hl, middle' l hl, hu, hv]
      simp [show l ≠ 0 by omega, show l ≠ 1 by omega]
    · exact nuRow_eq_of_not_mid _ _ _ _ _ _ interior
  obtain ⟨m, hm, em⟩ := nuRow_nat D u j hj τ 1 (by omega)
  obtain ⟨n, hn', en⟩ := nuRow_nat D v j hj τ 1 (by omega)
  change a 1 = m at em
  change b 1 = n at en
  have hmn : m < n := by exact_mod_cast (show (m : ℝ) < n by linarith only [step1, em, en, hd])
  have sep : (m : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt hmn
  have between : a 2 < a 1 := by linarith only [gap, sep, step1, em, en]
  have low : 0 < b 2 := RowWeightLemmas.nuRow_pos D v j hj τ 2 (by omega)
  have low' : 0 < a 2 := by linarith only [step2, low, hd]
  have high : 0 < a 1 := low'.trans between
  have high' : 0 < b 1 := by linarith only [step1, high, hd]
  have convexLo := phF_sub_le low' low
  have convexHi := phF_sub_le high high'
  have strict := mul_lt_mul_of_pos_left (Real.log_lt_log low' between) hd
  have diff : phF (a 1) + phF (a 2) < phF (b 1) + phF (b 2) := by
    rw [show a 2 - b 2 = d by linarith only [step2]] at convexLo
    rw [show a 1 - b 1 = -d by linarith only [step1], neg_mul] at convexHi
    linarith only [convexLo, convexHi, strict]
  let S := Finset.range (D.R.N j)
  have h1 : 1 ∈ S := Finset.mem_range.2 (by omega)
  have h2 : 2 ∈ S.erase 1 := Finset.mem_erase.2 ⟨by decide, Finset.mem_range.2 (by omega)⟩
  have splitSum (f : ℕ → ℝ) : (∑ r ∈ S, f r) = (∑ r ∈ (S.erase 1).erase 2, f r) + f 2 + f 1 := by
    rw [Finset.sum_erase_add _ _ h2, Finset.sum_erase_add _ _ h1]
  have tailEq (f : ℝ → ℝ) : (∑ r ∈ (S.erase 1).erase 2, f (a r)) = ∑ r ∈ (S.erase 1).erase 2, f (b r) :=
    Finset.sum_congr rfl fun r hr => congrArg f (rest r (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).1 (Finset.mem_erase.mp hr).1)
  have totals : (∑ r ∈ S, a r) = ∑ r ∈ S, b r := by
    have tail := tailEq id
    simp only [id_eq] at tail
    rw [splitSum a, splitSum b, tail]; linarith only [step1, step2]
  refine ⟨?_, totals⟩
  change (∑ r ∈ S, phF (a r)) - (∑ r ∈ S, a r) * L.logOm <
    (∑ r ∈ S, phF (b r)) - (∑ r ∈ S, b r) * L.logOm
  rw [totals, sub_lt_sub_iff_right, splitSum _, splitSum _, tailEq phF]
  linarith only [diff]

theorem arch_separated (D : D7) (L : SizeData₂ D) (pair : HasPair D) :
    ∃ u v, ProductionLevelHeight.arch L u < ProductionLevelHeight.arch L v ∧
      ArchWeightTest.totalWeight D u = ArchWeightTest.totalWeight D v := by
  classical
  obtain ⟨u, v, hu, hv⟩ := pair
  have hf : 0 < D.R.f := by unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega
  have : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (D.what₂.card_Tau ▸ hf)
  have hm := D.R.two_le_m
  have firstRow : 1 ∈ SizeData₂.lifts D := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  refine ⟨u, v, Finset.sum_lt_sum_of_nonempty ⟨1, firstRow⟩ ?_, ?_⟩
  · intro j hj
    have bounds := Finset.mem_Icc.mp hj
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun τ _ => (place_comparison D L u v hu hv t (by omega) τ).1)
  · suffices e : (ArchWeightTest.totalWeight D u : ℝ) = (ArchWeightTest.totalWeight D v : ℝ) by exact_mod_cast e
    simp only [ArchWeightTest.totalWeight, Nat.cast_sum, Fintype.sum_sigma, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun τ _ => ?_
    simp only [(ArchWeightTest.weight_spec D _ _).2]
    exact (Fin.sum_univ_eq_sum_range _ _).trans ((place_comparison D L u v hu hv j j.isLt τ).2.trans
      (Fin.sum_univ_eq_sum_range _ _).symm)

#print axioms arch_separated
end GeometryAudit.ArchWordSwap
