import ArchWordSwap
import Formalism.SharpRestriction.Divisibility.SlopeExcess.ConstRankBaseLePolyFourth
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScalePolynomialQuantitiesComparison
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeCoprimeSmallConductor

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions
open GeometryAudit.ArchWeightTest GeometryAudit.ProductionLevelHeight

namespace GeometryAudit.AssignedWordVariation

/-- On sufficiently large family rows, every level prime exceeds every kernel weight. -/
theorem weights_below_primes {eps : ℝ} (F : FamP eps) (pos : 0 < eps) : ∃ cutoff : ℝ,
    ∀ x ≥ cutoff, ∀ (i : F.Ix x) (u v : (F.D x i).what₂.Word) (ix : Ix (F.D x i)),
      weight (F.D x i) u ix < ((F.D x i).mem v).A.T := by
  let e := max F.Ct 5 + 3
  obtain ⟨x0, growth⟩ := GlobalTheory.scale_poly_comparison eps (e * 5 + 1) 1 pos one_pos
  refine ⟨max x0 (max 11 (F.x1 + 1)), fun x hx i u v ix => ?_⟩
  have room : F.x1 + 1 ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  have hxF : F.x1 < x := by linarith only [room]
  let D := F.D x i
  let L := F.L x i
  have sc : L.sc.x = x := F.L_x x i hxF
  have hx11 : 11 ≤ L.sc.x := by rw [sc]; exact (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have xp := zero_lt_one.trans L.sc.one_lt_alt
  have sizes := F.sizes x hxF i
  have poly := DIV.Proofs.szPol_le_rpow sizes (by linarith only [hx11] : 9 ≤ L.sc.x)
  change DIV.Proofs.szPol L ≤ L.sc.x ^ (max L.Ct 5 + 3) at poly
  rw [show L.Ct = F.Ct from F.Ct_eq x i] at poly
  change DIV.Proofs.szPol L ≤ L.sc.x ^ e at poly
  have hsmall := (growth L.sc (F.L_eps x i) (by rw [sc]; exact (le_max_left _ _).trans hx)).2.2.1
  rw [Real.rpow_one] at hsmall
  have xprime : 1 ≤ L.sc.X' := Real.one_le_exp (Real.rpow_nonneg xp.le _)
  have pnonneg : 0 ≤ DIV.Proofs.szPol L := zero_le_one.trans (DIV.Proofs.HHParts.one_le_szPol L)
  have poly5 : 11 * DIV.Proofs.szPol L ^ 5 ≤ L.sc.b := calc
    11 * DIV.Proofs.szPol L ^ 5 ≤ (L.sc.x ^ e) ^ 5 * L.sc.x := by rw [mul_comm (11 : ℝ)]; gcongr
    _ = L.sc.x ^ (e * 5 + 1) := by
      rw [Real.rpow_add xp (e * 5) 1, Real.rpow_one, Real.rpow_mul xp.le e 5]
      norm_num
    _ ≤ L.sc.x ^ (e * 5 + 1) * L.sc.X' := le_mul_of_one_le_right (Real.rpow_nonneg xp.le _) xprime
    _ ≤ L.sc.b := hsmall
  obtain ⟨hN, _, hK, _, _, _, _, _, hLa, _, hBot, _, _, hEta, _, _, hDel, _, _, _, hG, _⟩ := sizes
  obtain ⟨j, τ, r⟩ := ix
  let ν := nuRow D u (j.val + 1) τ r.val
  have hnu : |ν| ≤ 11 * DIV.Proofs.szPol L ^ 5 * L.sc.b := DIV.Proofs.HHParts.nuRow_abs
    (F.params x hxF i) hN hK hLa hBot hEta hDel u (j.val+1) j.isLt τ r.val (by simp)
  have hb : 1 ≤ L.sc.b := Real.one_le_exp (Real.rpow_nonneg xp.le _)
  have hk : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (show 1 ≤ D.R.k by have := D.R.m_add_three_le_k; omega)
  have bsmall : L.sc.b ≤ (D.R.k : ℝ) * L.sc.b := le_mul_of_one_le_left (by linarith) hk
  have hb2 : L.sc.b * L.sc.b ≤ ((D.R.k : ℝ) * L.sc.b) ^ 8 := calc
    L.sc.b * L.sc.b = L.sc.b ^ 2 := (sq _).symm
    _ ≤ ((D.R.k : ℝ) * L.sc.b) ^ 2 := by gcongr
    _ ≤ _ := pow_le_pow_right₀ (hb.trans bsmall) (by decide)
  have less : ν < ((D.mem v).A.T : ℝ) :=
    ((le_abs_self ν).trans (hnu.trans ((mul_le_mul_of_nonneg_right poly5 (by linarith)).trans
      (hb2.trans (hG 0 0).1)))).trans_lt (by exact_mod_cast GlobalTheory.EX.DC.firstTypePrime_lt_rowPrime D v)
  have val := (weight_spec D u ⟨j, τ, r⟩).2
  change (weight D u ⟨j, τ, r⟩ : ℝ) = ν at val
  exact_mod_cast val.trans_lt less

private theorem prime_avoids (D : D7) (u v : D.what₂.Word) (bound : ∀ ix, weight D u ix < (D.mem v).A.T) :
    ¬ (D.mem v).A.T ∣ weightProduct D u := by
  intro divides
  obtain ⟨ix, _, hit⟩ := ((D.mem v).A.T_prime.prime.dvd_finsetProd_iff _).1 divides
  have := (D.mem v).A.T_prime.dvd_of_dvd_pow hit
  exact (not_le_of_gt (bound ix)) (Nat.le_of_dvd (weight_spec D u ix).1 this)

private theorem multiplicity (D : D7) (L : SizeData₂ D) : ∃ n : ℕ, (n : ℝ) = ∑ t : D.host.TT, (L.aT t : ℝ) := by
  let s := ∑ t : D.host.TT, L.aT t
  have ha : 0 < L.sc.a := mul_pos (zero_lt_one.trans L.sc.one_lt_alt) (Real.exp_pos _)
  have hs : 0 ≤ s := Finset.sum_nonneg fun t _ => by exact_mod_cast ha.le.trans (L.aT_win t).1
  exact ⟨s.toNat, by rw [← Int.cast_natCast, Int.toNat_of_nonneg hs]; simp [s]⟩

/-- The prescribed pair has the same total weight, distinct assigned heights
    and strictly ordered archimedean contributions. -/
theorem assigned_differs_same_weight {eps : ℝ} (F : FamP eps) {x : ℝ} (hx : F.x1 < x) (i : F.Ix x)
    (pair : ArchWordSwap.HasPair (F.D x i))
    (bound : ∀ (u v : (F.D x i).what₂.Word) ix, weight (F.D x i) u ix < ((F.D x i).mem v).A.T) :
    ∃ u v, totalWeight (F.D x i) u = totalWeight (F.D x i) v ∧
      (F.D x i).div.h u ≠ (F.D x i).div.h v ∧ arch (F.L x i) u < arch (F.L x i) v := by
  let D := F.D x i
  let L := F.L x i
  obtain ⟨u, v, strict, same⟩ := ArchWordSwap.arch_separated D L pair
  refine ⟨u, v, same, ?_, strict⟩
  intro ht
  have diff := HeightComparison.formula_difference D L (F.X x i) F.Csz u v
  rw [← F.h_eq x hx i u, ← F.h_eq x hx i v, ht, sub_self] at diff
  simp only [HeightComparison.wordTerm, ← Finset.sum_mul] at diff
  obtain ⟨w, hw⟩ := multiplicity D L
  let p := (D.mem u).A.T
  let q := (D.mem v).A.T
  let a := weightProduct D u
  let b := weightProduct D v
  have pa : 0 < a := Finset.prod_pos fun ix _ => pow_pos (weight_spec D u ix).1 _
  have pb : 0 < b := Finset.prod_pos fun ix _ => pow_pos (weight_spec D v ix).1 _
  have pp : Nat.Prime p := (D.mem u).A.T_prime
  have pq : Nat.Prime q := (D.mem v).A.T_prime
  rw [← hw] at diff
  change 0 = -((w : ℝ) * Real.log (p : ℝ)) + arch L u - (-((w : ℝ) * Real.log (q : ℝ)) + arch L v) at diff
  rw [arch_formula, arch_formula, same] at diff
  have logs : Real.log (a : ℝ) + (w : ℝ) * Real.log (q : ℝ) = Real.log (b : ℝ) + (w : ℝ) * Real.log (p : ℝ) := by
    dsimp only [a, b, p, q]; linarith only [diff]
  have eqNat : a * q ^ w = b * p ^ w := by
    have log_product (n t : ℕ) (hn : 0 < n) (hp : 0 < t) :
        Real.log ((n * t ^ w : ℕ) : ℝ) = Real.log (n : ℝ) + (w : ℝ) * Real.log (t : ℝ) := by
      push_cast; rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    rw [← log_product a q pa pq.pos, ← log_product b p pb pp.pos] at logs
    have eqR := Real.log_injOn_pos (Set.mem_Ioi.mpr (Nat.cast_pos.mpr (Nat.mul_pos pa (pow_pos pq.pos w))))
      (Set.mem_Ioi.mpr (Nat.cast_pos.mpr (Nat.mul_pos pb (pow_pos pp.pos w)))) logs
    exact_mod_cast eqR
  have ne : a ≠ b := fun e => strict.ne ((eq_iff_product D u L v same).2 e)
  by_cases zero : w = 0
  · exact ne (by simpa [zero] using eqNat)
  by_cases eq : p = q
  · rw [eq] at eqNat
    exact ne (Nat.eq_of_mul_eq_mul_right (pow_pos pq.pos _) eqNat)
  have divides : p ∣ a * q ^ w := eqNat ▸ dvd_mul_of_dvd_right (dvd_pow_self p zero) b
  rcases pp.dvd_mul.mp divides with h | h
  · exact prime_avoids D u u (bound u u) h
  · exact eq ((Nat.prime_dvd_prime_iff_eq pp pq).1 (pp.dvd_of_dvd_pow h))

/-- A change of level prime cannot cancel the change of the archimedean sum for
    the prescribed pair. This covers the library's zero-height fallback as well. -/
theorem assigned_differs {eps : ℝ} (F : FamP eps) {x : ℝ} (hx : F.x1 < x) (i : F.Ix x)
    (pair : ArchWordSwap.HasPair (F.D x i))
    (bound : ∀ (u v : (F.D x i).what₂.Word) ix, weight (F.D x i) u ix < ((F.D x i).mem v).A.T) :
    ∃ u v, ((F.D x i).div.h u ≠ (F.D x i).div.h v) ∧ arch (F.L x i) u < arch (F.L x i) v := by
  obtain ⟨u, v, _, distinct, strict⟩ := assigned_differs_same_weight F hx i pair bound
  exact ⟨u, v, distinct, strict⟩

#print axioms weights_below_primes
#print axioms assigned_differs_same_weight
#print axioms assigned_differs
end GeometryAudit.AssignedWordVariation
