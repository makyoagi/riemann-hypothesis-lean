import FormBoundary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueRuleOfRegular

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam GlobalTheory.TrueGeo GlobalTheory.Toroidal
open GlobalTheory.AllWt GeometryAudit.FamilyTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GeometryAudit.FormReconstruction

-- Recover the underlying rule over the family's coefficient field before descent.
theorem unique_untwisted_rule {D : D7} {T : Top D} (h : LawsP T) {st : StFams D}
    (R : RowKits T h st) {j : ℕ} (hj : InR D j) (w : WeightFamilies.Wt D j) :
    let d := datW D R.F.κg j
    let s := R.F.at d
    let kit := R.k.at d
    ∀ t : ∀ k : s.Comp, (kit.Φ.C k).Y.Fn,
      (∀ k, t k ∈ (kit.Φ.C k).Y.H0 (s.Lw R.L kit.Φ k (wtOfN d.N w))) →
      ∃! g : Rul s.Xo d.κ.c, g ∈ sec s.Xo d.κ.c (wtA w) w.n ∧
        ∀ k, (kit.Φ.C k).val (g * (kit.key.ρ : Rul s.Xo d.κ.c) ^ (w.n / 2)) = t k := by
  let d := datW D R.F.κg j
  let S := R.F.sig d.N d.j d.two_le d.j_le
  let kit := R.k.at d
  have hp : S.Dw.p = (D.R.sigW j).1 := S.p_eq.trans (datW_j D R.F.κg hj.1 hj.2)
  have hq : S.Dw.q = (D.R.sigW j).2 := by
    have e := S.rank_eq.trans (datW_N D R.F.κg j)
    exact Nat.add_left_cancel ((congrArg (· + S.Dw.q) hp.symm).trans (e.trans (sigW_sum D hj.1 hj.2).symm))
  dsimp only
  intro t ht
  have reg k := (AsmCheck.Lw_wtOfN (R.F.at d) R.L w hp hq kit.Φ k) ▸ ht k
  obtain ⟨v, ⟨hv, hvk⟩, unique⟩ := existsUnique_rule_of_regular _ _ _ _ _ _ _ _ _ _ _ _ _ _ kit.Φ _
    (FlagCheck.exKey_none (wtA w) w.n_even) t (fun k y _ =>
      GlobalTheory.ProjVar.Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 (reg k) y)
  let u := kit.key.ρ ^ (w.n / 2)
  have eup : (u : Rul (R.F.at d).Xo d.κ.c) = (kit.key.ρ : Rul (R.F.at d).Xo d.κ.c) ^ (w.n / 2) :=
    Units.val_pow_eq_pow_val _ _
  have hu := kit.key.pow_mem (w.n / 2)
  rw [← eup] at hu
  have hi := mul_mem_secZ hv (inv_mem_secZ hu)
  have ex : exKey S.Dw (wtA w) w.n + -(fun i => ((w.n / 2 : ℕ) : ℤ) * keyEx S.Dw i) =
      fun i => (Formalism.L2.Pj.ex S.Dw (wtA w) w.n i : ℤ) := by
    funext i
    simp [exKey]
  rw [ex, secZ_nat] at hi
  refine ⟨v * (↑u⁻¹ : Rul (R.F.at d).Xo d.κ.c), ⟨hi, fun k => ?_⟩, fun g hg => ?_⟩
  · rw [← eup, mul_assoc, Units.inv_mul, mul_one]
    exact hvk k
  · have eqv := unique _ ⟨kit.key.mul_pow_mem hg.1, hg.2⟩
    rw [← eup] at eqv
    rw [← eqv, mul_assoc, Units.mul_inv, mul_one]

#print axioms unique_untwisted_rule
end GeometryAudit.FormReconstruction
