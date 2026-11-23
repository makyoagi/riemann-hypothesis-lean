import FormBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspSectionExtendsComponent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentRulBC

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam GlobalTheory.TrueGeo GlobalTheory.Toroidal
open GlobalTheory.AllWt GeometryAudit.FamilyTop GeometryAudit.FormBoundary
open scoped LaurentSeries

namespace GeometryAudit.FormDescent

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
    {F : Type} [Field F] {e : F ≃+* c.F} {σ₀ : c.F →+* ℂ} {r₀ : ℕ}
    {U₀ : Formalism.L2.PjFree.Unf Xo c σ₀ r₀} (Φ : FlagTor Z e U₀)

-- The compactified model detecting boundary vanishing and the uniformisation
-- on which cuspidality is tested may be chosen separately.
private theorem analytic_cusp_of_boundary {r : ℕ} {σ : c.F →+* ℂ} (U : Unf Xo c σ r)
    (hs : GoodEmb c σ) (hu : IsUnf U) (hfE : 1 < Module.finrank ℚ E / 2)
    {ex : Ix Dw → ℤ} (hex : ex none = 0) {g : Rul Xo c} (hg : g ∈ secZ Xo c ex)
    (hvan : ∀ k, (Φ.C k).Y.vanishOn ((Φ.C k).LEx ex) ((Φ.C k).val g) (Φ.C k).Ybd)
    (k : U.Comp) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt (U.X k).Ψ r)
    (hsec : (U.X k).IsSec la (rdU U g k)) : rdU U g k ∈ (U.X k).SS la := by
  refine GlobalTheory.FJZero.mem_SS_of_isModerate _ _ _ hsec (GlobalTheory.CuspFrom.isModerate _ hfE hsec) fun ξ hξ x hx => ?_
  let : Algebra c.F ℂ⸨X⸩ := (GlobalTheory.ArcId.cstL.comp σ).toAlgebra
  have halg : ∀ t : c.F, algebraMap c.F ℂ⸨X⸩ t = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ t)) :=
    fun _ => rfl
  obtain ⟨y, T₀, s, d, hbd, hd, hw⟩ := GlobalTheory.T.exists_laurentArc_degenerating_on_model_convergence
    _ _ _ _ _ _ σ _ (Formalism.L2.PjFree.Unf.ofPj U) halg hs ((Formalism.L2.PjFree.isUnf_ofPj U).2 hu) k ξ hξ x hx _ _ Z
  have hc : (algebraMap (PowerSeries ℂ) ℂ⸨X⸩).comp ((PowerSeries.C (R := ℂ)).comp σ) = algebraMap c.F ℂ⸨X⸩ :=
    RingHom.ext fun t => (halg t).symm
  obtain ⟨v, hv, hvl⟩ := GlobalTheory.T.eigenframe_base_change_local_rings _ _ _ _ _ _ _ _ Z
    (GlobalTheory.T.exists_lieEigenspaceFrame_localRing_baseChange _ _ _ _ _ _ _ _ Z) _ e _ _ _ Φ
    (PowerSeries ℂ) ℂ⸨X⸩ ((PowerSeries.C (R := ℂ)).comp σ) y ex g hc hbd hex hg hvan
  exact GlobalTheory.T.fourierJacobi_constant_term_eq_zero_of_flow_line _ _ _ _ _ ξ x s d T₀
    (fun m => (evR Xo c g y).coeff m) hsec (GlobalTheory.CuspFrom.freqNonneg _ hfE hsec) hξ hx hd
    (fun m hm => by rw [hvl]; exact GlobalTheory.CuspFrom.coeff_eq_zero hv hm)
    fun w hw' => ⟨(hw w hw').1, (hw w hw').2 ex hex _ hg⟩

private theorem key_factor_holomorphic {r : ℕ} {σ : c.F →+* ℂ} (U : Unf Xo c σ r)
    (hs : GoodEmb c σ) (hu : IsUnf U) (hr : 1 ≤ Dw.p + Dw.q) (key : KeySec Xo c)
    {b : Rul Xo c} {z : ℤ} (hb : b ∈ secZ Xo c (fun i => z * keyEx Dw i)) (k : U.Comp) :
    (U.X k).IsSec 0 (rdU U b k) := by
  let G : WTZ E := (fun _ => z, -2 * z)
  have exG : exZ Dw G = fun i => z * keyEx Dw i := by
    funext i; cases i <;> simp [exZ, G, keyEx, mul_comm]
  have wt : modelWt U G k = 0 := by
    funext τ i; simp only [modelWt, G, Pi.zero_apply]; split <;> omega
  have he : Even G.2 := ⟨-z, by dsimp [G]; ring⟩
  rw [← wt]
  apply GlobalTheory.T.isSec_reading_decreasing_integer_exponents _ _ _ _ _ _ _ _ U ⟨key⟩ hs hu hr G he (fun _ _ _ _ _ => le_rfl)
  rwa [exG]

theorem reconstructed_cusp {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
    (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (hfE : 1 < Module.finrank ℚ E / 2)
    (hr : 1 ≤ Dw.p + Dw.q) (key : KeySec Xo c) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hd : Dom a n)
    {g : Rul Xo c} (hg : g ∈ sec Xo c a n)
    (hvan : ∀ k, (Φ.C k).Y.vanishOn ((Φ.C k).LEx (exKey Dw a n))
      ((Φ.C k).val (g * (key.ρ : Rul Xo c) ^ (n / 2))) (Φ.C k).Ybd) : g ∈ cusp Xo c U a n := by
  refine (mem_cusp _ _ _ _ _ _).2 ⟨hg, fun σ hs => holCusp_mem_holSub _ _ fun k => ?_⟩
  let V := U σ
  let u := key.ρ ^ (n / 2)
  have hu := hU σ hs
  have hk := key.pow_mem (n / 2)
  have eup : (u : Rul Xo c) = (key.ρ : Rul Xo c) ^ (n / 2) := Units.val_pow_eq_pow_val _ _
  have hv := key_factor_holomorphic V hs hu hr key hk k
  have hf := hu.2.2.2.2.1 a n hd g hg k
  have htw : (V.X k).IsSec (laU V a n k) (rdU V (g * ↑u) k) := by
    rw [eup, GlobalTheory.CuspAllEmb.rd_mul]
    simpa only [add_zero, Pi.mul_apply] using GlobalTheory.CuspAllEmb.isSec_mul (V.X k) hf hv
  rw [eup] at htw
  have hcu := analytic_cusp_of_boundary Φ V hs hu hfE (FlagCheck.exKey_none a hd.2) (key.mul_pow_mem hg) hvan k _ htw
  rw [← eup] at hcu
  rw [← eup] at hk
  have hki : (↑u⁻¹ : Rul Xo c) ∈ secZ Xo c (fun i => -((n / 2 : ℕ) : ℤ) * keyEx Dw i) := by
    simpa only [neg_mul, Pi.neg_def] using (inv_mem_secZ (u := u) hk)
  have hi := key_factor_holomorphic V hs hu hr key hki k
  have hc := GlobalTheory.CuspAllEmb.ss_mul (V.X k) hfE hcu hi
  rw [add_zero] at hc
  have eq : rdU V (g * ↑u) k * rdU V (↑u⁻¹) k = rdU V g k := by
    change (rdU V (g * ↑u) * rdU V ↑u⁻¹) k = _
    rw [← GlobalTheory.CuspAllEmb.rd_mul, mul_assoc, Units.mul_inv, mul_one]
  rwa [eq] at hc

#print axioms reconstructed_cusp
end GeometryAudit.FormDescent
