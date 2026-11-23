import FormDescent
import FormReconstruction

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam GlobalTheory.TrueGeo GlobalTheory.Toroidal
open GlobalTheory.AllWt GeometryAudit.FamilyTop GeometryAudit.FormReconstruction
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GeometryAudit.FormSpan

private theorem span_tied {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {m m' : MD H} (tie : m = m')
    {c : Coeff m.1} {c' : Coeff m'.1} (le : c.F ≤ c'.F) {r : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Unf m.2.2 c σ r) (hu : ∀ σ, GoodEmb c σ → IsUnf (U σ))
    (hfE : 1 < Module.finrank ℚ E / 2) (hr : 1 ≤ m'.2.1.p + m'.2.1.q)
    {O : Type} [CommRing O] {β : O →+* c'.F} {Z : Model m'.2.2 c' β} {F : Type} [Field F]
    {e : F ≃+* c'.F} {σ₀ : c'.F →+* ℂ} {r₀ : ℕ} {V₀ : Formalism.L2.PjFree.Unf m'.2.2 c' σ₀ r₀}
    (Φ : FlagTor Z e V₀) (key : KeySec m'.2.2 c') {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hd : Dom a n)
    {g : Rul m'.2.2 c'} (hg : g ∈ sec m'.2.2 c' a n)
    (van : ∀ k, (Φ.C k).Y.vanishOn ((Φ.C k).LEx (exKey m'.2.1 a n))
      ((Φ.C k).val (g * (key.ρ : Rul m'.2.2 c') ^ (n / 2))) (Φ.C k).Ybd) :
    (fun k => (Φ.C k).val (g * (key.ρ : Rul m'.2.2 c') ^ (n / 2))) ∈
      Submodule.span F (Set.range fun (f : cusp m.2.2 c U a n) k =>
        (Φ.C k).val (trRul tie (c := c) (c' := c') le f.1 * (key.ρ : Rul m'.2.2 c') ^ (n / 2))) := by
  subst m'
  have hV σ (hs : GoodEmb c' σ) : IsUnf (unfBC le U σ) :=
    GlobalTheory.OneMapAll.isUnf_unfExt le σ (fun _ => rfl) (hu (σ.comp (incF c c' le)) hs)
  have hc := FormDescent.reconstructed_cusp Φ (unfBC le U) hV hfE hr key hd hg van
  rw [GlobalTheory.CuspFieldChange.cusp_unfBC_eq_span] at hc
  let u := (key.ρ : Rul m.2.2 c') ^ (n / 2)
  let ev (b : Rul m.2.2 c') (k : V₀.Comp) := (Φ.C k).val (b * u)
  let V := Submodule.span F (Set.range fun (f : cusp m.2.2 c U a n) => ev (GlobalTheory.FieldBC.rulBC le f.1))
  change ev g ∈ V
  refine Submodule.span_induction (p := fun b _ => ev b ∈ V) ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨f, hf, rfl⟩
    exact Submodule.subset_span ⟨⟨f, hf⟩, rfl⟩
  · have ez : ev 0 = 0 := by
      funext k
      change (Φ.C k).val (0 * u) = 0
      rw [zero_mul]
      let := (constF e (Φ.C k).Y).toAlgebra
      exact evalAt_zero _ _ (Φ.C k).y0
    rw [ez]; exact V.zero_mem
  · intro b b' _ _ hb hb'
    have ea : ev (b + b') = ev b + ev b' := by
      funext k
      change (Φ.C k).val ((b + b') * u) = (Φ.C k).val (b * u) + (Φ.C k).val (b' * u)
      rw [add_mul]
      exact (FlagCpt.fromTest_and_val_laws _ _ _ _ _ _ _ _ _ _ _ (Φ.C k)).2.2.2.1 _ _
    rw [ea]; exact V.add_mem hb hb'
  · intro t b _ hb
    have es : ev (t • b) = e.symm t • ev b := by
      funext k
      change (Φ.C k).val ((t • b) * u) = e.symm t • (Φ.C k).val (b * u)
      have hm : (t • b) * u = t • (b * u) := by
        funext p y
        exact smul_mul_assoc t (b p y) (u p y)
      rw [hm, (FlagCpt.fromTest_and_val_laws _ _ _ _ _ _ _ _ _ _ _ (Φ.C k)).2.2.2.2, Algebra.smul_def]
      rfl
    rw [es]; exact V.smul_mem _ hb

theorem span_global_cusp {D : D7} {T : Top D} (h : LawsP T) {st : StFams D}
    (R : RowKits T h st) {j : ℕ} (hj : InR D j) (w : WeightFamilies.Wt D j) :
    let d := datW D R.F.κg j
    let s := R.F.at d
    let kit := R.k.at d
    ∀ t : ∀ k : s.Comp, (kit.Φ.C k).Y.Fn,
      (∀ k, let C := kit.Φ.C k
            let Δ := s.Lw R.L kit.Φ k (wtOfN d.N w)
            t k ∈ C.Y.H0 Δ ∧ C.Y.vanishOn Δ (t k) C.Ybd) →
      t ∈ Submodule.span D.what₂.LL (Set.range fun (f : (recB h.toLawsCore).Cusp j w) k =>
        cmpAt h R.tie R.k hj w.n k f.1) := by
  let d := datW D R.F.κg j
  let S := R.F.sig d.N d.j d.two_le d.j_le
  let kit := R.k.at d
  have hp : S.Dw.p = (D.R.sigW j).1 := S.p_eq.trans (datW_j D R.F.κg hj.1 hj.2)
  have hq : S.Dw.q = (D.R.sigW j).2 := by
    have e := S.rank_eq.trans (datW_N D R.F.κg j)
    exact Nat.add_left_cancel ((congrArg (· + S.Dw.q) hp.symm).trans (e.trans (sigW_sum D hj.1 hj.2).symm))
  have hr : 1 ≤ S.Dw.p + S.Dw.q := S.rank_eq.symm ▸ le_trans (by decide : 1 ≤ 2) S.two_le
  dsimp only
  intro t ht
  obtain ⟨g, ⟨hg, hval⟩, _⟩ := unique_untwisted_rule h R hj w t (fun k => (ht k).1)
  have he := (CmDim.cm_dim D (ambOf T.Q h.pins.1)).2.1
  have hv k := (AsmCheck.Lw_wtOfN (R.F.at d) R.L w hp hq kit.Φ k) ▸ (ht k).2
  have span := span_tied (R.tie.same j hj) (c := T.Q.c) (c' := R.F.κg.c) R.tie.le
    (T.U j) (h.unf j hj) (by omega) hr kit.Φ kit.key (dom_wtA w) hg (fun k => (hval k).symm ▸ hv k)
  rw [← funext hval]
  refine Submodule.span_mono ?_ span
  rintro _ ⟨f, rfl⟩
  exact ⟨⟨f.1, (esec_mem_C h hj).mpr f.2⟩, rfl⟩

#print axioms span_global_cusp
end GeometryAudit.FormSpan
