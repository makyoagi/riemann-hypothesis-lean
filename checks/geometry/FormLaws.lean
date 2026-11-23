import Formalism.LocalToGlobal.ProjectiveLattices.ESecPfA
import FlagEvaluation
import FormReconstruction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentRulBC

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam GlobalTheory.TrueGeo GlobalTheory.Toroidal
open GeometryAudit.FamilyTop GeometryAudit.FormComparison GeometryAudit.FormReconstruction
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GeometryAudit.FormLaws

private theorem after_extension {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {m m' : MD H} (tie : m = m')
    {c : Coeff m.1} {c' : Coeff m'.1} (le : c.F ≤ c'.F) {a : (E →+* ℂ) × ℕ → ℕ} {n q : ℕ}
    (v : Fin q → Rul m.2.2 c) (hv : ∀ i, v i ∈ sec m.2.2 c a n) (hi : LinearIndependent c.F v) :
    LinearIndependent c'.F (fun i => trRul tie (c := c) (c' := c') le (v i)) ∧
    ∀ i, trRul tie (c := c) (c' := c') le (v i) ∈ sec m'.2.2 c' a n := by
  subst m'
  refine ⟨GlobalTheory.CuspFieldChange.linearIndependent_rulBC le hv hi, fun i => ?_⟩
  have hs := hv i
  rw [← GlobalTheory.AllWt.secZ_nat] at hs ⊢
  exact GlobalTheory.SlopeDesc.rulBC_mem_secZ le hs

private theorem independent_of_evaluation {K F : Type} [Field K] [Field F] (e : F ≃+* K)
    {B : Type} [AddCommGroup B] [Module K B] {ι : Type} {A : ι → Type}
    [∀ k, AddCommGroup (A k)] [∀ k, Module F (A k)] (W : Submodule K B) (L : ∀ k, B →+ A k)
    (scalar : ∀ k (t : F) b, L k (e t • b) = t • L k b)
    (zero_detect : ∀ b ∈ W, (∀ k, L k b = 0) → b = 0)
    {q : ℕ} (v : Fin q → B) (mem : ∀ i, v i ∈ W) (hi : LinearIndependent K v) :
    LinearIndependent F (fun i k => L k (v i)) := by
  rw [Fintype.linearIndependent_iff] at hi ⊢
  intro z hz i
  let b := ∑ i, e (z i) • v i
  have hb : b ∈ W := W.sum_mem fun i _ => W.smul_mem _ (mem i)
  have he : b = 0 := zero_detect b hb fun k => by
    change L k (∑ i, e (z i) • v i) = 0
    rw [map_sum]
    simp only [scalar]
    simpa only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] using congrFun hz k
  exact e.injective ((hi (fun i => e (z i)) he i).trans e.map_zero.symm)

private abbrev independentValues {K : Type} [Field K] {ι : Type} (Y : ι → GlobalTheory.ProjVar.Var K)
    {q : ℕ} (v : Fin q → ∀ k, (Y k).Fn) : Prop := LinearIndependent K v

private theorem independent_tied {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {m m' : MD H} (t : m = m')
    {c : Coeff m.1} {c' : Coeff m'.1} (le : c.F ≤ c'.F)
    {O : Type} [CommRing O] {β : O →+* c'.F} {Z : Model m'.2.2 c' β} {F : Type} [Field F]
    {e : F ≃+* c'.F} {σ₀ : c'.F →+* ℂ} {r : ℕ} {V : Formalism.L2.PjFree.Unf m'.2.2 c' σ₀ r}
    (Φ : FlagTor Z e V) (key : KeySec m'.2.2 c') {a : (E →+* ℂ) × ℕ → ℕ} {n q : ℕ}
    (v : Fin q → Rul m.2.2 c) (hv : ∀ i, v i ∈ sec m.2.2 c a n) (hi : LinearIndependent c.F v)
    (detect : ∀ b ∈ sec m'.2.2 c' a n,
      (∀ k, (Φ.C k).val (b * key.ρ.val ^ (n / 2)) = 0) → b = 0) :
    independentValues (fun k => (Φ.C k).Y) (fun i k =>
      (Φ.C k).val (trRul t (c := c) (c' := c') le (v i) * key.ρ.val ^ (n / 2))) := by
  obtain ⟨hb, hs⟩ := after_extension t le v hv hi (c' := c')
  let u := key.ρ.val ^ (n / 2)
  let L (k : V.Comp) := evaluateAdd (m := m') (Φ.C k) u
  refine independent_of_evaluation e (sec m'.2.2 c' a n) L ?_ detect _ hs hb
  intro k x f
  exact (evaluate_smul (m := m') (Φ.C k) u f (e x)).trans
    (congrArg (fun a : F => a • L k f) (e.symm_apply_apply x))

private abbrev subIndependent {K B : Type} [Field K] [AddCommGroup B] [Module K B]
    (W : Submodule K B) {q : ℕ} (v : Fin q → W) : Prop := LinearIndependent K v

private theorem independent_coe {K B : Type} [Field K] [AddCommGroup B] [Module K B]
    (W : Submodule K B) {q : ℕ} (v : Fin q → W) (hv : subIndependent W v) :
    LinearIndependent K (fun i => (v i).1) := hv.map' W.subtype (Submodule.ker_subtype W)

variable {D : D7} {T : Top D} (h : LawsP T) {st : StFams D} (R : RowKits T h st)
    {j : ℕ} (hj : InR D j)

private theorem eval_zero {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {m : MD H} {c : Coeff m.1}
    {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model m.2.2 c β}
    {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Z e) (key : KeySec m.2.2 c) (n : ℕ) :
    C.val (0 * key.ρ.val ^ (n / 2)) = 0 := (evaluateAdd (m := m) C _).map_zero

include hj in
private theorem zero_detected (w : WeightFamilies.Wt D j) :
    let d := datW D R.F.κg j
    let s := R.F.at d
    let kit := R.k.at d
    ∀ g ∈ sec s.Xo d.κ.c (wtA w) w.n,
      (∀ k, (kit.Φ.C k).val (g * kit.key.ρ.val ^ (w.n / 2)) = 0) → g = 0 := by
  let d := datW D R.F.κg j
  let kit := R.k.at d
  dsimp only
  intro f hf zeros
  obtain ⟨_, _, uniq⟩ := unique_untwisted_rule h R hj w (fun _ => 0) (fun k => Submodule.zero_mem _)
  refine (uniq f ⟨hf, zeros⟩).trans (uniq 0 ⟨Submodule.zero_mem _, fun k => ?_⟩).symm
  let m : MD T.Q.H := ⟨d.κ.l, (R.F.sig d.N d.j d.two_le d.j_le).Dw, (R.F.at d).Xo⟩
  exact eval_zero (m := m) (kit.Φ.C k) kit.key w.n

theorem independent_comparison (w : WeightFamilies.Wt D j) {q : ℕ}
    (v : Fin q → cutR T.C j w) (hi : subIndependent (cutR T.C j w) v) :
    independentValues (fun k => ((R.k.at (datW D R.F.κg j)).Φ.C k).Y) (fun i k => cmpAt h R.tie R.k hj w.n k (v i).1) := by
  have hv (i : Fin q) : (v i).1 ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n :=
    (cusp_le_sec _ _ _ _ _) ((esec_mem_C h hj).mp (v i).2)
  have hlin := independent_coe (cutR T.C j w) v hi
  let d := datW D R.F.κg j
  let kit := R.k.at d
  exact independent_tied (R.tie.same j hj) (c := T.Q.c) (c' := R.F.κg.c) R.tie.le
    kit.Φ kit.key (fun i => (v i).1) hv hlin (zero_detected h R hj w)

#print axioms independent_comparison
end GeometryAudit.FormLaws
