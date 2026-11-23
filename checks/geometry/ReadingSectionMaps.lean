import Mathlib

open Module
open scoped BigOperators
namespace GeometryAudit.ReadingSections
noncomputable section

private theorem independent_preimage {K L U V : Type} [Field K] [Field L]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module L V] {σ : K →+* L}
    (f : U →ₛₗ[σ] V) {n : ℕ} (u : Fin n → U) (h : LinearIndependent L (fun i => f (u i))) :
    LinearIndependent K u := by
  apply Fintype.linearIndependent_iff.2
  intro c hc i
  have eq := congrArg f hc
  simp only [map_sum, map_smulₛₗ, map_zero] at eq
  exact σ.injective ((Fintype.linearIndependent_iff.1 h _ eq i).trans σ.map_zero.symm)

private theorem basis_preimage {K L U V : Type} [Field K] [Field L]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U] [AddCommGroup V] [Module L V]
    {σ : K →+* L} (f : U →ₛₗ[σ] V) {n : ℕ} (b : Basis (Fin n) L V)
    (u : Fin n → U) (hu : ∀ i, f (u i) = b i) (dim : finrank K U ≤ n) :
    ∃ a : Basis (Fin n) K U, ∀ i, a i = u i := by
  have hi : LinearIndependent K u := independent_preimage f u ((funext hu).symm ▸ b.linearIndependent)
  have le := hi.fintype_card_le_finrank
  have h := hi.span_eq_top_of_card_eq_finrank' (by simpa using le_antisymm (by simpa using le) dim)
  exact ⟨Basis.mk hi h.ge, fun i => Basis.mk_apply _ _ i⟩

theorem sections_on_basis {K L U S M V : Type} [Field K] [Field L]
    [AddCommGroup U] [Module L U] [FiniteDimensional L U]
    [AddCommGroup S] [Module K S] [FiniteDimensional K S]
    [AddCommGroup M] [Module ℂ M] [AddCommGroup V] [Module L V]
    (i : K →+* L) (σ : L →+* ℂ) (J : U →ₛₗ[σ] M) (φ : S →ₛₗ[σ.comp i] M) (C : S →ₛₗ[i] V)
    (inj : Function.Injective J) {n : ℕ} (b : Basis (Fin n) ℂ M)
    (u : Fin n → U) (f : Fin n → S) (hu : ∀ k, J (u k) = b k) (hf : ∀ k, φ (f k) = b k)
    (du : finrank L U ≤ n) (df : finrank K S ≤ n)
    (indep : ∀ v : Fin n → S, LinearIndependent K v → LinearIndependent L (C ∘ v)) :
    ∃ I : U →ₗ[L] V, Function.Injective I ∧
      (∀ x, I x ∈ Submodule.span L (Set.range C)) ∧ ∀ x y, J x = φ y → I x = C y := by
  classical
  obtain ⟨bu, hbu⟩ := basis_preimage J b u hu du
  obtain ⟨bf, hbf⟩ := basis_preimage φ b f hf df
  let I := bu.constr L (C ∘ f)
  have Iu k : I (u k) = C (f k) := hbu k ▸ bu.constr_basis L (C ∘ f) k
  have li := indep f ((funext hbf) ▸ bf.linearIndependent)
  refine ⟨I, ?_, ?_, ?_⟩
  · apply (injective_iff_map_eq_zero I).2
    intro x hx
    have e := congrArg I (bu.sum_repr x)
    simp only [map_sum, map_smul, hbu, Iu, hx] at e
    have z := Fintype.linearIndependent_iff.1 li _ e
    rw [← bu.sum_repr x]
    simp [z]
  · intro x
    rw [← bu.sum_repr x, map_sum]
    exact Submodule.sum_mem _ fun k _ => by
      rw [map_smul, hbu, Iu]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨f k, rfl⟩)
  · intro x y eq
    have e : x = ∑ k, i (bf.repr y k) • u k := by
      apply inj
      rw [eq, map_sum]
      conv_lhs => rw [← bf.sum_repr y]
      simp only [map_sum, map_smulₛₗ, hbf, hu, hf, RingHom.comp_apply]
    rw [e, map_sum]
    conv_rhs => rw [← bf.sum_repr y]
    simp only [map_sum, map_smulₛₗ, RingHom.id_apply, hbf, Iu]

theorem sections_of_generators {K L U S M V : Type} [Field K] [Field L]
    [AddCommGroup U] [Module L U] [FiniteDimensional L U]
    [AddCommGroup S] [Module K S] [FiniteDimensional K S]
    [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] [AddCommGroup V] [Module L V]
    (i : K →+* L) (σ : L →+* ℂ) (J : U →ₛₗ[σ] M) (φ : S →ₛₗ[σ.comp i] M) (C : S →ₛₗ[i] V)
    (inj : Function.Injective J) (du : finrank L U ≤ finrank ℂ M)
    (gen : Finset M) (span : Submodule.span ℂ (gen : Set M) = ⊤)
    (ju : ∀ x ∈ gen, x ∈ Set.range J) (pf : ∀ x ∈ gen, x ∈ Set.range φ)
    (ifm : ∀ {n : ℕ} (v : Fin n → S), LinearIndependent K v → LinearIndependent ℂ (φ ∘ v))
    (ics : ∀ {n : ℕ} (v : Fin n → S), LinearIndependent K v → LinearIndependent L (C ∘ v)) :
    ∃ I : U →ₗ[L] V, Function.Injective I ∧
      (∀ x, I x ∈ Submodule.span L (Set.range C)) ∧ ∀ x y, J x = φ y → I x = C y := by
  classical
  obtain ⟨t, ht, hspan, hi⟩ := exists_linearIndependent ℂ (gen : Set M)
  have top : ⊤ ≤ Submodule.span ℂ (Set.range (Subtype.val : t → M)) := by
    rw [Subtype.range_coe, hspan, span]
  let b := Basis.mk hi top
  letI : Finite t := Module.Finite.finite_basis b
  letI : Fintype t := Fintype.ofFinite t
  let e : t ≃ Fin (Fintype.card t) := Fintype.equivFin t
  let a := b.reindex e
  have inGen (k) : a k ∈ gen := by
    have hb : (e.symm k).val ∈ gen := Finset.mem_coe.mp (ht (e.symm k).property)
    rw [show a k = b (e.symm k) from Basis.reindex_apply _ _ _, show b (e.symm k) = (e.symm k).val from Basis.mk_apply _ _ _]
    exact hb
  have card := Module.finrank_eq_card_basis b
  have df := (ifm (Module.finBasis K S) (Module.finBasis K S).linearIndependent).fintype_card_le_finrank
  exact sections_on_basis i σ J φ C inj a (fun k => (ju _ (inGen k)).choose) (fun k => (pf _ (inGen k)).choose)
    (fun k => (ju _ (inGen k)).choose_spec) (fun k => (pf _ (inGen k)).choose_spec)
    (du.trans_eq card) (by simpa only [Fintype.card_fin, ← card] using df) ics

end
#print axioms sections_on_basis
#print axioms sections_of_generators
end GeometryAudit.ReadingSections
