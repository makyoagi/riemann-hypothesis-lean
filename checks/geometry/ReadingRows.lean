import ReadingSectionMaps
import FamilySections

open Module NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Geo
open GlobalTheory.ShFam GlobalTheory.TrueGeo
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GeometryAudit.ReadingSections
noncomputable section
open Classical

variable {D : D7} {G : DV.Geo D.what₂.LL} {N : ℕ → ℕ} {I : ℕ → Type} [∀ j, Fintype (I j)]
    {alg : ∀ j, AlgPkg G D.what₂.Tau (N j) (I j)} {Y : ℕ → ℕ → Type}

private abbrev Section (X : DivX D) (j : ℕ) (a : AlgPkg G D.what₂.Tau (N j) (I j)) :=
  ∀ c, (X.MjH j).V →ₗ[D.what₂.LL] G.Fn (a.Yv c)

private theorem row_maps (P : FormsPkg D G N I alg Y) (X : DivX D) (j : ℕ) (hj : Formalism.L2.Pj.InR D j)
    (w : WeightFamilies.Wt D j) (s : Submodule P.KO (P.Cusp j w)) (φ : s →ₛₗ[P.sig0] D.what₂.Mj j)
    (ifm : ∀ {n : ℕ} (v : Fin n → s), LinearIndependent P.KO v → LinearIndependent ℂ (φ ∘ v))
    (cover : (D.what₂.MjLat j).carrier ⊆ Set.range φ) :
    ∃ ι : Section X j (alg j),
      (∀ c x, ι c x ∈ G.H0 ((alg j).Yv c) ((alg j).Lw c (wtOfN (N j) w))) ∧
      (∀ x, (∀ c, ι c x = 0) → x = 0) ∧ ∀ (f : s) x, X.jM j x = φ f → ∀ c, ι c x = P.cmp j w c f := by
  let V := ∀ c, G.Fn ((alg j).Yv c)
  let C : s →ₛₗ[P.kL] V := {
    toFun := fun f c => P.cmp j w c f.val
    map_add' := fun f g => funext fun c => (P.cmp j w c).map_add f.val g.val
    map_smul' := fun a f => funext fun c => (P.cmp j w c).map_smulₛₗ a f.val }
  letI : FiniteDimensional D.what₂.LL (X.MjH j).V := Module.Finite.of_basis (X.MjH j).b
  have du : finrank D.what₂.LL (X.MjH j).V ≤ finrank ℂ (D.what₂.Mj j) :=
    (finrank_eq_card_basis (X.MjH j).b).le.trans (X.jM_basis j).1.fintype_card_le_finrank
  have ic {n : ℕ} (v : Fin n → s) (h : LinearIndependent P.KO v) : LinearIndependent D.what₂.LL (C ∘ v) :=
    P.cmp_indep j w (s.subtype ∘ v) (h.map' s.subtype (Submodule.ker_subtype s))
  obtain ⟨L, inj, sp, agree⟩ := sections_of_generators P.kL D.what₂.embLL (X.jM j) φ C
    (Idx.jM_inj X j) du (D.what₂.MjLat j).gen (D.what₂.MjLat j).span_top
    (X.MjLat_sub j hj.1 hj.2) (fun _ hv => cover (Formalism.L2.G.ServJoint.gen_mem_carrier _ hv)) ifm ic
  refine ⟨fun c => (LinearMap.proj c).comp L, ?_, ?_, fun f x hx c => congrFun (agree x f hx) c⟩
  · intro c x
    let U := (G.H0 ((alg j).Yv c) ((alg j).Lw c (wtOfN (N j) w))).comap
      (LinearMap.proj c : V →ₗ[D.what₂.LL] G.Fn ((alg j).Yv c))
    have le : Submodule.span D.what₂.LL (Set.range C) ≤ U := Submodule.span_le.2 (by
      rintro _ ⟨f, rfl⟩
      exact P.cmp_mem j w c f)
    exact le (sp x)
  · intro x hx
    apply inj
    exact (funext hx).trans L.map_zero.symm

private def ReadRow (P : FormsPkg D G N I alg Y) (X : DivX D) (j : ℕ) (ι : Section X j (alg j)) : Prop :=
  (∀ x, (∀ c, ι c x = 0) → x = 0) ∧
    ∃ (w : WeightFamilies.Wt D j) (s : Submodule P.KO (P.Cusp j w)) (φ : s →ₛₗ[P.sig0] D.what₂.Mj j),
      w.n = D.R.nV ∧ wtOf w = DV.kapW D j ∧ Submodule.span ℂ (Set.range φ) = ⊤ ∧
      (D.what₂.MjLat j).carrier ⊆ Set.range φ ∧
      (∀ x : s, x.val ∈ P.Mlat j w ↔ φ x ∈ (D.what₂.MjLat j).carrier) ∧
      (∃ vol : ℝ, ∀ x : s, ‖φ x‖ = Real.sqrt (vol * dimKap D j) * P.l2NormAlt j w P.sig0 x) ∧
      ∀ (f : s) x, X.jM j x = φ f → ∀ c, ι c x = P.cmp j w c f

private theorem exists_at_row (P : FormsPkg D G N I alg Y) (X : DivX D) (j : ℕ) (hN : N j = D.R.r)
    (sat : Formalism.L2.Pj.InR D j → ∃ vol, P.MjSat j vol) :
    ∃ ι : Section X j (alg j),
      (∀ c x, ι c x ∈ G.H0 ((alg j).Yv c) ((alg j).Lw c (fun τ k => DV.kapW D j τ (Fin.cast hN k)))) ∧
      (Formalism.L2.Pj.InR D j → ReadRow P X j ι) := by
  by_cases hj : Formalism.L2.Pj.InR D j
  · obtain ⟨vol, w, hn, hw, s, φ, indep, span, cover, lat, norm⟩ := sat hj
    obtain ⟨ι, reg, inj, cmp⟩ := row_maps P X j hj w s φ indep cover
    have ew : (fun τ k => DV.kapW D j τ (Fin.cast hN k)) = wtOfN (N j) w := by
      funext τ k
      rw [← hw]
      rfl
    exact ⟨ι, fun c x => (congrArg (fun W => ι c x ∈ G.H0 ((alg j).Yv c) ((alg j).Lw c W)) ew).mpr (reg c x),
      fun _ => ⟨inj, w, s, φ, hn, hw, span, cover, lat, ⟨vol, norm⟩, cmp⟩⟩
  · exact ⟨fun _ => 0, fun _ _ => Submodule.zero_mem _, fun h => (hj h).elim⟩

theorem exists_reads {Q : KitClass D} {T : Formalism.L2.Pj.Top D} {h : Formalism.L2.Pj.LawsP T} {n : ℕ}
    (Φ : FamOver Q T h n) (X : DivX D) (sat : ∀ j, Formalism.L2.Pj.InR D j → ∃ vol, Φ.P.MjSat j vol) :
    ∃ (ι : ∀ j (a : (Φ.fam.Uw j).Comp), (X.MjH j).V →ₗ[D.what₂.LL] (geoTrue D.what₂.LL).Fn ((Φ.fam.Uw j).alg.Yv a)),
      (∀ j c x, ι j c x ∈ (geoTrue D.what₂.LL).H0 ((Φ.fam.Uw j).alg.Yv c) ((Φ.fam.Uw j).alg.Lw c
        (fun τ k => DV.kapW D j τ (Fin.cast (datW_N D Φ.F.κg j) k)))) ∧ Φ.Reads X ι := by
  have all j := exists_at_row Φ.P X j (datW_N D Φ.F.κg j) (sat j)
  exact ⟨fun j => (all j).choose, fun j => (all j).choose_spec.1,
    fun j h1 h2 => (all j).choose_spec.2 ⟨h1, h2⟩⟩

end
#print axioms row_maps
#print axioms exists_reads
end GeometryAudit.ReadingSections
