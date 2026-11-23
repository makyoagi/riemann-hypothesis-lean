import LocalPointLift
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LatticePeriodFormIndependentOfModels
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDegenerationDataAlgebraicPointModel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEmbeddingCompleteAlgClosedFixedCarrier
import GroundTheory.ArithmeticGeometry.AbelianVarieties.FormalGroupReduction

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj
open Formalism.MainNotions Formalism.MainNotions.DIV.Cons

namespace GeometryAudit.ModelComparison
open GlobalTheory.ModelIndep
noncomputable section

-- A bounded element of the fraction field belongs to a DVR embedded locally
-- in the valued field. This supplies the base map for either integral model.
theorem integral_base {O : Type} [CommRing O] {p : ℕ} (C : SCF p) (T : CDVR)
    (eF : T.Fr →+* ↥C.S) (hlt : ∀ a ∈ maximalIdeal T.V, ‖eF (algebraMap T.V T.Fr a)‖ < 1)
    (f : O →+* T.Fr) (hb : ∀ a, ‖eF (f a)‖ ≤ 1) :
    ∃ b : O →+* T.V, (algebraMap T.V T.Fr).comp b = f := by
  have mem (a : O) : f a ∈ Set.range (algebraMap T.V T.Fr) := by
    by_contra hn
    have hn0 : f a ≠ 0 := fun he => hn ⟨0, by simp [he]⟩
    obtain ⟨t, ht, he⟩ := GroundTheory.Arith.Abelian.exists_inv_mem_of_notMem_range T.Fr hn
    have lt := hlt t ht
    rw [he, map_inv₀, norm_inv] at lt
    exact (not_lt_of_ge (hb a)) ((inv_lt_one₀ (norm_pos_iff.mpr ((map_ne_zero_iff _ eF.injective).2 hn0))).mp lt)
  choose b h using mem
  have inj := IsFractionRing.injective T.V T.Fr
  exact ⟨{ toFun := b, map_zero' := inj (by simp [h]), map_one' := inj (by simp [h]),
           map_add' := fun _ _ => inj (by simp [h]), map_mul' := fun _ _ => inj (by simp [h]) },
    RingHom.ext h⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

-- Adapted from GlobalTheory.ModelIndep.exists_extension: use the integral base map directly.
private theorem extend_model {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    (T : CDVR) (io : c.F →+* T.Fr) (b : O →+* T.V)
    (hb : (algebraMap T.V T.Fr).comp b = io.comp β) (x : Sp T.Fr ⟶ Xo.X)
    (hxs : x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom))
    (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m1 : SABMap t' Xo.univ.t x)
    (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr)))
    {p : ℕ} {C : SCF p} (Pc : PointsOfFlagModel.PtC Y C) (eF : T.Fr →+* ↥C.S) (g : T.V →+* intO ↥C.S)
    (h1' : eF.comp io = Pc.fK) (h2' : Pc.y ≫ pullback.fst _ _ = spMap eF ≫ x)
    (h3' : ∀ a, ((g a : intO ↥C.S) : ↥C.S) = eF (algebraMap T.V T.Fr a)) :
    ∃ yt : Sp T.V ⟶ Y.X, spMap g ≫ yt = Pc.yt ∧ Nonempty (SABMap G Y.t yt) := by
  have hcond : x ≫ Xo.s = spMap io ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [hxs, GlobalTheory.EtaVal.spMap_comp_spMap]
  let z : Sp T.Fr ⟶ Xo.XF c := pullback.lift x (spMap io) hcond
  have hzs : z ≫ pullback.snd _ _ = spMap io := pullback.lift_snd _ _ _
  have hzf : z ≫ pullback.fst _ _ = x := pullback.lift_fst _ _ _
  have hx : z ≫ Y.j ≫ Y.s = Out.jK T.V ≫ spMap b := by
    show z ≫ (Y.jQ ≫ pullback.fst _ _) ≫ Y.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc, hzs]
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hb]
  obtain ⟨yt, h1, h2⟩ := extPt Y T b z hx
  obtain ⟨PP', cub, sym, adj, prim, mP, -⟩ := sabPull Out.CubePf.cubePull yt Y.t
  obtain ⟨mF, -⟩ := sabCancel pullCubCancel E H _ _ _ Xo.univ.t Y.oF.t t' (pullback.fst _ _) z Y.m0.toSABMap
    (PullbackSections.sabMapCast m1 hzf.symm)
  obtain ⟨mJ, -⟩ := sabComp pullCubComp E H _ _ _ Y.t Y.oF.t t' (Y.jQ ≫ pullback.fst _ _) z Y.m mF
  have hj : z ≫ Y.jQ ≫ pullback.fst _ _ = Out.jK T.V ≫ yt := h1.symm
  obtain ⟨mK, -⟩ := sabCancel pullCubCancel E H _ _ _ Y.t _ t' yt (Out.jK T.V) mP (PullbackSections.sabMapCast mJ hj)
  obtain ⟨-, ψ, -⟩ := GlobalTheory.sab_extensions_iso E H Dw l Xo T.V T.Fr x G _ t' t' m1 m2 m1 mK
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ Y.t _ G yt (𝟙 _) mP ψ
  have hprY : IsProper Y.s := projProper O Y.X Y.s Y.proj
  have hr : (intO ↥C.S).subtype.comp g = eF.comp (algebraMap T.V T.Fr) := RingHom.ext h3'
  have hy : Pc.y = spMap eF ≫ z := by
    apply pullback.hom_ext
    · rw [h2', Category.assoc, hzf]
    · rw [Pc.y_over, Category.assoc, hzs, GlobalTheory.EtaVal.spMap_comp_spMap, h1']
  have halg : g.comp b = Pc.alg := by
    refine RingHom.ext fun a => Subtype.ext ?_
    have q1 := DFunLike.congr_fun Pc.compat a
    have q2 := DFunLike.congr_fun hb a
    have q3 := DFunLike.congr_fun h1' (β a)
    simp only [RingHom.comp_apply] at q1 q2 q3 ⊢
    rw [h3', q2, q3]; exact q1.symm
  refine ⟨yt, ?_, ⟨PullbackSections.sabMapCast n (Category.id_comp yt)⟩⟩
  refine GlobalTheory.EtaVal.point_ext_of_injective (intO ↥C.S).subtype Subtype.val_injective Y.s _ _ ?_ ?_
  · rw [Pc.ext, hy, Category.assoc, ← h1, ← Category.assoc, GlobalTheory.EtaVal.spMap_comp_spMap, hr,
      ← GlobalTheory.EtaVal.spMap_comp_spMap, Category.assoc]
  · rw [Pc.yt_over, Category.assoc, h2, GlobalTheory.EtaVal.spMap_comp_spMap, halg]

private theorem compare_uniformisation {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    (T : CDVR) (hT : T.FinRes) (io : c.F →+* T.Fr) (x : Sp T.Fr ⟶ Xo.X)
    (hxs : x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom))
    (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m1 : SABMap t' Xo.univ.t x)
    (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr)))
    (T' : CDVR) (φ : T.V →+* T'.V) (hφ : Function.Injective φ) (hφf : φ.Finite) (G' : SAB H (Sp T'.V))
    (mG : SABMap G' G (spMap φ)) (U : PELUnif (maximalIdeal T'.V) G')
    (hU : ∀ χ, PsiUnitOn U.D.toPre χ (abLocus G'.G)) (hTo : U.TorsionIso)
    {p : ℕ} (hp : p.Prime) {C : SCF p} (Pc : PointsOfFlagModel.PtC Y C) (eF : T.Fr →+* ↥C.S)
    (h1' : eF.comp io = Pc.fK) (hle : ∀ a : T.V, ‖eF (algebraMap T.V T.Fr a)‖ ≤ 1)
    (hlt : ∀ a ∈ maximalIdeal T.V, ‖eF (algebraMap T.V T.Fr a)‖ < 1)
    (h2' : Pc.y ≫ pullback.fst _ _ = spMap eF ≫ x) (A : DatAt Y Pc) :
    ∃ (f : T'.V →+* intO ↥C.S) (q : U.D.toPre.X ≃ₗ[𝓞 E] A.Ylat),
      ∀ a b, A.beta (q a) (q b) = betaAt U.D.toPre ((intO ↥C.S).subtype.comp f) p a b := by
  let g : T.V →+* intO ↥C.S := (eF.comp (algebraMap T.V T.Fr)).codRestrict _ hle
  have hg : Function.Injective g := fun a b h =>
    IsFractionRing.injective T.V T.Fr (eF.injective (congrArg Subtype.val h))
  obtain ⟨b, hb⟩ := integral_base C T eF hlt (io.comp β) fun a => by
    have eq := RingHom.congr_fun Pc.compat a
    have eq' := RingHom.congr_fun h1' (β a)
    change ‖eF (io (β a))‖ ≤ 1
    change eF (io (β a)) = Pc.fK (β a) at eq'
    change ((Pc.alg a : intO ↥C.S) : ↥C.S) = Pc.fK (β a) at eq
    rw [eq', ← eq]
    exact (Pc.alg a).2
  obtain ⟨yt, hyt, ⟨n⟩⟩ := extend_model Y T io b hb x hxs G t' m1 m2 Pc eF g h1' h2' (fun _ => rfl)
  have hpm : (p : T.V) ∈ maximalIdeal T.V := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    have h := norm_unit_eq_one g u
    rw [hu, map_natCast] at h
    have h' : ‖(p : ↥C.S)‖ = 1 := by simpa using h
    rw [C.norm_p] at h'
    exact hp.ne_one (by exact_mod_cast inv_eq_one.1 h')
  obtain ⟨f, hf, -, hfl⟩ := (GlobalTheory.T.exists_embedding_completeAlgClosed_fixedCarrier T p hp hT hpm).2 C g T' φ hg hlt hφ hφf
  obtain ⟨n2, -⟩ := sabComp pullCubComp E H _ _ _ Y.t G G' yt (spMap φ) n mG
  have hab : (spMap φ ≫ yt) ⁻¹' abLocus Y.t.G = abLocus G'.G :=
    Set.ext fun q => abLocus_pullback abLocusOne Y.t.semi n2.cart.1 q
  let A₀ : DatAt Y Pc :=
    { R := T'.V
      noeth := inferInstance
      normal := inferInstance
      complete := inferInstance
      «ι» := spMap φ ≫ yt
      f := f
      f_loc := hfl
      fac := by rw [← Category.assoc, GlobalTheory.EtaVal.spMap_comp_spMap, hf, hyt]
      t := G'
      m := n2
      U := U
      unitOn := fun χ => by rw [hab]; exact hU χ
      tors := hTo }
  obtain ⟨-, q, hq⟩ := GlobalTheory.T.degenerationData_coords_ne_zero_lattices_isomorphic E H Dw l Xo c O β Y p C Pc hp T g yt hT hg hlt hyt A₀ A
  exact ⟨f, q, hq⟩

theorem compare_over_trait {c₂ : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c₂.F}
    (Y : Model Xo c β) (Y' : Model Xo c₂ β') (T : CDVR) (hT : T.FinRes) (io : c.F →+* T.Fr) (io' : c₂.F →+* T.Fr) (x : Sp T.Fr ⟶ Xo.X)
    (hxs : x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom))
    (hxs' : x ≫ Xo.s = spMap (io'.comp (IntermediateField.inclusion c₂.le).toRingHom))
    (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m1 : SABMap t' Xo.univ.t x)
    (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr)))
    {p : ℕ} (hp : p.Prime) {C C' : SCF p} (P : PointsOfFlagModel.PtC Y C) (P' : PointsOfFlagModel.PtC Y' C')
    (eF : T.Fr →+* ↥C.S) (a1 : eF.comp io = P.fK) (a2 : ∀ a : T.V, ‖eF (algebraMap T.V T.Fr a)‖ ≤ 1)
    (a3 : ∀ a ∈ maximalIdeal T.V, ‖eF (algebraMap T.V T.Fr a)‖ < 1)
    (a4 : P.y ≫ pullback.fst _ _ = spMap eF ≫ x)
    (eF' : T.Fr →+* ↥C'.S) (b1 : eF'.comp io' = P'.fK) (b2 : ∀ a : T.V, ‖eF' (algebraMap T.V T.Fr a)‖ ≤ 1)
    (b3 : ∀ a ∈ maximalIdeal T.V, ‖eF' (algebraMap T.V T.Fr a)‖ < 1)
    (b4 : P'.y ≫ pullback.fst _ _ = spMap eF' ≫ x) (A : DatAt Y P) (A' : DatAt Y' P') :
    ∃ f : A.Ylat ≃ₗ[𝓞 E] A'.Ylat, ∀ a b, A'.beta (f a) (f b) = A.beta a b := by
  obtain ⟨T', φ, G', mG, hφ, hφf, -, -, U, hU, hTo⟩ :=
    GlobalTheory.UnifAfterExt.exists_finite_ext_uniformised E H Dw l Xo T G t' m2 x m1 hT
  obtain ⟨f, q, hq⟩ := compare_uniformisation Y T hT io x hxs G t' m1 m2
    T' φ hφ hφf G' mG U hU hTo hp P eF a1 a2 a3 a4 A
  obtain ⟨f', q', hq'⟩ := compare_uniformisation Y' T hT io' x hxs' G t' m1 m2
    T' φ hφ hφf G' mG U hU hTo hp P' eF' b1 b2 b3 b4 A'
  refine ⟨q.symm.trans q', fun a b => ?_⟩
  have h1 := hq (q.symm a) (q.symm b)
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1
  exact (hq' (q.symm a) (q.symm b)).trans ((betaAt_eq_of_dvr hp _ _ f' f _ _ _).trans h1.symm)


private theorem bounded_extension {p : ℕ} (hp : p.Prime) (C : SCF p)
    (T U : CDVR) (φ : T.V →+* U.V) (finite : φ.Finite)
    (e : T.Fr →+* ↥C.S) (e' : U.Fr →+* ↥C.S)
    (ext : ∀ a, e' (algebraMap U.V U.Fr (φ a)) = e (algebraMap T.V T.Fr a))
    (bound : ∀ a : T.V, ‖e (algebraMap T.V T.Fr a)‖ ≤ 1) :
    (∀ a : U.V, ‖e' (algebraMap U.V U.Fr a)‖ ≤ 1) ∧
    ∀ a ∈ maximalIdeal U.V, ‖e' (algebraMap U.V U.Fr a)‖ < 1 := by
  let g := e'.comp (algebraMap U.V U.Fr)
  let : Algebra T.V U.V := φ.toAlgebra
  let : Algebra T.V ↥C.S := (e.comp (algebraMap T.V T.Fr)).toAlgebra
  let k : U.V →ₐ[T.V] ↥C.S := ⟨g, ext⟩
  have hi : Algebra.IsIntegral T.V U.V := ⟨finite.to_isIntegral⟩
  let v := NormedField.valuation (K := ↥C.S)
  let b := (algebraMap T.V ↥C.S).codRestrict v.integer (fun a => by
    rw [Valuation.mem_integer_iff]
    exact_mod_cast bound a)
  let : Algebra T.V v.integer := b.toAlgebra
  have : IsScalarTower T.V v.integer ↥C.S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hb (a : U.V) : ‖g a‖ ≤ 1 := by
    have integral := (Algebra.IsIntegral.isIntegral (R := T.V) a).map k
    have hv := (Valuation.integer.integers v).isIntegral_iff_v_le_one.1 integral.tower_top
    exact_mod_cast hv
  refine ⟨hb, fun _ ha => GlobalTheory.SmallClosedField.norm_lt_one_of_mem_maximalIdeal g hb
    (Nat.cast_ne_zero.2 hp.ne_zero) ?_ ha⟩
  rw [map_natCast, C.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)

private theorem base_at_point {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
    {p : ℕ} {C : SCF p} (P : PointsOfFlagModel.PtC Y C) :
    (P.y ≫ pullback.fst _ _) ≫ Xo.s = spMap (P.fK.comp (IntermediateField.inclusion c.le).toRingHom) := by
  rw [Category.assoc, pullback.condition, ← Category.assoc, P.y_over, GlobalTheory.EtaVal.spMap_comp_spMap]

private theorem pull_group {X Y : Scheme.{0}} (f : X ⟶ Y) (G : SAB H Y) :
    ∃ G' : SAB H X, Nonempty (SABMap G' G f) := by
  obtain ⟨_, _, _, _, _, m, _⟩ := sabPull Out.CubePf.cubePull f G
  exact ⟨_, ⟨m⟩⟩

-- Only the tower coefficient field has to embed in the original trait.
-- The second field is adjoined inside the common valued field of the points.
set_option maxHeartbeats 470000 in
theorem compare_at_point {c₂ : Coeff l} {O O' : Type} [CommRing O] [CommRing O']
    {β : O →+* c.F} {β' : O' →+* c₂.F} (Y : Model Xo c β) (Y' : Model Xo c₂ β')
    {p : ℕ} (hp : p.Prime) {C : SCF p} (P : PointsOfFlagModel.PtC Y C) (P' : PointsOfFlagModel.PtC Y' C)
    (T : CDVR) (hT : T.FinRes) (io : c.F →+* T.Fr) (e : T.Fr →+* ↥C.S)
    (x : Sp T.Fr ⟶ Xo.X) (G : SAB H (Sp T.V)) (t : SAB H (Sp T.Fr)) (mx : SABMap t Xo.univ.t x)
    (mg : SABMap t G (spMap (algebraMap T.V T.Fr))) (ei : e.comp io = P.fK)
    (bound : ∀ a : T.V, ‖e (algebraMap T.V T.Fr a)‖ ≤ 1)
    (ex : P.y ≫ pullback.fst _ _ = spMap e ≫ x)
    (ex' : P'.y ≫ pullback.fst _ _ = spMap e ≫ x) (A : DatAt Y P) (A' : DatAt Y' P') :
    ∃ f : A.Ylat ≃ₗ[𝓞 E] A'.Ylat, ∀ a b, A'.beta (f a) (f b) = A.beta a b := by
  have := c₂.fin
  obtain ⟨U, φ, e', io', inj, finite, hU, ei', ext⟩ :=
    GlobalTheory.DatAtPoint.exists_ext_containing T hT e P'.fK
  obtain ⟨i, _, _, hiV, _, _⟩ := GlobalTheory.EtaVal.finite_extension_ramification_embedding T U φ inj finite
  have hi : i.comp (algebraMap T.V T.Fr) = (algebraMap U.V U.Fr).comp φ := RingHom.ext hiV
  have he : e'.comp i = e := IsFractionRing.ringHom_ext (A := T.V) fun a => by
    change e' (i (algebraMap T.V T.Fr a)) = _
    exact (congrArg e' (hiV a)).trans (ext a)
  have ee : e'.comp (i.comp io) = P.fK := by rw [← RingHom.comp_assoc, he, ei]
  let x' := spMap i ≫ x
  have hxe : spMap e' ≫ x' = spMap e ≫ x := by
    dsimp [x']
    rw [← Category.assoc, GlobalTheory.EtaVal.spMap_comp_spMap, he]
  have base {c₀ : Coeff l} {O₀ : Type} [CommRing O₀] {β₀ : O₀ →+* c₀.F}
      {M : Model Xo c₀ β₀} (P₀ : PointsOfFlagModel.PtC M C) (f : c₀.F →+* U.Fr)
      (ef : e'.comp f = P₀.fK) (hx : P₀.y ≫ pullback.fst _ _ = spMap e ≫ x) :
      x' ≫ Xo.s = spMap (f.comp (IntermediateField.inclusion c₀.le).toRingHom) := by
    apply GlobalTheory.DatAtPoint.eq_of_field_ext e'
    rw [← Category.assoc, hxe, ← hx, base_at_point, GlobalTheory.EtaVal.spMap_comp_spMap,
      ← RingHom.comp_assoc, ef]
  obtain ⟨GU, ⟨mG⟩⟩ := pull_group (spMap φ) G
  obtain ⟨tU, ⟨mt⟩⟩ := pull_group (spMap i) t
  obtain ⟨mx', _⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ mx mt
  obtain ⟨mg', _⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ mg mt
  have square : spMap i ≫ spMap (algebraMap T.V T.Fr) = spMap (algebraMap U.V U.Fr) ≫ spMap φ := by
    rw [GlobalTheory.EtaVal.spMap_comp_spMap, GlobalTheory.EtaVal.spMap_comp_spMap, hi]
  obtain ⟨mg'', _⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ mG (PullbackSections.sabMapCast mg' square)
  obtain ⟨bU, ltU⟩ := bounded_extension hp C T U φ finite e e' ext bound
  exact compare_over_trait Y Y' U hU (i.comp io) io' x' (base P _ ee ex) (base P' _ ei' ex')
    GU tU mx' mg'' hp P P' e' ee bU ltU (ex.trans hxe.symm) e' ei' bU ltU (ex'.trans hxe.symm) A A'

#print axioms compare_at_point

#print axioms compare_over_trait
end
end GeometryAudit.ModelComparison
