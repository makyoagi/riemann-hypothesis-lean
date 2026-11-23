import ReadingRealisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TieInOfFwTie
import Formalism.LocalToGlobal.GroupLattices.JointServices.Cut

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions
open Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.RealGeo
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GeometryAudit.ReadingRealisation
noncomputable section

private theorem injective_of_independent {K U H : Type} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup H] [Module ℂ H] {σ : K →+* ℂ} (J : U →ₛₗ[σ] H)
    (h : ∀ n (v : Fin n → U), LinearIndependent K v → LinearIndependent ℂ (fun l => J (v l))) :
    Function.Injective J := by
  apply (injective_iff_map_eq_zero J).2
  intro x hx
  by_contra hn
  exact (h 1 (fun _ => x) (linearIndependent_unique_iff.2 hn)).ne_zero 0 hx

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type}
    {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL]
    {R : RealDat D A T.Q.c.F} {phase : Fin D.R.m → ℂ}

theorem integral_realisation (h : LawsCore T.toCore) (hK : DV.KapDef D) (hR : PreChar R)
    (B : GeoHalf T R phase) (geo : InGeo B) {F : Face D A} (mj : MjTie R F) (i : Fin D.R.m) :
    ∃ (s : Submodule T.Q.c.F (Cu T B.κ i)) (φ : s →ₛₗ[T.σ₀] D.what₂.Mj ((i : ℕ) + 1)),
      (∀ {n : ℕ} (v : Fin n → s), LinearIndependent T.Q.c.F v → LinearIndependent ℂ (φ ∘ v)) ∧
      Submodule.span ℂ (Set.range φ) = ⊤ ∧
      (D.what₂.MjLat ((i : ℕ) + 1)).carrier ⊆ Set.range φ ∧
      ∀ x : s, (IntAll T B.κ x.val ↔ φ x ∈ (D.what₂.MjLat ((i : ℕ) + 1)).carrier) ∧
        ‖φ x‖ = Real.sqrt (volRec R F i * Formalism.L2.Geo.dimKap D ((i : ℕ) + 1)) *
          h.Nl ((i : ℕ) + 1) (B.κ i) T.σ₀ (x.val : T.R ((i : ℕ) + 1)) := by
  let J := jTop T R B.κ B.v₀ i (sg0 D A)
  let E := mj.eW i
  let coord := (R.FW i).WK.subtype.comp (B.fw.e i).toLinearMap
  let good := (R.FW i).Wgood F.P0 F.ψ0⁻¹ (fun g => (idemOf A.X).coeff g)
  let s₀ := (LinearMap.range E).comap J
  let s := s₀ ⊓ (good.restrictScalars T.Q.c.F).comap coord
  have tie := GlobalTheory.OneMapRefObj.tieIn_of_fwTie B.fw
  obtain ⟨g, hg⟩ := normed_realisation T R B.κ B.v₀ h hK hR tie geo.jEvExists mj i
  let φ : s →ₛₗ[T.σ₀] D.what₂.Mj ((i : ℕ) + 1) := g.comp (Submodule.inclusion inf_le_left)
  have ej (x : s) : E (φ x) = J x.val := (hg ⟨x.val, x.property.1⟩).1
  have injE : Function.Injective E :=
    GlobalTheory.Mem.LiftForms.inj_of_norm_sq E (RealDat.nP_pos (F := F) false) (mj.eW_norm i)
  have hσ := base_embedding_good T R tie.alg tie.laws.pins.2.2.1
  have hv := tie.laws.spaceW _ (inR i) _ hσ
  have je := B.fw.jK_eq (B.fw.evaluates geo.jEvExists) geo.evInj hσ hv
  have hcoord (f : Cu T B.κ i) : (R.FW i).j (sg0 D A) (coord f) = J f :=
    DFunLike.congr_fun je f
  have jin := injective_of_independent J (geo.jUnif i (sg0 D A)).1
  have cover (v) (mem : v ∈ (D.what₂.MjLat ((i : ℕ) + 1)).carrier) :
      ∃ x : s, φ x = v ∧ IntAll T B.κ x.val := by
    obtain ⟨y, hym, hyg, he⟩ := (mj.eW_lat i v).1 mem
    let f := (B.fw.e i).symm ⟨y, hym.1⟩
    have cf : coord f = y := congrArg Subtype.val ((B.fw.e i).apply_symm_apply ⟨y, hym.1⟩)
    have jv : E v = J f := (he.trans (congrArg ((R.FW i).j (sg0 D A)) cf.symm)).trans (hcoord f)
    have fg : coord f ∈ good := (congrArg (fun z => z ∈ good) cf).mpr hyg
    have fm : coord f ∈ (R.FW i).MK := (congrArg (fun z => z ∈ (R.FW i).MK) cf).mpr hym
    let x : s := ⟨f, ⟨⟨v, jv⟩, fg⟩⟩
    exact ⟨x, injE ((ej x).trans jv.symm), (B.fw.mem_MK i f).1 fm⟩
  have includes : (D.what₂.MjLat ((i : ℕ) + 1)).carrier ⊆ Set.range φ :=
    fun v hv => ⟨(cover v hv).choose, (cover v hv).choose_spec.1⟩
  refine ⟨s, φ, ?_, top_unique ?_, includes, fun x => ⟨⟨?_, ?_⟩, (hg ⟨x.val, x.property.1⟩).2⟩⟩
  · intro n v hv
    apply LinearIndependent.of_comp E
    have he : E ∘ (φ ∘ v) = fun l => J (v l).val := funext fun l => ej (v l)
    rw [he]
    exact (geo.jUnif i (sg0 D A)).1 n _ (hv.map' s.subtype (Submodule.ker_subtype s))
  · rw [← (D.what₂.MjLat ((i : ℕ) + 1)).span_top]
    exact Submodule.span_mono fun v hv => includes (Formalism.L2.G.ServJoint.gen_mem_carrier _ hv)
  · intro hx
    exact (mj.eW_lat i _).2 ⟨coord x.val, (B.fw.mem_MK i x.val).2 hx, x.property.2,
      (ej x).trans (hcoord x.val).symm⟩
  · intro hx
    obtain ⟨y, he, hy⟩ := cover _ hx
    have eq : y.val = x.val := jin (((ej y).symm.trans (congrArg E he)).trans (ej x))
    exact eq ▸ hy

theorem core_cusp (h : LawsCore T.toCore) (hK : DV.KapDef D) (hR : PreChar R)
    (B : GeoHalf T R phase) (geo : InGeo B) {F : Face D A} (mj : MjTie R F) (i : Fin D.R.m) :
    MjCusp h ((i : ℕ) + 1) (B.κ i) (volRec R F i) := by
  obtain ⟨s, φ, indep, span, cover, row⟩ := integral_realisation h hK hR B geo mj i
  exact ⟨s, φ, indep, span, cover, fun x => (row x).1, fun x => (row x).2⟩

end
#print axioms integral_realisation
#print axioms core_cusp
end GeometryAudit.ReadingRealisation
