import ProductionHeightCandidates
import FamilySections
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArTopOfInduced
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MSmoothAndSemiPosIff
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.CycleHeightFormulas.CycleHeightsDirect
import Development.WeilBound.CoreStatements.ResolutionCharZero.PlugResK
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PoincareLelong.PoincareLelongInv
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ChernDegreeComplex.ChernDegreeComplex
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.PublishedTheoremStatements.BridgesGeo

open NumberField Formalism.BasicNotions Formalism.BasicNotions.DV
open Formalism.MainNotions.HeightShare Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam
open GlobalTheory.VarietyModelRecord GeometryAudit.ProductionHeight

namespace GeometryAudit.FamilyComponentIntersection

noncomputable section

/-- The component and its section metric are fixed before choosing generators. -/
def componentData {D : D7} (X : DivX D) (j : ℕ) (c : X.Comp j) : LData X.geo := by
  classical
  let gen := Submodule.fg_iff_exists_fin_generating_family.mp (X.MjH_good j).2.1
  let w := gen.choose_spec.choose
  exact {
    Y := X.Yv j c, bd := X.Ybd j c, L := X.Lw j c (kapW D j)
    W := X.MjH j, ιW := X.iMj j c, n := gen.choose, w := w
    abelian₂ := max 1 (sSup (Set.range fun iv : Fin gen.choose × InfinitePlace D.what₂.LL =>
      nrm (X.MjH j) iv.2 (w iv.1))) }

theorem componentData_height {D : D7} (X : DivX D) (j : ℕ) (c : X.Comp j) :
    (componentData X j c).h = componentHeight X j c := rfl

private theorem intersectionCalculus : Published.ArCalc :=
  ArithmeticHeightTower.ArakelovDirectHeights.arCalc_direct
    PositivityTheory.Tls2.Pl.poincareLelong PositivityTheory.ResPlug.FromRes.resK

private theorem intersectionDegree : Published.ArDegree :=
  PositivityTheory.Prw.arDegree_of
    (Published.CycleHeights.heightProjection
      (ArithmeticHeightTower.ArakelovDirectHeights.cycleHeights_direct
        PositivityTheory.Tls2.Pl.poincareLelong PositivityTheory.ResPlug.FromRes.resK))
    PositivityTheory.Tls2.Chern2.chernDegreeComplex

/-- A common zero persists under the complex frame change used by ofW. An
    induced model would make that same Fubini–Study metric smooth everywhere. -/
private theorem no_model_at_common_zero {F : Type} [Field F] [NumberField F] [StarRing F]
    (σ : F →+* ℂ) (Y : Var F) (Δ : Y.Dv) (W : HLat F) (ι : W.V →ₗ[F] Y.Fn)
    (Z : Y.Cl) (hne : (Z : Set Y.X).Nonempty) (van : ∀ v, Y.vanishOn Δ (ι v) Z) :
    ¬ (TrueGeo.ofW (cxSt F) Y Δ W ι).IsModel := by
  have := ComplexPoints.surjective_specMap_field σ
  have : AlgebraicGeometry.Smooth Y.str := AlgebraicGeometry.SmoothOfRelativeDimension.smooth Y.dim _
  obtain ⟨f, hf, hfZ⟩ := ComplexPoints.exists_geomPoint_mem Y.str
    (AlgebraicGeometry.Spec.map (CommRingCat.ofHom σ)) Z.isClosed.isLocallyClosed hne
  let y : Y.pts σ := ⟨f, hf⟩
  have hy : Var.base y ∈ Z := hfZ _
  rintro ⟨M, L, k, cf, hI⟩
  have smooth := (InducedSemiPos.mSmooth_and_semiPos_iff _ _ _ _ _ _ _ _ hI).1 σ
  obtain ⟨t, ht⟩ := (Var.mSmooth_fsMet_iff.mp smooth y).2
  apply ht
  let g := Var.eqn Δ y
  have hg := Var.mem_eqnSet Δ y
  have hz i := (Var.secZero_iff hg).mp
    (Var.secZero_cx_iff.mpr (van (W.b i) (Var.base y) hy))
  refine ⟨g, hg, ?_⟩
  have hv := Var.hasVal_sum_smul hg (fun i => (hz i).1) (fun i => frameAt W σ i t)
  have he : (∑ i, frameAt W σ i t * Var.fval (Var.eqn Δ y) (Y.cx σ (ι (W.b i))) y) = 0 :=
    Finset.sum_eq_zero fun i _ => mul_eq_zero_of_right _ (hz i).2
  rw [he] at hv
  exact hv

private def closedSet {F : Type} [Field F] (Y : Var F) (Z : Y.Cl) : Set Y.X := Z.carrier

private def baseAt {F : Type} [Field F] (Y : Var F) (Δ : Y.Dv) (V : Set Y.Fn) (x : Y.X) :=
  Δ.IsBasePoint V x

private theorem baseAt_of_vanishing {F : Type} [Field F] (Y : Var F) (Δ : Y.Dv)
    {E : Type} (ι : E → Y.Fn) (Z : Y.Cl) (van : ∀ v, Y.vanishOn Δ (ι v) Z)
    (x : Y.X) (hx : x ∈ Z) : baseAt Y Δ (Set.range ι) x := by
  rintro _ ⟨v, rfl⟩
  exact (Cartier.CartierDiv.vanishesAt_iff.mp (van v x hx)).2

private theorem arTop_of_no_model {F : Type} [Field F] [NumberField F] {C : CxSt F}
    {Y : Var F} (A : Adl C Y) (bad : ¬ A.IsModel) : A.arTop = 0 := by
  have noTop : ¬ ∃ t, A.IsArTop t := by
    rintro ⟨_, M, L, k, cf, _, hI, _⟩
    exact bad ⟨M, L, k, cf, hI⟩
  exact dif_neg noTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Family

variable {D : D7} {Q : KitClass D} {T : Top D} {h : LawsP T} {n : ℕ}
  (Φ : FamOver Q T h n) (X : DivX D)
  (iM : ∀ j (c : (Φ.fam.Uw j).Comp), (X.MjH j).V →ₗ[D.what₂.LL]
    (geoTrue D.what₂.LL).Fn ((Φ.fam.Uw j).alg.Yv c))
  (reg : ∀ j c x, iM j c x ∈ (geoTrue D.what₂.LL).H0 ((Φ.fam.Uw j).alg.Yv c)
    ((Φ.fam.Uw j).alg.Lw c (fun τ i => kapW D j τ (Fin.cast (datW_N D Φ.F.κg j) i))))
  (j : ℕ) (c : (Φ.fam.Uw j).Comp)

local notation "row" => record X Φ.fam iM reg Φ.dH
local notation "B" => componentData row j c
local notation "Yc" => (LData.Y B : Var D.what₂.LL)
local notation "boundarySet" => closedSet Yc (LData.bd B)

/-- A semipositive arithmetic model presenting this very bundle exists if the
    row sections generate at every point. The height is its normalized self-intersection. -/
theorem model_formula_of_bpf
    (bpf : (B).Y.bpf (B).L (Set.range (iM j c))) :
    ∃ (M : TrueGeo.Model (B).Y) (L : HermLB M.p),
      (B).Lbar.Induced M L 1 0 ∧ ArInt.NefFib L ∧ L.SemiPos (B).Y.dim ∧
      ∃ a : ℝ, (haveI := M.ar.isIntegral; L.IsSelfInter a) ∧
        (B).h = (a / (Module.finrank ℚ D.what₂.LL : ℝ)) / ((((B).Dm : ℝ) + 1) * (B).del) := by
  obtain ⟨M, L, hI, hn, hs⟩ := OfLattice.exists_induced D.what₂.LL (cxSt _)
    (B).Y (B).L (X.MjH j) (iM j c) (X.MjH_good j)
    (fun v hv => False.elim (InfinitePlace.not_isReal_iff_isComplex.2
      (IsTotallyComplex.isComplex v) hv)) (reg j c) bpf
  have := M.ar.isIntegral
  obtain ⟨H, hH⟩ := (intersectionCalculus.arExists _ M.X M.p _ M.ar).1 L
  let a := H (genericPoint M.X)
  have ha : L.IsSelfInter a := ⟨H, hH, rfl⟩
  refine ⟨M, L, hI, hn, hs, a, ha, ?_⟩
  have ht := (arTop_of_induced intersectionCalculus intersectionDegree _ (cxSt _)
    (B).Y (B).Lbar M L 1 0 hI).2 a ha
  change (B).Lbar.arTop / _ = _
  congr 1
  have e : ((B).Lbar.n : ℕ) = 1 := rfl
  simpa [e] using ht

/-- For the section maps satisfying Reads, every boundary point is a common
    base point. This concerns the precise generation hypothesis used above. -/
theorem boundary_is_base_point (reads : Φ.Reads X iM) (h1 : 1 ≤ j) (hm : j ≤ D.R.m)
    (x : (Yc).X) (hx : x ∈ boundarySet) :
    baseAt Yc (B).L (Set.range (iM j c)) x :=
  baseAt_of_vanishing Yc (B).L (iM j c) (B).bd
    (FamilySections.cusp_of_reads Φ X iM reg reads j h1 hm c) x hx

/-- With a nonempty boundary this component has no induced arithmetic model.
    Its library height evaluates to the default used by Adl.arTop. -/
theorem height_at_nonempty_boundary (reads : Φ.Reads X iM) (h1 : 1 ≤ j) (hm : j ≤ D.R.m)
    (boundary : (boundarySet).Nonempty) : ¬ (B).Lbar.IsModel ∧ (B).h = 0 := by
  have bad := no_model_at_common_zero D.what₂.embLL Yc (B).L (X.MjH j) (iM j c)
    (B).bd boundary (FamilySections.cusp_of_reads Φ X iM reg reads j h1 hm c)
  refine ⟨bad, ?_⟩
  exact (div_eq_zero_iff).mpr (.inl (arTop_of_no_model _ bad))

theorem not_bpf_of_boundary (reads : Φ.Reads X iM) (h1 : 1 ≤ j) (hm : j ≤ D.R.m)
    (boundary : (boundarySet).Nonempty) : ¬ (Yc).bpf (B).L (Set.range (iM j c)) := by
  intro hb
  obtain ⟨M, L, hI, -⟩ := model_formula_of_bpf Φ X iM reg j c hb
  exact (height_at_nonempty_boundary Φ X iM reg j c reads h1 hm boundary).1 ⟨M, L, 1, 0, hI⟩

end Family

#print axioms componentData_height
#print axioms model_formula_of_bpf
#print axioms boundary_is_base_point
#print axioms not_bpf_of_boundary
#print axioms height_at_nonempty_boundary

end
end GeometryAudit.FamilyComponentIntersection
