import FamilyComponentIntersection
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagComponentPointOverGeometricBasePoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLaurentArcDegeneratingOnModelConvergenceStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LinearIndependentSingleAdd
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LatticeSpanMembership
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianTraceFormVanishing

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.ShFam GlobalTheory.Toroidal GlobalTheory.TrueGeo
open ReciprocityTheory.ChartRestriction.G.FD
open scoped LaurentSeries

namespace GeometryAudit.ProductionBoundary

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Q : KitClass D} {T : Formalism.L2.Pj.Top D} {h : LawsP T}
  {n : ℕ} (Φ : FamOver Q T h n)

private abbrev rowModel (j : ℕ) := (Φ.F.at (datW D Φ.F.κg j)).T.Z
private abbrev rowFlag (j : ℕ) := (Φ.k.at (datW D Φ.F.κg j)).Φ

/-- Every component boundary is empty exactly when the row's open immersion covers
    its compactification. Coverage of the compactification by flags proves the converse. -/
theorem row_empty_iff_surjective (j : ℕ) :
    (∀ (c : (Φ.fam.Uw j).Comp) (y : ((rowFlag Φ j).C c).Y.X),
      y ∉ ((Φ.fam.Uw j).alg.Ybd c).carrier) ↔ Function.Surjective (rowModel Φ j).jQ := by
  constructor
  · intro hempty z
    obtain ⟨c, y, rfl⟩ := GlobalTheory.FlagCptBase.exists_mem_range (rowFlag Φ j) z
    by_contra missing
    exact hempty c y ((((rowFlag Φ j).C c).bd_supp y).2 missing)
  · intro covers c y hy
    exact (((rowFlag Φ j).C c).bd_supp y).1 hy (covers _)

/-- Properness is tested on the open moduli space after extending to the
    actual row's coefficient field. -/
theorem row_empty_iff_proper (j : ℕ) :
    (∀ (c : (Φ.fam.Uw j).Comp) (y : ((rowFlag Φ j).C c).Y.X),
      y ∉ ((Φ.fam.Uw j).alg.Ybd c).carrier) ↔ IsProper ((rowModel Φ j).jQ ≫ genStr (rowModel Φ j)) := by
  rw [row_empty_iff_surjective]
  have := isProper_genStr (rowModel Φ j)
  have := (rowModel Φ j).jQ_open
  constructor
  · intro covers
    have : Surjective (rowModel Φ j).jQ := ⟨covers⟩
    have : IsIso (rowModel Φ j).jQ := isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by
      ext x
      exact ⟨fun _ => trivial, fun _ => covers x⟩)
    infer_instance
  · intro proper
    have : IsProper (rowModel Φ j).jQ := IsProper.of_comp (rowModel Φ j).jQ (genStr (rowModel Φ j))
    exact Set.range_eq_univ.1 ((rowModel Φ j).jQ.isClosedMap.isClosed_range.closure_eq.symm.trans
      (rowModel Φ j).jQ_dense.closure_eq)

/-- Every flag component of the terminal production row has empty boundary. -/
theorem terminal_boundary_empty :
    ∀ (c : (Φ.fam.Uw D.R.m).Comp) (y : ((rowFlag Φ D.R.m).C c).Y.X),
      y ∉ ((Φ.fam.Uw D.R.m).alg.Ybd c).carrier := by
  apply (row_empty_iff_surjective Φ _).2
  apply surjective_jQ_of_dim_eq_zero
  have hq := (Φ.F.dat D.R.m ⟨(by have := D.R.two_le_m; omega), le_rfl⟩).2.1
  change (Φ.F.sigW D.R.m).Dw.q = D.R.m - D.R.m at hq
  have e : (Φ.F.sigW D.R.m).Dw.q = 0 := hq.trans (Nat.sub_self _)
  change (Φ.F.sigW D.R.m).Dw.dim = 0
  simp [Datum.dim, e]

/-- On each earlier in-range row both signature entries are positive. -/
theorem earlier_signature (j : ℕ) (hj : 1 ≤ j) (hm : j < D.R.m) :
    0 < (Φ.F.sigW j).Dw.p ∧ 0 < (Φ.F.sigW j).Dw.q := by
  have d := Φ.F.dat j ⟨hj, hm.le⟩
  have hp := d.1
  have hq := d.2.1
  change (Φ.F.sigW j).Dw.p = D.R.k + j - 1 at hp
  change (Φ.F.sigW j).Dw.q = D.R.m - j at hq
  have := D.R.m_add_three_le_k
  omega

private theorem chart_boundary {A : Amb D} {N u : ℕ} {S : Sig A N u} {κ : Lv A}
    (s : FinalTheorems S κ) (L : CmList A) (k : s.Comp) (hr : 2 < N) (hu : 0 < u) (hun : u < N) :
    ∃ z, z ∈ genBd s.T.Z := by
  let X := s.fd k
  have hp : X.p0 = N - u := s.p0_eq k
  obtain ⟨cu⟩ := GlobalTheory.CuspExist.nonempty_cuspFD GlobalTheory.QNorm.hasseNormSt
    D.host.E N 1 X (by omega) (by omega) (by omega)
  obtain ⟨d, hd, hmem⟩ := LatticeSpanMembership.exists_nat_smul_mem (X := X) (cu.e 0)
  let v := (d : D.host.E) • cu.e 0
  have hiso : X.IsIso v := by
    refine ⟨hmem, ?_, smul_ne_zero (Nat.cast_ne_zero.mpr hd.ne') (cu.ind.ne_zero 0)⟩
    simp only [v, HermitianTraceFormVanishing.herm_smul_left,
      HermitianTraceFormVanishing.herm_smul_right, cu.iso, mul_zero]
  let σ := κ.σ₀
  let : Algebra κ.c.F ℂ⸨X⸩ := (GlobalTheory.ArcId.cstL.comp σ).toAlgebra
  let f := s.frameOver L k 0
  obtain ⟨_, _, _, _, ⟨χ, _, _, _, _, centre⟩, _, _⟩ :=
    GlobalTheory.T.exists_laurentArc_degenerating_on_model_convergence
      _ _ _ _ _ _ σ N (s.U σ) (fun _ => rfl) κ.good_σ₀ s.isUnf k v hiso f.1 f.2 _ _ s.T.Z
  exact ⟨_, centre⟩

/-- Every earlier production row has a boundary point on at least one actual flag component. -/
theorem earlier_boundary_nonempty (j : ℕ) (hj : 1 ≤ j) (hm : j < D.R.m) :
    ∃ (c : (Φ.fam.Uw j).Comp) (y : ((rowFlag Φ j).C c).Y.X),
      y ∈ ((Φ.fam.Uw j).alg.Ybd c).carrier := by
  let w := datW D Φ.F.κg j
  have sig := earlier_signature Φ j hj hm
  have u : (Φ.F.sigW j).Dw.p = w.j := (Φ.F.sigW j).p_eq
  have r : (Φ.F.sigW j).Dw.p + (Φ.F.sigW j).Dw.q = w.N := (Φ.F.sigW j).rank_eq
  have hr : 2 < w.N := by
    change 2 < (datW D Φ.F.κg j).N
    rw [datW_N]
    have := D.R.two_le_m
    have := D.R.m_add_three_le_k
    unfold Ranks.r
    omega
  let s := Φ.F.at w
  obtain ⟨k⟩ := s.compNe
  obtain ⟨z, hz⟩ := chart_boundary s Φ.L k hr (by omega) (by omega)
  obtain ⟨c, y, rfl⟩ := GlobalTheory.FlagCptBase.exists_mem_range (rowFlag Φ j) z
  exact ⟨c, y, (((rowFlag Φ j).C c).bd_supp y).2 hz⟩

open Formalism.BasicNotions.DV Formalism.MainNotions.HeightShare
open GlobalTheory.VarietyModelRecord GeometryAudit.FamilyComponentIntersection

/-- On each earlier row the actual section metric has an obstructed component.
    Its height is the library's fallback value for the absence of an induced model. -/
theorem earlier_row_obstruction (X : DivX D)
    (iM : ∀ j (c : (Φ.fam.Uw j).Comp), (X.MjH j).V →ₗ[D.what₂.LL]
      (geoTrue D.what₂.LL).Fn ((Φ.fam.Uw j).alg.Yv c))
    (reg : ∀ j c x, iM j c x ∈ (geoTrue D.what₂.LL).H0 ((Φ.fam.Uw j).alg.Yv c)
      ((Φ.fam.Uw j).alg.Lw c (fun τ i => kapW D j τ (Fin.cast (datW_N D Φ.F.κg j) i))))
    (reads : Φ.Reads X iM) (j : ℕ) (hj : 1 ≤ j) (hm : j < D.R.m) :
    ∃ c : (Φ.fam.Uw j).Comp,
      let B := componentData (record X Φ.fam iM reg Φ.dH) j c
      ¬ B.Y.bpf B.L (Set.range (iM j c)) ∧ ¬ B.Lbar.IsModel ∧ B.h = 0 := by
  obtain ⟨c, y, hy⟩ := earlier_boundary_nonempty Φ j hj hm
  exact ⟨c, not_bpf_of_boundary Φ X iM reg j c reads hj hm.le ⟨y, hy⟩,
    height_at_nonempty_boundary Φ X iM reg j c reads hj hm.le ⟨y, hy⟩⟩

#print axioms row_empty_iff_surjective
#print axioms row_empty_iff_proper
#print axioms terminal_boundary_empty
#print axioms earlier_signature
#print axioms earlier_boundary_nonempty
#print axioms earlier_row_obstruction

end
end GeometryAudit.ProductionBoundary
