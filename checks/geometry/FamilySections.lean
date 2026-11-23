import FamilyTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFactorisationScalarReferenceTupleEqOne
import Formalism.LocalToGlobal.GroupLattices.JointServices.Cut
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToShimXEqShimXOfPkg

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.LocM
open GeometryAudit.FamilyTop
open Formalism.MainNotions.DIV.Cons (SCF)

namespace GeometryAudit.FamilySections

attribute [local instance] Formalism.BasicNotions.Host.cmStar

-- The family uses only the rank, signature index and level of a datum.
theorem family_iso {D : D7} {T : Top D} {h : LawsP T} {st : StFams D} (R : RowKits T h st)
    (P : FormsOver (cutSt _) (resSt _) R.k) :
    IsoInv (famOf (cutSt _) (resSt _) R.k (AsmCheck.primes_first R.F) P) := by
  intro w w' hS hk hj h h'
  have hr : w.N = w'.N := hS.rank_eq
  change shimXAt (cutSt _) (resSt _) R.k w.N w.j w.two_le w.j_le w.κ h =
    shimXAt (cutSt _) (resSt _) R.k w'.N w'.j w'.two_le w'.j_le w'.κ h'
  congr 1

open GlobalTheory.VarietyModelRecord GlobalTheory.ProjVar GlobalTheory.Cartier

private def vanishingSections {F : Type} [Field F] (Y : Var F) (Δ : Y.Dv) (Z : Y.Cl) : Submodule F Y.Fn where
  carrier := {f | Y.vanishOn Δ f Z}
  zero_mem' := fun x _ => Δ.vanishesAt_zero x
  add_mem' hf hg := fun x hx => (hf x hx).add (hg x hx)
  smul_mem' a f hf := by
    intro x hx
    obtain ⟨g, hg⟩ := Δ.exists_isEqn x
    apply hg.vanishesAt_iff.2
    have h := (hg.vanishesAt_iff.1 (hf x hx)).mul (Y.regAt_algebraMap x a)
    simpa [Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc] using h

-- The generators of the row lattice span the row over its coefficient field.
private theorem generated_row {D : D7} (X : DivX D) (j : ℕ) (h1 : 1 ≤ j) (hm : j ≤ D.R.m)
    (V : Submodule D.what₂.LL (X.MjH j).V)
    (onGen : ∀ v ∈ (D.what₂.MjLat j).gen, ∀ y, X.jM j y = v → y ∈ V) :
    ∀ x, x ∈ V := by
  classical
  intro x
  obtain ⟨a, ha⟩ := GlobalTheory.Mem.R3.Rw.NumDef.jM_mem_rng D X j h1 hm x
  let g (v : D.what₂.Mj j) := if h : v ∈ (D.what₂.MjLat j).gen then (X.MjLat_sub j h1 hm v h).choose else 0
  have hg v (hv : v ∈ (D.what₂.MjLat j).gen) : X.jM j (g v) = v := by
    simpa [g, hv] using (X.MjLat_sub j h1 hm v hv).choose_spec
  have e : x = ∑ v ∈ (D.what₂.MjLat j).gen, a v • g v := by
    apply Idx.jM_inj X j
    rw [ha, map_sum]
    exact Finset.sum_congr rfl fun v hv => by rw [LinearMap.map_smulₛₗ, hg v hv]
  rw [e]
  exact V.sum_mem fun v hv => V.smul_mem _ (onGen v hv _ (hg v hv))

theorem cusp_of_reads {D : D7} {T : Top D} {h : LawsP T} {Q : KitClass D} {n : ℕ}
    (Φ : FamOver Q T h n) (X : DivX D) (iM : _) (hiM : _) (reads : Φ.Reads X iM) :
    CuspTieX (record X Φ.fam iM hiM Φ.dH) := by
  intro j h1 hm c
  obtain ⟨_, w, s, φ, _, hw, _, hlat, _, _, cmp⟩ := reads j h1 hm
  have hwt : (fun τ i => DV.kapW D j τ (Fin.cast (datW_N D Φ.F.κg j) i)) =
      wtOfN (datW D Φ.F.κg j).N w := by
    funext τ i
    rw [← hw]
    rfl
  let U := Φ.fam.Uw j
  let V := (vanishingSections (U.alg.Yv c) (U.alg.Lw c (wtOfN (datW D Φ.F.κg j).N w)) (U.alg.Ybd c)).comap (iM j c)
  intro x
  change (geoTrue D.what₂.LL).vanishOn (U.alg.Yv c)
    ((U.alg.Lw c) (fun τ i => DV.kapW D j τ (Fin.cast (datW_N D Φ.F.κg j) i))) (iM j c x) (U.alg.Ybd c)
  apply (congrArg (fun W => (geoTrue D.what₂.LL).vanishOn (U.alg.Yv c) (U.alg.Lw c W) (iM j c x) (U.alg.Ybd c)) hwt).mpr
  apply generated_row X j h1 hm V _ x
  intro v hv y hy
  obtain ⟨f, hf⟩ := hlat (Formalism.L2.G.ServJoint.gen_mem_carrier _ hv)
  change (geoTrue D.what₂.LL).vanishOn _ _ (iM j c y) _
  exact (congrArg (fun g => (geoTrue D.what₂.LL).vanishOn (U.alg.Yv c)
    (U.alg.Lw c (wtOfN (datW D Φ.F.κg j).N w)) g (U.alg.Ybd c))
    (cmp f y (hy.trans hf.symm) c)).mpr (Φ.P.cmp_cusp j w c f)

#print axioms cusp_of_reads
#print axioms family_iso
end GeometryAudit.FamilySections
