import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupPinsOfMuIsW

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
open GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.DivRec
-- The original divEx_prov proof with a specified kit class and the stronger slot.
example (Q : ∀ D : D7, GlobalTheory.ShFam.KitClass D) (𝒮 : Slots)
    (hOx : 𝒮.Ox = OX (geoOf Q)) : DivEx 𝒮 :=
  StepW.of_all fun _ _ _ _ w _ _ hpin Z l =>
    let ⟨Y, h1, h2, h3, h4⟩ := exists_divT w hpin.some Z l
    ⟨Y, h1, h2, h3, fun O t hX hp ht => by
      rw [hOx]
      refine ⟨⟨?_, lamAre_heq hp ht (hX ▸ h4)⟩⟩
      change (∃ c : ℕ, 0 < c ∧ GlobalTheory.ShFam.IsGeoOf (Q _) t.r.z.core.toCore c O.X) ∧
        GlobalTheory.ShFam.Pad.HasTrueSurf O.X
      assumption⟩
end GlobalTheory.Mem.Top.DivRec
