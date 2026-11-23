import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupPinsOfMuIsW

open GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl

example (hL : GlobalTheory.Published.LocalLanglandsGL) : DivEx (prm0 hL).s :=
  DivRec.divEx_prov _ rfl
