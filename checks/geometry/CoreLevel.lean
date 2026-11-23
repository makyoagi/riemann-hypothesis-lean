import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin

open Formalism.BasicNotions Formalism.MainNotions.Inhab GlobalTheory.Mem GlobalTheory.Mem.Col2
open GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl
open GlobalTheory.Mem.LiteralAutomorphy

namespace GeometryAudit.CoreLevel

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
  {Z : w.Lt} {hL : GlobalTheory.Published.LocalLanglandsGL}

-- Identical source on the original checkout and the geometry-ablation branch.
-- Each statement concerns the very same row core that occurs in OAt.
theorem prm0_level (l : Lv4 (prm0 hL).s K w Z) :
    l.what₂.r.z.core.toCore.Q.l.A = 1 :=
  l.rx.laws.pins.2.1.2

theorem prm1_level (d : ℝ) (l : Lv4 (prm1 hL d).s K w Z) :
    l.what₂.r.z.core.toCore.Q.l.A = 1 :=
  l.rx.laws.pins.2.1.2

theorem prmA_level (d : ℝ) (a : _) (l : Lv4 (prmA hL d a).s K w Z) :
    l.what₂.r.z.core.toCore.Q.l.A = 1 :=
  l.rx.laws.pins.2.1.2

#print axioms prm0_level
#print axioms prm1_level
#print axioms prmA_level

end GeometryAudit.CoreLevel
