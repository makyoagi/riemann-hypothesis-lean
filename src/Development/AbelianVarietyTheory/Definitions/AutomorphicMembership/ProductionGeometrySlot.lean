import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsKitWithKitWith
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotMemPlaceholder
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse

open Formalism.BasicNotions GlobalTheory.ShFam

namespace GeometryAudit.ProductionGeometry

noncomputable def stages (D : D7) : StFams D := (KitCheck.nonempty_stFams D).some

end GeometryAudit.ProductionGeometry

namespace GlobalTheory.Mem.Top.Bl

noncomputable def productionPredicate : GeoP :=
  geoOf (fun D => IsKitOf (GeometryAudit.ProductionGeometry.stages D))

noncomputable def productionGeometry : Option GeoP := closeGeometry (some productionPredicate)

end GlobalTheory.Mem.Top.Bl
