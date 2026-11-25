import Armstrong.Frozen.RawBeta.GKArcSheet38

set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory intervalIntegral
namespace NlsGge.GK38
noncomputable section

def GKRootedArcJoin38 (φ : GKPotential38) (m : ℤ)
    (a b : GKRootedC1Arc38 φ m) : Prop :=
  GKArcCurve38 a 1 = GKArcCurve38 b 0 ∧
  GKArcSheet38 a 1 = GKArcSheet38 b 0 ∧
  GKArcCurve38 a 1 ∈ GKOriginalSlit38 φ m


end
end NlsGge.GK38
