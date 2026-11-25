import Armstrong.Frozen.RawBeta.GKRootedC1Arc38

set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory intervalIntegral
namespace NlsGge.GK38
noncomputable section

def GKArcCurve38 {φ : GKPotential38} {m : ℤ}
    (a : GKRootedC1Arc38 φ m) : ℝ → ℂ := a.1.1


end
end NlsGge.GK38
