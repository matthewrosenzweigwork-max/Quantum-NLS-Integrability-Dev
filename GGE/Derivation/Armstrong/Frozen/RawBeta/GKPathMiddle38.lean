import Armstrong.Frozen.RawBeta.GKPathFirst38

set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory intervalIntegral
namespace NlsGge.GK38
noncomputable section

def GKPathMiddle38 {φ : GKPotential38} {m : ℤ}
    (p : GKRootedPiecewisePath38 φ m) : List (GKRootedC1Arc38 φ m) := p.1.2.1


end
end NlsGge.GK38
