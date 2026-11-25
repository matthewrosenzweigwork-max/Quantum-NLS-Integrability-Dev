import Armstrong.Frozen.RawBeta.GKPathMiddle38

set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory intervalIntegral
namespace NlsGge.GK38
noncomputable section

def GKPathLast38 {φ : GKPotential38} {m : ℤ}
    (p : GKRootedPiecewisePath38 φ m) : GKRootedC1Arc38 φ m := p.1.2.2


end
end NlsGge.GK38
