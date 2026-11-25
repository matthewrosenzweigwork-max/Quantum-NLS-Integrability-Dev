import Armstrong.Frozen.RawBeta.GKRootedArcChain38

set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory intervalIntegral
namespace NlsGge.GK38
noncomputable section

def GKRootedPathData38 (φ : GKPotential38) (m : ℤ) : Type :=
  GKRootedC1Arc38 φ m ×
    (List (GKRootedC1Arc38 φ m) × GKRootedC1Arc38 φ m)


end
end NlsGge.GK38
