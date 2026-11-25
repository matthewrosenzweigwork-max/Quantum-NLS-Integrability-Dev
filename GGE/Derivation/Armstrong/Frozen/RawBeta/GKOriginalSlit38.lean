import Armstrong.Frozen.RawBeta.GKPotential38

set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory intervalIntegral
namespace NlsGge.GK38
noncomputable section

def GKOriginalSlit38 (φ : GKPotential38) (m : ℤ) : Set ℂ :=
  ball (discC φ.1 m) (discR φ.1 m) \
    segment ℝ (lamMinus φ.1 m) (lamPlus φ.1 m)


end
end NlsGge.GK38
