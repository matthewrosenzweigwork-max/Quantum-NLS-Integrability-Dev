import Armstrong.Frozen.RawBeta.GKPathMiddleIntegral38

set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory intervalIntegral
namespace NlsGge.GK38
noncomputable section

def GKPathTruncatedIntegral38 (n m : ℤ)
    (F : (k : ℤ) → PotPair → P2Space38 k) (φ : GKPotential38)
    (p : GKRootedPiecewisePath38 φ m) (ε η : ℝ) : ℂ :=
  (∫ t in ε..(1 : ℝ),
    GKRootedArcIntegrand38 n m F φ (GKPathFirst38 p) t) +
  GKPathMiddleIntegral38 n m F φ (GKPathMiddle38 p) +
  (∫ t in (0 : ℝ)..((1 : ℝ) - η),
    GKRootedArcIntegrand38 n m F φ (GKPathLast38 p) t)


end
end NlsGge.GK38
