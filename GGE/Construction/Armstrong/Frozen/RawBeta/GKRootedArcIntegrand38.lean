import Armstrong.Frozen.RawBeta.GKPathLast38

set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory intervalIntegral
namespace NlsGge.GK38
noncomputable section

def GKRootedArcIntegrand38 (n m : ℤ)
    (F : (k : ℤ) → PotPair → P2Space38 k) (φ : GKPotential38)
    (a : GKRootedC1Arc38 φ m) (t : ℝ) : ℂ :=
  (p6PsiNumerator38 n (F n) φ.1 (GKArcCurve38 a t) /
    GKArcSheet38 a t) * deriv (GKArcCurve38 a) t


end
end NlsGge.GK38
