import Armstrong.Frozen.RawBeta.GKPathTruncatedIntegral38

set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory intervalIntegral
namespace NlsGge.GK38
noncomputable section

def GKPathCompactIntegrable38 (n m : ℤ)
    (F : (k : ℤ) → PotPair → P2Space38 k) (φ : GKPotential38)
    (p : GKRootedPiecewisePath38 φ m) : Prop :=
  ∀ ε η : ℝ, 0 < ε → 0 < η → ε + η < 1 →
    IntervalIntegrable
      (GKRootedArcIntegrand38 n m F φ (GKPathFirst38 p)) volume ε 1 ∧
    (∀ a : GKRootedC1Arc38 φ m, a ∈ GKPathMiddle38 p →
      IntervalIntegrable (GKRootedArcIntegrand38 n m F φ a) volume 0 1) ∧
    IntervalIntegrable
      (GKRootedArcIntegrand38 n m F φ (GKPathLast38 p)) volume 0 (1 - η)


end
end NlsGge.GK38
