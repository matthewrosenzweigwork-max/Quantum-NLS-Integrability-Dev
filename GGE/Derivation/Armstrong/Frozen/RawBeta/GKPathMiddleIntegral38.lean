import Armstrong.Frozen.RawBeta.GKRootedArcIntegrand38

set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory intervalIntegral
namespace NlsGge.GK38
noncomputable section

def GKPathMiddleIntegral38 (n m : ℤ)
    (F : (k : ℤ) → PotPair → P2Space38 k) (φ : GKPotential38) :
    List (GKRootedC1Arc38 φ m) → ℂ
  | [] => 0
  | a :: tail =>
      (∫ t in (0 : ℝ)..(1 : ℝ), GKRootedArcIntegrand38 n m F φ a t) +
        GKPathMiddleIntegral38 n m F φ tail


end
end NlsGge.GK38
