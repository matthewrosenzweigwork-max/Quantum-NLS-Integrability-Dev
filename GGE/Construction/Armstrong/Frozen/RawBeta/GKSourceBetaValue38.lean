import Armstrong.Frozen.RawBeta.HasGKImproperPathIntegral38

set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory intervalIntegral
namespace NlsGge.GK38
noncomputable section

def GKSourceBetaValue38 (n m : ℤ) (hmn : m ≠ n)
    (F : (k : ℤ) → PotPair → P2Space38 k) (φ : GKPotential38)
    (β : ℂ) : Prop :=
  ∃ p : GKRootedPiecewisePath38 φ m,
    HasGKImproperPathIntegral38 n m F φ p β ∧
    ∀ q : GKRootedPiecewisePath38 φ m,
      HasGKImproperPathIntegral38 n m F φ q β


end
end NlsGge.GK38
