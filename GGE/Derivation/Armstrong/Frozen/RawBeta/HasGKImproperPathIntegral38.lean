import Armstrong.Frozen.RawBeta.GKPathCompactIntegrable38

set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory intervalIntegral
namespace NlsGge.GK38
noncomputable section

def HasGKImproperPathIntegral38 (n m : ℤ)
    (F : (k : ℤ) → PotPair → P2Space38 k) (φ : GKPotential38)
    (p : GKRootedPiecewisePath38 φ m) (β : ℂ) : Prop :=
  GKPathCompactIntegrable38 n m F φ p ∧
  Tendsto
    (fun q : ℝ × ℝ => GKPathTruncatedIntegral38 n m F φ p q.1 q.2)
    (nhdsWithin ((0 : ℝ), (0 : ℝ))
      {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < 1})
    (nhds β)


end
end NlsGge.GK38
