import Armstrong.Frozen.RawBeta.GKRootedPathData38

set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory intervalIntegral
namespace NlsGge.GK38
noncomputable section

def GKRootedPiecewisePath38 (φ : GKPotential38) (m : ℤ) : Type :=
  {q : GKRootedPathData38 φ m //
    IsolatingFamily38 φ.1 (discC φ.1) (discR φ.1) ∧
    GKRootedArcChain38 φ m (q.1 :: (q.2.1 ++ [q.2.2])) ∧
    GKArcCurve38 q.1 0 = lamMinus φ.1 m ∧
    GKArcCurve38 q.2.2 1 = muSeq φ.1 m ∧
    (muSeq φ.1 m ≠ lamMinus φ.1 m →
      muSeq φ.1 m ≠ lamPlus φ.1 m →
      GKArcSheet38 q.2.2 1 = antiDiscrim φ.1 (muSeq φ.1 m))}


end
end NlsGge.GK38
