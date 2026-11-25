import Armstrong.Frozen.RawBeta.GKRootedArcJoin38

set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory intervalIntegral
namespace NlsGge.GK38
noncomputable section

def GKRootedArcChain38 (φ : GKPotential38) (m : ℤ) :
    List (GKRootedC1Arc38 φ m) → Prop
  | [] => False
  | [_] => True
  | a :: b :: tail =>
      GKRootedArcJoin38 φ m a b ∧ GKRootedArcChain38 φ m (b :: tail)


end
end NlsGge.GK38
