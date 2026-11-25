import NlsGge.GK38.AbelianPsiTheorem141
import NlsGge.GK38.AbelianPeriods
import NlsGge.GK38.DirichletRealBridge
import NlsGge.GK38.IsolatingDefs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory intervalIntegral
namespace NlsGge.GK38
noncomputable section

def GKPotential38 : Type := {φ : PotPair // φ ∈ gkW}


end
end NlsGge.GK38
