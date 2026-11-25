import Mathlib
import NlsGge.ThirdConsultation.G3.G3SourcePathHost
import Armstrong.Frozen.RawBeta.GKRootedPathData38
import Armstrong.Frozen.RawBeta.GKRootedArcChain38
import Armstrong.Frozen.RawBeta.GKArcCurve38
import Armstrong.Frozen.RawBeta.GKArcSheet38
import Armstrong.Frozen.RawBeta.GKRootedArcIntegrand38
import Armstrong.Frozen.RawBeta.GKPathMiddleIntegral38

/- G3-005 UPPER-START HOST (proof development, AUTHOR; not self-reviewed). Target NlsGge/ThirdConsultation/G3/G3005UpperHost.lean (proposed).
   Bodies VERBATIM from root/gpt6pro_followup7 DEFINITIONS/G3.lean.md (definitions_design_20261027), section
   "Upper-start paths and their actual improper integral": UpperStartPath, HasUpperStartIntegral. SourcePotential/sourceGK are
   the landed G3SourcePathHost names (not redeclared). Only sealed Frozen RawBeta definitions are imported. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def UpperStartPath (m : ℤ) (φ : SourcePotential) : Type :=
  {q : GKRootedPathData38 (sourceGK φ) m //
    IsolatingFamily38 φ.1 (discC φ.1) (discR φ.1) ∧
    GKRootedArcChain38 (sourceGK φ) m (q.1 :: (q.2.1 ++ [q.2.2])) ∧
    GKArcCurve38 q.1 0 = lamPlus φ.1 m ∧
    GKArcCurve38 q.2.2 1 = muSeq φ.1 m ∧
    (muSeq φ.1 m ≠ lamMinus φ.1 m → muSeq φ.1 m ≠ lamPlus φ.1 m →
      GKArcSheet38 q.2.2 1 = antiDiscrim φ.1 (muSeq φ.1 m))}

def HasUpperStartIntegral (n m : ℤ) (φ : SourcePotential)
    (p : UpperStartPath m φ) (b : ℂ) : Prop :=
  (∀ ε η : ℝ, 0 < ε → 0 < η → ε+η < 1 →
    IntervalIntegrable (GKRootedArcIntegrand38 n m sourceF (sourceGK φ) p.1.1)
      volume ε 1 ∧
    (∀ a ∈ p.1.2.1, IntervalIntegrable
      (GKRootedArcIntegrand38 n m sourceF (sourceGK φ) a) volume 0 1) ∧
    IntervalIntegrable (GKRootedArcIntegrand38 n m sourceF (sourceGK φ) p.1.2.2)
      volume 0 (1-η)) ∧
  Tendsto (fun q : ℝ × ℝ =>
    (∫ t in q.1..(1 : ℝ), GKRootedArcIntegrand38 n m sourceF (sourceGK φ) p.1.1 t) +
    GKPathMiddleIntegral38 n m sourceF (sourceGK φ) p.1.2.1 +
    (∫ t in (0 : ℝ)..(1-q.2), GKRootedArcIntegrand38 n m sourceF (sourceGK φ) p.1.2.2 t))
    (𝓝[{q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1+q.2 < 1}] (0,0)) (𝓝 b)

end
end NlsGge.GKDefinitionDesign
