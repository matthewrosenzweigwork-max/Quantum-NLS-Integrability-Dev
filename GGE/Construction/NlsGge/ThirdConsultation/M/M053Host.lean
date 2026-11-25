import Mathlib
import NlsGge.GK38.Defs
import NlsGge.ThirdConsultation.KSPSInversePhaseHost
import NlsGge.Hierarchy.RiccatiAttachedRecursionCore
import NlsGge.Hierarchy.RiccatiPolynomialEvaluationAPI

                                                              
                                                   
                                                                                                
                                                                                          
                                                                                                          
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace NlsGge.ThirdConsultation.MRiccati
noncomputable section

abbrev HierarchyIndex (N : ℕ) :=
  {k : ℕ // 1 ≤ k ∧ k ≤ N + 1}

def realPhysicalFromPair {N : ℕ}
    (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N) :
    NlsGge.Pilot.PhysicalL2 :=
  (NlsGge.ThirdConsultation.KSPS.toPotPair φ).1

def RealPair {N : ℕ}
    (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N) : Prop :=
  NlsGge.ThirdConsultation.KSPS.toPotPair φ =
    NlsGge.GK38.realSlice (realPhysicalFromPair φ)

private def sourceHierarchyJet {N : ℕ}
    (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N)
    (x : ℝ) (v : NlsGge.HierarchyRiccati.Core.Jet) : ℂ :=
  NlsGge.GK38.coverRep38
    ((NlsGge.GKDefinitionDesign.weakDerivative^[v.2])
      (if v.1 then (NlsGge.ThirdConsultation.KSPS.toPotPair φ).2
       else (NlsGge.ThirdConsultation.KSPS.toPotPair φ).1)) x

def sourceHierarchyCharge (N : ℕ)
    (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N)
    (k : HierarchyIndex N) : ℂ :=
  if k.1 = 1 then
    ∫ x in (0 : ℝ)..1,
      NlsGge.GK38.coverRep38
        (NlsGge.ThirdConsultation.KSPS.toPotPair φ).1 x *
      NlsGge.GK38.coverRep38
        (NlsGge.ThirdConsultation.KSPS.toPotPair φ).2 x
  else
    ∫ x in (0 : ℝ)..1,
      NlsGge.GK38.coverRep38
        (NlsGge.ThirdConsultation.KSPS.toPotPair φ).1 x *
      NlsGge.HierarchyRiccati.Core.polynomialEvaluation
        (sourceHierarchyJet φ x)
        (NlsGge.HierarchyRiccati.Core.p k.1)

end
end NlsGge.ThirdConsultation.MRiccati

namespace NlsGge.ThirdConsultation.M
noncomputable section

def massCharge (u : NlsGge.Pilot.PhysicalL2) : ℝ := ‖u‖ ^ 2

def hierarchyCharge {N : ℕ}
    (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N)
    (k : NlsGge.ThirdConsultation.MRiccati.HierarchyIndex N) : ℂ :=
  NlsGge.ThirdConsultation.MRiccati.sourceHierarchyCharge N φ k

end
end NlsGge.ThirdConsultation.M
