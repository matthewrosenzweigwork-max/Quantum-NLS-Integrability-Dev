import Mathlib
import NlsGge.Hierarchy.ContractionMonomialBound38
import NlsGge.Hierarchy.GaussianTailContractionsF06C2_38
import NlsGge.Hierarchy.RiccatiLocalRemainderSobolev38
import NlsGge.Atomic.F.F016

                                                                                                                            
                                                                                                                                                                                                                               
                                                                                                                   
                                                                                           
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.Measure

namespace NlsGge.ThirdConsultation.F
attribute [local instance] Classical.propDecidable

-- covarianceTerm, tailCovariance: already landed in NlsGge/Atomic/F/F016.lean (byte-identical to Pro's text); imported, not redefined.

def tailUnbar (q : Jet →₀ ℕ) (R : Finset (OccType38 q)) :
    Finset (OccType38 q) :=
  (Finset.univ \ R).filter (fun t => occBar38 q t = false)

def tailBar (q : Jet →₀ ℕ) (R : Finset (OccType38 q)) :
    Finset (OccType38 q) :=
  (Finset.univ \ R).filter (fun t => occBar38 q t = true)

def contractionPatterns (q : Jet →₀ ℕ) :
    Finset (Finset (OccType38 q)) :=
  (Finset.univ : Finset (OccType38 q)).powerset.filter
    (fun R => R ≠ Finset.univ ∧
      (tailUnbar q R).card = (tailBar q R).card)

def wickMatchingSum (m : ℕ) (β : ℕ → ℝ) (N : ℕ)
    (q : Jet →₀ ℕ) (R : Finset (OccType38 q)) : ℂ :=
  ∑ σ : (↥(tailUnbar q R) ≃ ↥(tailBar q R)),
    ∏ i : ↥(tailUnbar q R),
      tailCovariance m β N (occOrd38 q i.1) (occOrd38 q (σ i).1)

def contractedMonomial (m : ℕ) (β : ℕ → ℝ) (N j : ℕ)
    (z : FourierPlane N) (q : Jet →₀ ℕ)
    (R : Finset (OccType38 q)) : ℝ :=
  (((normalizedRemainder38 j).coeff q : ℂ) *
    ∫ x in (0 : ℝ)..1,
      (∏ i ∈ R,
        jet38 (occBar38 q) (occOrd38 q) (planeReal N z) i x) *
      wickMatchingSum m β N q R).re

end NlsGge.ThirdConsultation.F
end

#print axioms NlsGge.ThirdConsultation.F.contractedMonomial
