import Mathlib
import NlsGge.Atomic.R.R018
import NlsGge.Atomic.R.R023

                                                                                                                 
                                                                                
                                                                                                        
                                                                                                               
                     
                                                                                                                      
                                                                                                          
set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology ENNReal BigOperators RealInnerProductSpace

namespace NlsGge.ThirdConsultation.R
noncomputable section

/-- The actual finite-dimensional HS norm, represented as a nonnegative real. -/
def hsDeriv
    (d : ℕ) (F : GaussianFiniteCarrier d → GaussianFiniteCarrier d)
    (x : GaussianFiniteCarrier d) : ℝ :=
  Real.sqrt (NlsGge.Ramer.hsNormSq (fderiv ℝ F x))

/-- Finite C² Gaussian L² graph core on a level-`N` head (Pro round 6, verbatim). -/
def GaussianL2CylindricalCore
    {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (N : ℕ)
    (f : NlsGge.Ramer.actualCMHead c N →
      NlsGge.Ramer.actualCMHead c N) : Prop :=
  ContDiff ℝ 2 f ∧
    MemLp f 2
      (NlsGge.Ramer.finiteStdGaussian (NlsGge.Ramer.actualCMHead c N)) ∧
    MemLp (NlsGge.Ramer.finiteGaussianDivergence f) 2
      (NlsGge.Ramer.finiteStdGaussian (NlsGge.Ramer.actualCMHead c N))

/-- H-valued cylinder of a level-`N` field, on the actual space `E_s` (Pro round 6, verbatim). -/
def cylFieldE
    {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (N : ℕ)
    (f : NlsGge.Ramer.actualCMHead c N →
      NlsGge.Ramer.actualCMHead c N)
    (x : RamerE c s) : RamerH c :=
  NlsGge.Ramer.cylField c N f (NlsGge.Ramer.coordE c s x)

/-- Scalar cylinder divergence on `E_s` (Pro round 6, verbatim). -/
def cylDivE
    {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (N : ℕ)
    (f : NlsGge.Ramer.actualCMHead c N →
      NlsGge.Ramer.actualCMHead c N)
    (x : RamerE c s) : ℝ :=
  NlsGge.Ramer.cylDiv c N f (NlsGge.Ramer.coordE c s x)

end
end NlsGge.ThirdConsultation.R
