import Mathlib
import NlsGge.ThirdConsultation.PDE.Round14ActionFreq
import NlsGge.ThirdConsultation.Common.Actions
import NlsGge.ThirdConsultation.Common.FiniteSupport
import NlsGge.Birkhoff.BirkhoffAPI38
import NlsGge.ThirdConsultation.PDE.PDE063Core

                                                                                                                          
                                                                                                                                 
                                                                                                             
                                                                                                                     
                                                                                                                   
                                                                                                                 
                                              
                                                                                                                        
                                                                                 
                                                                                                         
                                                                                                    
                                                                                                                      
                                                                                           
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.NLS38 NlsGge.GKDefinitionDesign NlsGge.Atomic.Common
open NlsGge.ThirdConsultation.Common
namespace NlsGge.ThirdConsultation.PDE
noncomputable section

def rotationSequence (z0 : NlsGge.GK38.Lib.L2Z) (t : ℝ) : ℤ → ℂ :=
  fun n : ℤ =>
    Complex.exp (-Complex.I * ((t * actualOmega n (actions z0) : ℝ) : ℂ)) * z0 n

def rotationDerivativeSequence (z0 : NlsGge.GK38.Lib.L2Z) (t : ℝ) : ℤ → ℂ :=
  fun n : ℤ => -Complex.I * (actualOmega n (actions z0) : ℂ) *
    rotationSequence z0 t n

theorem rotationSequence_finiteSupport
    (z0 : NlsGge.GK38.Lib.L2Z) (hz : FiniteSupportSequence z0) (t : ℝ) :
  {n : ℤ | rotationSequence z0 t n ≠ 0}.Finite :=
  PDE063Aux.rot_finite (fun n => actualOmega n (actions z0)) z0 hz t

theorem rotationDerivativeSequence_finiteSupport
    (z0 : NlsGge.GK38.Lib.L2Z) (hz : FiniteSupportSequence z0) (t : ℝ) :
  {n : ℤ | rotationDerivativeSequence z0 t n ≠ 0}.Finite :=
  PDE063Aux.rotDeriv_finite (fun n => actualOmega n (actions z0)) z0 hz t

def rotationCurve (r : ℝ) (z0 : NlsGge.GK38.Lib.L2Z)
    (hz : FiniteSupportSequence z0) (t : ℝ) : SobolevCarrier38 r :=
  carrierMk38 r (rotationSequence z0 t)
    (finiteSupport_mem_seqSobolev38 r _ (rotationSequence_finiteSupport z0 hz t))

def rotationDeriv (r : ℝ) (z0 : NlsGge.GK38.Lib.L2Z)
    (hz : FiniteSupportSequence z0) (t : ℝ) : SobolevCarrier38 r :=
  carrierMk38 r (rotationDerivativeSequence z0 t)
    (finiteSupport_mem_seqSobolev38 r _
      (rotationDerivativeSequence_finiteSupport z0 hz t))

end
end NlsGge.ThirdConsultation.PDE
