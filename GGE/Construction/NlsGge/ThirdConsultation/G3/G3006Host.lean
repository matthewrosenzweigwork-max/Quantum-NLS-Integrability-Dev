import Mathlib
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import Armstrong.Work.ActualScalarCartesianModels

                                                                              
                                                                                                                                       
                                                                                                                 
                                                                                                                                                  
                                                                                                                                                          
                                                                                                                                                        
                                                                                                              
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

abbrev ComplexAngle := ℂ ⧸ AddSubgroup.zmultiples (2*(Real.pi : ℂ))

def etaExponential (n : ℤ) (φ : PotPair) : ℂ :=
  gk16ActualScalarZPlus38 sourceF n φ / gap φ n

def etaRepresentative (n : ℤ) (φ : PotPair) : ℂ :=
  -Complex.I * Complex.log (etaExponential n φ)

def etaAngle (n : ℤ) (φ : PotPair) : ComplexAngle :=
  QuotientAddGroup.mk (etaRepresentative n φ)

end
end NlsGge.GKDefinitionDesign
