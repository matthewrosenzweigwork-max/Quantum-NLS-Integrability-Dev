import Mathlib
import NlsGge.ThirdConsultation.G3.G3003Host
import NlsGge.GK38.Lib.EntireProductsC34b
import Armstrong.Work.RawBetaSumSpectralMass

                                                                              
                                                                                                                               
                                                                                                                                                    
                                                                                                                                                    
                                                                                                                                
                                                                                                          
                                                                                                                                   
                                                                                                                                                  
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def spectralNorm (φ : PotPair) : ℝ :=
  Real.sqrt (∑' m : ℤ, ‖gk151BetaMass38 φ m‖^2)

def spectralTailNorm (φ : PotPair) (R : ℝ) : ℝ :=
  Real.sqrt (∑' m : ℤ, if R ≤ |(m : ℝ)| then ‖gk151BetaMass38 φ m‖^2 else 0)

def reciprocalSquareTail (R : ℝ) : ℝ :=
  Real.sqrt (∑' k : ℤ, if R < |(k : ℝ)| then Lib.c3w 0 k ^ 2 else 0)

def nearDiagonalBetaNorm (n : ℤ) (φ : PotPair) (m : ℤ) : ℝ :=
  if 0 < |(m : ℝ)-n| ∧ |(m : ℝ)-n| ≤ |(n : ℝ)|/2
  then ‖offDiagonalBeta n m φ‖ else 0

def farDiagonalBetaNorm (n : ℤ) (φ : PotPair) (m : ℤ) : ℝ :=
  if |(n : ℝ)|/2 < |(m : ℝ)-n| then ‖offDiagonalBeta n m φ‖ else 0

end
end NlsGge.GKDefinitionDesign
