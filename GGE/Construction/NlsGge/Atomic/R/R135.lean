import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.F01Determinant38c
import NlsGge.Birkhoff.W09Approx38b
import NlsGge.Birkhoff.W10Localized38e
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52
import NlsGge.Analysis.RegularizedDeterminant.IdealAndTransport

                                                                                                  
                                                                                                                    
                                                                                                                        
                                                                                                        
                                                                                                                
                                                                                                          
                                                                
                                                                                                             
                                                                                                                    
                                                                                                                     
                                                                                                                    
                                                                                                 
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem r135_main {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) (hs1 : s ≤ 1) (N : ℕ) (z : FullWeightedHilbert c s)
    (v : actualCMHead c N) :
    (B).GalerkinSol38 N (eCoe38 c s z) (eCoe38 c s (headToE c s N v)) ↔
      (B).TNfin38 O c hs1 N v = headPt c N (coordE c s z) :=
  (B).galerkin_iff_TNfin38 O c hs1 N z v

theorem r135_2 {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) (hs1 : s ≤ 1) (z : FullWeightedHilbert c s)
    (xN : ℕ → FullWeightedHilbert c s) (R' R'' : ℝ) (hle : R' ≤ R'') (N₀ : ℕ)
    (huniq : ∀ N ≥ N₀, ∀ y : H2_38, ‖y‖ ≤ R'' →
      (B).GalerkinSol38 N (eCoe38 c s z) (carrierCoe38 (((1 + 1 : ℕ)) : ℝ) y) →
      carrierCoe38 (((1 + 1 : ℕ)) : ℝ) y = eCoe38 c s (xN N))
    (N : ℕ) (hN : N ≥ N₀) (hsol : (B).GalerkinSol38 N (eCoe38 c s z) (eCoe38 c s (xN N)))
    (w : actualCMHead c N) (hw : w ∈ ballU38 c s N R')
    (hφ : (B).TNfin38 O c hs1 N w = headPt c N (coordE c s z)) :
    w = headPt c N (coordE c s (xN N)) :=
  (B).unique_preimage_W10 O c hs1 z xN R' R'' hle N₀ huniq N hN hsol w hw hφ

end NlsGge.ThirdConsultation.R
