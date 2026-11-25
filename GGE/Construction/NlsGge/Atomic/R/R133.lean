import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W10Localized38d
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

theorem r133_main {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) {χ : ℝ → ℝ} {R : ℝ}
    (hχ : CutoffProfile38 χ) (hR : 0 < R) (F : PhysicalL2 → ℝ)
    (hF : Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y))) (M : ℝ)
    (hM : ∀ y : ECarrier38 c s, |F (physOfE38 c s y)| ≤ M) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      Set.InjOn ((B).TNfin38 O c (by linarith : s ≤ 1) N) (ballU38 c s N (2 * R + 1)) ∧
      (∀ v ∈ ballU38 c s N (2 * R + 1),
        (fderiv ℝ ((B).TNfin38 O c (by linarith : s ≤ 1) N) v).det ≠ 0 ∧
          |(fderiv ℝ ((B).TNfin38 O c (by linarith : s ≤ 1) N) v).det|⁻¹ ≤ 2) ∧
      Measurable ((B).PsiN38 O c (by linarith : s ≤ 1) χ R F N) ∧
      (∀ z, |(B).PsiN38 O c (by linarith : s ≤ 1) χ R F N z| ≤ 2 * M) ∧
      ∫ x, locIntegrand38 c χ R F N x ∂(fullWeightedSequenceGaussian c s) =
        ∫ x, (B).PsiN38 O c (by linarith : s ≤ 1) χ R F N (headPt c N (coordE c s x))
          ∂(fullWeightedSequenceGaussian c s) :=
  BirkhoffInput38.W10a_localChange38 B O c hs hs' hχ hR F hF M hM

end NlsGge.ThirdConsultation.R
