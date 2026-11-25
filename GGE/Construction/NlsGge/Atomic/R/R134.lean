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

theorem r134_main {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) (hs' : s < 3 / 4) (hs1 : s ≤ 1) {χ : ℝ → ℝ} {R : ℝ}
    (hχ : CutoffProfile38 χ) (hR : 0 < R) (F : PhysicalL2 → ℝ) (M : ℝ)
    (hM : ∀ y : ECarrier38 c s, |F (physOfE38 c s y)| ≤ M) (N : ℕ)
    (hdet : ∀ v ∈ ballU38 c s N (2 * R + 1),
      (fderiv ℝ ((B).TNfin38 O c hs1 N) v).det ≠ 0 ∧
        |(fderiv ℝ ((B).TNfin38 O c hs1 N) v).det|⁻¹ ≤ 2)
    (hinj : Set.InjOn ((B).TNfin38 O c hs1 N) (ballU38 c s N (2 * R + 1))) (z : actualCMHead c N) :
    |(B).PsiN38 O c hs1 χ R F N z| ≤ 2 * M :=
  BirkhoffInput38.abs_PsiN38_le B O c hs' hs1 hχ hR F M hM N hdet hinj z

end NlsGge.ThirdConsultation.R
