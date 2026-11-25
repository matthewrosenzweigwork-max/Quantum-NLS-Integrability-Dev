import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W04WeightedSmoothing38c
import NlsGge.Birkhoff.W07Probability38c
import NlsGge.Birkhoff.W08Compact38
import NlsGge.Birkhoff.W10Localized38b
import NlsGge.Ramer.TruncatedDivergenceLimit
import NlsGge.Ramer.ActualHeadLawBridge
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52
import NlsGge.Analysis.RegularizedDeterminant.IdealAndTransport
import NlsGge.ThirdConsultation.R.R132Core

                                                                                                                      
                                                                                                                           
                                                                                                 
                                                                                                                     
                                                                                                                    
                                                                                                                         
                                                                                                        
                                                                                                                 
                                                                                                                        
                                                                                                                 
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem TN_is_chart_on_ball {lo up : ℝ}
    (c : BoundedCoefficients lo up) (s : ℝ) (hs1 : s ≤ 1)
    (R : ℝ) (hR : 0 < R) :
    ∀ᶠ N : ℕ in atTop,
      let T : actualCMHead c N → actualCMHead c N := (B).TNfin38 O c hs1 N
      let U : Set (actualCMHead c N) := ballU38 c s N (2 * R + 1)
      ∃ S : actualCMHead c N → actualCMHead c N,
        IsOpen U ∧ IsOpen (T '' U) ∧ Set.BijOn T U (T '' U) ∧
        Set.MapsTo S (T '' U) U ∧
        (∀ x : actualCMHead c N, x ∈ U → S (T x) = x) ∧
        (∀ y : actualCMHead c N, y ∈ T '' U → T (S y) = y) ∧
        ContDiffOn ℝ 1 T U ∧ ContDiffOn ℝ 1 S (T '' U) ∧
        (∀ x : actualCMHead c N, x ∈ U → (fderiv ℝ T x).det ≠ 0) := by
  obtain ⟨N₀, hN₀⟩ := (B).eventually_injOn_ballU38 O c hs1 (2 * R + 1)
  filter_upwards [((B).eventually_det_ballU38 O c hs1 (2 * R + 1)).1, eventually_ge_atTop N₀]
    with N hdet hN
  intro T U
  have hTc : ContDiff ℝ 1 T := by
    show ContDiff ℝ 1 (fun w => w + truncField c s ((B).KW06_38 O c hs1) N w)
    exact contDiff_id.add ((contDiff_truncField c s _ ((B).contDiff_KW06_W07 O c hs1) N).of_le
      (by norm_num))
  obtain ⟨S, h1, h2, h3, h4, h5, h6, h7⟩ := NlsGge.Birkhoff.R132Aux.chart_of T hTc U
    (isOpen_ballU38 c s N (2 * R + 1)) (hN₀ N hN) (fun x hx => (hdet x hx).1)
  exact ⟨S, isOpen_ballU38 c s N (2 * R + 1), h1, h2, h3, h4, h5, h6, h7, fun x hx => (hdet x hx).1⟩

end NlsGge.ThirdConsultation.R
