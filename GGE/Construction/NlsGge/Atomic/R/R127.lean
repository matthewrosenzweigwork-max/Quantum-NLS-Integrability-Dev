import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W09Approx38
import NlsGge.Birkhoff.W09Approx38b
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52
import NlsGge.Analysis.RegularizedDeterminant.IdealAndTransport

                                                                                                  
                                                                                                                    
                                                                                                          
                                                                                                          
                                                                                                                
                                                                                                                  
                                                                                                             
                                                                                   
                                                                                                                      
                                                                                                                 
                                                                                                                    
                                                                                  
                                                                                                                  
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open scoped NNReal
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem near_linearity_on_fixed_ball {lo up : ℝ}
    (c : BoundedCoefficients lo up) (s : ℝ) (x : ECarrier38 c s)
    (e : ECarrier38 c s ≃L[ℝ] ECarrier38 c s)
    (M rho : ℝ) (hM : 0 < M) (hrho : 0 ≤ rho) (N : ℕ)
    (hder : ∀ y : ECarrier38 c s, y ∈ Metric.closedBall x rho →
      ‖(1 + (projE38 c s N).comp (fderiv ℝ ((B).KE38 O c s) y)) -
        (e : ECarrier38 c s →L[ℝ] ECarrier38 c s)‖ ≤ (2 * M)⁻¹) :
    ApproximatesLinearOn
      (fun y : ECarrier38 c s => y + projE38 c s N ((B).KE38 O c s y))
      (e : ECarrier38 c s →L[ℝ] ECarrier38 c s) (Metric.closedBall x rho)
      (⟨(2 * M)⁻¹, (by positivity)⟩ : ℝ≥0) := by
  intro y hy y' hy'
  have hd : ∀ z ∈ Metric.closedBall x rho, HasFDerivWithinAt
      (fun w => (w + projE38 c s N ((B).KE38 O c s w)) - (e : ECarrier38 c s →L[ℝ] ECarrier38 c s) w)
      ((1 + (projE38 c s N).comp (fderiv ℝ ((B).KE38 O c s) z)) -
        (e : ECarrier38 c s →L[ℝ] ECarrier38 c s)) (Metric.closedBall x rho) z := by
    intro z _
    have h1 : HasFDerivAt (fun w => projE38 c s N ((B).KE38 O c s w))
        ((projE38 c s N).comp (fderiv ℝ ((B).KE38 O c s) z)) z :=
      (projE38 c s N).hasFDerivAt.comp z ((B).differentiableAt_KE38 O c s z).hasFDerivAt
    exact (((hasFDerivAt_id z).add h1).sub
      (e : ECarrier38 c s →L[ℝ] ECarrier38 c s).hasFDerivAt).hasFDerivWithinAt
  have key := (convex_closedBall x rho).norm_image_sub_le_of_norm_hasFDerivWithin_le hd hder hy' hy
  have e3 : (y + projE38 c s N ((B).KE38 O c s y)) - (y' + projE38 c s N ((B).KE38 O c s y')) -
      (e : ECarrier38 c s →L[ℝ] ECarrier38 c s) (y - y') =
      ((y + projE38 c s N ((B).KE38 O c s y)) - (e : ECarrier38 c s →L[ℝ] ECarrier38 c s) y) -
        ((y' + projE38 c s N ((B).KE38 O c s y')) - (e : ECarrier38 c s →L[ℝ] ECarrier38 c s) y') := by
    rw [map_sub]; abel
  show ‖(y + projE38 c s N ((B).KE38 O c s y)) - (y' + projE38 c s N ((B).KE38 O c s y')) -
      (e : ECarrier38 c s →L[ℝ] ECarrier38 c s) (y - y')‖ ≤ (2 * M)⁻¹ * ‖y - y'‖
  rw [e3]
  exact key

end NlsGge.ThirdConsultation.R
