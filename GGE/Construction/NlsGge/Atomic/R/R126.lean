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
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem derivative_approximation_fixed_ball {lo up : ℝ}
    (c : BoundedCoefficients lo up) (s : ℝ) (x : ECarrier38 c s)
    (e : ECarrier38 c s ≃L[ℝ] ECarrier38 c s)
    (he : (e : ECarrier38 c s →L[ℝ] ECarrier38 c s) =
      1 + fderiv ℝ ((B).KE38 O c s) x) :
    ∃ M rho : ℝ, 0 < M ∧ 0 < rho ∧
      ‖(e.symm : ECarrier38 c s →L[ℝ] ECarrier38 c s)‖ ≤ M ∧
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ y : ECarrier38 c s, y ∈ Metric.closedBall x rho →
          ‖(1 + (projE38 c s N).comp (fderiv ℝ ((B).KE38 O c s) y)) -
            (e : ECarrier38 c s →L[ℝ] ECarrier38 c s)‖ ≤ (2 * M)⁻¹ := by
  set M : ℝ := ‖(e.symm : ECarrier38 c s →L[ℝ] ECarrier38 c s)‖ + 1 with hMdef
  have hM : 0 < M := by positivity
  have hcc : 0 < (2 * M)⁻¹ := by positivity
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 ((B).continuousAt_fderiv_KE38 O c s x)
    ((2 * M)⁻¹ / 2) (by positivity)
  obtain ⟨N0, hN0⟩ := (Metric.tendsto_atTop.1 ((B).tendsto_tail_DKE38 O c s x)) ((2 * M)⁻¹ / 2) (by positivity)
  refine ⟨M, δ / 2, hM, by positivity, by linarith, N0, fun N hN y hy => ?_⟩
  have hy' : dist y x < δ := lt_of_le_of_lt (Metric.mem_closedBall.1 hy) (by linarith)
  have h1 : ‖fderiv ℝ ((B).KE38 O c s) y - fderiv ℝ ((B).KE38 O c s) x‖ ≤ (2 * M)⁻¹ / 2 := by
    have := hδ' hy'; rw [dist_eq_norm] at this; exact this.le
  have h2 : ‖fderiv ℝ ((B).KE38 O c s) x - (projE38 c s N).comp (fderiv ℝ ((B).KE38 O c s) x)‖ ≤
      (2 * M)⁻¹ / 2 := by
    have := hN0 N hN
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at this; exact this.le
  have hP := norm_projE38_le c s N
  rw [he]
  have heq : (1 + (projE38 c s N).comp (fderiv ℝ ((B).KE38 O c s) y)) -
      (1 + fderiv ℝ ((B).KE38 O c s) x) =
      (projE38 c s N).comp (fderiv ℝ ((B).KE38 O c s) y - fderiv ℝ ((B).KE38 O c s) x) -
        (fderiv ℝ ((B).KE38 O c s) x - (projE38 c s N).comp (fderiv ℝ ((B).KE38 O c s) x)) := by
    rw [ContinuousLinearMap.comp_sub]; abel
  rw [heq]
  calc ‖(projE38 c s N).comp (fderiv ℝ ((B).KE38 O c s) y - fderiv ℝ ((B).KE38 O c s) x) -
        (fderiv ℝ ((B).KE38 O c s) x - (projE38 c s N).comp (fderiv ℝ ((B).KE38 O c s) x))‖
      ≤ ‖(projE38 c s N).comp (fderiv ℝ ((B).KE38 O c s) y - fderiv ℝ ((B).KE38 O c s) x)‖ +
        ‖fderiv ℝ ((B).KE38 O c s) x - (projE38 c s N).comp (fderiv ℝ ((B).KE38 O c s) x)‖ := norm_sub_le _ _
    _ ≤ ‖projE38 c s N‖ * ‖fderiv ℝ ((B).KE38 O c s) y - fderiv ℝ ((B).KE38 O c s) x‖ + (2 * M)⁻¹ / 2 :=
        add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) h2
    _ ≤ 1 * ((2 * M)⁻¹ / 2) + (2 * M)⁻¹ / 2 := by
        gcongr
    _ = (2 * M)⁻¹ := by ring

end NlsGge.ThirdConsultation.R
