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

theorem solve_projected_residual {lo up : ℝ}
    (c : BoundedCoefficients lo up) (s : ℝ) (x : ECarrier38 c s)
    (e : ECarrier38 c s ≃L[ℝ] ECarrier38 c s) (M rho : ℝ)
    (hM : 0 < M) (hrho : 0 < rho)
    (hinv : ‖(e.symm : ECarrier38 c s →L[ℝ] ECarrier38 c s)‖ ≤ M)
    (N : ℕ)
    (heps : 2 * M * ‖x - projE38 c s N x‖ ≤ rho)
    (happ : ApproximatesLinearOn
      (fun y : ECarrier38 c s => y + projE38 c s N ((B).KE38 O c s y))
      (e : ECarrier38 c s →L[ℝ] ECarrier38 c s) (Metric.closedBall x rho)
      (⟨(2 * M)⁻¹, (by positivity)⟩ : ℝ≥0)) :
    ∃ y : ECarrier38 c s,
      ‖y - x‖ ≤ 2 * M * ‖x - projE38 c s N x‖ ∧
      y + projE38 c s N ((B).KE38 O c s y) =
        projE38 c s N (x + (B).KE38 O c s x) ∧ projE38 c s N y = y := by
  set f : ECarrier38 c s → ECarrier38 c s := fun y => y + projE38 c s N ((B).KE38 O c s y) with hf
  set P := projE38 c s N
  set ε : ℝ := 2 * M * ‖x - P x‖ with hε
  have hε0 : 0 ≤ ε := by positivity
  let f'symm : (e : ECarrier38 c s →L[ℝ] ECarrier38 c s).NonlinearRightInverse :=
    { toFun := e.symm
      nnnorm := ⟨M, hM.le⟩
      bound' := fun y => by
        calc ‖e.symm y‖ ≤ ‖(e.symm : ECarrier38 c s →L[ℝ] ECarrier38 c s)‖ * ‖y‖ :=
              (e.symm : ECarrier38 c s →L[ℝ] ECarrier38 c s).le_opNorm y
          _ ≤ M * ‖y‖ := mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
      right_inv' := fun y => e.apply_symm_apply y }
  have hsub : Metric.closedBall x ε ⊆ Metric.closedBall x rho := Metric.closedBall_subset_closedBall heps
  have hsurj := happ.surjOn_closedBall_of_nonlinearRightInverse f'symm hε0 hsub
  have hmem : P (x + (B).KE38 O c s x) ∈
      Metric.closedBall (f x) (((f'symm.nnnorm : ℝ)⁻¹ - (2 * M)⁻¹) * ε) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have e4 : P (x + (B).KE38 O c s x) - f x = P x - x := by
      simp only [hf, map_add]; abel
    rw [e4, norm_sub_rev]
    have e5 : ((f'symm.nnnorm : ℝ)⁻¹ - (2 * M)⁻¹) * ε = ‖x - P x‖ := by
      show (M⁻¹ - (2 * M)⁻¹) * (2 * M * ‖x - P x‖) = _
      field_simp
      ring
    rw [e5]
  obtain ⟨y, hy, hfy⟩ := hsurj hmem
  refine ⟨y, ?_, hfy, ?_⟩
  · rw [Metric.mem_closedBall, dist_eq_norm] at hy; exact hy
  · have h1 : P y + P ((B).KE38 O c s y) = P (x + (B).KE38 O c s x) := by
      have hidem : ∀ z, P (P z) = P z := fun z => projE38_idem c s N z
      have := congrArg P hfy
      simp only [hf, map_add, hidem] at this ⊢
      exact this
    have h2 : y + P ((B).KE38 O c s y) = P (x + (B).KE38 O c s x) := hfy
    exact add_right_cancel (h1.trans h2.symm)

end NlsGge.ThirdConsultation.R
