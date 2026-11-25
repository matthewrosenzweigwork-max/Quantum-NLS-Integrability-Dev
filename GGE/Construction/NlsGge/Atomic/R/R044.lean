import Mathlib
import NlsGge.ThirdConsultation.R.RamerSetting06
import NlsGge.Atomic.R.R032
import NlsGge.Ramer.RamerStep7
import NlsGge.Ramer.LinearDecomposition
import NlsGge.Ramer.TruncatedFieldConvergence
import NlsGge.Sobolev.PhysicalProjection

                                                                                                           
                                                                                                              
                                                                                               
                                                                                                                    
                                                                                                             
         
                                                                                                                   
                                                                                            
                                                                                                               
                                                                                                                    
                                                                                                                
                                                                                       
                                                                                                     
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Metric Filter MeasureTheory
open scoped Topology ENNReal BigOperators RealInnerProductSpace

namespace NlsGge.ThirdConsultation.R
noncomputable section

section R044Production
variable {lower upper : ℝ}
variable (c : NlsGge.Pilot.BoundedCoefficients lower upper)
variable (s : ℝ) (hs : (1 : ℝ) / 2 < s)

local notation "E" => RamerE c s
local notation "H" => RamerH c
local notation "μ" => ramerGaussian c s
local notation "i" => cmEmbedding c s hs
local notation "P" => NlsGge.Ramer.headProj c

/-- R-044 helper: the complementary coordinate projection `1 - P m` is a contraction on the Cameron-Martin
space (Pythagoras for the orthogonal projection `P m`). -/
theorem r044_norm_sub_headProj_le (m : ℕ) (w : H) : ‖w - P m w‖ ≤ ‖w‖ := by
  have hres := NlsGge.Pilot.weightedRealProjection_range_residual
    (NlsGge.Pilot.cmModeWeight c) (NlsGge.Pilot.symmetricModes m) w w
  have hP : P m w =
      NlsGge.Pilot.weightedRealProjectionContinuous (NlsGge.Pilot.cmModeWeight c)
        (NlsGge.Pilot.symmetricModes m) w := rfl
  rw [← hP] at hres
  have hpy : ‖P m w + (w - P m w)‖ * ‖P m w + (w - P m w)‖ =
      ‖P m w‖ * ‖P m w‖ + ‖w - P m w‖ * ‖w - P m w‖ :=
    norm_add_sq_eq_norm_sq_add_norm_sq_real hres
  have hw : P m w + (w - P m w) = w := by abel
  rw [hw] at hpy
  nlinarith [norm_nonneg (P m w), norm_nonneg (w - P m w), norm_nonneg w, mul_self_nonneg ‖P m w‖]

theorem PiMap_sub_mem_range
    (K₂ L : E → H) (m : ℕ) (ε : ℝ)
    (hL : ∀ y : E, L y = K₂ y - P m (K₂ y))
    (hStep : NlsGge.Ramer.Step7Hyp i L ε)
    (Sinv : E → E) (hSinv : IsSmallInverse c s hs L ε Sinv) :
    ∀ z ∈ ball (0 : E) (ε / 2),
      (Sinv z + i (K₂ (Sinv z))) - z =
        i (P m (K₂ (Sinv z))) ∧
      (Sinv z + i (K₂ (Sinv z))) - z ∈
        LinearMap.range ((i).comp (P m)).toLinearMap := by
  intro z hz
  obtain ⟨-, hS⟩ := hSinv z hz
  have key : (Sinv z + i (K₂ (Sinv z))) - z = i (P m (K₂ (Sinv z))) := by
    generalize Sinv z = x at hS ⊢
    rw [hL x] at hS
    rw [← hS, map_sub]
    abel
  refine ⟨key, ?_⟩
  rw [key]
  exact ⟨K₂ (Sinv z), rfl⟩

theorem exists_small_finiteRank_split
    (K₂ : E → H) (ε M : ℝ) (hε : 0 < ε) (hM : 0 < M)
    (hK : ContDiff ℝ 2 K₂)
    (hB : ∀ y ∈ closedBall (0 : E) ε, ‖K₂ y‖ ≤ M)
    (hD : ∀ y ∈ closedBall (0 : E) ε,
      ‖HDeriv i K₂ y‖ ≤ (1 / 2 : ℝ)) :
    ∃ m : ℕ,
      SmallFibreField c s hs (fun y : E => K₂ y - P m (K₂ y)) ε := by
  have hs' : 0 < s := by linarith
  have hKd : Differentiable ℝ K₂ := hK.differentiable (by norm_num)
  obtain ⟨m, hm⟩ := NlsGge.ThirdConsultation.R.exists_tail_small c s hs' M (ε / 4) hM (by positivity)
  refine ⟨m, hε, fun y _ => (hKd y).sub ((P m).differentiableAt.comp y (hKd y)), fun y hy => ?_,
    fun y hy => ?_⟩
  · exact hm (K₂ y) (hB y hy)
  · have hd : HasFDerivAt (fun y : E => K₂ y - P m (K₂ y)) _ y := (hKd y).hasFDerivAt.sub
      ((P m).hasFDerivAt.comp y (hKd y).hasFDerivAt)
    have hDK := hD y hy
    refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun h => ?_)
    have hval : fderiv ℝ (fun y : E => K₂ y - P m (K₂ y)) y (i h) =
        fderiv ℝ K₂ y (i h) - P m (fderiv ℝ K₂ y (i h)) :=
      congrArg (fun L => L (i h)) hd.fderiv
    have h1 : ‖fderiv ℝ K₂ y (i h)‖ ≤ 1 / 2 * ‖h‖ :=
      ((HDeriv i K₂ y).le_opNorm h).trans (mul_le_mul_of_nonneg_right hDK (norm_nonneg h))
    have h2 := r044_norm_sub_headProj_le c m (fderiv ℝ K₂ y (i h))
    show ‖fderiv ℝ (fun y : E => K₂ y - P m (K₂ y)) y (i h)‖ ≤ 1 / 2 * ‖h‖
    rw [hval]
    exact h2.trans h1

end R044Production

end
end NlsGge.ThirdConsultation.R
