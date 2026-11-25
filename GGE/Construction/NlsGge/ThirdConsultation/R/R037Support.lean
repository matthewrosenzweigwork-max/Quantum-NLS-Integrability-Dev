import Mathlib
import NlsGge.ThirdConsultation.R.RamerSetting06
import NlsGge.Ramer.RamerStep8b
import NlsGge.Ramer.RamerJacobianHead
import NlsGge.Ramer.SpaceTransfer

                                                                                     
                                                                                     
                                                                           
                                                                                                                 
                                                                                                            
                                           
                                                                                                                     
                                                              
                                                                                   
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Metric Filter MeasureTheory
open scoped Topology ENNReal BigOperators RealInnerProductSpace

namespace NlsGge.ThirdConsultation.R
noncomputable section

section Step8bSupport
variable {lower upper : ℝ}
variable (c : NlsGge.Pilot.BoundedCoefficients lower upper)
variable (s : ℝ) (hs : (1 : ℝ) / 2 < s)

theorem tendsto_ramerJn_ramerJac_of_tendsto
    (L : RamerE c s → RamerH c) (hL : ContDiff ℝ 2 L)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (x : RamerE c s)
    (hx : Tendsto (fun j : ℕ =>
        NlsGge.Ramer.ramerA c s (NlsGge.Ramer.zero_le_of_half_lt hs) (φ j) L
          (NlsGge.Ramer.coordE c s x))
      atTop (𝓝 (NlsGge.Ramer.ramerDiv c s hs L (NlsGge.Ramer.coordE c s x)))) :
    Tendsto (fun j : ℕ => NlsGge.Ramer.ramerJn c s (φ j) hs L x) atTop
      (𝓝 (ramerJac c s hs L x)) := by
  have hLd : Differentiable ℝ L := hL.differentiable (by norm_num)
  have tdet := (NlsGge.Ramer.tendsto_det2_headProj c s hs L hLd x).comp hφ.tendsto_atTop
  have tn : Tendsto (fun j : ℕ => ‖NlsGge.Ramer.headProj c (φ j) (L x)‖ ^ 2 / 2) atTop
      (𝓝 (‖L x‖ ^ 2 / 2)) :=
    ((((NlsGge.Ramer.headProj_tendsto c (L x)).comp hφ.tendsto_atTop).norm).pow 2).div_const 2
  unfold ramerJac
  simp_rw [NlsGge.Ramer.ramerJn_eq]
  exact tdet.abs.mul (Real.continuous_exp.tendsto _ |>.comp ((hx.neg).sub tn))

theorem ae_tendsto_ramerA_ramerDiv
    (L : RamerE c s → RamerH c) (hL : ContDiff ℝ 2 L) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ x ∂(ramerGaussian c s),
        Tendsto (fun j : ℕ =>
            NlsGge.Ramer.ramerA c s (NlsGge.Ramer.zero_le_of_half_lt hs) (φ j) L
              (NlsGge.Ramer.coordE c s x))
          atTop (𝓝 (NlsGge.Ramer.ramerDiv c s hs L (NlsGge.Ramer.coordE c s x))) := by
  obtain ⟨-, ⟨φ, hφ, hlim⟩, -⟩ := NlsGge.Ramer.ramerDiv_spec c s hs L hL
  exact ⟨φ, hφ, NlsGge.Ramer.ae_of_ae_coordE c s hs hlim⟩

end Step8bSupport

end
end NlsGge.ThirdConsultation.R
