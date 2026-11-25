import Mathlib
import NlsGge.ThirdConsultation.R.RamerSetting06
import NlsGge.Ramer.RamerStep4

                                                                                                           
                                                                                                            
                                                                                                               
                                                                                                 
                                                                                                             
                                                                                                           
                                                                                                             
                                                                                                              
                                                                                                   
                                                                                             
                                                           
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Metric Filter MeasureTheory
open scoped Topology ENNReal BigOperators RealInnerProductSpace

namespace NlsGge.ThirdConsultation.R
noncomputable section

section R043Production
variable {lower upper : ℝ}
variable (c : NlsGge.Pilot.BoundedCoefficients lower upper)
variable (s : ℝ) (hs : (1 : ℝ) / 2 < s)

local notation "E" => RamerE c s
local notation "H" => RamerH c
local notation "μ" => ramerGaussian c s
local notation "i" => cmEmbedding c s hs

theorem ramer_step4
    (T : E ≃ₜ E) (K Kinv : E → H)
    (hT : RamerHomeomorphismData c s hs T K Kinv) (x₀ : E) :
    ∃ chart : NormalizationChart c s,
      NormalizedSmallDerivativeChart c s hs T K Kinv x₀ chart := by
  obtain ⟨hK, hKi, hTK, hTKi⟩ := hT
  have hs0 : 0 ≤ s := le_of_lt (by linarith : (0 : ℝ) < s)
  have hT' : ∀ x : E, T x = x + i (K x) := fun x => hTK x
  have hTi' : ∀ y : E, T.symm y = y + i (Kinv y) := fun y => hTKi y
  have hinj : Function.Injective i :=
    NlsGge.Ramer.cmToFullWeightedHilbert_injective c s hs0
  have hKd : Differentiable ℝ K := hK.differentiable (by norm_num)
  have hKid : Differentiable ℝ Kinv := hKi.differentiable (by norm_num)
  obtain ⟨Tt, hTt, hTts, hv⟩ :=
    NlsGge.Ramer.exists_linearization i hinj T K Kinv hT' hTi'
      hKd hKid x₀
  obtain ⟨ε, hε, d, hd, e₁, e₂, he₂, hid, hKb, hHb, hH8, -, hy0, hz⟩ :=
    NlsGge.Ramer.ramer_step4_core c s hs T K hT' (hK.of_le (by norm_num)) x₀ Tt
      (fderiv ℝ Kinv (T x₀)) hTts hv
  subst he₂
  have hGeq := NlsGge.Ramer.K2_eq_Gmap i T K hT'
    (fderiv ℝ Kinv (T x₀)) x₀ e₁
  refine ⟨⟨Tt, e₁, -e₁ + K x₀ + fderiv ℝ Kinv (T x₀) (T x₀), ε, d⟩, hε, hd, hTt, hTts, rfl, hid, hy0, hz, ?_, ?_⟩
  · -- HDeriv = 0
    have hnf : normalizedField c s hs T K Kinv x₀ ⟨Tt, e₁, -e₁ + K x₀ + fderiv ℝ Kinv (T x₀) (T x₀), ε, d⟩ =
        fun y => NlsGge.Ramer.Gmap i K (fderiv ℝ Kinv (T x₀)) x₀
          (y - i e₁) := hGeq
    rw [hnf]
    apply ContinuousLinearMap.ext
    intro v
    unfold HDeriv
    have hcs := fderiv_comp_sub (𝕜 := ℝ)
      (f := NlsGge.Ramer.Gmap i K (fderiv ℝ Kinv (T x₀)) x₀)
      (x := x₀ + i e₁) (i e₁)
    have e : x₀ + i e₁ - i e₁ = x₀ := by
      abel
    rw [hcs, e]
    exact (NlsGge.Ramer.fderiv_Gmap_comp_zero i K
      (fderiv ℝ Kinv (T x₀)) x₀ (hKd x₀) hv v).trans (ContinuousLinearMap.zero_apply v).symm
  · intro y hy
    have hy' : ‖y‖ < ε := by simpa using hy
    exact ⟨hKb y hy', hHb y hy', hH8 y hy'⟩

end R043Production

end
end NlsGge.ThirdConsultation.R
