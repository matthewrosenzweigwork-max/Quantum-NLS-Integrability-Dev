import Mathlib
import NlsGge.Atomic.R.R027
import NlsGge.Atomic.R.R028
import NlsGge.ThirdConsultation.R.RamerSetting06B

                                                                                                           
                                                                                                                        
                                                                                    
                                                                                                                              
                                                                                                                           
                                         
                                                                                                                       
                                                                                                                       
                                                                               
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Metric Filter MeasureTheory
open scoped Topology ENNReal BigOperators RealInnerProductSpace

namespace NlsGge.ThirdConsultation.R
noncomputable section
section R029Main
variable {lower upper : ℝ}
variable (c : NlsGge.Pilot.BoundedCoefficients lower upper)
variable (s : ℝ) (hs : (1 : ℝ) / 2 < s)

local notation "E" => RamerE c s
local notation "H" => RamerH c
local notation "μ" => ramerGaussian c s

/-- **R-029, existence part** (Pro round 6 head, lexical repair only). -/
theorem exists_v2_local_closedDivergence
    (K : E → H) (hK : ContDiff ℝ 2 K) :
    ∃ d : E → ℝ,
      V2LocalClosedDivergence c s K d ∧
      LocalRamerApproxLimit c s hs K d ∧
      ∀ x₀ : E, ∃ r : ℝ, 0 < r ∧
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
          ∀ᵐ x ∂((μ).restrict (ball x₀ r)),
            Tendsto (fun j : ℕ => ramerApprox c s hs K (φ j) x)
              atTop (𝓝 (d x)) := by
  obtain ⟨d, hV, hL⟩ := NlsGge.ThirdConsultation.R.divergence_identification c s hs K hK
  refine ⟨d, hV, hL, fun x₀ => ?_⟩
  obtain ⟨r, hr, hL1, -⟩ := hL x₀
  have hconv : TendstoInMeasure (ramerGaussian c s)
      (fun N : ℕ => (ball x₀ r).indicator (fun x : E => ramerApprox c s hs K N x - d x))
      atTop (0 : E → ℝ) := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) ?_
    simp only [sub_zero]
    exact hL1
  obtain ⟨φ, hφ, hae⟩ := hconv.exists_seq_tendsto_ae
  refine ⟨r, hr, φ, hφ, ?_⟩
  rw [ae_restrict_iff' measurableSet_ball]
  filter_upwards [hae] with x hx hxS
  have h2 : Tendsto (fun j : ℕ => ramerApprox c s hs K (φ j) x - d x) atTop (𝓝 0) := by
    refine hx.congr (fun j => ?_)
    simp only [Set.indicator_of_mem hxS]
  have h3 := h2.add_const (d x)
  simp only [sub_add_cancel, zero_add] at h3
  exact h3

-- R-029 uniqueness part (Pro round 6 head, lexical repair only; `hs` included as in R-027, `include` must precede the docstring).
include hs in
/-- **R-029, uniqueness part** -/
theorem v2_divergence_unique
    (K : E → H) (hK : ContDiff ℝ 2 K) (d₁ d₂ : E → ℝ)
    (hd₁ : V2LocalClosedDivergence c s K d₁)
    (hd₂ : V2LocalClosedDivergence c s K d₂) :
    d₁ =ᵐ[μ] d₂ := by
  obtain ⟨-, h₁⟩ := hd₁
  obtain ⟨-, h₂⟩ := hd₂
  have h := NlsGge.ThirdConsultation.R.local_closedDiv_eq c s hs K K d₁ d₂ Set.univ hK hK
    (fun _ _ => rfl) isOpen_univ h₁ h₂
  rwa [Measure.restrict_univ] at h

end R029Main
end
end NlsGge.ThirdConsultation.R
