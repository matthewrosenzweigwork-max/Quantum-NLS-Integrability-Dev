import Mathlib
import NlsGge.ThirdConsultation.R.R021Support2
import NlsGge.Ramer.CylinderSeparation

                                                                                                                
                                                                                                           
                                                                                                          
                                                                                                         
                                                                                      
set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory Filter
open scoped Topology RealInnerProductSpace ENNReal

namespace NlsGge.ThirdConsultation.R
noncomputable section

open NlsGge.Ramer NlsGge.Pilot

variable {lower upper : ℝ}

/-- **Coordinate closability on the finite `L²` core.** If level-`N k` fields `g k` lie in the
`GaussianL2CylindricalCore`, their `H`-valued cylinders tend to `0` in `L²(γ)`, their divergences
tend in `L²(γ)` to `η`, and `η ∈ L²(γ)`, then `η = 0` `γ`-a.e. -/
theorem r021_cylDiv_closable_coord (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    {N : ℕ → ℕ} (g : ∀ k, actualCMHead c (N k) → actualCMHead c (N k))
    (hg : ∀ k, GaussianL2CylindricalCore c (N k) (g k))
    (η : (ℤ → ℂ) → ℝ) (hη : MemLp η 2 (NlsGge.Measure.fullWeightSequenceGaussian c.val))
    (hF : Tendsto (fun k => eLpNorm (fun z => ‖cylField c (N k) (g k) z‖) 2
      (NlsGge.Measure.fullWeightSequenceGaussian c.val)) atTop (𝓝 0))
    (hδ : Tendsto (fun k => eLpNorm (fun z => cylDiv c (N k) (g k) z - η z) 2
      (NlsGge.Measure.fullWeightSequenceGaussian c.val)) atTop (𝓝 0)) :
    η =ᵐ[NlsGge.Measure.fullWeightSequenceGaussian c.val] 0 := by
  set γ := NlsGge.Measure.fullWeightSequenceGaussian c.val with hγ
  have hηi : Integrable η γ := hη.integrable (by norm_num)
  refine ae_eq_zero_of_integral_cylinder_mul_eq_zero c η hηi (fun N₀ φ hφ hφc => ?_)
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (mod_cast le_top)
  obtain ⟨Bφ, hBφ⟩ := hφ1.continuous.bounded_above_of_compact_support hφc
  obtain ⟨Bφ', hBφ'⟩ := (hφ1.continuous_fderiv (by norm_num)).bounded_above_of_compact_support
    (hφc.fderiv (𝕜 := ℝ))
  have hBφ0 : 0 ≤ Bφ := (norm_nonneg _).trans (hBφ 0)
  have hBφ'0 : 0 ≤ Bφ' := (norm_nonneg _).trans (hBφ' 0)
  set K : ℝ := Bφ' * ‖headCoordCLM c N₀‖ with hK
  have hπm : Measurable (fun z : ℤ → ℂ => fun i => z (modeIndex N₀ i)) :=
    measurable_windowProj N₀
  have hφπm : AEStronglyMeasurable (fun z : ℤ → ℂ => φ (fun i => z (modeIndex N₀ i))) γ :=
    (hφ1.continuous.measurable.comp hπm).aestronglyMeasurable
  have hφηi : Integrable (fun z : ℤ → ℂ => φ (fun i => z (modeIndex N₀ i)) * η z) γ :=
    hηi.bdd_mul hφπm (ae_of_all _ fun z => hBφ _)
  have hk : ∀ k, ENNReal.ofReal |∫ z, φ (fun i => z (modeIndex N₀ i)) * η z ∂γ| ≤
      ENNReal.ofReal Bφ * eLpNorm (fun z => cylDiv c (N k) (g k) z - η z) 2 γ +
        ENNReal.ofReal K * eLpNorm (fun z => ‖cylField c (N k) (g k) z‖) 2 γ := by
    intro k
    obtain ⟨hint, hbd⟩ := r021_mixed_level c N₀ φ hφ1 Bφ Bφ' hBφ hBφ' (g k) (hg k)
    have hcylm : AEStronglyMeasurable (fun z => cylDiv c (N k) (g k) z) γ :=
      aestronglyMeasurable_cylDiv c (g k) ((r021_core_contDiff (hg k)).of_le (by norm_num))
    have hi1 : Integrable (fun z : ℤ → ℂ => φ (fun i => z (modeIndex N₀ i)) *
        (η z - cylDiv c (N k) (g k) z)) γ := by
      have e : (fun z : ℤ → ℂ => φ (fun i => z (modeIndex N₀ i)) *
          (η z - cylDiv c (N k) (g k) z)) = fun z => φ (fun i => z (modeIndex N₀ i)) * η z -
            φ (fun i => z (modeIndex N₀ i)) * cylDiv c (N k) (g k) z := by
        funext z; ring
      rw [e]; exact hφηi.sub hint
    have hsplit : ∫ z, φ (fun i => z (modeIndex N₀ i)) * η z ∂γ =
        ∫ z, φ (fun i => z (modeIndex N₀ i)) * (η z - cylDiv c (N k) (g k) z) ∂γ +
          ∫ z, φ (fun i => z (modeIndex N₀ i)) * cylDiv c (N k) (g k) z ∂γ := by
      rw [← integral_add hi1 hint]
      congr 1; funext z; ring
    have hb1 := ofReal_abs_integral_le_mul_eLpNorm γ
      (fun z => φ (fun i => z (modeIndex N₀ i)) * (η z - cylDiv c (N k) (g k) z))
      (fun z => cylDiv c (N k) (g k) z - η z) Bφ hBφ0 (hcylm.sub hη.aestronglyMeasurable)
      (fun z => by
        calc |φ (fun i => z (modeIndex N₀ i)) * (η z - cylDiv c (N k) (g k) z)|
            = |φ (fun i => z (modeIndex N₀ i))| * ‖cylDiv c (N k) (g k) z - η z‖ := by
              rw [abs_mul, Real.norm_eq_abs, ← abs_neg (cylDiv c (N k) (g k) z - η z), neg_sub]
          _ ≤ Bφ * ‖cylDiv c (N k) (g k) z - η z‖ :=
              mul_le_mul_of_nonneg_right (by simpa using hBφ _) (norm_nonneg _))
    calc ENNReal.ofReal |∫ z, φ (fun i => z (modeIndex N₀ i)) * η z ∂γ|
        ≤ ENNReal.ofReal (|∫ z, φ (fun i => z (modeIndex N₀ i)) *
              (η z - cylDiv c (N k) (g k) z) ∂γ| +
            |∫ z, φ (fun i => z (modeIndex N₀ i)) * cylDiv c (N k) (g k) z ∂γ|) := by
          rw [hsplit]; exact ENNReal.ofReal_le_ofReal (abs_add_le _ _)
      _ = ENNReal.ofReal |∫ z, φ (fun i => z (modeIndex N₀ i)) *
              (η z - cylDiv c (N k) (g k) z) ∂γ| +
            ENNReal.ofReal |∫ z, φ (fun i => z (modeIndex N₀ i)) * cylDiv c (N k) (g k) z ∂γ| :=
          ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
      _ ≤ _ := add_le_add hb1 hbd
  have hlim : Tendsto (fun k => ENNReal.ofReal Bφ *
        eLpNorm (fun z => cylDiv c (N k) (g k) z - η z) 2 γ +
      ENNReal.ofReal K * eLpNorm (fun z => ‖cylField c (N k) (g k) z‖) 2 γ) atTop (𝓝 0) := by
    have h1 := ENNReal.Tendsto.const_mul hδ (Or.inr (ENNReal.ofReal_ne_top (r := Bφ)))
    have h2 := ENNReal.Tendsto.const_mul hF (Or.inr (ENNReal.ofReal_ne_top (r := K)))
    simpa using h1.add h2
  have h0 : ENNReal.ofReal |∫ z, φ (fun i => z (modeIndex N₀ i)) * η z ∂γ| ≤ 0 :=
    ge_of_tendsto' hlim hk
  have := ENNReal.ofReal_eq_zero.1 (le_zero_iff.1 h0)
  exact abs_nonpos_iff.1 this

end
end NlsGge.ThirdConsultation.R
