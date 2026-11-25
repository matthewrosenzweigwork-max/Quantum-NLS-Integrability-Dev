import Mathlib
import NlsGge.Hierarchy.ALQ4Ensemble38
import NlsGge.Hierarchy.ALQ4Limit38

                                                                        
                                                                                                                  
                                                
         
                                                                                                                           
                                                                                                                
                                                                           
                                                                                                                      
                                                                                   
                                                                                                                            
set_option autoImplicit false

open MeasureTheory Filter Topology

namespace NlsGge.ThirdConsultation.AL
open NlsGge.AblowitzLadik

theorem al056_alh_tendsto : Tendsto (fun N : ℕ => alh38 N) atTop (𝓝 0) := by
  refine squeeze_zero (fun N => (alh38_pos N).le) (fun N => ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat
  unfold alh38
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  exact one_div_le_one_div_of_le (by linarith : (0 : ℝ) < (N : ℝ) + 1) (by linarith)

/-- Law of the Fourier coordinates under the Q4 ensemble: the transported Gaussian density. -/
theorem al056_fourierLaw {β₀ β₁ β₂ : ℝ} (hβ₀ : 0 < β₀) (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂)
    {N : ℕ} (hN : 1 ≤ N) (hh : alh38 N < β₀) :
    (alQ4Eta38 β₀ β₁ β₂ N).map (fun α => ZMod.dft α) =
      (ENNReal.ofReal (alQ4Z38 β₀ β₁ β₂ N))⁻¹ •
        ((alQ4Gauss38 β₀ β₁ β₂ N).withDensity
          (fun z => ENNReal.ofReal (alQ4F38 β₀ β₁ β₂ N (alQ4V38 N z)))) := by
  obtain ⟨hprob, hint, -, -, -, hmeasF, hbd, hintF, hZpos, -, -⟩ :=
    alQ4Ensemble38 hβ₀ hβ₁ hβ₂ hN hh
  have hdft : Measurable (fun α : ZMod (2 * N + 1) → ℂ => ZMod.dft α) := measurable_dft38
  have hmeasG : Measurable (fun z : ZMod (2 * N + 1) → ℂ =>
      ENNReal.ofReal (alQ4F38 β₀ β₁ β₂ N (alQ4V38 N z))) :=
    ENNReal.measurable_ofReal.comp hmeasF
  have hfin : IsFiniteMeasure ((alQ4Gauss38 β₀ β₁ β₂ N).withDensity
      (fun z => ENNReal.ofReal (alQ4F38 β₀ β₁ β₂ N (alQ4V38 N z)))) :=
    isFiniteMeasure_withDensity_ofReal hintF.hasFiniteIntegral
  have hfin' : IsFiniteMeasure ((ENNReal.ofReal (alQ4Z38 β₀ β₁ β₂ N))⁻¹ •
      ((alQ4Gauss38 β₀ β₁ β₂ N).withDensity
        (fun z => ENNReal.ofReal (alQ4F38 β₀ β₁ β₂ N (alQ4V38 N z))))) :=
    ⟨by
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (ENNReal.ofReal_pos.2 hZpos))
        (measure_lt_top _ _)⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hdft.aemeasurable f.continuous.aestronglyMeasurable,
    alQ4Eta_integral38 hβ₁ hβ₂ hN hh ⇑f,
    integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul hmeasG
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hZpos.le, smul_eq_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun û => ?_)
  dsimp only
  rw [ENNReal.toReal_ofReal (hbd (alQ4V38 N û)).1, smul_eq_mul, mul_comm]

/-- Transport of the Fourier law along the interpolation map (the eventually-N law clause). -/
theorem al056_law {β₀ β₁ β₂ : ℝ} (hβ₀ : 0 < β₀) (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂)
    {N : ℕ} (hN : 1 ≤ N) (hh : alh38 N < β₀) (s : ℝ) :
    alQ4Mu38 s β₀ β₁ β₂ N =
      (ENNReal.ofReal (alQ4Z38 β₀ β₁ β₂ N))⁻¹ •
        ((alQ4Gauss38 β₀ β₁ β₂ N).withDensity
          (fun z => ENNReal.ofReal (alQ4F38 β₀ β₁ β₂ N (alQ4V38 N z)))).map
            (alQ4Interp38 s N) := by
  have hdft : Measurable (fun α : ZMod (2 * N + 1) → ℂ => ZMod.dft α) := measurable_dft38
  have hmeasI : Measurable (alQ4Interp38 s N) := measurable_alQ4Interp38 s N
  unfold alQ4Mu38
  rw [show (fun α : ZMod (2 * N + 1) → ℂ => alQ4Interp38 s N (ZMod.dft α)) =
      alQ4Interp38 s N ∘ (fun α => ZMod.dft α) from rfl,
    ← Measure.map_map hmeasI hdft, al056_fourierLaw hβ₀ hβ₁ hβ₂ hN hh,
    Measure.map_smul _ hmeasI.aemeasurable]

theorem al056 {β₀ β₁ β₂ : ℝ} (h0 : 0 < β₀) (h1 : 0 < β₁) (h2 : 0 < β₂) :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ N ∧ alh38 N < β₀ / 2 ∧
      IsProbabilityMeasure (alQ4Eta38 β₀ β₁ β₂ N) ∧
      Integrable (alQ4Density38 β₀ β₁ β₂ N) ∧
      0 < alQ4Partition38 β₀ β₁ β₂ N ∧
      alQ4Partition38 β₀ β₁ β₂ N ≤
        (Real.pi * alh38 N / β₀) ^ (2 * N + 1) ∧
      (∀ k : ℤ, 0 < alSymbol38 β₀ β₁ β₂ N k) ∧
      0 < alQ4Z38 β₀ β₁ β₂ N ∧ alQ4Z38 β₀ β₁ β₂ N ≤ 1 ∧
      alQ4Partition38 β₀ β₁ β₂ N =
        alh38 N ^ (2 * N + 1) *
          (∏ k ∈ Finset.Icc (-(N : ℤ)) N, Real.pi / alSymbol38 β₀ β₁ β₂ N k) *
          alQ4Z38 β₀ β₁ β₂ N ∧
      (∀ s : ℝ, alQ4Mu38 s β₀ β₁ β₂ N =
        (ENNReal.ofReal (alQ4Z38 β₀ β₁ β₂ N))⁻¹ •
          ((alQ4Gauss38 β₀ β₁ β₂ N).withDensity
            (fun z => ENNReal.ofReal (alQ4F38 β₀ β₁ β₂ N (alQ4V38 N z)))).map
              (alQ4Interp38 s N)) := by
  have hev1 : ∀ᶠ N : ℕ in atTop, 1 ≤ N := eventually_ge_atTop 1
  have hev2 : ∀ᶠ N : ℕ in atTop, alh38 N < β₀ / 2 :=
    al056_alh_tendsto.eventually_lt_const (half_pos h0)
  filter_upwards [hev1, hev2] with N hN hN2
  have hh : alh38 N < β₀ := by linarith
  obtain ⟨hprob, hint, hpos, hle, hsym, -, -, -, hZpos, hZle, hid⟩ :=
    alQ4Ensemble38 h0 h1.le h2.le hN hh
  exact ⟨hN, hN2, hprob, hint, hpos, hle, hsym, hZpos, hZle, hid,
    fun s => al056_law h0 h1.le h2.le hN hh s⟩

end NlsGge.ThirdConsultation.AL
