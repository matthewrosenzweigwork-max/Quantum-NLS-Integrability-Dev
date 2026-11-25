import Mathlib

/-!+# FIN-EXT025-ROOT-02: Riemann--Lebesgue on compact L1 families

The integral below is unnormalized and uses the physical real frequency.
There is no differentiability assertion in “vanishing at infinity”.
The Fubini reduction and factorial-majorant application in the record are
separate mathematical statements, not descriptive prose granting those results.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped FourierTransform

namespace QuantumNLS.Ext025A

/-- The source's unnormalized oscillatory integral, on the actual L1 carrier. -/
def oscillatoryIntegral (f : Lp ℂ 1 (volume : Measure ℝ)) (ω : ℝ) : ℂ :=
  ∫ x : ℝ, Complex.exp (-Complex.I * ((ω * x : ℝ) : ℂ)) * f x

/-- Frequency conversion retains all normalization constants. -/
theorem oscillatoryIntegral_eq_fourier (f : Lp ℂ 1 (volume : Measure ℝ)) (ω : ℝ) :
    oscillatoryIntegral f ω = 𝓕 (f : ℝ → ℂ) (ω / (2 * Real.pi)) := by
  rw [Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with x
  simp only [RCLike.inner_apply, conj_trivial, smul_eq_mul]
  congr 2
  push_cast
  field_simp

/-- Compactness in the L1 norm, rather than boundedness, upgrades
pointwise Riemann--Lebesgue to uniform decay. Equicontinuity is supplied
by the same bounded Fourier map at every frequency. This is the
finite-net argument packaged by mathlib's compact equicontinuity theorem. -/
theorem root02_fourier_uniform {K : Set (Lp ℂ 1 (volume : Measure ℝ))}
    (hK : IsCompact K) :
    TendstoUniformly (fun ω : ℝ => fun f : K => 𝓕 (f.1 : ℝ → ℂ) ω)
      (fun _ => 0) (cocompact ℝ) := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let T := Real.Lp.fourierTransformCLM ℝ ℂ
  have hLip : ∀ ω : ℝ, LipschitzWith ‖T‖₊
      (fun f : K => 𝓕 (f.1 : ℝ → ℂ) ω) := by
    intro ω
    apply LipschitzWith.of_dist_le_mul
    intro f g
    calc
      dist (𝓕 (f.1 : ℝ → ℂ) ω) (𝓕 (g.1 : ℝ → ℂ) ω)
          ≤ dist (T f.1) (T g.1) :=
            BoundedContinuousFunction.dist_coe_le_dist (f := T f.1) (g := T g.1) ω
      _ ≤ ‖T‖ * dist f.1 g.1 := T.lipschitzWith.dist_le_mul _ _
      _ = (‖T‖₊ : ℝ) * dist f g := rfl
  have heq : Equicontinuous (fun ω : ℝ => fun f : K => 𝓕 (f.1 : ℝ → ℂ) ω) :=
    (LipschitzWith.uniformEquicontinuous _ ‖T‖₊ hLip).equicontinuous
  have hpoint : Tendsto (fun ω : ℝ => fun f : K => 𝓕 (f.1 : ℝ → ℂ) ω)
      (cocompact ℝ) (𝓝 (fun _ => (0 : ℂ))) := by
    exact tendsto_pi_nhds.mpr fun f => Real.zero_at_infty_fourier (f.1 : ℝ → ℂ)
  have h := (heq.tendsto_uniformFun_iff_pi (cocompact ℝ) (fun _ => (0 : ℂ))).2 hpoint
  exact UniformFun.tendsto_iff_tendstoUniformly.mp h

/-- ROOT-02, literally the unnormalized real-frequency conclusion:
each integrable profile decays, uniformly on every compact L1 family. -/
theorem «FIN-EXT025-ROOT-02» :
    (∀ f : Lp ℂ 1 (volume : Measure ℝ),
      Tendsto (oscillatoryIntegral f) (cocompact ℝ) (𝓝 0)) ∧
    (∀ K : Set (Lp ℂ 1 (volume : Measure ℝ)), IsCompact K →
      TendstoUniformly (fun ω : ℝ => fun f : K => oscillatoryIntegral f.1 ω)
        (fun _ => 0) (cocompact ℝ)) := by
  have hscale : Tendsto (fun ω : ℝ => ω / (2 * Real.pi))
      (cocompact ℝ) (cocompact ℝ) := by
    simpa only [div_eq_mul_inv] using
      (Filter.tendsto_cocompact_mul_right₀
        (inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)))
  constructor
  · intro f
    simpa only [Function.comp_def, ← oscillatoryIntegral_eq_fourier] using
      (Real.zero_at_infty_fourier (f : ℝ → ℂ)).comp hscale
  · intro K hK u hu
    simpa only [← oscillatoryIntegral_eq_fourier] using
      hscale.eventually (root02_fourier_uniform hK u hu)

end QuantumNLS.Ext025A

#print axioms QuantumNLS.Ext025A.oscillatoryIntegral
#print axioms QuantumNLS.Ext025A.oscillatoryIntegral_eq_fourier
#print axioms QuantumNLS.Ext025A.root02_fourier_uniform
#print axioms QuantumNLS.Ext025A.«FIN-EXT025-ROOT-02»
