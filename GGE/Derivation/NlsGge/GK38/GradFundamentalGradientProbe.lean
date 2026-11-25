import NlsGge.GK38.GradFundamentalGradientSeq
import NlsGge.GK38.GradFundamentalSpectralProbe
import NlsGge.GK38.PairAsymptoticsTriangularProbe

/-! # K1: free shifted phases and actual complex directional gradient probes. -/
set_option autoImplicit false
open MeasureTheory Set
namespace NlsGge.GK38
noncomputable section

theorem probe_k1_free_gradient_square38 (υ : ℤ → ℂ) (t : Icc (0 : ℝ) 1) :
    k1SquareBound38 (fun n => k1GradDiscrimMass38 0 (υ n) t) 0 ∧
      k1SquareBound38 (fun n => k1GradAntiMass38 0 (υ n) t) 0 := by
  constructor <;> apply k1SquareBound38_of_finite
  · intro n; unfold k1GradDiscrimMass38; positivity
  · intro T
    simp only [k1GradDiscrimMass38, scaled_gradDiscrim38_zero]
    simp
  · intro n; unfold k1GradAntiMass38; positivity
  · intro T
    simp [k1GradAntiMass38, k1GradAntiResidual38, scaled_gradAntiDiscrim38_zero]

/-- A half-lattice nonreal shift at an internal time retains its own frequency. -/
theorem probe_k1_free_nonreal_gradient38 (n : ℤ) :
    Complex.I • gradAntiDiscrim38 0
      ((n : ℂ) * Real.pi + Real.pi / 2 + Complex.I) (⟨1 / 4, by norm_num, by norm_num⟩ : Icc (0 : ℝ) 1) =
      ![-Complex.exp (-Complex.I * ((n : ℂ) * Real.pi + Real.pi / 2 + Complex.I) / 2),
        Complex.exp (Complex.I * ((n : ℂ) * Real.pi + Real.pi / 2 + Complex.I) / 2)] := by
  rw [scaled_gradAntiDiscrim38_zero]
  norm_num
  congr 1 <;> congr 1 <;> ring_nf <;> simp

/-- The first anti-gradient component for an arbitrary nonreal triangular potential. -/
theorem probe_k1_triangular_anti_first38 (a : ℂ) (t : Icc (0 : ℝ) 1) :
    gradAntiDiscrim38 (constL2 a, 0) 0 t 0 = Complex.I := by
  simp [gradAntiDiscrim38, fundColumn38, k1FundContEndpoint38, monodromyPair_eq_fundPair,
    triangularFund_eq38, triangularForce_lower_left38, pairForce38_diagonal, starProd38, freeE]

/-- Complex bilinearity gives minus one on the imaginary first-potential direction. -/
theorem probe_k1_triangular_imaginary_direction38 (a : ℂ) :
    gradAntiDiscrimCLM (constL2 a, 0) 0 (constL2 Complex.I, 0) = -1 := by
  rw [gradAntiDiscrimCLM_apply]
  have he : (fun s => gradAntiDiscrim38 (constL2 a, 0) 0 s 0 *
      potRepFst38 (constL2 Complex.I, 0) s + gradAntiDiscrim38 (constL2 a, 0) 0 s 1 *
        potRepSnd38 (constL2 Complex.I, 0) s) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      fun _ => (-1 : ℂ) := by
    filter_upwards [(ae_restrict_of_ae (coverRep38_const_ae Complex.I)),
      (ae_restrict_of_ae coverRep38_zero_ae), ae_restrict_mem measurableSet_Ioc] with s hs0 hs1 hm
    have hg := probe_k1_triangular_anti_first38 a ⟨s, hm.1.le, hm.2⟩
    change gradAntiDiscrim38 (constL2 a, 0) 0 s 0 = Complex.I at hg
    simp only [potRepFst38, potRepSnd38, hg, hs0, hs1, mul_zero, add_zero, Complex.I_mul_I]
  rw [intervalIntegral.integral_congr_ae_restrict (by
    simpa only [uIoc_of_le zero_le_one] using he)]
  simp

theorem probe_k1_actual_triangular_derivative38 (a : ℂ) :
    HasFDerivAt (fun ψ => antiDiscrim ψ 0) (gradAntiDiscrimCLM (constL2 a, 0) 0) (constL2 a, 0) ∧
      gradAntiDiscrimCLM (constL2 a, 0) 0 (constL2 Complex.I, 0) = -1 :=
  ⟨hasFDerivAt_gradAntiDiscrimCLM _ _, probe_k1_triangular_imaginary_direction38 a⟩

end
end NlsGge.GK38
