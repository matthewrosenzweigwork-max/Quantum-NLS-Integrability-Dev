import NlsGge.GK38.GradFundamentalSpectralDerivative

/-! # K1: exact free scaled gradient phases.
GK Chapter I, Lemma4.3. The anti-gradient phase retains the actual complex z.
-/
set_option autoImplicit false
open Set
namespace NlsGge.GK38
noncomputable section

theorem fundColumn38_zero (z : ℂ) (t : Icc (0 : ℝ) 1) (i j : Fin 2) :
    fundColumn38 0 z t j i = freeE z t i j := by
  rw [fundColumn38, ext38_of_mem _ t.2]
  change fundCont 0 z t i j = freeE z t i j
  rw [fundCont_zero]
  rfl

theorem scaled_gradDiscrim38_zero (z : ℂ) (t : Icc (0 : ℝ) 1) :
    Complex.I • gradDiscrim38 0 z t = 0 := by
  ext k
  fin_cases k <;> simp [gradDiscrim38, monodromyPair_zero_potential, starProd38,
    fundColumn38_zero, freeE]

theorem scaled_gradAntiDiscrim38_zero (z : ℂ) (t : Icc (0 : ℝ) 1) :
    Complex.I • gradAntiDiscrim38 0 z t =
      ![-Complex.exp (-Complex.I * z * (1 - 2 * (t : ℝ))),
        Complex.exp (Complex.I * z * (1 - 2 * (t : ℝ)))] := by
  ext k
  fin_cases k <;> simp [gradAntiDiscrim38, monodromyPair_zero_potential, starProd38,
    fundColumn38_zero, freeE, ← Complex.exp_add]
  · congr 2 <;> ring_nf <;> simp [Complex.I_sq]
  · congr 1 <;> ring_nf <;> simp [Complex.I_sq]

end
end NlsGge.GK38
