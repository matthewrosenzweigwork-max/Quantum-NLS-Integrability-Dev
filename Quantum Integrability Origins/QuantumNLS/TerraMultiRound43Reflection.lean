import QuantumNLS.TerraMultiRound39ConjugateResolvent

/-! Frequency reflection and the signed resolvent. This is an ingredient for
transporting positive-height estimates to negative heights. -/
set_option autoImplicit false
noncomputable section
open Complex
namespace QuantumNLS.TerraMultiRound43Reflection
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE1
open QuantumNLS.TerraMultiRound38SignedPicard

/-- Reflect Fourier frequency without complex conjugation. -/
def reflectEll (x : Ell2) : Ell2 :=
  ⟨fun k => x (-k), by
    apply memℓp_gen
    rw [two_toReal]
    simp only [Real.rpow_two]
    exact (summable_sq x).comp_injective neg_injective⟩

@[simp] theorem reflectEll_apply (x : Ell2) (k : ℤ) : reflectEll x k = x (-k) := rfl

@[simp] theorem reflectEll_invol (x : Ell2) : reflectEll (reflectEll x) = x := by
  apply lp.ext
  funext k
  simp

theorem norm_reflectEll (x : Ell2) : ‖reflectEll x‖ = ‖x‖ := by
  have h1 := norm_sq_eq_tsum (reflectEll x)
  have e : ∑' k, ‖reflectEll x k‖ ^ 2 = ∑' k, ‖x k‖ ^ 2 := by
    change (∑' k, ‖x (-k)‖ ^ 2) = _
    exact (Equiv.neg ℤ).tsum_eq (fun k => ‖x k‖ ^ 2)
  rw [e, ← norm_sq_eq_tsum x] at h1
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1

/-- Reflection turns the height `Y` resolvent into the negative of the
height `-Y` resolvent acting on the reflected Fourier sequence. -/
theorem reflect_signedCLM (L Y : ℝ) (hY : 0 < |Y|) (x : Ell2) :
    reflectEll (signedCLM L Y hY x) =
      -signedCLM L (-Y) (by simpa using hY) (reflectEll x) := by
  apply lp.ext
  funext k
  change x (-k) / ((Y : ℂ) + Complex.I * (freq L (-k) : ℂ)) =
    -(x (-k) / (((-Y : ℝ) : ℂ) + Complex.I * (freq L k : ℂ)))
  have hf : freq L (-k) = -freq L k := by simp [freq, neg_div]
  rw [hf]
  push_cast
  have h : -(Y : ℂ) + Complex.I * (freq L k : ℂ) =
      -((Y : ℂ) + Complex.I * (-(freq L k) : ℂ)) := by ring
  rw [h, div_neg, neg_neg]

#print axioms reflectEll_invol
#print axioms norm_reflectEll
#print axioms reflect_signedCLM
end QuantumNLS.TerraMultiRound43Reflection
