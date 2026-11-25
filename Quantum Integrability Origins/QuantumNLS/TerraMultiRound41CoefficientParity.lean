import QuantumNLS.TerraMultiRound41Coefficients

/-! The parity of the literal signed-recursion coefficients. This does not
establish the analytic expansion or the positive scalar-construction binding. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Complex
open scoped ComplexConjugate
namespace QuantumNLS.TerraMultiRound41CoefficientParity
open QuantumNLS.ClassicalCharges QuantumNLS.TerraMultiRound41Coefficients

lemma coefficient_conjugate {L κ : ℝ} {u : ℝ → ℂ} (hκ : 0 < κ)
    (hu : SmoothPeriodic L u) (n : ℕ) :
    conj (coefficient L κ u n) = (-1 : ℂ) ^ (n - 1) * coefficient L κ u n := by
  have hi := QuantumNLS.SmoothScalarMomentsFormal.charge_real hκ hu n
  have hc : conj (charge L κ u n) = charge L κ u n := by
    apply Complex.ext <;> simp [hi]
  rw [coefficient_eq_charge, map_mul, map_pow, hc]
  have hI : conj (-Complex.I) = -(-Complex.I) := by simp
  rw [hI, neg_pow]
  ring

/-- The coefficients at odd indices are real and those at positive even
indices are purely imaginary, for every smooth periodic field. -/
theorem coefficient_parity {L κ : ℝ} {u : ℝ → ℂ} (hκ : 0 < κ)
    (hu : SmoothPeriodic L u) :
    (∀ m : ℕ, (coefficient L κ u (2 * m + 1)).im = 0) ∧
    (∀ m : ℕ, (coefficient L κ u (2 * m + 2)).re = 0) := by
  constructor
  · intro m
    have h := coefficient_conjugate hκ hu (2 * m + 1)
    have he : Even (2 * m + 1 - 1) := by
      have : 2 * m + 1 - 1 = 2 * m := by omega
      rw [this]
      exact ⟨m, by omega⟩
    rw [he.neg_one_pow, one_mul] at h
    have h' := congrArg Complex.im h
    simp only [Complex.conj_im] at h'
    linarith
  · intro m
    have h := coefficient_conjugate hκ hu (2 * m + 2)
    have ho : Odd (2 * m + 2 - 1) := by
      have : 2 * m + 2 - 1 = 2 * m + 1 := by omega
      rw [this]
      exact ⟨m, by omega⟩
    rw [ho.neg_one_pow, neg_one_mul] at h
    have h' := congrArg Complex.re h
    simp only [Complex.conj_re, Complex.neg_re] at h'
    linarith

#print axioms coefficient_conjugate
#print axioms coefficient_parity
end QuantumNLS.TerraMultiRound41CoefficientParity
