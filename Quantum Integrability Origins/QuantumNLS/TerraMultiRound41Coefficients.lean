import QuantumNLS.SmoothScalarMomentsFormal

/-! Conversion of the printed signed Riccati coefficients to the established
classical-charge convention. This is a supporting result for REG-005. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Complex Finset MeasureTheory
open scoped ComplexConjugate
namespace QuantumNLS.TerraMultiRound41Coefficients
open QuantumNLS.ClassicalCharges

/-- Signed physical coefficients, with the zero term unused. -/
def aseq (κ : ℝ) (u : ℝ → ℂ) (n : ℕ) : ℝ → ℂ :=
  fun x => (-Complex.I) ^ (n - 1) * vseq κ u n x

lemma aseq_one (κ : ℝ) (u : ℝ → ℂ) : aseq κ u 1 = u := by
  funext x
  simp [aseq, vseq_one]

lemma aseq_succ {L : ℝ} (κ : ℝ) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (n : ℕ) :
    aseq κ u (n + 2) = fun x =>
      -deriv (aseq κ u (n + 1)) x - (κ : ℂ) * conj (u x) *
        ∑ j ∈ Finset.Icc 1 n, aseq κ u j x * aseq κ u (n + 1 - j) x := by
  funext x
  have hd : deriv (aseq κ u (n + 1)) x =
      (-Complex.I) ^ n * deriv (vseq κ u (n + 1)) x := by
    change deriv (fun t => (-Complex.I) ^ n * vseq κ u (n + 1) t) x = _
    exact deriv_const_mul ((-Complex.I) ^ n)
      ((contDiff_infty_iff_deriv.mp (vseq_regular κ hu (n + 1)).1).1 x)
  have hs : (∑ j ∈ Finset.Icc 1 n, aseq κ u j x * aseq κ u (n + 1 - j) x) =
      (-Complex.I) ^ (n - 1) * ∑ j ∈ Finset.Icc 1 n,
        vseq κ u j x * vseq κ u (n + 1 - j) x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_Icc.mp hj
    have hp : j - 1 + (n + 1 - j - 1) = n - 1 := by omega
    simp only [aseq]
    calc
      _ = ((-Complex.I) ^ (j - 1) * (-Complex.I) ^ (n + 1 - j - 1)) *
          (vseq κ u j x * vseq κ u (n + 1 - j) x) := by ring
      _ = _ := by rw [← pow_add, hp]
  rw [hd, hs]
  simp only [aseq, vseq_succ]
  have he : n + 2 - 1 = n + 1 := by omega
  rw [he]
  by_cases hn : n = 0
  · subst n
    simp [vseq_one, ← mul_assoc, Complex.I_mul_I]
  · have hn' : n - 1 + 1 = n := by omega
    have hI : (-Complex.I) ^ 2 = (-1 : ℂ) := by simp [Complex.I_sq]
    have hp : (-Complex.I) ^ (n + 1) = -((-Complex.I) ^ (n - 1)) := by
      have he : n + 1 = (n - 1) + 2 := by omega
      rw [he, pow_add, hI, mul_neg, mul_one]
    have hp' : (-Complex.I) ^ (n + 1) * (-Complex.I) = -((-Complex.I) ^ n) := by
      rw [pow_succ]
      calc
        _ = (-Complex.I) ^ n * ((-Complex.I) ^ 2) := by ring
        _ = _ := by rw [hI]; ring
    have h := hp'
    rw [hp] at h
    rw [hp]
    linear_combination (deriv (vseq κ u (n + 1)) x) * h

/-- Printed coefficient integral. -/
def coefficient (L κ : ℝ) (u : ℝ → ℂ) (n : ℕ) : ℂ :=
  ∫ x in (0 : ℝ)..L, conj (u x) * aseq κ u n x

lemma coefficient_eq_charge (L κ : ℝ) (u : ℝ → ℂ) (n : ℕ) :
    coefficient L κ u n = (-Complex.I) ^ (n - 1) * charge L κ u n := by
  unfold coefficient charge
  simp_rw [aseq, show ∀ x, conj (u x) * ((-Complex.I) ^ (n - 1) * vseq κ u n x) =
    (-Complex.I) ^ (n - 1) * (conj (u x) * vseq κ u n x) by intro x; ring]
  exact intervalIntegral.integral_const_mul _ _

#print axioms aseq_succ
#print axioms coefficient_eq_charge
end QuantumNLS.TerraMultiRound41Coefficients
