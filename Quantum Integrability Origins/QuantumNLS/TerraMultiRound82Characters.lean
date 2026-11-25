import QuantumNLS.ChartFrequencies
import QuantumNLS.LocalSpectralOperator

/-! Algebraic steps in the proof of R-877E839C. These are character and
momentum identities only: no physical-flow covariance or predecessor theorem
is assumed or claimed here. -/
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
namespace QuantumNLS.TerraMultiRound82Characters

/-- Cancellation at an active coordinate identifies a shifted frequency. -/
theorem shifted_frequency {a b c : ℝ} {w : ℂ} (hw : w ≠ 0)
    (h : ∀ t : ℝ,
      Complex.exp (-Complex.I * ((t * a : ℝ) : ℂ)) * w =
      (Complex.exp (-Complex.I * ((t * c : ℝ) : ℂ)) *
       Complex.exp (-Complex.I * ((t * b : ℝ) : ℂ))) * w) :
    a = b + c := by
  apply QuantumNLS.ChartFrequencies.freq_eq_of_char_eq hw
  intro t
  rw [h t, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Complex conjugation and reversal of time preserve the rotation frequency. -/
theorem conjugate_time_reversal (b t : ℝ) (w : ℂ) :
    conj (Complex.exp (-Complex.I * (((-t) * b : ℝ) : ℂ)) * w) =
      Complex.exp (-Complex.I * ((t * b : ℝ) : ℂ)) * conj w := by
  simp only [map_mul, ← Complex.exp_conj, map_neg, Complex.conj_ofReal, Complex.conj_I]
  congr 2
  push_cast
  ring

/-- No frequency cancellation is required at a zero coordinate. -/
theorem zero_coordinate (a t : ℝ) :
    Complex.exp (-Complex.I * ((t * a : ℝ) : ℂ)) * (0 : ℂ) = 0 := by simp

/-- The exact momentum correction in the boost calculation, for all L, k, n. -/
theorem boost_momentum (L : ℝ) (k n : ℤ) :
    QuantumNLS.LocalSpectral.pm L k ^ 2 +
      2 * QuantumNLS.LocalSpectral.pm L k * QuantumNLS.LocalSpectral.pm L (n-k) =
    QuantumNLS.LocalSpectral.pm L n ^ 2 - QuantumNLS.LocalSpectral.pm L (n-k) ^ 2 := by
  simp only [QuantumNLS.LocalSpectral.pm, Int.cast_sub]
  ring

#print axioms shifted_frequency
#print axioms conjugate_time_reversal
#print axioms zero_coordinate
#print axioms boost_momentum
end QuantumNLS.TerraMultiRound82Characters
