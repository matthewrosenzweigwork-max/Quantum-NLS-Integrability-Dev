import QuantumNLS.Local001BoundsLOCAL005

/-!
# Absolute mode formula for a LOCAL-005 resolvent word

For a path of intermediate modes in the parity sector of `n`, write its
successive shifts as `q₁, …, qₖ₋₁`, with endpoint shifts `q₀ = qₖ = 0`.
The potential label at step `j` is then `n + qⱼ₋₁ + qⱼ`.  This file records
the exact nonnegative word majorant, keeping each of the `k` inputs separate.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal

namespace QuantumNLS.ResolventWordCoefficientLOCAL005

open QuantumNLS.ResetFreeResolventLOCAL001

/-- Shift of the mode immediately before the `j`th potential factor. -/
def previousShift {k : ℕ} (q : Fin (k - 1) → ℤ) (j : Fin k) : ℤ :=
  if hj : (j : ℕ) = 0 then 0 else q ⟨j.val - 1, by omega⟩

/-- Shift of the mode immediately after the `j`th potential factor. -/
def nextShift {k : ℕ} (q : Fin (k - 1) → ℤ) (j : Fin k) : ℤ :=
  if hj : (j : ℕ) + 1 = k then 0 else q ⟨j.val, by omega⟩

/-- Fourier input label of the `j`th potential factor. -/
def wordLabel {k : ℕ} (n : ℤ) (q : Fin (k - 1) → ℤ) (j : Fin k) : ℤ :=
  n + previousShift q j + nextShift q j

/-- Absolute scalar term of the degree-`k` Neumann word, including its
potential normalization and its `k - 1` free-resolvent factors. -/
def wordTerm (L κ : ℝ) (k : ℕ) (n : ℤ) (z : ℂ)
    (u : Fin k → ℤ → ℂ) (q : Fin (k - 1) → ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * Real.sqrt (κ / L)) ^ k *
    (∏ j : Fin k, ENNReal.ofReal (‖u j (wordLabel n q j)‖)) *
    ∏ i : Fin (k - 1),
      ENNReal.ofReal
        (‖freeResolventMultiplier L n z (sourceMode n (q i))‖)

/-- The absolute Fourier-coefficient majorant of one degree-`k` resolvent
word at output mode `n`.  `ℝ≥0∞` preserves the value of a nonnegative sum
before its finiteness is proved. -/
def wordMajorant (L κ : ℝ) (k : ℕ) (n : ℤ) (z : ℂ)
    (u : Fin k → ℤ → ℂ) : ℝ≥0∞ :=
  ∑' q : Fin (k - 1) → ℤ, wordTerm L κ k n z u q

theorem wordTerm_nonneg (L κ : ℝ) (k : ℕ) (n : ℤ) (z : ℂ)
    (u : Fin k → ℤ → ℂ) (q : Fin (k - 1) → ℤ) :
    0 ≤ wordTerm L κ k n z u q := bot_le

#print axioms wordTerm_nonneg

end QuantumNLS.ResolventWordCoefficientLOCAL005
