import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Basic.Complex.Basic

/-!
# One-mode normal ordering on algebraic finite-particle vectors

The algebraic one-mode space is `Polynomial ℂ`. Its monomial `X ^ n` is the
unnormalized occupation vector `(a†)^n Ω`; creation is multiplication by `X`
and annihilation is polynomial differentiation. These are concrete operators,
with no assumed canonical commutation relation.

This file proves the complete contraction formula in this algebraic realization.
It does not construct the Hilbert-space Fock completion or the unitary sending
`X ^ n` to `sqrt(n!)` times the normalized occupation vector. That identification
is still required before LLFP-Q2-023 is accepted for the manuscript's carriers.
Neither the tensor Wick-product formula nor LLFP-Q2-024--028 is asserted here.

Source: LLFP-Q2-023, consolidated manuscript lines 1046--1051.
Reuse: Mathlib `Algebra/Polynomial/Derivative.lean`,
`Polynomial.iterate_derivative_mul_X_pow`, pinned revision d13f23b.
-/

open scoped BigOperators
open Polynomial

noncomputable section

namespace LiebLiniger.FixedPeriod.Quantum

/-- Finite-particle vectors in the unnormalized algebraic one-mode occupation basis. -/
abbrev AlgebraicOneMode := Polynomial ℂ

/-- The unscaled creation operator on algebraic finite-particle vectors. -/
def algebraicCreation (f : AlgebraicOneMode) : AlgebraicOneMode := X * f

/-- The unscaled annihilation operator on algebraic finite-particle vectors. -/
def algebraicAnnihilation (f : AlgebraicOneMode) : AlgebraicOneMode := derivative f

/-- Creation raises the unnormalized occupation basis with coefficient one. -/
theorem algebraicCreation_X_pow (n : ℕ) :
    algebraicCreation (X ^ n) = X ^ (n + 1) := by
  simp only [algebraicCreation, pow_succ, mul_comm]

/-- Annihilation lowers the unnormalized occupation basis with coefficient `n`.
In particular the vacuum (`n = 0`) is annihilated. -/
theorem algebraicAnnihilation_X_pow (n : ℕ) :
    algebraicAnnihilation (X ^ n) = n • (X ^ (n - 1) : AlgebraicOneMode) := by
  simp only [algebraicAnnihilation, derivative_X_pow, C_eq_natCast, nsmul_eq_mul]

/-- The canonical commutation relation is proved from the concrete actions. -/
theorem algebraicOneMode_ccr (f : AlgebraicOneMode) :
    algebraicAnnihilation (algebraicCreation f) =
      algebraicCreation (algebraicAnnihilation f) + f := by
  simp only [algebraicAnnihilation, algebraicCreation, derivative_mul, derivative_X,
    one_mul, add_comm]

/-- Iterated creation is multiplication by the corresponding monomial. -/
theorem algebraicCreation_iterate (q : ℕ) (f : AlgebraicOneMode) :
    algebraicCreation^[q] f = X ^ q * f := by
  induction q with
  | zero => simp only [Function.iterate_zero_apply, pow_zero, one_mul]
  | succ q ih =>
    rw [Function.iterate_succ_apply', algebraicCreation, ih, pow_succ]
    ring

/-- Exact one-mode contraction formula in the concrete polynomial realization.
All quantifiers range over arbitrary natural powers and arbitrary finite
polynomial vectors, including the vacuum and powers beyond an occupied sector. -/
theorem algebraicOneMode_normal_order (p q : ℕ) (f : AlgebraicOneMode) :
    algebraicAnnihilation^[p] (algebraicCreation^[q] f) =
      ∑ j ∈ Finset.range (min p q + 1),
        (j.factorial * p.choose j * q.choose j) •
          algebraicCreation^[q - j] (algebraicAnnihilation^[p - j] f) := by
  simp only [algebraicCreation_iterate]
  change derivative^[p] (X ^ q * f) =
    ∑ j ∈ Finset.range (min p q + 1),
      (j.factorial * p.choose j * q.choose j) •
        (X ^ (q - j) * derivative^[p - j] f)
  simpa only [Nat.succ_eq_add_one, Nat.min_comm,
    Nat.descFactorial_eq_factorial_mul_choose, mul_comm, mul_left_comm, mul_assoc] using
    Polynomial.iterate_derivative_mul_X_pow p q f

/-- The first commutation step used by the manuscript's induction proof. -/
theorem algebraicOneMode_commute_creation_pow (q : ℕ) (f : AlgebraicOneMode) :
    algebraicAnnihilation (algebraicCreation^[q] f) =
      algebraicCreation^[q] (algebraicAnnihilation f) +
        q • algebraicCreation^[q - 1] f := by
  simp only [algebraicCreation_iterate, algebraicAnnihilation, derivative_mul,
    derivative_X_pow, C_eq_natCast, nsmul_eq_mul]
  ring

end LiebLiniger.FixedPeriod.Quantum
