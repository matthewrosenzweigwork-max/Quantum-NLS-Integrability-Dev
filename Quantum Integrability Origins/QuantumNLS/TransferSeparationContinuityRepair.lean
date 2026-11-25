import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# R-533B0EC6 `basis:lem:separation` (periodic_basis.tex:399-416)

Transfer function (`basis:eq:spectralfunction`, periodic_basis.tex:345-355), for a real configuration
`q : Fin N → ℝ`:
`s_q(z) = ∏_j (1 + i c/(z - q_j)) + e^{iLz} ∏_j (1 - i c/(z - q_j))`.

Lemma (source): "For `c > 0`, two distinct real rapidity multisets have distinct transfer functions.
If both are on shell, their values differ at some real spectral parameter."

The inherited exponential-polynomial argument uses differentiation and polynomial
degrees rather than the printed large-imaginary-parameter asymptotics. This copy
repairs only the pinned-library continuity expressions and deprecated set notation.
The complex cofinite separation statement is proved below. The real-axis and
on-shell separation clauses mentioned in the historical module header were not
implemented in that source and are not added here.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Polynomial
open Polynomial Filter Topology

namespace QuantumNLS.TransferSeparationContinuityRepair

variable {N : ℕ}

/-- **The transfer function** `s_q(z)` of `basis:eq:spectralfunction` (literal). -/
def sFun (L c : ℝ) (q : Fin N → ℝ) (z : ℂ) : ℂ :=
  (∏ j, (1 + Complex.I * c / (z - q j))) +
    Complex.exp (Complex.I * L * z) * ∏ j, (1 - Complex.I * c / (z - q j))

/-- The rapidity multiset of a configuration. -/
def msOf (q : Fin N → ℝ) : Multiset ℝ := Multiset.map q Finset.univ.val

/-- **On shell** (`basis:eq:bethe`): `e^{iLq_j} = ∏_{k≠j} (q_j - q_k + ic)/(q_j - q_k - ic)`. -/
def OnShell (L c : ℝ) (q : Fin N → ℝ) : Prop :=
  ∀ j : Fin N, Complex.exp (Complex.I * L * q j) =
    ∏ k ∈ Finset.univ.erase j, (((q j : ℂ) - q k + Complex.I * c) / ((q j : ℂ) - q k - Complex.I * c))

/-! ### Polynomial form -/

/-- `∏_j (X - (q_j + a))`. -/
def shiftPoly (q : Fin N → ℝ) (a : ℂ) : ℂ[X] := ∏ j, (X - C ((q j : ℂ) + a))

theorem eval_shiftPoly (q : Fin N → ℝ) (a z : ℂ) :
    (shiftPoly q a).eval z = ∏ j, (z - ((q j : ℂ) + a)) := by
  simp [shiftPoly, eval_prod]

/-- Clearing denominators: for `z` away from the poles, `A_q(z)·∏(z-q_j) = ∏(z - q_j + ic)`. -/
theorem prod_plus_mul (c : ℝ) (q : Fin N → ℝ) (z : ℂ) (hz : ∀ j, z ≠ q j) :
    (∏ j, (1 + Complex.I * c / (z - q j))) * (shiftPoly q 0).eval z =
      (shiftPoly q (-(Complex.I * c))).eval z := by
  rw [eval_shiftPoly, eval_shiftPoly, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  have : z - q j ≠ 0 := sub_ne_zero.2 (hz j)
  simp only [add_zero]
  field_simp
  ring

theorem prod_minus_mul (c : ℝ) (q : Fin N → ℝ) (z : ℂ) (hz : ∀ j, z ≠ q j) :
    (∏ j, (1 - Complex.I * c / (z - q j))) * (shiftPoly q 0).eval z =
      (shiftPoly q (Complex.I * c)).eval z := by
  rw [eval_shiftPoly, eval_shiftPoly, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  have : z - q j ≠ 0 := sub_ne_zero.2 (hz j)
  simp only [add_zero]
  field_simp
  ring

/-! ### Exponential-polynomial independence -/

theorem poly_eq_zero_of_eval {P : ℂ[X]} (h : ∀ z, P.eval z = 0) : P = 0 :=
  Polynomial.funext fun z => by simpa using h z

/-- **No nonzero polynomial pair satisfies `U(z) + e^{iLz} V(z) = 0`** (`L ≠ 0`).
*Deviation from the printed proof*: instead of the asymptotics of `R(iy) + e^{-Ly}T(iy)` as
`y → ∞`, differentiate once: `U' V = U (V' + iL V)` as polynomials, which is impossible by degrees
unless `V = 0`; the conclusion `R = 0 ∧ T = 0` is the same. -/
theorem exp_poly_eq_zero {L : ℝ} (hL : L ≠ 0) (U V : ℂ[X])
    (h : ∀ z : ℂ, U.eval z + Complex.exp (Complex.I * L * z) * V.eval z = 0) : U = 0 ∧ V = 0 := by
  have hIL : (Complex.I * (L : ℂ)) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hL)
  have hder : ∀ z : ℂ, U.derivative.eval z + (Complex.exp (Complex.I * L * z) * (Complex.I * L) *
      V.eval z + Complex.exp (Complex.I * L * z) * V.derivative.eval z) = 0 := by
    intro z
    have he : HasDerivAt (fun z : ℂ => Complex.exp (Complex.I * L * z))
        (Complex.exp (Complex.I * L * z) * (Complex.I * L)) z := by
      simpa using ((hasDerivAt_id z).const_mul (Complex.I * (L : ℂ))).cexp
    have htot := (Polynomial.hasDerivAt U z).add (he.mul (Polynomial.hasDerivAt V z))
    have hfun : (fun z : ℂ => U.eval z + Complex.exp (Complex.I * L * z) * V.eval z) =
        fun _ => (0 : ℂ) := funext h
    have htot' : HasDerivAt (fun z : ℂ => U.eval z + Complex.exp (Complex.I * L * z) * V.eval z)
        (U.derivative.eval z + (Complex.exp (Complex.I * L * z) * (Complex.I * L) * V.eval z +
          Complex.exp (Complex.I * L * z) * V.derivative.eval z)) z := htot
    rw [hfun] at htot'
    exact (htot'.unique (hasDerivAt_const z (0 : ℂ)))
  have hkey : U.derivative * V = U * (V.derivative + C (Complex.I * L) * V) := by
    refine Polynomial.funext fun z => ?_
    have h1 := h z
    have h2 := hder z
    have hU : U.eval z = -(Complex.exp (Complex.I * L * z) * V.eval z) := by linear_combination h1
    have hU' : U.derivative.eval z = -(Complex.exp (Complex.I * L * z) *
        (Complex.I * L * V.eval z + V.derivative.eval z)) := by linear_combination h2
    simp only [eval_mul, eval_add, eval_C]
    rw [hU, hU']
    ring
  have hV : V = 0 := by
    by_contra hV0
    have hU0 : U ≠ 0 := by
      intro hU0
      apply hV0
      refine poly_eq_zero_of_eval fun z => ?_
      have := h z
      rw [hU0] at this
      simp only [eval_zero, zero_add, mul_eq_zero] at this
      exact this.resolve_left (Complex.exp_ne_zero _)
    have hdW : (V.derivative + C (Complex.I * L) * V).degree = V.degree := by
      have h1 : (C (Complex.I * L) * V).degree = V.degree := degree_C_mul hIL
      rw [add_comm, degree_add_eq_left_of_degree_lt (by rw [h1]; exact degree_derivative_lt hV0), h1]
    have hlt : (U.derivative * V).degree < (U * (V.derivative + C (Complex.I * L) * V)).degree := by
      rw [degree_mul, degree_mul, hdW]
      exact WithBot.add_lt_add_right (degree_ne_bot.2 hV0) (degree_derivative_lt hU0)
    rw [hkey] at hlt
    exact lt_irrefl _ hlt
  refine ⟨poly_eq_zero_of_eval fun z => ?_, hV⟩
  have := h z
  rw [hV] at this
  simpa using this


/-! ### Roots of the shifted products -/

/-- The complex multiset `{q_j + a}`. -/
def shiftMS (q : Fin N → ℝ) (a : ℂ) : Multiset ℂ := Multiset.map (fun j => (q j : ℂ) + a) Finset.univ.val

theorem shiftPoly_eq (q : Fin N → ℝ) (a : ℂ) :
    shiftPoly q a = ((shiftMS q a).map fun r => X - C r).prod := by
  unfold shiftPoly shiftMS
  rw [Multiset.map_map]
  rfl

theorem roots_shiftPoly (q : Fin N → ℝ) (a : ℂ) : (shiftPoly q a).roots = shiftMS q a := by
  rw [shiftPoly_eq, roots_multiset_prod_X_sub_C]

theorem shiftPoly_ne_zero (q : Fin N → ℝ) (a : ℂ) : shiftPoly q a ≠ 0 :=
  (monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _).ne_zero

theorem shiftMS_zero (q : Fin N → ℝ) :
    shiftMS q 0 = Multiset.map (fun r : ℝ => (r : ℂ)) (msOf q) := by
  unfold shiftMS msOf
  rw [Multiset.map_map]
  simp

/-- **No real cancellation**: if `P⁻_p · D_q = P⁻_q · D_p` (zeros of the numerators at
`q_j - ic`, off the real axis for `c ≠ 0`), the real zeros — the rapidity multisets — agree. -/
theorem msOf_eq_of_prod_eq {c : ℝ} (hc : c ≠ 0) (p q : Fin N → ℝ)
    (h : shiftPoly p (-(Complex.I * c)) * shiftPoly q 0 =
      shiftPoly q (-(Complex.I * c)) * shiftPoly p 0) : msOf p = msOf q := by
  have hr := congrArg Polynomial.roots h
  rw [roots_mul (mul_ne_zero (shiftPoly_ne_zero _ _) (shiftPoly_ne_zero _ _)),
    roots_mul (mul_ne_zero (shiftPoly_ne_zero _ _) (shiftPoly_ne_zero _ _)),
    roots_shiftPoly, roots_shiftPoly, roots_shiftPoly, roots_shiftPoly] at hr
  have hfilt := congrArg (Multiset.filter (fun r : ℂ => r.im = 0)) hr
  have hnon : ∀ r : Fin N → ℝ, Multiset.filter (fun x : ℂ => x.im = 0)
      (shiftMS r (-(Complex.I * c))) = 0 := by
    intro r
    rw [Multiset.filter_eq_nil]
    intro x hx
    unfold shiftMS at hx
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hx
    simpa using hc
  have hall : ∀ r : Fin N → ℝ, Multiset.filter (fun x : ℂ => x.im = 0) (shiftMS r 0) = shiftMS r 0 := by
    intro r
    rw [Multiset.filter_eq_self]
    intro x hx
    unfold shiftMS at hx
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hx
    simp
  rw [Multiset.filter_add, Multiset.filter_add, hnon, hnon, hall, hall, zero_add, zero_add] at hfilt
  rw [shiftMS_zero, shiftMS_zero] at hfilt
  exact (Multiset.map_injective Complex.ofReal_injective hfilt.symm)


/-! ### Separation (1) -/

/-- The finite set of real poles of `s_p` and `s_q`. -/
def poles (p q : Fin N → ℝ) : Finset ℂ :=
  Finset.univ.image (fun j => (p j : ℂ)) ∪ Finset.univ.image (fun j => (q j : ℂ))

theorem not_mem_poles {p q : Fin N → ℝ} {z : ℂ} (hz : z ∉ poles p q) :
    (∀ j, z ≠ p j) ∧ ∀ j, z ≠ q j := by
  simp only [poles, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, not_or,
    not_exists] at hz
  exact ⟨fun j hj => hz.1 j hj.symm, fun j hj => hz.2 j hj.symm⟩

theorem dense_compl_finset (B : Finset ℂ) : Dense ((B : Set ℂ)ᶜ) := by
  have h := Dense.sdiff_finite (dense_univ (X := ℂ)) B.finite_toSet
  simpa [Set.compl_eq_univ_sdiff] using h

/-- **Separation, version with an extra finite exceptional set `Q`**: if the transfer functions of
`p` and `q` agree at every `z` outside the (finite) poles and `Q`, then the rapidity multisets agree.
(`L > 0`, `c > 0`.)  Proof as printed: clear denominators to `R + e^{iLz} T = 0`, separate the rational
and exponential parts (`exp_poly_eq_zero`), then read the multiset off the real zeros. -/
theorem separation_cofinite {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (p q : Fin N → ℝ)
    (Q : Finset ℂ)
    (h : ∀ z : ℂ, z ∉ poles p q ∪ Q → sFun L c p z = sFun L c q z) : msOf p = msOf q := by
  set Dp := shiftPoly p 0 with hDp
  set Dq := shiftPoly q 0 with hDq
  set U : ℂ[X] := shiftPoly p (-(Complex.I * c)) * Dq - shiftPoly q (-(Complex.I * c)) * Dp with hU
  set V : ℂ[X] := shiftPoly p (Complex.I * c) * Dq - shiftPoly q (Complex.I * c) * Dp with hV
  have hoff : ∀ z : ℂ, z ∉ poles p q ∪ Q →
      U.eval z + Complex.exp (Complex.I * L * z) * V.eval z = 0 := by
    intro z hz
    have hzp : z ∉ poles p q := fun h' => hz (Finset.mem_union_left _ h')
    obtain ⟨hp, hq⟩ := not_mem_poles hzp
    have hs := h z hz
    unfold sFun at hs
    have h1 := prod_plus_mul c p z hp
    have h2 := prod_minus_mul c p z hp
    have h3 := prod_plus_mul c q z hq
    have h4 := prod_minus_mul c q z hq
    simp only [hU, hV, eval_sub, eval_mul]
    rw [← h1, ← h2, ← h3, ← h4]
    linear_combination (Dp.eval z * Dq.eval z) * hs
  have hall : ∀ z : ℂ, U.eval z + Complex.exp (Complex.I * L * z) * V.eval z = 0 := by
    have hcont : Continuous fun z : ℂ => U.eval z + Complex.exp (Complex.I * L * z) * V.eval z := by
      exact ((Polynomial.differentiable U).continuous.add ((Complex.continuous_exp.comp (continuous_const.mul continuous_id)).mul
        (Polynomial.differentiable V).continuous))
    have hdense : Dense (((poles p q ∪ Q : Finset ℂ) : Set ℂ)ᶜ) := dense_compl_finset _
    have := hcont.ext_on hdense continuous_const (f := fun z : ℂ => U.eval z +
      Complex.exp (Complex.I * L * z) * V.eval z) (g := fun _ => (0 : ℂ)) (fun z hz => by
        have hz' : z ∉ poles p q ∪ Q := by simpa using hz
        exact hoff z hz')
    exact fun z => congrFun this z
  obtain ⟨hU0, -⟩ := exp_poly_eq_zero hL.ne' U V hall
  apply msOf_eq_of_prod_eq hc.ne' p q
  exact sub_eq_zero.1 hU0

/-- **(1) Separation of transfer functions** (`c > 0`): if `s_p = s_q` as functions on the common
domain `ℂ ∖ (real poles)`, then the rapidity multisets coincide; equivalently distinct multisets have
distinct transfer functions. -/
theorem separation {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (p q : Fin N → ℝ)
    (h : ∀ z : ℂ, z ∉ poles p q → sFun L c p z = sFun L c q z) : msOf p = msOf q :=
  separation_cofinite hL hc p q ∅ fun z hz => h z (by simpa using hz)

theorem exists_ne_of_msOf_ne {L c : ℝ} (hL : 0 < L) (hc : 0 < c) {p q : Fin N → ℝ}
    (hne : msOf p ≠ msOf q) : ∃ z : ℂ, z ∉ poles p q ∧ sFun L c p z ≠ sFun L c q z := by
  by_contra hcon
  push Not at hcon
  exact hne (separation hL hc p q hcon)

end QuantumNLS.TransferSeparationContinuityRepair

-- Fresh repair copy; frozen TransferSeparation.lean and its object are preserved.

#print axioms QuantumNLS.TransferSeparationContinuityRepair.sFun
#print axioms QuantumNLS.TransferSeparationContinuityRepair.msOf
#print axioms QuantumNLS.TransferSeparationContinuityRepair.OnShell
#print axioms QuantumNLS.TransferSeparationContinuityRepair.shiftPoly
#print axioms QuantumNLS.TransferSeparationContinuityRepair.eval_shiftPoly
#print axioms QuantumNLS.TransferSeparationContinuityRepair.prod_plus_mul
#print axioms QuantumNLS.TransferSeparationContinuityRepair.prod_minus_mul
#print axioms QuantumNLS.TransferSeparationContinuityRepair.poly_eq_zero_of_eval
#print axioms QuantumNLS.TransferSeparationContinuityRepair.exp_poly_eq_zero
#print axioms QuantumNLS.TransferSeparationContinuityRepair.shiftMS
#print axioms QuantumNLS.TransferSeparationContinuityRepair.shiftPoly_eq
#print axioms QuantumNLS.TransferSeparationContinuityRepair.roots_shiftPoly
#print axioms QuantumNLS.TransferSeparationContinuityRepair.shiftPoly_ne_zero
#print axioms QuantumNLS.TransferSeparationContinuityRepair.shiftMS_zero
#print axioms QuantumNLS.TransferSeparationContinuityRepair.msOf_eq_of_prod_eq
#print axioms QuantumNLS.TransferSeparationContinuityRepair.poles
#print axioms QuantumNLS.TransferSeparationContinuityRepair.not_mem_poles
#print axioms QuantumNLS.TransferSeparationContinuityRepair.dense_compl_finset
#print axioms QuantumNLS.TransferSeparationContinuityRepair.separation_cofinite
#print axioms QuantumNLS.TransferSeparationContinuityRepair.separation
#print axioms QuantumNLS.TransferSeparationContinuityRepair.exists_ne_of_msOf_ne
