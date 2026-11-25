import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-! Factorial integral identity for a product on an ordered simplex.

The simplex integral is represented by its standard iterated interval integral:
the new outer variable is the largest coordinate, and the previous simplex is
integrated below it. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped Interval

namespace NlsGge.Atomic.G1

/-- Iterated integral of the product over `0 ≤ xₙ ≤ ⋯ ≤ x₁ ≤ t`. -/
def simplexIntegral : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, _, _ => 1
  | n + 1, f, t => ∫ x in (0 : ℝ)..t, f x * simplexIntegral n f x

/-- Integrating the derivative of a power of the primitive gives the scalar
factorial step. -/
theorem intervalIntegral_mul_primitive_pow (f : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hf : IntegrableOn f (Set.Icc (0 : ℝ) t)) (n : ℕ) :
    ∫ x in (0 : ℝ)..t, f x * (∫ s in (0 : ℝ)..x, f s) ^ n =
      (∫ s in (0 : ℝ)..t, f s) ^ (n + 1) / (n + 1 : ℝ) := by
  let F : ℝ → ℝ := fun x => ∫ s in (0 : ℝ)..x, f s
  have hfi : IntervalIntegrable f volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht).2 hf
  have hF : AbsolutelyContinuousOnInterval F 0 t := by
    exact hfi.absolutelyContinuousOnInterval_intervalIntegral (c := 0) Set.left_mem_uIcc
  have hpow : ∀ m : ℕ, AbsolutelyContinuousOnInterval (fun x => F x ^ m) 0 t := by
    intro m
    induction m with
    | zero =>
        have hconst : LipschitzOnWith (K := (0 : NNReal))
            (f := fun _ : ℝ => (1 : ℝ)) (s := Set.uIcc (0 : ℝ) t) := by
          intro x hx y hy
          simp
        exact LipschitzOnWith.absolutelyContinuousOnInterval (a := (0 : ℝ)) (b := t) hconst
    | succ m hm =>
        convert hm.mul hF using 1
        ext x
        simp only [Pi.mul_apply, pow_succ]
  have hG : AbsolutelyContinuousOnInterval (fun x => F x ^ (n + 1)) 0 t := hpow (n + 1)
  have hderiv : ∀ᵐ x, x ∈ Set.uIcc 0 t →
      deriv (fun x => F x ^ (n + 1)) x =
        ((n + 1 : ℕ) : ℝ) * F x ^ n * f x := by
    filter_upwards [hfi.ae_hasDerivAt_integral] with x hx
    intro hxI
    have hFx : HasDerivAt F (f x) x := by
      exact hx hxI 0 Set.left_mem_uIcc
    have hGx := hFx.pow (n + 1)
    have hpowFn : ((fun y : ℝ => F y) ^ (n + 1)) = (fun y => F y ^ (n + 1)) := by
      funext y
      simp
    have hcast : ((n + 1 : ℕ) : ℝ) * F x ^ ((n + 1 : ℕ) - 1) * f x =
        ((n + 1 : ℕ) : ℝ) * F x ^ n * f x := by simp
    rw [hpowFn] at hGx
    simpa [hcast] using hGx.deriv
  have hIntDeriv := hG.integral_deriv_eq_sub
  have hIntEq : ∫ x in (0 : ℝ)..t, deriv (fun x => F x ^ (n + 1)) x =
      ((n + 1 : ℕ) : ℝ) * ∫ x in (0 : ℝ)..t, f x * F x ^ n := by
    calc
      _ = ∫ x in (0 : ℝ)..t, ((n + 1 : ℕ) : ℝ) * F x ^ n * f x :=
        intervalIntegral.integral_congr_ae (by
          filter_upwards [hderiv] with x hx
          intro hxI
          exact hx (Set.uIoc_subset_uIcc hxI))
      _ = ((n + 1 : ℕ) : ℝ) * ∫ x in (0 : ℝ)..t, f x * F x ^ n := by
        calc
          _ = ∫ x in (0 : ℝ)..t, ((n + 1 : ℕ) : ℝ) * (f x * F x ^ n) := by
            apply intervalIntegral.integral_congr
            intro x hx
            ring
          _ = _ := intervalIntegral.integral_const_mul _ _
  rw [hIntEq] at hIntDeriv
  have hzero : F 0 = 0 := by simp [F]
  rw [hzero, zero_pow (Nat.succ_ne_zero n), sub_zero] at hIntDeriv
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  change (∫ x in (0 : ℝ)..t, f x * F x ^ n) = F t ^ (n + 1) / (n + 1 : ℝ)
  calc
    _ = ((n + 1 : ℕ) : ℝ)⁻¹ * (((n + 1 : ℕ) : ℝ) *
          ∫ x in (0 : ℝ)..t, f x * F x ^ n) := by field_simp [ne_of_gt hn]
    _ = ((n + 1 : ℕ) : ℝ)⁻¹ * F t ^ (n + 1) := by rw [hIntDeriv]
    _ = _ := by simp only [F]; field_simp [div_eq_mul_inv]; push_cast; ring_nf

/-- The ordered-simplex product integral is the `n`th power of the one-variable
integral divided by `n!`. The hypotheses are integrability on the interval,
a.e. nonnegativity there, and the endpoint condition `0 ≤ t`. -/
theorem ordered_simplex_product (f : ℝ → ℝ) (n : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (hf : IntegrableOn f (Set.Icc (0 : ℝ) t))
    (hf0 : 0 ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) t)] f) :
    simplexIntegral n f t = (∫ s in (0 : ℝ)..t, f s) ^ n / n.factorial := by
  induction n generalizing t with
  | zero => simp [simplexIntegral]
  | succ n ih =>
      rw [simplexIntegral]
      have hsub (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) t) :
          IntegrableOn f (Set.Icc (0 : ℝ) x) :=
        hf.mono_set (Set.Icc_subset_Icc_right hx.2)
      have hsub0 (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) t) :
          0 ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) x)] f := by
        exact ae_mono (Measure.restrict_mono (Set.Icc_subset_Icc_right hx.2) le_rfl) hf0
      have heq : ∀ x ∈ Set.Icc (0 : ℝ) t,
          simplexIntegral n f x = (∫ s in (0 : ℝ)..x, f s) ^ n / n.factorial := by
        intro x hx
        exact ih hx.1 (hsub x hx) (hsub0 x hx)
      have hIntEq : ∫ x in (0 : ℝ)..t, f x * simplexIntegral n f x =
          ∫ x in (0 : ℝ)..t, f x * (∫ s in (0 : ℝ)..x, f s) ^ n / n.factorial := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hxI : x ∈ Set.Icc (0 : ℝ) t := by
          simpa [Set.uIcc_of_le ht] using hx
        change f x * simplexIntegral n f x =
          f x * (∫ s in (0 : ℝ)..x, f s) ^ n / n.factorial
        rw [heq x hxI]
        ring
      rw [hIntEq]
      have hscale : ∫ x in (0 : ℝ)..t,
          f x * (∫ s in (0 : ℝ)..x, f s) ^ n / n.factorial =
          (n.factorial : ℝ)⁻¹ * ∫ x in (0 : ℝ)..t,
            f x * (∫ s in (0 : ℝ)..x, f s) ^ n := by
        calc
          _ = ∫ x in (0 : ℝ)..t,
              (n.factorial : ℝ)⁻¹ * (f x * (∫ s in (0 : ℝ)..x, f s) ^ n) := by
                apply intervalIntegral.integral_congr
                intro x hx
                simp [div_eq_mul_inv, mul_comm]
          _ = _ := intervalIntegral.integral_const_mul _ _
      rw [hscale, intervalIntegral_mul_primitive_pow f ht hf n]
      rw [Nat.factorial_succ]
      field_simp
      push_cast
      ring_nf

end NlsGge.Atomic.G1
