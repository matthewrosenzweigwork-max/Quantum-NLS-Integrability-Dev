import NlsGge.Spectral.CumulativePowerIntegralFromIntervalIntegrableV3
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open MeasureTheory
open NlsGge.SpectralFoundations.CumulativePowerV3

namespace NlsGge.SpectralFoundations.CumulativePowerGeneralEndpointV1

private lemma constant_ac (T : ℝ) :
    AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) 0 T := by
  rw [absolutelyContinuousOnInterval_iff]
  intro ε hε
  refine ⟨1, by norm_num, ?_⟩
  intro E hE hlen
  simpa using hε

private lemma primitive_ac (q : ℝ → ℝ) (T : ℝ)
    (hq : IntervalIntegrable q volume 0 T) :
    AbsolutelyContinuousOnInterval (actualCumulativeRealIntegral q) 0 T := by
  simpa only [actualCumulativeRealIntegral] using!
    hq.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)

private lemma primitive_hasDerivAt_ae (q : ℝ → ℝ) (T : ℝ)
    (hq : IntervalIntegrable q volume 0 T) :
    ∀ᵐ s ∂volume, s ∈ Set.uIcc 0 T →
      HasDerivAt (actualCumulativeRealIntegral q) (q s) s := by
  filter_upwards [hq.ae_hasDerivAt_integral] with s hs
  intro hsT
  simpa only [actualCumulativeRealIntegral] using! hs hsT 0 (by simp)

private lemma primitive_pow_ac (q : ℝ → ℝ) (T : ℝ)
    (hq : IntervalIntegrable q volume 0 T) :
    ∀ k : ℕ, AbsolutelyContinuousOnInterval
      (fun s => actualCumulativeRealIntegral q s ^ k) 0 T := by
  have hQ := primitive_ac q T hq
  have hOne : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) 0 T :=
    constant_ac T
  intro k
  induction k with
  | zero => simpa using hOne
  | succ k hk =>
      have hprod := hk.mul hQ
      exact hprod.congr (by
        intro s hs
        simp [pow_succ])

private lemma primitive_pow_deriv_ae (q : ℝ → ℝ) (T : ℝ)
    (hq : IntervalIntegrable q volume 0 T)
    (n : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ∀ᵐ s ∂volume, s ∈ Set.uIcc 0 t →
      deriv (fun x => actualCumulativeRealIntegral q x ^ (n + 1)) s =
        (n + 1 : ℝ) *
          (q s * actualCumulativeRealIntegral q s ^ n) := by
  have htSubset : Set.uIcc 0 t ⊆ Set.uIcc 0 T := by
    intro s hs
    rw [Set.uIcc_of_le ht0] at hs
    rw [Set.uIcc_of_le (le_trans ht0 htT)]
    exact ⟨hs.1, hs.2.trans htT⟩
  have hQderiv := primitive_hasDerivAt_ae q T hq
  filter_upwards [hQderiv] with s hs hs_t
  have hsT := hs (htSubset hs_t)
  have hpow := (hsT.pow (n + 1)).deriv
  simpa only [Pi.pow_apply, Nat.succ_sub_one, Nat.cast_add, Nat.cast_one,
    mul_assoc, mul_left_comm, mul_comm] using! hpow

/-- The cumulative-power identity on an arbitrary actual interval `[0,T]`.
It requires only interval integrability of `q`, with no sign or continuity
assumption. -/
theorem intervalIntegral_cumulativePower_eq
    (q : ℝ → ℝ) (T : ℝ) (hq : IntervalIntegrable q volume 0 T)
    (n : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (htT : t ≤ T) :
    (∫ s in (0 : ℝ)..t,
      q s * actualCumulativeRealIntegral q s ^ n) =
        actualCumulativeRealIntegral q t ^ (n + 1) / (n + 1 : ℝ) := by
  let Q := actualCumulativeRealIntegral q
  have htSubset : Set.uIcc 0 t ⊆ Set.uIcc 0 T := by
    intro s hs
    rw [Set.uIcc_of_le ht0] at hs
    rw [Set.uIcc_of_le (le_trans ht0 htT)]
    exact ⟨hs.1, hs.2.trans htT⟩
  have hQpow_ac := primitive_pow_ac q T hq
  have hderiv_ae := primitive_pow_deriv_ae q T hq n t ht0 htT
  have hFTC :
      (∫ s in (0 : ℝ)..t, deriv (fun x => Q x ^ (n + 1)) s) =
        Q t ^ (n + 1) - Q 0 ^ (n + 1) :=
    (hQpow_ac (n + 1)).mono htSubset |>.integral_deriv_eq_sub
  have hderiv_integral :
      (∫ s in (0 : ℝ)..t, deriv (fun x => Q x ^ (n + 1)) s) =
        (∫ s in (0 : ℝ)..t, (n + 1 : ℝ) * (q s * Q s ^ n)) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hderiv_ae] with s hs hs_t
    have hs_t' : s ∈ Set.uIcc 0 t := Set.uIoc_subset_uIcc hs_t
    have h := hs hs_t'
    simpa only [Q] using h
  have hQzero : Q 0 = 0 := by simp [Q, actualCumulativeRealIntegral]
  rw [hderiv_integral, intervalIntegral.integral_const_mul] at hFTC
  have hscale :
      (n + 1 : ℝ) * (∫ s in (0 : ℝ)..t, q s * Q s ^ n) = Q t ^ (n + 1) := by
    simpa [hQzero] using hFTC
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  calc
    (∫ s in (0 : ℝ)..t, q s * Q s ^ n) =
        (n + 1 : ℝ)⁻¹ * ((n + 1 : ℝ) *
          (∫ s in (0 : ℝ)..t, q s * Q s ^ n)) := by
            field_simp [hn]
    _ = Q t ^ (n + 1) / (n + 1 : ℝ) := by
          rw [hscale, div_eq_mul_inv]
          ring

/-- The cumulative-power integrand is interval-integrable on every initial
subinterval `[0,t]` contained in `[0,T]`, from integrability of `q` alone. -/
theorem intervalIntegrable_cumulativePower
    (q : ℝ → ℝ) (T : ℝ) (hq : IntervalIntegrable q volume 0 T)
    (n : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (htT : t ≤ T) :
    IntervalIntegrable
      (fun s => q s * actualCumulativeRealIntegral q s ^ n) volume 0 t := by
  have htSubset : Set.uIcc 0 t ⊆ Set.uIcc 0 T := by
    intro s hs
    rw [Set.uIcc_of_le ht0] at hs
    rw [Set.uIcc_of_le (le_trans ht0 htT)]
    exact ⟨hs.1, hs.2.trans htT⟩
  have hq_t : IntervalIntegrable q volume 0 t := hq.mono htSubset le_rfl
  have hQ_ac : AbsolutelyContinuousOnInterval
      (actualCumulativeRealIntegral q) 0 t := by
    simpa only [actualCumulativeRealIntegral] using!
      hq_t.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)
  have hQpow_cont : ContinuousOn
      (fun s => actualCumulativeRealIntegral q s ^ n) (Set.uIcc 0 t) :=
    hQ_ac.continuousOn.pow n
  simpa only [Pi.mul_apply] using!
    hq_t.mul_continuousOn hQpow_cont

end NlsGge.SpectralFoundations.CumulativePowerGeneralEndpointV1

end
