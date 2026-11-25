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

namespace NlsGge.SpectralFoundations.CumulativePowerV3

/-- The oriented cumulative integral of a real interval-integrable source. -/
def actualCumulativeRealIntegral (q : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, q s

private lemma actualCumulativePower_constant_ac :
    AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) 0 1 := by
  rw [absolutelyContinuousOnInterval_iff]
  intro ε hε
  refine ⟨1, by norm_num, ?_⟩
  intro E hE hlen
  simpa using hε

private lemma actualCumulativePower_primitive_ac
    (q : ℝ → ℝ) (hq : IntervalIntegrable q volume 0 1) :
    AbsolutelyContinuousOnInterval (actualCumulativeRealIntegral q) 0 1 := by
  simpa only [actualCumulativeRealIntegral] using!
    hq.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)

private lemma actualCumulativePower_primitive_hasDerivAt_ae
    (q : ℝ → ℝ) (hq : IntervalIntegrable q volume 0 1) :
    ∀ᵐ s ∂volume, s ∈ Set.uIcc 0 1 →
      HasDerivAt (actualCumulativeRealIntegral q) (q s) s := by
  filter_upwards [hq.ae_hasDerivAt_integral] with s hs
  intro hs01
  simpa only [actualCumulativeRealIntegral] using! hs hs01 0 (by simp)

private lemma actualCumulativePower_primitive_pow_ac
    (q : ℝ → ℝ) (hq : IntervalIntegrable q volume 0 1) :
    ∀ k : ℕ, AbsolutelyContinuousOnInterval
      (fun s => actualCumulativeRealIntegral q s ^ k) 0 1 := by
  have hQ := actualCumulativePower_primitive_ac q hq
  have hOne : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) 0 1 :=
    actualCumulativePower_constant_ac
  intro k
  induction k with
  | zero => simpa using hOne
  | succ k hk =>
      have hprod := hk.mul hQ
      exact hprod.congr (by
        intro s hs
        simp [pow_succ])

private lemma actualCumulativePower_primitive_pow_deriv_ae
    (q : ℝ → ℝ) (hq : IntervalIntegrable q volume 0 1)
    (n : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∀ᵐ s ∂volume, s ∈ Set.uIcc 0 t →
      deriv (fun x => actualCumulativeRealIntegral q x ^ (n + 1)) s =
        (n + 1 : ℝ) * (q s * actualCumulativeRealIntegral q s ^ n) := by
  have htSubset : Set.uIcc 0 t ⊆ Set.uIcc 0 1 := by
    intro s hs
    rw [Set.uIcc_of_le ht0] at hs
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ⟨hs.1, hs.2.trans ht1⟩
  have hQderiv := actualCumulativePower_primitive_hasDerivAt_ae q hq
  filter_upwards [hQderiv] with s hs hs_t
  have hs01 := hs (htSubset hs_t)
  have hpow := (hs01.pow (n + 1)).deriv
  simpa only [Pi.pow_apply, Nat.succ_sub_one, Nat.cast_add, Nat.cast_one,
    mul_assoc, mul_left_comm, mul_comm] using! hpow

/-- The cumulative-power integral identity for a real interval-integrable
source. In particular, it requires no nonnegativity or continuity assumption
on `q`; those hypotheses belong only to later majorant arguments. -/
theorem intervalIntegral_cumulativePower_eq
    (q : ℝ → ℝ) (hq : IntervalIntegrable q volume 0 1)
    (n : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫ s in (0 : ℝ)..t,
      q s * actualCumulativeRealIntegral q s ^ n) =
        actualCumulativeRealIntegral q t ^ (n + 1) / (n + 1 : ℝ) := by
  let Q := actualCumulativeRealIntegral q
  have htSubset : Set.uIcc 0 t ⊆ Set.uIcc 0 1 := by
    intro s hs
    rw [Set.uIcc_of_le ht0] at hs
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ⟨hs.1, hs.2.trans ht1⟩
  have hQpow_ac := actualCumulativePower_primitive_pow_ac q hq
  have hderiv_ae := actualCumulativePower_primitive_pow_deriv_ae
    q hq n t ht0 ht1
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

end NlsGge.SpectralFoundations.CumulativePowerV3

end
