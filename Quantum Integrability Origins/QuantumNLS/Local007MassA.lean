import Mathlib
import QuantumNLS.Local007EvalT

/-! LOCAL-007 stage M1: the real series identity `arsinh(√s) = √s Ω(s)`, `Ω(s) = Σ C(-1/2,j)/(2j+1) s^j`
(`0 ≤ s < 1`), and `arcosh(√(1+s)) = arsinh(√s)`. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set Metric
open scoped Interval
namespace QuantumNLS.Local007MassA
open QuantumNLS.Local007AlgB (cOm radius_Om)
open QuantumNLS.Local007EvalT (OmC)

theorem arcosh_sqrt {s : ℝ} (hs : 0 ≤ s) : Real.arcosh (Real.sqrt (1 + s)) = Real.arsinh (Real.sqrt s) := by
  have h1 : Real.cosh (Real.arsinh (Real.sqrt s)) = Real.sqrt (1 + s) := by
    rw [Real.cosh_arsinh, Real.sq_sqrt hs, add_comm]
  have h2 : 0 ≤ Real.arsinh (Real.sqrt s) := Real.arsinh_nonneg_iff.2 (Real.sqrt_nonneg _)
  rw [← h1, Real.arcosh_cosh h2]

/-- Real binomial series `(1+x)^{-1/2}`. -/
theorem hasSum_binom_real {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ => Ring.choose (-1 / 2 : ℝ) n * x ^ n) ((Real.sqrt (1 + x))⁻¹) := by
  have hmem : (x : ℂ) ∈ Metric.eball (0 : ℂ) 1 := by
    rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs]
    exact ENNReal.ofReal_lt_one.2 hx
  have h4 := (Complex.one_add_cpow_hasFPowerSeriesOnBall_zero (a := (-1 / 2 : ℂ))).hasSum hmem
  rw [zero_add] at h4
  have hb' : binomialSeries ℂ (-1 / 2 : ℂ) =
      FormalMultilinearSeries.ofScalars ℂ (fun n => Ring.choose (-1 / 2 : ℂ) n) := rfl
  simp only [hb', FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] at h4
  have e : ∀ n : ℕ, Ring.choose (-1 / 2 : ℂ) n * (x : ℂ) ^ n = ((Ring.choose (-1 / 2 : ℝ) n * x ^ n : ℝ) : ℂ) := by
    intro n
    rw [show (Ring.choose (-1 / 2 : ℂ) n) = ((Ring.choose (-1 / 2 : ℝ) n : ℝ) : ℂ) by
      rw [Complex.ofReal_choose]; push_cast; rfl]
    push_cast; ring
  simp only [e] at h4
  have h1x : 0 ≤ 1 + x := by linarith [(abs_lt.1 hx).1]
  have e2 : (1 + (x : ℂ)) ^ (-1 / 2 : ℂ) = (((Real.sqrt (1 + x))⁻¹ : ℝ) : ℂ) := by
    have : (1 + (x : ℂ)) = ((1 + x : ℝ) : ℂ) := by push_cast; rfl
    rw [this, show (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_cpow h1x]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_mul h1x]
    norm_num
  rw [e2] at h4
  exact Complex.hasSum_ofReal.1 h4

theorem arsinh_om {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    Real.arsinh (Real.sqrt s) = Real.sqrt s * ∑' j : ℕ, cOm j * s ^ j := by
  rcases hs0.eq_or_lt with h | hpos
  · subst h; simp
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hpos
  -- FTC
  have hFTC : ∫ y in (0 : ℝ)..1, Real.sqrt s * (Real.sqrt (1 + s * y ^ 2))⁻¹ = Real.arsinh (Real.sqrt s) := by
    have hd : ∀ y ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun y => Real.arsinh (Real.sqrt s * y))
        (Real.sqrt s * (Real.sqrt (1 + s * y ^ 2))⁻¹) y := by
      intro y _
      have h1 := (Real.hasDerivAt_arsinh (Real.sqrt s * y)).comp y ((hasDerivAt_id y).const_mul (Real.sqrt s))
      have e : (Real.sqrt s * y) ^ 2 = s * y ^ 2 := by rw [mul_pow, Real.sq_sqrt hpos.le]
      exact h1.congr_deriv (by simp only [e, mul_one]; ring)
    have hi : IntervalIntegrable (fun y : ℝ => Real.sqrt s * (Real.sqrt (1 + s * y ^ 2))⁻¹) volume 0 1 := by
      apply Continuous.intervalIntegrable
      refine continuous_const.mul (Continuous.inv₀ (by fun_prop) fun y => ?_)
      exact (Real.sqrt_pos.2 (by positivity)).ne'
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
    simp
  -- termwise integration
  let G : ℕ → ℝ → ℝ := fun j y => Real.sqrt s * (Ring.choose (-1 / 2 : ℝ) j * (s * y ^ 2) ^ j)
  have hrad : ∀ r : ℝ, 0 ≤ r → r < 1 → Summable fun j : ℕ => |Ring.choose (-1 / 2 : ℝ) j| * r ^ j := by
    intro r hr0 hr1
    have h1 : 1 ≤ (binomialSeries ℝ (-1 / 2 : ℝ)).radius := binomialSeries_radius_ge_one
    have hr : ((Real.toNNReal r : NNReal) : ENNReal) < (binomialSeries ℝ (-1 / 2 : ℝ)).radius := by
      refine lt_of_lt_of_le ?_ h1
      show ENNReal.ofReal r < 1
      exact ENNReal.ofReal_lt_one.2 hr1
    have := (binomialSeries ℝ (-1 / 2 : ℝ)).summable_norm_mul_pow hr
    rw [Real.coe_toNNReal r hr0] at this
    have hb : binomialSeries ℝ (-1 / 2 : ℝ) =
        FormalMultilinearSeries.ofScalars ℝ (fun n => Ring.choose (-1 / 2 : ℝ) n) := rfl
    simp only [hb, FormalMultilinearSeries.ofScalars_norm, Real.norm_eq_abs] at this
    exact this
  have hsum := hrad s hpos.le hs1
  have hGm : ∀ j, AEStronglyMeasurable (G j) (volume.restrict (Ioc (0 : ℝ) 1)) := fun j =>
    (by fun_prop : Continuous (G j)).aestronglyMeasurable
  have hGb : ∀ j, ∀ᵐ y ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      ‖G j y‖ ≤ Real.sqrt s * (|Ring.choose (-1 / 2 : ℝ) j| * s ^ j) := by
    intro j
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    have h1 : y ^ 2 ≤ 1 := by nlinarith [hy.1, hy.2]
    change ‖Real.sqrt s * (Ring.choose (-1 / 2 : ℝ) j * (s * y ^ 2) ^ j)‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hsq, abs_mul, abs_pow, abs_of_nonneg (by positivity : 0 ≤ s * y ^ 2)]
    have h2 : (s * y ^ 2) ^ j ≤ s ^ j := pow_le_pow_left₀ (by positivity) (by nlinarith) j
    gcongr
  have hlim : ∀ᵐ y ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      HasSum (fun j => G j y) (Real.sqrt s * (Real.sqrt (1 + s * y ^ 2))⁻¹) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    have h1 : y ^ 2 ≤ 1 := by nlinarith [hy.1, hy.2]
    have hx : |s * y ^ 2| < 1 := by
      rw [abs_of_nonneg (by positivity)]; nlinarith [sq_nonneg y]
    exact (hasSum_binom_real hx).mul_left (Real.sqrt s)
  have hdom := hasSum_integral_of_dominated_convergence (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (fun j (_ : ℝ) => Real.sqrt s * (|Ring.choose (-1 / 2 : ℝ) j| * s ^ j)) hGm hGb
    (ae_of_all _ fun _ => hsum.mul_left _) (integrable_const _) hlim
  have e1 : ∀ j : ℕ, ∫ y in Ioc (0 : ℝ) 1, G j y = Real.sqrt s * (cOm j * s ^ j) := by
    intro j
    rw [← intervalIntegral.integral_of_le (zero_le_one' ℝ)]
    have : ∀ y : ℝ, G j y = (Real.sqrt s * Ring.choose (-1 / 2 : ℝ) j * s ^ j) * y ^ (2 * j) := by
      intro y; simp only [G]; rw [mul_pow, ← pow_mul]; ring
    simp only [this]
    rw [intervalIntegral.integral_const_mul, integral_pow]
    unfold cOm
    have h2 : ((2 * j : ℕ) : ℝ) + 1 = 2 * (j : ℝ) + 1 := by push_cast; ring
    have h3 : (2 * (j : ℝ) + 1) ≠ 0 := by positivity
    simp only [one_pow, zero_pow (Nat.succ_ne_zero _), sub_zero]
    push_cast
    field_simp
  have e2 : ∫ y in Ioc (0 : ℝ) 1, Real.sqrt s * (Real.sqrt (1 + s * y ^ 2))⁻¹ = Real.arsinh (Real.sqrt s) := by
    rw [← hFTC, intervalIntegral.integral_of_le (zero_le_one' ℝ)]
  simp only [e1, e2] at hdom
  rw [← hdom.tsum_eq, tsum_mul_left]

end QuantumNLS.Local007MassA
#print axioms QuantumNLS.Local007MassA.arsinh_om
