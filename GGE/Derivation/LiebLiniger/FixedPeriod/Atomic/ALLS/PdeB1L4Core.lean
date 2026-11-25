import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB1TimeConv
import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB1Resonance

/-! # Track B, step B1: the Fourier-side bilinear `L⁴` estimate

Pro report, proof of `X^{0,a} ↪ L⁴(ℝ × 𝕋)` with `a = 13/32`. On the spacetime Fourier side
(`ṽ(τ,n)`, time phase `e^{-itτ}`), `v²` has transform `(2π)^{-1} Σ_k ∫ ṽ(λ,k) ṽ(τ-λ,n-k) dλ`.
Pro bounds its `L²` norm by Cauchy–Schwarz, (timeconv) and (latticesum):
`Σ_m ∫ |Σ_k ∫ ṽ(λ,k) ṽ(τ-λ,m-k) dλ|² dτ ≤ C (Σ_k ∫ ⟨λ+(2πk)²⟩^{2a} |ṽ(λ,k)|² dλ)²`.

This module proves that inequality for an arbitrary family of measurable nonnegative
extended-real functions `F k` (apply it to `F k = |ṽ(·,k)|`), so no integrability or summability
side condition is needed and no totalized branch is used: all sums and integrals are in `ℝ≥0∞`.
The identification of the left side with `‖v‖⁴_{L⁴}` (Plancherel on `ℝ × 𝕋`) is a separate step.
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.ALLS.PdeB

open MeasureTheory
open scoped ENNReal

/-- The modulation weight `⟨λ + (2πk)²⟩^e` as an extended nonnegative real. -/
def modWt (e : ℝ) (k : ℤ) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (brk (t + (2 * Real.pi * k) ^ 2) ^ e)

theorem measurable_modWt (e : ℝ) (k : ℤ) : Measurable (modWt e k) :=
  ENNReal.measurable_ofReal.comp
    ((continuous_brk_rpow e).comp (continuous_id.add continuous_const)).measurable

/-- `⟨·⟩^{-e} ⟨·⟩^{e} = 1`. -/
theorem modWt_neg_mul (e : ℝ) (k : ℤ) (t : ℝ) : modWt (-e) k t * modWt e k t = 1 := by
  unfold modWt
  rw [← ENNReal.ofReal_mul (brk_rpow_nonneg _ _), Real.rpow_neg (brk_pos _).le,
    inv_mul_cancel₀ (Real.rpow_pos_of_pos (brk_pos _) _).ne', ENNReal.ofReal_one]

/-- `(⟨·⟩^{e})² = ⟨·⟩^{2e}`. -/
theorem modWt_sq (e : ℝ) (k : ℤ) (t : ℝ) : modWt e k t ^ 2 = modWt (2 * e) k t := by
  unfold modWt
  rw [← ENNReal.ofReal_pow (brk_rpow_nonneg _ _), ← Real.rpow_natCast,
    ← Real.rpow_mul (brk_pos _).le]
  congr 2
  push_cast
  ring

/-- Cauchy–Schwarz for `Σ_k ∫ dλ` (counting × Lebesgue measure on `ℤ × ℝ`). -/
theorem sum_lintegral_mul_sq_le (X Y : ℤ → ℝ → ℝ≥0∞) (hX : ∀ k, Measurable (X k))
    (hY : ∀ k, Measurable (Y k)) :
    (∑' k, ∫⁻ t, X k t * Y k t) ^ 2 ≤
      (∑' k, ∫⁻ t, X k t ^ 2) * (∑' k, ∫⁻ t, Y k t ^ 2) := by
  set ν : Measure (ℤ × ℝ) := (Measure.count : Measure ℤ).prod volume
  have hXm : Measurable fun p : ℤ × ℝ => X p.1 p.2 :=
    measurable_from_prod_countable_right fun k => hX k
  have hYm : Measurable fun p : ℤ × ℝ => Y p.1 p.2 :=
    measurable_from_prod_countable_right fun k => hY k
  have conv : ∀ Z : ℤ → ℝ → ℝ≥0∞, Measurable (fun p : ℤ × ℝ => Z p.1 p.2) →
      ∑' k, ∫⁻ t, Z k t = ∫⁻ p, Z p.1 p.2 ∂ν := fun Z hZ => by
    rw [lintegral_prod _ hZ.aemeasurable, lintegral_count]
  rw [conv _ (hXm.mul hYm), conv _ (hXm.pow_const 2), conv _ (hYm.pow_const 2)]
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two hXm.aemeasurable
    hYm.aemeasurable
  simp only [Pi.mul_apply, ENNReal.rpow_two] at h
  calc (∫⁻ p, X p.1 p.2 * Y p.1 p.2 ∂ν) ^ 2
      ≤ ((∫⁻ p, X p.1 p.2 ^ 2 ∂ν) ^ (1 / (2 : ℝ)) * (∫⁻ p, Y p.1 p.2 ^ 2 ∂ν) ^ (1 / (2 : ℝ))) ^ 2 :=
        pow_le_pow_left₀ bot_le h 2
    _ = (∫⁻ p, X p.1 p.2 ^ 2 ∂ν) * (∫⁻ p, Y p.1 p.2 ^ 2 ∂ν) := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num

/-- The reciprocal-weight factor is bounded uniformly in `m` and `τ`
(time convolution, then the resonance sum). -/
theorem weight_factor_bound : ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (m : ℤ) (τ : ℝ),
    ∑' k : ℤ, ∫⁻ t, modWt (-(2 * (13 / 32 : ℝ))) k t *
      modWt (-(2 * (13 / 32 : ℝ))) (m - k) (τ - t) ≤ K := by
  obtain ⟨C, hC⟩ := time_conv_bound_pro
  obtain ⟨C', hC'⟩ := resonance_sum_bound_pro
  refine ⟨ENNReal.ofReal (max C 0) * ENNReal.ofReal C', by finiteness, fun m τ => ?_⟩
  set e : ℝ := -(2 * (13 / 32 : ℝ))
  set x : ℤ → ℝ := fun k =>
    brk (τ + (2 * Real.pi * k) ^ 2 + (2 * Real.pi * ((m : ℝ) - k)) ^ 2) ^ (1 - 4 * (13 / 32 : ℝ))
    with hx
  have hx0 : ∀ k, 0 ≤ x k := fun k => brk_rpow_nonneg _ _
  have hterm : ∀ k : ℤ, ∫⁻ t, modWt e k t * modWt e (m - k) (τ - t) ≤
      ENNReal.ofReal (max C 0) * ENNReal.ofReal (x k) := by
    intro k
    set c1 : ℝ := (2 * Real.pi * k) ^ 2
    set A : ℝ := τ + (2 * Real.pi * k) ^ 2 + (2 * Real.pi * ((m : ℝ) - k)) ^ 2
    have hfun : (fun t => modWt e k t * modWt e (m - k) (τ - t)) =
        fun t => (fun μ => ENNReal.ofReal (brk μ ^ e * brk (A - μ) ^ e)) (t + c1) := by
      funext t
      have harg : τ - t + (2 * Real.pi * ((m - k : ℤ) : ℝ)) ^ 2 = A - (t + c1) := by
        simp only [A, c1]; push_cast; ring
      unfold modWt
      rw [← ENNReal.ofReal_mul (brk_rpow_nonneg _ _), harg]
    rw [hfun, lintegral_add_right_eq_self (fun μ => ENNReal.ofReal (brk μ ^ e * brk (A - μ) ^ e)) c1,
      ← ofReal_integral_eq_lintegral_ofReal (hC A).1
        (Filter.Eventually.of_forall fun μ => mul_nonneg (brk_rpow_nonneg _ _) (brk_rpow_nonneg _ _)),
      ← ENNReal.ofReal_mul (le_max_right _ _)]
    apply ENNReal.ofReal_le_ofReal
    refine (hC A).2.trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (brk_rpow_nonneg _ _)
  calc ∑' k : ℤ, ∫⁻ t, modWt e k t * modWt e (m - k) (τ - t)
      ≤ ∑' k : ℤ, ENNReal.ofReal (max C 0) * ENNReal.ofReal (x k) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (max C 0) * ENNReal.ofReal (∑' k, x k) := by
        rw [ENNReal.tsum_mul_left, ENNReal.ofReal_tsum_of_nonneg hx0 (hC' τ m).1]
    _ ≤ ENNReal.ofReal (max C 0) * ENNReal.ofReal C' := by
        gcongr
        exact (hC' τ m).2

/-- The weighted density `P_k(λ) = ⟨λ+(2πk)²⟩^{2a} F_k(λ)²`. -/
def weightedSq (F : ℤ → ℝ → ℝ≥0∞) (k : ℤ) (t : ℝ) : ℝ≥0∞ :=
  modWt (2 * (13 / 32 : ℝ)) k t * F k t ^ 2

theorem measurable_weightedSq (F : ℤ → ℝ → ℝ≥0∞) (hF : ∀ k, Measurable (F k)) (k : ℤ) :
    Measurable (weightedSq F k) :=
  (measurable_modWt _ k).mul ((hF k).pow_const 2)

/-- Tonelli + translation + reindexing:
`Σ_m ∫ Σ_k ∫ P_k(λ) P_{m-k}(τ-λ) dλ dτ = (Σ_k ∫ P_k)²`. -/
theorem convolution_mass (P : ℤ → ℝ → ℝ≥0∞) (hP : ∀ k, Measurable (P k)) :
    ∑' m : ℤ, ∫⁻ τ, ∑' k : ℤ, ∫⁻ t, P k t * P (m - k) (τ - t) =
      (∑' k : ℤ, ∫⁻ t, P k t) ^ 2 := by
  set Q : ℤ → ℝ≥0∞ := fun j => ∫⁻ t, P j t with hQ
  have hjoint : ∀ k j : ℤ, Measurable (fun q : ℝ × ℝ => P k q.2 * P j (q.1 - q.2)) :=
    fun k j => ((hP k).comp measurable_snd).mul ((hP j).comp (measurable_fst.sub measurable_snd))
  have hinner : ∀ k j : ℤ, Measurable (fun τ : ℝ => ∫⁻ t, P k t * P j (τ - t)) :=
    fun k j => (hjoint k j).lintegral_prod_right'
  have hpair : ∀ k j : ℤ, ∫⁻ τ, ∫⁻ t, P k t * P j (τ - t) = Q k * Q j := by
    intro k j
    rw [lintegral_lintegral_swap (hjoint k j).aemeasurable]
    have : ∀ t : ℝ, ∫⁻ τ, P k t * P j (τ - t) = P k t * Q j := fun t => by
      have hm : Measurable fun τ => P j (τ - t) := (hP j).comp (measurable_id.sub measurable_const)
      rw [lintegral_const_mul (P k t) hm,
        lintegral_sub_right_eq_self (P j) t]
    simp_rw [this]
    rw [lintegral_mul_const _ (hP k)]
  calc ∑' m : ℤ, ∫⁻ τ, ∑' k : ℤ, ∫⁻ t, P k t * P (m - k) (τ - t)
      = ∑' m : ℤ, ∑' k : ℤ, Q k * Q (m - k) := by
        congr 1; funext m
        rw [lintegral_tsum fun k => (hinner k (m - k)).aemeasurable]
        congr 1; funext k
        exact hpair k (m - k)
    _ = ∑' k : ℤ, ∑' m : ℤ, Q k * Q (m - k) := ENNReal.tsum_comm
    _ = ∑' k : ℤ, Q k * ∑' j : ℤ, Q j := by
        congr 1; funext k
        rw [ENNReal.tsum_mul_left]
        congr 1
        exact (Equiv.subRight k).tsum_eq Q
    _ = (∑' k : ℤ, Q k) ^ 2 := by
        rw [ENNReal.tsum_mul_right, sq]

/-- **Fourier-side bilinear `L⁴` estimate** (`a = 13/32`). There is a finite constant `K` such
that for every family of measurable `F : ℤ → ℝ → [0,∞]`,
`Σ_m ∫ (Σ_k ∫ F_k(λ) F_{m-k}(τ-λ) dλ)² dτ ≤ K (Σ_k ∫ ⟨λ+(2πk)²⟩^{2a} F_k(λ)² dλ)²`. -/
theorem bilinear_L4_fourier :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ F : ℤ → ℝ → ℝ≥0∞, (∀ k, Measurable (F k)) →
      ∑' m : ℤ, ∫⁻ τ, (∑' k : ℤ, ∫⁻ t, F k t * F (m - k) (τ - t)) ^ 2 ≤
        K * (∑' k : ℤ, ∫⁻ t, weightedSq F k t) ^ 2 := by
  obtain ⟨K, hK, hKb⟩ := weight_factor_bound
  refine ⟨K, hK, fun F hF => ?_⟩
  set a : ℝ := 13 / 32
  have hpt : ∀ (m : ℤ) (τ : ℝ),
      (∑' k : ℤ, ∫⁻ t, F k t * F (m - k) (τ - t)) ^ 2 ≤
        K * ∑' k : ℤ, ∫⁻ t, weightedSq F k t * weightedSq F (m - k) (τ - t) := by
    intro m τ
    set X : ℤ → ℝ → ℝ≥0∞ := fun k t => modWt (-a) k t * modWt (-a) (m - k) (τ - t)
    set Y : ℤ → ℝ → ℝ≥0∞ := fun k t =>
      (modWt a k t * F k t) * (modWt a (m - k) (τ - t) * F (m - k) (τ - t))
    have hXm : ∀ k, Measurable (X k) := fun k =>
      (measurable_modWt _ k).mul ((measurable_modWt _ _).comp (measurable_const.sub measurable_id))
    have hYm : ∀ k, Measurable (Y k) := fun k =>
      ((measurable_modWt _ k).mul (hF k)).mul
        (((measurable_modWt _ _).mul (hF _)).comp (measurable_const.sub measurable_id))
    have hXY : ∀ k t, F k t * F (m - k) (τ - t) = X k t * Y k t := fun k t => by
      simp only [X, Y]
      calc F k t * F (m - k) (τ - t)
          = (modWt (-a) k t * modWt a k t) * (modWt (-a) (m - k) (τ - t) *
              modWt a (m - k) (τ - t)) * (F k t * F (m - k) (τ - t)) := by
            rw [modWt_neg_mul, modWt_neg_mul, one_mul, one_mul]
        _ = _ := by ring
    have hX2 : ∀ k t, X k t ^ 2 =
        modWt (-(2 * a)) k t * modWt (-(2 * a)) (m - k) (τ - t) := fun k t => by
      simp only [X]
      rw [mul_pow, modWt_sq, modWt_sq, show 2 * -a = -(2 * a) by ring]
    have hY2 : ∀ k t, Y k t ^ 2 = weightedSq F k t * weightedSq F (m - k) (τ - t) := fun k t => by
      simp only [Y, weightedSq]
      rw [mul_pow, mul_pow, mul_pow, modWt_sq, modWt_sq]
    calc (∑' k : ℤ, ∫⁻ t, F k t * F (m - k) (τ - t)) ^ 2
        = (∑' k : ℤ, ∫⁻ t, X k t * Y k t) ^ 2 := by simp_rw [hXY]
      _ ≤ (∑' k, ∫⁻ t, X k t ^ 2) * (∑' k, ∫⁻ t, Y k t ^ 2) :=
          sum_lintegral_mul_sq_le X Y hXm hYm
      _ ≤ K * ∑' k : ℤ, ∫⁻ t, weightedSq F k t * weightedSq F (m - k) (τ - t) := by
          simp_rw [hX2, hY2]
          gcongr
          exact hKb m τ
  calc ∑' m : ℤ, ∫⁻ τ, (∑' k : ℤ, ∫⁻ t, F k t * F (m - k) (τ - t)) ^ 2
      ≤ ∑' m : ℤ, ∫⁻ τ, K * ∑' k : ℤ, ∫⁻ t, weightedSq F k t * weightedSq F (m - k) (τ - t) :=
        ENNReal.tsum_le_tsum fun m => lintegral_mono fun τ => hpt m τ
    _ = K * ∑' m : ℤ, ∫⁻ τ, ∑' k : ℤ, ∫⁻ t, weightedSq F k t * weightedSq F (m - k) (τ - t) := by
        rw [← ENNReal.tsum_mul_left]
        congr 1; funext m
        rw [lintegral_const_mul']
        exact hK
    _ = K * (∑' k : ℤ, ∫⁻ t, weightedSq F k t) ^ 2 := by
        rw [convolution_mass _ (measurable_weightedSq F hF)]

end LiebLiniger.FixedPeriod.ALLS.PdeB
