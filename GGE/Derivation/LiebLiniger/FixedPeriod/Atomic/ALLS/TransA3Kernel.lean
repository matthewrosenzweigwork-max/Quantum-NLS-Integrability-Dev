import Mathlib
import NlsGge.Birkhoff.S01Equivariance38

/-! # Track A, step A3 (scalar part): the fractional difference kernel

Author: Claude Opus 5.5 (track A).  Not self-reviewed, not accepted.

For `0 < σ < 1` and `n ∈ ℤ` put (as an extended nonnegative real, no integrability assumed)

  `diffKernel σ n = ∫⁻ θ in (0, π], ‖e^{inθ} - 1‖² θ^{-1-2σ} dθ`,

with `e^{inθ} = rotPhase38 θ n` the phase of the diagonal rotation `rotSeq38 θ`.
This file proves the two-sided bound

  `kernelLow σ · |n|^{2σ} ≤ diffKernel σ n ≤ kernelUp σ · |n|^{2σ}`,

with `kernelUp σ = 1/(2-2σ) + 2/σ`, `kernelLow σ = π^{-2σ}/2` (lower bound for `n ≠ 0`; the
kernel vanishes at `n = 0`).  This is the scalar core of the difference-norm characterization
of `h^{N+σ}` over the integer base `h^N` (Pro report, "Difference norms"; the angle variable
is `θ = 2π a`, one-sided, which only changes constants). -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set NlsGge.Birkhoff
open scoped ENNReal

namespace NlsGge.ALLS.TransA

/-- The fractional difference kernel `∫⁻_{(0,π]} ‖e^{inθ}-1‖² θ^{-1-2σ} dθ`. -/
def diffKernel (σ : ℝ) (n : ℤ) : ℝ≥0∞ :=
  ∫⁻ θ in Ioc 0 Real.pi, ENNReal.ofReal (‖rotPhase38 θ n - 1‖ ^ 2 * θ ^ (-1 - 2 * σ))

/-- Upper kernel constant. -/
def kernelUp (σ : ℝ) : ℝ := 1 / (2 - 2 * σ) + 2 / σ

/-- Lower kernel constant. -/
def kernelLow (σ : ℝ) : ℝ := Real.pi ^ (-2 * σ) / 2

theorem kernelUp_pos {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) : 0 < kernelUp σ := by
  unfold kernelUp
  have h1 : 0 < 2 - 2 * σ := by linarith
  positivity

theorem kernelLow_pos (σ : ℝ) : 0 < kernelLow σ := by
  unfold kernelLow
  have := Real.rpow_pos_of_pos Real.pi_pos (-2 * σ)
  positivity

theorem rotPhase38_sub_one_eq (θ : ℝ) (n : ℤ) :
    rotPhase38 θ n - 1 = Complex.exp (Complex.I * (((n : ℝ) * θ : ℝ) : ℂ)) - 1 := by
  unfold rotPhase38
  rw [mul_comm]

theorem norm_rotPhase38_sub_one_le (θ : ℝ) (n : ℤ) :
    ‖rotPhase38 θ n - 1‖ ≤ |(n : ℝ)| * |θ| := by
  rw [rotPhase38_sub_one_eq, ← abs_mul]
  simpa [Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := (n : ℝ) * θ))

theorem norm_rotPhase38_sub_one_le_two (θ : ℝ) (n : ℤ) : ‖rotPhase38 θ n - 1‖ ≤ 2 := by
  calc ‖rotPhase38 θ n - 1‖ ≤ ‖rotPhase38 θ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_rotPhase38, norm_one]; norm_num

theorem rotPhase38_zero_index (θ : ℝ) : rotPhase38 θ 0 = 1 := by
  simp [rotPhase38]

/-- On `π/2 ≤ |n| θ ≤ π` the phase difference is at least one in modulus. -/
theorem one_le_norm_rotPhase38_sub_one_sq {θ : ℝ} {n : ℤ} (hθ : 0 ≤ θ)
    (h1 : Real.pi / 2 ≤ |(n : ℝ)| * θ) (h2 : |(n : ℝ)| * θ ≤ Real.pi) :
    1 ≤ ‖rotPhase38 θ n - 1‖ ^ 2 := by
  rw [rotPhase38_sub_one_eq, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
    abs_two]
  set y : ℝ := |(n : ℝ)| * θ / 2 with hy
  have hy0' : 0 ≤ y := by rw [hy]; positivity
  have hyπ : y ≤ Real.pi := by rw [hy]; linarith [Real.pi_pos]
  have habs : |Real.sin ((n : ℝ) * θ / 2)| = Real.sin y := by
    rcases le_or_gt 0 (n : ℝ) with hn | hn
    · have e : (n : ℝ) * θ / 2 = y := by rw [hy, abs_of_nonneg hn]
      rw [e, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hy0' hyπ)]
    · have e : (n : ℝ) * θ / 2 = -y := by rw [hy, abs_of_neg hn]; ring
      rw [e, Real.sin_neg, abs_neg, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hy0' hyπ)]
  rw [habs]
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hy1 : y ≤ Real.pi / 2 := by rw [hy]; linarith
  have hy2 : Real.pi / 4 ≤ y := by rw [hy]; linarith
  have hs := Real.mul_le_sin hy0 hy1
  have hpi := Real.pi_pos
  have : 1 / 2 ≤ Real.sin y := by
    calc (1 : ℝ) / 2 = 2 / Real.pi * (Real.pi / 4) := by field_simp; ring
      _ ≤ 2 / Real.pi * y := by gcongr
      _ ≤ Real.sin y := hs
  nlinarith

/-- `∫_{(0,c]} θ^{r} = c^{r+1}/(r+1)` for `r > -1`, as a lower integral. -/
theorem lintegral_Ioc_rpow {r c : ℝ} (hr : -1 < r) (hc : 0 < c) (K : ℝ) (hK : 0 ≤ K) :
    ∫⁻ θ in Ioc 0 c, ENNReal.ofReal (K * θ ^ r) = ENNReal.ofReal (K * (c ^ (r + 1) / (r + 1))) := by
  have hint : IntegrableOn (fun θ : ℝ => θ ^ r) (Ioc 0 c) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hc.le).1 (intervalIntegral.intervalIntegrable_rpow' hr)
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 c)] fun θ : ℝ => K * θ ^ r := by
    refine (ae_restrict_mem measurableSet_Ioc).mono fun θ hθ => ?_
    exact mul_nonneg hK (Real.rpow_nonneg hθ.1.le _)
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul K) hnn, integral_const_mul,
    ← intervalIntegral.integral_of_le hc.le, integral_rpow (Or.inl hr),
    Real.zero_rpow (by linarith), sub_zero]

/-- `∫_{(c,∞)} θ^{a} = -c^{a+1}/(a+1)` for `a < -1`, as a lower integral. -/
theorem lintegral_Ioi_rpow {a c : ℝ} (ha : a < -1) (hc : 0 < c) (K : ℝ) (hK : 0 ≤ K) :
    ∫⁻ θ in Ioi c, ENNReal.ofReal (K * θ ^ a) = ENNReal.ofReal (K * (-c ^ (a + 1) / (a + 1))) := by
  have hint : IntegrableOn (fun θ : ℝ => θ ^ a) (Ioi c) := integrableOn_Ioi_rpow_of_lt ha hc
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi c)] fun θ : ℝ => K * θ ^ a := by
    refine (ae_restrict_mem measurableSet_Ioi).mono fun θ hθ => ?_
    exact mul_nonneg hK (Real.rpow_nonneg (hc.trans hθ).le _)
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul K) hnn, integral_const_mul,
    integral_Ioi_rpow_of_lt ha hc]

/-- The kernel vanishes at the zero mode. -/
theorem diffKernel_zero (σ : ℝ) : diffKernel σ 0 = 0 := by
  unfold diffKernel
  simp [rotPhase38_zero_index]

/-- **Upper kernel bound**: `diffKernel σ n ≤ kernelUp σ · |n|^{2σ}`. -/
theorem diffKernel_le {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (n : ℤ) :
    diffKernel σ n ≤ ENNReal.ofReal (kernelUp σ * |(n : ℝ)| ^ (2 * σ)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [diffKernel_zero]; exact bot_le
  have hN : 0 < |(n : ℝ)| := abs_pos.2 (by exact_mod_cast hn)
  set N : ℝ := |(n : ℝ)| with hNdef
  set c : ℝ := N⁻¹ with hcdef
  have hc : 0 < c := inv_pos.2 hN
  set a : ℝ := -1 - 2 * σ with hadef
  have hsplit : Ioc 0 Real.pi ⊆ Ioc 0 c ∪ Ioi c := by
    intro θ hθ
    rcases le_or_gt θ c with h | h
    · exact Or.inl ⟨hθ.1, h⟩
    · exact Or.inr h
  have h1 : ∀ θ ∈ Ioc 0 c, ENNReal.ofReal (‖rotPhase38 θ n - 1‖ ^ 2 * θ ^ a) ≤
      ENNReal.ofReal (N ^ 2 * θ ^ (a + 2)) := by
    intro θ hθ
    apply ENNReal.ofReal_le_ofReal
    have hθ0 := hθ.1
    have hb := norm_rotPhase38_sub_one_le θ n
    rw [abs_of_pos hθ0] at hb
    have hsq : ‖rotPhase38 θ n - 1‖ ^ 2 ≤ (N * θ) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hb 2
    rw [Real.rpow_add hθ0, Real.rpow_two]
    have hpos := Real.rpow_pos_of_pos hθ0 a
    calc ‖rotPhase38 θ n - 1‖ ^ 2 * θ ^ a ≤ (N * θ) ^ 2 * θ ^ a := by gcongr
      _ = N ^ 2 * (θ ^ a * θ ^ 2) := by ring
  have h2 : ∀ θ ∈ Ioi c, ENNReal.ofReal (‖rotPhase38 θ n - 1‖ ^ 2 * θ ^ a) ≤
      ENNReal.ofReal (4 * θ ^ a) := by
    intro θ hθ
    apply ENNReal.ofReal_le_ofReal
    have hθ0 : 0 < θ := hc.trans hθ
    have hb := norm_rotPhase38_sub_one_le_two θ n
    have hsq : ‖rotPhase38 θ n - 1‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (rotPhase38 θ n - 1)]
    have hpos := Real.rpow_pos_of_pos hθ0 a
    gcongr
  have hr : -1 < a + 2 := by rw [hadef]; linarith
  have ha : a < -1 := by rw [hadef]; linarith
  have hI1 := lintegral_Ioc_rpow hr hc (N ^ 2) (sq_nonneg _)
  have hI2 := lintegral_Ioi_rpow ha hc 4 (by norm_num)
  have e1 : a + 2 + 1 = 2 - 2 * σ := by rw [hadef]; ring
  have e2 : a + 1 = -(2 * σ) := by rw [hadef]; ring
  have hcp : c ^ (-(2 * σ)) = N ^ (2 * σ) := by
    rw [hcdef, Real.inv_rpow hN.le, Real.rpow_neg hN.le, inv_inv]
  have hcq : c ^ (2 - 2 * σ) = (N ^ (2 : ℝ))⁻¹ * N ^ (2 * σ) := by
    rw [hcdef, Real.inv_rpow hN.le, sub_eq_add_neg, Real.rpow_add hN, Real.rpow_neg hN.le,
      mul_inv, inv_inv]
  have hσ2 : 0 < 2 * σ := by linarith
  have h3 : 0 < 2 - 2 * σ := by linarith
  have hNp : 0 < N ^ (2 * σ) := Real.rpow_pos_of_pos hN _
  have hv1 : N ^ 2 * (c ^ (a + 2 + 1) / (a + 2 + 1)) = N ^ (2 * σ) / (2 - 2 * σ) := by
    rw [e1, hcq, ← Real.rpow_two]
    have : 0 < N ^ (2 : ℝ) := Real.rpow_pos_of_pos hN _
    field_simp
  have hv2 : 4 * (-c ^ (a + 1) / (a + 1)) = 4 * N ^ (2 * σ) / (2 * σ) := by
    rw [e2, hcp, neg_div_neg_eq]; ring
  have hsum : N ^ (2 * σ) / (2 - 2 * σ) + 4 * N ^ (2 * σ) / (2 * σ) = kernelUp σ * N ^ (2 * σ) := by
    unfold kernelUp
    field_simp
    ring
  calc diffKernel σ n
      ≤ ∫⁻ θ in Ioc 0 c ∪ Ioi c, ENNReal.ofReal (‖rotPhase38 θ n - 1‖ ^ 2 * θ ^ a) :=
        lintegral_mono_set hsplit
    _ ≤ (∫⁻ θ in Ioc 0 c, ENNReal.ofReal (‖rotPhase38 θ n - 1‖ ^ 2 * θ ^ a)) +
        (∫⁻ θ in Ioi c, ENNReal.ofReal (‖rotPhase38 θ n - 1‖ ^ 2 * θ ^ a)) :=
        lintegral_union_le _ _ _
    _ ≤ (∫⁻ θ in Ioc 0 c, ENNReal.ofReal (N ^ 2 * θ ^ (a + 2))) +
        (∫⁻ θ in Ioi c, ENNReal.ofReal (4 * θ ^ a)) :=
        add_le_add (setLIntegral_mono' measurableSet_Ioc h1) (setLIntegral_mono' measurableSet_Ioi h2)
    _ = ENNReal.ofReal (kernelUp σ * N ^ (2 * σ)) := by
        rw [hI1, hI2, hv1, hv2, ← ENNReal.ofReal_add (by positivity) (by positivity), hsum]

/-- **Lower kernel bound**: `kernelLow σ · |n|^{2σ} ≤ diffKernel σ n` for `n ≠ 0`. -/
theorem le_diffKernel {σ : ℝ} (hσ0 : 0 < σ) {n : ℤ} (hn : n ≠ 0) :
    ENNReal.ofReal (kernelLow σ * |(n : ℝ)| ^ (2 * σ)) ≤ diffKernel σ n := by
  have hN1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
    have h' : ((1 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast this
    simpa [Int.cast_abs] using h'
  have hN : 0 < |(n : ℝ)| := by linarith
  set N : ℝ := |(n : ℝ)| with hNdef
  set a : ℝ := -1 - 2 * σ with hadef
  have hpi := Real.pi_pos
  set lo : ℝ := Real.pi / (2 * N) with hlo
  set hi : ℝ := Real.pi / N with hhi
  have hlo0 : 0 < lo := by positivity
  have hlohi : lo ≤ hi := by
    rw [hlo, hhi]; apply div_le_div_of_nonneg_left hpi.le hN; linarith
  have hsub : Icc lo hi ⊆ Ioc 0 Real.pi := by
    intro θ hθ
    refine ⟨hlo0.trans_le hθ.1, hθ.2.trans ?_⟩
    rw [hhi, div_le_iff₀ hN]; nlinarith
  have hpt : ∀ θ ∈ Icc lo hi, ENNReal.ofReal (hi ^ a) ≤
      ENNReal.ofReal (‖rotPhase38 θ n - 1‖ ^ 2 * θ ^ a) := by
    intro θ hθ
    apply ENNReal.ofReal_le_ofReal
    have hθ0 : 0 < θ := hlo0.trans_le hθ.1
    have hge : 1 ≤ ‖rotPhase38 θ n - 1‖ ^ 2 := by
      apply one_le_norm_rotPhase38_sub_one_sq hθ0.le
      · have := hθ.1; rw [hlo, div_le_iff₀ (by positivity)] at this; nlinarith
      · have := hθ.2; rw [hhi, le_div_iff₀ hN] at this; nlinarith
    have hmono : hi ^ a ≤ θ ^ a := Real.rpow_le_rpow_of_nonpos hθ0 hθ.2 (by rw [hadef]; linarith)
    have hpos : 0 ≤ θ ^ a := (Real.rpow_pos_of_pos hθ0 a).le
    nlinarith
  calc ENNReal.ofReal (kernelLow σ * N ^ (2 * σ))
      = ENNReal.ofReal (hi ^ a) * volume (Icc lo hi) := by
        rw [Real.volume_Icc, ← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
        congr 1
        rw [hhi, hlo, hadef, Real.div_rpow hpi.le hN.le]
        have e : (-1 - 2 * σ) = -(1 + 2 * σ) := by ring
        rw [e, Real.rpow_neg hpi.le, Real.rpow_neg hN.le]
        have e2 : Real.pi ^ (1 + 2 * σ) = Real.pi * Real.pi ^ (2 * σ) := by
          rw [Real.rpow_add hpi, Real.rpow_one]
        have e3 : N ^ (1 + 2 * σ) = N * N ^ (2 * σ) := by
          rw [Real.rpow_add hN, Real.rpow_one]
        rw [e2, e3]
        unfold kernelLow
        have e4 : Real.pi ^ (-2 * σ) = (Real.pi ^ (2 * σ))⁻¹ := by
          rw [show -2 * σ = -(2 * σ) by ring, Real.rpow_neg hpi.le]
        rw [e4]
        have hp1 : 0 < Real.pi ^ (2 * σ) := Real.rpow_pos_of_pos hpi _
        have hp2 : 0 < N ^ (2 * σ) := Real.rpow_pos_of_pos hN _
        field_simp
        ring
    _ = ∫⁻ _ in Icc lo hi, ENNReal.ofReal (hi ^ a) := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ θ in Icc lo hi, ENNReal.ofReal (‖rotPhase38 θ n - 1‖ ^ 2 * θ ^ a) :=
        setLIntegral_mono' measurableSet_Icc hpt
    _ ≤ diffKernel σ n := lintegral_mono_set hsub

end NlsGge.ALLS.TransA
