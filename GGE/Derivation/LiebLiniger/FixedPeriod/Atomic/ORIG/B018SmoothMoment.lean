import NlsGge.Atomic.I.I007
import NlsGge.Spectral.ChargeJensenSobolev38

/-! # B018.C02 (record NEW-E01), smooth case: H-based moment composition
(paper/v2.tex l.209-214, `F:eq:moment`).

For a smooth period-one field, with `M = Q₀`, `H = Q₂`: `H ≥ ∫₀¹|u|⁴ ≥ M²`, and for `j ≥ 1`
`Q_{2j} ≥ H^{(j+1)/2}`, `Q_{2j} ≥ M^{j+1}`; for a nonzero field `M > 0` and
`Q_{2j} ≥ H^j/M^{j-1} ≥ H^{(j+1)/2}`.
The statement of `smoothMomentH38` is the reviewed frozen statement (STATEMENTS_SG08_B018.md). -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open MeasureTheory NlsGge.Pilot
open scoped ContDiff

section B018SmoothLemmas

open Filter Topology

/-- Real-power algebra: `M > 0`, `M² ≤ H` give `H^{(j+1)/2} ≤ H^j / M^{j-1}` (`j ≥ 1`). -/
theorem rpow_le_pow_div_B018 (H M : ℝ) (j : ℕ) (hj : 1 ≤ j) (hM : 0 < M) (hMH : M ^ 2 ≤ H) :
    H ^ (((j : ℝ) + 1) / 2) ≤ H ^ j / M ^ (j - 1) := by
  have hH : 0 < H := lt_of_lt_of_le (by positivity) hMH
  rw [le_div_iff₀ (by positivity)]
  have hpow : M ^ (j - 1) = (M ^ 2) ^ ((((j - 1 : ℕ) : ℝ)) / 2) := by
    have e : (2 : ℝ) * (((j - 1 : ℕ) : ℝ) / 2) = ((j - 1 : ℕ) : ℝ) := by ring
    rw [← Real.rpow_natCast M 2, ← Real.rpow_mul hM.le, Nat.cast_ofNat, e, Real.rpow_natCast]
  have h1 : M ^ (j - 1) ≤ H ^ ((((j - 1 : ℕ) : ℝ)) / 2) := by
    rw [hpow]
    exact Real.rpow_le_rpow (by positivity) hMH (by positivity)
  calc H ^ (((j : ℝ) + 1) / 2) * M ^ (j - 1)
      ≤ H ^ (((j : ℝ) + 1) / 2) * H ^ ((((j - 1 : ℕ) : ℝ)) / 2) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = H ^ j := by
        rw [← Real.rpow_add hH, ← Real.rpow_natCast]
        congr 1
        rw [Nat.cast_sub hj]
        push_cast
        ring

/-- A continuous period-one field that is not identically zero has positive mass on `[0,1]`. -/
theorem intervalMass_pos_B018 (U : ℝ → ℂ) (hc : Continuous U) (hper : Function.Periodic U 1)
    (hU0 : U ≠ 0) : 0 < ∫ x in (0 : ℝ)..1, ‖U x‖ ^ 2 := by
  obtain ⟨x0, hx0⟩ : ∃ x0, U x0 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hU0 (funext h)
  have hymem : toIcoMod one_pos 0 x0 ∈ Set.Ico (0 : ℝ) (0 + 1) := toIcoMod_mem_Ico one_pos 0 x0
  set y := toIcoMod one_pos 0 x0 with hy
  have hUy : U y = U x0 := by
    rw [hy, toIcoMod]
    exact hper.sub_zsmul_eq _
  have hfc : Continuous (fun x => ‖U x‖ ^ 2) := hc.norm.pow 2
  have hfy : 0 < ‖U y‖ ^ 2 := by
    rw [hUy]
    exact pow_pos (norm_pos_iff.2 hx0) 2
  have hev : ∀ᶠ x in 𝓝 y, ‖U y‖ ^ 2 / 2 < ‖U x‖ ^ 2 :=
    hfc.continuousAt.eventually (lt_mem_nhds (by linarith))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hy1 : y < 1 := by simpa using hymem.2
  have hyb : y < min (y + δ / 2) 1 := lt_min (by linarith) hy1
  have hb1 : min (y + δ / 2) 1 ≤ 1 := min_le_right _ _
  have hbd : min (y + δ / 2) 1 ≤ y + δ / 2 := min_le_left _ _
  have hfi : IntervalIntegrable (fun x => ‖U x‖ ^ 2) volume 0 1 := hfc.intervalIntegrable _ _
  have h1 : ∫ x in y..(min (y + δ / 2) 1), ‖U x‖ ^ 2 ≤ ∫ x in (0 : ℝ)..1, ‖U x‖ ^ 2 :=
    intervalIntegral.integral_mono_interval hymem.1 hyb.le hb1
      (Filter.Eventually.of_forall (fun x => sq_nonneg ‖U x‖)) hfi
  have h2 : ∫ x in y..(min (y + δ / 2) 1), ‖U y‖ ^ 2 / 2 ≤
      ∫ x in y..(min (y + δ / 2) 1), ‖U x‖ ^ 2 :=
    intervalIntegral.integral_mono_on hyb.le intervalIntegrable_const
      (hfc.intervalIntegrable _ _) (fun x hx => (hball (by
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith [hx.1, hx.2])).le)
  rw [intervalIntegral.integral_const, smul_eq_mul] at h2
  have : 0 < (min (y + δ / 2) 1 - y) * (‖U y‖ ^ 2 / 2) := mul_pos (by linarith) (by positivity)
  linarith

/-- Cauchy-Schwarz on the unit interval: `(∫₀¹|U|²)² ≤ ∫₀¹|U|⁴` for continuous `U`. -/
theorem mass_sq_le_quartic_B018 (U : ℝ → ℂ) (hc : Continuous U) :
    (∫ x in (0 : ℝ)..1, ‖U x‖ ^ 2) ^ 2 ≤ ∫ x in (0 : ℝ)..1, ‖U x‖ ^ 4 := by
  set m := ∫ x in (0 : ℝ)..1, ‖U x‖ ^ 2 with hm
  have h2 : IntervalIntegrable (fun x => ‖U x‖ ^ 2) MeasureTheory.volume 0 1 :=
    (hc.norm.pow 2).intervalIntegrable _ _
  have h4 : IntervalIntegrable (fun x => ‖U x‖ ^ 4) MeasureTheory.volume 0 1 :=
    (hc.norm.pow 4).intervalIntegrable _ _
  have hlow : IntervalIntegrable (fun x => 2 * m * ‖U x‖ ^ 2 - m ^ 2)
      MeasureTheory.volume 0 1 :=
    (h2.const_mul _).sub intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on (zero_le_one' ℝ) hlow h4 (fun x _ => by
    nlinarith [sq_nonneg (‖U x‖ ^ 2 - m)])
  rw [intervalIntegral.integral_sub (h2.const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul] at hmono
  simp at hmono
  nlinarith [hmono]

/-- `M^{j+1} ≤ Q_{2j}` for smooth period-one fields (`j ≥ 1`), via the Sobolev extension. -/
theorem smooth_mass_moment_B018 (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1)
    (j : ℕ) (hj : 1 ≤ j) : (localCharge38 U 0) ^ (j + 1) ≤ localCharge38 U j := by
  obtain ⟨x, hx⟩ :=
    riccatiSmoothPeriodic_hasSobolevCarrierWithExactFourierCoefficientsRecovery30 (j + 1 - 1) U hU hper
  have h := chargeMoment_mass_sobolev38 (j + 1) (by omega) x
  rw [chargeSobolev38_smooth (j + 1) 0 (by omega) (by omega) U hU hper x hx,
    chargeSobolev38_smooth (j + 1) (j + 1 - 1) (by omega) (by omega) U hU hper x hx] at h
  simpa using h

end B018SmoothLemmas

/-- **B018.C02, smooth.** Every smooth period-one field `U`, with `M = Q₀`, `H = Q₂`:
`H ≥ ∫₀¹|U|⁴ ≥ M²`; for `j ≥ 1`, `Q_{2j} ≥ H^{(j+1)/2}` and `Q_{2j} ≥ M^{j+1}` (zero field
included); and for a nonzero field `M > 0`, `Q_{2j} ≥ H^j/M^{j-1} ≥ H^{(j+1)/2}`. -/
theorem smoothMomentH38 (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1) :
    (localCharge38 U 0) ^ 2 ≤ ∫ x in (0 : ℝ)..1, ‖U x‖ ^ 4 ∧
    ∫ x in (0 : ℝ)..1, ‖U x‖ ^ 4 ≤ localCharge38 U 1 ∧
    ∀ j : ℕ, 1 ≤ j →
      (localCharge38 U 1) ^ (((j : ℝ) + 1) / 2) ≤ localCharge38 U j ∧
      (localCharge38 U 0) ^ (j + 1) ≤ localCharge38 U j ∧
      (U ≠ 0 →
        0 < localCharge38 U 0 ∧
        (localCharge38 U 1) ^ j / (localCharge38 U 0) ^ (j - 1) ≤ localCharge38 U j ∧
        (localCharge38 U 1) ^ (((j : ℝ) + 1) / 2) ≤
          (localCharge38 U 1) ^ j / (localCharge38 U 0) ^ (j - 1)) := by
  have hQ0 : localCharge38 U 0 = ∫ x in (0 : ℝ)..1, ‖U x‖ ^ 2 :=
    NlsGge.SpectralFoundations.complexQ0_local_formula_Q024 U
  have hQ2 : localCharge38 U 1 = ∫ x in (0 : ℝ)..1, (‖deriv U x‖ ^ 2 + ‖U x‖ ^ 4) :=
    NlsGge.SpectralFoundations.complexQ2_local_formula_Q024 U hU hper
  have hc : Continuous U := hU.continuous
  have hd : Continuous (deriv U) := hU.continuous_deriv (by simp)
  have hMQ : (localCharge38 U 0) ^ 2 ≤ ∫ x in (0 : ℝ)..1, ‖U x‖ ^ 4 := by
    rw [hQ0]; exact mass_sq_le_quartic_B018 U hc
  have hQH : ∫ x in (0 : ℝ)..1, ‖U x‖ ^ 4 ≤ localCharge38 U 1 := by
    rw [hQ2]
    refine intervalIntegral.integral_mono_on (zero_le_one' ℝ)
      ((hc.norm.pow 4).intervalIntegrable _ _)
      (((hd.norm.pow 2).add (hc.norm.pow 4)).intervalIntegrable _ _) (fun x _ => ?_)
    have := sq_nonneg ‖deriv U x‖
    linarith
  have hMH : (localCharge38 U 0) ^ 2 ≤ localCharge38 U 1 := hMQ.trans hQH
  refine ⟨hMQ, hQH, fun j hj => ?_⟩
  have hmass := smooth_mass_moment_B018 U hU hper j hj
  by_cases hU0 : U = 0
  · have hH0 : localCharge38 U 1 = 0 := by
      rw [hQ2, hU0]; simp
    have hM0 : localCharge38 U 0 = 0 := by
      rw [hQ0, hU0]; simp
    refine ⟨?_, hmass, fun h => absurd hU0 h⟩
    rw [hH0, Real.zero_rpow (by positivity)]
    rw [hM0, zero_pow (by omega)] at hmass
    exact hmass
  · have hMp : 0 < localCharge38 U 0 := by
      rw [hQ0]; exact intervalMass_pos_B018 U hc hper hU0
    have hi : (localCharge38 U 1) ^ j / (localCharge38 U 0) ^ (j - 1) ≤ localCharge38 U j :=
      (NlsGge.ThirdConsultation.I.i007 U hU hper hMp).2.2 j hj
    have halg := rpow_le_pow_div_B018 (localCharge38 U 1) (localCharge38 U 0) j hj hMp hMH
    exact ⟨halg.trans hi, hmass, fun _ => ⟨hMp, hi, halg⟩⟩

end NlsGge.HierarchyRiccati.Core
