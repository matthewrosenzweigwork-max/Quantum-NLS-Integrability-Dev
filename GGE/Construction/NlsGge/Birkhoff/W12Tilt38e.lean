import NlsGge.Birkhoff.W12Tilt38c
import NlsGge.Spectral.ChargeJensenSobolev38

/-! # W12 (`D:prop:tilt`), part 5 (Birkhoff-free): mass coercivity `E_B(u) ≥ W(√Q_0(u)) - β_0`

v2 l.1861-1863: "`F:eq:moment` gives `Q_{2j} ≥ M^{j+1}` for `j ≥ 1`, and the same identity holds for
`j = 0`. Multiply by `β_{j+1}` and sum."

* `spectralEnergy_eq_chargeSeries_general38`: for coefficients `c` with `β_j ≥ 0` and summable
  `weightTerm c r` (so also for `bCoef38 c`), the spectral energy of a smooth field is the
  nonnegative series `∑_j β_j Q_{2j}` in `[0,∞]` (monotone convergence and the E02 trace formula;
  copy of `spectralEnergyW38_eq_chargeSeries` with the positivity/summability hypotheses isolated).
* `localCharge38_mass_le38`: `Q_0(U)^{j+1} ≤ Q_{2j}(U)` for smooth `U` (F07 part 1, `Q_{2j} ≥ Q_0^{j+1}`
  of `chargeMoment_mass_sobolev38`, the Sobolev form of `F:eq:moment`).
* `norm_sq_smoothL2_38`: `Q_0(U) = ‖U‖²_{L²}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.SpectralFoundations
  NlsGge.HierarchyRiccati.Core Filter Topology
open scoped ENNReal Real ContDiff

section ChargeSeries

/-- `E_c(smoothL2 U) = ∑_j β_j Q_{2j}(U)` in `[0,∞]` for nonnegative `β_j` with summable
`weightTerm c r` (any such `c`, not only a bounded class). -/
theorem spectralEnergy_eq_chargeSeries_general38 (c : ℕ → ℝ)
    (hcoef : ∀ j, 0 ≤ NlsGge.coefficient c j) (hsum : ∀ r, Summable (NlsGge.weightTerm c r))
    (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1) :
    spectralEnergyW38 c (smoothL2_38 U hU hper) = chargeSeriesW38 c U := by
  set u := smoothL2_38 U hU hper with hu
  have hu1 : SobolevSquareSummable 1 (physicalFourier u) := smoothL2_38_sobolev U hU hper
  have hae := smoothL2_38_cover_ae U hU hper
  have htr := fun j => actualTraceFormula_E02_38 u hu1 U hU hper hae j
  have hv0 := actualGapHeightE02_38_nonneg u
  set F : ℕ → ℝ → ℝ := fun j t =>
    NlsGge.coefficient c j * ((2 * t) ^ (2 * j) * actualGapHeightE02_38 u t) with hF
  have hF0 : ∀ j t, 0 ≤ F j t := fun j t =>
    mul_nonneg (hcoef j) (mul_nonneg (by rw [pow_mul]; positivity) (hv0 t))
  have hFint : ∀ j, Integrable (F j) := fun j => (htr j).1.const_mul _
  have hIj : ∀ j, ∫ t, F j t = (Real.pi / 2) * (NlsGge.coefficient c j * localCharge38 U j) := by
    intro j
    simp only [hF]
    rw [integral_const_mul]
    have h := (htr j).2
    have : localCharge38 U j =
        (2 / Real.pi) * ∫ t : ℝ, (2 * t) ^ (2 * j) * actualGapHeightE02_38 u t := h
    rw [this]
    field_simp
  have hpt : ∀ t, HasSum (fun j => F j t) (weight c (2 * t) * actualGapHeightE02_38 u t) := by
    intro t
    have hs := (hsum (2 * t)).hasSum
    have := hs.mul_right (actualGapHeightE02_38 u t)
    have e : (fun j => F j t) =
        fun j => NlsGge.weightTerm c (2 * t) j * actualGapHeightE02_38 u t := by
      funext j
      simp only [hF, NlsGge.weightTerm]
      ring
    rw [e]
    exact this
  have hL : ∫⁻ t, ENNReal.ofReal (weight c (2 * t) * actualGapHeightE02_38 u t) =
      ∑' j, ∫⁻ t, ENNReal.ofReal (F j t) := by
    rw [← lintegral_tsum (fun j => (hFint j).1.aemeasurable.ennreal_ofReal)]
    refine lintegral_congr (fun t => ?_)
    rw [← (hpt t).tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun j => hF0 j t) (hpt t).summable]
  have hIe : ∀ j, ∫⁻ t, ENNReal.ofReal (F j t) = ENNReal.ofReal (∫ t, F j t) := fun j =>
    (ofReal_integral_eq_lintegral_ofReal (hFint j) (Filter.Eventually.of_forall (hF0 j))).symm
  unfold spectralEnergyW38 chargeSeriesW38
  rw [hL, ENNReal.tsum_mul_left.symm]
  refine tsum_congr (fun j => ?_)
  rw [hIe j, hIj j, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

variable {lower upper : ℝ}

theorem EB38_eq_chargeSeries (c : BoundedCoefficients lower upper) (U : ℝ → ℂ)
    (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1) :
    EB38 c.val (smoothL2_38 U hU hper) = chargeSeriesW38 (bCoef38 c.val) U :=
  spectralEnergy_eq_chargeSeries_general38 _ (coefficient_bCoef_nonneg38 c)
    (summable_weightTerm_bCoef38 c) U hU hper

end ChargeSeries

section Mass

/-- `Q_0(U) = ‖smoothL2 U‖²_{L²}`: the local mass is the squared `L²` norm. -/
theorem norm_sq_smoothL2_38 (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1) :
    localCharge38 U 0 = ‖smoothL2_38 U hU hper‖ ^ 2 := by
  have h1 : localCharge38 U 0 = ∫ x in (0 : ℝ)..1, ‖U x‖ ^ 2 :=
    complexQ0_local_formula_Q024 U
  have h2 := (smoothDerivative_parseval38 0 U hU hper).2
  simp only [iteratedDeriv_zero, Nat.mul_zero, pow_zero, one_mul] at h2
  rw [h1, h2, norm_sq_eq_tsum_fourierSeq38, ← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr (fun n => ?_)
  simp only [Equiv.neg_apply, fourierSeq38_apply, norm_neg]
  rfl

theorem localCharge38_nonneg (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1) :
    0 ≤ localCharge38 U 0 := by
  rw [norm_sq_smoothL2_38 U hU hper]; positivity

/-- **`F:eq:moment` for all `j ≥ 0`: `Q_{2j}(U) ≥ Q_0(U)^{j+1}`** for smooth periodic `U`
(`j = 0` is trivial; `j ≥ 1` is `chargeMoment_mass_sobolev38` with `m = j+1`). -/
theorem localCharge38_mass_le38 (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1)
    (j : ℕ) : localCharge38 U 0 ^ (j + 1) ≤ localCharge38 U j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · obtain ⟨x, hx⟩ := riccatiSmoothPeriodic_hasSobolevCarrierWithExactFourierCoefficientsRecovery30
      j U hU hper
    have hm : 2 ≤ j + 1 := by omega
    have hmj := chargeMoment_mass_sobolev38 (j + 1) hm x
    have e0 := chargeSobolev38_smooth (j + 1) 0 hm (by omega) U hU hper x hx
    have e1 := chargeSobolev38_smooth (j + 1) (j + 1 - 1) hm (by omega) U hU hper x hx
    rw [e0, e1] at hmj
    simpa using hmj

variable {lower upper : ℝ}

/-- **Mass coercivity (v2 `D:eq:masscoercivity`).** For every smooth period-one `U`, with
`M = Q_0(U) = ‖U‖²_{L²}`,
`E_B(U) ≥ W(√M) - β_0` (as an inequality in `[0,∞]`; `W(r) = weight c r`, `β_0 = c_0`). -/
theorem EB_mass_coercivity_38 (c : BoundedCoefficients lower upper) (U : ℝ → ℂ)
    (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1) :
    ENNReal.ofReal (weight c.val (Real.sqrt (localCharge38 U 0)) - NlsGge.coefficient c.val 0) ≤
      EB38 c.val (smoothL2_38 U hU hper) := by
  set M := localCharge38 U 0 with hM
  have hM0 : 0 ≤ M := localCharge38_nonneg U hU hper
  set r := Real.sqrt M with hr
  have hr2 : r ^ 2 = M := Real.sq_sqrt hM0
  rw [EB38_eq_chargeSeries c U hU hper]
  unfold chargeSeriesW38
  have hs := weightTerm_summable lower upper c.val (coef_lower38 c) (coef_bound38 c)
    (coef_upper38 c) r
  have hterm : ∀ j : ℕ, NlsGge.weightTerm c.val r (j + 1) =
      NlsGge.coefficient (bCoef38 c.val) j * M ^ (j + 1) := fun j => by
    unfold NlsGge.weightTerm
    rw [coefficient_bCoef38, show 2 * (j + 1) = 2 * (j + 1) from rfl, pow_mul, hr2]
  have hnn : ∀ j : ℕ, 0 ≤ NlsGge.weightTerm c.val r (j + 1) := fun j =>
    mul_nonneg (coefficient_nonneg38' c _) (by rw [pow_mul]; positivity)
  have hsum1 : Summable (fun j : ℕ => NlsGge.weightTerm c.val r (j + 1)) :=
    (summable_nat_add_iff 1).2 hs
  have hW : weight c.val r - NlsGge.coefficient c.val 0 =
      ∑' j : ℕ, NlsGge.weightTerm c.val r (j + 1) := by
    unfold weight
    rw [hs.tsum_eq_zero_add]
    have h0 : NlsGge.weightTerm c.val r 0 = NlsGge.coefficient c.val 0 := by
      simp [NlsGge.weightTerm]
    rw [h0]; ring
  rw [hW, ENNReal.ofReal_tsum_of_nonneg hnn hsum1]
  refine ENNReal.tsum_le_tsum (fun j => ENNReal.ofReal_le_ofReal ?_)
  rw [hterm j]
  exact mul_le_mul_of_nonneg_left (localCharge38_mass_le38 U hU hper j)
    (coefficient_bCoef_nonneg38 c j)

/-- The same, with `√M = ‖u‖_{L²}`: `E_B(u) ≥ W(‖u‖_{L²}) - β_0`. -/
theorem EB_mass_coercivity_norm_38 (c : BoundedCoefficients lower upper) (U : ℝ → ℂ)
    (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1) :
    ENNReal.ofReal (weight c.val ‖smoothL2_38 U hU hper‖ - NlsGge.coefficient c.val 0) ≤
      EB38 c.val (smoothL2_38 U hU hper) := by
  have h := EB_mass_coercivity_38 c U hU hper
  rwa [norm_sq_smoothL2_38 U hU hper, Real.sqrt_sq (norm_nonneg _)] at h

end Mass

end NlsGge.Birkhoff
end
