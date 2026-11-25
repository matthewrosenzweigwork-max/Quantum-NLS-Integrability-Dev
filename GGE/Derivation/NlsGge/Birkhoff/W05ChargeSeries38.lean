import NlsGge.Birkhoff.W05FiniteGap38
import NlsGge.Birkhoff.S01Equivariance38b

/-! # W05, completion (review fix R1): the charge series `E_W = ∑_j β_j Q_{2j}` on `𝓕⁻¹ E_s`

Source: `paper/v2.tex` l.1500-1510 (`D:cor:Rcontinuous`: "monotone convergence in the nonnegative
power series and trace formulas gives its integral representation") and `eq:fullbare`,
`A:eq:localidentification`.

For a smooth period-one `U` (no finite-gap hypothesis), the spectral energy `spectralEnergyW38`
of `u = smoothL2 U` equals, in `[0,∞]`, the nonnegative series `∑' j ofReal(β_j Q_{2j}(U))` with
`β_j = c_j/(j!)^4` and `Q_{2j}` the local charge (`localCharge38`). Every point of `𝓕⁻¹ E_s`
(any real `s`) has a smooth representative (`E_s ⊂ H^m` for all `m`). Then W05 is restated for the
charge series.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.Weights NlsGge.HierarchyRiccati.Core Filter Topology
open scoped ENNReal Real ContDiff

/-- The charge series `E_W(U) = ∑_j β_j Q_{2j}(U)` of a smooth period-one `U`, as a nonnegative
extended real (`β_j = NlsGge.coefficient c j = c_j/(j!)^4`, `Q_{2j}` the local charge). -/
def chargeSeriesW38 (c : ℕ → ℝ) (U : ℝ → ℂ) : ℝ≥0∞ :=
  ∑' j : ℕ, ENNReal.ofReal (NlsGge.coefficient c j * localCharge38 U j)

/-- **Monotone convergence and trace formulas, in `[0,∞]` (v2 `A:eq:localidentification`).**
For every smooth period-one `U` (no hypothesis on the number of gaps), the spectral energy of
`smoothL2 U` is the charge series, an identity in `ℝ≥0∞`. -/
theorem spectralEnergyW38_eq_chargeSeries {lower upper : ℝ} (c : BoundedCoefficients lower upper)
    (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1) :
    spectralEnergyW38 c.val (smoothL2_38 U hU hper) = chargeSeriesW38 c.val U := by
  set u := smoothL2_38 U hU hper with hu
  have hlower := coef_lower38 c
  have hbound := coef_bound38 c
  have hupper := coef_upper38 c
  have hu1 : SobolevSquareSummable 1 (physicalFourier u) := smoothL2_38_sobolev U hU hper
  have hae := smoothL2_38_cover_ae U hU hper
  have htr := fun j => actualTraceFormula_E02_38 u hu1 U hU hper hae j
  have hv0 := actualGapHeightE02_38_nonneg u
  have hcoef : ∀ j, 0 ≤ NlsGge.coefficient c.val j := fun j =>
    div_nonneg ((hlower.le.trans (hbound j))) (by positivity)
  set F : ℕ → ℝ → ℝ := fun j t =>
    NlsGge.coefficient c.val j * ((2 * t) ^ (2 * j) * actualGapHeightE02_38 u t) with hF
  have hF0 : ∀ j t, 0 ≤ F j t := fun j t =>
    mul_nonneg (hcoef j) (mul_nonneg (by rw [pow_mul]; positivity) (hv0 t))
  have hFint : ∀ j, Integrable (F j) := fun j => (htr j).1.const_mul _
  have hIj : ∀ j, ∫ t, F j t = (Real.pi / 2) * (NlsGge.coefficient c.val j * localCharge38 U j) := by
    intro j
    simp only [hF]
    rw [integral_const_mul]
    have h := (htr j).2
    have : localCharge38 U j =
        (2 / Real.pi) * ∫ t : ℝ, (2 * t) ^ (2 * j) * actualGapHeightE02_38 u t := h
    rw [this]
    field_simp
  have hpt : ∀ t, HasSum (fun j => F j t) (weight c.val (2 * t) * actualGapHeightE02_38 u t) := by
    intro t
    have hs := (weightTerm_summable lower upper c.val hlower hbound hupper (2 * t)).hasSum
    have := hs.mul_right (actualGapHeightE02_38 u t)
    have e : (fun j => F j t) =
        fun j => weightTerm c.val (2 * t) j * actualGapHeightE02_38 u t := by
      funext j
      simp only [hF, NlsGge.weightTerm]
      ring
    rw [e]
    exact this
  have hL : ∫⁻ t, ENNReal.ofReal (weight c.val (2 * t) * actualGapHeightE02_38 u t) =
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

section Energy

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)

/-- **R1.** Every `x ∈ E_s` (any real `s`; no `B`, `O`) gives a field `u = 𝓕⁻¹ x` with a `C^∞`
period-one representative `U`, and the spectral energy of `u` is the charge series
`∑_j β_j Q_{2j}(U)` in `[0,∞]`. -/
theorem spectralEnergyW38_eq_chargeSeries_physOfE38 (x : ECarrier38 c s) :
    ∃ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1),
      smoothL2_38 U hU hper = physOfE38 c s x ∧
      spectralEnergyW38 c.val (physOfE38 c s x) =
        ∑' j : ℕ, ENNReal.ofReal (NlsGge.coefficient c.val j * localCharge38 U j) := by
  obtain ⟨U, hU, hper, hUu⟩ := exists_smooth_rep38 (physOfE38 c s x)
    (fun m => sobolev_physOfE38 c s (m : ℝ) x)
  refine ⟨U, hU, hper, hUu, ?_⟩
  rw [← hUu]
  exact spectralEnergyW38_eq_chargeSeries c U hU hper

namespace BirkhoffInput38

variable (B : BirkhoffInput38) {c s}

/-- **W05, headline with the charge series (v2 `D:cor:Rcontinuous`), conditional on `B`, `O`.**
On `𝓕⁻¹ E_s` (topology transported from `E_s` by `𝓕`), `s < 3/4`:
1. `R_W` is a well defined (absolutely summable) continuous function;
2. `R_W ≥ 0`;
3. every `u ∈ 𝓕⁻¹ E_s` has a `C^∞` period-one representative `U`;
4. for every such `U` (`smoothL2 U = u`): if the charge series `E_W(U) = ∑_j β_j Q_{2j}(U)` is
   finite then `∑ a_n |Φ_n(u)|² < ∞` and `E_W(U) = ∑ a_n |Φ_n(u)|² + R_W(u)`;
5. the spectral-integral form of the energy agrees with the charge series. -/
theorem W05_chargeSeries_38 (O : OneSmoothingInput38 B) (hs : s < 3 / 4) :
    (∀ u : FinvE38 c s, Summable (fun n : ℤ => remainderSummand38 c.val u.1 n)) ∧
    @Continuous (FinvE38 c s) ℝ (topFinvE38 c s) _ (fun u => remainder38 c.val u.1) ∧
    (∀ u : FinvE38 c s, 0 ≤ remainder38 c.val u.1) ∧
    (∀ u : FinvE38 c s, ∃ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1),
      smoothL2_38 U hU hper = u.1) ∧
    (∀ u : FinvE38 c s, ∀ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1),
      smoothL2_38 U hU hper = u.1 → chargeSeriesW38 c.val U ≠ ⊤ →
      Summable (fun n : ℤ => fullWeightRate c.val n * ‖B.Φ u.1 n‖ ^ 2) ∧
      (chargeSeriesW38 c.val U).toReal =
        ∑' n : ℤ, fullWeightRate c.val n * ‖B.Φ u.1 n‖ ^ 2 + remainder38 c.val u.1) ∧
    (∀ u : FinvE38 c s, ∀ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1),
      smoothL2_38 U hU hper = u.1 → spectralEnergyW38 c.val u.1 = chargeSeriesW38 c.val U) := by
  obtain ⟨h1, h2, h3, h4⟩ := B.W05_38 c s O hs
  have h5 : ∀ u : FinvE38 c s, ∀ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1),
      smoothL2_38 U hU hper = u.1 → spectralEnergyW38 c.val u.1 = chargeSeriesW38 c.val U := by
    intro u U hU hper hUu
    rw [← hUu]
    exact spectralEnergyW38_eq_chargeSeries c U hU hper
  refine ⟨h1, h2, h3, fun u => ?_, fun u U hU hper hUu hfin => ?_, h5⟩
  · obtain ⟨U, hU, hper, hUu, -⟩ := spectralEnergyW38_eq_chargeSeries_physOfE38 c s (toE38 c s u)
    exact ⟨U, hU, hper, by rw [hUu, physOfE38_toE38]⟩
  · have e := h5 u U hU hper hUu
    rw [← e] at hfin ⊢
    exact h4 u hfin

end BirkhoffInput38

end Energy

end NlsGge.Birkhoff
end
