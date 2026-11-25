import NlsGge.Birkhoff.W12Tilt38f
import NlsGge.Birkhoff.W12Tilt38e

/-! # W12 (`D:prop:tilt`), part 7: the gapwise bound for `B` and the assembled statement

* `EB_gap_dominated_38` (W12.02, gapwise bound): for `u` in an `H¹` ball the gap integral of `B` is
  dominated by the action-weighted tail `C a_n ⟨n⟩^{-3/2} |Φ_n(u)|²`.  (v2's displayed bound has
  `⟨n⟩^{-2}`; the exponent `-3/2` obtained here from the W05 estimate suffices for the finiteness and
  continuity on `𝓕⁻¹ E_s`, `s < 3/4`, and is not used further.)
* `W12_38`: the four assertions of `D:prop:tilt` as one conjunction (conditional on `B`, `O`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.SpectralFoundations
  NlsGge.Sobolev38 Filter Topology
open scoped ENNReal Real ContDiff

section Gapwise

variable {lower upper : ℝ}

theorem tailWeight38_tilt_le (c : BoundedCoefficients lower upper) {δ : ℝ} (_hδ0 : 0 < δ)
    (_hδ : δ * upper < lower) (n : ℤ) :
    tailWeight38 (tiltCoef38 c.val δ) n ≤ tailWeight38 c.val n := by
  unfold tailWeight38
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (japaneseBracket_pos n).le _)
  rw [fullWeightRate_tilt38]
  nlinarith [bRate38_nonneg c n]

namespace BirkhoffInput38

variable (B : BirkhoffInput38)

/-- **W12.02 (gapwise bound).** Conditional on `B`.  For `Bd ≥ 1` there is `C` such that every
`u ∈ H¹` with `‖u‖_{H¹} ≤ Bd` has `(2/π)∫_{g_n(u)} B(2λ) v(λ;u) dλ ≤ C a_n ⟨n⟩^{-3/2} |Φ_n(u)|²`. -/
theorem EB_gap_dominated_38 (c : BoundedCoefficients lower upper) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ * upper < lower) (Bd : ℝ) (hBd : 1 ≤ Bd) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : PhysicalL2, ∀ hu : SobolevSquareSummable 1 (physicalFourier u),
      ‖physicalSobolevL2 1 u hu‖ ≤ Bd → ∀ n : ℤ,
      gapIntegral38 (bCoef38 c.val) u n ≤ C * (tailWeight38 c.val n * ‖B.Φ u n‖ ^ 2) := by
  obtain ⟨CB1, hCB1, h1⟩ := B.remainderSummand_dominated_phys38 c Bd hBd
  obtain ⟨CB2, hCB2, h2⟩ := B.remainderSummand_dominated_phys38 (tiltBounded38 c hδ0 hδ) Bd hBd
  set K : ℝ := max 1 (upper / lower) with hK
  refine ⟨K + (CB1 + CB2) / δ, by positivity, fun u hu hn n => ?_⟩
  have hid := remainderSummand38_tilt c hδ0 hδ u n
  have hI : ‖B.Φ u n‖ ^ 2 = actualGapActionAllE02_38 u n := B.sq_norm_Φ_eq_action u hu n
  have hr1 := h1 u hu hn n
  have hr2 := h2 u hu hn n
  rw [tiltBounded38_val] at hr2
  have htw := tailWeight38_tilt_le c hδ0 hδ n
  have hbn := bRate38_le_tail38 c n
  have hI0 : 0 ≤ ‖B.Φ u n‖ ^ 2 := sq_nonneg _
  have htw0 : 0 ≤ tailWeight38 c.val n :=
    tailWeight38_nonneg lower upper c.val (coef_lower38 c) (coef_bound38 c) (coef_upper38 c) n
  -- `g_B = b I + (R_W - R_W̃)/δ`
  have hgB : gapIntegral38 (bCoef38 c.val) u n = bRate38 c.val n * ‖B.Φ u n‖ ^ 2 +
      (remainderSummand38 c.val u n - remainderSummand38 (tiltCoef38 c.val δ) u n) / δ := by
    rw [hI]
    field_simp
    linarith [hid]
  rw [hgB]
  have habs : remainderSummand38 c.val u n - remainderSummand38 (tiltCoef38 c.val δ) u n ≤
      (CB1 + CB2) * (tailWeight38 c.val n * ‖B.Φ u n‖ ^ 2) := by
    have a1 := (abs_le.1 hr1).2
    have a2 := (abs_le.1 hr2).1
    have : CB2 * (tailWeight38 (tiltCoef38 c.val δ) n * ‖B.Φ u n‖ ^ 2) ≤
        CB2 * (tailWeight38 c.val n * ‖B.Φ u n‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right htw hI0) hCB2.le
    linarith
  have h3 : (remainderSummand38 c.val u n - remainderSummand38 (tiltCoef38 c.val δ) u n) / δ ≤
      (CB1 + CB2) / δ * (tailWeight38 c.val n * ‖B.Φ u n‖ ^ 2) := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right habs hδ0.le
  have h4 : bRate38 c.val n * ‖B.Φ u n‖ ^ 2 ≤ K * (tailWeight38 c.val n * ‖B.Φ u n‖ ^ 2) := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hbn hI0
  nlinarith

end BirkhoffInput38

end Gapwise

section Headline

variable {lower upper : ℝ}

/-- **Mass coercivity on `𝓕⁻¹ E_s`**: `E_B(u) ≥ W(‖u‖_{L²}) - β_0` (`√Q_0(u) = ‖u‖_{L²}`), as an
inequality in `[0,∞]`, for every `u ∈ 𝓕⁻¹ E_s` (each such `u` has a smooth representative). -/
theorem EB_mass_coercivity_FinvE38 (c : BoundedCoefficients lower upper) (s : ℝ)
    (u : FinvE38 c s) :
    ENNReal.ofReal (weight c.val ‖u.1‖ - NlsGge.coefficient c.val 0) ≤ EB38 c.val u.1 := by
  obtain ⟨U, hU, hper, hUu⟩ := NlsGge.Birkhoff.exists_smooth_rep38 (physOfE38 c s (toE38 c s u))
    (fun m => sobolev_physOfE38 c s (m : ℝ) (toE38 c s u))
  rw [physOfE38_toE38] at hUu
  rw [← hUu]
  exact EB_mass_coercivity_norm_38 c U hU hper

namespace BirkhoffInput38

variable (B : BirkhoffInput38)

/-- **W12 (v2 `D:prop:tilt`), assembled; conditional on `B : BirkhoffInput38` (E01) and
`O : OneSmoothingInput38 B` (E04).**  Let `c` be bounded coefficients, `δ > 0` with `δ c_+ < c_-`
(v2: `δ < c_minus/(4 c_plus)`, or `δ < 1/4` for `1 ≤ c_j ≤ 2`), `s < 3/4`, `W̃ = W - δ B` (numerators
`tiltCoef38 c δ`), `b_n = B(2πn)`, `D_δ = ∏_n (1 - δ b_n/a_n)`. Then
1. `E_B` is finite and continuous on `𝓕⁻¹ E_s` (topology of `E_s`);
2. `D_δ > 0` and the product converges (`HasProd`);
3. `e^{δ E_B}` is `μ_W`-integrable, `E_B < ∞` `μ_W`-a.e., and
   `∫ e^{δ E_B} dμ_W = Z_W̃/(Z_W D_δ)`;
4. `E_B(u) ≥ W(‖u‖_{L²}) - β_0` for every `u ∈ 𝓕⁻¹ E_s`. -/
theorem W12_38 (O : OneSmoothingInput38 B) (c : BoundedCoefficients lower upper) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ : δ * upper < lower) {s : ℝ} (hs : s < 3 / 4) :
    ((∀ u : FinvE38 c s, EB38 c.val u.1 ≠ ⊤) ∧
      @Continuous (FinvE38 c s) ℝ (topFinvE38 c s) _ (fun u => (EB38 c.val u.1).toReal)) ∧
    (0 < Dtilt38 c.val δ ∧
      HasProd (fun n : ℤ => 1 - δ * bRate38 c.val n / fullWeightRate c.val n)
        (Dtilt38 c.val δ)) ∧
    (Integrable (fun u => Real.exp (δ * (EB38 c.val u).toReal)) (B.muW38 c.val) ∧
      (∀ᵐ u ∂(B.muW38 c.val), EB38 c.val u ≠ ⊤) ∧
      ∫ u, Real.exp (δ * (EB38 c.val u).toReal) ∂(B.muW38 c.val) =
        B.ZW38 (tiltCoef38 c.val δ) / (B.ZW38 c.val * Dtilt38 c.val δ)) ∧
    (∀ u : FinvE38 c s,
      ENNReal.ofReal (weight c.val ‖u.1‖ - NlsGge.coefficient c.val 0) ≤ EB38 c.val u.1) :=
  ⟨B.EB_finite_continuous_W12_38 O c hs,
    hasProd_tilt38 c hδ0 hδ,
    ⟨B.tilt_integrable_W12_38 c hδ0 hδ, B.ae_muW38_EB_ne_top c hδ0 hδ,
      B.tilt_integral_W12_38 c hδ0 hδ⟩,
    fun u => EB_mass_coercivity_FinvE38 c s u⟩

end BirkhoffInput38

end Headline

end NlsGge.Birkhoff
end
