import NlsGge.Birkhoff.W12Tilt38d
import NlsGge.Birkhoff.W05ChargeSeries38

/-! # W12 (`D:prop:tilt`), part 6 (conditional on `B` and `O`): `E_B` is finite and continuous on
`𝓕⁻¹ E_s`

v2 l.1836-1837, 1852-1853: "The functional `E_B` is finite and continuous on `𝓕⁻¹ E_s`."

Route in Lean (a departure from the displayed proof, which re-runs the W05 dominated-convergence
estimate with the weight `B`): for an admissible `δ` the exact relation of W12.05,
`E_B(u) = (R_W(u) - R_W̃(u))/δ + ∑ b_n |Φ_n(u)|²`, expresses `E_B` through
* the remainders `R_W`, `R_W̃`, which are finite and continuous on `𝓕⁻¹ E_s` by W05
  (`W05_chargeSeries_38`, applied to `W` and to `W̃ = W - δ B`; `E_s(W) ⊆ E_s(W̃)` continuously, since
  `ã_n ≤ a_n`), and
* the quadratic form `Q_b(y) = ∑ b_n |y_n|²`, bounded and continuous on `E_s` because
  `b_n ≤ max(1, c_+/c_-) a_n ⟨n⟩^{-3/2} ≤ max(1,c_+/c_-) a_n ⟨n⟩^{-2s}` for `s ≤ 3/4`
  (`bRate38_le_mul_fullModeWeight`), composed with the W04 homeomorphism `T` of `E_s`.
Both arguments use the same inputs (W05, W04); neither assumes the target.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.SpectralFoundations
  NlsGge.Sobolev38 Filter Topology
open scoped ENNReal Real

section QuadraticForm

variable {lower upper : ℝ}

theorem bRate38_pos (c : BoundedCoefficients lower upper) (n : ℤ) : 0 < bRate38 c.val n := by
  have hs := summable_weightTerm_bCoef38 c (2 * Real.pi * n)
  have h0 : 0 < NlsGge.weightTerm (bCoef38 c.val) (2 * Real.pi * n) 0 := by
    simp only [NlsGge.weightTerm, Nat.mul_zero, pow_zero, mul_one]
    rw [coefficient_bCoef38]
    exact div_pos ((coef_lower38 c).trans_le (coef_bound38 c 1)) (by positivity)
  exact h0.trans_le (hs.le_tsum 0 (fun j _ => weightTerm_bCoef_nonneg38 c _ j))

instance bRateFact38 (c : BoundedCoefficients lower upper) :
    Fact (∀ n : ℤ, 0 < bRate38 c.val n) := ⟨bRate38_pos c⟩

/-- `b_n ≤ max(1, c_+/c_-) · a_n ⟨n⟩^{-2s}` for `s ≤ 3/4`. -/
theorem bRate38_le_mul_fullModeWeight (c : BoundedCoefficients lower upper) {s : ℝ} (hs : s ≤ 3 / 4)
    (n : ℤ) : bRate38 c.val n ≤ max 1 (upper / lower) * fullModeWeight c s n := by
  refine (bRate38_le_tail38 c n).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  unfold tailWeight38 fullModeWeight
  rw [sourceRate_eq_fullWeightRate38]
  refine mul_le_mul_of_nonneg_left ?_ (fullWeightRate_pos38 c n).le
  have : (-(3 / 2) : ℝ) ≤ -2 * s := by linarith
  exact Real.rpow_le_rpow_of_exponent_le (japaneseBracket_one_le38 n) this

theorem summable_bRate_mul_sq_of_seqE38 (c : BoundedCoefficients lower upper) {s : ℝ} (hs : s ≤ 3 / 4)
    {y : ℤ → ℂ} (hy : y ∈ seqE38 c s) :
    Summable (fun n : ℤ => bRate38 c.val n * ‖y n‖ ^ 2) := by
  have h := ((mem_seqE38_iff c s y).1 hy).mul_left (max 1 (upper / lower))
  refine h.of_nonneg_of_le (fun n => mul_nonneg (bRate38_pos c n).le (sq_nonneg _)) (fun n => ?_)
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (bRate38_le_mul_fullModeWeight c hs n) (sq_nonneg _)

theorem mem_weightedSubmodule_bRate38 (c : BoundedCoefficients lower upper) {s : ℝ} (hs : s ≤ 3 / 4)
    {y : ℤ → ℂ} (hy : y ∈ seqE38 c s) : y ∈ weightedSubmodule (bRate38 c.val) := by
  change Memℓp (weightedCoordinates (bRate38 c.val) y) 2
  rw [weightedCoordinates_mem_l2_iff _ (fun n => (bRate38_pos c n).le)]
  exact summable_bRate_mul_sq_of_seqE38 c hs hy

/-- The inclusion `E_s → ℓ²(b)` (`ℓ²` with weight `b_n`) of `E_s`, `s ≤ 3/4`. -/
def iotaB38 (c : BoundedCoefficients lower upper) {s : ℝ} (hs : s ≤ 3 / 4) (x : ECarrier38 c s) :
    WeightedHilbert (bRate38 c.val) :=
  ⟨eCoe38 c s x, mem_weightedSubmodule_bRate38 c hs (eCoe38_mem c s x)⟩

theorem iotaB38_sub (c : BoundedCoefficients lower upper) {s : ℝ} (hs : s ≤ 3 / 4)
    (x y : ECarrier38 c s) :
    iotaB38 c hs (x - y) = iotaB38 c hs x - iotaB38 c hs y := Subtype.ext rfl

theorem norm_sq_iotaB38 (c : BoundedCoefficients lower upper) {s : ℝ} (hs : s ≤ 3 / 4)
    (y : ECarrier38 c s) :
    ‖iotaB38 c hs y‖ ^ 2 = ∑' n : ℤ, bRate38 c.val n * ‖eCoe38 c s y n‖ ^ 2 :=
  weightedHilbert_norm_sq (bRate38 c.val) (iotaB38 c hs y)

theorem norm_sq_iotaB38_le (c : BoundedCoefficients lower upper) {s : ℝ} (hs : s ≤ 3 / 4)
    (y : ECarrier38 c s) : ‖iotaB38 c hs y‖ ^ 2 ≤ max 1 (upper / lower) * ‖y‖ ^ 2 := by
  rw [norm_sq_iotaB38, norm_sq_eCarrier38, ← tsum_mul_left]
  have h1 : Summable (fun n : ℤ => bRate38 c.val n * ‖eCoe38 c s y n‖ ^ 2) :=
    summable_bRate_mul_sq_of_seqE38 c hs (eCoe38_mem c s y)
  have h2 : Summable (fun n : ℤ => fullModeWeight c s n * ‖eCoe38 c s y n‖ ^ 2) :=
    (hasSum_norm_sq_eCarrier38 c s y).summable
  refine h1.tsum_le_tsum (fun n => ?_) (h2.mul_left _)
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (bRate38_le_mul_fullModeWeight c hs n) (sq_nonneg _)

theorem continuous_iotaB38 (c : BoundedCoefficients lower upper) {s : ℝ} (hs : s ≤ 3 / 4) :
    Continuous (iotaB38 c hs) := by
  refine (LipschitzWith.of_dist_le_mul
    (K := ⟨Real.sqrt (max 1 (upper / lower)), Real.sqrt_nonneg _⟩) (fun x y => ?_)).continuous
  rw [dist_eq_norm, dist_eq_norm, ← iotaB38_sub]
  have h := norm_sq_iotaB38_le c hs (x - y)
  show ‖iotaB38 c hs (x - y)‖ ≤ Real.sqrt _ * ‖x - y‖
  rw [← Real.sqrt_sq (norm_nonneg (iotaB38 c hs (x - y))), ← Real.sqrt_sq (norm_nonneg (x - y)),
    ← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt h

/-- `Q_b(y) = ∑ b_n |y_n|²` is a bounded, continuous quadratic form on `E_s` (`s ≤ 3/4`). -/
theorem continuous_Qb38 (c : BoundedCoefficients lower upper) {s : ℝ} (hs : s ≤ 3 / 4) :
    Continuous (fun y : ECarrier38 c s => ∑' n : ℤ, bRate38 c.val n * ‖eCoe38 c s y n‖ ^ 2) := by
  have : (fun y : ECarrier38 c s => ∑' n : ℤ, bRate38 c.val n * ‖eCoe38 c s y n‖ ^ 2) =
      fun y => ‖iotaB38 c hs y‖ ^ 2 := by
    funext y; rw [norm_sq_iotaB38]
  rw [this]
  exact (continuous_iotaB38 c hs).norm.pow 2

end QuadraticForm

section Comparison

variable {lower upper : ℝ}

theorem fullModeWeight_tilt_le (c : BoundedCoefficients lower upper) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ * upper < lower) (s : ℝ) (n : ℤ) :
    fullModeWeight (tiltBounded38 c hδ0 hδ) s n ≤ fullModeWeight c s n := by
  unfold fullModeWeight
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (japaneseBracket_pos n).le _)
  rw [sourceRate_eq_fullWeightRate38, sourceRate_eq_fullWeightRate38]
  rw [tiltBounded38_val, fullWeightRate_tilt38]
  nlinarith [bRate38_nonneg c n]

theorem seqE38_subset_tilt (c : BoundedCoefficients lower upper) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ * upper < lower) (s : ℝ) {y : ℤ → ℂ} (hy : y ∈ seqE38 c s) :
    y ∈ seqE38 (tiltBounded38 c hδ0 hδ) s := by
  rw [mem_seqE38_iff] at hy ⊢
  refine hy.of_nonneg_of_le (fun n => mul_nonneg (fullModeWeight_pos _ s n).le (sq_nonneg _))
    (fun n => ?_)
  exact mul_le_mul_of_nonneg_right (fullModeWeight_tilt_le c hδ0 hδ s n) (sq_nonneg _)

/-- The identity map `E_s(W) → E_s(W̃)`. -/
def jE38 (c : BoundedCoefficients lower upper) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ * upper < lower)
    (s : ℝ) (x : ECarrier38 c s) : ECarrier38 (tiltBounded38 c hδ0 hδ) s :=
  eMk38 _ s (eCoe38 c s x) (seqE38_subset_tilt c hδ0 hδ s (eCoe38_mem c s x))

theorem eCoe38_jE38 (c : BoundedCoefficients lower upper) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ * upper < lower) (s : ℝ) (x : ECarrier38 c s) :
    eCoe38 (tiltBounded38 c hδ0 hδ) s (jE38 c hδ0 hδ s x) = eCoe38 c s x := by
  unfold jE38
  exact eCoe38_mk _ _ _ _

theorem jE38_sub (c : BoundedCoefficients lower upper) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ * upper < lower) (s : ℝ) (x y : ECarrier38 c s) :
    jE38 c hδ0 hδ s (x - y) = jE38 c hδ0 hδ s x - jE38 c hδ0 hδ s y := by
  apply eExt38
  funext n
  rw [eCoe38_sub, eCoe38_jE38, eCoe38_jE38, eCoe38_jE38, eCoe38_sub]

theorem norm_sq_jE38_le (c : BoundedCoefficients lower upper) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ * upper < lower) (s : ℝ) (y : ECarrier38 c s) :
    ‖jE38 c hδ0 hδ s y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
  rw [norm_sq_eCarrier38, norm_sq_eCarrier38]
  simp only [eCoe38_jE38]
  have h2 := (hasSum_norm_sq_eCarrier38 c s y).summable
  have h1 : Summable (fun n : ℤ => fullModeWeight (tiltBounded38 c hδ0 hδ) s n *
      ‖eCoe38 c s y n‖ ^ 2) :=
    h2.of_nonneg_of_le (fun n => mul_nonneg (fullModeWeight_pos _ s n).le (sq_nonneg _))
      (fun n => mul_le_mul_of_nonneg_right (fullModeWeight_tilt_le c hδ0 hδ s n) (sq_nonneg _))
  exact h1.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_right
    (fullModeWeight_tilt_le c hδ0 hδ s n) (sq_nonneg _)) h2

theorem continuous_jE38 (c : BoundedCoefficients lower upper) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ * upper < lower) (s : ℝ) : Continuous (jE38 c hδ0 hδ s) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) (fun x y => ?_)).continuous
  rw [dist_eq_norm, dist_eq_norm, ← jE38_sub]
  have h := norm_sq_jE38_le c hδ0 hδ s (x - y)
  simp only [NNReal.coe_one, one_mul]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

theorem physOfE38_jE38 (c : BoundedCoefficients lower upper) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ * upper < lower) (s : ℝ) (x : ECarrier38 c s) :
    physOfE38 (tiltBounded38 c hδ0 hδ) s (jE38 c hδ0 hδ s x) = physOfE38 c s x := by
  apply fourierSeq38_injective
  rw [fourierSeq38_physOfE38, fourierSeq38_physOfE38, eCoe38_jE38]

end Comparison

namespace BirkhoffInput38

variable {lower upper : ℝ} (B : BirkhoffInput38)

/-- **W12.02 + W12.05 on `E_s`.** Conditional on `B`, `O`; for any admissible `δ` (`0 < δ`,
`δ c_+ < c_-`) and `s < 3/4`, the field `u = 𝓕⁻¹ x`, `x ∈ E_s`, has `E_B(u) < ∞` and
`δ E_B(u) = R_W(u) - R_W̃(u) + δ ∑ b_n |(T x)_n|²`. -/
theorem EB_identity_physOfE38 (O : OneSmoothingInput38 B) (c : BoundedCoefficients lower upper)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ * upper < lower) {s : ℝ} (hs : s < 3 / 4)
    (x : ECarrier38 c s) :
    EB38 c.val (physOfE38 c s x) ≠ ⊤ ∧
    δ * (EB38 c.val (physOfE38 c s x)).toReal =
      remainder38 c.val (physOfE38 c s x) - remainder38 (tiltCoef38 c.val δ) (physOfE38 c s x) +
        δ * ∑' n : ℤ, bRate38 c.val n * ‖eCoe38 c s (B.weightedHomeoE38 O c s x) n‖ ^ 2 := by
  set u := physOfE38 c s x with hu
  have h1 : Summable (fun n : ℤ => remainderSummand38 c.val u n) :=
    B.summable_remainder_physOfE38 c s O hs.le x
  have h2' := B.summable_remainder_physOfE38 (tiltBounded38 c hδ0 hδ) s O hs.le (jE38 c hδ0 hδ s x)
  rw [physOfE38_jE38] at h2'
  have h2 : Summable (fun n : ℤ => remainderSummand38 (tiltCoef38 c.val δ) u n) := h2'
  have hact : ∀ n, actualGapActionAllE02_38 u n =
      ‖eCoe38 c s (B.weightedHomeoE38 O c s x) n‖ ^ 2 := fun n => by
    rw [B.action_physOfE38 c s x n, B.eCoe_weightedHomeoE38 c s O x]
  have hmem : eCoe38 c s (B.weightedHomeoE38 O c s x) ∈ seqE38 c s := eCoe38_mem _ _ _
  have h3 : Summable (fun n : ℤ => bRate38 c.val n * actualGapActionAllE02_38 u n) := by
    simp_rw [hact]; exact summable_bRate_mul_sq_of_seqE38 c hs.le hmem
  obtain ⟨hfin, hid⟩ := remainder_tilt_identity38 c hδ0 hδ u h1 h2 h3
  refine ⟨hfin, ?_⟩
  have : ∑' n : ℤ, bRate38 c.val n * actualGapActionAllE02_38 u n =
      ∑' n : ℤ, bRate38 c.val n * ‖eCoe38 c s (B.weightedHomeoE38 O c s x) n‖ ^ 2 := by
    simp_rw [hact]
  rw [← this]
  linarith [hid]

/-- **`E_B` is finite and continuous on `𝓕⁻¹ E_s`** (v2 `D:prop:tilt`, first assertion), conditional
on `B` (E01) and `O` (E04), for `s < 3/4` (v2: `1/2 < s < 3/4`), with the topology of `𝓕⁻¹ E_s`
transported from `E_s` by `𝓕` (`topFinvE38`).  `E_B` is the extended-real spectral energy
`(2/π)∫ B(2λ) v dλ` of the reserved weight `B`. -/
theorem EB_finite_continuous_W12_38 (O : OneSmoothingInput38 B) (c : BoundedCoefficients lower upper)
    {s : ℝ} (hs : s < 3 / 4) :
    (∀ u : FinvE38 c s, EB38 c.val u.1 ≠ ⊤) ∧
    @Continuous (FinvE38 c s) ℝ (topFinvE38 c s) _ (fun u => (EB38 c.val u.1).toReal) := by
  have hl := coef_lower38 c
  have hup : 0 < upper := lt_of_lt_of_le hl c.property.2.1
  set δ : ℝ := lower / (2 * upper) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδu : δ * upper < lower := by
    rw [hδ, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  refine ⟨fun u => ?_, ?_⟩
  · have := (B.EB_identity_physOfE38 O c hδ0 hδu hs (toE38 c s u)).1
    rwa [physOfE38_toE38] at this
  · let _ := topFinvE38 c s
    -- continuity on the carrier
    have hcont : Continuous (fun x : ECarrier38 c s => (EB38 c.val (physOfE38 c s x)).toReal) := by
      have hR := B.continuous_remainder_physOfE38 c s O hs
      have hR' := (B.continuous_remainder_physOfE38 (tiltBounded38 c hδ0 hδu) s O hs).comp
        (continuous_jE38 c hδ0 hδu s)
      have hQ := (continuous_Qb38 c hs.le).comp (B.weightedHomeoE38 O c s).continuous
      have hall : Continuous (fun x : ECarrier38 c s =>
          (remainder38 c.val (physOfE38 c s x) -
            remainder38 (tiltCoef38 c.val δ) (physOfE38 c s x)) / δ +
          ∑' n : ℤ, bRate38 c.val n * ‖eCoe38 c s (B.weightedHomeoE38 O c s x) n‖ ^ 2) := by
        refine ((hR.sub ?_).div_const δ).add hQ
        have e : (fun x : ECarrier38 c s => remainder38 (tiltCoef38 c.val δ) (physOfE38 c s x)) =
            (fun x : ECarrier38 c s => remainder38 (tiltBounded38 c hδ0 hδu).val
              (physOfE38 (tiltBounded38 c hδ0 hδu) s (jE38 c hδ0 hδu s x))) := by
          funext x
          rw [physOfE38_jE38]; rfl
        rw [e]; exact hR'
      refine hall.congr (fun x => ?_)
      have := (B.EB_identity_physOfE38 O c hδ0 hδu hs x).2
      field_simp
      linarith
    have h1 : Continuous (fun u : FinvE38 c s => toE38 c s u) := continuous_induced_dom
    have e : (fun u : FinvE38 c s => (EB38 c.val u.1).toReal) =
        (fun x : ECarrier38 c s => (EB38 c.val (physOfE38 c s x)).toReal) ∘ (toE38 c s) := by
      funext u; simp only [Function.comp_apply, physOfE38_toE38]
    rw [e]; exact hcont.comp h1

end BirkhoffInput38

end NlsGge.Birkhoff
end
