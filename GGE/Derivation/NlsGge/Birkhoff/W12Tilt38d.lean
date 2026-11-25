import NlsGge.Birkhoff.W12Tilt38c
import NlsGge.Birkhoff.S04Moments38b

/-! # W12 (`D:prop:tilt`), part 4 (conditional on `B : BirkhoffInput38`): the exact tilt identity

v2 l.1856-1860: substitution of `R_W̃ = R_W - δ(E_B - ∑ b_n I_n)` in the defining Birkhoff integrals
gives `∫ e^{δ E_B} dμ_W = Z_W̃ / (Z_W D_δ)`.

Only `B` (E01) is used here (through the S03 objects `Rbar38`, `ZW38`, `muHatW38`, `muW38`); the
one-smoothing input `O` is not needed for the identity.  The proof, in the Lean formalization:

1. `Φ u ∈ Ω₀(c)` for `μ_W`-a.e. `u`, and `Ω₀(c) ⊆ Ω₀(W̃)` (`ã_n ≤ a_n`);
2. for `Φ u ∈ Ω₀(c)`, `u = Φ⁻¹ z` has summable remainders for `W` and `W̃` (S03) and
   `∑ b_n |z_n|² < ∞` (`b_n ≤ a_n/(2πn)²`, `Ω₀`), so `remainder_tilt_identity38` gives `E_B(u) < ∞`
   and `R_W̃ = R_W - δ(E_B - ∑ b_n|z_n|²)`;
3. the integrand `e^{δ E_B}` is `μ_W`-a.e. equal to the measurable function
   `e^{R̄_W - R̄_W̃ + δ ∑ b_n |Φ_n|²} ∘ Φ` (so no measurability of `E_B` itself is needed);
4. `∫ e^{δ E_B} dμ_W = Z_W^{-1} ∫ e^{δ ∑b|z|²} e^{-R̄_W̃} dγ_W = (Z_W D_δ)^{-1} ∫ e^{-R̄_W̃} dγ_W̃`
   by `gaussian_tilt_density38`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.SpectralFoundations
  NlsGge.Sobolev38 Filter Topology
open scoped ENNReal Real

section Bounds

variable {lower upper : ℝ}

theorem japaneseBracket_one_le38 (n : ℤ) : 1 ≤ japaneseBracket n := by
  unfold japaneseBracket
  exact Real.one_le_sqrt.2 (by nlinarith [sq_nonneg (n : ℝ)])

theorem japaneseBracket_sq38 (n : ℤ) : japaneseBracket n ^ 2 = 1 + (n : ℝ) ^ 2 := by
  unfold japaneseBracket
  exact Real.sq_sqrt (by positivity)

/-- `b_n ≤ max(1, c_+/c_-) · a_n ⟨n⟩^{-3/2}`: `b_n (2πn)² ≤ a_n` for `n ≠ 0`, `b_0 ≤ (c_+/c_-) a_0`. -/
theorem bRate38_le_tail38 (c : BoundedCoefficients lower upper) (n : ℤ) :
    bRate38 c.val n ≤ max 1 (upper / lower) * tailWeight38 c.val n := by
  have ha := fullWeightRate_pos38 c n
  have hl := coef_lower38 c
  have hup : 0 < upper := lt_of_lt_of_le hl c.property.2.1
  have hb0 := bRate38_nonneg c n
  unfold tailWeight38
  by_cases hn : n = 0
  · subst hn
    have hJ : japaneseBracket 0 = 1 := by simp [japaneseBracket]
    rw [hJ, Real.one_rpow, mul_one]
    calc bRate38 c.val 0 ≤ (upper / lower) * fullWeightRate c.val 0 := bRate38_le38 c 0
      _ ≤ max 1 (upper / lower) * fullWeightRate c.val 0 :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) ha.le
  · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
      have : (1 : ℤ) ≤ n ^ 2 := by nlinarith [Int.one_le_abs hn, sq_abs n]
      exact_mod_cast this
    have h1 := bRate38_mul_sq_le38 c n
    have hJ := japaneseBracket_one_le38 n
    have hJ2 := japaneseBracket_sq38 n
    have hrp : japaneseBracket n ^ (3 / 2 : ℝ) ≤ (2 * Real.pi * n) ^ 2 := by
      calc japaneseBracket n ^ (3 / 2 : ℝ) ≤ japaneseBracket n ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hJ (by norm_num)
        _ = 1 + (n : ℝ) ^ 2 := by rw [Real.rpow_two]; exact hJ2
        _ ≤ (2 * Real.pi * n) ^ 2 := by
            have hp4 : (4 : ℝ) ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
            rw [mul_pow]
            nlinarith
    have hpos : 0 < japaneseBracket n ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    have hneg : japaneseBracket n ^ (-(3 / 2) : ℝ) = (japaneseBracket n ^ (3 / 2 : ℝ))⁻¹ :=
      Real.rpow_neg (by linarith) _
    rw [hneg]
    have h2 : bRate38 c.val n ≤ fullWeightRate c.val n * (japaneseBracket n ^ (3 / 2 : ℝ))⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hpos]
      have hsq : 0 ≤ bRate38 c.val n := hb0
      calc bRate38 c.val n * japaneseBracket n ^ (3 / 2 : ℝ)
          ≤ bRate38 c.val n * (2 * Real.pi * n) ^ 2 := mul_le_mul_of_nonneg_left hrp hsq
        _ = (2 * Real.pi * n) ^ 2 * bRate38 c.val n := by ring
        _ ≤ _ := h1
    calc bRate38 c.val n ≤ fullWeightRate c.val n * (japaneseBracket n ^ (3 / 2 : ℝ))⁻¹ := h2
      _ ≤ max 1 (upper / lower) * (fullWeightRate c.val n *
          (japaneseBracket n ^ (3 / 2 : ℝ))⁻¹) :=
          le_mul_of_one_le_left (mul_nonneg ha.le (inv_nonneg.2 hpos.le)) (le_max_left _ _)

/-- `∑ b_n |z_n|² < ∞` on `Ω₀` (the tail series of v2 `A:eq:tailsum` dominates it). -/
theorem summable_bRate_mul_sq_of_Omega038 (c : BoundedCoefficients lower upper) {z : ℤ → ℂ}
    (hz : z ∈ Omega038 c.val) :
    Summable (fun n : ℤ => bRate38 c.val n * ‖z n‖ ^ 2) := by
  refine (hz.2.mul_left (max 1 (upper / lower))).of_nonneg_of_le
    (fun n => mul_nonneg (bRate38_nonneg c n) (sq_nonneg _)) (fun n => ?_)
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (bRate38_le_tail38 c n) (sq_nonneg _)

/-- `Ω₀(c) ⊆ Ω₀(c̃)` (`ã_n ≤ a_n`). -/
theorem Omega038_subset_tilt (c : BoundedCoefficients lower upper) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ * upper < lower) : Omega038 c.val ⊆ Omega038 (tiltCoef38 c.val δ) := by
  intro z hz
  refine ⟨hz.1, hz.2.of_nonneg_of_le (fun n => ?_) (fun n => ?_)⟩
  · exact mul_nonneg (tailWeight38_nonneg (lower - δ * upper) upper _
      (tiltCoef38_bounds c hδ0 hδ).1 (fun j => ((tiltCoef38_bounds c hδ0 hδ).2.2 j).1)
      (fun j => ((tiltCoef38_bounds c hδ0 hδ).2.2 j).2) n) (sq_nonneg _)
  · refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    unfold tailWeight38
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (japaneseBracket_pos n).le _)
    rw [fullWeightRate_tilt38]
    nlinarith [bRate38_nonneg c n]

end Bounds

namespace BirkhoffInput38

open BirkhoffTop38

variable {lower upper : ℝ} (B : BirkhoffInput38)

theorem measurable_Phi38 : Measurable B.Φ := by
  have : B.Φ = fun u => B.cleanT0 (fourierSeq38 u) :=
    funext fun u => (B.cleanT0_of_mem _ (fourierSeq38_mem_zero u)).symm
  rw [this]
  exact B.measurable_cleanT0.comp measurable_fourierSeq38

theorem cleanΦinv_Φ38 (u : PhysicalL2) : B.cleanΦinv (B.Φ u) = u := by
  rw [B.cleanΦinv_of_mem _ (B.Φ_mem_zero u)]
  exact B.Φinv_Φ u

/-- `Φ u ∈ Ω₀(c)` for `μ_W`-almost every `u` (`Ω₀` has full `γ_W`, hence `μ̂_W`, measure and
`Φ(Φ⁻¹ z) = z` on it). -/
theorem ae_muW38_Phi_mem_Omega038 (c : BoundedCoefficients lower upper) :
    ∀ᵐ u ∂(B.muW38 c.val), B.Φ u ∈ Omega038 c.val := by
  have hmeas : MeasurableSet {u : PhysicalL2 | B.Φ u ∈ Omega038 c.val} :=
    (measurableSet_Omega038 lower upper c.val (coef_lower38 c) (coef_bound38 c)
      (coef_upper38 c)).preimage B.measurable_Phi38
  refine (ae_map_iff B.measurable_cleanΦinv.aemeasurable hmeas).2 ?_
  have h0 : ∀ᵐ z ∂(fullWeightSequenceGaussian c.val), z ∈ Omega038 c.val ∧ B.Φ (B.cleanΦinv z) = z := by
    filter_upwards [ae_mem_Omega038 lower upper c.val (coef_lower38 c) (coef_bound38 c)
      (coef_upper38 c)] with z hz
    exact ⟨hz, B.Φ_cleanΦinv z (seqSobolev38_natCast_mono (mem_seqSobolev38_of_Omega038 _ hz 1))⟩
  have h1 := (B.muHatW38_equivalent lower upper c.val (coef_lower38 c) (coef_bound38 c)
    (coef_upper38 c)).1.ae_le h0
  filter_upwards [h1] with z hz
  show B.Φ (B.cleanΦinv z) ∈ Omega038 c.val
  rw [hz.2]; exact hz.1

/-- **W12.05 in Birkhoff coordinates.** If `Φ u ∈ Ω₀(c)` then `E_B(u) < ∞` and, with
`z = Φ u`, `R̄_W̃(z) = R̄_W(z) - δ (E_B(u) - ∑ b_n |z_n|²)`. -/
theorem tilt_remainder_identity38 (c : BoundedCoefficients lower upper) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ * upper < lower) (u : PhysicalL2) (hu : B.Φ u ∈ Omega038 c.val) :
    EB38 c.val u ≠ ⊤ ∧
    B.Rbar38 (tiltCoef38 c.val δ) (B.Φ u) = B.Rbar38 c.val (B.Φ u) -
      δ * ((EB38 c.val u).toReal - bEnergy38 c.val (B.Φ u)) := by
  set z := B.Φ u with hz
  have hadm := tiltCoef38_bounds c hδ0 hδ
  have hz' : z ∈ Omega038 (tiltCoef38 c.val δ) := Omega038_subset_tilt c hδ0 hδ hu
  have hz1 : z ∈ seqSobolev38 ((1 : ℕ) : ℝ) := mem_seqSobolev38_of_Omega038 _ hu 1
  have hcl : B.cleanΦinv z = u := B.cleanΦinv_Φ38 u
  obtain ⟨h1, -⟩ := B.remainder_tendsto_pathwise38 lower upper c.val (coef_lower38 c)
    (coef_bound38 c) (coef_upper38 c) z hu isExhaustion_stdExh38
  obtain ⟨h2, -⟩ := B.remainder_tendsto_pathwise38 (lower - δ * upper) upper (tiltCoef38 c.val δ)
    hadm.1 (fun j => (hadm.2.2 j).1) (fun j => (hadm.2.2 j).2) z hz' isExhaustion_stdExh38
  rw [hcl] at h1 h2
  have hact : ∀ n, actualGapActionAllE02_38 u n = ‖z n‖ ^ 2 := fun n => by
    rw [← hcl]; exact B.action_cleanΦinv38 z hz1 n
  have h3 : Summable (fun n : ℤ => bRate38 c.val n * actualGapActionAllE02_38 u n) := by
    simp_rw [hact]; exact summable_bRate_mul_sq_of_Omega038 c hu
  obtain ⟨hfin, hid⟩ := remainder_tilt_identity38 c hδ0 hδ u h1 h2 h3
  refine ⟨hfin, ?_⟩
  rw [B.Rbar38_of_mem _ hz', B.Rbar38_of_mem _ hu, hcl, hid]
  have : ∑' n : ℤ, bRate38 c.val n * actualGapActionAllE02_38 u n = bEnergy38 c.val z := by
    simp_rw [hact]
    exact (bEnergy38_eq_tsum c (summable_bRate_mul_sq_of_Omega038 c hu)).symm
  rw [this]

theorem ae_muW38_EB_ne_top (c : BoundedCoefficients lower upper) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ * upper < lower) : ∀ᵐ u ∂(B.muW38 c.val), EB38 c.val u ≠ ⊤ := by
  filter_upwards [B.ae_muW38_Phi_mem_Omega038 c] with u hu
  exact (B.tilt_remainder_identity38 c hδ0 hδ u hu).1

/-- **W12 (v2 `D:eq:exacttilt`), extended-real form.**
For `0 < δ`, `δ c_+ < c_-` (which contains v2's ranges `δ < c_minus/(4 c_plus)` and, for `1 ≤ c_j ≤ 2`,
`δ < 1/4`):
`∫ e^{δ E_B} dμ_W = Z_W̃ / (Z_W D_δ)`, with `E_B(u) < ∞` for `μ_W`-a.e. `u`,
`Z_W̃ = B.ZW38 (tiltCoef38 c δ)` the normalizer of the weight `W̃ = W - δ B`. -/
theorem tilt_lintegral_W12_38 (c : BoundedCoefficients lower upper) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ * upper < lower) :
    ∫⁻ u, ENNReal.ofReal (Real.exp (δ * (EB38 c.val u).toReal)) ∂(B.muW38 c.val) =
      ENNReal.ofReal (B.ZW38 (tiltCoef38 c.val δ) / (B.ZW38 c.val * Dtilt38 c.val δ)) := by
  classical
  have hl := coef_lower38 c
  have hbd := coef_bound38 c
  have hup := coef_upper38 c
  have hadm := tiltCoef38_bounds c hδ0 hδ
  have hl' := hadm.1
  have hbd' : ∀ j : ℕ, lower - δ * upper ≤ tiltCoef38 c.val δ j := fun j => (hadm.2.2 j).1
  have hup' : ∀ j : ℕ, tiltCoef38 c.val δ j ≤ upper := fun j => (hadm.2.2 j).2
  obtain ⟨hDpos, -⟩ := hasProd_tilt38 c hδ0 hδ
  set D := Dtilt38 c.val δ with hD
  set c' := tiltCoef38 c.val δ with hc'
  have hZ := (B.ZW38_pos_le_one lower upper c.val hl hbd hup).1
  have hZ' := (B.ZW38_pos_le_one (lower - δ * upper) upper c' hl' hbd' hup').1
  -- measurable functions on Birkhoff coordinates
  have hmR := B.measurable_Rbar38 lower upper c.val hl hbd hup
  have hmR' := B.measurable_Rbar38 (lower - δ * upper) upper c' hl' hbd' hup'
  have hmE := measurable_bEnergy38 c.val
  set Gz : (ℤ → ℂ) → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp (B.Rbar38 c.val z -
    B.Rbar38 c' z + δ * bEnergy38 c.val z)) with hGz
  have hGm : Measurable Gz := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    ((hmR.sub hmR').add (hmE.const_mul δ)))
  -- the integrand is a.e. a measurable function of `Φ u`
  have hae : ∀ᵐ u ∂(B.muW38 c.val),
      ENNReal.ofReal (Real.exp (δ * (EB38 c.val u).toReal)) = Gz (B.Φ u) := by
    filter_upwards [B.ae_muW38_Phi_mem_Omega038 c] with u hu
    have := (B.tilt_remainder_identity38 c hδ0 hδ u hu).2
    simp only [hGz]
    congr 2
    rw [← hc'] at this
    rw [this]; ring
  rw [lintegral_congr_ae hae]
  have hmapped : ∫⁻ u, Gz (B.Φ u) ∂(B.muW38 c.val) = ∫⁻ z, Gz z ∂(B.muHatW38 c.val) := by
    unfold muW38
    rw [lintegral_map (f := fun u => Gz (B.Φ u)) (hGm.comp B.measurable_Phi38)
      B.measurable_cleanΦinv]
    refine lintegral_congr_ae ?_
    have h0 : ∀ᵐ z ∂(fullWeightSequenceGaussian c.val), B.Φ (B.cleanΦinv z) = z := by
      filter_upwards [ae_mem_Omega038 lower upper c.val hl hbd hup] with z hz
      exact B.Φ_cleanΦinv z (seqSobolev38_natCast_mono (mem_seqSobolev38_of_Omega038 _ hz 1))
    filter_upwards [(B.muHatW38_equivalent lower upper c.val hl hbd hup).1.ae_le h0] with z hz
    simp only [hz]
  rw [hmapped]
  unfold muHatW38
  rw [lintegral_withDensity_eq_lintegral_mul _ (B.measurable_density38 lower upper c.val hl hbd hup) hGm]
  -- pointwise rewriting of the integrand
  have hpt : ∀ z, ((fun z => ENNReal.ofReal (Real.exp (-(B.Rbar38 c.val z)) / B.ZW38 c.val)) * Gz) z =
      ENNReal.ofReal (1 / B.ZW38 c.val) * (ENNReal.ofReal (Real.exp (δ * bEnergy38 c.val z)) *
        ENNReal.ofReal (Real.exp (-(B.Rbar38 c' z)))) := by
    intro z
    simp only [Pi.mul_apply, hGz]
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have e1 : Real.exp (B.Rbar38 c.val z - B.Rbar38 c' z + δ * bEnergy38 c.val z) =
        Real.exp (B.Rbar38 c.val z) * (Real.exp (δ * bEnergy38 c.val z) *
          Real.exp (-(B.Rbar38 c' z))) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have e0 : Real.exp (-(B.Rbar38 c.val z)) * Real.exp (B.Rbar38 c.val z) = 1 := by
      rw [← Real.exp_add]; simp
    calc Real.exp (-(B.Rbar38 c.val z)) / B.ZW38 c.val *
          Real.exp (B.Rbar38 c.val z - B.Rbar38 c' z + δ * bEnergy38 c.val z)
        = (Real.exp (-(B.Rbar38 c.val z)) * Real.exp (B.Rbar38 c.val z)) *
          (Real.exp (δ * bEnergy38 c.val z) * Real.exp (-(B.Rbar38 c' z))) / B.ZW38 c.val := by
          rw [e1]; ring
      _ = _ := by rw [e0]; ring
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- the Gaussian density identity
  have hdens : fullWeightSequenceGaussian c' = (fullWeightSequenceGaussian c.val).withDensity
      (fun z => ENNReal.ofReal (D * Real.exp (δ * bEnergy38 c.val z))) :=
    gaussian_tilt_density38 c hδ0 hδ
  have hint' : ∫⁻ z, ENNReal.ofReal (Real.exp (-(B.Rbar38 c' z)))
      ∂(fullWeightSequenceGaussian c') = ENNReal.ofReal (B.ZW38 c') := by
    unfold ZW38
    rw [← ofReal_integral_eq_lintegral_ofReal
      (B.integrable_exp_neg_Rbar38 (lower - δ * upper) upper c' hl' hbd' hup')
      (Filter.Eventually.of_forall fun z => (Real.exp_pos _).le)]
  have hkey : ENNReal.ofReal D * ∫⁻ z, ENNReal.ofReal (Real.exp (δ * bEnergy38 c.val z)) *
      ENNReal.ofReal (Real.exp (-(B.Rbar38 c' z))) ∂(fullWeightSequenceGaussian c.val) =
      ENNReal.ofReal (B.ZW38 c') := by
    rw [← hint', hdens, lintegral_withDensity_eq_lintegral_mul (fullWeightSequenceGaussian c.val)
      (f := fun z => ENNReal.ofReal (D * Real.exp (δ * bEnergy38 c.val z)))
      (g := fun z => ENNReal.ofReal (Real.exp (-(B.Rbar38 c' z))))
      (ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp
        (hmE.const_mul δ))))
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hmR'.neg)),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr (fun z => ?_)
    simp only [Pi.mul_apply]
    rw [ENNReal.ofReal_mul hDpos.le, mul_assoc]
  have hX : ∫⁻ z, ENNReal.ofReal (Real.exp (δ * bEnergy38 c.val z)) *
      ENNReal.ofReal (Real.exp (-(B.Rbar38 c' z))) ∂(fullWeightSequenceGaussian c.val) =
      ENNReal.ofReal (D⁻¹ * B.ZW38 c') := by
    have h1 : ENNReal.ofReal D⁻¹ * (ENNReal.ofReal D * ∫⁻ z, ENNReal.ofReal
        (Real.exp (δ * bEnergy38 c.val z)) * ENNReal.ofReal (Real.exp (-(B.Rbar38 c' z)))
        ∂(fullWeightSequenceGaussian c.val)) = ENNReal.ofReal D⁻¹ * ENNReal.ofReal (B.ZW38 c') := by
      rw [hkey]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hDpos.le), inv_mul_cancel₀ hDpos.ne',
      ENNReal.ofReal_one, one_mul, ← ENNReal.ofReal_mul (inv_nonneg.2 hDpos.le)] at h1
    exact h1
  rw [hX, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/-- The measurable function of the Birkhoff coordinates that represents `e^{δ E_B(Φ⁻¹ z)}`:
`exp(R̄_W(z) - R̄_W̃(z) + δ ∑ b_n |z_n|²)`. -/
def tiltG38 (c : ℕ → ℝ) (δ : ℝ) (z : ℤ → ℂ) : ℝ :=
  Real.exp (B.Rbar38 c z - B.Rbar38 (tiltCoef38 c δ) z + δ * bEnergy38 c z)

theorem measurable_tiltG38 (c : BoundedCoefficients lower upper) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ * upper < lower) : Measurable (B.tiltG38 c.val δ) := by
  have hadm := tiltCoef38_bounds c hδ0 hδ
  have hmR := B.measurable_Rbar38 lower upper c.val (coef_lower38 c) (coef_bound38 c) (coef_upper38 c)
  have hmR' := B.measurable_Rbar38 (lower - δ * upper) upper (tiltCoef38 c.val δ) hadm.1
    (fun j => (hadm.2.2 j).1) (fun j => (hadm.2.2 j).2)
  exact Real.measurable_exp.comp ((hmR.sub hmR').add ((measurable_bEnergy38 c.val).const_mul δ))

theorem ae_exp_EB_eq_tiltG38 (c : BoundedCoefficients lower upper) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ * upper < lower) :
    ∀ᵐ u ∂(B.muW38 c.val),
      Real.exp (δ * (EB38 c.val u).toReal) = B.tiltG38 c.val δ (B.Φ u) := by
  filter_upwards [B.ae_muW38_Phi_mem_Omega038 c] with u hu
  have := (B.tilt_remainder_identity38 c hδ0 hδ u hu).2
  unfold tiltG38
  congr 1
  rw [this]; ring

/-- **W12 (v2 `D:eq:exacttilt`), integrability.** `e^{δ E_B}` is `μ_W`-integrable. -/
theorem tilt_integrable_W12_38 (c : BoundedCoefficients lower upper) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ * upper < lower) :
    Integrable (fun u => Real.exp (δ * (EB38 c.val u).toReal)) (B.muW38 c.val) := by
  have hmeas : AEStronglyMeasurable (fun u => Real.exp (δ * (EB38 c.val u).toReal))
      (B.muW38 c.val) :=
    (((B.measurable_tiltG38 c hδ0 hδ).comp B.measurable_Phi38).aestronglyMeasurable).congr
      ((B.ae_exp_EB_eq_tiltG38 c hδ0 hδ).mono fun u hu => hu.symm)
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun u => (Real.exp_pos _).le))]
  rw [B.tilt_lintegral_W12_38 c hδ0 hδ]
  exact ENNReal.ofReal_lt_top

/-- **W12 (v2 `D:eq:exacttilt`), real form:** `∫ e^{δ E_B} dμ_W = Z_W̃ / (Z_W D_δ)`. -/
theorem tilt_integral_W12_38 (c : BoundedCoefficients lower upper) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ * upper < lower) :
    ∫ u, Real.exp (δ * (EB38 c.val u).toReal) ∂(B.muW38 c.val) =
      B.ZW38 (tiltCoef38 c.val δ) / (B.ZW38 c.val * Dtilt38 c.val δ) := by
  have hl := coef_lower38 c
  have hadm := tiltCoef38_bounds c hδ0 hδ
  have hZ := (B.ZW38_pos_le_one lower upper c.val hl (coef_bound38 c) (coef_upper38 c)).1
  have hZ' := (B.ZW38_pos_le_one (lower - δ * upper) upper (tiltCoef38 c.val δ) hadm.1
    (fun j => (hadm.2.2 j).1) (fun j => (hadm.2.2 j).2)).1
  obtain ⟨hDpos, -⟩ := hasProd_tilt38 c hδ0 hδ
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall
    (fun u => (Real.exp_pos _).le)) (B.tilt_integrable_W12_38 c hδ0 hδ).1,
    B.tilt_lintegral_W12_38 c hδ0 hδ, ENNReal.toReal_ofReal (by positivity)]

end BirkhoffInput38

end NlsGge.Birkhoff
end
