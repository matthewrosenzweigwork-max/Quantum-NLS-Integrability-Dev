import Mathlib
import QuantumNLS.OneParticleBorn
import QuantumNLS.RootMeasureExistence
import QuantumNLS.CauchyLimitCriterion

/-!
# R-28C650F0 `prop:root-free`, free-limit clause, step (ii): `μ_{κ,u} ⇀ Σ_n |û(n)|² δ_{2πn/L}` as `κ ↓ 0`

Source: `ROOT_spectral_measure.tex`, `prop:root-free`, first clause and its proof ("expansion of eq:root-symbol and eq:root-characterization gives
`g_κ(z) = a_1(z)/(i(1−e^{izL})) + O_z(κ)`; the periodic approximate identity and Parseval identify the limiting Cauchy transform; tightness and weak
convergence follow by the same mass-one argument").

* `freeMeasure L u = Σ_n |û(n)|² δ_{2πn/L}` (`û(n) = coeff L u n`), a probability measure for unit `u` (`freeProb`);
* `hasSum_cauchy_free`, `a1_eq`: `a_1(z) = i(1−e^{izL}) G_{free}(z)` (from `OneParticleBorn.hasSum_a1_fourier`);
* `gStar_free_dist`: `|g_κ(z) − G_free(z)| ≤ 5κ/(Im z)²` on the high half-plane (from `productSymbol_approx`, `fz_taylor`, `‖e^{izL}‖ ≤ 1/16`);
* `one_add_mul_im_tendsto_prob`: no loss of mass for any probability measure (dominated convergence);
* `tendsto_free_seq` / `tendsto_muKappa_free`: the quantum-derived measures `μ_{κ,u}` converge weakly to `freeMeasure` as `κ ↓ 0`
  (via `CauchyLimitCriterion.tendsto_of_cauchy`).
No EXT-025 contract is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal

noncomputable section

namespace QuantumNLS.FreeLimit

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Fourier (coeff)
open QuantumNLS.CauchyUniqueness (cauchyTransform)
open QuantumNLS.RootMeasureComplex (HighHalf norm_exp_izL_le)
open QuantumNLS.RootMeasureConcentration (gStar gStar_spec)
open QuantumNLS.NormalizedTransfer (productSymbol orderedKernel)
open QuantumNLS.KernelDefinition (kernelProductSymbol)
open QuantumNLS.BulkResponseActual (IsLimitingRapidityMeasure)

variable {L : ℝ} [Fact (0 < L)]

/-! ### The free measure -/

/-- `Σ_n |û(n)|² δ_{2πn/L}`. -/
def freeMeasure (L : ℝ) [Fact (0 < L)] (u : L2T L) : Measure ℝ :=
  Measure.sum (fun n : ℤ => ENNReal.ofReal (‖coeff L (u : AddCircle L → ℂ) n‖ ^ 2) •
    Measure.dirac (2 * Real.pi * n / L))

theorem freeMeasure_univ (u : L2T L) (hu : ‖u‖ = 1) : freeMeasure L u Set.univ = 1 := by
  unfold freeMeasure
  rw [Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  have h := QuantumNLS.OneParticleBorn.hasSum_coeff_sq u
  rw [hu] at h
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) h.summable, h.tsum_eq]
  simp

theorem isProbability_free (u : L2T L) (hu : ‖u‖ = 1) : IsProbabilityMeasure (freeMeasure L u) :=
  ⟨freeMeasure_univ u hu⟩

/-- The free measure as a probability measure (unit `u`). -/
def freeProb (u : L2T L) (hu : ‖u‖ = 1) : ProbabilityMeasure ℝ :=
  ⟨freeMeasure L u, isProbability_free u hu⟩

theorem hasSum_cauchy_free (u : L2T L) (hu : ‖u‖ = 1) {z : ℂ} (hz : 0 < z.im) :
    HasSum (fun n : ℤ => ((‖coeff L (u : AddCircle L → ℂ) n‖ ^ 2 : ℝ) : ℂ) *
        (z - ((2 * Real.pi * n / L : ℝ) : ℂ))⁻¹)
      (cauchyTransform (freeMeasure L u) z) := by
  haveI := isProbability_free u hu
  have hint := QuantumNLS.CauchyUniqueness.integrable_cauchyKernel (freeMeasure L u) hz
  have h := hasSum_integral_measure hint
  unfold cauchyTransform
  convert h using 1
  · funext n
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (sq_nonneg _), Complex.real_smul]
  · rfl

/-- **`a_1(z) = i(1−e^{izL}) G_free(z)`.** -/
theorem a1_eq {κ : ℝ} (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {z : ℂ} (hz : 0 < z.im) :
    kernelProductSymbol (orderedKernel L 1 z) u =
      Complex.I * (1 - Complex.exp (Complex.I * z * L)) * cauchyTransform (freeMeasure L u) z := by
  have h1 := QuantumNLS.OneParticleBorn.hasSum_a1_fourier hκ u hu hz
  have h2 := (hasSum_cauchy_free u hu hz).mul_left (Complex.I * (1 - Complex.exp (Complex.I * z * L)))
  refine h1.unique ?_
  convert h2 using 1
  funext n
  rw [div_eq_mul_inv]; ring

/-- **`|g_κ(z) − G_free(z)| ≤ 5κ/η²`** for `Im z = η ≥ η₀`. -/
theorem gStar_free_dist {κ : ℝ} (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {z : ℂ} (hz : HighHalf L κ z) :
    ‖gStar L κ hκ u hu z - cauchyTransform (freeMeasure L u) z‖ ≤ 5 * κ / z.im ^ 2 := by
  have hη : 0 < z.im := by linarith [hz.1]
  obtain ⟨hg1, hg2⟩ := gStar_spec hκ u hu hz
  have h1 := QuantumNLS.RootMeasureNoLoss.productSymbol_approx hκ u hu hz
  have h2 := QuantumNLS.RootMeasureNoLoss.fz_taylor hκ hz hg1
  rw [hg2] at h2
  rw [a1_eq hκ u hu hη] at h1
  set E := Complex.exp (Complex.I * z * L) with hE
  set g := gStar L κ hκ u hu z with hg
  set G := cauchyTransform (freeMeasure L u) z with hG
  set s := productSymbol L κ u z with hs
  have hid : (κ : ℂ) * (Complex.I * (1 - E) * (g - G)) =
      (s - (1 + E) - κ * (Complex.I * (1 - E) * G)) - (s - (1 + E) - Complex.I * κ * (1 - E) * g) := by ring
  have hx : (0 : ℝ) ≤ κ / z.im := by positivity
  have hnorm : ‖(κ : ℂ) * (Complex.I * (1 - E) * (g - G))‖ ≤ 14 / 3 * (κ / z.im) ^ 2 := by
    rw [hid]
    calc _ ≤ ‖s - (1 + E) - κ * (Complex.I * (1 - E) * G)‖ + ‖s - (1 + E) - Complex.I * κ * (1 - E) * g‖ :=
          norm_sub_le _ _
      _ ≤ 8 / 3 * (κ / z.im) ^ 2 + 2 * (κ / z.im) ^ 2 := add_le_add h1 h2
      _ = 14 / 3 * (κ / z.im) ^ 2 := by ring
  have hE1 : ‖E‖ ≤ 1 / 16 := norm_exp_izL_le hz
  have h1E : 15 / 16 ≤ ‖1 - E‖ := by
    have := norm_sub_norm_le (1 : ℂ) E
    rw [norm_one] at this
    linarith
  have hlow : κ * (15 / 16) * ‖g - G‖ ≤ ‖(κ : ℂ) * (Complex.I * (1 - E) * (g - G))‖ := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hκ]
    have : κ * (15 / 16) * ‖g - G‖ ≤ κ * (‖1 - E‖ * ‖g - G‖) := by
      rw [← mul_assoc]
      gcongr
    exact this
  have hmain : κ * (15 / 16) * ‖g - G‖ ≤ κ * (15 / 16) * (5 * κ / z.im ^ 2) := by
    refine hlow.trans (hnorm.trans ?_)
    rw [div_pow]
    have hsq : (0 : ℝ) ≤ κ ^ 2 / z.im ^ 2 := by positivity
    calc 14 / 3 * (κ ^ 2 / z.im ^ 2) ≤ 75 / 16 * (κ ^ 2 / z.im ^ 2) := by nlinarith
      _ = κ * (15 / 16) * (5 * κ / z.im ^ 2) := by field_simp; ring
  exact le_of_mul_le_mul_left hmain (by positivity)

/-! ### No loss of mass for probability measures -/

theorem one_add_mul_im_eq (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {Y : ℝ} (hY : 0 < Y) :
    1 + Y * (cauchyTransform ρ (Complex.I * (Y : ℂ))).im = ∫ t : ℝ, t ^ 2 / (t ^ 2 + Y ^ 2) ∂ρ := by
  rw [QuantumNLS.CauchyLimitCriterion.im_cauchy_iY ρ hY]
  have hpos : ∀ t : ℝ, 0 < t ^ 2 + Y ^ 2 := fun t => by positivity
  have hint2 : Integrable (fun t : ℝ => -(Y / (t ^ 2 + Y ^ 2))) ρ := by
    have hc : Continuous (fun t : ℝ => -(Y / (t ^ 2 + Y ^ 2))) :=
      (continuous_const.div (by fun_prop) (fun t => (hpos t).ne')).neg
    refine Integrable.mono' (integrable_const (Y⁻¹)) hc.aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [div_le_iff₀ (hpos t)]
    have : Y⁻¹ * (t ^ 2 + Y ^ 2) ≥ Y := by
      rw [ge_iff_le, ← sub_nonneg]
      have : Y⁻¹ * (t ^ 2 + Y ^ 2) - Y = Y⁻¹ * t ^ 2 := by field_simp; ring
      rw [this]; positivity
    linarith
  have h1 : ∫ t : ℝ, (1 : ℝ) ∂ρ = 1 := by simp
  have : ∀ t : ℝ, 1 + Y * (-(Y / (t ^ 2 + Y ^ 2))) = t ^ 2 / (t ^ 2 + Y ^ 2) := by
    intro t
    have := (hpos t).ne'
    field_simp; ring
  calc 1 + Y * ∫ t : ℝ, -(Y / (t ^ 2 + Y ^ 2)) ∂ρ
      = ∫ t : ℝ, (1 + Y * (-(Y / (t ^ 2 + Y ^ 2)))) ∂ρ := by
        rw [integral_add (integrable_const 1) (hint2.const_mul Y), integral_const_mul, h1]
    _ = ∫ t : ℝ, t ^ 2 / (t ^ 2 + Y ^ 2) ∂ρ := by simp_rw [this]

theorem one_add_mul_im_tendsto_prob (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    Tendsto (fun Y : ℝ => 1 + Y * (cauchyTransform ρ (Complex.I * (Y : ℂ))).im) atTop (𝓝 0) := by
  have hlim : Tendsto (fun Y : ℝ => ∫ t : ℝ, t ^ 2 / (t ^ 2 + Y ^ 2) ∂ρ) atTop (𝓝 (∫ t : ℝ, (0 : ℝ) ∂ρ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ ?_ (integrable_const _) ?_
    · refine Eventually.of_forall fun Y => ?_
      exact (by fun_prop : Measurable fun t : ℝ => t ^ 2 / (t ^ 2 + Y ^ 2)).aestronglyMeasurable
    · filter_upwards [eventually_gt_atTop 0] with Y hY
      refine Eventually.of_forall fun t => ?_
      have hp : 0 < t ^ 2 + Y ^ 2 := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_one hp]
      nlinarith [sq_nonneg Y]
    · refine Eventually.of_forall fun t => ?_
      have h1 : Tendsto (fun Y : ℝ => t ^ 2 + Y ^ 2) atTop atTop :=
        tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)
      have h2 := (tendsto_inv_atTop_zero.comp h1).const_mul (t ^ 2)
      simpa [div_eq_mul_inv] using h2
  simp only [integral_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with Y hY
  exact (one_add_mul_im_eq ρ hY).symm

/-! ### The free limit -/

theorem tendsto_free_seq (u : L2T L) (hu : ‖u‖ = 1) (κs : ℕ → ℝ) (hlim : Tendsto κs atTop (𝓝 0))
    (hev : ∀ᶠ n in atTop, 0 < κs n) (μs : ℕ → ProbabilityMeasure ℝ)
    (hμs : ∀ n (h : 0 < κs n), IsLimitingRapidityMeasure L (κs n) h u hu (μs n)) :
    Tendsto μs atTop (𝓝 (freeProb u hu)) := by
  have hL : 0 < L := Fact.out
  set η₀ : ℝ := max 4 (Real.log 16 / L) with hη₀
  have hη0 : 0 < η₀ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  let q : ℕ → ℝ := TopologicalSpace.denseSeq ℝ
  let Y : ℕ → ℝ := fun j => η₀ + j
  have hYge : ∀ j, η₀ ≤ Y j := fun j => by
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    simp only [Y]; linarith
  have hYpos : ∀ j, 0 < Y j := fun j => lt_of_lt_of_le hη0 (hYge j)
  haveI := isProbability_free u hu
  -- pointwise convergence of the Cauchy transforms on `Im z ≥ η₀`
  have hconv : ∀ z : ℂ, η₀ ≤ z.im →
      Tendsto (fun n => cauchyTransform (μs n : Measure ℝ) z) atTop
        (𝓝 (cauchyTransform (freeMeasure L u) z)) := by
    intro z hz
    have hη : 0 < z.im := lt_of_lt_of_le hη0 hz
    have hsmall : ∀ᶠ n in atTop, 0 < κs n ∧ κs n ≤ 1 :=
      hev.and (hlim.eventually (ge_mem_nhds (by norm_num)))
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : Tendsto (fun n => 5 * κs n / z.im ^ 2) atTop (𝓝 0) := by
      have := (hlim.const_mul 5).div_const (z.im ^ 2)
      simpa using this
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hb
    filter_upwards [hsmall] with n hn
    have hH : HighHalf L (κs n) z := by
      refine ⟨by have := le_max_left 4 (Real.log 16 / L); nlinarith [hn.2], ?_⟩
      have : Real.log 16 / L ≤ z.im := (le_max_right _ _).trans hz
      rwa [div_le_iff₀ hL, mul_comm] at this
    have hc := QuantumNLS.RootMeasureExistence.cauchy_limiting_measure hn.1 u hu (hμs n hn.1) hH
    rw [hc]
    exact gStar_free_dist hn.1 u hu hH
  have hmassY : Tendsto (fun j : ℕ => 1 + Y j * (cauchyTransform (freeMeasure L u)
      (Complex.I * (Y j : ℂ))).im) atTop (𝓝 0) :=
    (one_add_mul_im_tendsto_prob (freeMeasure L u)).comp
      (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop)
  exact QuantumNLS.CauchyLimitCriterion.tendsto_of_cauchy (η₀ := η₀) (q := q)
    (g := fun z => cauchyTransform (freeMeasure L u) z) (Y := Y) hη0
    (TopologicalSpace.denseRange_denseSeq ℝ) μs hYpos (freeProb u hu)
    (fun k => rfl) hmassY
    (fun j => hconv _ (by simpa using hYge j))
    (fun k => hconv _ (by simp))

/-- The chosen quantum-derived limiting measure `μ_{κ,u}` for `κ > 0` (the free measure for `κ ≤ 0`, a convention not used). -/
def muKappa (u : L2T L) (hu : ‖u‖ = 1) (κ : ℝ) : ProbabilityMeasure ℝ :=
  if h : 0 < κ then Classical.choose (QuantumNLS.RootMeasureExistence.exists_limiting_measure h u hu)
  else freeProb u hu

theorem muKappa_spec (u : L2T L) (hu : ‖u‖ = 1) {κ : ℝ} (h : 0 < κ) :
    IsLimitingRapidityMeasure L κ h u hu (muKappa u hu κ) := by
  unfold muKappa
  rw [dif_pos h]
  exact Classical.choose_spec (QuantumNLS.RootMeasureExistence.exists_limiting_measure h u hu)

/-- **Free limit (`prop:root-free`, first clause)**: `μ_{κ,u} ⇀ Σ_n |û(n)|² δ_{2πn/L}` as `κ ↓ 0`. -/
theorem tendsto_muKappa_free (u : L2T L) (hu : ‖u‖ = 1) :
    Tendsto (muKappa u hu) (𝓝[>] 0) (𝓝 (freeProb u hu)) := by
  rw [tendsto_iff_seq_tendsto]
  intro x hx
  rw [tendsto_nhdsWithin_iff] at hx
  exact tendsto_free_seq u hu x hx.1 (hx.2.mono fun n hn => hn) (fun n => muKappa u hu (x n))
    (fun n h => muKappa_spec u hu h)

end QuantumNLS.FreeLimit

#print axioms QuantumNLS.FreeLimit.freeMeasure_univ
#print axioms QuantumNLS.FreeLimit.hasSum_cauchy_free
#print axioms QuantumNLS.FreeLimit.a1_eq
#print axioms QuantumNLS.FreeLimit.gStar_free_dist
#print axioms QuantumNLS.FreeLimit.one_add_mul_im_tendsto_prob
#print axioms QuantumNLS.FreeLimit.tendsto_free_seq
#print axioms QuantumNLS.FreeLimit.tendsto_muKappa_free
