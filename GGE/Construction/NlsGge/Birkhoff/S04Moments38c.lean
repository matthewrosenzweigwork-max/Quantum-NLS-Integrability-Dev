import NlsGge.Birkhoff.S04Moments38

/-! # S04.06 (part 1): Gaussian exponential moments of the sequence Sobolev norms (Birkhoff-free)

v2 l.434-440: for each `m` choose `δ > 0` with `δ sup_n ⟨n⟩^{2m}/a_n < 1/2`; then
`E_{γ_W} e^{δ‖z‖²_{h^m}} = ∏_n (1 - δ⟨n⟩^{2m}/a_n)^{-1} < ∞` (independence and monotone convergence).

Declarations: `exp_moment_sobolev38` (the product formula as the limit of the partial products
over `[-N,N]`, equal to the extended-real integral, with the finiteness bound; v2 writes the
infinite product), `integrable_hnorm_pow38` (all polynomial moments of `‖z‖_{h^m}`), then
(B-dependent, field `inverse_polynomial` = Molnár Thm 1 as packaged in `BirkhoffTop38`)
`exists_cleanTinvC_bound38`, `integrable_norm_cleanTinvC_pow38`, `muHatW38_le`
(`dμ̂_W/dγ_W ≤ Z_W⁻¹`) and `integrable_muW38_sobolev_pow`: `‖u‖_{H^m}^p` is `μ_W`-integrable for
all `m, p ∈ ℕ` (S04.06, physical Sobolev moments).
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.Sobolev38 Filter Topology
open scoped ENNReal BoundedContinuousFunction

/-- `‖z‖²_{h^m} = ∑ ⟨n⟩^{2m}|z_n|²` as a real number (junk `0` if the extended sum is infinite;
it is used only on the a.s. finite set). -/
def sobEnergy38 (m : ℕ) (z : ℤ → ℂ) : ℝ := (sequenceEnergy (sobolevWeight38 m) z).toReal

theorem measurable_sobEnergy38 (m : ℕ) : Measurable (sobEnergy38 m) :=
  (measurable_sequenceEnergy _).ennreal_toReal

theorem sobEnergy38_nonneg (m : ℕ) (z : ℤ → ℂ) : 0 ≤ sobEnergy38 m z := ENNReal.toReal_nonneg

theorem sobEnergy38_eq_tsum (m : ℕ) {z : ℤ → ℂ}
    (hz : Summable (fun n : ℤ => sobolevWeight38 m n * ‖z n‖ ^ 2)) :
    sobEnergy38 m z = ∑' n : ℤ, sobolevWeight38 m n * ‖z n‖ ^ 2 := by
  unfold sobEnergy38 sequenceEnergy
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun n => mul_nonneg (sobolevWeight38_nonneg m n) (sq_nonneg _)) hz,
    ENNReal.toReal_ofReal (tsum_nonneg (fun n => mul_nonneg (sobolevWeight38_nonneg m n) (sq_nonneg _)))]

/-- Single-coordinate exponential moment of the proper complex Gaussian of rate `a`. -/
theorem integrable_exp_complexGaussian38 (a b : ℝ) (ha : 0 < a) (hba : b < a) :
    Integrable (fun y : ℂ => Real.exp (b * ‖y‖ ^ 2)) (complexGaussian a) ∧
    ∫ y : ℂ, Real.exp (b * ‖y‖ ^ 2) ∂(complexGaussian a) = a / (a - b) := by
  have hab : 0 < a - b := by linarith
  have hm : Measurable (fun y : ℂ => ENNReal.ofReal ((a / Real.pi) * Real.exp (-a * ‖y‖ ^ 2))) := by
    fun_prop
  have hconv : ∀ y : ℂ, (a / Real.pi) * Real.exp (-a * ‖y‖ ^ 2) * Real.exp (b * ‖y‖ ^ 2) =
      (a / Real.pi) * Real.exp (-(a - b) * ‖y‖ ^ 2) := fun y => by
    rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hpos : ∀ y : ℂ, 0 ≤ (a / Real.pi) * Real.exp (-a * ‖y‖ ^ 2) := fun y =>
    mul_nonneg (div_nonneg ha.le Real.pi_pos.le) (Real.exp_pos _).le
  rw [complexGaussian_density a ha]
  refine ⟨?_, ?_⟩
  · rw [integrable_withDensity_iff_integrable_smul' hm (Filter.Eventually.of_forall
      (fun _ => ENNReal.ofReal_lt_top))]
    have : (fun y : ℂ => (ENNReal.ofReal ((a / Real.pi) * Real.exp (-a * ‖y‖ ^ 2))).toReal •
        Real.exp (b * ‖y‖ ^ 2)) = fun y => (a / Real.pi) * Real.exp (-(a - b) * ‖y‖ ^ 2) := by
      funext y
      simp only [smul_eq_mul]
      rw [ENNReal.toReal_ofReal (hpos y), hconv]
    rw [this]
    exact (integrable_complexGaussianKernel (a - b) hab).const_mul _
  · rw [integral_withDensity_eq_integral_toReal_smul hm (Filter.Eventually.of_forall
      (fun _ => ENNReal.ofReal_lt_top))]
    have : (fun y : ℂ => (ENNReal.ofReal ((a / Real.pi) * Real.exp (-a * ‖y‖ ^ 2))).toReal •
        Real.exp (b * ‖y‖ ^ 2)) = fun y => (a / Real.pi) * Real.exp (-(a - b) * ‖y‖ ^ 2) := by
      funext y
      simp only [smul_eq_mul]
      rw [ENNReal.toReal_ofReal (hpos y), hconv]
    rw [this, integral_const_mul, integral_complexGaussianKernel (a - b) hab]
    field_simp


/-- **Independence (finite coordinates).** For finitely many coordinates `s` and `b_n < a_n`,
`E_{γ_W} e^{∑_{n∈s} b_n |z_n|²} = ∏_{n∈s} a_n/(a_n - b_n)`. -/
theorem lintegral_exp_energy_finset38 (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) (s : Finset ℤ) (b : ℤ → ℝ)
    (hb : ∀ n, b n < fullWeightRate c n) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (∑ n ∈ s, b n * ‖z n‖ ^ 2)) ∂(fullWeightSequenceGaussian c) =
      ENNReal.ofReal (∏ n ∈ s, fullWeightRate c n / (fullWeightRate c n - b n)) := by
  have hq := fun n => fullWeightRate_pos lower upper c hlower hbound hupper n
  set G : (s → ℂ) → ℝ := fun y => ∏ i : s, Real.exp (b i * ‖y i‖ ^ 2) with hG
  have hGm : Measurable G := by
    refine Finset.measurable_prod _ (fun i _ => ?_)
    exact Real.measurable_exp.comp ((measurable_pi_apply i).norm.pow_const 2 |>.const_mul _)
  have hGc : ∀ z : ℤ → ℂ, Real.exp (∑ n ∈ s, b n * ‖z n‖ ^ 2) = G (s.restrict z) := by
    intro z
    simp only [hG, Finset.restrict]
    rw [Real.exp_sum, ← Finset.prod_coe_sort s]
  simp_rw [hGc]
  have hlm := lintegral_map (μ := fullWeightSequenceGaussian c) (f := fun y => ENNReal.ofReal (G y))
    (ENNReal.measurable_ofReal.comp hGm) (Finset.measurable_restrict s)
  rw [← hlm]
  have hmap : (fullWeightSequenceGaussian c).map s.restrict = Measure.pi (fun i : s =>
      complexGaussian (fullWeightRate c i)) := gammaΛ38_eq_map c s
  rw [hmap]
  have hint : Integrable G (Measure.pi (fun i : s => complexGaussian (fullWeightRate c i))) :=
    Integrable.fintype_prod (fun i : s => (integrable_exp_complexGaussian38 _ _ (hq (i : ℤ)) (hb (i : ℤ))).1)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall
    (fun y => Finset.prod_nonneg (fun i _ => (Real.exp_pos _).le)))]
  congr 1
  rw [hG, integral_fintype_prod_eq_prod
    (μ := fun i : s => complexGaussian (fullWeightRate c i))
    (fun (i : s) (y : ℂ) => Real.exp (b i * ‖y‖ ^ 2))]
  rw [← Finset.prod_coe_sort s]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  exact (integrable_exp_complexGaussian38 _ _ (hq (i : ℤ)) (hb (i : ℤ))).2


theorem inv_one_sub_le_exp38 {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) : (1 - x)⁻¹ ≤ Real.exp (2 * x) := by
  have hx : 0 < 1 - x := by linarith
  have h2 : (1 - x)⁻¹ ≤ 1 + 2 * x := by
    rw [inv_le_iff_one_le_mul₀' hx]
    nlinarith
  exact h2.trans (by linarith [Real.add_one_le_exp (2 * x)])

theorem summable_sobolevWeight_iff38 (m : ℕ) (z : ℤ → ℂ) :
    Summable (fun n : ℤ => sobolevWeight38 m n * ‖z n‖ ^ 2) ↔ SobolevSquareSummable (m : ℝ) z := by
  unfold SobolevSquareSummable sobolevWeight38
  simp only [Real.rpow_eq_pow]

/-- **S04.06 (Gaussian exponential moment, v2 l.435-440).** If `δ > 0` and
`δ ⟨n⟩^{2m}/a_n ≤ 1/2` for all `n` (v2 requires `δ sup_n ⟨n⟩^{2m}/a_n < 1/2`), then
`E_{γ_W} e^{δ‖z‖²_{h^m}}` is the limit of the partial products `∏_{|n|≤N}(1-δ⟨n⟩^{2m}/a_n)^{-1}`
(independence plus monotone convergence) and is finite, at most `exp(2δ ∑ ⟨n⟩^{2m}/a_n)`. -/
theorem exp_moment_sobolev38 (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) (m : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hδ2 : ∀ n : ℤ, δ * sobolevWeight38 m n / fullWeightRate c n ≤ 1 / 2) :
    Tendsto (fun N : ℕ => ENNReal.ofReal (∏ n ∈ Finset.Icc (-(N : ℤ)) N,
        (1 - δ * sobolevWeight38 m n / fullWeightRate c n)⁻¹)) atTop
      (𝓝 (∫⁻ z, ENNReal.ofReal (Real.exp (δ * sobEnergy38 m z)) ∂(fullWeightSequenceGaussian c))) ∧
    (∫⁻ z, ENNReal.ofReal (Real.exp (δ * sobEnergy38 m z)) ∂(fullWeightSequenceGaussian c)) ≤
      ENNReal.ofReal (Real.exp (2 * ∑' n : ℤ, δ * sobolevWeight38 m n / fullWeightRate c n)) ∧
    (∫⁻ z, ENNReal.ofReal (Real.exp (δ * sobEnergy38 m z)) ∂(fullWeightSequenceGaussian c)) ≠ ⊤ := by
  have hq := fun n => fullWeightRate_pos lower upper c hlower hbound hupper n
  have hw := sobolevWeight38_nonneg m
  set a := fullWeightRate c with ha
  set x : ℤ → ℝ := fun n => δ * sobolevWeight38 m n / a n with hx
  have hx0 : ∀ n, 0 ≤ x n := fun n => div_nonneg (mul_nonneg hδ.le (hw n)) (hq n).le
  have hxs : Summable x := by
    have := (summable_fullWeightRate_invSobolev lower upper c hlower hbound hupper m).mul_left δ
    refine this.congr (fun n => ?_)
    simp only [hx, sobolevWeight38, Real.rpow_eq_pow]
    ring
  set b : ℤ → ℝ := fun n => δ * sobolevWeight38 m n with hb
  have hba : ∀ n, b n < a n := fun n => by
    have h := hδ2 n
    rw [div_le_iff₀ (hq n)] at h
    simp only [hb]; linarith [hq n]
  set f : ℕ → (ℤ → ℂ) → ℝ≥0∞ := fun N z =>
    ENNReal.ofReal (Real.exp (∑ n ∈ Finset.Icc (-(N : ℤ)) N, b n * ‖z n‖ ^ 2)) with hf
  have hfint : ∀ N : ℕ, ∫⁻ z, f N z ∂(fullWeightSequenceGaussian c) =
      ENNReal.ofReal (∏ n ∈ Finset.Icc (-(N : ℤ)) N, (1 - x n)⁻¹) := by
    intro N
    rw [lintegral_exp_energy_finset38 lower upper c hlower hbound hupper _ b hba]
    congr 1
    refine Finset.prod_congr rfl (fun n _ => ?_)
    have := (hq n).ne'
    have h2 : a n - b n ≠ 0 := (sub_pos.2 (hba n)).ne'
    simp only [hx, hb]
    field_simp
    rfl
  have hfm : ∀ N, Measurable (f N) := fun N => by
    refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)
    exact Finset.measurable_sum _ (fun n _ => ((measurable_pi_apply n).norm.pow_const 2).const_mul _)
  have hmono : ∀ z : ℤ → ℂ, Monotone (fun N => f N z) := by
    intro z N M hNM
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc (by omega)
      (by exact_mod_cast hNM)) (fun n _ _ => ?_)
    exact mul_nonneg (mul_nonneg hδ.le (hw n)) (sq_nonneg _)
  have hlim : ∀ᵐ z ∂(fullWeightSequenceGaussian c), Tendsto (fun N => f N z) atTop
      (𝓝 (ENNReal.ofReal (Real.exp (δ * sobEnergy38 m z)))) := by
    filter_upwards [ae_fullWeightSequenceGaussian_sobolev lower upper c hlower hbound hupper m]
      with z hz
    have hs := (summable_sobolevWeight_iff38 m z).2 hz
    have hsum : HasSum (fun n : ℤ => b n * ‖z n‖ ^ 2)
        (δ * ∑' n : ℤ, sobolevWeight38 m n * ‖z n‖ ^ 2) := by
      have := hs.hasSum.mul_left δ
      convert this using 1
      funext n
      simp only [hb]
      ring
    have h1 : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) N, b n * ‖z n‖ ^ 2) atTop
        (𝓝 (δ * sobEnergy38 m z)) := by
      rw [sobEnergy38_eq_tsum m hs]
      exact hsum.comp isExhaustion_stdExh38.tendsto_atTop
    exact (ENNReal.continuous_ofReal.tendsto _).comp ((Real.continuous_exp.tendsto _).comp h1)
  have hT := lintegral_tendsto_of_tendsto_of_monotone (μ := fullWeightSequenceGaussian c)
    (fun N => (hfm N).aemeasurable) (Filter.Eventually.of_forall hmono) hlim
  have hT' : Tendsto (fun N : ℕ => ENNReal.ofReal (∏ n ∈ Finset.Icc (-(N : ℤ)) N, (1 - x n)⁻¹))
      atTop (𝓝 (∫⁻ z, ENNReal.ofReal (Real.exp (δ * sobEnergy38 m z)) ∂(fullWeightSequenceGaussian c))) :=
    hT.congr (fun N => hfint N)
  have hle : ∀ N : ℕ, ENNReal.ofReal (∏ n ∈ Finset.Icc (-(N : ℤ)) N, (1 - x n)⁻¹) ≤
      ENNReal.ofReal (Real.exp (2 * ∑' n : ℤ, x n)) := by
    intro N
    refine ENNReal.ofReal_le_ofReal ?_
    calc ∏ n ∈ Finset.Icc (-(N : ℤ)) N, (1 - x n)⁻¹
        ≤ ∏ n ∈ Finset.Icc (-(N : ℤ)) N, Real.exp (2 * x n) :=
          Finset.prod_le_prod₀ (fun n _ => inv_nonneg.2 (by
              have : x n ≤ 1 / 2 := hδ2 n
              linarith))
            (fun n _ => inv_one_sub_le_exp38 (hx0 n) (hδ2 n))
      _ = Real.exp (2 * ∑ n ∈ Finset.Icc (-(N : ℤ)) N, x n) := by
          rw [← Real.exp_sum, Finset.mul_sum]
      _ ≤ _ := Real.exp_le_exp.2 (by
          have := hxs.sum_le_tsum (Finset.Icc (-(N : ℤ)) N) (fun n _ => hx0 n)
          linarith)
  have hlim_le := le_of_tendsto' hT' hle
  refine ⟨hT', hlim_le, ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlim_le⟩


/-- The `h^m` norm of a sequence (`√∑⟨n⟩^{2m}|z_n|²`), junk `0` off the a.s. finite set. -/
def hnorm38 (m : ℕ) (z : ℤ → ℂ) : ℝ := Real.sqrt (sobEnergy38 m z)

theorem measurable_hnorm38 (m : ℕ) : Measurable (hnorm38 m) :=
  Real.continuous_sqrt.measurable.comp (measurable_sobEnergy38 m)

theorem hnorm38_nonneg (m : ℕ) (z : ℤ → ℂ) : 0 ≤ hnorm38 m z := Real.sqrt_nonneg _

theorem exists_delta38 (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) (m : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℤ, δ * sobolevWeight38 m n / fullWeightRate c n ≤ 1 / 2 := by
  have hq := fun n => fullWeightRate_pos lower upper c hlower hbound hupper n
  have hsum : Summable (fun n : ℤ => sobolevWeight38 m n / fullWeightRate c n) :=
    (gaussian_sobolev_expectation38 lower upper c hlower hbound hupper m).1
  obtain ⟨M, hM⟩ := hsum.tendsto_cofinite_zero.bddAbove_range_of_cofinite
  have hM' : ∀ n, sobolevWeight38 m n / fullWeightRate c n ≤ M := fun n => hM ⟨n, rfl⟩
  have hM0 : 0 ≤ M := (div_nonneg (sobolevWeight38_nonneg m 0) (hq 0).le).trans (hM' 0)
  refine ⟨1 / (2 * (M + 1)), by positivity, fun n => ?_⟩
  have h1 : 1 / (2 * (M + 1)) * sobolevWeight38 m n / fullWeightRate c n =
      1 / (2 * (M + 1)) * (sobolevWeight38 m n / fullWeightRate c n) := by ring
  rw [h1]
  calc 1 / (2 * (M + 1)) * (sobolevWeight38 m n / fullWeightRate c n)
      ≤ 1 / (2 * (M + 1)) * M :=
        mul_le_mul_of_nonneg_left (hM' n) (by positivity)
    _ ≤ 1 / 2 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith

theorem integrable_exp_sobEnergy38 (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) (m : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hδ2 : ∀ n : ℤ, δ * sobolevWeight38 m n / fullWeightRate c n ≤ 1 / 2) :
    Integrable (fun z => Real.exp (δ * sobEnergy38 m z)) (fullWeightSequenceGaussian c) := by
  have h := (exp_moment_sobolev38 lower upper c hlower hbound hupper m δ hδ hδ2).2.2
  refine ⟨(Real.measurable_exp.comp ((measurable_sobEnergy38 m).const_mul δ)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun z => (Real.exp_pos _).le))]
  exact lt_top_iff_ne_top.2 h

theorem pow_one_add_le38 (t : ℝ) (ht : 0 ≤ t) (k : ℕ) :
    (1 + t) ^ k ≤ 2 ^ k * (1 + (t ^ 2) ^ k) := by
  rw [← pow_mul]
  have h1 : (1 + t) ^ k ≤ (2 * max 1 t) ^ k :=
    pow_le_pow_left₀ (by positivity) (by
      rcases le_total 1 t with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith) k
  refine h1.trans ?_
  rw [mul_pow]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rcases le_total 1 t with h | h
  · rw [max_eq_right h]
    have : t ^ k ≤ t ^ (2 * k) := pow_le_pow_right₀ h (by omega)
    linarith [pow_nonneg ht (2 * k)]
  · rw [max_eq_left h, one_pow]
    linarith [pow_nonneg ht (2 * k)]

/-- **S04.06 (Gaussian polynomial moments).** `(1 + ‖z‖_{h^m})^k` is `γ_W`-integrable for all
`m, k` (all sequence Sobolev norms have moments of all finite orders). -/
theorem integrable_hnorm_pow38 (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) (m k : ℕ) :
    Integrable (fun z => (1 + hnorm38 m z) ^ k) (fullWeightSequenceGaussian c) := by
  obtain ⟨δ, hδ, hδ2⟩ := exists_delta38 lower upper c hlower hbound hupper m
  have hI := integrable_exp_sobEnergy38 lower upper c hlower hbound hupper m δ hδ hδ2
  have hg : Integrable (fun z => (2 : ℝ) ^ k * (1 + ((k.factorial : ℝ) * (δ⁻¹) ^ k) *
      Real.exp (δ * sobEnergy38 m z))) (fullWeightSequenceGaussian c) :=
    ((integrable_const (1 : ℝ)).add (hI.const_mul ((k.factorial : ℝ) * (δ⁻¹) ^ k))).const_mul _
  refine hg.mono' ((measurable_const.add (measurable_hnorm38 m)).pow_const k).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => ?_))
  have hE := sobEnergy38_nonneg m z
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by linarith [hnorm38_nonneg m z]) _)]
  refine (pow_one_add_le38 _ (hnorm38_nonneg m z) k).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hsq : hnorm38 m z ^ 2 = sobEnergy38 m z := Real.sq_sqrt hE
  rw [hsq]
  have h1 := Real.pow_div_factorial_le_exp (δ * sobEnergy38 m z) (by positivity) k
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  rw [div_le_iff₀ hf, mul_pow] at h1
  have hδk : 0 < δ ^ k := by positivity
  have h2 : sobEnergy38 m z ^ k ≤ (k.factorial : ℝ) * (δ⁻¹) ^ k * Real.exp (δ * sobEnergy38 m z) := by
    calc sobEnergy38 m z ^ k = (δ ^ k)⁻¹ * (δ ^ k * sobEnergy38 m z ^ k) := by field_simp
      _ ≤ (δ ^ k)⁻¹ * (Real.exp (δ * sobEnergy38 m z) * (k.factorial : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (k.factorial : ℝ) * (δ⁻¹) ^ k * Real.exp (δ * sobEnergy38 m z) := by
          rw [inv_pow]; ring
  linarith


/-! ## Transfer to physical Sobolev norms through `Φ⁻¹` (Molnár polynomial bound) and to `μ_W` -/

theorem norm_carrierMk_eq_hnorm38 (m : ℕ) (z : ℤ → ℂ) (hz : z ∈ seqSobolev38 (m : ℝ)) :
    ‖carrierMk38 (m : ℝ) z hz‖ = hnorm38 m z := by
  have h := carrier_hasSum_norm_sq38 (m : ℝ) (carrierMk38 (m : ℝ) z hz)
  have hs : Summable (fun n : ℤ => sobolevWeight38 m n * ‖z n‖ ^ 2) := h.summable
  have h2 : sobEnergy38 m z = ‖carrierMk38 (m : ℝ) z hz‖ ^ 2 := by
    rw [sobEnergy38_eq_tsum m hs]
    exact h.tsum_eq
  unfold hnorm38
  rw [h2, Real.sqrt_sq (norm_nonneg _)]

theorem norm_carrierMk_mono38 {r s : ℝ} (hrs : r ≤ s) (y : ℤ → ℂ) (hy : y ∈ seqSobolev38 s) :
    ‖carrierMk38 r y (seqSobolev38_mono hrs hy)‖ ≤ ‖carrierMk38 s y hy‖ := by
  have h1 := carrier_hasSum_norm_sq38 r (carrierMk38 r y (seqSobolev38_mono hrs hy))
  have h2 := carrier_hasSum_norm_sq38 s (carrierMk38 s y hy)
  simp only [carrierCoe38_mk] at h1 h2
  have : ‖carrierMk38 r y (seqSobolev38_mono hrs hy)‖ ^ 2 ≤ ‖carrierMk38 s y hy‖ ^ 2 :=
    hasSum_le (fun n => mul_le_mul_of_nonneg_right (sobolevModeWeight_mono hrs n) (sq_nonneg _)) h1 h2
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this

namespace BirkhoffTop38

variable (B : BirkhoffTop38)

/-- **Molnár transfer (field `inverse_polynomial`).** For `m ≥ 1` there are `C ≥ 0`, `d` with
`‖T⁻¹ z‖_{h^m} ≤ C (1 + ‖z‖_{h^m})^d` for every `z ∈ h^m`, in the cleaned form on sequences. -/
theorem exists_cleanTinvC_bound38 (hM : BirkhoffMolnar38 B) (m : ℕ) (hm : 1 ≤ m) :
    ∃ (C : ℝ) (d : ℕ), 0 ≤ C ∧ ∀ z : ℤ → ℂ, z ∈ seqSobolev38 (m : ℝ) →
      ‖B.cleanTinvC m z‖ ≤ C * (1 + hnorm38 m z) ^ d := by
  obtain ⟨C, d, hCd⟩ := hM.inverse_polynomial m hm
  have hC : 0 ≤ C := by
    have := hCd 0
    have h2 : 0 ≤ ‖B.TinvC m 0‖ := norm_nonneg _
    simp only [norm_zero, add_zero, one_pow, mul_one] at this
    linarith
  refine ⟨C, d, hC, fun z hz => ?_⟩
  rw [B.cleanTinvC_of_mem m z hz, ← norm_carrierMk_eq_hnorm38 m z hz]
  exact hCd _

/-- For `z ∈ h^{m+1}`: `‖T⁻¹ z‖_{h^m} ≤ ‖T⁻¹ z‖_{h^{m+1}}`. -/
theorem norm_cleanTinvC_mono38 (m : ℕ) (z : ℤ → ℂ) (hz : z ∈ seqSobolev38 ((m + 1 : ℕ) : ℝ)) :
    ‖B.cleanTinvC m z‖ ≤ ‖B.cleanTinvC (m + 1) z‖ := by
  have hzm : z ∈ seqSobolev38 (m : ℝ) :=
    seqSobolev38_mono (by exact_mod_cast Nat.le_succ m) hz
  have hT : B.Tinv z ∈ seqSobolev38 ((m + 1 : ℕ) : ℝ) := B.mapsTo_Tinv (m + 1) z hz
  rw [B.cleanTinvC_of_mem m z hzm, B.cleanTinvC_of_mem (m + 1) z hz]
  have := norm_carrierMk_mono38 (r := (m : ℝ)) (s := ((m + 1 : ℕ) : ℝ))
    (by exact_mod_cast Nat.le_succ m) (B.Tinv z) hT
  have e1 : ‖B.TinvC m (carrierMk38 (m : ℝ) z hzm)‖ =
      ‖carrierMk38 (m : ℝ) (B.Tinv z) (seqSobolev38_mono (by exact_mod_cast Nat.le_succ m) hT)‖ :=
    congrArg norm (carrierExt38 rfl)
  have e2 : ‖B.TinvC (m + 1) (carrierMk38 ((m + 1 : ℕ) : ℝ) z hz)‖ =
      ‖carrierMk38 ((m + 1 : ℕ) : ℝ) (B.Tinv z) hT‖ := congrArg norm (carrierExt38 rfl)
  rw [e1, e2]
  exact this

section Moments

variable (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
  (hupper : ∀ j : ℕ, c j ≤ upper)

include hlower hbound hupper

/-- Moments of `‖Φ⁻¹ z‖_{H^m}` under the Gaussian `γ_W`, for every `m` and every power. -/
theorem integrable_norm_cleanTinvC_pow38 (hM : BirkhoffMolnar38 B) (m p : ℕ) :
    Integrable (fun z => ‖B.cleanTinvC m z‖ ^ p) (fullWeightSequenceGaussian c) := by
  let _ : MeasurableSpace (SobolevCarrier38 (m : ℝ)) := borel _
  have : BorelSpace (SobolevCarrier38 (m : ℝ)) := ⟨rfl⟩
  obtain ⟨C, d, hC, hCd⟩ := B.exists_cleanTinvC_bound38 hM (m + 1) (by omega)
  have hg := (integrable_hnorm_pow38 lower upper c hlower hbound hupper (m + 1) (d * p)).const_mul (C ^ p)
  refine hg.mono' (((B.measurable_cleanTinvC m).norm).pow_const p).aestronglyMeasurable ?_
  filter_upwards [ae_mem_Omega038 lower upper c hlower hbound hupper] with z hz
  have hz1 : z ∈ seqSobolev38 ((m + 1 : ℕ) : ℝ) := mem_seqSobolev38_of_Omega038 c hz (m + 1)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  calc ‖B.cleanTinvC m z‖ ^ p ≤ (C * (1 + hnorm38 (m + 1) z) ^ d) ^ p :=
        pow_le_pow_left₀ (norm_nonneg _) ((B.norm_cleanTinvC_mono38 m z hz1).trans (hCd z hz1)) p
    _ = C ^ p * (1 + hnorm38 (m + 1) z) ^ (d * p) := by rw [mul_pow, ← pow_mul]

/-- `μ̂_W ≤ Z_W⁻¹ γ_W` (the density of `μ̂_W` is at most `Z_W⁻¹`, v2 l.442). -/
theorem muHatW38_le : B.muHatW38 c ≤ ENNReal.ofReal (1 / B.ZW38 c) • fullWeightSequenceGaussian c := by
  obtain ⟨hZ, -⟩ := B.ZW38_pos_le_one lower upper c hlower hbound hupper
  rw [← withDensity_const]
  unfold muHatW38
  refine withDensity_mono (Filter.Eventually.of_forall (fun z => ?_))
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_div_iff₀ hZ hZ]
  nlinarith [B.exp_neg_Rbar38_le_one lower upper c hlower hbound hupper z]

/-- **S04.06 (v2 l.440-443).** For every `m, p ∈ ℕ`, `‖u‖_{H^m}^p` is `μ_W`-integrable
(`H^m` through the isometry `𝓕 : H^m → h^m`, see `norm_physH38`). Uses field `inverse_polynomial`,
the Gaussian moments, and the density bound `dμ̂_W/dγ_W ≤ Z_W⁻¹`. -/
theorem integrable_muW38_sobolev_pow (hM : BirkhoffMolnar38 B) (m p : ℕ) :
    Integrable (fun u : PhysicalL2 => ‖physH38 m u‖ ^ p) (B.muW38 c) := by
  let _ : MeasurableSpace (SobolevCarrier38 (m : ℝ)) := borel _
  have : BorelSpace (SobolevCarrier38 (m : ℝ)) := ⟨rfl⟩
  have hmeas : Measurable (fun u : PhysicalL2 => ‖physH38 m u‖ ^ p) :=
    ((measurable_physH38 m).norm).pow_const p
  unfold muW38
  rw [integrable_map_measure hmeas.aestronglyMeasurable B.measurable_cleanΦinv.aemeasurable]
  have h1 : Integrable (fun z => ‖B.cleanTinvC m z‖ ^ p) (fullWeightSequenceGaussian c) :=
    B.integrable_norm_cleanTinvC_pow38 lower upper c hlower hbound hupper hM m p
  have h2 := (h1.smul_measure (c := ENNReal.ofReal (1 / B.ZW38 c)) ENNReal.ofReal_ne_top)
  refine (h2.mono_measure (B.muHatW38_le lower upper c hlower hbound hupper)).congr ?_
  exact Filter.Eventually.of_forall (fun z => by simp only [Function.comp, physH38_cleanΦinv])

end Moments

end BirkhoffTop38

end NlsGge.Birkhoff
