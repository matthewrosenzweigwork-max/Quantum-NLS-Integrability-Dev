import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB1L4Dense

/-! # Track B, step B1: the dual estimate `L^{4/3} → X^{0,-a}` on the dense class

Dense class (as in `PdeB1L4Dense`): a finite set `S ⊂ ℤ` and time-side Schwartz functions `f_k`
(`f_k = 0` off `S`); the forcing is `F(t,x) = Σ_{k∈S} f_k(t) e^{2πikx}`. With `θ_k = 𝓕⁻ f_k`
(Mathlib convention) the `X^{0,-a}` norm (squared, `a = 13/32`, same normalization as
`denseNormSq`) is
`dualNormSq f = Σ_k ∫ ⟨-2πξ + (2πk)²⟩^{-2a} |θ_k(ξ)|² dξ`.

Main result `dense_dual_bound`: one finite constant `C` with
`dualNormSq f ≤ C · (∫_ℝ ∫_𝕋 |F|^{4/3})^{3/2}` for every dense-class forcing, i.e.
`‖F‖_{X^{0,-a}} ≤ C' ‖F‖_{L^{4/3}(ℝ×𝕋)}`.

Proof (duality with an explicit extremizer, no density argument): the test field `G` has modes
`g_k = 𝓕(w_k θ_k)` with the real weight `w_k(ξ) = ⟨-2πξ + (2πk)²⟩^{-2a}`; `w_k` has temperate
growth, so `g_k` is Schwartz (`smulLeftCLM`). Torus orthogonality and Schwartz Plancherel give
`∫∫ conj(G) F = Σ_k ∫ w_k |θ_k|² = dualNormSq f`, and `denseNormSq g = dualNormSq f`. Hölder
`(4/3, 4)` on `volume × Haar` and `dense_L4_bound` give `N ≤ ‖F‖_{4/3} (K N²)^{1/4}`; `N < ∞`
because `N` is the norm of a complex number, hence `N ≤ K^{1/2} ‖F‖²_{4/3}`.

Gap G2 (precise form): the estimate is proved for dense-class forcing only, where the time
transform is the Schwartz transform. For general `F ∈ L^{4/3}` the `X^{0,-a}` norm is never used:
the density step is carried out at the level of the final short-time Duhamel estimate
(PHASE0_REPORT §9).
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.ALLS.PdeB

open MeasureTheory SchwartzMap FourierTransform AddCircle
open scoped ENNReal ComplexConjugate

/-! ### Torus orthogonality -/

/-- Fourier coefficients of a trigonometric polynomial. -/
theorem fourierCoeff_torusPoly (S : Finset ℤ) (a : ℤ → ℂ) (ha : ∀ k ∉ S, a k = 0) (m : ℤ) :
    fourierCoeff (torusPoly S a) m = a m := by
  have hint : ∀ (n : ℤ) (c : ℂ), Integrable (⇑(c • (fourier n : C(AddCircle (1 : ℝ), ℂ))))
      haarAddCircle := fun n c =>
    (c • (fourier n : C(AddCircle (1 : ℝ), ℂ))).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [torusPoly, ContinuousMap.coe_sum, fourierCoeff.sum _ _ fun j _ => hint _ _,
    Finset.sum_apply]
  have h2 : ∀ j ∈ S, fourierCoeff (⇑(a j • (fourier j : C(AddCircle (1 : ℝ), ℂ)))) m
      = if j = m then a j else 0 := by
    intro j _
    rw [ContinuousMap.coe_smul, fourierCoeff.const_smul, fourierCoeff_fourier]
    by_cases hj : j = m
    · subst hj
      simp
    · simp [Ne.symm hj, hj]
  rw [Finset.sum_congr rfl h2, Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [ha _ hm]

/-- Torus orthogonality: `∫_𝕋 conj(Σ_S b_k e_k) (Σ_S a_k e_k) = Σ_S conj(b_k) a_k`. -/
theorem integral_conj_torusPoly_mul (S : Finset ℤ) (a b : ℤ → ℂ) (ha : ∀ k ∉ S, a k = 0) :
    ∫ x, conj (torusPoly S b x) * torusPoly S a x ∂haarAddCircle =
      ∑ k ∈ S, conj (b k) * a k := by
  have hint : ∀ k : ℤ, Integrable (fun x => fourier (-k) x • torusPoly S a x) haarAddCircle :=
    fun k => ((fourier (-k)).continuous.smul (torusPoly S a).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hpt : ∀ x, conj (torusPoly S b x) * torusPoly S a x =
      ∑ k ∈ S, conj (b k) * (fourier (-k) x • torusPoly S a x) := by
    intro x
    rw [torusPoly_apply, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, _root_.fourier_neg, smul_eq_mul]
    ring
  simp_rw [hpt]
  rw [integral_finsetSum _ fun k _ => (hint k).const_mul _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul]
  congr 1
  exact fourierCoeff_torusPoly S a ha k

/-! ### The dual weight and the extremizer -/

/-- The real dual weight `w_k(ξ) = ⟨-2πξ + (2πk)²⟩^{-2a}`, `a = 13/32`. -/
def dualWt (k : ℤ) (ξ : ℝ) : ℝ :=
  brk (-(2 * Real.pi) * ξ + (2 * Real.pi * k) ^ 2) ^ (-(2 * (13 / 32 : ℝ)))

theorem dualWt_nonneg (k : ℤ) (ξ : ℝ) : 0 ≤ dualWt k ξ := brk_rpow_nonneg _ _

theorem continuous_dualWt (k : ℤ) : Continuous (dualWt k) := by
  have ha : Continuous (fun ξ : ℝ => -(2 * Real.pi) * ξ + (2 * Real.pi * k) ^ 2) := by fun_prop
  exact (continuous_brk_rpow (-(2 * (13 / 32 : ℝ)))).comp ha

theorem brk_rpow_neg_two_mul (r a : ℝ) : brk r ^ (-(2 * a)) = (1 + ‖r‖ ^ 2) ^ (-a) := by
  rw [brk, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity), Real.norm_eq_abs, sq_abs]
  congr 1
  ring

/-- The complexified dual weight has temperate growth. -/
theorem hasTemperateGrowth_dualWt (k : ℤ) :
    (fun ξ : ℝ => ((dualWt k ξ : ℝ) : ℂ)).HasTemperateGrowth := by
  have haff : (fun ξ : ℝ => -(2 * Real.pi) * ξ + (2 * Real.pi * k) ^ 2).HasTemperateGrowth := by
    fun_prop
  have hw : (fun x : ℝ => (1 + ‖x‖ ^ 2) ^ (-(13 / 32 : ℝ))).HasTemperateGrowth :=
    Function.hasTemperateGrowth_one_add_norm_sq_rpow ℝ _
  have h := Complex.hasTemperateGrowth_ofReal.comp (hw.comp haff)
  have he : (fun ξ : ℝ => ((dualWt k ξ : ℝ) : ℂ)) =
      Complex.ofReal ∘ ((fun x : ℝ => (1 + ‖x‖ ^ 2) ^ (-(13 / 32 : ℝ))) ∘
        fun ξ : ℝ => -(2 * Real.pi) * ξ + (2 * Real.pi * k) ^ 2) := by
    funext ξ
    simp only [Function.comp_apply]
    rw [dualWt, brk_rpow_neg_two_mul]
  rw [he]
  exact h

theorem enorm_dualWt (k : ℤ) (ξ : ℝ) :
    ‖((dualWt k ξ : ℝ) : ℂ)‖ₑ = modWt (-(2 * (13 / 32 : ℝ))) k (-(2 * Real.pi) * ξ) := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (dualWt_nonneg k ξ)]
  rfl

/-- The `X^{0,-a}` norm (squared) of a dense-class forcing, `a = 13/32`, same normalization as
`denseNormSq`. -/
def dualNormSq (f : ℤ → 𝓢(ℝ, ℂ)) : ℝ≥0∞ :=
  ∑' k : ℤ, ∫⁻ ξ, modWt (-(2 * (13 / 32 : ℝ))) k (-(2 * Real.pi) * ξ) * ‖(𝓕⁻ (f k)) ξ‖ₑ ^ 2

/-- The extremizer's modes `g_k = 𝓕(w_k · 𝓕⁻ f_k)`. -/
def dualTest (f : ℤ → 𝓢(ℝ, ℂ)) (k : ℤ) : 𝓢(ℝ, ℂ) :=
  𝓕 (smulLeftCLM ℂ (fun ξ : ℝ => ((dualWt k ξ : ℝ) : ℂ)) (𝓕⁻ (f k)))

theorem dualTest_eq_zero (f : ℤ → 𝓢(ℝ, ℂ)) (k : ℤ) (hk : f k = 0) : dualTest f k = 0 := by
  rw [dualTest, hk, FourierTransform.fourierInv_zero, map_zero, FourierTransform.fourier_zero]

/-- The extremizer has `X^{0,a}` norm equal to the `X^{0,-a}` norm of the forcing. -/
theorem denseNormSq_dualTest (f : ℤ → 𝓢(ℝ, ℂ)) : denseNormSq (dualTest f) = dualNormSq f := by
  unfold denseNormSq dualNormSq
  refine tsum_congr fun k => lintegral_congr fun ξ => ?_
  rw [dualTest, FourierTransform.fourierInv_fourier_eq]
  simp only [smulLeftCLM_apply_apply (hasTemperateGrowth_dualWt k), smul_eq_mul]
  rw [enorm_mul, enorm_dualWt, mul_pow, ← mul_assoc]
  calc modWt (2 * (13 / 32 : ℝ)) k (-(2 * Real.pi) * ξ) *
          modWt (-(2 * (13 / 32 : ℝ))) k (-(2 * Real.pi) * ξ) ^ 2 * ‖(𝓕⁻ (f k)) ξ‖ₑ ^ 2
      = (modWt (-(2 * (13 / 32 : ℝ))) k (-(2 * Real.pi) * ξ) *
          modWt (2 * (13 / 32 : ℝ)) k (-(2 * Real.pi) * ξ)) *
          modWt (-(2 * (13 / 32 : ℝ))) k (-(2 * Real.pi) * ξ) * ‖(𝓕⁻ (f k)) ξ‖ₑ ^ 2 := by ring
    _ = _ := by rw [modWt_neg_mul, one_mul]

theorem integrable_dualWt_mul (f : ℤ → 𝓢(ℝ, ℂ)) (k : ℤ) :
    Integrable (fun ξ => dualWt k ξ * ‖(𝓕⁻ (f k)) ξ‖ ^ 2) := by
  have hb : ∀ ξ, ‖‖(𝓕⁻ (f k)) ξ‖‖ ≤ SchwartzMap.seminorm ℝ 0 0 (𝓕⁻ (f k)) := fun ξ => by
    rw [norm_norm]
    exact SchwartzMap.norm_le_seminorm ℝ (𝓕⁻ (f k)) ξ
  have h2 : Integrable (fun ξ => ‖(𝓕⁻ (f k)) ξ‖ * ‖(𝓕⁻ (f k)) ξ‖) :=
    (𝓕⁻ (f k)).integrable.norm.bdd_mul (𝓕⁻ (f k)).continuous.norm.aestronglyMeasurable
      (ae_of_all _ hb)
  have hw : ∀ ξ, ‖dualWt k ξ‖ ≤ 1 := fun ξ => by
    rw [Real.norm_of_nonneg (dualWt_nonneg k ξ), dualWt]
    exact brk_rpow_neg_le_one _ (by norm_num)
  have h3 := h2.bdd_mul (continuous_dualWt k).aestronglyMeasurable (ae_of_all _ hw)
  simpa only [sq] using h3

/-- Mode-wise pairing via Schwartz Plancherel: `∫ conj(g_k) f_k = ∫ w_k |θ_k|²`. -/
theorem integral_conj_dualTest_mul (f : ℤ → 𝓢(ℝ, ℂ)) (k : ℤ) :
    ∫ t, conj (dualTest f k t) * f k t =
      ((∫ ξ, dualWt k ξ * ‖(𝓕⁻ (f k)) ξ‖ ^ 2 : ℝ) : ℂ) := by
  have hf : 𝓕 (𝓕⁻ (f k)) = f k := FourierTransform.fourier_fourierInv_eq (f k)
  have h2 : ∫ t, conj (dualTest f k t) * f k t =
      ∫ t, inner ℂ ((𝓕 (smulLeftCLM ℂ (fun ξ : ℝ => ((dualWt k ξ : ℝ) : ℂ)) (𝓕⁻ (f k)))) t)
        ((𝓕 (𝓕⁻ (f k))) t) := by
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    beta_reduce
    rw [RCLike.inner_apply', hf]
    rfl
  rw [h2, integral_inner_fourier_fourier, ← integral_complex_ofReal]
  refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
  simp only [RCLike.inner_apply', smulLeftCLM_apply_apply (hasTemperateGrowth_dualWt k),
    smul_eq_mul]
  rw [map_mul, Complex.conj_ofReal, mul_assoc, Complex.conj_mul']
  simp only [Complex.ofReal_mul, Complex.ofReal_pow]

/-- The dual norm is the modulus of the pairing with the extremizer (in particular finite). -/
theorem dualNormSq_eq_enorm (S : Finset ℤ) (f : ℤ → 𝓢(ℝ, ℂ)) (hf : ∀ k ∉ S, f k = 0) :
    dualNormSq f = ‖∑ k ∈ S, ∫ t, conj (dualTest f k t) * f k t‖ₑ := by
  have hnn : ∀ k, 0 ≤ ∫ ξ, dualWt k ξ * ‖(𝓕⁻ (f k)) ξ‖ ^ 2 := fun k =>
    integral_nonneg fun ξ => mul_nonneg (dualWt_nonneg k ξ) (sq_nonneg _)
  simp_rw [integral_conj_dualTest_mul]
  rw [← Complex.ofReal_sum, ← ofReal_norm, Complex.norm_real,
    Real.norm_of_nonneg (Finset.sum_nonneg fun k _ => hnn k),
    ENNReal.ofReal_sum_of_nonneg fun k _ => hnn k]
  rw [dualNormSq, tsum_eq_sum (s := S) fun k hk => by simp [hf k hk]]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_dualWt_mul f k)
    (ae_of_all _ fun ξ => mul_nonneg (dualWt_nonneg k ξ) (sq_nonneg _))]
  refine lintegral_congr fun ξ => ?_
  rw [ENNReal.ofReal_mul (dualWt_nonneg k ξ), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rfl

/-- Spacetime pairing of two dense-class fields, by torus orthogonality. -/
theorem sum_integral_eq_integral_integral (S : Finset ℤ) (f g : ℤ → 𝓢(ℝ, ℂ))
    (hf : ∀ k ∉ S, f k = 0) :
    ∑ k ∈ S, ∫ t, conj (g k t) * f k t =
      ∫ t, ∫ x, conj (denseField S g t x) * denseField S f t x ∂haarAddCircle := by
  have hint : ∀ k, Integrable (fun t => conj (g k t) * f k t) := fun k =>
    (f k).integrable.bdd_mul (Complex.continuous_conj.comp (g k).continuous).aestronglyMeasurable
      (ae_of_all _ fun t => (by
        rw [Complex.norm_conj]
        exact SchwartzMap.norm_le_seminorm ℝ (g k) t :
          ‖conj (g k t)‖ ≤ SchwartzMap.seminorm ℝ 0 0 (g k)))
  rw [← integral_finsetSum _ fun k _ => hint k]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [denseField]
  rw [integral_conj_torusPoly_mul S (fun k => f k t) (fun k => g k t)
    (fun k hk => by simp [hf k hk])]

theorem measurable_denseField (S : Finset ℤ) (f : ℤ → 𝓢(ℝ, ℂ)) :
    Measurable (fun z : ℝ × AddCircle (1 : ℝ) => denseField S f z.1 z.2) := by
  simp only [denseField, torusPoly_apply]
  exact Finset.measurable_sum _ fun k _ =>
    ((f k).continuous.measurable.comp measurable_fst).mul
      ((fourier k).continuous.measurable.comp measurable_snd)

/-- Hölder `(4/3, 4)` on `ℝ × 𝕋` for dense-class fields. -/
theorem lintegral_mul_denseField_le (S : Finset ℤ) (f g : ℤ → 𝓢(ℝ, ℂ)) :
    ∫⁻ t, ∫⁻ x, ‖denseField S f t x‖ₑ * ‖denseField S g t x‖ₑ ∂haarAddCircle ≤
      (∫⁻ t, ∫⁻ x, ‖denseField S f t x‖ₑ ^ (4 / 3 : ℝ) ∂haarAddCircle) ^ (3 / 4 : ℝ) *
      (∫⁻ t, ∫⁻ x, ‖denseField S g t x‖ₑ ^ 4 ∂haarAddCircle) ^ (1 / 4 : ℝ) := by
  set ν : Measure (ℝ × AddCircle (1 : ℝ)) := (volume : Measure ℝ).prod haarAddCircle
  have hF := (measurable_denseField S f).enorm
  have hG := (measurable_denseField S g).enorm
  have conv : ∀ Φ : ℝ × AddCircle (1 : ℝ) → ℝ≥0∞, Measurable Φ →
      ∫⁻ t, ∫⁻ x, Φ (t, x) ∂haarAddCircle = ∫⁻ z, Φ z ∂ν := fun Φ hΦ =>
    (lintegral_prod Φ hΦ.aemeasurable).symm
  have hpq : (4 / 3 : ℝ).HolderConjugate 4 := Real.holderConjugate_iff.2 ⟨by norm_num, by norm_num⟩
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hpq hF.aemeasurable hG.aemeasurable
  rw [conv (fun z => ‖denseField S f z.1 z.2‖ₑ * ‖denseField S g z.1 z.2‖ₑ) (hF.mul hG),
    conv (fun z => ‖denseField S f z.1 z.2‖ₑ ^ (4 / 3 : ℝ)) (hF.pow_const _),
    conv (fun z => ‖denseField S g z.1 z.2‖ₑ ^ 4) (hG.pow_const _)]
  have e4 : ∀ z : ℝ≥0∞, z ^ (4 : ℝ) = z ^ (4 : ℕ) := fun z => by
    rw [← ENNReal.rpow_natCast]
    norm_num
  have e34 : (1 : ℝ) / (4 / 3) = 3 / 4 := by norm_num
  simp only [Pi.mul_apply, e4] at h
  rw [e34] at h
  exact h

/-- `N ≤ x N^{1/2}` with `N < ∞` implies `N ≤ x²`. -/
theorem le_sq_of_le_mul_rpow_half {N x : ℝ≥0∞} (hN : N ≠ ⊤) (h : N ≤ x * N ^ (1 / 2 : ℝ)) :
    N ≤ x ^ 2 := by
  have hNy : N = (N ^ (1 / 2 : ℝ)) ^ 2 := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  by_cases h0 : N ^ (1 / 2 : ℝ) = 0
  · rw [hNy, h0]
    simp
  have hyt : N ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hN
  have h' : N ^ (1 / 2 : ℝ) * N ^ (1 / 2 : ℝ) ≤ x * N ^ (1 / 2 : ℝ) := by
    rw [← sq, ← hNy]
    exact h
  have hyx : N ^ (1 / 2 : ℝ) ≤ x := (ENNReal.mul_le_mul_iff_left h0 hyt).1 h'
  rw [hNy]
  exact pow_le_pow_left₀ bot_le hyx 2

/-- **Dual estimate on the dense class.** One finite constant `C` with
`‖F‖²_{X^{0,-a}} ≤ C (∫∫ |F|^{4/3})^{3/2}` for every dense-class forcing `F` (`a = 13/32`). -/
theorem dense_dual_bound :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (S : Finset ℤ) (f : ℤ → 𝓢(ℝ, ℂ)), (∀ k ∉ S, f k = 0) →
      dualNormSq f ≤
        C * (∫⁻ t, ∫⁻ x, ‖denseField S f t x‖ₑ ^ (4 / 3 : ℝ) ∂haarAddCircle) ^ (3 / 2 : ℝ) := by
  obtain ⟨K, hK, hL4⟩ := dense_L4_bound
  refine ⟨K ^ (1 / 2 : ℝ), ENNReal.rpow_ne_top_of_nonneg (by norm_num) hK, fun S f hf => ?_⟩
  have hg : ∀ k ∉ S, dualTest f k = 0 := fun k hk => dualTest_eq_zero f k (hf k hk)
  have hP := dualNormSq_eq_enorm S f hf
  have hNt : dualNormSq f ≠ ⊤ := by
    rw [hP]
    exact enorm_ne_top
  have hB : ∫⁻ t, ∫⁻ x, ‖denseField S (dualTest f) t x‖ₑ ^ 4 ∂haarAddCircle ≤
      K * dualNormSq f ^ 2 := by
    have := hL4 S (dualTest f) hg
    rwa [denseNormSq_dualTest] at this
  set A := ∫⁻ t, ∫⁻ x, ‖denseField S f t x‖ₑ ^ (4 / 3 : ℝ) ∂haarAddCircle with hA
  have h1 : dualNormSq f ≤ A ^ (3 / 4 : ℝ) *
      (∫⁻ t, ∫⁻ x, ‖denseField S (dualTest f) t x‖ₑ ^ 4 ∂haarAddCircle) ^ (1 / 4 : ℝ) := by
    calc dualNormSq f
        = ‖∫ t, ∫ x, conj (denseField S (dualTest f) t x) * denseField S f t x
            ∂haarAddCircle‖ₑ := by
          rw [hP, sum_integral_eq_integral_integral S f (dualTest f) hf]
      _ ≤ ∫⁻ t, ‖∫ x, conj (denseField S (dualTest f) t x) * denseField S f t x
            ∂haarAddCircle‖ₑ := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ t, ∫⁻ x, ‖denseField S f t x‖ₑ * ‖denseField S (dualTest f) t x‖ₑ
            ∂haarAddCircle := by
          refine lintegral_mono fun t => (enorm_integral_le_lintegral_enorm _).trans
            (le_of_eq (lintegral_congr fun x => ?_))
          rw [enorm_mul, ← ofReal_norm (conj (denseField S (dualTest f) t x)),
            Complex.norm_conj, ofReal_norm, mul_comm]
      _ ≤ _ := lintegral_mul_denseField_le S f (dualTest f)
  have e1 : (dualNormSq f ^ 2) ^ (1 / 4 : ℝ) = dualNormSq f ^ (1 / 2 : ℝ) := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have h2 : dualNormSq f ≤ (A ^ (3 / 4 : ℝ) * K ^ (1 / 4 : ℝ)) * dualNormSq f ^ (1 / 2 : ℝ) := by
    refine h1.trans ?_
    calc A ^ (3 / 4 : ℝ) *
          (∫⁻ t, ∫⁻ x, ‖denseField S (dualTest f) t x‖ₑ ^ 4 ∂haarAddCircle) ^ (1 / 4 : ℝ)
        ≤ A ^ (3 / 4 : ℝ) * (K * dualNormSq f ^ 2) ^ (1 / 4 : ℝ) := by gcongr
      _ = _ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 4), e1, mul_assoc]
  have e2 : ∀ (z : ℝ≥0∞) (r : ℝ), (z ^ r) ^ 2 = z ^ (2 * r) := fun z r => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 1
    push_cast
    ring
  calc dualNormSq f ≤ (A ^ (3 / 4 : ℝ) * K ^ (1 / 4 : ℝ)) ^ 2 := le_sq_of_le_mul_rpow_half hNt h2
    _ = K ^ (1 / 2 : ℝ) * A ^ (3 / 2 : ℝ) := by
      rw [mul_pow, e2, e2, mul_comm (A ^ _)]
      norm_num

end LiebLiniger.FixedPeriod.ALLS.PdeB
