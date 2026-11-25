import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB5Free

/-! # Track B, package 2: the free `L⁴([-1,1] × 𝕋)` estimate

`free_L4` : there is `C < ∞` such that every `u ∈ L²(𝕋)` has a spacetime representative `W` of
`t ↦ e^{it∂ₓ²} u` on `[-1,1] × 𝕋` (slices `W(t,·) = freeL2 t u` a.e., for a.e. `t ∈ [-1,1]`) with
`‖W‖_{L⁴([-1,1]×𝕋)} ≤ C ‖u‖_{L²}`.

Proof: for trigonometric polynomials `g` (coefficients vanishing off a finite `S`) the field
`e^{it∂ₓ²} g = Σ_{k∈S} e^{-it(2πk)²} ĝ_k e_k` coincides on `[-1,1]` with the dense-class field with
time modes `ĝ_k e^{-i(2πk)²t} η(t)` (`η = etaS = 1` on `[-1,1]`), whose `X^{0,13/32}` norm is
`A Σ_k |ĝ_k|²` with `A = ∫ ⟨2πξ⟩^{13/16} |𝓕⁻η(ξ)|² dξ < ∞` (modulation = frequency shift); the
dense `L⁴` bound `dense_L4_bound` applies. General `u`: Fourier truncations, geometric Cauchy
subsequence in `L⁴`, a.e. limit, Fatou, and slice identification by Fatou in `L²`.
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.ALLS.PdeB

open MeasureTheory Filter Topology NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38
open SchwartzMap FourierTransform
open scoped ENNReal

attribute [local instance] isProbabilityMeasure_spatialMeasure

/-! ### Measures -/

/-- `dt ⊗ dx` on `[-1,1] × 𝕋`. -/
abbrev freeMeasure : Measure (ℝ × PhysicalCircle) :=
  ((volume : Measure ℝ).restrict (Set.Icc (-1) 1)).prod spatialMeasure

theorem freeMeasure_eq : freeMeasure = stMeasure.restrict (Set.Icc (-1) 1 ×ˢ Set.univ) := by
  have h := Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := spatialMeasure)
    (Set.Icc (-1 : ℝ) 1) Set.univ
  rw [Measure.restrict_univ] at h
  exact h

theorem slabMeasure_le_free {δ : ℝ} (hδ1 : δ ≤ 1) : slabMeasure δ ≤ freeMeasure := by
  rw [slabMeasure_eq, freeMeasure_eq]
  exact Measure.restrict_mono (Set.prod_mono (Set.Icc_subset_Icc (by norm_num) hδ1) le_rfl) le_rfl

/-! ### Modulated Schwartz cutoff -/

/-- `t ↦ e^{-iλt} η(t)`. -/
def modS (lam : ℝ) (η : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) := SchwartzMap.smulLeftCLM ℂ (ph (-lam)) η

theorem modS_apply (lam : ℝ) (η : 𝓢(ℝ, ℂ)) (t : ℝ) : modS lam η t = ph (-lam) t * η t := by
  rw [modS, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_ph (-lam)), smul_eq_mul]

theorem fourierInv_modS (lam : ℝ) (η : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    (𝓕⁻ (modS lam η) : 𝓢(ℝ, ℂ)) ξ = (𝓕⁻ η : 𝓢(ℝ, ℂ)) (ξ - lam / (2 * Real.pi)) := by
  rw [fourierInv_schwartz_apply, fourierInv_schwartz_apply]
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  have ha : 2 * Real.pi * (lam / (2 * Real.pi)) = lam := by
    rw [mul_comm]; exact div_mul_cancel₀ _ hπ
  have he : 2 * Real.pi * ξ + -lam = 2 * Real.pi * (ξ - lam / (2 * Real.pi)) := by
    rw [mul_sub, ha]; ring
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  rw [modS_apply, ← mul_assoc, ph_mul, he]

theorem fourierInv_smul_schwartz (c : ℂ) (f : 𝓢(ℝ, ℂ)) (y : ℝ) :
    (𝓕⁻ (c • f) : 𝓢(ℝ, ℂ)) y = c * (𝓕⁻ f : 𝓢(ℝ, ℂ)) y := by
  rw [fourierInv_schwartz_apply, fourierInv_schwartz_apply, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [smul_apply, smul_eq_mul]
  ring

/-- Time modes of the cut-off free evolution of `Σ c_k e_k`. -/
def freeDense (c : ℤ → ℂ) : ℤ → 𝓢(ℝ, ℂ) := fun k => c k • modS ((2 * Real.pi * k) ^ 2) etaS

/-- The modulation-invariant constant `∫ ⟨2πξ⟩^{13/16} |𝓕⁻η(ξ)|² dξ`. -/
def freeA : ℝ≥0∞ := ∫⁻ x, bw (2 * (13 / 32 : ℝ)) x * ‖(𝓕⁻ etaS : 𝓢(ℝ, ℂ)) x‖ₑ ^ 2

theorem freeA_ne_top : freeA ≠ ⊤ := by
  set D : ℝ≥0∞ := ENNReal.ofReal (decayC (𝓕⁻ etaS : 𝓢(ℝ, ℂ)))
  have hle : ∀ x, bw (2 * (13 / 32 : ℝ)) x * ‖(𝓕⁻ etaS : 𝓢(ℝ, ℂ)) x‖ₑ ^ 2 ≤
      D ^ 2 * bw (-(51 / 16)) x := by
    intro x
    calc bw (2 * (13 / 32 : ℝ)) x * ‖(𝓕⁻ etaS : 𝓢(ℝ, ℂ)) x‖ₑ ^ 2
        ≤ bw (2 * (13 / 32 : ℝ)) x * (D * bw (-2) x) ^ 2 := by
          gcongr
          exact enorm_le_decayC _ x
      _ = D ^ 2 * (bw (2 * (13 / 32 : ℝ)) x * bw (2 * (-2)) x) := by rw [mul_pow, bw_sq]; ring
      _ = D ^ 2 * bw (-(51 / 16)) x := by rw [bw_mul]; norm_num
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hle)
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
  exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    (lintegral_bw_lt_top (by norm_num)).ne

theorem denseNormSq_freeDense (c : ℤ → ℂ) :
    denseNormSq (freeDense c) = freeA * ∑' k, ‖c k‖ₑ ^ 2 := by
  unfold denseNormSq
  rw [← ENNReal.tsum_mul_left]
  congr 1
  funext k
  have h : ∀ ξ, modWt (2 * (13 / 32 : ℝ)) k (-(2 * Real.pi) * ξ) *
      ‖(𝓕⁻ (freeDense c k) : 𝓢(ℝ, ℂ)) ξ‖ₑ ^ 2 =
      ‖c k‖ₑ ^ 2 * (fun x => bw (2 * (13 / 32 : ℝ)) x * ‖(𝓕⁻ etaS : 𝓢(ℝ, ℂ)) x‖ₑ ^ 2)
        (ξ - (2 * Real.pi * k) ^ 2 / (2 * Real.pi)) := by
    intro ξ
    simp only [freeDense]
    rw [fourierInv_smul_schwartz, fourierInv_modS, modWt_eq_bw, enorm_mul, mul_pow]
    ring
  simp_rw [h]
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top enorm_ne_top),
    lintegral_sub_right_eq_self (fun x => bw (2 * (13 / 32 : ℝ)) x *
      ‖(𝓕⁻ etaS : 𝓢(ℝ, ℂ)) x‖ₑ ^ 2) _, mul_comm]
  rfl

/-- **Dense free `L⁴` bound** on `[-1,1] × 𝕋` for trigonometric polynomial data. -/
theorem free_dense_L4 : ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (S : Finset ℤ) (c : ℤ → ℂ), (∀ k ∉ S, c k = 0) →
    ∫⁻ t in Set.Icc (-1 : ℝ) 1, ∫⁻ x, ‖torusPoly S (fun k => freePhase t k * c k) x‖ₑ ^ 4
      ∂AddCircle.haarAddCircle ≤ K * (∑ k ∈ S, ‖c k‖ₑ ^ 2) ^ 2 := by
  obtain ⟨K, hK, h⟩ := dense_L4_bound
  refine ⟨K * freeA ^ 2, ENNReal.mul_ne_top hK (ENNReal.pow_ne_top freeA_ne_top),
    fun S c hc => ?_⟩
  have hfs : ∀ k ∉ S, freeDense c k = 0 := fun k hk => by simp [freeDense, hc k hk]
  have heq : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ∀ x, torusPoly S (fun k => freePhase t k * c k) x =
      denseField S (freeDense c) t x := by
    intro t ht x
    simp only [denseField]
    congr 2
    funext k
    rw [freeDense, smul_apply, smul_eq_mul, modS_apply, etaS_eq_one ht, mul_one,
      freePhase_eq_ph, disp]
    ring
  calc ∫⁻ t in Set.Icc (-1 : ℝ) 1, ∫⁻ x, ‖torusPoly S (fun k => freePhase t k * c k) x‖ₑ ^ 4
        ∂AddCircle.haarAddCircle
      = ∫⁻ t in Set.Icc (-1 : ℝ) 1, ∫⁻ x, ‖denseField S (freeDense c) t x‖ₑ ^ 4
          ∂AddCircle.haarAddCircle :=
        setLIntegral_congr_fun measurableSet_Icc (fun t ht => by simp only [heq t ht])
    _ ≤ ∫⁻ t, ∫⁻ x, ‖denseField S (freeDense c) t x‖ₑ ^ 4 ∂AddCircle.haarAddCircle :=
        setLIntegral_le_lintegral _ _
    _ ≤ K * denseNormSq (freeDense c) ^ 2 := h S _ hfs
    _ = K * freeA ^ 2 * (∑ k ∈ S, ‖c k‖ₑ ^ 2) ^ 2 := by
        rw [denseNormSq_freeDense, tsum_eq_sum (s := S) (fun k hk => by simp [hc k hk]), mul_pow]
        ring

/-! ### Trigonometric-polynomial data in `L²` -/

/-- The free evolution field `(t,x) ↦ Σ_{k∈S} e^{-it(2πk)²} ĝ_k e_k(x)`. -/
def fieldOf (S : Finset ℤ) (g : PhysicalL2) (p : ℝ × PhysicalCircle) : ℂ :=
  torusPoly S (fun k => freePhase p.1 k * physicalFourier g k) p.2

theorem fieldOf_apply (S : Finset ℤ) (g : PhysicalL2) (p : ℝ × PhysicalCircle) :
    fieldOf S g p = ∑ k ∈ S, freePhase p.1 k * physicalFourier g k * fourier k p.2 := by
  rw [fieldOf, torusPoly_apply]

theorem continuous_fieldOf (S : Finset ℤ) (g : PhysicalL2) : Continuous (fieldOf S g) := by
  have h : fieldOf S g = fun p => ∑ k ∈ S, freePhase p.1 k * physicalFourier g k * fourier k p.2 :=
    funext (fieldOf_apply S g)
  rw [h]
  exact continuous_finsetSum _ fun k _ =>
    (((continuous_freePhase k).comp continuous_fst).mul continuous_const).mul
      ((fourier k).continuous.comp continuous_snd)

theorem fieldOf_sub (S : Finset ℤ) (a b : PhysicalL2) (p : ℝ × PhysicalCircle) :
    fieldOf S (a - b) p = fieldOf S a p - fieldOf S b p := by
  rw [fieldOf_apply, fieldOf_apply, fieldOf_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [physicalFourier_sub_l2]
  ring

theorem fieldOf_mono {S T : Finset ℤ} (hST : S ⊆ T) {g : PhysicalL2}
    (hg : ∀ k ∉ S, physicalFourier g k = 0) : fieldOf S g = fieldOf T g := by
  funext p
  rw [fieldOf_apply, fieldOf_apply]
  refine Finset.sum_subset hST fun k _ hk => ?_
  rw [hg k hk]
  ring

theorem sum_enorm_sq_eq {S : Finset ℤ} {g : PhysicalL2} (hg : ∀ k ∉ S, physicalFourier g k = 0) :
    ∑ k ∈ S, ‖physicalFourier g k‖ₑ ^ 2 = ‖g‖ₑ ^ 2 := by
  have h1 := hasSum_physicalFourier_sq g
  have h2 : HasSum (fun n : ℤ => ‖physicalFourier g n‖ ^ 2)
      (∑ k ∈ S, ‖physicalFourier g k‖ ^ 2) :=
    hasSum_sum_of_ne_finset_zero (fun k hk => by simp [hg k hk])
  have he := h2.unique h1
  simp_rw [← ofReal_norm]
  rw [← ENNReal.ofReal_pow (norm_nonneg _)]
  simp_rw [← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity), he]

theorem freeL2_eq_toLp {S : Finset ℤ} {g : PhysicalL2} (hg : ∀ k ∉ S, physicalFourier g k = 0)
    (t : ℝ) : freeL2 t g = ContinuousMap.toLp 2 spatialMeasure ℂ
      (torusPoly S (fun k => freePhase t k * physicalFourier g k)) := by
  refine physicalFourier_ext_l2 fun n => ?_
  rw [physicalFourier_freeL2, physicalFourier_congr_ae
    (ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := spatialMeasure) (𝕜 := ℂ) _)]
  exact (fourierCoeff_torusPoly S (fun k => freePhase t k * physicalFourier g k)
    (fun k hk => mul_eq_zero.2 (Or.inr (hg k hk))) n).symm

theorem fieldOf_slice {S : Finset ℤ} {g : PhysicalL2} (hg : ∀ k ∉ S, physicalFourier g k = 0)
    (t : ℝ) : (fun x => fieldOf S g (t, x)) =ᵐ[spatialMeasure] (freeL2 t g : PhysicalCircle → ℂ) := by
  rw [freeL2_eq_toLp hg t]
  filter_upwards [ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := spatialMeasure) (𝕜 := ℂ)
    (torusPoly S (fun k => freePhase t k * physicalFourier g k))] with x hx
  rw [hx]
  rfl

/-- **Free `L⁴` bound for trigonometric-polynomial data**: `‖e^{it∂ₓ²}g‖_{L⁴([-1,1]×𝕋)} ≤ K ‖g‖`. -/
theorem free_field_L4 : ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (S : Finset ℤ) (g : PhysicalL2),
    (∀ k ∉ S, physicalFourier g k = 0) → eLpNorm (fieldOf S g) 4 freeMeasure ≤ K * ‖g‖ₑ := by
  obtain ⟨K, hK, h⟩ := free_dense_L4
  refine ⟨K ^ ((4 : ℕ)⁻¹ : ℝ), ENNReal.rpow_ne_top_of_nonneg (by norm_num) hK,
    fun S g hg => enn_le_of_pow_le four_ne_zero ?_⟩
  have hm : AEMeasurable (fun p => ‖fieldOf S g p‖ₑ ^ (4 : ℝ)) freeMeasure :=
    ((continuous_fieldOf S g).measurable.enorm.pow_const _).aemeasurable
  have hL : eLpNorm (fieldOf S g) 4 freeMeasure ^ 4 =
      ∫⁻ t in Set.Icc (-1 : ℝ) 1, ∫⁻ x, ‖torusPoly S (fun k => freePhase t k * physicalFourier g k) x‖ₑ ^ 4
        ∂AddCircle.haarAddCircle := by
    have h4 : (4 : ℝ≥0∞) = ENNReal.ofReal 4 := by simp
    rw [h4, ← ENNReal.rpow_natCast, show ((4 : ℕ) : ℝ) = 4 by norm_num,
      eLpNorm_rpow_eq_lintegral (continuous_fieldOf S g).aestronglyMeasurable (by norm_num),
      lintegral_prod _ hm]
    refine lintegral_congr fun t => lintegral_congr fun x => ?_
    rw [← ENNReal.rpow_natCast]
    norm_num
    rfl
  rw [hL, mul_pow, ENNReal.rpow_inv_natCast_pow four_ne_zero]
  refine (h S (physicalFourier g) hg).trans (le_of_eq ?_)
  rw [sum_enorm_sq_eq hg, ← pow_mul]

/-! ### Approximation by trigonometric polynomials -/

/-- The symmetric frequency window `{-N, …, N}`. -/
def truncS (N : ℕ) : Finset ℤ := Finset.Icc (-(N : ℤ)) N

theorem tendsto_truncS : Tendsto truncS atTop atTop := by
  refine Filter.tendsto_atTop_finset_of_monotone (fun a b hab => ?_) (fun k => ⟨k.natAbs, ?_⟩)
  · exact Finset.Icc_subset_Icc (neg_le_neg (by exact_mod_cast hab)) (by exact_mod_cast hab)
  · rw [truncS, Finset.mem_Icc, Int.natCast_natAbs]
    exact ⟨neg_abs_le k, le_abs_self k⟩

/-- Fourier truncation `P_S u = Σ_{k∈S} û_k e_k` in `L²`. -/
def projL2 (S : Finset ℤ) (u : PhysicalL2) : PhysicalL2 :=
  ContinuousMap.toLp 2 spatialMeasure ℂ
    (torusPoly S (fun k => if k ∈ S then physicalFourier u k else 0))

theorem physicalFourier_projL2 (S : Finset ℤ) (u : PhysicalL2) (n : ℤ) :
    physicalFourier (projL2 S u) n = if n ∈ S then physicalFourier u n else 0 := by
  rw [projL2, physicalFourier_congr_ae
    (ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := spatialMeasure) (𝕜 := ℂ) _)]
  exact fourierCoeff_torusPoly S _ (fun k hk => by simp [hk]) n

theorem norm_projL2_sub_sq (S : Finset ℤ) (u : PhysicalL2) :
    ‖projL2 S u - u‖ ^ 2 = ‖u‖ ^ 2 - ∑ k ∈ S, ‖physicalFourier u k‖ ^ 2 := by
  have h1 := hasSum_physicalFourier_sq (projL2 S u - u)
  have h2 := hasSum_physicalFourier_sq u
  have h3 : HasSum (fun n : ℤ => if n ∈ S then ‖physicalFourier u n‖ ^ 2 else 0)
      (∑ k ∈ S, ‖physicalFourier u k‖ ^ 2) := by
    have : HasSum (fun n : ℤ => if n ∈ S then ‖physicalFourier u n‖ ^ 2 else 0)
        (∑ k ∈ S, if k ∈ S then ‖physicalFourier u k‖ ^ 2 else 0) :=
      hasSum_sum_of_ne_finset_zero (fun k hk => by simp [hk])
    convert this using 1
    exact Finset.sum_congr rfl fun k hk => by simp [hk]
  have h4 := h2.sub h3
  have hf : (fun n : ℤ => ‖physicalFourier (⇑(projL2 S u - u)) n‖ ^ 2) =
      fun n => ‖physicalFourier u n‖ ^ 2 - (if n ∈ S then ‖physicalFourier u n‖ ^ 2 else 0) := by
    funext n
    rw [physicalFourier_sub_l2, physicalFourier_projL2]
    split_ifs <;> simp
  rw [hf] at h1
  exact h1.unique h4

theorem tendsto_projL2 (u : PhysicalL2) :
    Tendsto (fun N => ‖projL2 (truncS N) u - u‖) atTop (𝓝 0) := by
  have h2 := hasSum_physicalFourier_sq u
  have hT : Tendsto (fun s : Finset ℤ => ∑ b ∈ s, ‖physicalFourier u b‖ ^ 2) atTop
      (𝓝 (‖u‖ ^ 2)) := h2
  have hsq : Tendsto (fun N => ‖projL2 (truncS N) u - u‖ ^ 2) atTop (𝓝 0) := by
    simp_rw [norm_projL2_sub_sq]
    have := (tendsto_const_nhds (x := ‖u‖ ^ 2)).sub (hT.comp tendsto_truncS)
    rw [sub_self] at this
    exact this
  have := hsq.sqrt
  simp_rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at this
  exact this

theorem exists_trig_approx (u : PhysicalL2) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ (S : Finset ℤ) (g : PhysicalL2), (∀ k ∉ S, physicalFourier g k = 0) ∧ ‖g - u‖ₑ ≤ ε := by
  have h := ENNReal.tendsto_ofReal (tendsto_projL2 u)
  rw [ENNReal.ofReal_zero] at h
  obtain ⟨N, hN⟩ := (h.eventually (gt_mem_nhds (pos_iff_ne_zero.2 hε))).exists
  refine ⟨truncS N, projL2 (truncS N) u, fun k hk => by simp [physicalFourier_projL2, hk], ?_⟩
  rw [← ofReal_norm]
  exact hN.le

/-! ### Limits -/

/-- Slice identification of an a.e. limit of continuous fields whose slices converge in `L²`. -/
theorem slice_of_ae_tendsto {ρ : Measure ℝ} [SFinite ρ] {w : ℕ → ℝ × PhysicalCircle → ℂ}
    {W : ℝ × PhysicalCircle → ℂ} {y : ℕ → ℝ → PhysicalL2} {v : ℝ → PhysicalL2}
    (hw : ∀ n, Continuous (w n))
    (hy : ∀ n t, (fun x => w n (t, x)) =ᵐ[spatialMeasure] (y n t : PhysicalCircle → ℂ))
    (hv : ∀ t, Tendsto (fun n => y n t) atTop (𝓝 (v t)))
    (hlim : ∀ᵐ p ∂(ρ.prod spatialMeasure), Tendsto (fun n => w n p) atTop (𝓝 (W p))) :
    ∀ᵐ t ∂ρ, (fun x => W (t, x)) =ᵐ[spatialMeasure] (v t : PhysicalCircle → ℂ) := by
  filter_upwards [Measure.ae_ae_of_ae_prod hlim] with t ht
  set f : ℕ → PhysicalCircle → ℂ := fun n x => w n (t, x) - (v t : PhysicalCircle → ℂ) x
  have hfm : ∀ n, AEStronglyMeasurable (f n) spatialMeasure := fun n =>
    ((hw n).comp (Continuous.prodMk_right t)).aestronglyMeasurable.sub (Lp.aestronglyMeasurable _)
  have hglim : ∀ᵐ x ∂spatialMeasure,
      Tendsto (fun n => f n x) atTop (𝓝 (W (t, x) - (v t : PhysicalCircle → ℂ) x)) := by
    filter_upwards [ht] with x hx
    exact hx.sub tendsto_const_nhds
  have hgm := aestronglyMeasurable_of_tendsto_ae atTop hfm hglim
  have hfn : ∀ n, eLpNorm (f n) 2 spatialMeasure = edist (y n t) (v t) := by
    intro n
    rw [edist_eq_enorm_sub, Lp.enorm_def]
    refine eLpNorm_congr_ae ?_
    filter_upwards [hy n t, Lp.coeFn_sub (y n t) (v t)] with x h1 h2
    simp only [f]
    rw [h2, Pi.sub_apply, h1]
  have h0 : eLpNorm (fun x => W (t, x) - (v t : PhysicalCircle → ℂ) x) 2 spatialMeasure = 0 := by
    refine le_antisymm ((Lp.eLpNorm_lim_le_liminf_eLpNorm hfm _ hgm hglim).trans ?_) bot_le
    simp only [hfn]
    rw [((tendsto_iff_edist_tendsto_0.1 (hv t))).liminf_eq]
  rw [eLpNorm_eq_zero_iff two_ne_zero] at h0
  filter_upwards [h0] with x hx
  exact sub_eq_zero.1 hx

/-- **Free `L⁴([-1,1] × 𝕋)` estimate** with an actual spacetime representative. -/
theorem free_L4 : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ u : PhysicalL2, ∃ W : ℝ × PhysicalCircle → ℂ,
    AEStronglyMeasurable W freeMeasure ∧ eLpNorm W 4 freeMeasure ≤ C * ‖u‖ₑ ∧
    ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Icc (-1) 1)),
      (fun x => W (t, x)) =ᵐ[spatialMeasure] (freeL2 t u : PhysicalCircle → ℂ) := by
  obtain ⟨K, hK, hL4⟩ := free_field_L4
  refine ⟨K, hK, fun u => ?_⟩
  have h2 : (2⁻¹ : ℝ≥0∞) ≠ 0 := ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top
  choose S g hgS hg using fun n : ℕ => exists_trig_approx u (ε := 2⁻¹ ^ n) (pow_ne_zero _ h2)
  set w : ℕ → ℝ × PhysicalCircle → ℂ := fun n => fieldOf (S n) (g n) with hw
  have hwc : ∀ n, Continuous (w n) := fun n => continuous_fieldOf _ _
  have hwm : ∀ n, AEStronglyMeasurable (w n) freeMeasure := fun n => (hwc n).aestronglyMeasurable
  have hdiff : ∀ n m, ‖g n - g m‖ₑ ≤ 2⁻¹ ^ n + 2⁻¹ ^ m := fun n m => by
    calc ‖g n - g m‖ₑ = ‖(g n - u) - (g m - u)‖ₑ := by rw [sub_sub_sub_cancel_right]
      _ ≤ ‖g n - u‖ₑ + ‖g m - u‖ₑ := enorm_sub_le
      _ ≤ _ := add_le_add (hg n) (hg m)
  have hvan : ∀ n m, ∀ k ∉ S n ∪ S m, physicalFourier (⇑(g n - g m)) k = 0 := by
    intro n m k hk
    rw [physicalFourier_sub_l2, hgS n k (fun h => hk (Finset.mem_union_left _ h)),
      hgS m k (fun h => hk (Finset.mem_union_right _ h)), sub_zero]
  have hw_diff : ∀ n m, eLpNorm (w n - w m) 4 freeMeasure ≤ K * (2⁻¹ ^ n + 2⁻¹ ^ m) := by
    intro n m
    have he : w n - w m = fieldOf (S n ∪ S m) (g n - g m) := by
      funext p
      simp only [hw, Pi.sub_apply]
      rw [fieldOf_sub, fieldOf_mono Finset.subset_union_left (hgS n),
        fieldOf_mono Finset.subset_union_right (hgS m)]
    rw [he]
    exact (hL4 _ _ (hvan n m)).trans (emL (hdiff n m))
  have hsum_le : ∀ N n m : ℕ, N ≤ n → N ≤ m → (2⁻¹ : ℝ≥0∞) ^ n + 2⁻¹ ^ m ≤ 2 * 2⁻¹ ^ N :=
    fun N n m hn hm => by
      rw [two_mul]; exact add_le_add (two_inv_pow_anti hn) (two_inv_pow_anti hm)
  have hA2 : K * 2 ≠ ⊤ := ENNReal.mul_ne_top hK ENNReal.ofNat_ne_top
  have hae : ∀ᵐ p ∂freeMeasure, ∃ l : ℂ, Tendsto (fun n => w n p) atTop (𝓝 l) := by
    refine Lp.ae_tendsto_of_cauchy_eLpNorm hwm (by norm_num : (1 : ℝ≥0∞) ≤ 4)
      (B := fun N => (K * 2 + 1) * 2⁻¹ ^ N) ?_ ?_
    · rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
      exact ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨hA2, ENNReal.one_ne_top⟩)
        ENNReal.ofNat_ne_top
    · intro N n m hn hm
      refine (hw_diff n m).trans_lt ?_
      calc K * (2⁻¹ ^ n + 2⁻¹ ^ m) ≤ K * (2 * 2⁻¹ ^ N) := emL (hsum_le N n m hn hm)
        _ = K * 2 * 2⁻¹ ^ N := by ring
        _ < (K * 2 + 1) * 2⁻¹ ^ N := by
          rw [mul_comm _ (2⁻¹ ^ N), mul_comm _ (2⁻¹ ^ N)]
          exact ENNReal.mul_lt_mul_right (pow_ne_zero _ h2)
            (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 two_ne_zero))
            (ENNReal.lt_add_right hA2 one_ne_zero)
  set W : ℝ × PhysicalCircle → ℂ := fun p => limUnder atTop fun n => w n p with hW_def
  have hWlim : ∀ᵐ p ∂freeMeasure, Tendsto (fun n => w n p) atTop (𝓝 (W p)) := by
    filter_upwards [hae] with p hp
    exact tendsto_nhds_limUnder hp
  have hWm : AEStronglyMeasurable W freeMeasure :=
    aestronglyMeasurable_of_tendsto_ae atTop hwm hWlim
  have hgn : ∀ n, ‖g n‖ₑ ≤ ‖u‖ₑ + 2⁻¹ ^ n := fun n => by
    calc ‖g n‖ₑ = ‖u + (g n - u)‖ₑ := by congr 1; abel
      _ ≤ ‖u‖ₑ + ‖g n - u‖ₑ := enorm_add_le _ _
      _ ≤ _ := add_le_add le_rfl (hg n)
  have hWb : eLpNorm W 4 freeMeasure ≤ K * ‖u‖ₑ := by
    refine (Lp.eLpNorm_lim_le_liminf_eLpNorm hwm W hWm hWlim).trans ?_
    have hle : ∀ n, eLpNorm (w n) 4 freeMeasure ≤ K * (‖u‖ₑ + 2⁻¹ ^ n) := fun n =>
      (hL4 _ _ (hgS n)).trans (emL (hgn n))
    refine (Filter.liminf_le_liminf (Eventually.of_forall hle)).trans ?_
    rw [(bound_tendsto hK ‖u‖ₑ).liminf_eq]
  refine ⟨W, hWm, hWb, ?_⟩
  refine slice_of_ae_tendsto hwc (y := fun n t => freeL2 t (g n))
    (fun n t => fieldOf_slice (hgS n) t) (fun t => ?_) hWlim
  rw [tendsto_iff_edist_tendsto_0]
  have he : ∀ n, edist (freeL2 t (g n)) (freeL2 t u) = ‖g n - u‖ₑ := fun n => by
    rw [edist_eq_enorm_sub, ← ofReal_norm, norm_freeL2_sub, ofReal_norm]
  simp_rw [he]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (geom_tendsto ENNReal.one_ne_top) (fun n => bot_le) (fun n => ?_)
  rw [one_mul]
  exact hg n

end LiebLiniger.FixedPeriod.ALLS.PdeB
