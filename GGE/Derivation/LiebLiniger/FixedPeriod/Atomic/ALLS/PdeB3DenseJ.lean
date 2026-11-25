import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB3Density

/-! # Track B, step B3: the dense short-time Duhamel estimates on `J = [0, δ]`, in `Lᵖ` form

With the concrete cutoff `etaS` (`= 1` on `[-1,1]`), `0 < δ ≤ 1` and a dense forcing
`G = Σ_{k∈S} G_k(t) e_k(x)`:

* `duhH F t = ∫₀ᵗ e^{i(t-r)∂ₓ²}(-iF(r)) dr` is the actual `H⁻¹` Bochner Duhamel integral;
* `dField δ S G t ∈ L²(𝕋)` is the field `-i Σ_k (dOut δ G k)(t) e_k`, with
  `dOut δ G k = duhOut etaS ((2πk)²) (etaS(·/δ) G_k)`, and `wOut δ S G` is the same field as a
  spacetime function on `ℝ × 𝕋`;
* `dField_ident` : `l2ToHm1 (dField δ S G t) = duhH G t` for `t ∈ [0,δ]`;
* `dField_trace` : `‖dField δ S G t‖_{L²} ≤ K δ^{1/16} ‖G‖_{L^{4/3}(ℝ×𝕋)}` for every `t`;
* `wOut_L4` : `‖wOut δ S G‖_{L⁴(ℝ×𝕋)} ≤ K δ^{1/16} ‖G‖_{L^{4/3}(ℝ×𝕋)}`;
* linearity in the forcing (`denseSp_sub_union`, `wOut_sub`, `dField_sub`) and continuity of
  `t ↦ dField δ S G t` in `L²`.
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.ALLS.PdeB

open MeasureTheory Filter Topology NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38
open SchwartzMap
open scoped ENNReal

attribute [local instance] isProbabilityMeasure_spatialMeasure

/-- The spacetime measure `dt ⊗ dx` on `ℝ × 𝕋`. -/
abbrev stMeasure : Measure (ℝ × PhysicalCircle) := (volume : Measure ℝ).prod spatialMeasure

/-- The actual `H⁻¹` Bochner Duhamel integral `∫₀ᵗ e^{i(t-r)∂ₓ²}(-iF(r)) dr`. -/
def duhH (F : ℝ × PhysicalCircle → ℂ) (t : ℝ) : SobolevCarrier38 (-1) :=
  ∫ r in (0 : ℝ)..t, freeProp (-1) (t - r) (negIMul (-1) (fnToHm1 (fun x => F (r, x))))

/-- Mode `k` of the fixed-cutoff Duhamel output of the cut-off forcing `etaS(·/δ) G_k`. -/
def dOut (δ : ℝ) (G : ℤ → 𝓢(ℝ, ℂ)) (k : ℤ) : 𝓢(ℝ, ℂ) :=
  duhOut etaS ((2 * Real.pi * k) ^ 2) (cutMul (dilateS etaS δ) (G k))

/-- The dense Duhamel output at time `t` as an element of `L²(𝕋)`. -/
def dField (δ : ℝ) (S : Finset ℤ) (G : ℤ → 𝓢(ℝ, ℂ)) (t : ℝ) : PhysicalL2 :=
  ContinuousMap.toLp 2 spatialMeasure ℂ (torusPoly S (fun k => -Complex.I * dOut δ G k t))

/-- The dense Duhamel output as a spacetime function. -/
def wOut (δ : ℝ) (S : Finset ℤ) (G : ℤ → 𝓢(ℝ, ℂ)) (p : ℝ × PhysicalCircle) : ℂ :=
  -Complex.I * denseSp S (dOut δ G) p

theorem cutMul_zero_right (c : 𝓢(ℝ, ℂ)) : cutMul c 0 = 0 := by
  ext t; simp [cutMul_apply]

theorem cutMul_sub_right (c f g : 𝓢(ℝ, ℂ)) : cutMul c (f - g) = cutMul c f - cutMul c g := by
  ext t; simp [cutMul_apply, mul_sub]

theorem duhOut_sub_apply (η : 𝓢(ℝ, ℂ)) (lam : ℝ) (f g : 𝓢(ℝ, ℂ)) (t : ℝ) :
    duhOut η lam (f - g) t = duhOut η lam f t - duhOut η lam g t := by
  have hc : ∀ h : 𝓢(ℝ, ℂ), Continuous fun r => ph (-lam) (t - r) * h r := fun h =>
    ((continuous_ph _).comp (continuous_const.sub continuous_id)).mul h.continuous
  rw [duhOut_apply, duhOut_apply, duhOut_apply, ← mul_sub,
    ← intervalIntegral.integral_sub ((hc f).intervalIntegrable _ _) ((hc g).intervalIntegrable _ _)]
  congr 2
  ext r
  rw [_root_.sub_apply, mul_sub]

theorem dOut_eq_zero {δ : ℝ} {G : ℤ → 𝓢(ℝ, ℂ)} {k : ℤ} (hk : G k = 0) : dOut δ G k = 0 := by
  rw [dOut, hk, duhOut_cutMul_zero]

theorem dOut_sub_apply (δ : ℝ) (G G' : ℤ → 𝓢(ℝ, ℂ)) (k : ℤ) (t : ℝ) :
    dOut δ (G - G') k t = dOut δ G k t - dOut δ G' k t := by
  rw [dOut, Pi.sub_apply, cutMul_sub_right, duhOut_sub_apply]
  rfl

theorem continuous_wOut (δ : ℝ) (S : Finset ℤ) (G : ℤ → 𝓢(ℝ, ℂ)) : Continuous (wOut δ S G) :=
  continuous_const.mul (continuous_denseSp S _)

theorem wOut_apply_eq (δ : ℝ) (S : Finset ℤ) (G : ℤ → 𝓢(ℝ, ℂ)) (t : ℝ) (x : PhysicalCircle) :
    wOut δ S G (t, x) = torusPoly S (fun k => -Complex.I * dOut δ G k t) x := by
  rw [wOut, denseSp_apply, torusPoly_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem dField_ae (δ : ℝ) (S : Finset ℤ) (G : ℤ → 𝓢(ℝ, ℂ)) (t : ℝ) :
    (dField δ S G t : PhysicalCircle → ℂ) =ᵐ[spatialMeasure] fun x => wOut δ S G (t, x) := by
  have h := ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := spatialMeasure) (𝕜 := ℂ)
    (torusPoly S (fun k => -Complex.I * dOut δ G k t))
  filter_upwards [h] with x hx
  rw [dField, hx, wOut_apply_eq]

/-- **Identification on `J = [0,δ]`** with the actual `H⁻¹` Bochner Duhamel integral. -/
theorem dField_ident {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (S : Finset ℤ) (G : ℤ → 𝓢(ℝ, ℂ))
    (hG : ∀ k ∉ S, G k = 0) {t : ℝ} (ht : t ∈ Set.Icc 0 δ) :
    l2ToHm1 (dField δ S G t) = duhH (denseSp S G) t := by
  have hG' : ∀ k ∉ S, (fun k => cutMul (dilateS etaS δ) (G k)) k = 0 := fun k hk => by
    simp only [hG k hk, cutMul_zero_right]
  have h1 := duhamel_dense_eq_l2ToHm1 etaS S (fun k => cutMul (dilateS etaS δ) (G k)) hG' t
    (etaS_eq_one ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have h2 : duhH (denseSp S (fun k => cutMul (dilateS etaS δ) (G k))) t =
      duhH (denseSp S G) t := by
    unfold duhH
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_le ht.1] at hr
    have hrδ : r / δ ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨by linarith [div_nonneg hr.1 hδ.le], (div_le_one hδ).2 (hr.2.trans ht.2)⟩
    have hx : ∀ x, denseSp S (fun k => cutMul (dilateS etaS δ) (G k)) (r, x) =
        denseSp S G (r, x) := fun x => by
      simp only [denseSp]
      rw [denseField_cutMul etaS hδ.ne' S G r x, etaS_eq_one hrδ, one_mul]
    simp only [hx]
  rw [← h2]
  exact h1.symm

theorem enorm_negI : ‖-Complex.I‖ₑ = 1 := by
  rw [← ofReal_norm, norm_neg, Complex.norm_I, ENNReal.ofReal_one]

/-- `x ≤ y` from `xⁿ ≤ yⁿ` in `ℝ≥0∞`. -/
theorem enn_le_of_pow_le {x y : ℝ≥0∞} {n : ℕ} (hn : n ≠ 0) (h : x ^ n ≤ y ^ n) : x ≤ y := by
  have := ENNReal.rpow_le_rpow h (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)
  rwa [ENNReal.pow_rpow_inv_natCast hn, ENNReal.pow_rpow_inv_natCast hn] at this

theorem eLpNorm_rpow_eq_lintegral {α : Type*} [MeasurableSpace α] {ν : Measure α} {f : α → ℂ}
    (hf : AEStronglyMeasurable f ν) {q : ℝ} (hq : 0 < q) :
    eLpNorm f (ENNReal.ofReal q) ν ^ q = ∫⁻ a, ‖f a‖ₑ ^ q ∂ν := by
  rw [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.2 hq).ne' ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hq.le, lintegral_rpow_enorm_eq_rpow_eLpNorm' hq]

theorem four_thirds_eq : (4 / 3 : ℝ≥0∞) = ENNReal.ofReal (4 / 3) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]
  simp

/-- The iterated `L^{4/3}` integral of a dense forcing is `‖G‖_{L^{4/3}}^{4/3}`. -/
theorem lintegral_dense_four_thirds (S : Finset ℤ) (G : ℤ → 𝓢(ℝ, ℂ)) :
    (∫⁻ t, ∫⁻ x, ‖denseField S G t x‖ₑ ^ (4 / 3 : ℝ) ∂AddCircle.haarAddCircle) ^ (3 / 2 : ℝ) =
      eLpNorm (denseSp S G) (4 / 3) stMeasure ^ 2 := by
  have hm : AEMeasurable (fun p => ‖denseSp S G p‖ₑ ^ (4 / 3 : ℝ)) stMeasure :=
    ((continuous_denseSp S G).measurable.enorm.pow_const _).aemeasurable
  have h1 : ∫⁻ t, ∫⁻ x, ‖denseField S G t x‖ₑ ^ (4 / 3 : ℝ) ∂AddCircle.haarAddCircle =
      ∫⁻ p, ‖denseSp S G p‖ₑ ^ (4 / 3 : ℝ) ∂stMeasure :=
    (lintegral_prod _ hm).symm
  rw [h1, ← eLpNorm_rpow_eq_lintegral (continuous_denseSp S G).aestronglyMeasurable (by norm_num),
    ← four_thirds_eq, ← ENNReal.rpow_mul, ← ENNReal.rpow_two]
  norm_num

theorem ofReal_rpow_sixteenth_pow {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) :
    ENNReal.ofReal (δ ^ (1 / 16 : ℝ)) ^ n = ENNReal.ofReal (δ ^ ((n : ℝ) / 16)) := by
  rw [← ENNReal.ofReal_pow (Real.rpow_nonneg hδ _), ← Real.rpow_natCast, ← Real.rpow_mul hδ]
  congr 2
  ring

/-- **Dense short-time trace bound**: `‖dField δ S G t‖_{L²} ≤ K δ^{1/16} ‖G‖_{L^{4/3}}`. -/
theorem dField_trace : ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ δ : ℝ, 0 < δ → ∀ (S : Finset ℤ) (G : ℤ → 𝓢(ℝ, ℂ)),
    (∀ k ∉ S, G k = 0) → ∀ t : ℝ,
      ‖dField δ S G t‖ₑ ≤ K * ENNReal.ofReal (δ ^ (1 / 16 : ℝ)) *
        eLpNorm (denseSp S G) (4 / 3) stMeasure := by
  obtain ⟨C, hC, h⟩ := dense_short_time_trace etaS
  refine ⟨C ^ ((2 : ℕ)⁻¹ : ℝ), ENNReal.rpow_ne_top_of_nonneg (by norm_num) hC,
    fun δ hδ S G hG t => enn_le_of_pow_le two_ne_zero ?_⟩
  have hws : AEStronglyMeasurable (fun x => wOut δ S G (t, x)) spatialMeasure :=
    ((continuous_wOut δ S G).comp (Continuous.prodMk_right t)).aestronglyMeasurable
  have hL : ‖dField δ S G t‖ₑ ^ 2 =
      ∫⁻ x, ‖denseField S (dOut δ G) t x‖ₑ ^ 2 ∂AddCircle.haarAddCircle := by
    rw [Lp.enorm_def, eLpNorm_congr_ae (dField_ae δ S G t)]
    have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
    rw [h2, ← ENNReal.rpow_two, eLpNorm_rpow_eq_lintegral hws (by norm_num)]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.rpow_two, wOut, enorm_mul, enorm_negI, one_mul]
    rfl
  rw [hL, mul_pow, mul_pow, ENNReal.rpow_inv_natCast_pow two_ne_zero,
    ofReal_rpow_sixteenth_pow hδ.le, mul_assoc, ← lintegral_dense_four_thirds]
  refine (h δ hδ S G hG t).trans_eq ?_
  norm_num

/-- **Dense short-time `L⁴(ℝ × 𝕋)` bound**: `‖wOut δ S G‖_{L⁴} ≤ K δ^{1/16} ‖G‖_{L^{4/3}}`. -/
theorem wOut_L4 : ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ δ : ℝ, 0 < δ → ∀ (S : Finset ℤ) (G : ℤ → 𝓢(ℝ, ℂ)),
    (∀ k ∉ S, G k = 0) →
      eLpNorm (wOut δ S G) 4 stMeasure ≤ K * ENNReal.ofReal (δ ^ (1 / 16 : ℝ)) *
        eLpNorm (denseSp S G) (4 / 3) stMeasure := by
  obtain ⟨C, hC, h⟩ := dense_short_time_L4 etaS
  refine ⟨C ^ ((4 : ℕ)⁻¹ : ℝ), ENNReal.rpow_ne_top_of_nonneg (by norm_num) hC,
    fun δ hδ S G hG => enn_le_of_pow_le four_ne_zero ?_⟩
  have hm : AEMeasurable (fun p => ‖wOut δ S G p‖ₑ ^ (4 : ℝ)) stMeasure :=
    ((continuous_wOut δ S G).measurable.enorm.pow_const _).aemeasurable
  have hL : eLpNorm (wOut δ S G) 4 stMeasure ^ 4 =
      ∫⁻ t, ∫⁻ x, ‖denseField S (dOut δ G) t x‖ₑ ^ 4 ∂AddCircle.haarAddCircle := by
    have h4 : (4 : ℝ≥0∞) = ENNReal.ofReal 4 := by simp
    rw [h4, ← ENNReal.rpow_natCast, show ((4 : ℕ) : ℝ) = 4 by norm_num,
      eLpNorm_rpow_eq_lintegral (continuous_wOut δ S G).aestronglyMeasurable (by norm_num),
      lintegral_prod _ hm]
    refine lintegral_congr fun t => lintegral_congr fun x => ?_
    rw [← ENNReal.rpow_natCast, wOut, enorm_mul, enorm_negI, one_mul]
    norm_num
    rfl
  rw [hL, mul_pow, mul_pow, ENNReal.rpow_inv_natCast_pow four_ne_zero,
    ofReal_rpow_sixteenth_pow hδ.le]
  calc ∫⁻ t, ∫⁻ x, ‖denseField S (dOut δ G) t x‖ₑ ^ 4 ∂AddCircle.haarAddCircle
      ≤ C * (ENNReal.ofReal (δ ^ (1 / 8 : ℝ)) *
          (∫⁻ t, ∫⁻ x, ‖denseField S G t x‖ₑ ^ (4 / 3 : ℝ) ∂AddCircle.haarAddCircle) ^
            (3 / 2 : ℝ)) ^ 2 := h δ hδ S G hG
    _ = C * ENNReal.ofReal (δ ^ (((4 : ℕ) : ℝ) / 16)) *
          eLpNorm (denseSp S G) (4 / 3) stMeasure ^ 4 := by
        rw [lintegral_dense_four_thirds, mul_pow, ← pow_mul,
          ← ENNReal.ofReal_pow (Real.rpow_nonneg hδ.le _), ← Real.rpow_natCast,
          ← Real.rpow_mul hδ.le, mul_assoc]
        norm_num

theorem denseSp_sub_union {S S' : Finset ℤ} {G G' : ℤ → 𝓢(ℝ, ℂ)} (hG : ∀ k ∉ S, G k = 0)
    (hG' : ∀ k ∉ S', G' k = 0) :
    denseSp (S ∪ S') (G - G') = denseSp S G - denseSp S' G' := by
  funext p
  have e1 : ∑ k ∈ S ∪ S', G k p.1 * fourier k p.2 = ∑ k ∈ S, G k p.1 * fourier k p.2 :=
    (Finset.sum_subset Finset.subset_union_left fun k _ hk => by simp [hG k hk]).symm
  have e2 : ∑ k ∈ S ∪ S', G' k p.1 * fourier k p.2 = ∑ k ∈ S', G' k p.1 * fourier k p.2 :=
    (Finset.sum_subset Finset.subset_union_right fun k _ hk => by simp [hG' k hk]).symm
  rw [Pi.sub_apply, denseSp_apply, denseSp_apply, denseSp_apply, ← e1, ← e2,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.sub_apply, _root_.sub_apply, sub_mul]

theorem sub_zero_off {S S' : Finset ℤ} {G G' : ℤ → 𝓢(ℝ, ℂ)} (hG : ∀ k ∉ S, G k = 0)
    (hG' : ∀ k ∉ S', G' k = 0) : ∀ k ∉ S ∪ S', (G - G') k = 0 := fun k hk => by
  rw [Finset.mem_union, not_or] at hk
  rw [Pi.sub_apply, hG k hk.1, hG' k hk.2, sub_zero]

theorem wOut_sub (δ : ℝ) {S S' : Finset ℤ} {G G' : ℤ → 𝓢(ℝ, ℂ)} (hG : ∀ k ∉ S, G k = 0)
    (hG' : ∀ k ∉ S', G' k = 0) :
    wOut δ (S ∪ S') (G - G') = wOut δ S G - wOut δ S' G' := by
  have hd : dOut δ (G - G') = dOut δ G - dOut δ G' := by
    funext k; ext t; rw [dOut_sub_apply, Pi.sub_apply, _root_.sub_apply]
  funext p
  rw [wOut, hd, denseSp_sub_union (fun k hk => dOut_eq_zero (hG k hk))
    (fun k hk => dOut_eq_zero (hG' k hk)), Pi.sub_apply, Pi.sub_apply, wOut, wOut, mul_sub]

theorem dField_sub (δ : ℝ) {S S' : Finset ℤ} {G G' : ℤ → 𝓢(ℝ, ℂ)} (hG : ∀ k ∉ S, G k = 0)
    (hG' : ∀ k ∉ S', G' k = 0) (t : ℝ) :
    dField δ (S ∪ S') (G - G') t = dField δ S G t - dField δ S' G' t := by
  refine Lp.ext ?_
  filter_upwards [dField_ae δ (S ∪ S') (G - G') t, Lp.coeFn_sub (dField δ S G t) (dField δ S' G' t),
    dField_ae δ S G t, dField_ae δ S' G' t] with x h1 h2 h3 h4
  rw [h1, h2, Pi.sub_apply, h3, h4, wOut_sub δ hG hG', Pi.sub_apply]

theorem continuous_dField (δ : ℝ) (S : Finset ℤ) (G : ℤ → 𝓢(ℝ, ℂ)) : Continuous (dField δ S G) := by
  have h : dField δ S G = fun t => ∑ k ∈ S, (-Complex.I * dOut δ G k t) •
      ContinuousMap.toLp 2 spatialMeasure ℂ (fourier k : C(PhysicalCircle, ℂ)) := by
    funext t
    simp only [dField, torusPoly, map_sum, map_smul]
  rw [h]
  exact continuous_finsetSum _ fun k _ =>
    (continuous_const.mul (dOut δ G k).continuous).smul continuous_const

end LiebLiniger.FixedPeriod.ALLS.PdeB
