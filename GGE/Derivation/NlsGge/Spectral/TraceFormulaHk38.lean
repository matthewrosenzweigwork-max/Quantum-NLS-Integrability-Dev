import NlsGge.Spectral.TraceFormulaLowerOrder38
import NlsGge.Spectral.NonlinearRemainderDensity38
import NlsGge.Spectral.ActualQuasimomentumDecayE02_38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis NlsGge.HierarchyRiccati.Core NlsGge.Sobolev38

/-! # R4 (TF-H^k): the trace formula `M_{2k} = Q_{2k}` on `H^k`, conditional on R3c

Also the cross-`m` consistency of the charge extension `chargeSobolev38 m j`. -/

/-- **Cross-`m` consistency.** For `2 ≤ m ≤ m'` and `j ≤ m - 1`, the charge extensions at the two ambient
Sobolev orders agree on elements with the same Fourier coefficients. -/
theorem chargeSobolev38_cross_m (m m' j : ℕ) (hm : 2 ≤ m) (hmm : m ≤ m') (hj : j ≤ m - 1)
    (y : SobolevHilbert ((m' - 1 : ℕ) : ℝ)) (y' : SobolevHilbert ((m - 1 : ℕ) : ℝ))
    (h : ∀ n : ℤ,
      (show WeightedHilbert (sobolevModeWeight ((m' - 1 : ℕ) : ℝ)) from y) n =
      (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from y') n) :
    chargeSobolev38 m' j y = chargeSobolev38 m j y' := by
  have hT := tendsto_truncSobolev38 ((m' - 1 : ℕ) : ℝ) y
  have hT' := tendsto_truncSobolev38 ((m - 1 : ℕ) : ℝ) y'
  have h1 := ((continuous_chargeSobolev38 m' j (by omega)).tendsto y).comp hT
  have h2 := ((continuous_chargeSobolev38 m j hj).tendsto y').comp hT'
  refine tendsto_nhds_unique h1 (h2.congr fun N => ?_)
  simp only [Function.comp]
  rw [chargeSobolev38_trunc m j hm (by omega) N y', chargeSobolev38_trunc m' j (by omega) (by omega) N y]
  congr 2
  funext i
  exact (h _).symm

/-! ## Abstract monotone-convergence step -/

/-- The damping factor `η²/(t²+η²)` tends to `1` as `η → ∞`. -/
theorem damp_tendsto38 (t : ℝ) :
    Tendsto (fun η : ℝ => η ^ 2 / (t ^ 2 + η ^ 2)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun η : ℝ => t ^ 2 + η ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop (two_ne_zero))
  have h2 : Tendsto (fun η : ℝ => t ^ 2 / (t ^ 2 + η ^ 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop h1
  have h3 := (tendsto_const_nhds (x := (1:ℝ))).sub h2
  rw [sub_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with η hη
  have : 0 < t ^ 2 + η ^ 2 := by positivity
  field_simp
  ring

theorem damp_nonneg38 (t η : ℝ) : 0 ≤ η ^ 2 / (t ^ 2 + η ^ 2) := by positivity

theorem damp_le_one38 (t η : ℝ) (hη : η ≠ 0) : η ^ 2 / (t ^ 2 + η ^ 2) ≤ 1 := by
  have : 0 < t ^ 2 + η ^ 2 := by positivity
  rw [div_le_one this]; nlinarith [sq_nonneg t]

/-- Monotone convergence, in the form needed for R4: if the damped integrals of a nonnegative continuous
`f` converge to `L`, then `f` is integrable and `∫ f = L`. -/
theorem integrable_of_damped_tendsto38 (f : ℝ → ℝ) (hc : Continuous f) (h0 : ∀ t, 0 ≤ f t) (L : ℝ)
    (hA : ∀ η : ℝ, 0 < η → Integrable (fun t => f t * (η ^ 2 / (t ^ 2 + η ^ 2))))
    (hL : Tendsto (fun η : ℝ => ∫ t, f t * (η ^ 2 / (t ^ 2 + η ^ 2))) atTop (𝓝 L)) :
    Integrable f ∧ ∫ t, f t = L := by
  have hmeas : ∀ η : ℝ, AEStronglyMeasurable (fun t => f t * (η ^ 2 / (t ^ 2 + η ^ 2))) volume := by
    intro η
    have : Measurable (fun t : ℝ => f t * (η ^ 2 / (t ^ 2 + η ^ 2))) :=
      hc.measurable.mul (measurable_const.div (by fun_prop))
    exact this.aestronglyMeasurable
  have hbd : ∀ η : ℝ, 0 < η → ∀ t, ‖f t * (η ^ 2 / (t ^ 2 + η ^ 2))‖ ≤ f t := by
    intro η hη t
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (h0 t),
      abs_of_nonneg (damp_nonneg38 t η)]
    exact mul_le_of_le_one_right (h0 t) (damp_le_one38 t η hη.ne')
  have hpt : ∀ t : ℝ, Tendsto (fun η : ℝ => f t * (η ^ 2 / (t ^ 2 + η ^ 2))) atTop (𝓝 (f t)) := by
    intro t
    simpa using (damp_tendsto38 t).const_mul (f t)
  -- interval bound
  have hB : ∀ T : ℝ, 0 ≤ T → ∫ t in Icc (-T) T, f t ≤ L := by
    intro T hT
    have hIcc : IntegrableOn f (Icc (-T) T) := hc.continuousOn.integrableOn_Icc
    have hconv : Tendsto (fun η : ℝ => ∫ t in Icc (-T) T, f t * (η ^ 2 / (t ^ 2 + η ^ 2))) atTop
        (𝓝 (∫ t in Icc (-T) T, f t)) := by
      refine tendsto_integral_filter_of_dominated_convergence (fun t => f t) ?_ ?_ hIcc ?_
      · exact Eventually.of_forall fun η => (hmeas η).restrict
      · filter_upwards [eventually_gt_atTop 0] with η hη
        exact Eventually.of_forall fun t => hbd η hη t
      · exact Eventually.of_forall fun t => hpt t
    refine le_of_tendsto_of_tendsto hconv hL ?_
    filter_upwards [eventually_gt_atTop 0] with η hη
    exact setIntegral_le_integral (hA η hη) (Eventually.of_forall fun t => mul_nonneg (h0 t)
      (damp_nonneg38 t η))
  obtain ⟨hint, _⟩ := integrable_of_Icc_bound38 f hc h0 L hB
  refine ⟨hint, ?_⟩
  have hfull : Tendsto (fun η : ℝ => ∫ t, f t * (η ^ 2 / (t ^ 2 + η ^ 2))) atTop (𝓝 (∫ t, f t)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun t => f t) ?_ ?_ hint ?_
    · exact Eventually.of_forall fun η => hmeas η
    · filter_upwards [eventually_gt_atTop 0] with η hη
      exact Eventually.of_forall fun t => hbd η hη t
    · exact Eventually.of_forall fun t => hpt t
  exact tendsto_nhds_unique hfull hL

/-! ## Geometric expansion and the Herglotz identity on the imaginary axis -/

theorem geom_expand38 (k : ℕ) (η t : ℝ) (hη : 0 < η) :
    η / (t ^ 2 + η ^ 2) = ∑ j ∈ Finset.range k, (-1 : ℝ) ^ j * (t ^ (2 * j) / η ^ (2 * j + 1)) +
      (-1 : ℝ) ^ k * (t ^ (2 * k) / η ^ (2 * k + 1)) * (η ^ 2 / (t ^ 2 + η ^ 2)) := by
  have hd : 0 < t ^ 2 + η ^ 2 := by positivity
  induction k with
  | zero => simp; field_simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have h2 : (-1 : ℝ) ^ k * (t ^ (2 * k) / η ^ (2 * k + 1)) * (η ^ 2 / (t ^ 2 + η ^ 2)) =
        (-1 : ℝ) ^ k * (t ^ (2 * k) / η ^ (2 * k + 1)) +
        (-1 : ℝ) ^ (k + 1) * (t ^ (2 * (k + 1)) / η ^ (2 * (k + 1) + 1)) *
          (η ^ 2 / (t ^ 2 + η ^ 2)) := by
      field_simp
      ring
    rw [ih, h2]; ring

/-- Imaginary part of the Herglotz representation at `iη`. -/
theorem herglotz_im38 (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u))
    (η : ℝ) (hη : 0 < η) :
    Integrable (fun t : ℝ => actualGapHeightE02_38 u t * (η / (t ^ 2 + η ^ 2))) ∧
    (actualQuasimomentumE02_38 u (Complex.I * η)).im - η =
      (1 / Real.pi) * ∫ t : ℝ, actualGapHeightE02_38 u t * (η / (t ^ 2 + η ^ 2)) := by
  have hz : 0 < (Complex.I * (η : ℂ)).im := by simpa using hη
  obtain ⟨hint, heq⟩ := actualQuasimomentum_herglotz_E02_38 u hu _ hz
  have hpt : ∀ t : ℝ, ((actualGapHeightE02_38 u t : ℂ) / ((t : ℂ) - Complex.I * η)).im =
      actualGapHeightE02_38 u t * (η / (t ^ 2 + η ^ 2)) := by
    intro t
    have hd : 0 < t ^ 2 + η ^ 2 := by positivity
    have hne : ((t : ℂ) - Complex.I * η) ≠ 0 := by
      intro h
      have h1 := congrArg Complex.im h
      have h2 := congrArg Complex.re h
      simp at h1 h2
      linarith
    rw [Complex.div_im]
    simp [Complex.normSq_apply]
    field_simp
  have hint' := hint.im
  simp only [RCLike.im_to_complex] at hint'
  have hint2 : Integrable (fun t : ℝ => actualGapHeightE02_38 u t * (η / (t ^ 2 + η ^ 2))) := by
    refine hint'.congr (Eventually.of_forall fun t => ?_)
    exact hpt t
  refine ⟨hint2, ?_⟩
  have hIm := integral_im hint
  have h1 := congrArg Complex.im heq
  simp only [RCLike.im_to_complex] at hIm
  simp only [hpt] at hIm
  rw [Complex.add_im] at h1
  rw [h1]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  rw [← hIm]
  simp

/-! ## The main theorem -/

/-- **R4** (TF-H^k, conditional on the R3c hypothesis).  For `u ∈ H^k`, `k ≥ 1`, the `2k`-moment of the gap
height is finite and `(2/π) ∫ (2t)^{2k} v = Q_{2k}(u)`. -/
theorem actualTraceFormula_Hk38 (k : ℕ) (hk : 1 ≤ k) (hR3c : NonlinRiccatiSmoothBound38 k)
    (u : PhysicalL2) (y : SobolevHilbert ((k + 1 - 1 : ℕ) : ℝ))
    (hy : ∀ n : ℤ, (show WeightedHilbert (sobolevModeWeight ((k + 1 - 1 : ℕ) : ℝ)) from y) n =
      physicalFourier u n) :
    Integrable (fun t : ℝ => (2*t)^(2*k) * actualGapHeightE02_38 u t) ∧
    (2/Real.pi) * ∫ t : ℝ, (2*t)^(2*k) * actualGapHeightE02_38 u t =
      chargeSobolev38 (k + 1) k y := by
  have hpi := Real.pi_pos
  have hvc : Continuous (actualGapHeightE02_38 u) := continuous_actualGapHeightE02_38 u
  have hv0 : ∀ t, 0 ≤ actualGapHeightE02_38 u t := actualGapHeightE02_38_nonneg u
  have hu1 : SobolevSquareSummable 1 (physicalFourier u) :=
    hk_summable38 k u y hy hk u (fun _ => le_rfl)
  have hpow : ∀ (j : ℕ) (t : ℝ), (2*t)^(2*j) * actualGapHeightE02_38 u t =
      4^j * (t^(2*j) * actualGapHeightE02_38 u t) := by
    intro j t; rw [mul_pow, pow_mul]; norm_num; ring
  -- lower moments from R1
  have hlow : ∀ j : ℕ, j < k → Integrable (fun t : ℝ => t^(2*j) * actualGapHeightE02_38 u t) ∧
      ∫ t : ℝ, t^(2*j) * actualGapHeightE02_38 u t =
        (Real.pi / 2) * chargeSobolev38 (k+1) j y / 4^j := by
    intro j hj
    obtain ⟨hI, hE⟩ := actualTraceFormula_lower_E02_38 (k+1) u y hy j (by omega)
    simp only [hpow] at hI hE
    have h4 : (0:ℝ) < 4^j := by positivity
    refine ⟨?_, ?_⟩
    · have := hI.const_mul ((4:ℝ)^j)⁻¹
      refine this.congr (Eventually.of_forall fun t => ?_)
      simp only
      field_simp
    · rw [integral_const_mul] at hE
      field_simp
      field_simp at hE
      linarith
  have hRtend := nonlinRiccati38_full_remainder_tendsto k hk hR3c u y hy
  -- the damped moment identity
  have hid : ∀ η : ℝ, 0 < η →
      Integrable (fun t : ℝ => (t^(2*k) * actualGapHeightE02_38 u t) * (η ^ 2 / (t ^ 2 + η ^ 2))) ∧
      ∫ t : ℝ, (t^(2*k) * actualGapHeightE02_38 u t) * (η ^ 2 / (t ^ 2 + η ^ 2)) =
        (-1:ℝ)^k * η^(2*k+1) * (Real.pi * ((actualQuasimomentumE02_38 u (Complex.I * η)).im - η) -
          ∑ j ∈ Finset.range k, (-1:ℝ)^j * (1 / η^(2*j+1)) *
            ((Real.pi / 2) * chargeSobolev38 (k+1) j y / 4^j)) := by
    intro η hη
    obtain ⟨hgI, hgE⟩ := herglotz_im38 u hu1 η hη
    have hpt : ∀ t : ℝ, (t^(2*k) * actualGapHeightE02_38 u t) * (η ^ 2 / (t ^ 2 + η ^ 2)) =
        (-1:ℝ)^k * η^(2*k+1) * (actualGapHeightE02_38 u t * (η / (t ^ 2 + η ^ 2)) -
          ∑ j ∈ Finset.range k, (-1:ℝ)^j * (1 / η^(2*j+1)) *
            (t^(2*j) * actualGapHeightE02_38 u t)) := by
      intro t
      have hg := geom_expand38 k η t hη
      have hs : ∑ j ∈ Finset.range k, actualGapHeightE02_38 u t *
            ((-1 : ℝ) ^ j * (t ^ (2 * j) / η ^ (2 * j + 1))) =
          ∑ j ∈ Finset.range k, (-1:ℝ)^j * (1 / η^(2*j+1)) * (t^(2*j) * actualGapHeightE02_38 u t) :=
        Finset.sum_congr rfl (fun j _ => by ring)
      rw [hg, mul_add, Finset.mul_sum, hs, add_sub_cancel_left]
      have h1 : ((-1:ℝ)^k) * (-1)^k = 1 := by rw [← mul_pow]; norm_num
      have hη' : η ^ (2*k+1) ≠ 0 := by positivity
      have hd : 0 < t ^ 2 + η ^ 2 := by positivity
      generalize (-1:ℝ)^k = a at h1 ⊢
      generalize η ^ (2*k+1) = E at hη' ⊢
      have h2 : a * E * (actualGapHeightE02_38 u t * (a * (t ^ (2 * k) / E) * (η ^ 2 / (t ^ 2 + η ^ 2)))) =
          (a * a) * (t ^ (2 * k) * actualGapHeightE02_38 u t * (η ^ 2 / (t ^ 2 + η ^ 2))) := by
        field_simp
      rw [h2, h1, one_mul]
    have hsumI : Integrable (fun t : ℝ => ∑ j ∈ Finset.range k, (-1:ℝ)^j * (1 / η^(2*j+1)) *
        (t^(2*j) * actualGapHeightE02_38 u t)) :=
      integrable_finsetSum _ (fun j hj => (hlow j (Finset.mem_range.1 hj)).1.const_mul _)
    have hI : Integrable (fun t : ℝ => (t^(2*k) * actualGapHeightE02_38 u t) *
        (η ^ 2 / (t ^ 2 + η ^ 2))) := by
      simp only [hpt]
      exact (hgI.sub hsumI).const_mul _
    refine ⟨hI, ?_⟩
    simp only [hpt]
    rw [integral_const_mul, integral_sub hgI hsumI, integral_finsetSum _
      (fun j hj => (hlow j (Finset.mem_range.1 hj)).1.const_mul _)]
    have hsumeq : ∑ j ∈ Finset.range k, ∫ t : ℝ, (-1:ℝ)^j * (1 / η^(2*j+1)) *
        (t^(2*j) * actualGapHeightE02_38 u t) =
        ∑ j ∈ Finset.range k, (-1:ℝ)^j * (1 / η^(2*j+1)) *
          ((Real.pi / 2) * chargeSobolev38 (k+1) j y / 4^j) :=
      Finset.sum_congr rfl (fun j hj => by
        rw [integral_const_mul, (hlow j (Finset.mem_range.1 hj)).2])
    have hπ : Real.pi * (1 / Real.pi * ∫ t : ℝ, actualGapHeightE02_38 u t * (η / (t ^ 2 + η ^ 2))) =
        ∫ t : ℝ, actualGapHeightE02_38 u t * (η / (t ^ 2 + η ^ 2)) := by
      rw [← mul_assoc, mul_one_div_cancel hpi.ne', one_mul]
    rw [hsumeq, hgE, hπ]
  -- identification of the damped integral with the R3a remainder
  have hA : ∀ η : ℝ, 0 < η →
      ∫ t : ℝ, (t^(2*k) * actualGapHeightE02_38 u t) * (η ^ 2 / (t ^ 2 + η ^ 2)) =
        Real.pi * ((-1:ℝ)^k * (η ^ (2*k+1) *
          ((actualQuasimomentumE02_38 u (Complex.I * η)).im - η -
            ∑ j ∈ Finset.range (k + 1), (-1:ℝ)^j / (2 * 4^j * η^(2*j+1)) *
              chargeSobolev38 (k + 1) j y)) + chargeSobolev38 (k + 1) k y / (2 * 4^k)) := by
    intro η hη
    rw [(hid η hη).2, Finset.sum_range_succ]
    have hsum : ∑ j ∈ Finset.range k, (-1:ℝ)^j * (1 / η^(2*j+1)) *
        ((Real.pi / 2) * chargeSobolev38 (k+1) j y / 4^j) =
        Real.pi * ∑ j ∈ Finset.range k, (-1:ℝ)^j / (2 * 4^j * η^(2*j+1)) *
          chargeSobolev38 (k + 1) j y := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      field_simp
    rw [hsum]
    have h1 : ((-1:ℝ)^k) * (-1)^k = 1 := by rw [← mul_pow]; norm_num
    have hη' : η ^ (2*k+1) ≠ 0 := by positivity
    generalize (-1:ℝ)^k = a at h1 ⊢
    generalize η ^ (2*k+1) = E at hη' ⊢
    field_simp
    linear_combination (chargeSobolev38 (k + 1) k y) * h1
  -- the damped integrals converge to `π Q_k / (2·4^k)`
  have hlim : Tendsto (fun η : ℝ => ∫ t : ℝ, (t^(2*k) * actualGapHeightE02_38 u t) *
      (η ^ 2 / (t ^ 2 + η ^ 2))) atTop
      (𝓝 (Real.pi * (chargeSobolev38 (k + 1) k y / (2 * 4^k)))) := by
    have h0 := (hRtend.const_mul ((-1:ℝ)^k)).add_const (chargeSobolev38 (k + 1) k y / (2 * 4^k))
    have h1 := h0.const_mul Real.pi
    rw [mul_zero, zero_add] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with η hη
    exact (hA η hη).symm
  obtain ⟨hfI, hfE⟩ := integrable_of_damped_tendsto38
    (fun t : ℝ => t^(2*k) * actualGapHeightE02_38 u t)
    ((continuous_pow _).mul hvc) (fun t => mul_nonneg (by
      rw [pow_mul]; positivity) (hv0 t)) _ (fun η hη => (hid η hη).1) hlim
  have h4 : (0:ℝ) < 4^k := by positivity
  refine ⟨?_, ?_⟩
  · have := hfI.const_mul ((4:ℝ)^k)
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp only [hpow]
  · simp only [hpow]
    rw [integral_const_mul, hfE]
    field_simp

end NlsGge.SpectralFoundations
end
