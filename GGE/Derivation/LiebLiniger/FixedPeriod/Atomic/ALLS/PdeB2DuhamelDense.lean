import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB2DuhamelFourier

/-! # Track B, step B2: the dense-class fixed-cutoff Duhamel estimate and its assembly

* `dense_duhamel_bound` (Pro's eq:duhamel, `1/2 < c ≤ 1`, dense class): for the mode-wise
  fixed-cutoff Duhamel output `h_k(t) = η(t) ∫₀ᵗ e^{-i(2πk)²(t-r)} F_k(r) dr`,
  `‖h‖²_{X^{0,c}} ≤ C ‖F‖²_{X^{0,c-1}}`, uniformly in `F`.
* `dense_short_time_duhamel`: with the forcing cutoff `η(·/δ)` (`δ > 0`), `b = 17/32`,
  `α = 13/32`, `β = 15/32`: `‖h‖²_{X^{0,b}} ≤ C δ^{1/8} ‖F‖³_{L^{4/3}(ℝ×𝕋)}`
  (Duhamel, cutoff gain, `L^{4/3} → X^{0,-α}` duality), and the resulting `L⁴(ℝ×𝕋)` and
  `sup_t L²(𝕋)` bounds (`dense_short_time_L4`, `dense_short_time_trace`).
All norms are the `ℝ≥0∞` dense-class norms (squared, resp. fourth powers).
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.ALLS.PdeB

open MeasureTheory SchwartzMap FourierTransform AddCircle
open scoped ENNReal

theorem modWt_eq_bw (e : ℝ) (k : ℤ) (ξ : ℝ) :
    modWt e k (-(2 * Real.pi) * ξ) = bw e (ξ - (2 * Real.pi * k) ^ 2 / (2 * Real.pi)) := by
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  have ha : 2 * Real.pi * ((2 * Real.pi * k) ^ 2 / (2 * Real.pi)) = (2 * Real.pi * k) ^ 2 := by
    rw [mul_comm]
    exact div_mul_cancel₀ _ hπ
  have h : 2 * Real.pi * (ξ - (2 * Real.pi * k) ^ 2 / (2 * Real.pi)) =
      -(-(2 * Real.pi) * ξ + (2 * Real.pi * k) ^ 2) := by
    rw [mul_sub, ha]
    ring
  rw [modWt, bw, h, brk_neg]

theorem modWt_mono {e e' : ℝ} (h : e ≤ e') (k : ℤ) (t : ℝ) : modWt e k t ≤ modWt e' k t :=
  ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le (one_le_brk _) h)

theorem denseNormSqE_mono {e e' : ℝ} (h : e ≤ e') (s : ℤ → 𝓢(ℝ, ℂ)) :
    denseNormSqE e s ≤ denseNormSqE e' s :=
  ENNReal.tsum_le_tsum fun k => lintegral_mono fun _ => enn_mul_le_right (modWt_mono h k _) _

/-- One frequency shift `λ`: the scalar fixed-cutoff Duhamel estimate on Schwartz functions. -/
theorem duhamel_shift_bound {c : ℝ} (hc : 1 / 2 < c) (hc1 : c ≤ 1) (η : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (lam : ℝ) (g : 𝓢(ℝ, ℂ)),
      ∫⁻ ξ, bw (2 * c) (ξ - lam / (2 * Real.pi)) *
          ‖(𝓕⁻ (duhOut η lam g) : 𝓢(ℝ, ℂ)) ξ‖ₑ ^ 2 ≤
        C * ∫⁻ ζ, bw (2 * (c - 1)) (ζ - lam / (2 * Real.pi)) * ‖(𝓕⁻ g : 𝓢(ℝ, ℂ)) ζ‖ₑ ^ 2 := by
  obtain ⟨C, hC, h⟩ := duhamel_kernel_bound hc hc1 (𝓕⁻ η : 𝓢(ℝ, ℂ))
  refine ⟨C, hC, fun lam g => ?_⟩
  have hθ : Measurable fun z => (𝓕⁻ g : 𝓢(ℝ, ℂ)) (z + lam / (2 * Real.pi)) :=
    ((𝓕⁻ g : 𝓢(ℝ, ℂ)).continuous.comp (continuous_id.add continuous_const)).measurable
  have h1 := h (fun z => (𝓕⁻ g : 𝓢(ℝ, ℂ)) (z + lam / (2 * Real.pi))) hθ
  calc ∫⁻ ξ, bw (2 * c) (ξ - lam / (2 * Real.pi)) *
        ‖(𝓕⁻ (duhOut η lam g) : 𝓢(ℝ, ℂ)) ξ‖ₑ ^ 2
      ≤ ∫⁻ ξ, bw (2 * c) (ξ - lam / (2 * Real.pi)) *
          (∫⁻ z, ‖duhKer (𝓕⁻ η : 𝓢(ℝ, ℂ)) (ξ - lam / (2 * Real.pi)) z‖ₑ *
            ‖(𝓕⁻ g : 𝓢(ℝ, ℂ)) (z + lam / (2 * Real.pi))‖ₑ) ^ 2 := by
        refine lintegral_mono fun ξ => ?_
        gcongr
        exact enorm_fourierInv_duhOut_le η lam g ξ
    _ = ∫⁻ x, bw (2 * c) x * (∫⁻ z, ‖duhKer (𝓕⁻ η : 𝓢(ℝ, ℂ)) x z‖ₑ *
            ‖(𝓕⁻ g : 𝓢(ℝ, ℂ)) (z + lam / (2 * Real.pi))‖ₑ) ^ 2 :=
        lintegral_sub_right_eq_self (fun x => bw (2 * c) x *
          (∫⁻ z, ‖duhKer (𝓕⁻ η : 𝓢(ℝ, ℂ)) x z‖ₑ *
            ‖(𝓕⁻ g : 𝓢(ℝ, ℂ)) (z + lam / (2 * Real.pi))‖ₑ) ^ 2) (lam / (2 * Real.pi))
    _ ≤ C * ∫⁻ z, bw (2 * (c - 1)) z * ‖(𝓕⁻ g : 𝓢(ℝ, ℂ)) (z + lam / (2 * Real.pi))‖ₑ ^ 2 := h1
    _ = C * ∫⁻ ζ, bw (2 * (c - 1)) (ζ - lam / (2 * Real.pi)) * ‖(𝓕⁻ g : 𝓢(ℝ, ℂ)) ζ‖ₑ ^ 2 := by
        congr 1
        rw [← lintegral_sub_right_eq_self (fun z => bw (2 * (c - 1)) z *
          ‖(𝓕⁻ g : 𝓢(ℝ, ℂ)) (z + lam / (2 * Real.pi))‖ₑ ^ 2) (lam / (2 * Real.pi))]
        simp only [sub_add_cancel]

/-- **Fixed-cutoff Duhamel estimate on the dense class** (`1/2 < c ≤ 1`):
`‖η(t) ∫₀ᵗ U(t-r) F(r) dr‖²_{X^{0,c}} ≤ C ‖F‖²_{X^{0,c-1}}`, mode by mode with `λ_k = (2πk)²`. -/
theorem dense_duhamel_bound {c : ℝ} (hc : 1 / 2 < c) (hc1 : c ≤ 1) (η : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ F : ℤ → 𝓢(ℝ, ℂ),
      denseNormSqE (2 * c) (fun k => duhOut η ((2 * Real.pi * k) ^ 2) (F k)) ≤
        C * denseNormSqE (2 * (c - 1)) F := by
  obtain ⟨C, hC, h⟩ := duhamel_shift_bound hc hc1 η
  refine ⟨C, hC, fun F => ?_⟩
  unfold denseNormSqE
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun k => ?_
  simp only [modWt_eq_bw]
  exact h _ (F k)

theorem duhOut_cutMul_zero (η c : 𝓢(ℝ, ℂ)) (lam : ℝ) : duhOut η lam (cutMul c 0) = 0 := by
  ext t
  rw [duhOut_apply]
  simp [cutMul_apply]

/-- **Short-time Duhamel estimate on the dense class, `X^{0,b}` form** (`b = 17/32`):
`‖h‖²_{X^{0,b}} ≤ C δ^{1/8} (∫∫ |F|^{4/3})^{3/2}` for the fixed-cutoff Duhamel output `h` of the
cut-off forcing `η(·/δ) F`, uniformly in `δ > 0` and the dense forcing `F`. -/
theorem dense_short_time_duhamel (η : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ δ : ℝ, 0 < δ → ∀ (S : Finset ℤ) (F : ℤ → 𝓢(ℝ, ℂ)),
      (∀ k ∉ S, F k = 0) →
      denseNormSqE (2 * (17 / 32 : ℝ))
          (fun k => duhOut η ((2 * Real.pi * k) ^ 2) (cutMul (dilateS η δ) (F k))) ≤
        C * ENNReal.ofReal (δ ^ (1 / 8 : ℝ)) *
          (∫⁻ t, ∫⁻ x, ‖denseField S F t x‖ₑ ^ (4 / 3 : ℝ) ∂haarAddCircle) ^ (3 / 2 : ℝ) := by
  obtain ⟨C1, hC1, h1⟩ := dense_duhamel_bound (c := 17 / 32) (by norm_num) (by norm_num) η
  obtain ⟨C2, hC2, h2⟩ := dense_cutoff_gain (α := 13 / 32) (β := 15 / 32) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) η
  obtain ⟨C3, hC3, h3⟩ := dense_dual_bound
  refine ⟨C1 * C2 * C3, ENNReal.mul_ne_top (ENNReal.mul_ne_top hC1 hC2) hC3,
    fun δ hδ S F hF => ?_⟩
  have e1 : (2 * ((17 / 32 : ℝ) - 1)) = -(2 * (15 / 32 : ℝ)) := by norm_num
  have e2 : (2 * (15 / 32 : ℝ) - 2 * (13 / 32)) = 1 / 8 := by norm_num
  calc denseNormSqE (2 * (17 / 32 : ℝ))
        (fun k => duhOut η ((2 * Real.pi * k) ^ 2) (cutMul (dilateS η δ) (F k)))
      ≤ C1 * denseNormSqE (2 * ((17 / 32 : ℝ) - 1)) (fun k => cutMul (dilateS η δ) (F k)) :=
        h1 _
    _ = C1 * denseNormSqE (-(2 * (15 / 32 : ℝ))) (fun k => cutMul (dilateS η δ) (F k)) := by
        rw [e1]
    _ ≤ C1 * (C2 * ENNReal.ofReal (δ ^ (2 * (15 / 32 : ℝ) - 2 * (13 / 32))) *
          denseNormSqE (-(2 * (13 / 32 : ℝ))) F) :=
        enn_mul_le_left (h2 δ hδ F) _
    _ ≤ C1 * (C2 * ENNReal.ofReal (δ ^ (1 / 8 : ℝ)) *
          (C3 * (∫⁻ t, ∫⁻ x, ‖denseField S F t x‖ₑ ^ (4 / 3 : ℝ) ∂haarAddCircle) ^
            (3 / 2 : ℝ))) := by
        rw [e2]
        exact enn_mul_le_left (enn_mul_le_left (h3 S F hF) _) _
    _ = _ := by ring

/-- **Short-time Duhamel estimate, `L⁴(ℝ × 𝕋)` part** (fourth powers):
`∫∫ |h|⁴ ≤ C (δ^{1/8} (∫∫ |F|^{4/3})^{3/2})²`, i.e. `‖h‖_{L⁴} ≤ C' δ^{1/16} ‖F‖_{L^{4/3}}`. -/
theorem dense_short_time_L4 (η : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ δ : ℝ, 0 < δ → ∀ (S : Finset ℤ) (F : ℤ → 𝓢(ℝ, ℂ)),
      (∀ k ∉ S, F k = 0) →
      ∫⁻ t, ∫⁻ x, ‖denseField S
          (fun k => duhOut η ((2 * Real.pi * k) ^ 2) (cutMul (dilateS η δ) (F k))) t x‖ₑ ^ 4
            ∂haarAddCircle ≤
        C * (ENNReal.ofReal (δ ^ (1 / 8 : ℝ)) *
          (∫⁻ t, ∫⁻ x, ‖denseField S F t x‖ₑ ^ (4 / 3 : ℝ) ∂haarAddCircle) ^ (3 / 2 : ℝ)) ^ 2 := by
  obtain ⟨C0, hC0, h0⟩ := dense_short_time_duhamel η
  obtain ⟨K, hK, hL4⟩ := dense_L4_bound
  refine ⟨K * C0 ^ 2, ENNReal.mul_ne_top hK (ENNReal.pow_ne_top hC0), fun δ hδ S F hF => ?_⟩
  have hmodes : ∀ k ∉ S,
      (fun k : ℤ => duhOut η ((2 * Real.pi * k) ^ 2) (cutMul (dilateS η δ) (F k))) k = 0 :=
    fun k hk => by beta_reduce; rw [hF k hk, duhOut_cutMul_zero]
  calc ∫⁻ t, ∫⁻ x, ‖denseField S
          (fun k => duhOut η ((2 * Real.pi * k) ^ 2) (cutMul (dilateS η δ) (F k))) t x‖ₑ ^ 4
            ∂haarAddCircle
      ≤ K * denseNormSq
          (fun k => duhOut η ((2 * Real.pi * k) ^ 2) (cutMul (dilateS η δ) (F k))) ^ 2 :=
        hL4 S _ hmodes
    _ ≤ K * denseNormSqE (2 * (17 / 32 : ℝ))
          (fun k => duhOut η ((2 * Real.pi * k) ^ 2) (cutMul (dilateS η δ) (F k))) ^ 2 := by
        rw [denseNormSq_eq_denseNormSqE]
        exact enn_mul_le_left (pow_le_pow_left₀ bot_le (denseNormSqE_mono (by norm_num) _) 2) _
    _ ≤ K * (C0 * ENNReal.ofReal (δ ^ (1 / 8 : ℝ)) *
          (∫⁻ t, ∫⁻ x, ‖denseField S F t x‖ₑ ^ (4 / 3 : ℝ) ∂haarAddCircle) ^ (3 / 2 : ℝ)) ^ 2 :=
        enn_mul_le_left (pow_le_pow_left₀ bot_le (h0 δ hδ S F hF) 2) _
    _ = _ := by ring

/-- **Short-time Duhamel estimate, `sup_t L²(𝕋)` part** (squares). -/
theorem dense_short_time_trace (η : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ δ : ℝ, 0 < δ → ∀ (S : Finset ℤ) (F : ℤ → 𝓢(ℝ, ℂ)),
      (∀ k ∉ S, F k = 0) → ∀ t : ℝ,
      ∫⁻ x, ‖denseField S
          (fun k => duhOut η ((2 * Real.pi * k) ^ 2) (cutMul (dilateS η δ) (F k))) t x‖ₑ ^ 2
            ∂haarAddCircle ≤
        C * (ENNReal.ofReal (δ ^ (1 / 8 : ℝ)) *
          (∫⁻ t, ∫⁻ x, ‖denseField S F t x‖ₑ ^ (4 / 3 : ℝ) ∂haarAddCircle) ^ (3 / 2 : ℝ)) := by
  obtain ⟨C0, hC0, h0⟩ := dense_short_time_duhamel η
  obtain ⟨Ct, hCt, htr⟩ := dense_trace_bound (c := 17 / 32) (by norm_num)
  refine ⟨Ct * C0, ENNReal.mul_ne_top hCt hC0, fun δ hδ S F hF t => ?_⟩
  have hmodes : ∀ k ∉ S,
      (fun k : ℤ => duhOut η ((2 * Real.pi * k) ^ 2) (cutMul (dilateS η δ) (F k))) k = 0 :=
    fun k hk => by beta_reduce; rw [hF k hk, duhOut_cutMul_zero]
  calc ∫⁻ x, ‖denseField S
          (fun k => duhOut η ((2 * Real.pi * k) ^ 2) (cutMul (dilateS η δ) (F k))) t x‖ₑ ^ 2
            ∂haarAddCircle
      ≤ Ct * denseNormSqE (2 * (17 / 32 : ℝ))
          (fun k => duhOut η ((2 * Real.pi * k) ^ 2) (cutMul (dilateS η δ) (F k))) :=
        htr S _ hmodes t
    _ ≤ Ct * (C0 * ENNReal.ofReal (δ ^ (1 / 8 : ℝ)) *
          (∫⁻ t, ∫⁻ x, ‖denseField S F t x‖ₑ ^ (4 / 3 : ℝ) ∂haarAddCircle) ^ (3 / 2 : ℝ)) :=
        enn_mul_le_left (h0 δ hδ S F hF) _
    _ = _ := by ring

end LiebLiniger.FixedPeriod.ALLS.PdeB
