import Mathlib
import QuantumNLS.Local007AlgB

/-! LOCAL-007 stage E1: the semicircle transform through the Cauchy formula (scalar part).

For `D` holomorphic near the closed disc `|z| ≤ c` and real `α, t` with `|α| + t < c`:
`∫_{-1}^{1} √(1-s²) D(α + t s) ds = (1/2π) ∫_0^{2π} ξ D(ξ) w⁻¹ M((t/w)²) dθ`, `ξ = c e^{iθ}`, `w = ξ - α`,
`M(x) = Σ cM_j x^j`, `cM_j = ∫_{-1}^1 s^{2j} √(1-s²) ds`.  (Kernel series + Cauchy + Fubini.) -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set Metric Complex
open scoped Interval
namespace QuantumNLS.Local007EvalS
open QuantumNLS.Local007AlgB (cM)

theorem odd_moment (j : ℕ) : ∫ s in (-1 : ℝ)..1, s ^ (2 * j + 1) * Real.sqrt (1 - s ^ 2) = 0 := by
  have h := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 1)
    (fun s : ℝ => s ^ (2 * j + 1) * Real.sqrt (1 - s ^ 2))
  simp only [neg_neg] at h
  have e : ∀ x : ℝ, (-x) ^ (2 * j + 1) * Real.sqrt (1 - (-x) ^ 2) = -(x ^ (2 * j + 1) * Real.sqrt (1 - x ^ 2)) := by
    intro x
    rw [neg_sq, Odd.neg_pow (by exact ⟨j, rfl⟩)]; ring
  simp only [e, intervalIntegral.integral_neg] at h
  linarith

theorem even_moment (j : ℕ) :
    ∫ s in (-1 : ℝ)..1, s ^ (2 * j) * Real.sqrt (1 - s ^ 2) = cM j := rfl

theorem kernel_series {w : ℂ} {t : ℝ} (hw : w ≠ 0) (ht : ‖(t : ℂ) / w‖ < 1) :
    ∫ s in (-1 : ℝ)..1, ((Real.sqrt (1 - s ^ 2) : ℝ) : ℂ) * (w - (t : ℂ) * (s : ℂ))⁻¹ =
      w⁻¹ * ∑' j : ℕ, (cM j : ℂ) * (((t : ℂ) / w) ^ 2) ^ j := by
  set q : ℂ := (t : ℂ) / w with hq
  have hq1 : ‖q‖ < 1 := ht
  let F : ℕ → ℝ → ℂ := fun k s => q ^ k * ((s ^ k * Real.sqrt (1 - s ^ 2) : ℝ) : ℂ)
  have hFm : ∀ k, AEStronglyMeasurable (F k) (volume.restrict (Ioc (-1 : ℝ) 1)) := fun k =>
    (by fun_prop : Continuous (F k)).aestronglyMeasurable
  have hFb : ∀ k, ∀ᵐ s ∂(volume.restrict (Ioc (-1 : ℝ) 1)), ‖F k s‖ ≤ ‖q‖ ^ k := by
    intro k
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have h1 : |s| ≤ 1 := abs_le.2 ⟨hs.1.le, hs.2⟩
    have h2 : Real.sqrt (1 - s ^ 2) ≤ 1 := by rw [Real.sqrt_le_one]; nlinarith [sq_nonneg s]
    change ‖q ^ k * ((s ^ k * Real.sqrt (1 - s ^ 2) : ℝ) : ℂ)‖ ≤ _
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    have h3 : |s| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg s) h1
    have h4 : |s| ^ k * Real.sqrt (1 - s ^ 2) ≤ 1 := by
      calc |s| ^ k * Real.sqrt (1 - s ^ 2) ≤ 1 * 1 := by gcongr
        _ = 1 := one_mul 1
    calc ‖q‖ ^ k * (|s| ^ k * Real.sqrt (1 - s ^ 2)) ≤ ‖q‖ ^ k * 1 := by gcongr
      _ = ‖q‖ ^ k := mul_one _
  have hlim : ∀ᵐ s ∂(volume.restrict (Ioc (-1 : ℝ) 1)),
      HasSum (fun k => F k s) (((Real.sqrt (1 - s ^ 2) : ℝ) : ℂ) * (1 - q * (s : ℂ))⁻¹) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have h1 : |s| ≤ 1 := abs_le.2 ⟨hs.1.le, hs.2⟩
    have hqs : ‖q * (s : ℂ)‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      nlinarith [norm_nonneg q, abs_nonneg s]
    have hg := (hasSum_geometric_of_norm_lt_one hqs).mul_left (((Real.sqrt (1 - s ^ 2) : ℝ) : ℂ))
    convert hg using 1
    funext k
    simp only [F]; push_cast; ring
  have hdom := hasSum_integral_of_dominated_convergence (μ := volume.restrict (Ioc (-1 : ℝ) 1))
    (fun k (_ : ℝ) => ‖q‖ ^ k) hFm hFb
    (ae_of_all _ fun _ => summable_geometric_of_lt_one (norm_nonneg _) hq1)
    (integrable_const _) hlim
  set μm : ℕ → ℝ := fun k => ∫ s in (-1 : ℝ)..1, s ^ k * Real.sqrt (1 - s ^ 2) with hμm
  have e1 : ∀ k, ∫ s in Ioc (-1 : ℝ) 1, F k s = q ^ k * (μm k : ℂ) := by
    intro k
    simp only [F]
    rw [integral_const_mul]
    congr 1
    rw [integral_complex_ofReal]
    show ((∫ a in Ioc (-1 : ℝ) 1, a ^ k * Real.sqrt (1 - a ^ 2) : ℝ) : ℂ) =
      ((∫ s in (-1 : ℝ)..1, s ^ k * Real.sqrt (1 - s ^ 2) : ℝ) : ℂ)
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have e2 : ∫ s in Ioc (-1 : ℝ) 1, ((Real.sqrt (1 - s ^ 2) : ℝ) : ℂ) * (1 - q * (s : ℂ))⁻¹ =
      ∫ s in (-1 : ℝ)..1, ((Real.sqrt (1 - s ^ 2) : ℝ) : ℂ) * (1 - q * (s : ℂ))⁻¹ :=
    (intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)).symm
  simp only [e1, e2] at hdom
  have hodd : ∀ j : ℕ, μm (2 * j + 1) = 0 := fun j => odd_moment j
  have hev : ∀ j : ℕ, μm (2 * j) = cM j := fun j => rfl
  have hinj : Function.Injective (fun j : ℕ => 2 * j) := fun a b h => by simpa using h
  have hzero : ∀ k ∉ Set.range (fun j : ℕ => 2 * j), q ^ k * (μm k : ℂ) = 0 := by
    intro k hk
    obtain ⟨j, hj⟩ := Nat.even_or_odd' k
    rcases hj with h | h
    · exact absurd ⟨j, h.symm⟩ hk
    · rw [h, hodd, Complex.ofReal_zero, mul_zero]
  have hH := (hinj.hasSum_iff hzero).2 hdom
  have hH' : HasSum (fun j : ℕ => (cM j : ℂ) * (q ^ 2) ^ j) (∫ s in (-1 : ℝ)..1,
      ((Real.sqrt (1 - s ^ 2) : ℝ) : ℂ) * (1 - q * (s : ℂ))⁻¹) := by
    convert hH using 1
    funext j
    simp only [Function.comp, hev, pow_mul]
    ring
  rw [hH'.tsum_eq]
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  have : (1 - q * (s : ℂ)) = (w - (t : ℂ) * (s : ℂ)) / w := by
    rw [hq]; field_simp
  rw [this, inv_div]
  field_simp


theorem cauchy_rep {c : ℝ} (hc : 0 < c) {D : ℂ → ℂ} (hD : DifferentiableOn ℂ D (closedBall 0 c)) {p : ℂ}
    (hp : ‖p‖ < c) :
    D p = (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
      circleMap 0 c θ * ((circleMap 0 c θ - p)⁻¹ * D (circleMap 0 c θ)) := by
  have hpb : p ∈ ball (0 : ℂ) c := by simpa using hp
  have h := circleIntegral_sub_inv_smul_of_differentiable_on_off_countable (c := (0 : ℂ)) (R := c) (w := p)
    (f := D) (s := ∅) countable_empty hpb hD.continuousOn (fun x hx => by
      refine hD.differentiableAt ?_
      exact Filter.mem_of_superset (isOpen_ball.mem_nhds hx.1) ball_subset_closedBall)
  unfold circleIntegral at h
  simp only [deriv_circleMap, smul_eq_mul] at h
  have e : ∀ θ : ℝ, circleMap 0 c θ * I * ((circleMap 0 c θ - p)⁻¹ * D (circleMap 0 c θ)) =
      I * (circleMap 0 c θ * ((circleMap 0 c θ - p)⁻¹ * D (circleMap 0 c θ))) := fun θ => by ring
  simp only [e] at h
  rw [intervalIntegral.integral_const_mul] at h
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have h2 : ∫ θ in (0 : ℝ)..(2 * Real.pi), circleMap 0 c θ * ((circleMap 0 c θ - p)⁻¹ * D (circleMap 0 c θ)) =
      (2 * Real.pi : ℂ) * D p := by
    have : I * (∫ θ in (0 : ℝ)..(2 * Real.pi), circleMap 0 c θ * ((circleMap 0 c θ - p)⁻¹ * D (circleMap 0 c θ))) =
        I * ((2 * Real.pi : ℂ) * D p) := by
      rw [h]; ring
    exact mul_left_cancel₀ hI this
  rw [h2]
  push_cast
  field_simp

theorem eval_scalar {c : ℝ} (hc : 0 < c) {D : ℂ → ℂ} (hD : DifferentiableOn ℂ D (closedBall 0 c))
    {α t : ℝ} (ht : 0 ≤ t) (hαt : |α| + t < c) :
    ∫ s in (-1 : ℝ)..1, ((Real.sqrt (1 - s ^ 2) : ℝ) : ℂ) * D ((α : ℂ) + (t : ℂ) * (s : ℂ)) =
      (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
        circleMap 0 c θ * D (circleMap 0 c θ) *
          ((circleMap 0 c θ - (α : ℂ))⁻¹ *
            ∑' j : ℕ, (cM j : ℂ) * (((t : ℂ) / (circleMap 0 c θ - (α : ℂ))) ^ 2) ^ j) := by
  set ξ : ℝ → ℂ := fun θ => circleMap 0 c θ with hξ
  have hξn : ∀ θ, ‖ξ θ‖ = c := fun θ => by simp [hξ, abs_of_pos hc]
  have hwn : ∀ θ, t < ‖ξ θ - (α : ℂ)‖ := by
    intro θ
    have h1 : ‖ξ θ‖ ≤ ‖ξ θ - (α : ℂ)‖ + ‖(α : ℂ)‖ := by
      calc ‖ξ θ‖ = ‖(ξ θ - (α : ℂ)) + (α : ℂ)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    rw [hξn, Complex.norm_real, Real.norm_eq_abs] at h1
    linarith
  have hw0 : ∀ θ, ξ θ - (α : ℂ) ≠ 0 := fun θ h => by
    have := hwn θ; rw [h, norm_zero] at this; linarith
  -- Cauchy representation for each s
  have hrep : ∀ s ∈ uIcc (-1 : ℝ) 1, ((Real.sqrt (1 - s ^ 2) : ℝ) : ℂ) * D ((α : ℂ) + (t : ℂ) * (s : ℂ)) =
      (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
        ((Real.sqrt (1 - s ^ 2) : ℝ) : ℂ) * (ξ θ * ((ξ θ - ((α : ℂ) + (t : ℂ) * (s : ℂ)))⁻¹ * D (ξ θ))) := by
    intro s hs
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hs
    have hp : ‖(α : ℂ) + (t : ℂ) * (s : ℂ)‖ < c := by
      calc ‖(α : ℂ) + (t : ℂ) * (s : ℂ)‖ ≤ ‖(α : ℂ)‖ + ‖(t : ℂ) * (s : ℂ)‖ := norm_add_le _ _
        _ ≤ |α| + t := by
          rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ht]
          have : |s| ≤ 1 := abs_le.2 ⟨hs.1, hs.2⟩
          nlinarith [abs_nonneg s]
        _ < c := hαt
    rw [cauchy_rep hc hD hp, intervalIntegral.integral_const_mul]
    ring
  rw [intervalIntegral.integral_congr hrep, intervalIntegral.integral_const_mul]
  congr 1
  -- Fubini
  let Fm : ℝ → ℝ → ℂ := fun s θ =>
    ((Real.sqrt (1 - s ^ 2) : ℝ) : ℂ) * (ξ θ * ((ξ θ - ((α : ℂ) + (t : ℂ) * (s : ℂ)))⁻¹ * D (ξ θ)))
  have hne : ∀ s ∈ Icc (-1 : ℝ) 1, ∀ θ : ℝ, ξ θ - ((α : ℂ) + (t : ℂ) * (s : ℂ)) ≠ 0 := by
    intro s hs θ h
    have h1 : ξ θ - (α : ℂ) = (t : ℂ) * (s : ℂ) := by linear_combination h
    have h2 := hwn θ
    rw [h1, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg ht] at h2
    have : |s| ≤ 1 := abs_le.2 ⟨hs.1, hs.2⟩
    nlinarith [abs_nonneg s]
  have hcont : ContinuousOn (Function.uncurry Fm) (Icc (-1 : ℝ) 1 ×ˢ Icc (0 : ℝ) (2 * Real.pi)) := by
    have hξc : Continuous ξ := by simp only [hξ]; exact continuous_circleMap 0 c
    have hDc : Continuous fun θ => D (ξ θ) := by
      have := hD.continuousOn.comp_continuous hξc (fun θ => by simp [hξ, abs_of_pos hc])
      exact this
    have hinv : ContinuousOn (fun q : ℝ × ℝ => (ξ q.2 - ((α : ℂ) + (t : ℂ) * (q.1 : ℂ)))⁻¹)
        (Icc (-1 : ℝ) 1 ×ˢ Icc (0 : ℝ) (2 * Real.pi)) := by
      refine ContinuousOn.inv₀ (by fun_prop) (fun q hq => hne q.1 hq.1 q.2)
    have h1 : Continuous fun q : ℝ × ℝ => ((Real.sqrt (1 - q.1 ^ 2) : ℝ) : ℂ) * ξ q.2 * D (ξ q.2) := by
      have : Continuous fun q : ℝ × ℝ => ((Real.sqrt (1 - q.1 ^ 2) : ℝ) : ℂ) := by fun_prop
      exact (this.mul (hξc.comp continuous_snd)).mul (hDc.comp continuous_snd)
    have := h1.continuousOn.mul hinv
    refine this.congr fun q _ => ?_
    change Fm q.1 q.2 = (((Real.sqrt (1 - q.1 ^ 2) : ℝ) : ℂ) * ξ q.2 * D (ξ q.2)) *
      (ξ q.2 - ((α : ℂ) + (t : ℂ) * (q.1 : ℂ)))⁻¹
    simp only [Fm]; ring
  have hint : IntegrableOn (Function.uncurry Fm) (uIoc (-1 : ℝ) 1 ×ˢ uIoc (0 : ℝ) (2 * Real.pi)) := by
    refine (hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set ?_
    rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1), uIoc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    exact prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self
  have hswap := MeasureTheory.intervalIntegral_intervalIntegral_swap (F := Fm) hint
  simp only [Fm] at hswap
  rw [hswap]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have hk := kernel_series (hw0 θ) (by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht, div_lt_one (lt_of_le_of_lt ht (hwn θ))]
    exact hwn θ)
  have e : ∀ s : ℝ, ((Real.sqrt (1 - s ^ 2) : ℝ) : ℂ) * (ξ θ * ((ξ θ - ((α : ℂ) + (t : ℂ) * (s : ℂ)))⁻¹ * D (ξ θ))) =
      (ξ θ * D (ξ θ)) * (((Real.sqrt (1 - s ^ 2) : ℝ) : ℂ) * ((ξ θ - (α : ℂ)) - (t : ℂ) * (s : ℂ))⁻¹) := by
    intro s
    have : ξ θ - ((α : ℂ) + (t : ℂ) * (s : ℂ)) = (ξ θ - (α : ℂ)) - (t : ℂ) * (s : ℂ) := by ring
    rw [this]; ring
  simp only [e]
  rw [intervalIntegral.integral_const_mul, hk]

end QuantumNLS.Local007EvalS
#print axioms QuantumNLS.Local007EvalS.eval_scalar
#print axioms QuantumNLS.Local007EvalS.cauchy_rep
