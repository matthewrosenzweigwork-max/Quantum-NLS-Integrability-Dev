import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB1L4Core
import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB1L4Time
import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB1Torus

/-! # Track B, step B1: `X^{0,a} ↪ L⁴(ℝ × 𝕋)` on the dense class

Dense class: a finite set `S ⊂ ℤ` and time-side Schwartz functions `s_k` (`s_k = 0` off `S`); the
spacetime field is `v(t,x) = Σ_{k∈S} s_k(t) e^{2πikx}` (a trigonometric polynomial in `x` for each
`t`). With `θ_k = 𝓕⁻ s_k` (Mathlib convention), the spacetime Fourier transform in Pro's
variables is `ṽ(τ,k) ∝ θ_k(-τ/2π)`, and the `X^{0,a}` norm is
`N(s) = Σ_k ∫ ⟨-2πξ + (2πk)²⟩^{2a} |θ_k(ξ)|² dξ` (Pro's norm up to the Jacobian `2π`).

Main result `dense_L4_bound`: one finite constant `K` with
`∫_ℝ ∫_𝕋 |v(t,x)|⁴ dx dt ≤ K · N(s)²` for every dense-class field (`a = 13/32`).
Proof: torus Parseval (`PdeB1Torus`), time Plancherel/convolution (`PdeB1L4Time`), the change of
variables `λ = -2πη`, and the Fourier-side bilinear estimate (`PdeB1L4Core`). Extended reals
throughout; integrability of the torus integrand is proved before the real/extended conversion.
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.ALLS.PdeB

open MeasureTheory SchwartzMap FourierTransform AddCircle
open scoped ENNReal

/-- Linear change of variables for lower integrals on `ℝ`: `∫ f(cx) dx = |c|⁻¹ ∫ f`. -/
theorem lintegral_comp_mul_left_real (f : ℝ → ℝ≥0∞) {c : ℝ} (hc : c ≠ 0) :
    ∫⁻ x, f (c * x) = ENNReal.ofReal |c⁻¹| * ∫⁻ x, f x := by
  calc ∫⁻ x, f (c * x) = ∫⁻ x, f x ∂(Measure.map (MeasurableEquiv.mulLeft₀ c hc) volume) :=
        (lintegral_map_equiv f (MeasurableEquiv.mulLeft₀ c hc)).symm
    _ = ∫⁻ x, f x ∂(ENNReal.ofReal |c⁻¹| • volume) := by
        congr 1
        exact Real.map_volume_mul_left hc
    _ = _ := lintegral_smul_measure _ _

/-- The dense-class spacetime field `v(t,x) = Σ_{k∈S} s_k(t) e_k(x)`. -/
def denseField (S : Finset ℤ) (s : ℤ → 𝓢(ℝ, ℂ)) (t : ℝ) (x : AddCircle (1 : ℝ)) : ℂ :=
  torusPoly S (fun k => s k t) x

/-- The `X^{0,a}` norm (squared) of a dense-class field, `a = 13/32`, in Mathlib's frequency variable. -/
def denseNormSq (s : ℤ → 𝓢(ℝ, ℂ)) : ℝ≥0∞ :=
  ∑' k : ℤ, ∫⁻ ξ, modWt (2 * (13 / 32 : ℝ)) k (-(2 * Real.pi) * ξ) * ‖(𝓕⁻ (s k)) ξ‖ₑ ^ 2

/-- Spatial step for each time: `∫_𝕋 |v(t,·)|⁴ = Σ_m |Σ_k s_k(t)s_{m-k}(t)|²`. -/
theorem lintegral_torus_denseField (S : Finset ℤ) (s : ℤ → 𝓢(ℝ, ℂ)) (hs : ∀ k ∉ S, s k = 0)
    (t : ℝ) :
    ∫⁻ x, ‖denseField S s t x‖ₑ ^ 4 ∂haarAddCircle =
      ∑' m : ℤ, ‖∑ k ∈ S, s k t * s (m - k) t‖ₑ ^ 2 := by
  have hc : ∀ k ∉ S, (fun k => s k t) k = 0 := fun k hk => by simp [hs k hk]
  have hint : Integrable (fun x => ‖denseField S s t x‖ ^ 4) haarAddCircle :=
    ((torusPoly S fun k => s k t).continuous.norm.pow 4).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsum : Summable fun m : ℤ => ‖∑ k ∈ S, s k t * s (m - k) t‖ ^ 2 := by
    refine summable_of_ne_finset_zero (s := (S ×ˢ S).image fun p => p.1 + p.2) fun m hm => ?_
    have : ∑ k ∈ S, s k t * s (m - k) t = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      have hmk : m - k ∉ S := fun h => hm (Finset.mem_image.2 ⟨(k, m - k),
        Finset.mem_product.2 ⟨hk, h⟩, by simp⟩)
      simp [hs _ hmk]
    simp [this]
  calc ∫⁻ x, ‖denseField S s t x‖ₑ ^ 4 ∂haarAddCircle
      = ENNReal.ofReal (∫ x, ‖denseField S s t x‖ ^ 4 ∂haarAddCircle) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint
          (Filter.Eventually.of_forall fun x => by positivity)]
        congr 1; funext x
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    _ = ENNReal.ofReal (∑' m : ℤ, ‖∑ k ∈ S, s k t * s (m - k) t‖ ^ 2) := by
        unfold denseField
        rw [integral_norm_pow_four_torusPoly S _ hc]
    _ = ∑' m : ℤ, ‖∑ k ∈ S, s k t * s (m - k) t‖ₑ ^ 2 := by
        rw [ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hsum]
        congr 1; funext m
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- **Dense-class `L⁴` bound** (`a = 13/32`): `∫∫ |v|⁴ ≤ K · N(s)²` with one finite `K`. -/
theorem dense_L4_bound :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (S : Finset ℤ) (s : ℤ → 𝓢(ℝ, ℂ)), (∀ k ∉ S, s k = 0) →
      ∫⁻ t, ∫⁻ x, ‖denseField S s t x‖ₑ ^ 4 ∂haarAddCircle ≤ K * denseNormSq s ^ 2 := by
  obtain ⟨K, hK, hcore⟩ := bilinear_L4_fourier
  set c : ℝ := -(2 * Real.pi) with hcdef
  have hc : c ≠ 0 := by rw [hcdef]; have := Real.pi_pos; linarith
  set ρ : ℝ≥0∞ := ENNReal.ofReal |c⁻¹| with hρ
  have hρt : ρ ≠ ⊤ := ENNReal.ofReal_ne_top
  refine ⟨ρ * K, ENNReal.mul_ne_top hρt hK, fun S s hs => ?_⟩
  set θ : ℤ → 𝓢(ℝ, ℂ) := fun k => 𝓕⁻ (s k) with hθ
  have hθ0 : ∀ k ∉ S, θ k = 0 := fun k hk => by simp [hθ, hs k hk]
  set F : ℤ → ℝ → ℝ≥0∞ := fun k l => ‖θ k (c⁻¹ * l)‖ₑ with hFdef
  have hFm : ∀ k, Measurable (F k) := fun k =>
    ((θ k).continuous.comp (continuous_const.mul continuous_id)).enorm.measurable
  have hFc : ∀ k η, ‖θ k η‖ₑ = F k (c * η) := fun k η => by
    simp only [hFdef]; rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  -- the core right side and the dense norm
  have hN : denseNormSq s = ρ * ∑' k : ℤ, ∫⁻ l, weightedSq F k l := by
    unfold denseNormSq
    rw [← ENNReal.tsum_mul_left]
    congr 1; funext k
    have : (fun ξ => modWt (2 * (13 / 32 : ℝ)) k (-(2 * Real.pi) * ξ) * ‖(𝓕⁻ (s k)) ξ‖ₑ ^ 2) =
        fun ξ => weightedSq F k (c * ξ) := by
      funext ξ
      simp only [weightedSq]
      rw [← hFc]
    rw [this, lintegral_comp_mul_left_real (weightedSq F k) hc]
  -- per-mode comparison
  have hm : ∀ m : ℤ, ∫⁻ t, ‖∑ k ∈ S, s k t * s (m - k) t‖ₑ ^ 2 ≤
      ρ ^ 3 * ∫⁻ τ, (∑' k : ℤ, ∫⁻ l, F k l * F (m - k) (τ - l)) ^ 2 := by
    intro m
    refine (lintegral_sq_sum_mul_le S s m).trans (le_of_eq ?_)
    have hI : ∀ ξ, ∑ k ∈ S, ∫⁻ η, ‖(𝓕⁻ (s k)) η‖ₑ * ‖(𝓕⁻ (s (m - k))) (ξ - η)‖ₑ =
        ρ * ∑' k : ℤ, ∫⁻ l, F k l * F (m - k) (c * ξ - l) := by
      intro ξ
      rw [← ENNReal.tsum_mul_left, tsum_eq_sum (s := S)]
      · refine Finset.sum_congr rfl fun k _ => ?_
        have : (fun η => ‖(𝓕⁻ (s k)) η‖ₑ * ‖(𝓕⁻ (s (m - k))) (ξ - η)‖ₑ) =
            fun η => (fun l => F k l * F (m - k) (c * ξ - l)) (c * η) := by
          funext η
          change ‖θ k η‖ₑ * ‖θ (m - k) (ξ - η)‖ₑ = _
          rw [hFc, hFc, mul_sub]
        rw [this]
        exact lintegral_comp_mul_left_real (fun l => F k l * F (m - k) (c * ξ - l)) hc
      · intro k hk
        simp [hFdef, hθ0 k hk]
    simp_rw [hI]
    have hpow : (fun ξ => (ρ * ∑' k : ℤ, ∫⁻ l, F k l * F (m - k) (c * ξ - l)) ^ 2) =
        fun ξ => ρ ^ 2 * (fun τ => (∑' k : ℤ, ∫⁻ l, F k l * F (m - k) (τ - l)) ^ 2) (c * ξ) := by
      funext ξ; rw [mul_pow]
    have hsc : ∫⁻ a, (fun τ => (∑' k : ℤ, ∫⁻ l, F k l * F (m - k) (τ - l)) ^ 2) (c * a) =
        ρ * ∫⁻ τ, (∑' k : ℤ, ∫⁻ l, F k l * F (m - k) (τ - l)) ^ 2 :=
      lintegral_comp_mul_left_real (fun τ => (∑' k : ℤ, ∫⁻ l, F k l * F (m - k) (τ - l)) ^ 2) hc
    rw [hpow, lintegral_const_mul' _ _ (ENNReal.pow_ne_top hρt), hsc]
    ring
  calc ∫⁻ t, ∫⁻ x, ‖denseField S s t x‖ₑ ^ 4 ∂haarAddCircle
      = ∫⁻ t, ∑' m : ℤ, ‖∑ k ∈ S, s k t * s (m - k) t‖ₑ ^ 2 := by
        congr 1; funext t; exact lintegral_torus_denseField S s hs t
    _ = ∑' m : ℤ, ∫⁻ t, ‖∑ k ∈ S, s k t * s (m - k) t‖ₑ ^ 2 := by
        refine lintegral_tsum fun m => ?_
        have hcont : Continuous fun t => ∑ k ∈ S, s k t * s (m - k) t :=
          continuous_finsetSum _ fun k _ => (s k).continuous.mul (s (m - k)).continuous
        exact (hcont.measurable.enorm.pow_const 2).aemeasurable
    _ ≤ ∑' m : ℤ, ρ ^ 3 * ∫⁻ τ, (∑' k : ℤ, ∫⁻ l, F k l * F (m - k) (τ - l)) ^ 2 :=
        ENNReal.tsum_le_tsum hm
    _ = ρ ^ 3 * ∑' m : ℤ, ∫⁻ τ, (∑' k : ℤ, ∫⁻ l, F k l * F (m - k) (τ - l)) ^ 2 :=
        ENNReal.tsum_mul_left
    _ ≤ ρ ^ 3 * (K * (∑' k : ℤ, ∫⁻ l, weightedSq F k l) ^ 2) := by
        gcongr
        exact hcore F hFm
    _ = ρ * K * denseNormSq s ^ 2 := by
        rw [hN]; ring

end LiebLiniger.FixedPeriod.ALLS.PdeB
