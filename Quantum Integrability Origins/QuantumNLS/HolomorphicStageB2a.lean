import Mathlib
import QuantumNLS.HolomorphicStageB1

/-!
# C2 stage B2a: the difference-quotient limit for small `v`

Let `f : E → F` be complex differentiable on an open `U`, `y0 ∈ U`, and let `ball y0 ρ ⊆ U` with `fderiv ℂ f` Lipschitz
(constant `Λ`) on `ball y0 ρ`. For `k` and small `v`, the difference quotients
`Q_s(v) = s⁻¹ • (fderiv ℂ f (y0 + s•k) v − fderiv ℂ f y0 v)` satisfy
`‖Q_s(v) − ik k v‖ ≤ Λ ‖s‖ ‖k‖²`, where `ik k v = (2πi)⁻¹ • ∮_{|ζ|=1} ζ⁻² • fderiv ℂ f (y0 + ζ•v) k`.
Hence `Q_s(v) → ik k v` as `s → 0` (`tendsto_quot_small`). This is the existence of the limit that stage B2b extends
to all `v` by homogeneity. Standard axioms only.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology Metric Complex Set

namespace QuantumNLS.HolomorphicStageB2a

open QuantumNLS.HolomorphicStageB1

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The Cauchy integral `ik` of the derivative in direction `k`, along the circle of `v`. -/
def ik (f : E → F) (y0 k v : E) : F :=
  (2 * Real.pi * Complex.I)⁻¹ • ∮ ζ in C(0, 1), (1 / ζ ^ 2) • fderiv ℂ f (y0 + ζ • v) k

/-- A function continuous on a ball is circle-integrable along a circle `c + ζ • v` lying in the ball. -/
theorem circleIntegrable_inv_sq_smul {g : E → F} {y0 : E} {ρ : ℝ} (hg : ContinuousOn g (ball y0 ρ))
    (c v : E) (hc : ∀ ζ : ℂ, ‖ζ‖ = 1 → c + ζ • v ∈ ball y0 ρ) :
    CircleIntegrable (fun ζ : ℂ => (1 / ζ ^ 2) • g (c + ζ • v)) 0 1 := by
  have hcont1 : ContinuousOn (fun ζ : ℂ => (1 / ζ ^ 2)) (sphere (0 : ℂ) 1) :=
    continuousOn_const.div (continuous_pow 2).continuousOn
      (fun ζ hζ => pow_ne_zero 2 (by
        rw [mem_sphere_zero_iff_norm] at hζ
        intro h
        rw [h, norm_zero] at hζ
        exact zero_ne_one hζ))
  have haff : Continuous fun ζ : ℂ => c + ζ • v := by fun_prop
  have hcont2 : ContinuousOn (fun ζ : ℂ => g (c + ζ • v)) (sphere (0 : ℂ) 1) :=
    hg.comp haff.continuousOn (fun ζ hζ => hc ζ (by simpa using hζ))
  have hsm := hcont1.smul hcont2
  unfold CircleIntegrable
  refine ContinuousOn.intervalIntegrable ?_
  exact hsm.comp (continuous_circleMap 0 1).continuousOn (fun θ _ => by simpa using circleMap_mem_sphere' 0 1 θ)

/-- Norm bound for the Cauchy integral `ik`, from a bound on the directional derivative on the ball. -/
theorem norm_ik_le {f : E → F} {y0 : E} {ρ K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ p ∈ ball y0 ρ, ∀ w : E, ‖fderiv ℂ f p w‖ ≤ K * ‖w‖)
    {k v : E} (hv : ‖v‖ ≤ ρ / 4) (hball : ∀ ζ : ℂ, ‖ζ‖ = 1 → y0 + ζ • v ∈ ball y0 ρ) :
    ‖ik f y0 k v‖ ≤ K * ‖k‖ := by
  unfold ik
  have hint : ‖∮ ζ in C(0, 1), (1 / ζ ^ 2) • fderiv ℂ f (y0 + ζ • v) k‖ ≤ 2 * Real.pi * 1 * (K * ‖k‖) := by
    refine circleIntegral.norm_integral_le_of_norm_le_const zero_le_one (fun ζ hζ => ?_)
    rw [mem_sphere_zero_iff_norm] at hζ
    rw [norm_smul]
    have h1 : ‖(1 / ζ ^ 2 : ℂ)‖ = 1 := by
      rw [norm_div, norm_one, norm_pow, hζ]
      norm_num
    rw [h1, one_mul]
    exact hK _ (hball ζ hζ) k
  rw [norm_smul]
  have hpi : ‖(2 * Real.pi * Complex.I)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    norm_num
  rw [hpi]
  calc (2 * Real.pi)⁻¹ * ‖∮ ζ in C(0, 1), (1 / ζ ^ 2) • fderiv ℂ f (y0 + ζ • v) k‖
      ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * 1 * (K * ‖k‖)) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = K * ‖k‖ := by field_simp


/-- Continuity of `p ↦ fderiv ℂ f p` on a ball, from the Lipschitz bound. -/
theorem continuousOn_fderiv_ball {f : E → F} {y0 : E} {ρ Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ p ∈ ball y0 ρ, ∀ q ∈ ball y0 ρ, ‖fderiv ℂ f p - fderiv ℂ f q‖ ≤ Λ * ‖p - q‖) :
    ContinuousOn (fun p => fderiv ℂ f p) (ball y0 ρ) := by
  intro p hp
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  refine ⟨ε / (Λ + 1), by positivity, fun x hx hd => ?_⟩
  have h1 := hΛ x hx p hp
  rw [dist_eq_norm]
  have h2 : ‖x - p‖ = dist x p := (dist_eq_norm x p).symm
  rw [h2] at h1
  have h3 : Λ * dist x p < ε := by
    have hdx : dist x p < ε / (Λ + 1) := hd
    have : Λ * dist x p ≤ (Λ + 1) * dist x p := by nlinarith [dist_nonneg (x := x) (y := p)]
    have h4 : (Λ + 1) * dist x p < ε := by
      have := (lt_div_iff₀ (by linarith : (0 : ℝ) < Λ + 1)).1 hdx
      linarith
    linarith
  linarith

/-- **Quotient estimate.** For `s ≠ 0` small and `k`, `v` small, the difference quotient of the derivative differs from
`ik` by at most `Λ ‖s‖ ‖k‖²`. -/
theorem quot_bound {U : Set E} (hU : IsOpen U) {f : E → F} (hf : DifferentiableOn ℂ f U) {y0 : E} {ρ Λ : ℝ}
    (hρ : 0 < ρ) (hball : ball y0 ρ ⊆ U) (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ p ∈ ball y0 ρ, ∀ q ∈ ball y0 ρ, ‖fderiv ℂ f p - fderiv ℂ f q‖ ≤ Λ * ‖p - q‖)
    {k v : E} {s : ℂ} (hs : s ≠ 0) (hk : ‖k‖ ≤ ρ / 8) (hsk : ‖s • k‖ ≤ ρ / 8) (hv : ‖v‖ ≤ ρ / 4) :
    ‖s⁻¹ • (fderiv ℂ f (y0 + s • k) v - fderiv ℂ f y0 v) - ik f y0 k v‖ ≤ Λ * ‖s‖ * ‖k‖ ^ 2 := by
  have hsk_ball : y0 + s • k ∈ ball y0 ρ := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    linarith
  have hv_ball : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → y0 + ζ • v ∈ ball y0 ρ := by
    intro ζ hζ
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    have h1 : ‖ζ‖ * ‖v‖ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hζ (norm_nonneg v)
    linarith
  have hsv_ball : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → y0 + s • k + ζ • v ∈ ball y0 ρ := by
    intro ζ hζ
    rw [mem_ball, dist_eq_norm, show y0 + s • k + ζ • v - y0 = s • k + ζ • v by abel]
    have h1 : ‖ζ • v‖ ≤ ‖v‖ := by
      rw [norm_smul]
      have : ‖ζ‖ * ‖v‖ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hζ (norm_nonneg v)
      linarith
    have := norm_add_le (s • k) (ζ • v)
    linarith
  have hcontD := continuousOn_fderiv_ball (f := f) (y0 := y0) (ρ := ρ) hΛ0 hΛ
  have hcontF : ContinuousOn f (ball y0 ρ) := hf.continuousOn.mono hball
  have I1 := circleIntegrable_inv_sq_smul hcontF (y0 + s • k) v (fun ζ hζ => hsv_ball ζ hζ.le)
  have I2 := circleIntegrable_inv_sq_smul hcontF y0 v (fun ζ hζ => hv_ball ζ hζ.le)
  have I3 := circleIntegrable_inv_sq_smul (g := fun p => fderiv ℂ f p k)
    (hcontD.clm_apply continuousOn_const) y0 v (fun ζ hζ => hv_ball ζ hζ.le)
  have eA := fderiv_apply_eq_circleIntegral hU hf (hball hsk_ball)
    (fun ζ hζ => hball (hsv_ball ζ hζ))
  have eB := fderiv_apply_eq_circleIntegral hU hf (hball (mem_ball_self hρ))
    (fun ζ hζ => hball (hv_ball ζ hζ))
  have hpt : ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖s⁻¹ • (f (y0 + s • k + ζ • v) - f (y0 + ζ • v)) -
      fderiv ℂ f (y0 + ζ • v) k‖ ≤ Λ * ‖s‖ * ‖k‖ ^ 2 := by
    intro ζ hζ
    have hw : y0 + ζ • v ∈ ball y0 ρ := hv_ball ζ hζ.le
    have hwk : y0 + ζ • v + s • k ∈ ball y0 ρ := by
      have := hsv_ball ζ hζ.le
      rwa [show y0 + ζ • v + s • k = y0 + s • k + ζ • v by abel]
    have hB := norm_sub_sub_fderiv_le hU hf hball (convex_ball y0 ρ) hΛ0 hΛ hw hwk
    have hlin : fderiv ℂ f (y0 + ζ • v) (s • k) = s • fderiv ℂ f (y0 + ζ • v) k := map_smul _ _ _
    rw [hlin] at hB
    have hrw : s⁻¹ • (f (y0 + s • k + ζ • v) - f (y0 + ζ • v)) - fderiv ℂ f (y0 + ζ • v) k =
        s⁻¹ • (f (y0 + ζ • v + s • k) - f (y0 + ζ • v) - s • fderiv ℂ f (y0 + ζ • v) k) := by
      rw [show y0 + ζ • v + s • k = y0 + s • k + ζ • v from by abel]
      simp only [smul_sub, smul_smul, inv_mul_cancel₀ hs, one_smul]
    rw [hrw, norm_smul, norm_inv]
    have hn : ‖s • k‖ ^ 2 = ‖s‖ ^ 2 * ‖k‖ ^ 2 := by rw [norm_smul]; ring
    have hs0 : 0 < ‖s‖ := norm_pos_iff.2 hs
    have hB' : ‖f (y0 + ζ • v + s • k) - f (y0 + ζ • v) - s • fderiv ℂ f (y0 + ζ • v) k‖ ≤
        Λ * (‖s‖ ^ 2 * ‖k‖ ^ 2) := by
      rw [← hn]
      exact hB
    calc ‖s‖⁻¹ * ‖f (y0 + ζ • v + s • k) - f (y0 + ζ • v) - s • fderiv ℂ f (y0 + ζ • v) k‖
        ≤ ‖s‖⁻¹ * (Λ * (‖s‖ ^ 2 * ‖k‖ ^ 2)) := mul_le_mul_of_nonneg_left hB' (by positivity)
      _ = Λ * ‖s‖ * ‖k‖ ^ 2 := by field_simp
  -- the integral identity
  have hsum : fderiv ℂ f (y0 + s • k) v - fderiv ℂ f y0 v = (2 * Real.pi * Complex.I)⁻¹ •
      ∮ ζ in C(0, 1), ((1 / ζ ^ 2) • f (y0 + s • k + ζ • v) - (1 / ζ ^ 2) • f (y0 + ζ • v)) := by
    rw [eA, eB, ← smul_sub, circleIntegral.integral_sub I1 I2]
  have hcontS : ContinuousOn (fun p => s⁻¹ • f p) (ball y0 ρ) := hcontF.const_smul s⁻¹
  have I1s := circleIntegrable_inv_sq_smul (g := fun p => s⁻¹ • f p) hcontS (y0 + s • k) v
    (fun ζ hζ => hsv_ball ζ hζ.le)
  have I2s := circleIntegrable_inv_sq_smul (g := fun p => s⁻¹ • f p) hcontS y0 v
    (fun ζ hζ => hv_ball ζ hζ.le)
  have hH : (∮ ζ in C(0, 1), (1 / ζ ^ 2) • (s⁻¹ • (f (y0 + s • k + ζ • v) - f (y0 + ζ • v)) -
      fderiv ℂ f (y0 + ζ • v) k)) =
      (∮ ζ in C(0, 1), (1 / ζ ^ 2) • (s⁻¹ • f (y0 + s • k + ζ • v))) -
        (∮ ζ in C(0, 1), (1 / ζ ^ 2) • (s⁻¹ • f (y0 + ζ • v))) -
        ∮ ζ in C(0, 1), (1 / ζ ^ 2) • fderiv ℂ f (y0 + ζ • v) k := by
    have e : (fun ζ : ℂ => (1 / ζ ^ 2) • (s⁻¹ • (f (y0 + s • k + ζ • v) - f (y0 + ζ • v)) -
        fderiv ℂ f (y0 + ζ • v) k)) =
        fun ζ : ℂ => ((1 / ζ ^ 2) • (s⁻¹ • f (y0 + s • k + ζ • v)) -
          (1 / ζ ^ 2) • (s⁻¹ • f (y0 + ζ • v))) - (1 / ζ ^ 2) • fderiv ℂ f (y0 + ζ • v) k := by
      funext ζ
      module
    have k1 : (∮ ζ in C(0, 1), ((1 / ζ ^ 2) • (s⁻¹ • f (y0 + s • k + ζ • v)) -
        (1 / ζ ^ 2) • (s⁻¹ • f (y0 + ζ • v)))) =
        (∮ ζ in C(0, 1), (1 / ζ ^ 2) • (s⁻¹ • f (y0 + s • k + ζ • v))) -
          ∮ ζ in C(0, 1), (1 / ζ ^ 2) • (s⁻¹ • f (y0 + ζ • v)) :=
      circleIntegral.integral_sub I1s I2s
    have k2 : (∮ ζ in C(0, 1), (((1 / ζ ^ 2) • (s⁻¹ • f (y0 + s • k + ζ • v)) -
        (1 / ζ ^ 2) • (s⁻¹ • f (y0 + ζ • v))) - (1 / ζ ^ 2) • fderiv ℂ f (y0 + ζ • v) k)) =
        (∮ ζ in C(0, 1), ((1 / ζ ^ 2) • (s⁻¹ • f (y0 + s • k + ζ • v)) -
          (1 / ζ ^ 2) • (s⁻¹ • f (y0 + ζ • v)))) -
          ∮ ζ in C(0, 1), (1 / ζ ^ 2) • fderiv ℂ f (y0 + ζ • v) k :=
      circleIntegral.integral_sub (I1s.sub I2s) I3
    rw [e, k2, k1]
  have e1 : (∮ ζ in C(0, 1), (1 / ζ ^ 2) • (s⁻¹ • f (y0 + s • k + ζ • v))) =
      s⁻¹ • ∮ ζ in C(0, 1), (1 / ζ ^ 2) • f (y0 + s • k + ζ • v) := by
    rw [← circleIntegral.integral_smul]
    congr 1
    funext ζ
    module
  have e2 : (∮ ζ in C(0, 1), (1 / ζ ^ 2) • (s⁻¹ • f (y0 + ζ • v))) =
      s⁻¹ • ∮ ζ in C(0, 1), (1 / ζ ^ 2) • f (y0 + ζ • v) := by
    rw [← circleIntegral.integral_smul]
    congr 1
    funext ζ
    module
  have hX : s⁻¹ • (fderiv ℂ f (y0 + s • k) v - fderiv ℂ f y0 v) -
      (2 * Real.pi * Complex.I)⁻¹ • ∮ ζ in C(0, 1), (1 / ζ ^ 2) • fderiv ℂ f (y0 + ζ • v) k =
      (2 * Real.pi * Complex.I)⁻¹ • ∮ ζ in C(0, 1), (1 / ζ ^ 2) • (s⁻¹ • (f (y0 + s • k + ζ • v) -
        f (y0 + ζ • v)) - fderiv ℂ f (y0 + ζ • v) k) := by
    have k0 : (∮ ζ in C(0, 1), ((1 / ζ ^ 2) • f (y0 + s • k + ζ • v) -
        (1 / ζ ^ 2) • f (y0 + ζ • v))) =
        (∮ ζ in C(0, 1), (1 / ζ ^ 2) • f (y0 + s • k + ζ • v)) -
          ∮ ζ in C(0, 1), (1 / ζ ^ 2) • f (y0 + ζ • v) :=
      circleIntegral.integral_sub I1 I2
    rw [hsum, k0, hH, e1, e2]
    module
  unfold ik
  rw [hX]
  have hint : ‖∮ ζ in C(0, 1), (1 / ζ ^ 2) • (s⁻¹ • (f (y0 + s • k + ζ • v) - f (y0 + ζ • v)) -
      fderiv ℂ f (y0 + ζ • v) k)‖ ≤ 2 * Real.pi * 1 * (Λ * ‖s‖ * ‖k‖ ^ 2) := by
    refine circleIntegral.norm_integral_le_of_norm_le_const zero_le_one (fun ζ hζ => ?_)
    rw [mem_sphere_zero_iff_norm] at hζ
    rw [norm_smul]
    have h1 : ‖(1 / ζ ^ 2 : ℂ)‖ = 1 := by
      rw [norm_div, norm_one, norm_pow, hζ]
      norm_num
    rw [h1, one_mul]
    exact hpt ζ hζ
  have hpi : ‖(2 * Real.pi * Complex.I)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    norm_num
  rw [norm_smul, hpi]
  calc (2 * Real.pi)⁻¹ * ‖∮ ζ in C(0, 1), (1 / ζ ^ 2) • (s⁻¹ • (f (y0 + s • k + ζ • v) -
        f (y0 + ζ • v)) - fderiv ℂ f (y0 + ζ • v) k)‖
      ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * 1 * (Λ * ‖s‖ * ‖k‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = Λ * ‖s‖ * ‖k‖ ^ 2 := by field_simp

/-- The difference quotients converge to `ik` as `s → 0` (for fixed small `k`, `v`). -/
theorem tendsto_quot_small {U : Set E} (hU : IsOpen U) {f : E → F} (hf : DifferentiableOn ℂ f U) {y0 : E}
    {ρ Λ : ℝ} (hρ : 0 < ρ) (hball : ball y0 ρ ⊆ U) (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ p ∈ ball y0 ρ, ∀ q ∈ ball y0 ρ, ‖fderiv ℂ f p - fderiv ℂ f q‖ ≤ Λ * ‖p - q‖)
    {k v : E} (hk : ‖k‖ ≤ ρ / 8) (hv : ‖v‖ ≤ ρ / 4) :
    Tendsto (fun s : ℂ => s⁻¹ • (fderiv ℂ f (y0 + s • k) v - fderiv ℂ f y0 v)) (𝓝[≠] 0)
      (𝓝 (ik f y0 k v)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : Tendsto (fun s : ℂ => Λ * ‖s‖ * ‖k‖ ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    have hc : Continuous (fun s : ℂ => Λ * ‖s‖ * ‖k‖ ^ 2) := by fun_prop
    have h : Tendsto (fun s : ℂ => Λ * ‖s‖ * ‖k‖ ^ 2) (𝓝 0) (𝓝 0) := by
      simpa using hc.tendsto (0 : ℂ)
    exact h.mono_left nhdsWithin_le_nhds
  refine squeeze_zero' ?_ ?_ hbound
  · exact eventually_nhdsWithin_of_forall fun s _ => norm_nonneg _
  · have hev : ∀ᶠ s in 𝓝 (0 : ℂ), ‖s‖ < 1 :=
      (continuous_norm.tendsto 0).eventually (gt_mem_nhds (by simp : ‖(0 : ℂ)‖ < 1))
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hev, self_mem_nhdsWithin] with s hs1 hs2
    have hs : s ≠ 0 := hs2
    have hsk : ‖s • k‖ ≤ ρ / 8 := by
      rw [norm_smul]
      have : ‖s‖ * ‖k‖ ≤ 1 * (ρ / 8) := mul_le_mul hs1.le hk (norm_nonneg _) zero_le_one
      linarith
    exact quot_bound hU hf hρ hball hΛ0 hΛ hs hk hsk hv

end QuantumNLS.HolomorphicStageB2a

#print axioms QuantumNLS.HolomorphicStageB2a.norm_ik_le
#print axioms QuantumNLS.HolomorphicStageB2a.circleIntegrable_inv_sq_smul
#print axioms QuantumNLS.HolomorphicStageB2a.quot_bound
#print axioms QuantumNLS.HolomorphicStageB2a.tendsto_quot_small
