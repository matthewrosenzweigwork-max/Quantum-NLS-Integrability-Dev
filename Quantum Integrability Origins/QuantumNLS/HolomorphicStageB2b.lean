import Mathlib
import QuantumNLS.HolomorphicStageB2a

/-!
# C2 stage B2b: the derivative of `fderiv ℂ f` as a ℂ-linear map

Hypotheses (as in B2a): `ball y0 ρ ⊆ U` with `DifferentiableOn ℂ f U`, `fderiv ℂ f` Lipschitz (constant `Λ`) and
bounded (`‖fderiv ℂ f p w‖ ≤ K ‖w‖`) on `ball y0 ρ`.

* `Lk f y0 k v := limUnder (𝓝[≠]0) (s ↦ s⁻¹ • (fderiv ℂ f (y0+s•k) v − fderiv ℂ f y0 v))` (defined for all `v`, `k`);
* `Lk_eq_ik`: `Lk = ik` for small `k`, `v` (stage B2a);
* `Lk` is ℂ-linear in `v` and in `k`, and `‖Lk k v‖ ≤ (4K/ρ) ‖k‖ ‖v‖`;
* `hasFDerivAt_fderiv`: `HasFDerivAt (fun p => fderiv ℂ f p) (Lcl) y0` with `Lcl : E →L[ℂ] (E →L[ℂ] F)`.

Standard axioms only.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology Metric Complex Set

namespace QuantumNLS.HolomorphicStageB2b

open QuantumNLS.HolomorphicStageB2a QuantumNLS.HolomorphicStageB1

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The difference quotient in direction `k` at `v`, as a function of `s`. -/
def Qs (f : E → F) (y0 k v : E) (s : ℂ) : F :=
  s⁻¹ • (fderiv ℂ f (y0 + s • k) v - fderiv ℂ f y0 v)

/-- The limit of the difference quotients (exists for all `v` by `tendsto_Qs`). -/
def Lk (f : E → F) (y0 k v : E) : F :=
  limUnder (𝓝[≠] (0 : ℂ)) (fun s => Qs f y0 k v s)

theorem Qs_smul_v (f : E → F) (y0 k v : E) (c s : ℂ) :
    Qs f y0 k (c • v) s = c • Qs f y0 k v s := by
  unfold Qs
  rw [map_smul, map_smul]
  module

theorem Qs_add_v (f : E → F) (y0 k v w : E) (s : ℂ) :
    Qs f y0 k (v + w) s = Qs f y0 k v s + Qs f y0 k w s := by
  unfold Qs
  rw [map_add, map_add]
  module

theorem Qs_smul_k (f : E → F) (y0 k v : E) {c : ℂ} (hc : c ≠ 0) (s : ℂ) :
    Qs f y0 (c • k) v s = c • Qs f y0 k v (c * s) := by
  unfold Qs
  rw [show (c * s) • k = s • (c • k) from by rw [mul_smul, smul_comm]]
  simp only [smul_smul, mul_inv, mul_inv_cancel_left₀ hc]

theorem tendsto_mul_nhdsWithin_zero {c : ℂ} (hc : c ≠ 0) :
    Tendsto (fun s : ℂ => c * s) (𝓝[≠] 0) (𝓝[≠] 0) := by
  have h1 : Tendsto (fun s : ℂ => c * s) (𝓝 0) (𝓝 0) := by
    have hc' : Continuous fun s : ℂ => c * s := continuous_const.mul continuous_id
    simpa using hc'.tendsto (0 : ℂ)
  exact tendsto_nhdsWithin_iff.2 ⟨h1.mono_left nhdsWithin_le_nhds,
    eventually_nhdsWithin_of_forall fun s hs => mul_ne_zero hc hs⟩

/-- For small `k` and `v`, the limit is the Cauchy integral `ik`. -/
theorem tendsto_Qs_small {U : Set E} (hU : IsOpen U) {f : E → F} (hf : DifferentiableOn ℂ f U) {y0 : E}
    {ρ Λ : ℝ} (hρ : 0 < ρ) (hball : ball y0 ρ ⊆ U) (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ p ∈ ball y0 ρ, ∀ q ∈ ball y0 ρ, ‖fderiv ℂ f p - fderiv ℂ f q‖ ≤ Λ * ‖p - q‖)
    {k v : E} (hk : ‖k‖ ≤ ρ / 8) (hv : ‖v‖ ≤ ρ / 4) :
    Tendsto (fun s => Qs f y0 k v s) (𝓝[≠] 0) (𝓝 (ik f y0 k v)) :=
  tendsto_quot_small hU hf hρ hball hΛ0 hΛ hk hv

theorem Lk_eq_ik {U : Set E} (hU : IsOpen U) {f : E → F} (hf : DifferentiableOn ℂ f U) {y0 : E}
    {ρ Λ : ℝ} (hρ : 0 < ρ) (hball : ball y0 ρ ⊆ U) (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ p ∈ ball y0 ρ, ∀ q ∈ ball y0 ρ, ‖fderiv ℂ f p - fderiv ℂ f q‖ ≤ Λ * ‖p - q‖)
    {k v : E} (hk : ‖k‖ ≤ ρ / 8) (hv : ‖v‖ ≤ ρ / 4) :
    Lk f y0 k v = ik f y0 k v := by
  unfold Lk
  have hlim : Tendsto (fun s => Qs f y0 k v s) (𝓝[≠] 0) (𝓝 (limUnder (𝓝[≠] (0 : ℂ)) (fun s => Qs f y0 k v s))) :=
    tendsto_nhds_limUnder ⟨_, tendsto_Qs_small hU hf hρ hball hΛ0 hΛ hk hv⟩
  exact tendsto_nhds_unique hlim (tendsto_Qs_small hU hf hρ hball hΛ0 hΛ hk hv)

theorem tendsto_Qs_all {U : Set E} (hU : IsOpen U) {f : E → F} (hf : DifferentiableOn ℂ f U) {y0 : E}
    {ρ Λ : ℝ} (hρ : 0 < ρ) (hball : ball y0 ρ ⊆ U) (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ p ∈ ball y0 ρ, ∀ q ∈ ball y0 ρ, ‖fderiv ℂ f p - fderiv ℂ f q‖ ≤ Λ * ‖p - q‖)
    {k : E} (hk : ‖k‖ ≤ ρ / 8) (v : E) :
    Tendsto (fun s => Qs f y0 k v s) (𝓝[≠] 0) (𝓝 (Lk f y0 k v)) := by
  by_cases hv0 : v = 0
  · subst hv0
    have hQ0 : ∀ s, Qs f y0 k (0 : E) s = 0 := fun s => by
      unfold Qs
      rw [map_zero, map_zero, sub_self, smul_zero]
    have : Lk f y0 k (0 : E) = 0 := by
      unfold Lk
      simp only [hQ0]
      exact tendsto_nhds_unique (tendsto_nhds_limUnder ⟨0, tendsto_const_nhds⟩) tendsto_const_nhds
    rw [this]
    simp only [hQ0]
    exact tendsto_const_nhds
  · have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
    set c : ℝ := 4 * ‖v‖ / ρ with hc
    have hcpos : 0 < c := by
      rw [hc]
      positivity
    have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hcpos.ne'
    obtain ⟨v', hv'⟩ : ∃ v' : E, v' = (c : ℂ)⁻¹ • v := ⟨_, rfl⟩
    have hnorm : ‖v'‖ ≤ ρ / 4 := by
      rw [hv', norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos, hc]
      rw [inv_mul_le_iff₀ (by positivity)]
      field_simp
      linarith
    have hvv : v = (c : ℂ) • v' := by
      rw [hv', smul_smul, mul_inv_cancel₀ hcC, one_smul]
    have hlim' : Tendsto (fun s => Qs f y0 k v' s) (𝓝[≠] 0) (𝓝 (ik f y0 k v')) :=
      tendsto_Qs_small hU hf hρ hball hΛ0 hΛ hk hnorm
    have hfin : Tendsto (fun s => Qs f y0 k v s) (𝓝[≠] 0) (𝓝 ((c : ℂ) • ik f y0 k v')) := by
      have := hlim'.const_smul (c : ℂ)
      refine this.congr (fun s => ?_)
      rw [hvv, Qs_smul_v]
    exact tendsto_nhds_limUnder ⟨_, hfin⟩

theorem ik_smul_k (f : E → F) (y0 v k : E) (c : ℂ) :
    ik f y0 (c • k) v = c • ik f y0 k v := by
  unfold ik
  have hpt : ∀ ζ : ℂ, (1 / ζ ^ 2) • fderiv ℂ f (y0 + ζ • v) (c • k) =
      c • ((1 / ζ ^ 2) • fderiv ℂ f (y0 + ζ • v) k) := fun ζ => by
    rw [map_smul]
    module
  simp_rw [hpt]
  rw [circleIntegral.integral_smul]
  module

theorem ik_add_k {U : Set E} {f : E → F} {y0 : E} {ρ Λ : ℝ} (hρ : 0 < ρ) (hball : ball y0 ρ ⊆ U)
    (hf : DifferentiableOn ℂ f U)
    (hΛ0 : 0 ≤ Λ) (hΛ : ∀ p ∈ ball y0 ρ, ∀ q ∈ ball y0 ρ, ‖fderiv ℂ f p - fderiv ℂ f q‖ ≤ Λ * ‖p - q‖)
    {v : E} (hv : ‖v‖ ≤ ρ / 4) (k1 k2 : E) :
    ik f y0 (k1 + k2) v = ik f y0 k1 v + ik f y0 k2 v := by
  have hv_ball : ∀ ζ : ℂ, ‖ζ‖ = 1 → y0 + ζ • v ∈ ball y0 ρ := by
    intro ζ hζ
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hζ, one_mul]
    linarith
  have hcontD := continuousOn_fderiv_ball (f := f) (y0 := y0) (ρ := ρ) hΛ0 hΛ
  have I1 := circleIntegrable_inv_sq_smul (g := fun p => fderiv ℂ f p k1)
    (hcontD.clm_apply continuousOn_const) y0 v hv_ball
  have I2 := circleIntegrable_inv_sq_smul (g := fun p => fderiv ℂ f p k2)
    (hcontD.clm_apply continuousOn_const) y0 v hv_ball
  unfold ik
  have hpt : ∀ ζ : ℂ, (1 / ζ ^ 2) • fderiv ℂ f (y0 + ζ • v) (k1 + k2) =
      (1 / ζ ^ 2) • fderiv ℂ f (y0 + ζ • v) k1 + (1 / ζ ^ 2) • fderiv ℂ f (y0 + ζ • v) k2 := fun ζ => by
    rw [map_add, smul_add]
  simp_rw [hpt]
  rw [circleIntegral.integral_add I1 I2, smul_add]


/-- The limit exists for every `k` (for small `v`), by rescaling `k` to a small vector. -/
theorem tendsto_Qs_gen {U : Set E} (hU : IsOpen U) {f : E → F} (hf : DifferentiableOn ℂ f U) {y0 : E}
    {ρ Λ : ℝ} (hρ : 0 < ρ) (hball : ball y0 ρ ⊆ U) (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ p ∈ ball y0 ρ, ∀ q ∈ ball y0 ρ, ‖fderiv ℂ f p - fderiv ℂ f q‖ ≤ Λ * ‖p - q‖)
    (k : E) {v : E} (hv : ‖v‖ ≤ ρ / 4) :
    Tendsto (fun s => Qs f y0 k v s) (𝓝[≠] 0) (𝓝 (ik f y0 k v)) := by
  set c : ℝ := (ρ / 8) / (‖k‖ + 1) with hc
  have hcpos : 0 < c := by
    rw [hc]
    positivity
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hcpos.ne'
  have hcc : c * (‖k‖ + 1) = ρ / 8 := by
    rw [hc]
    field_simp
  have hck : ‖(c : ℂ) • k‖ ≤ ρ / 8 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos]
    have : c * ‖k‖ ≤ c * (‖k‖ + 1) := mul_le_mul_of_nonneg_left (by linarith) hcpos.le
    linarith
  have hQ := tendsto_Qs_small hU hf hρ hball hΛ0 hΛ hck hv
  have hinv : Tendsto (fun s : ℂ => (c : ℂ)⁻¹ * s) (𝓝[≠] 0) (𝓝[≠] 0) :=
    tendsto_mul_nhdsWithin_zero (inv_ne_zero hcC)
  have hcomp := (hQ.comp hinv).const_smul ((c : ℂ)⁻¹)
  rw [ik_smul_k, smul_smul, inv_mul_cancel₀ hcC, one_smul] at hcomp
  refine hcomp.congr (fun s => ?_)
  show (c : ℂ)⁻¹ • Qs f y0 ((c : ℂ) • k) v ((c : ℂ)⁻¹ * s) = Qs f y0 k v s
  rw [Qs_smul_k f y0 k v hcC ((c : ℂ)⁻¹ * s), mul_inv_cancel_left₀ hcC, smul_smul, inv_mul_cancel₀ hcC,
    one_smul]

/-- The limit exists for every `k` and every `v`. -/
theorem tendsto_Qs_all_gen {U : Set E} (hU : IsOpen U) {f : E → F} (hf : DifferentiableOn ℂ f U) {y0 : E}
    {ρ Λ : ℝ} (hρ : 0 < ρ) (hball : ball y0 ρ ⊆ U) (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ p ∈ ball y0 ρ, ∀ q ∈ ball y0 ρ, ‖fderiv ℂ f p - fderiv ℂ f q‖ ≤ Λ * ‖p - q‖)
    (k v : E) :
    Tendsto (fun s => Qs f y0 k v s) (𝓝[≠] 0) (𝓝 (Lk f y0 k v)) := by
  by_cases hv0 : v = 0
  · subst hv0
    have hQ0 : ∀ s, Qs f y0 k (0 : E) s = 0 := fun s => by
      unfold Qs
      rw [map_zero, map_zero, sub_self, smul_zero]
    have : Lk f y0 k (0 : E) = 0 := by
      unfold Lk
      simp only [hQ0]
      exact tendsto_nhds_unique (tendsto_nhds_limUnder ⟨0, tendsto_const_nhds⟩) tendsto_const_nhds
    rw [this]
    simp only [hQ0]
    exact tendsto_const_nhds
  · have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
    set c : ℝ := 4 * ‖v‖ / ρ with hc
    have hcpos : 0 < c := by
      rw [hc]
      positivity
    have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hcpos.ne'
    obtain ⟨v', hv'⟩ : ∃ v' : E, v' = (c : ℂ)⁻¹ • v := ⟨_, rfl⟩
    have hnorm : ‖v'‖ ≤ ρ / 4 := by
      rw [hv', norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos, hc]
      rw [inv_mul_le_iff₀ (by positivity)]
      field_simp
      linarith
    have hvv : v = (c : ℂ) • v' := by
      rw [hv', smul_smul, mul_inv_cancel₀ hcC, one_smul]
    have hfin : Tendsto (fun s => Qs f y0 k v s) (𝓝[≠] 0) (𝓝 ((c : ℂ) • ik f y0 k v')) := by
      have := (tendsto_Qs_gen hU hf hρ hball hΛ0 hΛ k hnorm).const_smul (c : ℂ)
      refine this.congr (fun s => ?_)
      rw [hvv, Qs_smul_v]
    exact tendsto_nhds_limUnder ⟨_, hfin⟩

theorem Lk_eq_ik_gen {U : Set E} (hU : IsOpen U) {f : E → F} (hf : DifferentiableOn ℂ f U) {y0 : E}
    {ρ Λ : ℝ} (hρ : 0 < ρ) (hball : ball y0 ρ ⊆ U) (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ p ∈ ball y0 ρ, ∀ q ∈ ball y0 ρ, ‖fderiv ℂ f p - fderiv ℂ f q‖ ≤ Λ * ‖p - q‖)
    (k : E) {v : E} (hv : ‖v‖ ≤ ρ / 4) :
    Lk f y0 k v = ik f y0 k v :=
  tendsto_nhds_unique (tendsto_Qs_all_gen hU hf hρ hball hΛ0 hΛ k v)
    (tendsto_Qs_gen hU hf hρ hball hΛ0 hΛ k hv)

theorem Lk_add_v {U : Set E} (hU : IsOpen U) {f : E → F} (hf : DifferentiableOn ℂ f U) {y0 : E}
    {ρ Λ : ℝ} (hρ : 0 < ρ) (hball : ball y0 ρ ⊆ U) (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ p ∈ ball y0 ρ, ∀ q ∈ ball y0 ρ, ‖fderiv ℂ f p - fderiv ℂ f q‖ ≤ Λ * ‖p - q‖)
    (k v w : E) : Lk f y0 k (v + w) = Lk f y0 k v + Lk f y0 k w := by
  refine tendsto_nhds_unique (tendsto_Qs_all_gen hU hf hρ hball hΛ0 hΛ k (v + w)) ?_
  refine (tendsto_Qs_all_gen hU hf hρ hball hΛ0 hΛ k v).add
    (tendsto_Qs_all_gen hU hf hρ hball hΛ0 hΛ k w) |>.congr (fun s => ?_)
  rw [Qs_add_v]

theorem Lk_smul_v {U : Set E} (hU : IsOpen U) {f : E → F} (hf : DifferentiableOn ℂ f U) {y0 : E}
    {ρ Λ : ℝ} (hρ : 0 < ρ) (hball : ball y0 ρ ⊆ U) (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ p ∈ ball y0 ρ, ∀ q ∈ ball y0 ρ, ‖fderiv ℂ f p - fderiv ℂ f q‖ ≤ Λ * ‖p - q‖)
    (k v : E) (c : ℂ) : Lk f y0 k (c • v) = c • Lk f y0 k v := by
  refine tendsto_nhds_unique (tendsto_Qs_all_gen hU hf hρ hball hΛ0 hΛ k (c • v)) ?_
  refine ((tendsto_Qs_all_gen hU hf hρ hball hΛ0 hΛ k v).const_smul c).congr (fun s => ?_)
  rw [Qs_smul_v]


/-- Reduction of an arbitrary `v` to a small one, by homogeneity in `v`. -/
theorem exists_small_scale (ρ : ℝ) (hρ : 0 < ρ) {v : E} (hv0 : v ≠ 0) :
    ∃ (c : ℝ) (v' : E), 0 < c ∧ ‖v'‖ ≤ ρ / 4 ∧ v = (c : ℂ) • v' ∧ c = 4 * ‖v‖ / ρ := by
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
  refine ⟨4 * ‖v‖ / ρ, (((4 * ‖v‖ / ρ : ℝ) : ℂ))⁻¹ • v, by positivity, ?_, ?_, rfl⟩
  · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    field_simp
    linarith
  · rw [smul_smul, mul_inv_cancel₀, one_smul]
    exact_mod_cast (by positivity : (4 * ‖v‖ / ρ : ℝ) ≠ 0)

theorem Lk_zero_v {U : Set E} (hU : IsOpen U) {f : E → F} (hf : DifferentiableOn ℂ f U) {y0 : E}
    {ρ Λ : ℝ} (hρ : 0 < ρ) (hball : ball y0 ρ ⊆ U) (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ p ∈ ball y0 ρ, ∀ q ∈ ball y0 ρ, ‖fderiv ℂ f p - fderiv ℂ f q‖ ≤ Λ * ‖p - q‖) (k : E) :
    Lk f y0 k 0 = 0 := by
  have := Lk_smul_v hU hf hρ hball hΛ0 hΛ k (0 : E) (0 : ℂ)
  simpa using this

theorem Lk_add_k {U : Set E} (hU : IsOpen U) {f : E → F} (hf : DifferentiableOn ℂ f U) {y0 : E}
    {ρ Λ : ℝ} (hρ : 0 < ρ) (hball : ball y0 ρ ⊆ U) (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ p ∈ ball y0 ρ, ∀ q ∈ ball y0 ρ, ‖fderiv ℂ f p - fderiv ℂ f q‖ ≤ Λ * ‖p - q‖)
    (k1 k2 v : E) : Lk f y0 (k1 + k2) v = Lk f y0 k1 v + Lk f y0 k2 v := by
  by_cases hv0 : v = 0
  · subst hv0
    rw [Lk_zero_v hU hf hρ hball hΛ0 hΛ, Lk_zero_v hU hf hρ hball hΛ0 hΛ, Lk_zero_v hU hf hρ hball hΛ0 hΛ,
      add_zero]
  obtain ⟨c, v', hc, hv', hvv, -⟩ := exists_small_scale ρ hρ hv0
  have hsmall : Lk f y0 (k1 + k2) v' = Lk f y0 k1 v' + Lk f y0 k2 v' := by
    rw [Lk_eq_ik_gen hU hf hρ hball hΛ0 hΛ _ hv', Lk_eq_ik_gen hU hf hρ hball hΛ0 hΛ _ hv',
      Lk_eq_ik_gen hU hf hρ hball hΛ0 hΛ _ hv']
    exact ik_add_k hρ hball hf hΛ0 hΛ hv' k1 k2
  rw [hvv, Lk_smul_v hU hf hρ hball hΛ0 hΛ, Lk_smul_v hU hf hρ hball hΛ0 hΛ,
    Lk_smul_v hU hf hρ hball hΛ0 hΛ, hsmall, smul_add]

theorem Lk_smul_k {U : Set E} (hU : IsOpen U) {f : E → F} (hf : DifferentiableOn ℂ f U) {y0 : E}
    {ρ Λ : ℝ} (hρ : 0 < ρ) (hball : ball y0 ρ ⊆ U) (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ p ∈ ball y0 ρ, ∀ q ∈ ball y0 ρ, ‖fderiv ℂ f p - fderiv ℂ f q‖ ≤ Λ * ‖p - q‖)
    (c : ℂ) (k v : E) : Lk f y0 (c • k) v = c • Lk f y0 k v := by
  by_cases hv0 : v = 0
  · subst hv0
    rw [Lk_zero_v hU hf hρ hball hΛ0 hΛ, Lk_zero_v hU hf hρ hball hΛ0 hΛ, smul_zero]
  obtain ⟨d, v', hd, hv', hvv, -⟩ := exists_small_scale ρ hρ hv0
  have hsmall : Lk f y0 (c • k) v' = c • Lk f y0 k v' := by
    rw [Lk_eq_ik_gen hU hf hρ hball hΛ0 hΛ _ hv', Lk_eq_ik_gen hU hf hρ hball hΛ0 hΛ _ hv', ik_smul_k]
  rw [hvv, Lk_smul_v hU hf hρ hball hΛ0 hΛ, Lk_smul_v hU hf hρ hball hΛ0 hΛ, hsmall, smul_comm]

theorem Lk_bound {U : Set E} (hU : IsOpen U) {f : E → F} (hf : DifferentiableOn ℂ f U) {y0 : E}
    {ρ Λ K : ℝ} (hρ : 0 < ρ) (hball : ball y0 ρ ⊆ U) (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ p ∈ ball y0 ρ, ∀ q ∈ ball y0 ρ, ‖fderiv ℂ f p - fderiv ℂ f q‖ ≤ Λ * ‖p - q‖)
    (hK0 : 0 ≤ K) (hK : ∀ p ∈ ball y0 ρ, ∀ w : E, ‖fderiv ℂ f p w‖ ≤ K * ‖w‖) (k v : E) :
    ‖Lk f y0 k v‖ ≤ (4 * K / ρ) * ‖k‖ * ‖v‖ := by
  by_cases hv0 : v = 0
  · subst hv0
    rw [Lk_zero_v hU hf hρ hball hΛ0 hΛ, norm_zero, norm_zero, mul_zero]
  obtain ⟨d, v', hd, hv', hvv, hdeq⟩ := exists_small_scale ρ hρ hv0
  have hsmall : ‖Lk f y0 k v'‖ ≤ K * ‖k‖ := by
    rw [Lk_eq_ik_gen hU hf hρ hball hΛ0 hΛ _ hv']
    refine norm_ik_le hK0 hK hv' (fun ζ hζ => ?_)
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hζ, one_mul]
    linarith
  have hLv : Lk f y0 k v = (d : ℂ) • Lk f y0 k v' := by
    conv_lhs => rw [hvv]
    exact Lk_smul_v hU hf hρ hball hΛ0 hΛ k v' (d : ℂ)
  have hd_eq : 4 * K / ρ * ‖k‖ * ‖v‖ = d * (K * ‖k‖) := by
    rw [hdeq]
    ring
  rw [hLv, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd, hd_eq]
  exact mul_le_mul_of_nonneg_left hsmall hd.le


/-- **Stage B2b, main.** Under the local hypotheses, `fderiv ℂ f` has a ℂ-linear Fréchet derivative at `y0`. -/
theorem hasFDerivAt_fderiv_local {U : Set E} (hU : IsOpen U) {f : E → F} (hf : DifferentiableOn ℂ f U) {y0 : E}
    {ρ Λ K : ℝ} (hρ : 0 < ρ) (hball : ball y0 ρ ⊆ U) (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ p ∈ ball y0 ρ, ∀ q ∈ ball y0 ρ, ‖fderiv ℂ f p - fderiv ℂ f q‖ ≤ Λ * ‖p - q‖)
    (hK0 : 0 ≤ K) (hK : ∀ p ∈ ball y0 ρ, ∀ w : E, ‖fderiv ℂ f p w‖ ≤ K * ‖w‖) :
    ∃ L : E →L[ℂ] (E →L[ℂ] F), HasFDerivAt (fun p => fderiv ℂ f p) L y0 := by
  let Lv : E → (E →L[ℂ] F) := fun k => LinearMap.mkContinuous
    { toFun := fun v => Lk f y0 k v
      map_add' := fun v w => Lk_add_v hU hf hρ hball hΛ0 hΛ k v w
      map_smul' := fun c v => by
        rw [Lk_smul_v hU hf hρ hball hΛ0 hΛ k v c]
        rfl }
    ((4 * K / ρ) * ‖k‖) (fun v => by
      have h := Lk_bound hU hf hρ hball hΛ0 hΛ hK0 hK k v
      calc ‖Lk f y0 k v‖ ≤ 4 * K / ρ * ‖k‖ * ‖v‖ := h
        _ = (4 * K / ρ * ‖k‖) * ‖v‖ := rfl)
  have hLv_apply : ∀ k v, Lv k v = Lk f y0 k v := fun k v => rfl
  have hLv_add : ∀ k1 k2, Lv (k1 + k2) = Lv k1 + Lv k2 := fun k1 k2 =>
    ContinuousLinearMap.ext fun v => by
      rw [hLv_apply, ContinuousLinearMap.add_apply, hLv_apply, hLv_apply]
      exact Lk_add_k hU hf hρ hball hΛ0 hΛ k1 k2 v
  have hLv_smul : ∀ (c : ℂ) k, Lv (c • k) = c • Lv k := fun c k =>
    ContinuousLinearMap.ext fun v => by
      rw [hLv_apply, ContinuousLinearMap.smul_apply, hLv_apply]
      exact Lk_smul_k hU hf hρ hball hΛ0 hΛ c k v
  have hLv_bound : ∀ k, ‖Lv k‖ ≤ (4 * K / ρ) * ‖k‖ := fun k =>
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => by
      rw [hLv_apply]
      have h := Lk_bound hU hf hρ hball hΛ0 hΛ hK0 hK k v
      linarith [h, show 4 * K / ρ * ‖k‖ * ‖v‖ = (4 * K / ρ * ‖k‖) * ‖v‖ from rfl])
  let Lcl : E →L[ℂ] (E →L[ℂ] F) := LinearMap.mkContinuous
    { toFun := Lv
      map_add' := hLv_add
      map_smul' := fun c k => hLv_smul c k }
    (4 * K / ρ) (fun k => by
      have h := hLv_bound k
      calc ‖Lv k‖ ≤ (4 * K / ρ) * ‖k‖ := h
        _ = (4 * K / ρ) * ‖k‖ := rfl)
  refine ⟨Lcl, ?_⟩
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hLcl : ∀ h v, Lcl h v = Lk f y0 h v := fun h v => rfl
  have hrem : ∀ h : E, ‖h‖ ≤ ρ / 8 →
      ‖fderiv ℂ f (y0 + h) - fderiv ℂ f y0 - Lcl h‖ ≤ (4 * Λ / ρ) * ‖h‖ ^ 2 := by
    intro h hh
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
    by_cases hv0 : v = 0
    · subst hv0
      simp
    obtain ⟨d, v', hd, hv', hvv, hdeq⟩ := exists_small_scale ρ hρ hv0
    have hh1 : ‖(1 : ℂ) • h‖ ≤ ρ / 8 := by
      rw [one_smul]
      exact hh
    have hq := quot_bound hU hf hρ hball hΛ0 hΛ (k := h) (v := v') (s := 1) one_ne_zero hh hh1 hv'
    simp only [inv_one, one_smul, norm_one, mul_one] at hq
    have hsmall : ‖(fderiv ℂ f (y0 + h) - fderiv ℂ f y0 - Lcl h) v'‖ ≤ Λ * ‖h‖ ^ 2 := by
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply, hLcl,
        Lk_eq_ik_gen hU hf hρ hball hΛ0 hΛ h hv']
      exact hq
    have hlin : (fderiv ℂ f (y0 + h) - fderiv ℂ f y0 - Lcl h) v =
        (d : ℂ) • (fderiv ℂ f (y0 + h) - fderiv ℂ f y0 - Lcl h) v' := by
      conv_lhs => rw [hvv]
      rw [map_smul]
    rw [hlin, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
    have hd_eq : 4 * Λ / ρ * ‖h‖ ^ 2 * ‖v‖ = d * (Λ * ‖h‖ ^ 2) := by
      rw [hdeq]
      ring
    rw [hd_eq]
    exact mul_le_mul_of_nonneg_left hsmall hd.le
  refine Asymptotics.isLittleO_iff.2 (fun c hc => ?_)
  rw [Metric.eventually_nhds_iff]
  have hMpos : 0 ≤ 4 * Λ / ρ := by positivity
  refine ⟨min (ρ / 8) (c / (4 * Λ / ρ + 1)), lt_min (by positivity) (by positivity), fun x hx => ?_⟩
  rw [dist_zero_right] at hx
  have hx1 : ‖x‖ ≤ ρ / 8 := (lt_of_lt_of_le hx (min_le_left _ _)).le
  have hx2 : ‖x‖ < c / (4 * Λ / ρ + 1) := lt_of_lt_of_le hx (min_le_right _ _)
  have hM : 4 * Λ / ρ * ‖x‖ ≤ c := by
    have h1 : ‖x‖ * (4 * Λ / ρ + 1) < c := (lt_div_iff₀ (by positivity)).1 hx2
    nlinarith [norm_nonneg x]
  show ‖fderiv ℂ f (y0 + x) - fderiv ℂ f y0 - Lcl x‖ ≤ c * ‖x‖
  calc ‖fderiv ℂ f (y0 + x) - fderiv ℂ f y0 - Lcl x‖ ≤ (4 * Λ / ρ) * ‖x‖ ^ 2 := hrem x hx1
    _ = (4 * Λ / ρ * ‖x‖) * ‖x‖ := by ring
    _ ≤ c * ‖x‖ := mul_le_mul_of_nonneg_right hM (norm_nonneg x)

end QuantumNLS.HolomorphicStageB2b
#print axioms QuantumNLS.HolomorphicStageB2b.hasFDerivAt_fderiv_local
#print axioms QuantumNLS.HolomorphicStageB2b.Lk_bound
