import Mathlib
import QuantumNLS.LocalSpectralReduced

/-! LOCAL-006, identification of the cubic Taylor coefficient (gap
LOCAL006-G3-IDENTIFICATION), generic analytic part.

* `series_isBigO`: a power series in one real variable which converges on an
  interval has remainder `O(a^N)` after its first `N` terms.
* `invSqrtM_sub_le`: the binomial series `(1 + X)^{-1/2}` agrees with
  `1 - X/2` up to `2‖X‖²` on `‖X‖ ≤ 1/2`.
* `normalized_product_cubic`: the cubic term of `A B A` for
  `A = 1 - (a²/2) W + O(a³)` and `B = a V₁ + a² V₂ + a³ V₃ + O(a⁴)` is
  `V₃ - (1/2)(W V₁ + V₁ W)`.
* `cubic_coeff_zero` and `third_coeff_of_expansion`: uniqueness of the cubic
  coefficient. A genuine power series at zero is compared, along each real
  line, with a cubic expansion with `O(a⁴)` remainder.

No source-specific statement is a hypothesis here. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open Filter Topology Asymptotics Metric
open scoped BigOperators
namespace QuantumNLS.Local006.G3Asymp
open QuantumNLS.LocalSpectral

abbrev Op2 := E2 →L[ℂ] E2

/-- Convergence on an interval gives an `O(a^N)` remainder after `N` terms. -/
theorem series_isBigO {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : ℝ → E} {c : ℕ → E} {ρ : ℝ} (hρ : 0 < ρ)
    (hs : ∀ a : ℝ, |a| < ρ → HasSum (fun k => (a : ℂ) ^ k • c k) (F a)) (N : ℕ) :
    (fun a : ℝ => F a - ∑ k ∈ Finset.range N, (a : ℂ) ^ k • c k) =O[𝓝 0]
      fun a : ℝ => a ^ N := by
  set a0 : ℝ := ρ / 2 with ha0
  have ha0p : 0 < a0 := by positivity
  have hconv := hs a0 (by rw [abs_of_pos ha0p]; linarith)
  obtain ⟨M, hM⟩ : ∃ M, ∀ k, ‖(a0 : ℂ) ^ k • c k‖ ≤ M := by
    have ht := hconv.summable.tendsto_atTop_zero.norm
    obtain ⟨M, hM⟩ := ht.bddAbove_range
    exact ⟨M, fun k => hM ⟨k, rfl⟩⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  refine IsBigO.of_bound (2 * M / a0 ^ N) ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (half_pos ha0p)] with a ha
  have ha' : |a| < a0 / 2 := by simpa [Real.dist_eq] using ha
  have haρ : |a| < ρ := by linarith
  set t : ℝ := |a| / a0 with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 / 2 := by
    rw [ht, div_le_iff₀ ha0p]; linarith
  have hterm : ∀ k, ‖(a : ℂ) ^ k • c k‖ ≤ M * t ^ k := by
    intro k
    have h1 : ‖(a : ℂ) ^ k • c k‖ = t ^ k * ‖(a0 : ℂ) ^ k • c k‖ := by
      rw [norm_smul, norm_smul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ha0p, ht, div_pow]
      field_simp
    rw [h1, mul_comm M]
    exact mul_le_mul_of_nonneg_left (hM k) (by positivity)
  have htail := (hasSum_nat_add_iff' N).mpr (hs a haρ)
  have hgeo : HasSum (fun k : ℕ => M * t ^ N * t ^ k) (M * t ^ N * (1 - t)⁻¹) :=
    (hasSum_geometric_of_lt_one ht0 (by linarith)).mul_left _
  have hle := htail.norm_le_of_bounded hgeo (fun k => by
    have h := hterm (k + N)
    calc ‖(a : ℂ) ^ (k + N) • c (k + N)‖ ≤ M * t ^ (k + N) := h
      _ = M * t ^ N * t ^ k := by rw [pow_add]; ring)
  have hinv : (1 - t)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hpos : 0 ≤ M * t ^ N := by positivity
  calc ‖F a - ∑ k ∈ Finset.range N, (a : ℂ) ^ k • c k‖ ≤ M * t ^ N * (1 - t)⁻¹ := hle
    _ ≤ M * t ^ N * 2 := mul_le_mul_of_nonneg_left hinv hpos
    _ = 2 * M / a0 ^ N * ‖a ^ N‖ := by
      rw [norm_pow, Real.norm_eq_abs, ht, div_pow]
      field_simp

lemma invSqrtCoeff_zero' : invSqrtCoeff 0 = 1 := by simp [invSqrtCoeff]

lemma invSqrtCoeff_one' : invSqrtCoeff 1 = -(1 / 2) := by simp [invSqrtCoeff]

/-- Second-order accuracy of the binomial inverse square root about the identity. -/
theorem invSqrtM_sub_le (X : Op2) (hX : ‖X‖ ≤ 1 / 2) :
    ‖invSqrtM (1 + X) - (1 - (1 / 2 : ℂ) • X)‖ ≤ 2 * ‖X‖ ^ 2 := by
  have h1 : ‖(1 + X) - 1‖ < 1 := by rw [add_sub_cancel_left]; linarith
  have hs := hasSum_invSqrtM h1
  rw [add_sub_cancel_left] at hs
  have ht := (hasSum_nat_add_iff' 2).mpr hs
  have hfirst : ∑ i ∈ Finset.range 2, (invSqrtCoeff i : ℂ) • X ^ i = 1 - (1 / 2 : ℂ) • X := by
    rw [Finset.sum_range_succ, Finset.sum_range_one, invSqrtCoeff_zero', invSqrtCoeff_one',
      pow_zero, pow_one]
    push_cast
    module
  rw [hfirst] at ht
  have hx0 : 0 ≤ ‖X‖ := norm_nonneg _
  have hgeo : HasSum (fun k : ℕ => ‖X‖ ^ 2 * ‖X‖ ^ k) (‖X‖ ^ 2 * (1 - ‖X‖)⁻¹) :=
    (hasSum_geometric_of_lt_one hx0 (by linarith)).mul_left _
  have hle := ht.norm_le_of_bounded hgeo (fun k => by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    calc |invSqrtCoeff (k + 2)| * ‖X ^ (k + 2)‖ ≤ 1 * ‖X‖ ^ (k + 2) :=
          mul_le_mul (abs_invSqrtCoeff_le _) (norm_pow_le _ _) (norm_nonneg _) zero_le_one
      _ = ‖X‖ ^ 2 * ‖X‖ ^ k := by ring)
  have hinv : (1 - ‖X‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  calc _ ≤ ‖X‖ ^ 2 * (1 - ‖X‖)⁻¹ := hle
    _ ≤ ‖X‖ ^ 2 * 2 := mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = 2 * ‖X‖ ^ 2 := by ring

/-- Powers near zero: `a^k = O(a^j)` for `j ≤ k`. -/
lemma pow_isBigO_pow {j k : ℕ} (hjk : j ≤ k) :
    (fun a : ℝ => a ^ k) =O[𝓝 0] fun a : ℝ => a ^ j := by
  have h1 : (fun a : ℝ => a ^ (k - j)) =O[𝓝 0] (fun _ : ℝ => (1 : ℝ)) :=
    ((continuous_pow (k - j)).tendsto (0 : ℝ)).isBigO_one ℝ
  have h := (isBigO_refl (fun a : ℝ => a ^ j) (𝓝 0)).mul h1
  refine h.congr_left (fun a => ?_) |>.congr_right (fun a => by ring)
  rw [← pow_add, Nat.add_sub_cancel' hjk]

/-- A continuous function is `O(1)` at zero. -/
lemma continuous_isBigO_one {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} (hf : Continuous f) :
    f =O[𝓝 0] fun _ : ℝ => (1 : ℝ) :=
  (hf.tendsto 0).isBigO_one ℝ

/-- Complex powers of a real variable have the same size as the real powers. -/
lemma cpow_isBigO (k : ℕ) : (fun a : ℝ => (a : ℂ) ^ k) =O[𝓝 0] fun a : ℝ => a ^ k :=
  isBigO_of_le _ (fun a => by rw [norm_pow, norm_pow, Complex.norm_real])

/-- `a^k • Y(a)` with `Y` continuous is `O(a^k)`. -/
lemma smul_cont_isBigO {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (k : ℕ)
    {Y : ℝ → E} (hY : Continuous Y) :
    (fun a : ℝ => (a : ℂ) ^ k • Y a) =O[𝓝 0] fun a : ℝ => a ^ k := by
  have h := (cpow_isBigO k).smul (continuous_isBigO_one hY)
  exact h.congr_right (fun a => by simp)

/-- The exact polynomial identity behind the normalized cubic term. -/
lemma polynomial_part (a : ℝ) (W V1 V2 V3 : Op2) :
    (1 - ((a : ℂ) ^ 2 / 2) • W) *
        ((a : ℂ) • V1 + (a : ℂ) ^ 2 • V2 + (a : ℂ) ^ 3 • V3) *
        (1 - ((a : ℂ) ^ 2 / 2) • W) -
      ((a : ℂ) • V1 + (a : ℂ) ^ 2 • V2 +
        (a : ℂ) ^ 3 • (V3 - (1 / 2 : ℂ) • (W * V1 + V1 * W))) =
      (a : ℂ) ^ 4 • (-(1 / 2 : ℂ) • (W * V2 + V2 * W) - ((a : ℂ) / 2) • (W * V3 + V3 * W) +
        ((a : ℂ) / 4) • (W * V1 * W + (a : ℂ) • (W * V2 * W) + (a : ℂ) ^ 2 • (W * V3 * W))) := by
  simp only [sub_mul, mul_sub, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc,
    mul_smul_comm, smul_add, smul_sub, smul_smul, mul_assoc]
  module

lemma key_identity {R : Type*} [Ring R] (A B A0 B0 P : R) :
    A * B * A - P = (A - A0) * B * A + A0 * (B - B0) * A + A0 * B0 * (A - A0) +
      (A0 * B0 * A0 - P) := by
  noncomm_ring

/-- The cubic coefficient of the normalized product `A B A`. -/
theorem normalized_product_cubic {A B : ℝ → Op2} {W V1 V2 V3 : Op2}
    (hA : (fun a : ℝ => A a - (1 - ((a : ℂ) ^ 2 / 2) • W)) =O[𝓝 0] fun a : ℝ => a ^ 3)
    (hB : (fun a : ℝ => B a - ((a : ℂ) • V1 + (a : ℂ) ^ 2 • V2 + (a : ℂ) ^ 3 • V3)) =O[𝓝 0]
      fun a : ℝ => a ^ 4) :
    (fun a : ℝ => A a * B a * A a - ((a : ℂ) • V1 + (a : ℂ) ^ 2 • V2 +
      (a : ℂ) ^ 3 • (V3 - (1 / 2 : ℂ) • (W * V1 + V1 * W)))) =O[𝓝 0] fun a : ℝ => a ^ 4 := by
  set A0 : ℝ → Op2 := fun a => 1 - ((a : ℂ) ^ 2 / 2) • W with hA0
  set B0 : ℝ → Op2 := fun a => (a : ℂ) • V1 + (a : ℂ) ^ 2 • V2 + (a : ℂ) ^ 3 • V3 with hB0
  set Y : ℝ → Op2 := fun a => -(1 / 2 : ℂ) • (W * V2 + V2 * W) - ((a : ℂ) / 2) • (W * V3 + V3 * W) +
        ((a : ℂ) / 4) • (W * V1 * W + (a : ℂ) • (W * V2 * W) + (a : ℂ) ^ 2 • (W * V3 * W)) with hY
  have hA0c : Continuous A0 := by rw [hA0]; fun_prop
  have hYc : Continuous Y := by rw [hY]; fun_prop
  have hB0O : B0 =O[𝓝 0] fun a : ℝ => a ^ 1 := by
    have hc : Continuous fun a : ℝ => V1 + (a : ℂ) • V2 + (a : ℂ) ^ 2 • V3 := by fun_prop
    refine (smul_cont_isBigO 1 hc).congr_left (fun a => ?_)
    simp only [hB0, pow_one, smul_add, smul_smul]
    congr 2 <;> ring_nf
  have hBO : B =O[𝓝 0] fun a : ℝ => a ^ 1 := by
    have h := (hB.trans (pow_isBigO_pow (by norm_num : 1 ≤ 4))).add hB0O
    exact h.congr_left (fun a => by simp [hB0])
  have hA0O : A0 =O[𝓝 0] fun _ : ℝ => (1 : ℝ) := continuous_isBigO_one hA0c
  have hA1 : (fun a : ℝ => A a - A0 a) =O[𝓝 0] fun _ : ℝ => (1 : ℝ) :=
    hA.trans (((continuous_pow 3).tendsto (0 : ℝ)).isBigO_one ℝ)
  have hAO : A =O[𝓝 0] fun _ : ℝ => (1 : ℝ) :=
    (hA1.add hA0O).congr_left (fun a => by simp)
  have t1 : (fun a : ℝ => (A a - A0 a) * B a * A a) =O[𝓝 0] fun a : ℝ => a ^ 4 :=
    ((hA.mul hBO).mul hAO).congr_right (fun a => by ring)
  have t2 : (fun a : ℝ => A0 a * (B a - B0 a) * A a) =O[𝓝 0] fun a : ℝ => a ^ 4 :=
    ((hA0O.mul hB).mul hAO).congr_right (fun a => by ring)
  have t3 : (fun a : ℝ => A0 a * B0 a * (A a - A0 a)) =O[𝓝 0] fun a : ℝ => a ^ 4 :=
    ((hA0O.mul hB0O).mul hA).congr_right (fun a => by ring)
  have t4 : (fun a : ℝ => (a : ℂ) ^ 4 • Y a) =O[𝓝 0] fun a : ℝ => a ^ 4 :=
    smul_cont_isBigO 4 hYc
  refine (((t1.add t2).add t3).add t4).congr_left (fun a => ?_)
  have hp : A0 a * B0 a * A0 a - ((a : ℂ) • V1 + (a : ℂ) ^ 2 • V2 +
      (a : ℂ) ^ 3 • (V3 - (1 / 2 : ℂ) • (W * V1 + V1 * W))) = (a : ℂ) ^ 4 • Y a :=
    polynomial_part a W V1 V2 V3
  rw [key_identity (A a) (B a) (A0 a) (B0 a), hp]

/-- A cubic polynomial in one real variable which is `O(a⁴)` has zero cubic coefficient. -/
theorem cubic_coeff_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (d0 d1 d2 d3 : E)
    (h : (fun a : ℝ => d0 + (a : ℂ) • d1 + (a : ℂ) ^ 2 • d2 + (a : ℂ) ^ 3 • d3) =O[𝓝 0]
      fun a : ℝ => a ^ 4) : d3 = 0 := by
  set P : ℝ → E := fun a => d0 + (a : ℂ) • d1 + (a : ℂ) ^ 2 • d2 + (a : ℂ) ^ 3 • d3 with hP
  obtain ⟨C, hC⟩ := h.bound
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.mp hC
  have hb : ∀ a : ℝ, |a| < ε → ‖P a‖ ≤ C * a ^ 4 := by
    intro a ha
    have h' := hεb (show dist a 0 < ε by simpa [Real.dist_eq] using ha)
    have h4 : ‖a ^ 4‖ = a ^ 4 := by
      rw [norm_pow, Real.norm_eq_abs, pow_abs, abs_of_nonneg (by positivity)]
    rwa [h4] at h'
  have hid : ∀ a : ℝ, P (3 * a) - (3 : ℂ) • P (2 * a) + (3 : ℂ) • P a - P 0 =
      (6 * (a : ℂ) ^ 3) • d3 := by
    intro a
    simp only [hP]
    push_cast
    module
  have hsmall : ∀ a : ℝ, 0 < a → a < ε / 3 → ‖d3‖ ≤ 22 * C * a := by
    intro a ha0 haε
    have e3 := hb (3 * a) (by rw [abs_of_pos (by linarith)]; linarith)
    have e2 := hb (2 * a) (by rw [abs_of_pos (by linarith)]; linarith)
    have e1 := hb a (by rw [abs_of_pos ha0]; linarith)
    have e0 := hb 0 (by simpa using hε)
    have hn : ‖(6 * (a : ℂ) ^ 3) • d3‖ ≤ 132 * C * a ^ 4 := by
      rw [← hid a]
      calc ‖P (3 * a) - (3 : ℂ) • P (2 * a) + (3 : ℂ) • P a - P 0‖
          ≤ ‖P (3 * a)‖ + 3 * ‖P (2 * a)‖ + 3 * ‖P a‖ + ‖P 0‖ := by
            have n1 := norm_sub_le (P (3 * a) - (3 : ℂ) • P (2 * a) + (3 : ℂ) • P a) (P 0)
            have n2 := norm_add_le (P (3 * a) - (3 : ℂ) • P (2 * a)) ((3 : ℂ) • P a)
            have n3 := norm_sub_le (P (3 * a)) ((3 : ℂ) • P (2 * a))
            have s1 : ‖(3 : ℂ) • P (2 * a)‖ = 3 * ‖P (2 * a)‖ := by rw [norm_smul]; norm_num
            have s2 : ‖(3 : ℂ) • P a‖ = 3 * ‖P a‖ := by rw [norm_smul]; norm_num
            linarith
        _ ≤ C * (3 * a) ^ 4 + 3 * (C * (2 * a) ^ 4) + 3 * (C * a ^ 4) + C * 0 ^ 4 := by
            gcongr
        _ = 132 * C * a ^ 4 := by ring
    have hn' : ‖(6 * (a : ℂ) ^ 3) • d3‖ = 6 * a ^ 3 * ‖d3‖ := by
      rw [norm_smul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0]
      norm_num
    rw [hn'] at hn
    have ha3 : 0 < 6 * a ^ 3 := by positivity
    have : 6 * a ^ 3 * ‖d3‖ ≤ 6 * a ^ 3 * (22 * C * a) := by nlinarith
    exact le_of_mul_le_mul_left this ha3
  have hlim : Tendsto (fun a : ℝ => 22 * C * a) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h0 : Tendsto (fun a : ℝ => 22 * C * a) (𝓝 (0 : ℝ)) (𝓝 (22 * C * 0)) :=
      ((continuous_const.mul continuous_id).tendsto 0)
    rw [mul_zero] at h0
    exact tendsto_nhdsWithin_of_tendsto_nhds h0
  have hev : ∀ᶠ a in 𝓝[>] (0 : ℝ), ‖d3‖ ≤ 22 * C * a := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < ε / 3 by positivity)] with a ha
    exact hsmall a ha.1 ha.2
  have hle : ‖d3‖ ≤ 0 := ge_of_tendsto hlim hev
  exact norm_le_zero_iff.mp hle

/-- Uniqueness of the cubic Taylor coefficient: the coordinate of `p 3` along
`u` equals the cubic coefficient of any cubic expansion of `a ↦ G (a • u) n`
with `O(a⁴)` remainder. -/
theorem third_coeff_of_expansion {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {G : X → lp (fun _ : ℤ => ℂ) 2}
    {p : FormalMultilinearSeries ℝ X (lp (fun _ : ℤ => ℂ) 2)}
    (hp : HasFPowerSeriesAt G p 0) (u : X) (n : ℤ) (c1 c2 c3 : ℂ)
    (h : (fun a : ℝ => G (a • u) n - ((a : ℂ) * c1 + (a : ℂ) ^ 2 * c2 + (a : ℂ) ^ 3 * c3))
      =O[𝓝 0] fun a : ℝ => a ^ 4) :
    p 3 (fun _ => u) n = c3 := by
  have hT : Tendsto (fun a : ℝ => a • u) (𝓝 0) (𝓝 0) := by
    have h0 : Tendsto (fun a : ℝ => a • u) (𝓝 0) (𝓝 ((0 : ℝ) • u)) :=
      (continuous_id.smul continuous_const).tendsto 0
    rwa [zero_smul] at h0
  have hO := (hp.isBigO_sub_partialSum_pow 4).comp_tendsto hT
  have hO' : (fun a : ℝ => G (a • u) - p.partialSum 4 (a • u)) =O[𝓝 0] fun a : ℝ => a ^ 4 := by
    refine (hO.congr_left (fun a => by simp)).trans ?_
    refine isBigO_of_le' (c := ‖u‖ ^ 4) _ (fun a => ?_)
    simp only [Function.comp_apply, norm_smul, Real.norm_eq_abs, mul_pow, norm_pow]
    rw [abs_of_nonneg (by positivity), mul_comm]
  have hcoord : (fun a : ℝ => (G (a • u) - p.partialSum 4 (a • u)) n) =O[𝓝 0]
      fun a : ℝ => a ^ 4 :=
    (isBigO_of_le _ (fun a => lp.norm_apply_le_norm (by norm_num) _ n)).trans hO'
  have hterm : ∀ (k : ℕ) (a : ℝ), p k (fun _ => a • u) n = (a : ℂ) ^ k * p k (fun _ => u) n := by
    intro k a
    have hm := (p k).map_smul_univ (fun _ => a) (fun _ => u)
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hm
    rw [hm, lp.coeFn_smul, Pi.smul_apply, Complex.real_smul, Complex.ofReal_pow]
  set q : ℕ → ℂ := fun k => p k (fun _ => u) n with hq
  have hdiff := hcoord.sub h
  have hfinal : (fun a : ℝ => (q 0 - 0) + (a : ℂ) • (q 1 - c1) + (a : ℂ) ^ 2 • (q 2 - c2) +
      (a : ℂ) ^ 3 • (q 3 - c3)) =O[𝓝 0] fun a : ℝ => a ^ 4 := by
    refine (hdiff.neg_left).congr_left (fun a => ?_)
    simp only [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, lp.coeFn_sub, Pi.sub_apply, lp.coeFn_add, Pi.add_apply, smul_eq_mul]
    rw [hterm 0 a, hterm 1 a, hterm 2 a, hterm 3 a]
    ring
  have h3 := cubic_coeff_zero _ _ _ _ hfinal
  exact sub_eq_zero.mp h3

end QuantumNLS.Local006.G3Asymp

#print axioms QuantumNLS.Local006.G3Asymp.series_isBigO
#print axioms QuantumNLS.Local006.G3Asymp.invSqrtM_sub_le
#print axioms QuantumNLS.Local006.G3Asymp.normalized_product_cubic
#print axioms QuantumNLS.Local006.G3Asymp.cubic_coeff_zero
#print axioms QuantumNLS.Local006.G3Asymp.third_coeff_of_expansion

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local006.G3Asymp." ||
        n.toString.startsWith "_private.QuantumNLS.Local006G3Asymp" then
      pending := pending.push n
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"Local006G3Asymp audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
