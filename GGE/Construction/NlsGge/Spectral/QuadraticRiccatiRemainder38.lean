import NlsGge.Sobolev.PeriodicBridge
import Mathlib

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology BigOperators
namespace NlsGge.SpectralFoundations
open NlsGge.Pilot

/-! # R3b: the quadratic Riccati term is exact in Fourier variables

`q_η(u) = Σ_n |û_n|² · 2η/(4η² + 4π²n²)`, its asymptotic expansion in `1/η` up to order `2k+1`
with remainder bounded by the `H^k`-tail `Σ (πn)^{2k} |û_n|² min(1, (πn/η)²)`, and the
vanishing of that tail as `η → ∞`. -/

/-- `q_η(u) = Σ_n |û_n|² · 2η/(4η² + 4π²n²)`. -/
def quadRiccati38 (u : PhysicalL2) (η : ℝ) : ℝ :=
  ∑' n : ℤ, ‖physicalFourier u n‖ ^ 2 * (2 * η / (4 * η ^ 2 + 4 * Real.pi ^ 2 * (n:ℝ) ^ 2))

/-- The Sobolev weight `⟨n⟩^{2k}` equals `(1+n²)^k`. -/
theorem japaneseBracket_rpow_two_nat38 (k : ℕ) (n : ℤ) :
    Real.rpow (japaneseBracket n) (2 * (k : ℝ)) = (1 + (n : ℝ) ^ 2) ^ k := by
  unfold japaneseBracket
  rw [Real.sqrt_eq_rpow]
  show ((1 + (n : ℝ) ^ 2) ^ ((1:ℝ)/2)) ^ (2 * (k:ℝ)) = _
  rw [← Real.rpow_mul (by positivity)]
  have : (1:ℝ)/2 * (2 * (k:ℝ)) = (k:ℝ) := by ring
  rw [this, Real.rpow_natCast]

/-- `H^k` square summability as summability of `(1+n²)^k |û_n|²`. -/
theorem summable_sobolev_nat38 (k : ℕ) (u : PhysicalL2)
    (hu : SobolevSquareSummable (k : ℝ) (physicalFourier u)) :
    Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2) ^ k * ‖physicalFourier u n‖ ^ 2) := by
  have := hu
  unfold SobolevSquareSummable at this
  refine this.congr (fun n => ?_)
  rw [japaneseBracket_rpow_two_nat38]

theorem summable_pow_mul_sq38 (k j : ℕ) (hj : j ≤ k) (c : ℝ) (u : PhysicalL2)
    (hu : SobolevSquareSummable (k : ℝ) (physicalFourier u)) :
    Summable (fun n : ℤ => (c * (n : ℝ)) ^ (2 * j) * ‖physicalFourier u n‖ ^ 2) := by
  have hS := (summable_sobolev_nat38 k u hu).mul_left (|c| ^ (2 * j))
  refine Summable.of_norm_bounded hS (fun n => ?_)
  have h1 : (n : ℝ) ^ (2 * j) ≤ (1 + (n : ℝ) ^ 2) ^ k := by
    rw [pow_mul]
    calc ((n:ℝ) ^ 2) ^ j ≤ (1 + (n : ℝ) ^ 2) ^ j :=
          pow_le_pow_left₀ (by positivity) (by linarith) j
      _ ≤ (1 + (n : ℝ) ^ 2) ^ k := pow_le_pow_right₀ (by nlinarith [sq_nonneg (n:ℝ)]) hj
  have h2 : 0 ≤ ‖physicalFourier u n‖ ^ 2 := by positivity
  have h3 : 0 ≤ (c * (n : ℝ)) ^ (2 * j) := by
    rw [pow_mul]; positivity
  rw [Real.norm_of_nonneg (mul_nonneg h3 h2), mul_pow]
  have h4 : 0 ≤ c ^ (2 * j) := by rw [pow_mul]; positivity
  have h5 : c ^ (2 * j) = |c| ^ (2 * j) := by
    rw [pow_mul, pow_mul, sq_abs]
  rw [h5, mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 h2) (by positivity)

/-- Geometric-sum identity. -/
theorem geom_neg_aux38 (x : ℝ) (m : ℕ) :
    (1 + x) * ∑ j ∈ Finset.range m, (-x) ^ j = 1 - (-x) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih]; ring

/-- The termwise exact identity. -/
theorem quad_term_identity38 (k : ℕ) (a t η : ℝ) (hη : 0 < η) :
    η ^ (2 * k + 1) * (a * (2 * η / (4 * η ^ 2 + 4 * t ^ 2)) -
      ∑ j ∈ Finset.range (k + 1), (-1:ℝ) ^ j / (2 * 4 ^ j * η ^ (2 * j + 1)) *
        ((2 * t) ^ (2 * j) * a)) =
    (1 / 2) * (-1) ^ (k + 1) * (t ^ (2 * k) * a * ((t / η) ^ 2 / (1 + (t / η) ^ 2))) := by
  have hη0 : η ≠ 0 := hη.ne'
  set x : ℝ := (t / η) ^ 2 with hx
  have hx0 : 0 ≤ x := by positivity
  have h1x : (1 + x) ≠ 0 := by positivity
  have hterm : ∀ j : ℕ, (-1:ℝ) ^ j / (2 * 4 ^ j * η ^ (2 * j + 1)) * ((2 * t) ^ (2 * j) * a) =
      a / (2 * η) * (-x) ^ j := by
    intro j
    have e1 : (2 * t) ^ (2 * j) = 4 ^ j * t ^ (2 * j) := by
      rw [mul_pow, pow_mul, pow_mul]; norm_num
    have e2 : (-x) ^ j = (-1) ^ j * (t ^ (2 * j) / η ^ (2 * j)) := by
      rw [hx, neg_pow, ← pow_mul, div_pow, mul_comm 2 j]
    have e3 : η ^ (2 * j + 1) = η ^ (2 * j) * η := pow_succ _ _
    rw [e1, e2, e3]
    have : η ^ (2 * j) ≠ 0 := pow_ne_zero _ hη0
    field_simp
  rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum]
  have hgeo := geom_neg_aux38 x (k + 1)
  have hsum : ∑ j ∈ Finset.range (k + 1), (-x) ^ j = (1 - (-x) ^ (k + 1)) / (1 + x) := by
    field_simp; linarith
  have hf : a * (2 * η / (4 * η ^ 2 + 4 * t ^ 2)) = a / (2 * η) * (1 / (1 + x)) := by
    rw [hx, div_pow]
    field_simp
    ring
  rw [hsum, hf]
  have hxk : η ^ (2 * k) * x ^ k = t ^ (2 * k) := by
    have : x ^ k = t ^ (2 * k) / η ^ (2 * k) := by
      rw [hx, ← pow_mul, div_pow, mul_comm 2 k]
    rw [this]
    have : η ^ (2 * k) ≠ 0 := pow_ne_zero _ hη0
    field_simp
  have : (-x) ^ (k + 1) = (-1) ^ (k + 1) * (x ^ k * x) := by
    rw [neg_pow, pow_succ x k]
  rw [this]
  have e : η ^ (2 * k + 1) = η ^ (2 * k) * η := pow_succ _ _
  rw [e]
  field_simp
  have hk : t ^ (2 * k) = η ^ (2 * k) * x ^ k := hxk.symm
  rw [hk]
  ring

theorem quadRiccati38_remainder (k : ℕ) (u : PhysicalL2)
    (hu : SobolevSquareSummable (k : ℝ) (physicalFourier u)) (η : ℝ) (hη : 0 < η) :
    |η ^ (2*k+1) * (quadRiccati38 u η -
        ∑ j ∈ Finset.range (k + 1), (-1:ℝ)^j / (2 * 4^j * η^(2*j+1)) *
          ∑' n : ℤ, (2*Real.pi*n)^(2*j) * ‖physicalFourier u n‖ ^ 2)| ≤
      (1/2) * ∑' n : ℤ, (Real.pi*n)^(2*k) * ‖physicalFourier u n‖ ^ 2 *
        min 1 ((Real.pi*n/η)^2) := by
  have hη0 : η ≠ 0 := hη.ne'
  set a : ℤ → ℝ := fun n => ‖physicalFourier u n‖ ^ 2 with ha
  have ha0 : ∀ n, 0 ≤ a n := fun n => by positivity
  have haS : Summable a := summable_physicalFourier_sq u
  have hF : ∀ j, j ≤ k → Summable (fun n : ℤ => (2 * Real.pi * (n:ℝ)) ^ (2 * j) * a n) :=
    fun j hj => summable_pow_mul_sq38 k j hj (2 * Real.pi) u hu
  have hb : Summable (fun n : ℤ => (Real.pi * (n:ℝ)) ^ (2 * k) * a n) :=
    summable_pow_mul_sq38 k k le_rfl Real.pi u hu
  have hf : Summable (fun n : ℤ => a n * (2 * η / (4 * η ^ 2 + 4 * Real.pi ^ 2 * (n:ℝ) ^ 2))) := by
    refine Summable.of_norm_bounded (haS.mul_right (1 / (2 * η))) (fun n => ?_)
    have hd : 0 < 4 * η ^ 2 + 4 * Real.pi ^ 2 * (n:ℝ) ^ 2 := by positivity
    have hq0 : 0 ≤ 2 * η / (4 * η ^ 2 + 4 * Real.pi ^ 2 * (n:ℝ) ^ 2) := by positivity
    rw [Real.norm_of_nonneg (mul_nonneg (ha0 n) hq0)]
    refine mul_le_mul_of_nonneg_left ?_ (ha0 n)
    rw [div_le_div_iff₀ hd (by positivity)]
    nlinarith [sq_nonneg (Real.pi * (n:ℝ)), mul_pos hη hη]
  -- the sum over j of the termwise coefficients
  have hc : ∀ j ∈ Finset.range (k + 1), Summable (fun n : ℤ =>
      (-1:ℝ) ^ j / (2 * 4 ^ j * η ^ (2 * j + 1)) * ((2 * (Real.pi * (n:ℝ))) ^ (2 * j) * a n)) := by
    intro j hj
    have := (hF j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).mul_left
      ((-1:ℝ) ^ j / (2 * 4 ^ j * η ^ (2 * j + 1)))
    refine this.congr (fun n => ?_)
    show _ = _
    rw [← mul_assoc 2 Real.pi (n:ℝ)]
  set g : ℤ → ℝ := fun n =>
    (1 / 2) * (-1) ^ (k + 1) * ((Real.pi * (n:ℝ)) ^ (2 * k) * a n *
      (((Real.pi * (n:ℝ)) / η) ^ 2 / (1 + ((Real.pi * (n:ℝ)) / η) ^ 2))) with hg
  set bd : ℤ → ℝ := fun n =>
    (1 / 2) * ((Real.pi * (n:ℝ)) ^ (2 * k) * a n * min 1 (((Real.pi * (n:ℝ)) / η) ^ 2)) with hbd
  have hbd_le : ∀ n, ‖g n‖ ≤ bd n := by
    intro n
    set t : ℝ := Real.pi * (n:ℝ) with ht
    have hp : 0 ≤ t ^ (2 * k) := by rw [pow_mul]; positivity
    have hx0 : 0 ≤ (t / η) ^ 2 := by positivity
    have hq0 : 0 ≤ (t / η) ^ 2 / (1 + (t / η) ^ 2) := by positivity
    have hq1 : (t / η) ^ 2 / (1 + (t / η) ^ 2) ≤ min 1 ((t / η) ^ 2) := by
      apply le_min
      · rw [div_le_one (by positivity)]; linarith
      · rw [div_le_iff₀ (by positivity)]; nlinarith
    rw [hg, hbd]
    simp only
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one,
      Real.norm_of_nonneg (mul_nonneg (mul_nonneg hp (ha0 n)) hq0)]
    rw [Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq1 (mul_nonneg hp (ha0 n)))
      (by norm_num)
  have hbd_sum : Summable bd := by
    refine Summable.of_norm_bounded (hb.mul_left (1 / 2)) (fun n => ?_)
    have hp : 0 ≤ (Real.pi * (n:ℝ)) ^ (2 * k) := by rw [pow_mul]; positivity
    have hm0 : 0 ≤ min 1 (((Real.pi * (n:ℝ)) / η) ^ 2) := le_min zero_le_one (by positivity)
    have hbn : 0 ≤ bd n := by rw [hbd]; simp only; positivity
    rw [Real.norm_of_nonneg hbn, hbd]
    simp only
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    calc (Real.pi * (n:ℝ)) ^ (2 * k) * a n * min 1 (((Real.pi * (n:ℝ)) / η) ^ 2)
        ≤ (Real.pi * (n:ℝ)) ^ (2 * k) * a n * 1 :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) (mul_nonneg hp (ha0 n))
      _ = _ := mul_one _
  have hg_sum : Summable g :=
    Summable.of_norm_bounded hbd_sum hbd_le
  -- the left-hand side is the sum of g
  have hterm : ∀ n : ℤ, η ^ (2 * k + 1) * (a n * (2 * η / (4 * η ^ 2 + 4 * Real.pi ^ 2 * (n:ℝ) ^ 2)) -
      ∑ j ∈ Finset.range (k + 1), (-1:ℝ) ^ j / (2 * 4 ^ j * η ^ (2 * j + 1)) *
        ((2 * (Real.pi * (n:ℝ))) ^ (2 * j) * a n)) = g n := by
    intro n
    have := quad_term_identity38 k (a n) (Real.pi * (n:ℝ)) η hη
    have e : 4 * η ^ 2 + 4 * Real.pi ^ 2 * (n:ℝ) ^ 2 = 4 * η ^ 2 + 4 * (Real.pi * (n:ℝ)) ^ 2 := by
      ring
    rw [hg]
    simp only
    rw [e]
    exact this
  have hLHS : η ^ (2*k+1) * (quadRiccati38 u η -
        ∑ j ∈ Finset.range (k + 1), (-1:ℝ)^j / (2 * 4^j * η^(2*j+1)) *
          ∑' n : ℤ, (2*Real.pi*n)^(2*j) * ‖physicalFourier u n‖ ^ 2) = ∑' n, g n := by
    have h1 : ∀ j ∈ Finset.range (k + 1), (-1:ℝ)^j / (2 * 4^j * η^(2*j+1)) *
          ∑' n : ℤ, (2*Real.pi*n)^(2*j) * ‖physicalFourier u n‖ ^ 2 =
        ∑' n : ℤ, (-1:ℝ) ^ j / (2 * 4 ^ j * η ^ (2 * j + 1)) *
          ((2 * (Real.pi * (n:ℝ))) ^ (2 * j) * a n) := by
      intro j hj
      rw [← Summable.tsum_mul_left _ (hF j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))]
      refine tsum_congr (fun n => ?_)
      rw [← mul_assoc 2 Real.pi (n:ℝ)]
    rw [Finset.sum_congr rfl h1, ← Summable.tsum_finsetSum hc]
    unfold quadRiccati38
    rw [← Summable.tsum_sub hf (summable_sum hc), ← Summable.tsum_mul_left _
      (hf.sub (summable_sum hc))]
    exact tsum_congr hterm
  rw [hLHS]
  have hbd_tsum : (1/2) * ∑' n : ℤ, (Real.pi*n)^(2*k) * ‖physicalFourier u n‖ ^ 2 *
        min 1 ((Real.pi*n/η)^2) = ∑' n, bd n := by
    have hs : Summable (fun n : ℤ => (Real.pi*n)^(2*k) * ‖physicalFourier u n‖ ^ 2 *
        min 1 ((Real.pi*n/η)^2)) := by
      refine (hbd_sum.mul_left 2).congr (fun n => ?_)
      rw [hbd]; simp only; ring
    rw [← Summable.tsum_mul_left _ hs]
  rw [hbd_tsum]
  calc |∑' n, g n| = ‖∑' n, g n‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' n, ‖g n‖ := norm_tsum_le_tsum_norm hg_sum.norm
    _ ≤ ∑' n, bd n := hg_sum.norm.tsum_le_tsum hbd_le hbd_sum

theorem quadRiccati38_remainder_tendsto (k : ℕ) (u : PhysicalL2)
    (hu : SobolevSquareSummable (k : ℝ) (physicalFourier u)) :
    Tendsto (fun η : ℝ => ∑' n : ℤ, (Real.pi*n)^(2*k) * ‖physicalFourier u n‖ ^ 2 *
      min 1 ((Real.pi*n/η)^2)) atTop (𝓝 0) := by
  have hb : Summable (fun n : ℤ => (Real.pi * (n:ℝ)) ^ (2 * k) * ‖physicalFourier u n‖ ^ 2) :=
    summable_pow_mul_sq38 k k le_rfl Real.pi u hu
  have h0 : (0:ℝ) = ∑' n : ℤ, (0:ℝ) := by simp
  rw [h0]
  refine tendsto_tsum_of_dominated_convergence (bound := fun n : ℤ =>
    (Real.pi * (n:ℝ)) ^ (2 * k) * ‖physicalFourier u n‖ ^ 2) hb (fun n => ?_) ?_
  · have hdiv : Tendsto (fun η : ℝ => Real.pi * (n:ℝ) / η) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have hsq : Tendsto (fun η : ℝ => (Real.pi * (n:ℝ) / η) ^ 2) atTop (𝓝 0) := by
      simpa using hdiv.pow 2
    have hm : Tendsto (fun η : ℝ => min 1 ((Real.pi * (n:ℝ) / η) ^ 2)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := (1:ℝ))).min hsq
    simpa using hm.const_mul ((Real.pi * (n:ℝ)) ^ (2 * k) * ‖physicalFourier u n‖ ^ 2)
  · refine Eventually.of_forall (fun η n => ?_)
    have hp : 0 ≤ (Real.pi * (n:ℝ)) ^ (2 * k) := by rw [pow_mul]; positivity
    have hnn : 0 ≤ (Real.pi * (n:ℝ)) ^ (2 * k) * ‖physicalFourier u n‖ ^ 2 := by positivity
    have hm0 : 0 ≤ min 1 ((Real.pi * (n:ℝ) / η) ^ 2) := le_min zero_le_one (by positivity)
    rw [Real.norm_of_nonneg (mul_nonneg hnn hm0)]
    calc _ ≤ (Real.pi * (n:ℝ)) ^ (2 * k) * ‖physicalFourier u n‖ ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hnn
      _ = _ := mul_one _

end NlsGge.SpectralFoundations
