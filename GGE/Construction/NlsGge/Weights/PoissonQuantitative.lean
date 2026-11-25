import NlsGge.Weights.PoissonBounds
import NlsGge.Weights.Regularity
/-! Source W02 concrete fourth-power sum bounds and exact weight/probability
identification. Actual series convergence and positive normalization precede identities. -/
set_option autoImplicit false
noncomputable section
namespace NlsGge.Weights

lemma poissonFourth_sum_bounds : ∃ L U : ℝ, 0 < L ∧ 0 < U ∧
    ∀ t : ℝ, 4 ≤ t →
      L*t^(-3/2 : ℝ) ≤ (∑' j : ℕ, (poissonTerm t j)^4) ∧
      (∑' j : ℕ, (poissonTerm t j)^4) ≤ U*t^(-3/2 : ℝ) := by
  obtain ⟨C, hC, hupper⟩ := poisson_uniform_upper
  obtain ⟨δ, hδ, hlower⟩ := poisson_uniform_central_lower
  refine ⟨δ^4, C^3, pow_pos hδ _, pow_pos hC _, ?_⟩
  intro t ht
  have ht0 : 0 < t := by linarith
  have hs := poissonTerm_fourth_summable t ht0.le
  have hD : 0 ≤ C*t^(-1/2 : ℝ) := mul_nonneg hC.le (Real.rpow_nonneg ht0.le _)
  have hδt : 0 ≤ δ*t^(-1/2 : ℝ) := mul_nonneg hδ.le (Real.rpow_nonneg ht0.le _)
  constructor
  · let s := Finset.Icc (Nat.ceil (t-Real.sqrt t)) (Nat.floor (t+Real.sqrt t))
    have hm (j : ℕ) (hj : j ∈ s) : |(j : ℝ)-t| ≤ Real.sqrt t := by
      have hj' := Finset.mem_Icc.mp hj
      have ha : (Nat.ceil (t-Real.sqrt t) : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj'.1
      have hb : (j : ℝ) ≤ (Nat.floor (t+Real.sqrt t) : ℝ) := by exact_mod_cast hj'.2
      have hcl := Nat.le_ceil (t-Real.sqrt t)
      have hfu := Nat.floor_le (by positivity : 0 ≤ t+Real.sqrt t)
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hcard : Real.sqrt t * (δ*t^(-1/2 : ℝ))^4 ≤ (s.card : ℝ)*(δ*t^(-1/2 : ℝ))^4 :=
      mul_le_mul_of_nonneg_right (poisson_central_window_count t ht) (pow_nonneg hδt _)
    have hfinite : (s.card : ℝ)*(δ*t^(-1/2 : ℝ))^4 ≤ ∑' j : ℕ, (poissonTerm t j)^4 := by
      calc
        (s.card : ℝ)*(δ*t^(-1/2 : ℝ))^4 = ∑ j ∈ s, (δ*t^(-1/2 : ℝ))^4 := by
          simp only [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ j ∈ s, (poissonTerm t j)^4 := Finset.sum_le_sum (fun j hj =>
          pow_le_pow_left₀ hδt (hlower t ht j (hm j hj)) 4)
        _ ≤ ∑' j : ℕ, (poissonTerm t j)^4 := hs.sum_le_tsum s
          (fun j hj => pow_nonneg (poissonTerm_nonneg t ht0.le j) _)
    have hp : Real.sqrt t * (δ*t^(-1/2 : ℝ))^4 = δ^4*t^(-3/2 : ℝ) := by
      calc
        Real.sqrt t * (δ*t^(-1/2 : ℝ))^4 =
          δ^4 * (t^(1/2 : ℝ) * (t^(-1/2 : ℝ))^4) := by rw [Real.sqrt_eq_rpow, mul_pow]; ring
        _ = δ^4*t^(-3/2 : ℝ) := by
          rw [← Real.rpow_mul_natCast ht0.le, ← Real.rpow_add ht0]
          norm_num
    rw [hp] at hcard
    exact hcard.trans hfinite
  · have hpoint (j : ℕ) : (poissonTerm t j)^4 ≤ (C*t^(-1/2 : ℝ))^3*poissonTerm t j := by
      calc
        (poissonTerm t j)^4 = (poissonTerm t j)^3*poissonTerm t j := pow_succ _ _
        _ ≤ (C*t^(-1/2 : ℝ))^3*poissonTerm t j := mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (poissonTerm_nonneg t ht0.le j) (hupper t (by linarith) j) 3)
          (poissonTerm_nonneg t ht0.le j)
    have htsum := hs.tsum_le_tsum hpoint
      ((poissonTerm_hasSum t ht0.le).summable.mul_left ((C*t^(-1/2 : ℝ))^3))
    rw [(poissonTerm_hasSum t ht0.le).summable.tsum_mul_left,
      (poissonTerm_hasSum t ht0.le).tsum_eq, mul_one] at htsum
    have hp : (C*t^(-1/2 : ℝ))^3 = C^3*t^(-3/2 : ℝ) := by
      rw [mul_pow, ← Real.rpow_mul_natCast ht0.le]
      norm_num
    simpa only [hp] using htsum

lemma weightedPoissonFourth_summable (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (t : ℝ) (ht : 0 ≤ t) :
    Summable (fun j : ℕ => c j*(poissonTerm t j)^4) := by
  apply ((poissonTerm_fourth_summable t ht).mul_left upper).of_nonneg_of_le
    (fun j => mul_nonneg (hlower.trans_le (hbound j)).le (pow_nonneg (poissonTerm_nonneg t ht j) _))
  intro j
  exact mul_le_mul_of_nonneg_right (hupper j) (pow_nonneg (poissonTerm_nonneg t ht j) _)

lemma weightedPoissonFourth_pos (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (t : ℝ) (ht : 0 ≤ t) :
    0 < (∑' j : ℕ, c j*(poissonTerm t j)^4) := by
  have hs := weightedPoissonFourth_summable lower upper c hlower hbound hupper t ht
  have hp : 0 < c 0*(poissonTerm t 0)^4 := by
    have hc : 0 < c 0 := hlower.trans_le (hbound 0)
    simp only [poissonTerm, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
    positivity
  exact hp.trans_le (hs.le_tsum 0 (fun j hj =>
    mul_nonneg (hlower.trans_le (hbound j)).le (pow_nonneg (poissonTerm_nonneg t ht j) _)))

lemma weightTerm_poissonFourth_identity (c : ℕ → ℝ) (t : ℝ) (ht : 0 ≤ t) (j : ℕ) :
    weightTerm c (t^2) j = Real.exp (4*t)*(c j*(poissonTerm t j)^4) := by
  have hsqrt : Real.sqrt |t^2| = t := by rw [abs_of_nonneg (sq_nonneg t), Real.sqrt_sq ht]
  have he : Real.exp (4*t)*(Real.exp (-t))^4 = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    norm_num only [Nat.cast_ofNat]
    rw [show 4*t+(4 : ℝ)*(-t) = 0 by ring, Real.exp_zero]
  rw [weightTerm_eq_fourth_power, hsqrt, poissonTerm]
  simp only [mul_div_assoc, mul_pow]
  calc
    c j*(t^j/(Nat.factorial j : ℝ))^4 = 1*(c j*(t^j/(Nat.factorial j : ℝ))^4) := by ring
    _ = (Real.exp (4*t)*(Real.exp (-t))^4)*(c j*(t^j/(Nat.factorial j : ℝ))^4) := by rw [he]
    _ = _ := by ring

lemma weight_poissonFourth_identity (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (t : ℝ) (ht : 0 ≤ t) :
    weight c (t^2) = Real.exp (4*t)*(∑' j : ℕ, c j*(poissonTerm t j)^4) := by
  have hs := (weightedPoissonFourth_summable lower upper c hlower hbound hupper t ht).hasSum.mul_left (Real.exp (4*t))
  have hw : HasSum (weightTerm c (t^2))
      (Real.exp (4*t)*(∑' j : ℕ, c j*(poissonTerm t j)^4)) :=
    hs.congr_fun (fun j => weightTerm_poissonFourth_identity c t ht j)
  exact hw.tsum_eq

lemma probabilityTerm_poissonFourth_identity (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (t : ℝ) (ht : 0 ≤ t) (j : ℕ) :
    probabilityTerm c (t^2) j =
      (c j*(poissonTerm t j)^4)/(∑' k : ℕ, c k*(poissonTerm t k)^4) := by
  have hd := (weightedPoissonFourth_pos lower upper c hlower hbound hupper t ht).ne'
  rw [probabilityTerm, weightTerm_poissonFourth_identity c t ht j,
    weight_poissonFourth_identity lower upper c hlower hbound hupper t ht]
  field_simp

end NlsGge.Weights
