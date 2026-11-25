                                                                                              
                                                                                                
                                                                                                     
                                                                                              
                                                                                                       
                                                                               
                                                                                               
                                                                                        
import Mathlib

set_option autoImplicit false
noncomputable section

namespace NlsGge.Atomic.I037

open Filter Topology

/-- `j`-th term `c_j r^(2j) / (j!)^p` with real exponent `p`. -/
def factorialPowerTerm (p : ℝ) (c : ℕ → ℝ) (r : ℝ) (j : ℕ) : ℝ :=
  c j * r ^ (2 * j) / ((Nat.factorial j : ℝ) ^ p)

/-- The weight `W(r) = sum_j c_j r^(2j)/(j!)^p`; totalized `tsum`, used only after summability. -/
def factorialPowerWeight (p : ℝ) (c : ℕ → ℝ) (r : ℝ) : ℝ :=
  ∑' j : ℕ, factorialPowerTerm p c r j

/-- The partial sum `W_m(r) = sum_{j <= m} c_j r^(2j)/(j!)^p`. -/
def factorialPowerPartial (p : ℝ) (c : ℕ → ℝ) (m : ℕ) (r : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), factorialPowerTerm p c r j

private lemma fact_one_le (j : ℕ) : (1 : ℝ) ≤ (Nat.factorial j : ℝ) := by
  exact_mod_cast Nat.factorial_pos j

private lemma fact_le_rpow {p : ℝ} (hp : 1 ≤ p) (j : ℕ) :
    (Nat.factorial j : ℝ) ≤ (Nat.factorial j : ℝ) ^ p :=
  Real.self_le_rpow_of_one_le (fact_one_le j) hp

private lemma fact_rpow_pos (p : ℝ) (j : ℕ) : 0 < (Nat.factorial j : ℝ) ^ p :=
  Real.rpow_pos_of_pos (by exact_mod_cast Nat.factorial_pos j) p

private lemma pow_two_mul_nonneg (r : ℝ) (j : ℕ) : 0 ≤ r ^ (2 * j) := by
  rw [pow_mul]; positivity

theorem term_nonneg {p : ℝ} {c : ℕ → ℝ} (hc : ∀ j, 1 ≤ c j ∧ c j ≤ 2) (r : ℝ) (j : ℕ) :
    0 ≤ factorialPowerTerm p c r j := by
  unfold factorialPowerTerm
  exact div_nonneg (mul_nonneg (by linarith [(hc j).1]) (pow_two_mul_nonneg r j))
    (fact_rpow_pos p j).le

theorem term_pos {p : ℝ} {c : ℕ → ℝ} (hc : ∀ j, 1 ≤ c j ∧ c j ≤ 2) {r : ℝ} (hr : 0 < r)
    (j : ℕ) : 0 < factorialPowerTerm p c r j := by
  unfold factorialPowerTerm
  exact div_pos (mul_pos (by linarith [(hc j).1]) (by positivity)) (fact_rpow_pos p j)

private lemma term_le {p : ℝ} (hp : 1 ≤ p) {c : ℕ → ℝ} (hc : ∀ j, 1 ≤ c j ∧ c j ≤ 2) (r : ℝ)
    (j : ℕ) : factorialPowerTerm p c r j ≤ 2 * ((r ^ 2) ^ j / (Nat.factorial j : ℝ)) := by
  unfold factorialPowerTerm
  have hx : 0 ≤ (r ^ 2) ^ j := by positivity
  have hF : (0 : ℝ) < (Nat.factorial j : ℝ) := by exact_mod_cast Nat.factorial_pos j
  rw [← pow_mul]
  calc c j * r ^ (2 * j) / (Nat.factorial j : ℝ) ^ p
      ≤ 2 * r ^ (2 * j) / (Nat.factorial j : ℝ) ^ p := by
        apply div_le_div_of_nonneg_right _ (fact_rpow_pos p j).le
        exact mul_le_mul_of_nonneg_right (hc j).2 (pow_two_mul_nonneg r j)
    _ ≤ 2 * r ^ (2 * j) / (Nat.factorial j : ℝ) := by
        apply div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (pow_two_mul_nonneg r j)) hF (fact_le_rpow hp j)
    _ = 2 * (r ^ (2 * j) / (Nat.factorial j : ℝ)) := by ring

/-- The series is summable for every real `r` (it is entire). -/
theorem summable_term {p : ℝ} (hp : 1 ≤ p) {c : ℕ → ℝ} (hc : ∀ j, 1 ≤ c j ∧ c j ≤ 2) (r : ℝ) :
    Summable (factorialPowerTerm p c r) := by
  refine Summable.of_nonneg_of_le (term_nonneg hc r) (fun j => ?_)
    ((Real.summable_pow_div_factorial (r ^ 2)).mul_left 2)
  exact term_le hp hc r j

theorem weight_pos {p : ℝ} (hp : 1 ≤ p) {c : ℕ → ℝ} (hc : ∀ j, 1 ≤ c j ∧ c j ≤ 2) {r : ℝ}
    (hr : 0 < r) : 0 < factorialPowerWeight p c r :=
  Summable.tsum_pos (summable_term hp hc r) (term_nonneg hc r) 0 (term_pos hc hr 0)

theorem partial_pos {p : ℝ} {c : ℕ → ℝ} (hc : ∀ j, 1 ≤ c j ∧ c j ≤ 2) {r : ℝ} (hr : 0 < r)
    (m : ℕ) : 0 < factorialPowerPartial p c m r :=
  Finset.sum_pos (fun j _ => term_pos hc hr j) ⟨0, by simp⟩

/-- Derivative of one term (all real `y`). -/
private lemma hasDerivAt_term (p : ℝ) (c : ℕ → ℝ) (n : ℕ) (y : ℝ) :
    HasDerivAt (fun y => factorialPowerTerm p c y n)
      (c n * (((2 * n : ℕ) : ℝ) * y ^ (2 * n - 1)) / ((Nat.factorial n : ℝ) ^ p)) y := by
  unfold factorialPowerTerm
  exact ((hasDerivAt_pow (2 * n) y).const_mul (c n)).div_const _

private lemma mul_deriv_term (p : ℝ) (c : ℕ → ℝ) (n : ℕ) (y : ℝ) :
    y * (c n * (((2 * n : ℕ) : ℝ) * y ^ (2 * n - 1)) / ((Nat.factorial n : ℝ) ^ p)) =
      2 * ((n : ℝ) * factorialPowerTerm p c y n) := by
  unfold factorialPowerTerm
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · obtain ⟨m, hm⟩ : ∃ m, 2 * n = m + 1 := ⟨2 * n - 1, by omega⟩
    have hm' : 2 * n - 1 = m := by omega
    rw [hm', hm, pow_succ]
    push_cast
    have h2 : (2 : ℝ) * n = m + 1 := by exact_mod_cast hm
    rw [← h2]
    ring

private lemma summable_deriv_bound (R : ℝ) :
    Summable (fun n : ℕ => 4 * ((n : ℝ) * R ^ (2 * n - 1) / (Nat.factorial n : ℝ))) := by
  refine Summable.mul_left 4 ?_
  rw [← summable_nat_add_iff 1]
  have key : ∀ k : ℕ, (((k + 1 : ℕ) : ℝ) * R ^ (2 * (k + 1) - 1) / (Nat.factorial (k + 1) : ℝ)) =
      R * ((R ^ 2) ^ k / (Nat.factorial k : ℝ)) := by
    intro k
    have h1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    have hk : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
    rw [h1, Nat.factorial_succ, pow_succ, pow_mul]
    push_cast
    field_simp
  simp only [key]
  exact (Real.summable_pow_div_factorial (R ^ 2)).mul_left R

/-- The weight is differentiable with the termwise derivative, at every real point. -/
theorem hasDerivAt_weight {p : ℝ} (hp : 1 ≤ p) {c : ℕ → ℝ} (hc : ∀ j, 1 ≤ c j ∧ c j ≤ 2)
    (r : ℝ) :
    HasDerivAt (factorialPowerWeight p c)
      (∑' n : ℕ, c n * (((2 * n : ℕ) : ℝ) * r ^ (2 * n - 1)) / ((Nat.factorial n : ℝ) ^ p)) r := by
  set R : ℝ := |r| + 1 with hR
  have hR0 : 0 < R := by positivity
  have hmem : r ∈ Metric.ball (0 : ℝ) R := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]; linarith [abs_nonneg r]
  have h0 : (0 : ℝ) ∈ Metric.ball (0 : ℝ) R := Metric.mem_ball_self hR0
  have := hasDerivAt_tsum_of_isPreconnected (summable_deriv_bound R) Metric.isOpen_ball
    (convex_ball (0 : ℝ) R).isPreconnected
    (fun n y _ => hasDerivAt_term p c n y) ?_ h0 (summable_term hp hc 0) hmem
  · exact this
  · intro n y hy
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hy
    have hF : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have hFp := fact_rpow_pos p n
    have hy0 : 0 ≤ |y| := abs_nonneg y
    have hpow : |y| ^ (2 * n - 1) ≤ R ^ (2 * n - 1) := pow_le_pow_left₀ hy0 hy.le _
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_of_pos hFp, abs_pow,
      Nat.abs_cast, abs_of_nonneg (by linarith [(hc n).1] : 0 ≤ c n)]
    have hcn : c n ≤ 2 := (hc n).2
    have hn0 : (0 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := Nat.cast_nonneg _
    calc c n * (((2 * n : ℕ) : ℝ) * |y| ^ (2 * n - 1)) / (Nat.factorial n : ℝ) ^ p
        ≤ 2 * (((2 * n : ℕ) : ℝ) * R ^ (2 * n - 1)) / (Nat.factorial n : ℝ) ^ p := by
          apply div_le_div_of_nonneg_right _ hFp.le
          apply mul_le_mul hcn (mul_le_mul_of_nonneg_left hpow hn0) (by positivity) (by norm_num)
      _ ≤ 2 * (((2 * n : ℕ) : ℝ) * R ^ (2 * n - 1)) / (Nat.factorial n : ℝ) := by
          apply div_le_div_of_nonneg_left (by positivity) hF (fact_le_rpow hp n)
      _ = 4 * ((n : ℝ) * R ^ (2 * n - 1) / (Nat.factorial n : ℝ)) := by
          push_cast; ring

/-- Core Hölder lemma over `ℕ`: a nonnegative summable weight `s` with the shifted moment bound
`(k+1)^p s_{k+1} ≤ M s_k` has first moment `∑ j s_j ≤ M^(1/p) ∑ s_j`. -/
theorem core_moment (p : ℝ) (hp : 1 < p) (s : ℕ → ℝ) (hs0 : ∀ j, 0 ≤ s j) (hs : Summable s)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ k : ℕ, ((k + 1 : ℕ) : ℝ) ^ p * s (k + 1) ≤ M * s k) :
    Summable (fun j : ℕ => (j : ℝ) * s j) ∧
      ∑' j : ℕ, (j : ℝ) * s j ≤ M ^ (1 / p) * ∑' j : ℕ, s j := by
  have hp0 : 0 < p := by linarith
  -- moment summability
  have hmom_shift : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ p * s (k + 1)) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (by positivity) (hs0 _)) hM (hs.mul_left M)
  have hmom : Summable (fun j : ℕ => (j : ℝ) ^ p * s j) := by
    rw [← summable_nat_add_iff 1]
    exact hmom_shift
  have hmom_le : ∑' j : ℕ, (j : ℝ) ^ p * s j ≤ M * ∑' j : ℕ, s j := by
    have h0 : ((0 : ℕ) : ℝ) ^ p * s 0 = 0 := by
      simp [Real.zero_rpow hp0.ne']
    rw [hmom.tsum_eq_zero_add, h0, zero_add]
    calc ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ p * s (k + 1)
        ≤ ∑' k : ℕ, M * s k := Summable.tsum_le_tsum hM hmom_shift (hs.mul_left M)
      _ = M * ∑' k : ℕ, s k := tsum_mul_left
  -- Hölder with exponents p and q
  set q : ℝ := Real.conjExponent p with hq
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hsum1 : 1 / p + 1 / q = 1 := by
    have := hpq.inv_add_inv_eq_one
    simpa [one_div] using this
  have hf0 : ∀ j : ℕ, 0 ≤ (j : ℝ) * s j ^ (1 / p) := fun j =>
    mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (hs0 j) _)
  have hg0 : ∀ j : ℕ, 0 ≤ s j ^ (1 / q) := fun j => Real.rpow_nonneg (hs0 j) _
  have hfp : ∀ j : ℕ, ((j : ℝ) * s j ^ (1 / p)) ^ p = (j : ℝ) ^ p * s j := by
    intro j
    rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg (hs0 j) _), ← Real.rpow_mul (hs0 j),
      one_div_mul_cancel hp0.ne', Real.rpow_one]
  have hgq : ∀ j : ℕ, (s j ^ (1 / q)) ^ q = s j := by
    intro j
    rw [← Real.rpow_mul (hs0 j), one_div_mul_cancel hpq.symm.pos.ne', Real.rpow_one]
  have hfg : ∀ j : ℕ, ((j : ℝ) * s j ^ (1 / p)) * s j ^ (1 / q) = (j : ℝ) * s j := by
    intro j
    rw [mul_assoc, ← Real.rpow_add' (hs0 j) (by rw [hsum1]; norm_num), hsum1, Real.rpow_one]
  have hfs : Summable (fun j : ℕ => ((j : ℝ) * s j ^ (1 / p)) ^ p) := by
    simpa only [hfp] using hmom
  have hgs : Summable (fun j : ℕ => (s j ^ (1 / q)) ^ q) := by
    simpa only [hgq] using hs
  obtain ⟨hsumfg, hH⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hpq hf0 hg0 hfs hgs
  have e1 : (fun j : ℕ => ((j : ℝ) * s j ^ (1 / p)) * s j ^ (1 / q)) = fun j : ℕ => (j : ℝ) * s j :=
    funext hfg
  rw [e1] at hsumfg hH
  refine ⟨hsumfg, ?_⟩
  refine hH.trans ?_
  have e2 : (∑' j : ℕ, ((j : ℝ) * s j ^ (1 / p)) ^ p) = ∑' j : ℕ, (j : ℝ) ^ p * s j :=
    tsum_congr hfp
  have e3 : (∑' j : ℕ, (s j ^ (1 / q)) ^ q) = ∑' j : ℕ, s j := tsum_congr hgq
  rw [e2, e3]
  have hS0 : 0 ≤ ∑' j : ℕ, s j := tsum_nonneg hs0
  calc (∑' j : ℕ, (j : ℝ) ^ p * s j) ^ (1 / p) * (∑' j : ℕ, s j) ^ (1 / q)
      ≤ (M * ∑' j : ℕ, s j) ^ (1 / p) * (∑' j : ℕ, s j) ^ (1 / q) := by
        gcongr
        · exact tsum_nonneg (fun j => mul_nonneg (by positivity) (hs0 j))
    _ = M ^ (1 / p) * ∑' j : ℕ, s j := by
        rw [Real.mul_rpow hM0 hS0, mul_assoc,
          ← Real.rpow_add' hS0 (by rw [hsum1]; norm_num), hsum1, Real.rpow_one]


/-! ### Assembly of (A) -/

/-- Shifted moment bound for the terms. -/
private lemma term_moment {p : ℝ} (_hp : 1 < p) {c : ℕ → ℝ} (hc : ∀ j, 1 ≤ c j ∧ c j ≤ 2)
    (r : ℝ) (k : ℕ) :
    ((k + 1 : ℕ) : ℝ) ^ p * factorialPowerTerm p c r (k + 1) ≤
      2 * r ^ 2 * factorialPowerTerm p c r k := by
  unfold factorialPowerTerm
  have hF : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hFp := fact_rpow_pos p k
  have ha : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) ^ p := Real.rpow_pos_of_pos (by positivity) p
  have hfs : ((Nat.factorial (k + 1) : ℕ) : ℝ) ^ p = ((k + 1 : ℕ) : ℝ) ^ p * (Nat.factorial k : ℝ) ^ p := by
    rw [Nat.factorial_succ, Nat.cast_mul, Real.mul_rpow (by positivity) hF.le]
  rw [hfs]
  have hr2 : 0 ≤ r ^ (2 * k) := pow_two_mul_nonneg r k
  have e1 : ((k + 1 : ℕ) : ℝ) ^ p * (c (k + 1) * r ^ (2 * (k + 1)) /
      (((k + 1 : ℕ) : ℝ) ^ p * (Nat.factorial k : ℝ) ^ p)) =
      c (k + 1) * (r ^ 2 * r ^ (2 * k)) / (Nat.factorial k : ℝ) ^ p := by
    have : r ^ (2 * (k + 1)) = r ^ 2 * r ^ (2 * k) := by
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]; ring
    rw [this]
    field_simp
  rw [e1]
  have hc1 := (hc k).1
  have hc2 := (hc (k + 1)).2
  have hr : 0 ≤ r ^ 2 * r ^ (2 * k) := by positivity
  calc c (k + 1) * (r ^ 2 * r ^ (2 * k)) / (Nat.factorial k : ℝ) ^ p
      ≤ (2 * c k) * (r ^ 2 * r ^ (2 * k)) / (Nat.factorial k : ℝ) ^ p := by
        apply div_le_div_of_nonneg_right _ hFp.le
        exact mul_le_mul_of_nonneg_right (by linarith) hr
    _ = 2 * r ^ 2 * (c k * r ^ (2 * k) / (Nat.factorial k : ℝ) ^ p) := by ring

/-- Log-derivative bookkeeping: from `r D = 2 B`, `B ≤ (2 r²)^(1/p) A`. -/
private lemma logderiv_bound {p : ℝ} {r A B D : ℝ} (hr : 0 < r) (hA : 0 < A)
    (hD : r * D = 2 * B) (hB0 : 0 ≤ B) (hB : B ≤ (2 * r ^ 2) ^ (1 / p) * A) :
    0 ≤ D / A ∧ D / A ≤ 2 * (2 : ℝ) ^ (1 / p) * r ^ (2 / p - 1) := by
  have hD' : D = 2 * B / r := by field_simp; linarith
  have hr2 : (0 : ℝ) ≤ r ^ 2 := by positivity
  have hpow : (2 * r ^ 2) ^ (1 / p) = (2 : ℝ) ^ (1 / p) * r ^ (2 / p) := by
    rw [Real.mul_rpow (by norm_num) hr2]
    congr 1
    rw [show (r ^ 2 : ℝ) = r ^ (2 : ℝ) by rw [Real.rpow_two], ← Real.rpow_mul hr.le]
    congr 1; ring
  refine ⟨?_, ?_⟩
  · rw [hD']; positivity
  · rw [hD', Real.rpow_sub_one hr.ne', div_div, div_le_iff₀ (mul_pos hr hA)]
    calc 2 * B ≤ 2 * ((2 * r ^ 2) ^ (1 / p) * A) := by linarith
      _ = 2 * (2 : ℝ) ^ (1 / p) * (r ^ (2 / p) / r) * (r * A) := by
          rw [hpow]; field_simp

theorem weight_logderiv_full {p : ℝ} (hp : 1 < p) {c : ℕ → ℝ} (hc : ∀ j, 1 ≤ c j ∧ c j ≤ 2)
    {r : ℝ} (hr : 0 < r) :
    0 < factorialPowerWeight p c r ∧ DifferentiableAt ℝ (factorialPowerWeight p c) r ∧
      0 ≤ deriv (factorialPowerWeight p c) r / factorialPowerWeight p c r ∧
      deriv (factorialPowerWeight p c) r / factorialPowerWeight p c r ≤
        2 * (2 : ℝ) ^ (1 / p) * r ^ (2 / p - 1) := by
  have hp1 : 1 ≤ p := hp.le
  have hA := weight_pos hp1 hc hr
  have hder := hasDerivAt_weight hp1 hc r
  obtain ⟨_, hB⟩ := core_moment p hp (factorialPowerTerm p c r) (term_nonneg hc r)
    (summable_term hp1 hc r) (2 * r ^ 2) (by positivity) (term_moment hp hc r)
  have hD : r * (∑' n : ℕ, c n * (((2 * n : ℕ) : ℝ) * r ^ (2 * n - 1)) /
        ((Nat.factorial n : ℝ) ^ p)) =
      2 * ∑' j : ℕ, (j : ℝ) * factorialPowerTerm p c r j := by
    rw [← tsum_mul_left, tsum_congr (fun n => mul_deriv_term p c n r), tsum_mul_left]
  have hB0 : 0 ≤ ∑' j : ℕ, (j : ℝ) * factorialPowerTerm p c r j :=
    tsum_nonneg (fun j => mul_nonneg (Nat.cast_nonneg _) (term_nonneg hc r j))
  refine ⟨hA, hder.differentiableAt, ?_⟩
  rw [hder.deriv]
  exact logderiv_bound hr hA hD hB0 hB

theorem weight_logderiv_partial {p : ℝ} (hp : 1 < p) {c : ℕ → ℝ} (hc : ∀ j, 1 ≤ c j ∧ c j ≤ 2)
    {r : ℝ} (hr : 0 < r) (m : ℕ) :
    0 < factorialPowerPartial p c m r ∧ DifferentiableAt ℝ (factorialPowerPartial p c m) r ∧
      0 ≤ deriv (factorialPowerPartial p c m) r / factorialPowerPartial p c m r ∧
      deriv (factorialPowerPartial p c m) r / factorialPowerPartial p c m r ≤
        2 * (2 : ℝ) ^ (1 / p) * r ^ (2 / p - 1) := by
  obtain ⟨s, hs⟩ : ∃ s : ℕ → ℝ, s = fun j => if j ≤ m then factorialPowerTerm p c r j else 0 :=
    ⟨_, rfl⟩
  have hs0 : ∀ j, 0 ≤ s j := by
    intro j; rw [hs]; dsimp only; split_ifs
    · exact term_nonneg hc r j
    · exact le_rfl
  have hsfin : ∀ j ∉ Finset.range (m + 1), s j = 0 := by
    intro j hj
    have : ¬ j ≤ m := by simpa [Finset.mem_range, Nat.lt_succ_iff] using hj
    rw [hs]; dsimp only; rw [if_neg this]
  have hssum : Summable s := summable_of_ne_finset_zero hsfin
  have hM : ∀ k : ℕ, ((k + 1 : ℕ) : ℝ) ^ p * s (k + 1) ≤ (2 * r ^ 2) * s k := by
    intro k
    by_cases h : k + 1 ≤ m
    · have hk : k ≤ m := by omega
      have e1 : s (k + 1) = factorialPowerTerm p c r (k + 1) := by
        rw [hs]; dsimp only; rw [if_pos h]
      have e2 : s k = factorialPowerTerm p c r k := by
        rw [hs]; dsimp only; rw [if_pos hk]
      rw [e1, e2]
      exact term_moment hp hc r k
    · have e1 : s (k + 1) = 0 := by rw [hs]; dsimp only; rw [if_neg h]
      rw [e1, mul_zero]
      exact mul_nonneg (by positivity) (hs0 k)
  obtain ⟨_, hB⟩ := core_moment p hp s hs0 hssum (2 * r ^ 2) (by positivity) hM
  have hAeq : ∑' j : ℕ, s j = factorialPowerPartial p c m r := by
    rw [tsum_eq_sum hsfin]
    unfold factorialPowerPartial
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    rw [hs]; dsimp only; rw [if_pos this]
  have hBeq : ∑' j : ℕ, (j : ℝ) * s j =
      ∑ j ∈ Finset.range (m + 1), (j : ℝ) * factorialPowerTerm p c r j := by
    rw [tsum_eq_sum (s := Finset.range (m + 1)) (fun j hj => by rw [hsfin j hj, mul_zero])]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    rw [hs]; dsimp only; rw [if_pos this]
  rw [hAeq, hBeq] at hB
  have hder : HasDerivAt (factorialPowerPartial p c m)
      (∑ n ∈ Finset.range (m + 1), c n * (((2 * n : ℕ) : ℝ) * r ^ (2 * n - 1)) /
        ((Nat.factorial n : ℝ) ^ p)) r :=
    HasDerivAt.fun_sum (fun j _ => hasDerivAt_term p c j r)
  have hD : r * (∑ n ∈ Finset.range (m + 1), c n * (((2 * n : ℕ) : ℝ) * r ^ (2 * n - 1)) /
        ((Nat.factorial n : ℝ) ^ p)) =
      2 * ∑ j ∈ Finset.range (m + 1), (j : ℝ) * factorialPowerTerm p c r j := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun n _ => mul_deriv_term p c n r)
  have hB0 : 0 ≤ ∑ j ∈ Finset.range (m + 1), (j : ℝ) * factorialPowerTerm p c r j :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (Nat.cast_nonneg _) (term_nonneg hc r j))
  have hA := partial_pos (p := p) hc hr m
  refine ⟨hA, hder.differentiableAt, ?_⟩
  rw [hder.deriv]
  exact logderiv_bound hr hA hD hB0 hB

/-- Part (A) of COMMAND03. -/
theorem factorialPower_logDerivative_majorant :
    (∀ (p : ℝ), 2 < p → ∀ (c : ℕ → ℝ), (∀ j, 1 ≤ c j ∧ c j ≤ 2) →
    (∀ r' : ℝ, Summable (factorialPowerTerm p c r')) ∧
    ∀ r : ℝ, 0 < r →
      (0 < factorialPowerWeight p c r ∧
        DifferentiableAt ℝ (factorialPowerWeight p c) r ∧
        0 ≤ deriv (factorialPowerWeight p c) r / factorialPowerWeight p c r ∧
        deriv (factorialPowerWeight p c) r / factorialPowerWeight p c r ≤
          2 * (2 : ℝ) ^ (1 / p) * r ^ (2 / p - 1)) ∧
      ∀ m : ℕ,
        (0 < factorialPowerPartial p c m r ∧
          DifferentiableAt ℝ (factorialPowerPartial p c m) r ∧
          0 ≤ deriv (factorialPowerPartial p c m) r / factorialPowerPartial p c m r ∧
          deriv (factorialPowerPartial p c m) r / factorialPowerPartial p c m r ≤
            2 * (2 : ℝ) ^ (1 / p) * r ^ (2 / p - 1))) := by
  intro p hp c hc
  have hp1 : 1 < p := by linarith
  exact ⟨fun r' => summable_term hp1.le hc r',
    fun r hr => ⟨weight_logderiv_full hp1 hc hr, fun m => weight_logderiv_partial hp1 hc hr m⟩⟩

/-- The Japanese bracket `<n> = (1 + n^2)^(1/2)`. -/
def bracket (n : ℤ) : ℝ := Real.sqrt (1 + (n : ℝ) ^ 2)

private lemma abs_le_bracket (n : ℤ) : |(n : ℝ)| ≤ bracket n := by
  unfold bracket
  exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (n : ℝ)])

private lemma one_le_bracket (n : ℤ) : 1 ≤ bracket n := by
  unfold bracket
  exact Real.one_le_sqrt.2 (by nlinarith [sq_nonneg (n : ℝ)])

private lemma bracket_pos (n : ℤ) : 0 < bracket n := lt_of_lt_of_le one_pos (one_le_bracket n)

/-- Part (B) of COMMAND03: the high-gap loss is summable exactly because `p > 2`. -/
theorem summable_bracket_rpow : (∀ p : ℝ, 2 < p → Summable (fun n : ℤ => bracket n ^ (2 / p - 2))) := by
  intro p hp
  have hp0 : 0 < p := by linarith
  have hb : 1 < 2 - 2 / p := by
    have : 2 / p < 1 := by rw [div_lt_one hp0]; exact hp
    linarith
  have hg := Real.summable_abs_int_rpow hb
  refine Summable.of_norm_bounded_eventually hg ?_
  rw [Filter.eventually_cofinite]
  refine Set.Finite.subset (Set.finite_singleton (0 : ℤ)) ?_
  intro n hn
  by_contra hne
  have hne' : n ≠ 0 := hne
  apply hn
  have hn1 : (0 : ℝ) < |(n : ℝ)| := by
    rw [abs_pos]; exact_mod_cast hne'
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (bracket_pos n) _)]
  have : 2 / p - 2 = -(2 - 2 / p) := by ring
  rw [this]
  exact Real.rpow_le_rpow_of_nonpos hn1 (abs_le_bracket n) (by linarith)

/-! ### Ingredients for (C) -/

theorem weight_even (p : ℝ) (c : ℕ → ℝ) (r : ℝ) :
    factorialPowerWeight p c (-r) = factorialPowerWeight p c r := by
  unfold factorialPowerWeight
  refine tsum_congr (fun j => ?_)
  unfold factorialPowerTerm
  rw [Even.neg_pow (by simp)]

theorem weight_ge_one {p : ℝ} (hp : 1 ≤ p) {c : ℕ → ℝ} (hc : ∀ j, 1 ≤ c j ∧ c j ≤ 2) (r : ℝ) :
    1 ≤ factorialPowerWeight p c r := by
  have h0 : factorialPowerTerm p c r 0 = c 0 := by
    unfold factorialPowerTerm; simp
  have := Summable.le_tsum (summable_term hp hc r) 0 (fun j _ => term_nonneg hc r j)
  rw [h0] at this
  exact le_trans (hc 0).1 this

/-- Crude growth bound, used only for finitely many indices. -/
theorem weight_le {p : ℝ} (hp : 1 ≤ p) {c : ℕ → ℝ} (hc : ∀ j, 1 ≤ c j ∧ c j ≤ 2) {r R : ℝ}
    (hr : |r| ≤ R) :
    factorialPowerWeight p c r ≤ ∑' j : ℕ, 2 * ((R ^ 2) ^ j / (Nat.factorial j : ℝ)) := by
  unfold factorialPowerWeight
  refine Summable.tsum_le_tsum (fun j => ?_) (summable_term hp hc r)
    ((Real.summable_pow_div_factorial (R ^ 2)).mul_left 2)
  refine (term_le hp hc r j).trans ?_
  have hF : (0 : ℝ) < (Nat.factorial j : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hr2 : r ^ 2 ≤ R ^ 2 := by
    have := sq_le_sq' (by linarith [abs_nonneg r, neg_abs_le r]) (le_trans (le_abs_self r) hr)
    exact this
  have : (r ^ 2) ^ j ≤ (R ^ 2) ^ j := pow_le_pow_left₀ (sq_nonneg r) hr2 j
  gcongr

theorem weight_monotone {p : ℝ} (hp : 1 < p) {c : ℕ → ℝ} (hc : ∀ j, 1 ≤ c j ∧ c j ≤ 2) {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    factorialPowerWeight p c x ≤ factorialPowerWeight p c y := by
  have hdiffAt : ∀ t, HasDerivAt (factorialPowerWeight p c) (deriv (factorialPowerWeight p c) t) t :=
    fun t => (hasDerivAt_weight hp.le hc t).differentiableAt.hasDerivAt
  have hmono : MonotoneOn (factorialPowerWeight p c) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun t _ => (hdiffAt t).continuousAt.continuousWithinAt)
      (fun t _ => (hdiffAt t).differentiableAt.differentiableWithinAt) ?_
    intro t ht
    rw [interior_Ici] at ht
    have ht' : 0 < t := ht
    obtain ⟨hA, _, h0, _⟩ := weight_logderiv_full hp hc ht'
    exact (div_nonneg_iff.1 h0).elim (fun h => h.1) (fun h => absurd h.2 (not_le.2 hA))
  exact hmono hx (le_trans hx hxy) hxy

/-- Gronwall-type growth: `W y ≤ W x exp (L x^(2/p-1) (y-x))` for `0 < x ≤ y`. -/
theorem weight_growth {p : ℝ} (hp2 : 2 ≤ p) {c : ℕ → ℝ} (hc : ∀ j, 1 ≤ c j ∧ c j ≤ 2) {x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) :
    factorialPowerWeight p c y ≤ factorialPowerWeight p c x *
      Real.exp (2 * (2 : ℝ) ^ (1 / p) * x ^ (2 / p - 1) * (y - x)) := by
  have hp : 1 < p := by linarith
  have hdiffAt : ∀ t, HasDerivAt (factorialPowerWeight p c) (deriv (factorialPowerWeight p c) t) t :=
    fun t => (hasDerivAt_weight hp.le hc t).differentiableAt.hasDerivAt
  have hlogd : ∀ t, 0 < t → HasDerivAt (fun u => Real.log (factorialPowerWeight p c u))
      (deriv (factorialPowerWeight p c) t / factorialPowerWeight p c t) t :=
    fun t ht => (hdiffAt t).log (weight_pos hp.le hc ht).ne'
  have hs' : 2 / p - 1 ≤ 0 := by
    have : 2 / p ≤ 1 := by rw [div_le_one (by linarith)]; exact hp2
    linarith
  have key := (convex_Icc x y).image_sub_le_mul_sub_of_deriv_le
    (f := fun u => Real.log (factorialPowerWeight p c u))
    (C := 2 * (2 : ℝ) ^ (1 / p) * x ^ (2 / p - 1))
    (fun t ht => (hlogd t (lt_of_lt_of_le hx ht.1)).continuousAt.continuousWithinAt)
    (fun t ht => by
      rw [interior_Icc] at ht
      exact (hlogd t (lt_trans hx ht.1)).differentiableAt.differentiableWithinAt)
    (fun t ht => by
      rw [interior_Icc] at ht
      have ht0 : 0 < t := lt_trans hx ht.1
      rw [(hlogd t ht0).deriv]
      refine (weight_logderiv_full hp hc ht0).2.2.2.trans ?_
      have h2 : (0 : ℝ) ≤ 2 * (2 : ℝ) ^ (1 / p) := by positivity
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hx ht.1.le hs') h2)
    x (Set.left_mem_Icc.2 hxy) y (Set.right_mem_Icc.2 hxy) hxy
  have hWx := weight_pos hp.le hc hx
  have hWy := weight_pos hp.le hc (lt_of_lt_of_le hx hxy)
  calc factorialPowerWeight p c y
      = Real.exp (Real.log (factorialPowerWeight p c y)) := (Real.exp_log hWy).symm
    _ ≤ Real.exp (Real.log (factorialPowerWeight p c x) +
          2 * (2 : ℝ) ^ (1 / p) * x ^ (2 / p - 1) * (y - x)) := by
        apply Real.exp_le_exp.2; linarith
    _ = factorialPowerWeight p c x *
          Real.exp (2 * (2 : ℝ) ^ (1 / p) * x ^ (2 / p - 1) * (y - x)) := by
        rw [Real.exp_add, Real.exp_log hWx]

theorem weight_abs (p : ℝ) (c : ℕ → ℝ) (t : ℝ) :
    factorialPowerWeight p c |t| = factorialPowerWeight p c t := by
  rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
  · rw [h, weight_even]

private lemma exp_sub_one_le {ε : ℝ} (hε : 0 ≤ ε) : Real.exp ε - 1 ≤ ε * Real.exp ε := by
  have h1 := Real.add_one_le_exp (-ε)
  have h2 : Real.exp (-ε) * Real.exp ε = 1 := by rw [← Real.exp_add]; simp
  have h3 : 0 < Real.exp ε := Real.exp_pos ε
  nlinarith [mul_le_mul_of_nonneg_right h1 h3.le]

private lemma bracket_le_two_mul_abs (n : ℤ) (hn : 1 ≤ |(n : ℝ)|) : bracket n ≤ 2 * |(n : ℝ)| := by
  unfold bracket
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have : (n : ℝ) ^ 2 = |(n : ℝ)| ^ 2 := (sq_abs _).symm
  nlinarith [sq_nonneg (|(n : ℝ)|)]

/-- Large indices: the gap estimate with an explicit constant. -/
theorem gap_large {p : ℝ} (hp : 2 < p) {c : ℕ → ℝ} (hc : ∀ j, 1 ≤ c j ∧ c j ≤ 2) {K : ℝ}
    (hK : 0 < K) {n : ℤ} (hn : 2 * K ≤ Real.pi * |(n : ℝ)|) (hn1 : 1 ≤ |(n : ℝ)|) {lam : ℝ}
    (hl : |lam - Real.pi * n| ≤ K / bracket n) :
    |factorialPowerWeight p c (2 * lam) - factorialPowerWeight p c (2 * Real.pi * n)| ≤
      (2 * K * (2 * (2 : ℝ) ^ (1 / p)) * Real.exp (2 * K * (2 * (2 : ℝ) ^ (1 / p)))) *
        factorialPowerWeight p c (2 * Real.pi * n) * bracket n ^ (2 / p - 2) := by
  have hp1 : 1 < p := by linarith
  have hp0 : 0 < p := by linarith
  set L : ℝ := 2 * (2 : ℝ) ^ (1 / p) with hL
  have hL0 : 0 ≤ L := by positivity
  have hs' : 2 / p - 1 ≤ 0 := by
    have : 2 / p ≤ 1 := by rw [div_le_one hp0]; exact hp.le
    linarith
  have hs : 2 / p - 2 ≤ 0 := by linarith
  have hB1 := one_le_bracket n
  have hBpos := bracket_pos n
  set r1 : ℝ := |2 * Real.pi * n| with hr1
  set r2 : ℝ := |2 * lam| with hr2
  have hr1e : r1 = 2 * (Real.pi * |(n : ℝ)|) := by
    rw [hr1, abs_mul, abs_mul, abs_of_pos Real.pi_pos]; norm_num; ring
  have hpin : 1 ≤ Real.pi * |(n : ℝ)| := by
    have := Real.pi_gt_three
    nlinarith [abs_nonneg (n : ℝ)]
  have hr1pos : 0 < r1 := by rw [hr1e]; linarith
  set δ : ℝ := 2 * K / bracket n with hδ
  have hδK : δ ≤ 2 * K := by
    rw [hδ, div_le_iff₀ hBpos]; nlinarith
  have hδ_le : δ ≤ Real.pi * |(n : ℝ)| := hδK.trans hn
  have hdiff : |r2 - r1| ≤ δ := by
    calc |r2 - r1| ≤ |2 * lam - 2 * Real.pi * n| := abs_abs_sub_abs_le_abs_sub _ _
      _ = 2 * |lam - Real.pi * n| := by
          rw [show 2 * lam - 2 * Real.pi * n = 2 * (lam - Real.pi * n) by ring, abs_mul]; norm_num
      _ ≤ 2 * (K / bracket n) := by linarith
      _ = δ := by rw [hδ]; ring
  have hWa : factorialPowerWeight p c (2 * Real.pi * n) = factorialPowerWeight p c r1 :=
    (weight_abs p c _).symm
  have hWb : factorialPowerWeight p c (2 * lam) = factorialPowerWeight p c r2 :=
    (weight_abs p c _).symm
  rw [hWa, hWb]
  -- bound for the exponent
  have hε_bound : ∀ x y : ℝ, r1 / 2 ≤ x → x ≤ y → y - x ≤ δ →
      L * x ^ (2 / p - 1) * (y - x) ≤ 2 * K * L * bracket n ^ (2 / p - 2) := by
    intro x y hx hxy hyx
    have hxpos : 0 < x := lt_of_lt_of_le (by linarith) hx
    have hxn : bracket n ≤ x := by
      have h1 := bracket_le_two_mul_abs n hn1
      have h2 : r1 / 2 = Real.pi * |(n : ℝ)| := by rw [hr1e]; ring
      have h3 : 2 * |(n : ℝ)| ≤ Real.pi * |(n : ℝ)| := by
        nlinarith [Real.pi_gt_three, abs_nonneg (n : ℝ)]
      linarith
    have h4 : x ^ (2 / p - 1) ≤ bracket n ^ (2 / p - 1) :=
      Real.rpow_le_rpow_of_nonpos hBpos hxn hs'
    have h5 : bracket n ^ (2 / p - 1 - 1) = bracket n ^ (2 / p - 1) / bracket n :=
      Real.rpow_sub_one hBpos.ne' _
    have h6 : (2 / p - 1 - 1) = 2 / p - 2 := by ring
    rw [h6] at h5
    have hxpow : 0 ≤ x ^ (2 / p - 1) := Real.rpow_nonneg hxpos.le _
    calc L * x ^ (2 / p - 1) * (y - x) ≤ L * bracket n ^ (2 / p - 1) * δ := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left h4 hL0) hyx (by linarith) (by positivity)
      _ = 2 * K * L * (bracket n ^ (2 / p - 1) / bracket n) := by
          rw [hδ]; field_simp
      _ = 2 * K * L * bracket n ^ (2 / p - 2) := by rw [h5]
  have hBs1 : bracket n ^ (2 / p - 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hB1 hs
  have hBs0 : 0 ≤ bracket n ^ (2 / p - 2) := Real.rpow_nonneg hBpos.le _
  set ε0 : ℝ := 2 * K * L * bracket n ^ (2 / p - 2) with hε0
  have hε0nn : 0 ≤ ε0 := by positivity
  have hε0le : ε0 ≤ 2 * K * L := by
    rw [hε0]
    have : 0 ≤ 2 * K * L := by positivity
    nlinarith
  have hfinal : ∀ x y : ℝ, r1 / 2 ≤ x → x ≤ y → y - x ≤ δ →
      factorialPowerWeight p c y - factorialPowerWeight p c x ≤
        factorialPowerWeight p c x * (ε0 * Real.exp (2 * K * L)) := by
    intro x y hx hxy hyx
    have hxpos : 0 < x := lt_of_lt_of_le (by linarith) hx
    have hg := weight_growth hp.le hc hxpos hxy
    have hWx := weight_pos hp1.le hc hxpos
    set ε : ℝ := L * x ^ (2 / p - 1) * (y - x) with hε
    have hεnn : 0 ≤ ε := by
      rw [hε]; have := Real.rpow_nonneg hxpos.le (2 / p - 1); have : 0 ≤ y - x := by linarith
      positivity
    have hεle : ε ≤ ε0 := hε_bound x y hx hxy hyx
    have hexp : Real.exp ε ≤ Real.exp (2 * K * L) := Real.exp_le_exp.2 (hεle.trans hε0le)
    calc factorialPowerWeight p c y - factorialPowerWeight p c x
        ≤ factorialPowerWeight p c x * Real.exp ε - factorialPowerWeight p c x := by
          have : factorialPowerWeight p c y ≤ factorialPowerWeight p c x * Real.exp (2 * (2 : ℝ) ^ (1 / p) * x ^ (2 / p - 1) * (y - x)) := hg
          have e : 2 * (2 : ℝ) ^ (1 / p) * x ^ (2 / p - 1) * (y - x) = ε := by rw [hε, hL]
          rw [e] at this; linarith
      _ = factorialPowerWeight p c x * (Real.exp ε - 1) := by ring
      _ ≤ factorialPowerWeight p c x * (ε * Real.exp ε) :=
          mul_le_mul_of_nonneg_left (exp_sub_one_le hεnn) hWx.le
      _ ≤ factorialPowerWeight p c x * (ε0 * Real.exp (2 * K * L)) := by
          apply mul_le_mul_of_nonneg_left _ hWx.le
          exact mul_le_mul hεle hexp (Real.exp_pos _).le hε0nn
  have hr1h : r1 / 2 ≤ r1 - δ := by
    have : r1 / 2 = Real.pi * |(n : ℝ)| := by rw [hr1e]; ring
    linarith
  have hfin : 0 ≤ ε0 * Real.exp (2 * K * L) := by positivity
  rcases le_total r1 r2 with h12 | h21
  · -- r1 ≤ r2: x = r1, y = r2
    have hmono := weight_monotone hp1 hc hr1pos.le h12
    rw [abs_of_nonneg (by linarith)]
    have := hfinal r1 r2 (by linarith) h12 (by have := abs_of_nonneg (sub_nonneg.2 h12); linarith)
    calc factorialPowerWeight p c r2 - factorialPowerWeight p c r1
        ≤ factorialPowerWeight p c r1 * (ε0 * Real.exp (2 * K * L)) := this
      _ = (2 * K * L * Real.exp (2 * K * L)) * factorialPowerWeight p c r1 *
            bracket n ^ (2 / p - 2) := by rw [hε0]; ring
  · -- r2 ≤ r1: x = r2, y = r1
    have hx2 : r1 / 2 ≤ r2 := by
      have : -δ ≤ r2 - r1 := by linarith [neg_abs_le (r2 - r1)]
      linarith
    have hmono := weight_monotone hp1 hc (by linarith : 0 ≤ r2) h21
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    have := hfinal r2 r1 hx2 h21 (by
      have := abs_of_nonneg (sub_nonneg.2 h21)
      have h' : |r1 - r2| = |r2 - r1| := abs_sub_comm _ _
      linarith)
    have hW21 : factorialPowerWeight p c r2 ≤ factorialPowerWeight p c r1 := hmono
    calc factorialPowerWeight p c r1 - factorialPowerWeight p c r2
        ≤ factorialPowerWeight p c r2 * (ε0 * Real.exp (2 * K * L)) := this
      _ ≤ factorialPowerWeight p c r1 * (ε0 * Real.exp (2 * K * L)) :=
          mul_le_mul_of_nonneg_right hW21 hfin
      _ = (2 * K * L * Real.exp (2 * K * L)) * factorialPowerWeight p c r1 *
            bracket n ^ (2 / p - 2) := by rw [hε0]; ring

/-- Finitely many small indices: a (non-explicit) constant independent of the coefficients. -/
theorem gap_small {p : ℝ} (hp : 2 < p) {K : ℝ} (hK : 0 < K) (N : ℕ) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ c : ℕ → ℝ, (∀ j, 1 ≤ c j ∧ c j ≤ 2) → ∀ (n : ℤ) (lam : ℝ),
      |(n : ℝ)| ≤ N → |lam - Real.pi * n| ≤ K / bracket n →
        |factorialPowerWeight p c (2 * lam) - factorialPowerWeight p c (2 * Real.pi * n)| ≤
          C0 * factorialPowerWeight p c (2 * Real.pi * n) * bracket n ^ (2 / p - 2) := by
  have hp1 : 1 ≤ p := by linarith
  have hp0 : 0 < p := by linarith
  have hs : 2 / p - 2 ≤ 0 := by
    have : 0 ≤ 2 / p := by positivity
    have h2 : 2 / p ≤ 1 := by rw [div_le_one hp0]; exact hp.le
    linarith
  set R : ℝ := 2 * Real.pi * N + 2 * K with hR
  set M : ℝ := ∑' j : ℕ, 2 * ((R ^ 2) ^ j / (Nat.factorial j : ℝ)) with hM
  have hMsum : Summable (fun j : ℕ => 2 * ((R ^ 2) ^ j / (Nat.factorial j : ℝ))) :=
    (Real.summable_pow_div_factorial (R ^ 2)).mul_left 2
  have hM2 : 2 ≤ M := by
    have := Summable.le_tsum hMsum 0 (fun j _ => by positivity)
    simpa using this
  have hMpos : 0 < M := by linarith
  set m0 : ℝ := bracket (N : ℤ) ^ (2 / p - 2) with hm0
  have hm0pos : 0 < m0 := Real.rpow_pos_of_pos (bracket_pos _) _
  refine ⟨2 * M / m0, by positivity, fun c hc n lam hn hl => ?_⟩
  have hB1 := one_le_bracket n
  have hBpos := bracket_pos n
  have hRa' : |2 * Real.pi * n| ≤ 2 * Real.pi * N := by
    rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos]
    have : |(2 : ℝ)| = 2 := by norm_num
    rw [this]
    exact mul_le_mul_of_nonneg_left hn (by positivity)
  have hRa : |2 * Real.pi * n| ≤ R := by
    have : 0 ≤ 2 * K := by positivity
    linarith
  have hRb : |2 * lam| ≤ R := by
    have h1 : |2 * lam| ≤ |2 * Real.pi * n| + |2 * lam - 2 * Real.pi * n| := by
      have := abs_sub_abs_le_abs_sub (2 * lam) (2 * Real.pi * n)
      linarith
    have h2 : |2 * lam - 2 * Real.pi * n| ≤ 2 * K := by
      rw [show 2 * lam - 2 * Real.pi * n = 2 * (lam - Real.pi * n) by ring, abs_mul]
      have hl' : |lam - Real.pi * n| ≤ K := by
        refine hl.trans ?_
        rw [div_le_iff₀ hBpos]; nlinarith
      have : |(2 : ℝ)| = 2 := by norm_num
      rw [this]; linarith
    linarith [hRa']
  have hWa1 := weight_ge_one hp1 hc (2 * Real.pi * n)
  have hWb1 := weight_ge_one hp1 hc (2 * lam)
  have hWaM := weight_le hp1 hc hRa
  have hWbM := weight_le hp1 hc hRb
  have hdiff : |factorialPowerWeight p c (2 * lam) - factorialPowerWeight p c (2 * Real.pi * n)| ≤
      2 * M := by
    rw [abs_le]; constructor <;> linarith
  have hbr : bracket n ≤ bracket (N : ℤ) := by
    unfold bracket
    apply Real.sqrt_le_sqrt
    have : (n : ℝ) ^ 2 ≤ ((N : ℤ) : ℝ) ^ 2 := by
      rw [Int.cast_natCast, ← sq_abs (n : ℝ)]
      exact pow_le_pow_left₀ (abs_nonneg _) hn 2
    linarith
  have hm : m0 ≤ bracket n ^ (2 / p - 2) := Real.rpow_le_rpow_of_nonpos hBpos hbr hs
  have hBs0 : 0 ≤ bracket n ^ (2 / p - 2) := Real.rpow_nonneg hBpos.le _
  calc |factorialPowerWeight p c (2 * lam) - factorialPowerWeight p c (2 * Real.pi * n)|
      ≤ 2 * M := hdiff
    _ = (2 * M / m0) * 1 * m0 := by field_simp
    _ ≤ (2 * M / m0) * factorialPowerWeight p c (2 * Real.pi * n) * bracket n ^ (2 / p - 2) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hWa1 (by positivity)) hm hm0pos.le
        positivity

/-- Part (C) of COMMAND03. -/
theorem factorialPower_gap_loss :
    (∀ p : ℝ, 2 < p → ∀ K : ℝ, 0 < K → ∃ C : ℝ, 0 < C ∧ ∀ c : ℕ → ℝ,
    (∀ j, 1 ≤ c j ∧ c j ≤ 2) → ∀ (n : ℤ) (lam : ℝ), |lam - Real.pi * n| ≤ K / bracket n →
      |factorialPowerWeight p c (2 * lam) - factorialPowerWeight p c (2 * Real.pi * n)| ≤
        C * factorialPowerWeight p c (2 * Real.pi * n) * bracket n ^ (2 / p - 2)) := by
  intro p hp K hK
  have hp1 : 1 ≤ p := by linarith
  obtain ⟨N0, hN0⟩ := exists_nat_ge (2 * K / Real.pi)
  obtain ⟨C0, hC0, hsmall⟩ := gap_small hp hK (N0 + 1)
  set Cl : ℝ := 2 * K * (2 * (2 : ℝ) ^ (1 / p)) * Real.exp (2 * K * (2 * (2 : ℝ) ^ (1 / p))) with hCl
  have hCl0 : 0 ≤ Cl := by positivity
  refine ⟨Cl + C0, by linarith, fun c hc n lam hl => ?_⟩
  have hBs0 : 0 ≤ bracket n ^ (2 / p - 2) := Real.rpow_nonneg (bracket_pos n).le _
  have hW0 : 0 ≤ factorialPowerWeight p c (2 * Real.pi * n) := by
    linarith [weight_ge_one hp1 hc (2 * Real.pi * n)]
  by_cases hnN : |(n : ℝ)| ≤ ((N0 + 1 : ℕ) : ℝ)
  · have := hsmall c hc n lam hnN hl
    calc _ ≤ C0 * factorialPowerWeight p c (2 * Real.pi * n) * bracket n ^ (2 / p - 2) := this
      _ ≤ (Cl + C0) * factorialPowerWeight p c (2 * Real.pi * n) * bracket n ^ (2 / p - 2) := by
          have : 0 ≤ Cl * factorialPowerWeight p c (2 * Real.pi * n) * bracket n ^ (2 / p - 2) :=
            by positivity
          nlinarith
  · have hn' : ((N0 + 1 : ℕ) : ℝ) < |(n : ℝ)| := not_le.1 hnN
    have hn1 : 1 ≤ |(n : ℝ)| := by
      have : (1 : ℝ) ≤ ((N0 + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N0)
      linarith
    have hK2 : 2 * K ≤ Real.pi * |(n : ℝ)| := by
      have h1 : 2 * K / Real.pi ≤ |(n : ℝ)| := by
        have : (N0 : ℝ) ≤ ((N0 + 1 : ℕ) : ℝ) := by push_cast; linarith
        linarith
      rw [div_le_iff₀ Real.pi_pos] at h1
      linarith
    have := gap_large hp hc hK hK2 hn1 hl
    calc _ ≤ Cl * factorialPowerWeight p c (2 * Real.pi * n) * bracket n ^ (2 / p - 2) := this
      _ ≤ (Cl + C0) * factorialPowerWeight p c (2 * Real.pi * n) * bracket n ^ (2 / p - 2) := by
          have : 0 ≤ C0 * factorialPowerWeight p c (2 * Real.pi * n) * bracket n ^ (2 / p - 2) :=
            by positivity
          nlinarith

/-! ### Statement identity with COMMAND03 (verbatim propositions) -/

theorem I037_command03_A : (∀ (p : ℝ), 2 < p → ∀ (c : ℕ → ℝ), (∀ j, 1 ≤ c j ∧ c j ≤ 2) →
    (∀ r' : ℝ, Summable (factorialPowerTerm p c r')) ∧
    ∀ r : ℝ, 0 < r →
      (0 < factorialPowerWeight p c r ∧
        DifferentiableAt ℝ (factorialPowerWeight p c) r ∧
        0 ≤ deriv (factorialPowerWeight p c) r / factorialPowerWeight p c r ∧
        deriv (factorialPowerWeight p c) r / factorialPowerWeight p c r ≤
          2 * (2 : ℝ) ^ (1 / p) * r ^ (2 / p - 1)) ∧
      ∀ m : ℕ,
        (0 < factorialPowerPartial p c m r ∧
          DifferentiableAt ℝ (factorialPowerPartial p c m) r ∧
          0 ≤ deriv (factorialPowerPartial p c m) r / factorialPowerPartial p c m r ∧
          deriv (factorialPowerPartial p c m) r / factorialPowerPartial p c m r ≤
            2 * (2 : ℝ) ^ (1 / p) * r ^ (2 / p - 1)) : Prop) :=
  factorialPower_logDerivative_majorant

theorem I037_command03_B :
    (∀ p : ℝ, 2 < p → Summable (fun n : ℤ => bracket n ^ (2 / p - 2)) : Prop) :=
  summable_bracket_rpow

theorem I037_command03_C :
    (∀ p : ℝ, 2 < p → ∀ K : ℝ, 0 < K → ∃ C : ℝ, 0 < C ∧ ∀ c : ℕ → ℝ,
    (∀ j, 1 ≤ c j ∧ c j ≤ 2) → ∀ (n : ℤ) (lam : ℝ), |lam - Real.pi * n| ≤ K / bracket n →
      |factorialPowerWeight p c (2 * lam) - factorialPowerWeight p c (2 * Real.pi * n)| ≤
        C * factorialPowerWeight p c (2 * Real.pi * n) * bracket n ^ (2 / p - 2) : Prop) :=
  factorialPower_gap_loss

end NlsGge.Atomic.I037
