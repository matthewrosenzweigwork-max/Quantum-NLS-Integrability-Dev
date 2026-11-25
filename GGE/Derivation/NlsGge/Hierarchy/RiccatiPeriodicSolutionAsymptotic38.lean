import NlsGge.Hierarchy.RiccatiWronskianIdentity38
import NlsGge.Hierarchy.RiccatiSmoothJetDerivativeAfterProductPrerequisite
import NlsGge.Hierarchy.RiccatiDerivativeExcessAndPeriodicEvaluatorRecoverySecond
import NlsGge.Hierarchy.RiccatiAttachedRecursionCore
import Mathlib

set_option autoImplicit false

/-! Asymptotic periodic Riccati solutions for large `η`.

Convention: `Γ' = -2ηΓ + ū - uΓ²` (the Riccati equation `Γ' = 2iζΓ + ū - uΓ²` at `ζ = iη`).
Smoothness predicate: `ContDiff ℝ ∞ u` (`∞` is `((⊤ : ℕ∞) : WithTop ℕ∞)`; `⊤` would be
analyticity in this Mathlib).  The formal variable `X = 1/(2iζ)` evaluates to `(-2η)⁻¹`. -/

namespace NlsGge.HierarchyRiccati.Core
open scoped ContDiff

noncomputable section


lemma sum_Icc_eq_range38 (f : ℕ → ℂ) (h0 : f 0 = 0) (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, f k = ∑ k ∈ Finset.range (K + 1), f k := by
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < K + 1), h0, zero_add]
  rfl

theorem residual_scalar38 (a b : ℕ → ℂ) (ub uu T lam : ℂ) (hT : lam * T = 1)
    (ha0 : a 0 = 0) (hb0 : b 0 = 0)
    (hrec : ∀ m, a (m + 1) = (if m = 0 then -ub else 0) + b m +
      uu * PowerSeries.coeff m (PowerSeries.mk a * PowerSeries.mk a)) (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, b k * T ^ k) - lam * (∑ k ∈ Finset.Icc 1 K, a k * T ^ k) - ub
        + uu * (∑ k ∈ Finset.Icc 1 K, a k * T ^ k) ^ 2
      = (if K = 0 then -ub else 0) + b K * T ^ K + uu * ∑ n ∈ Finset.Icc K (2 * K),
          (PowerSeries.trunc (K + 1) (PowerSeries.mk a) *
            PowerSeries.trunc (K + 1) (PowerSeries.mk a)).coeff n * T ^ n := by
  set P := PowerSeries.trunc (K + 1) (PowerSeries.mk a) with hP
  have hcP : ∀ k, k < K + 1 → P.coeff k = a k := by
    intro k hk
    simp [hP, PowerSeries.coeff_trunc, hk]
  have hS : ∑ k ∈ Finset.Icc 1 K, a k * T ^ k = P.eval T := by
    rw [sum_Icc_eq_range38 (fun k => a k * T ^ k) (by simp [ha0]),
      Polynomial.eval_eq_sum_range' (PowerSeries.natDegree_trunc_lt _ K)]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hcP k (Finset.mem_range.mp hk)]
  have hS2 : (P.eval T) ^ 2 = ∑ n ∈ Finset.range (2 * K + 1), (P * P).coeff n * T ^ n := by
    rw [sq, ← Polynomial.eval_mul,
      Polynomial.eval_eq_sum_range' (n := 2 * K + 1)]
    have h1 : P.natDegree < K + 1 := PowerSeries.natDegree_trunc_lt (PowerSeries.mk a) K
    have h2 := Polynomial.natDegree_mul_le (p := P) (q := P)
    omega
  have hg2 : ∀ n, n < K + 1 → (P * P).coeff n =
      PowerSeries.coeff n (PowerSeries.mk a * PowerSeries.mk a) := by
    intro n hn
    rw [Polynomial.coeff_mul, PowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    rw [hcP x.1 (by omega), hcP x.2 (by omega)]
    simp
  have hsplit : ∑ n ∈ Finset.range (2 * K + 1), (P * P).coeff n * T ^ n =
      ∑ n ∈ Finset.range K, (P * P).coeff n * T ^ n +
        ∑ n ∈ Finset.Icc K (2 * K), (P * P).coeff n * T ^ n := by
    have := Finset.sum_range_add_sum_Ico (fun n => (P * P).coeff n * T ^ n)
      (show K ≤ 2 * K + 1 by omega)
    rw [← this]
    congr 2
  have hlam : lam * (∑ k ∈ Finset.range (K + 1), a k * T ^ k) =
      ∑ j ∈ Finset.range K, a (j + 1) * T ^ j := by
    rw [Finset.sum_range_succ', mul_add, Finset.mul_sum]
    simp only [ha0, zero_mul, mul_zero, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_succ]
    linear_combination (a (j + 1) * T ^ j) * hT
  have hite : ∑ j ∈ Finset.range K, (if j = 0 then -ub else 0) * T ^ j =
      if K = 0 then 0 else -ub := by
    rcases Nat.eq_zero_or_pos K with rfl | hK
    · simp
    · rw [Finset.sum_eq_single 0]
      · simp [hK.ne']
      · intro j _ hj; simp [hj]
      · intro h; exact absurd (Finset.mem_range.mpr hK) h
  have hrecsum : ∑ j ∈ Finset.range K, a (j + 1) * T ^ j =
      (if K = 0 then 0 else -ub) + ∑ j ∈ Finset.range K, b j * T ^ j +
        uu * ∑ j ∈ Finset.range K, (P * P).coeff j * T ^ j := by
    rw [← hite, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hrec j, hg2 j (by have := Finset.mem_range.mp hj; omega)]
    ring
  have hbsum : ∑ k ∈ Finset.Icc 1 K, b k * T ^ k =
      ∑ j ∈ Finset.range K, b j * T ^ j + b K * T ^ K := by
    rw [sum_Icc_eq_range38 (fun k => b k * T ^ k) (by simp [hb0]), Finset.sum_range_succ]
  have hSa : ∑ k ∈ Finset.Icc 1 K, a k * T ^ k = ∑ k ∈ Finset.range (K + 1), a k * T ^ k :=
    sum_Icc_eq_range38 (fun k => a k * T ^ k) (by simp [ha0]) K
  have e1 : lam * ∑ k ∈ Finset.Icc 1 K, a k * T ^ k = ∑ j ∈ Finset.range K, a (j + 1) * T ^ j := by
    rw [hSa]; exact hlam
  have e2 : (∑ k ∈ Finset.Icc 1 K, a k * T ^ k) ^ 2 =
      ∑ n ∈ Finset.range K, (P * P).coeff n * T ^ n +
        ∑ n ∈ Finset.Icc K (2 * K), (P * P).coeff n * T ^ n := by
    rw [hS, hS2, hsplit]
  rw [hbsum, e1, e2, hrecsum]
  split_ifs <;> ring


lemma residual_rhs_bound38 (a b : ℕ → ℂ) (ub uu T : ℂ) (K : ℕ) {M : ℝ}
    (hM0 : 0 ≤ M) (ha : ∀ k, k ≤ K → ‖a k‖ ≤ M) (hb : ‖b K‖ ≤ M) (hub : ‖ub‖ ≤ M)
    (huu : ‖uu‖ ≤ M) (hT : ‖T‖ ≤ 1) :
    ‖(if K = 0 then -ub else 0) + b K * T ^ K + uu * ∑ n ∈ Finset.Icc K (2 * K),
          (PowerSeries.trunc (K + 1) (PowerSeries.mk a) *
            PowerSeries.trunc (K + 1) (PowerSeries.mk a)).coeff n * T ^ n‖
      ≤ (M + M + M * (((K : ℝ) + 1) * ((2 * K + 1) * M ^ 2))) * ‖T‖ ^ K := by
  set P := PowerSeries.trunc (K + 1) (PowerSeries.mk a) with hP
  have hcP : ∀ k, ‖P.coeff k‖ ≤ M := by
    intro k
    by_cases hk : k < K + 1
    · simp only [hP, PowerSeries.coeff_trunc, if_pos hk, PowerSeries.coeff_mk]
      exact ha k (by omega)
    · simp [hP, PowerSeries.coeff_trunc, hk, hM0]
  have hcc : ∀ n, n ≤ 2 * K → ‖(P * P).coeff n‖ ≤ (2 * K + 1) * M ^ 2 := by
    intro n hn
    rw [Polynomial.coeff_mul]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, ‖P.coeff x.1 * P.coeff x.2‖
        ≤ ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, M ^ 2 := by
          refine Finset.sum_le_sum fun x _ => ?_
          rw [norm_mul, sq]
          exact mul_le_mul (hcP _) (hcP _) (norm_nonneg _) hM0
      _ = (n + 1) * M ^ 2 := by
          rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]; push_cast; ring
      _ ≤ _ := by
          have : (n : ℝ) ≤ 2 * K := by exact_mod_cast hn
          nlinarith [sq_nonneg M]
  have hT0 := norm_nonneg T
  have hsum : ‖∑ n ∈ Finset.Icc K (2 * K), (P * P).coeff n * T ^ n‖ ≤
      ((K : ℝ) + 1) * ((2 * K + 1) * M ^ 2) * ‖T‖ ^ K := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ n ∈ Finset.Icc K (2 * K), ‖(P * P).coeff n * T ^ n‖
        ≤ ∑ n ∈ Finset.Icc K (2 * K), (2 * K + 1) * M ^ 2 * ‖T‖ ^ K := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hn' := Finset.mem_Icc.mp hn
          rw [norm_mul, norm_pow]
          refine mul_le_mul (hcc n hn'.2) ?_ (by positivity) (by positivity)
          exact pow_le_pow_of_le_one hT0 hT hn'.1
      _ = ((K : ℝ) + 1) * ((2 * K + 1) * M ^ 2 * ‖T‖ ^ K) := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
          have : 2 * K + 1 - K = K + 1 := by omega
          rw [this]; push_cast; ring
      _ = _ := by ring
  have hTK : 0 ≤ ‖T‖ ^ K := by positivity
  calc _ ≤ ‖(if K = 0 then -ub else 0)‖ + ‖b K * T ^ K‖ + ‖uu * ∑ n ∈ Finset.Icc K (2 * K),
          (P * P).coeff n * T ^ n‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr; exact norm_add_le _ _
    _ ≤ M * ‖T‖ ^ K + M * ‖T‖ ^ K + M * (((K : ℝ) + 1) * ((2 * K + 1) * M ^ 2) * ‖T‖ ^ K) := by
        gcongr
        · split_ifs with h
          · subst h; simpa using hub
          · simp; positivity
        · rw [norm_mul, norm_pow]; gcongr
        · rw [norm_mul]; gcongr
    _ = _ := by ring


section Resolvent38
open MeasureTheory Set Filter Topology


def resInt38 (η : ℝ) (g : ℝ → ℂ) (t : ℝ) : ℂ := (Real.exp (2 * η * t)) • g t

def resolv38 (η : ℝ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Real.exp (-(2 * η) * x)) • ∫ t in Iic x, resInt38 η g t

lemma resInt38_continuous (η : ℝ) {g : ℝ → ℂ} (hg : Continuous g) :
    Continuous (resInt38 η g) := by
  unfold resInt38
  exact (Real.continuous_exp.comp (by fun_prop)).smul hg

lemma resInt38_integrableOn {η : ℝ} (hη : 0 < η) {g : ℝ → ℂ} (hg : Continuous g) {B : ℝ}
    (hB : ∀ x, ‖g x‖ ≤ B) (x : ℝ) : IntegrableOn (resInt38 η g) (Iic x) := by
  have h := (integrableOn_exp_mul_Iic (a := 2 * η) (by positivity) x).const_mul B
  refine Integrable.mono' h (resInt38_continuous η hg).aestronglyMeasurable ?_
  filter_upwards with t
  unfold resInt38
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm]
  exact mul_le_mul_of_nonneg_right (hB t) (Real.exp_pos _).le

lemma resolv38_bound {η : ℝ} (hη : 0 < η) {g : ℝ → ℂ} (hg : Continuous g) {B : ℝ}
    (hB : ∀ x, ‖g x‖ ≤ B) (x : ℝ) : ‖resolv38 η g x‖ ≤ B / (2 * η) := by
  have hint := (integrableOn_exp_mul_Iic (a := 2 * η) (by positivity) x).const_mul B
  have h1 : ‖∫ t in Iic x, resInt38 η g t‖ ≤ ∫ t in Iic x, B * Real.exp (2 * η * t) := by
    refine norm_integral_le_of_norm_le hint ?_
    filter_upwards with t
    unfold resInt38
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm]
    exact mul_le_mul_of_nonneg_right (hB t) (Real.exp_pos _).le
  rw [integral_const_mul, integral_exp_mul_Iic (by positivity)] at h1
  unfold resolv38
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-(2 * η) * x) * ‖∫ t in Iic x, resInt38 η g t‖
      ≤ Real.exp (-(2 * η) * x) * (B * (Real.exp (2 * η * x) / (2 * η))) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = B / (2 * η) := by
        have : Real.exp (-(2 * η) * x) * Real.exp (2 * η * x) = 1 := by
          rw [← Real.exp_add]; simp
        calc Real.exp (-(2 * η) * x) * (B * (Real.exp (2 * η * x) / (2 * η)))
            = (Real.exp (-(2 * η) * x) * Real.exp (2 * η * x)) * (B / (2 * η)) := by ring
          _ = B / (2 * η) := by rw [this, one_mul]

lemma resolv38_hasDerivAt {η : ℝ} (hη : 0 < η) {g : ℝ → ℂ} (hg : Continuous g) {B : ℝ}
    (hB : ∀ x, ‖g x‖ ≤ B) (x : ℝ) :
    HasDerivAt (resolv38 η g) (-(2 * (η : ℂ)) * resolv38 η g x + g x) x := by
  have hc := resInt38_continuous η hg
  set c : ℂ := ∫ t in Iic 0, resInt38 η g t with hcdef
  have hrepr : ∀ y, resolv38 η g y =
      (Real.exp (-(2 * η) * y)) • (c + ∫ t in (0:ℝ)..y, resInt38 η g t) := by
    intro y
    unfold resolv38
    congr 1
    have := intervalIntegral.integral_Iic_sub_Iic (resInt38_integrableOn hη hg hB 0)
      (resInt38_integrableOn hη hg hB y) (μ := volume)
    rw [← this]; ring
  have h1 : HasDerivAt (fun y : ℝ => Real.exp (-(2 * η) * y))
      (Real.exp (-(2 * η) * x) * (-(2 * η))) x := by
    have := ((hasDerivAt_id x).const_mul (-(2 * η))).exp
    simpa using this
  have h2 : HasDerivAt (fun y : ℝ => c + ∫ t in (0:ℝ)..y, resInt38 η g t)
      (resInt38 η g x) x :=
    ((hc.integral_hasStrictDerivAt 0 x).hasDerivAt).const_add c
  have h3 := h1.smul h2
  have hfun : resolv38 η g = fun y => (Real.exp (-(2 * η) * y)) •
      (c + ∫ t in (0:ℝ)..y, resInt38 η g t) := funext hrepr
  rw [hfun]
  have hE : Real.exp (-(2 * η) * x) * Real.exp (2 * η * x) = 1 := by
    rw [← Real.exp_add]; simp
  have hk : Real.exp (-(2 * η) * x) • resInt38 η g x = g x := by
    unfold resInt38; rw [smul_smul, hE, one_smul]
  convert h3 using 1
  beta_reduce
  rw [hk]
  simp only [Complex.real_smul]
  push_cast
  ring


lemma resolv38_periodic {η : ℝ} {g : ℝ → ℂ} (hg : Function.Periodic g 1) :
    Function.Periodic (resolv38 η g) 1 := by
  intro x
  have hmp : MeasurePreserving (fun t : ℝ => t + 1) volume volume :=
    measurePreserving_add_right volume 1
  have hpre : (fun t : ℝ => t + 1) ⁻¹' Iic (x + 1) = Iic x := by
    ext t; simp
  have h := hmp.setIntegral_preimage_emb (measurableEmbedding_addRight (1 : ℝ))
    (resInt38 η g) (Iic (x + 1))
  rw [hpre] at h
  have hshift : ∀ t, resInt38 η g (t + 1) = (Real.exp (2 * η)) • resInt38 η g t := by
    intro t
    unfold resInt38
    rw [hg t, smul_smul, ← Real.exp_add]
    congr 2; ring
  simp only [hshift] at h
  rw [integral_smul] at h
  unfold resolv38
  rw [← h, smul_smul]
  have : Real.exp (-(2 * η) * (x + 1)) * Real.exp (2 * η) = Real.exp (-(2 * η) * x) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [this]

lemma periodic_ode_zero {η : ℝ} (hη : 0 < η) {f : ℝ → ℂ}
    (hd : ∀ x, HasDerivAt f (-(2 * (η : ℂ)) * f x) x) (hp : Function.Periodic f 1) :
    ∀ x, f x = 0 := by
  have hφ : ∀ x, HasDerivAt (fun y => (Real.exp (2 * η * y)) • f y) 0 x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => Real.exp (2 * η * y))
        (Real.exp (2 * η * x) * (2 * η)) x := by
      simpa using ((hasDerivAt_id x).const_mul (2 * η)).exp
    have h3 := h1.smul (hd x)
    convert h3 using 1
    simp only [Complex.real_smul]; push_cast; ring
  have hconst : ∀ x, (Real.exp (2 * η * x)) • f x = (Real.exp (2 * η * 0)) • f 0 := by
    intro x
    exact is_const_of_deriv_eq_zero (fun y => (hφ y).differentiableAt)
      (fun y => (hφ y).deriv) x 0
  have hf : ∀ x, f x = Complex.ofReal (Real.exp (-(2 * η) * x)) * f 0 := by
    intro x
    have := hconst x
    simp only [mul_zero, Real.exp_zero, one_smul, Complex.real_smul] at this
    have hne : (Real.exp (2 * η * x) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.exp_pos _).ne'
    have e : (Real.exp (-(2 * η) * x) : ℂ) * Real.exp (2 * η * x) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]; simp
    calc f x = (Real.exp (-(2 * η) * x) : ℂ) * (Real.exp (2 * η * x) * f x) := by
          rw [← mul_assoc, e, one_mul]
      _ = _ := by rw [this]
  have h1 := hf 1
  have h10 : f 1 = f 0 := by simpa using hp 0
  rw [h10] at h1
  have hlt : Real.exp (-(2 * η) * 1) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  have h0 : f 0 = 0 := by
    have h2 : (1 - (Real.exp (-(2 * η) * 1) : ℂ)) * f 0 = 0 := by
      rw [sub_mul, one_mul]; exact sub_eq_zero.mpr h1
    rcases mul_eq_zero.mp h2 with h | h
    · exfalso
      have h' : Real.exp (-(2 * η) * 1) = 1 := by
        have : (Real.exp (-(2 * η) * 1) : ℂ) = 1 := (sub_eq_zero.mp h).symm
        exact_mod_cast this
      linarith
    · exact h
  intro x
  rw [hf x, h0, mul_zero]

lemma resolv38_sub {η : ℝ} (hη : 0 < η) {g₁ g₂ : ℝ → ℂ} (h₁ : Continuous g₁) (h₂ : Continuous g₂)
    {B₁ B₂ : ℝ} (hB₁ : ∀ x, ‖g₁ x‖ ≤ B₁) (hB₂ : ∀ x, ‖g₂ x‖ ≤ B₂) (x : ℝ) :
    resolv38 η (fun y => g₁ y - g₂ y) x = resolv38 η g₁ x - resolv38 η g₂ x := by
  unfold resolv38
  rw [← smul_sub, ← integral_sub (resInt38_integrableOn hη h₁ hB₁ x)
    (resInt38_integrableOn hη h₂ hB₂ x)]
  congr 2
  funext t
  unfold resInt38
  rw [smul_sub]


open BoundedContinuousFunction in
theorem riccati_correction_exists38 {η : ℝ} (hη : 0 < η) {u S ρ : ℝ → ℂ}
    (hu : Continuous u) (hS : Continuous S) (hρ : Continuous ρ)
    (hup : Function.Periodic u 1) (hSp : Function.Periodic S 1)
    (hρp : Function.Periodic ρ 1)
    {Mu : ℝ} (hMu0 : 0 ≤ Mu) (hMu : ∀ x, ‖u x‖ ≤ Mu) (hS1 : ∀ x, ‖S x‖ ≤ 1)
    (hηM : 4 * Mu ≤ η) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hρδ : ∀ x, ‖ρ x‖ ≤ η * δ) :
    ∃ R : ℝ → ℂ, Continuous R ∧ Function.Periodic R 1 ∧ (∀ x, ‖R x‖ ≤ δ) ∧
      ∀ x, HasDerivAt R (-(2 * (η : ℂ)) * R x +
        (-ρ x - u x * (2 * S x * R x + R x ^ 2))) x := by
  classical
  let G : (ℝ → ℂ) → ℝ → ℂ := fun R y => -ρ y - u y * (2 * S y * R y + R y ^ 2)
  have hGc : ∀ R : ℝ → ℂ, Continuous R → Continuous (G R) := by
    intro R hR
    simp only [G]; fun_prop
  have hGb : ∀ R : ℝ →ᵇ ℂ, ∀ y, ‖G R y‖ ≤ η * δ + Mu * (2 * ‖R‖ + ‖R‖ ^ 2) := by
    intro R y
    have hRy : ‖R y‖ ≤ ‖R‖ := R.norm_coe_le_norm y
    have h1 : ‖u y * (2 * S y * R y + R y ^ 2)‖ ≤ Mu * (2 * ‖R‖ + ‖R‖ ^ 2) := by
      rw [norm_mul]
      refine mul_le_mul (hMu y) ?_ (norm_nonneg _) hMu0
      calc ‖2 * S y * R y + R y ^ 2‖ ≤ ‖2 * S y * R y‖ + ‖R y ^ 2‖ := norm_add_le _ _
        _ ≤ 2 * ‖R‖ + ‖R‖ ^ 2 := by
          have a1 : ‖2 * S y * R y‖ ≤ 2 * ‖R‖ := by
            rw [norm_mul, norm_mul]
            have : ‖(2 : ℂ)‖ = 2 := by simp
            rw [this]
            have := hS1 y
            nlinarith [norm_nonneg (S y), norm_nonneg (R y)]
          have a2 : ‖R y ^ 2‖ ≤ ‖R‖ ^ 2 := by
            rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hRy 2
          linarith
    calc ‖G R y‖ ≤ ‖ρ y‖ + ‖u y * (2 * S y * R y + R y ^ 2)‖ := by
          simp only [G, sub_eq_add_neg]
          calc _ ≤ ‖-ρ y‖ + ‖-(u y * (2 * S y * R y + R y ^ 2))‖ := norm_add_le _ _
            _ = _ := by rw [norm_neg, norm_neg]
      _ ≤ _ := by linarith [hρδ y]
  have hGp : ∀ R : ℝ →ᵇ ℂ, Function.Periodic R 1 → Function.Periodic (G R) 1 := by
    intro R hR x
    simp only [G, hup x, hSp x, hρp x, hR x]
  have hTc : ∀ R : ℝ →ᵇ ℂ, Continuous (resolv38 η (G R)) := by
    intro R
    exact continuous_iff_continuousAt.mpr fun x =>
      (resolv38_hasDerivAt hη (hGc R R.continuous) (hGb R) x).continuousAt
  let T : (ℝ →ᵇ ℂ) → (ℝ →ᵇ ℂ) := fun R =>
    BoundedContinuousFunction.ofNormedAddCommGroup (resolv38 η (G R)) (hTc R)
      ((η * δ + Mu * (2 * ‖R‖ + ‖R‖ ^ 2)) / (2 * η))
      (fun x => resolv38_bound hη (hGc R R.continuous) (hGb R) x)
  have hTapp : ∀ R x, T R x = resolv38 η (G R) x := fun R x => rfl
  let s : Set (ℝ →ᵇ ℂ) := {R | Function.Periodic R 1 ∧ ‖R‖ ≤ δ}
  have hev : ∀ x : ℝ, Continuous fun R : ℝ →ᵇ ℂ => R x := fun x =>
    (LipschitzWith.of_dist_le_mul (K := 1) fun a b => by
      simpa using BoundedContinuousFunction.dist_coe_le_dist (f := a) (g := b) x).continuous
  have hsc : IsClosed s := by
    have h1 : IsClosed {R : ℝ →ᵇ ℂ | Function.Periodic R 1} := by
      have : {R : ℝ →ᵇ ℂ | Function.Periodic R 1} = ⋂ x : ℝ, {R | R (x + 1) = R x} := by
        ext R; simp [Function.Periodic]
      rw [this]
      exact isClosed_iInter fun x => isClosed_eq
        (hev (x + 1)) (hev x)
    have h2 : IsClosed {R : ℝ →ᵇ ℂ | ‖R‖ ≤ δ} := isClosed_le continuous_norm continuous_const
    exact h1.inter h2
  have hmaps : Set.MapsTo T s s := by
    rintro R ⟨hRp, hRn⟩
    refine ⟨?_, ?_⟩
    · exact resolv38_periodic (hGp R hRp)
    · refine (BoundedContinuousFunction.norm_le hδ0).mpr fun x => ?_
      rw [hTapp]
      refine (resolv38_bound hη (hGc R R.continuous) (hGb R) x).trans ?_
      rw [div_le_iff₀ (by positivity)]
      have hm0 := norm_nonneg R
      have h2 : 2 * ‖R‖ + ‖R‖ ^ 2 ≤ 3 * δ := by nlinarith
      have h3 : Mu * (2 * ‖R‖ + ‖R‖ ^ 2) ≤ Mu * (3 * δ) :=
        mul_le_mul_of_nonneg_left h2 hMu0
      nlinarith [mul_nonneg hMu0 hδ0]
  have hlip : ∀ R₁ ∈ s, ∀ R₂ ∈ s, dist (T R₁) (T R₂) ≤ (1 / 2) * dist R₁ R₂ := by
    rintro R₁ ⟨-, h₁⟩ R₂ ⟨-, h₂⟩
    have hd0 := dist_nonneg (x := R₁) (y := R₂)
    refine (BoundedContinuousFunction.dist_le (by positivity)).mpr fun x => ?_
    rw [dist_eq_norm, hTapp, hTapp]
    have hdiff : ∀ y, ‖G R₁ y - G R₂ y‖ ≤ 4 * Mu * dist R₁ R₂ := by
      intro y
      have e : G R₁ y - G R₂ y = -(u y * ((R₁ y - R₂ y) * (2 * S y + R₁ y + R₂ y))) := by
        simp only [G]; ring
      rw [e, norm_neg, norm_mul, norm_mul]
      have a1 : ‖R₁ y - R₂ y‖ ≤ dist R₁ R₂ := by
        rw [← dist_eq_norm]; exact BoundedContinuousFunction.dist_coe_le_dist y
      have a2 : ‖2 * S y + R₁ y + R₂ y‖ ≤ 4 := by
        calc _ ≤ ‖2 * S y‖ + ‖R₁ y‖ + ‖R₂ y‖ := by
              refine (norm_add_le _ _).trans ?_
              gcongr; exact norm_add_le _ _
          _ ≤ 2 + δ + δ := by
              have : ‖2 * S y‖ ≤ 2 := by
                rw [norm_mul]
                have : ‖(2 : ℂ)‖ = 2 := by simp
                rw [this]; nlinarith [hS1 y]
              have b1 := R₁.norm_coe_le_norm y
              have b2 := R₂.norm_coe_le_norm y
              linarith
          _ ≤ 4 := by linarith
      calc ‖u y‖ * (‖R₁ y - R₂ y‖ * ‖2 * S y + R₁ y + R₂ y‖)
          ≤ Mu * (dist R₁ R₂ * 4) := by
            gcongr
            · exact hMu y
        _ = 4 * Mu * dist R₁ R₂ := by ring
    have hc1 := hGc R₁ R₁.continuous
    have hc2 := hGc R₂ R₂.continuous
    have hB1 := hGb R₁
    have hB2 := hGb R₂
    rw [← resolv38_sub hη hc1 hc2 hB1 hB2 x]
    have := resolv38_bound hη (hc1.sub hc2) (fun y => hdiff y) x
    refine this.trans ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hd0 hMu0]
  have hcontr : ContractingWith (2⁻¹ : NNReal) (hmaps.restrict T s s) := by
    refine ⟨by
      rw [← NNReal.coe_lt_coe]; simp; norm_num, ?_⟩
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    have := hlip a a.2 b b.2
    change dist (T (a : ℝ →ᵇ ℂ)) (T (b : ℝ →ᵇ ℂ)) ≤ ((2⁻¹ : NNReal) : ℝ) * dist (a : ℝ →ᵇ ℂ) b
    simpa using this
  have hz : (0 : ℝ →ᵇ ℂ) ∈ s := ⟨fun x => rfl, by simpa using hδ0⟩
  obtain ⟨R, hRs, hRfix, -⟩ := hcontr.exists_fixedPoint' hsc.isComplete hmaps hz
    (edist_ne_top _ _)
  have hReq : ∀ x, R x = resolv38 η (G R) x := by
    intro x
    have := congrArg (fun F : ℝ →ᵇ ℂ => F x) hRfix
    simpa [hTapp] using this.symm
  have hRfun : (R : ℝ → ℂ) = resolv38 η (G R) := funext hReq
  refine ⟨R, R.continuous, hRs.1, fun x => (R.norm_coe_le_norm x).trans hRs.2, fun x => ?_⟩
  have := resolv38_hasDerivAt hη (hGc R R.continuous) (hGb R) x
  rw [← hRfun] at this
  exact this


theorem periodic_norm_attains38 {f : ℝ → ℂ} (hf : Continuous f) (hp : Function.Periodic f 1) :
    ∃ x₀, ∀ x, ‖f x‖ ≤ ‖f x₀‖ := by
  obtain ⟨y, -, hy⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMaxOn
    (Set.nonempty_Icc.mpr zero_le_one) (hf.norm.continuousOn)
  refine ⟨y, fun x => ?_⟩
  obtain ⟨z, hz, hxz⟩ := hp.exists_mem_Ico₀ one_pos x
  rw [hxz]
  exact hy ⟨hz.1, hz.2.le⟩

theorem riccati_unique_abstract38 {η : ℝ} (hη : 0 < η) {u v Γ₁ Γ₂ : ℝ → ℂ}
    (hu : Continuous u) (hup : Function.Periodic u 1)
    {Mu b : ℝ} (hMu : ∀ x, ‖u x‖ ≤ Mu) (hb₁ : ∀ x, ‖Γ₁ x‖ ≤ b) (hb₂ : ∀ x, ‖Γ₂ x‖ ≤ b)
    (hMb : Mu * b < η)
    (hc₁ : Continuous Γ₁) (hc₂ : Continuous Γ₂)
    (hp₁ : Function.Periodic Γ₁ 1) (hp₂ : Function.Periodic Γ₂ 1)
    (hd₁ : ∀ x, HasDerivAt Γ₁ (-(2 * (η : ℂ)) * Γ₁ x + v x - u x * Γ₁ x ^ 2) x)
    (hd₂ : ∀ x, HasDerivAt Γ₂ (-(2 * (η : ℂ)) * Γ₂ x + v x - u x * Γ₂ x ^ 2) x) :
    ∀ x, Γ₁ x = Γ₂ x := by
  set D : ℝ → ℂ := fun x => Γ₁ x - Γ₂ x with hD
  set h : ℝ → ℂ := fun x => -(u x * (Γ₁ x + Γ₂ x) * D x) with hh
  have hDc : Continuous D := hc₁.sub hc₂
  have hDp : Function.Periodic D 1 := fun x => by simp only [hD, hp₁ x, hp₂ x]
  have hhc : Continuous h := by simp only [hh]; fun_prop
  have hhp : Function.Periodic h 1 := fun x => by simp only [hh, hD, hup x, hp₁ x, hp₂ x]
  obtain ⟨x₀, hx₀⟩ := periodic_norm_attains38 hDc hDp
  have hMu0 : 0 ≤ Mu := (norm_nonneg _).trans (hMu 0)
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb₁ 0)
  set m := ‖D x₀‖ with hm
  have hhB : ∀ x, ‖h x‖ ≤ 2 * Mu * b * m := by
    intro x
    simp only [hh, norm_neg, norm_mul]
    have : ‖Γ₁ x + Γ₂ x‖ ≤ 2 * b := (norm_add_le _ _).trans (by linarith [hb₁ x, hb₂ x])
    have h1 : ‖u x‖ * ‖Γ₁ x + Γ₂ x‖ ≤ Mu * (2 * b) :=
      mul_le_mul (hMu x) this (norm_nonneg _) hMu0
    calc ‖u x‖ * ‖Γ₁ x + Γ₂ x‖ * ‖D x‖ ≤ Mu * (2 * b) * m :=
          mul_le_mul h1 (hx₀ x) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hW : ∀ x, HasDerivAt (fun y => D y - resolv38 η h y) (-(2 * (η : ℂ)) *
      (D x - resolv38 η h x)) x := by
    intro x
    have h1 := (hd₁ x).sub (hd₂ x)
    have h2 := resolv38_hasDerivAt hη hhc (fun y => hhB y) x
    have h3 := h1.sub h2
    convert h3 using 1
    simp only [hh, hD]; ring
  have hW0 := periodic_ode_zero hη hW (fun x => by
    simp only [hDp x, resolv38_periodic hhp x])
  have hDeq : ∀ x, D x = resolv38 η h x := fun x => sub_eq_zero.mp (hW0 x)
  have hbound : m ≤ (Mu * b / η) * m := by
    have := resolv38_bound hη hhc (fun y => hhB y) x₀
    rw [← hDeq] at this
    refine this.trans (le_of_eq ?_)
    field_simp
  have hq : Mu * b / η < 1 := by rw [div_lt_one hη]; exact hMb
  have hm0 : m = 0 := by
    by_contra hne
    have hpos : 0 < m := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    nlinarith
  intro x
  have := hx₀ x
  rw [hm0] at this
  have : D x = 0 := norm_le_zero_iff.mp this
  exact sub_eq_zero.mp this


end Resolvent38


lemma evalJet_recursion38 (u : ℝ → ℂ) (x : ℝ) (m : ℕ) :
    riccatiJetEvaluation u x (p (m + 1)) =
      (if m = 0 then -star (u x) else 0) + riccatiJetEvaluation u x (spatialD (p m)) +
      u x * PowerSeries.coeff m (PowerSeries.mk (fun k => riccatiJetEvaluation u x (p k)) *
        PowerSeries.mk (fun k => riccatiJetEvaluation u x (p k))) := by
  have h := congrArg (PowerSeries.coeff (m + 1)) riccatiGamma38_eq
  have hP : p (m + 1) = (if m = 0 then -MvPolynomial.X (true, 0) else 0) + spatialD (p m) +
      MvPolynomial.X (false, 0) * ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m, p x.1 * p x.2 := by
    have := h
    rw [map_add, map_add, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_C_mul, seriesD38_coeff, map_neg, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_mul] at this
    simp only [riccatiGamma38, PowerSeries.coeff_mk, PowerSeries.coeff_X] at this
    rw [this]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · simp [hm.ne']
  have h2 := congrArg (riccatiJetEvaluation u x) hP
  rw [h2]
  simp only [riccatiJetEvaluation, map_add, map_mul, map_sum, polynomialEvaluation_add, polynomialEvaluation_mul, PowerSeries.coeff_mul, PowerSeries.coeff_mk]
  have e1 : (polynomialEvaluation fun v => riccatiJetFunction u v x)
      (MvPolynomial.X (false, 0)) = u x := by simp [riccatiJetFunction]
  have e2 : (polynomialEvaluation fun v => riccatiJetFunction u v x)
      (if m = 0 then -MvPolynomial.X (true, 0) else 0) = if m = 0 then -star (u x) else 0 := by
    split_ifs
    · simp [riccatiJetFunction]
    · simp
  rw [e1, e2]


section Asymptotic38

lemma evalJet_continuous38 (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (P : Poly) :
    Continuous (fun x => riccatiJetEvaluation u x P) :=
  continuous_iff_continuousAt.mpr fun x =>
    (riccatiJetEvaluation_hasDerivAt u hu P x).continuousAt

lemma evalJet_periodic38 (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (hper : Function.Periodic u 1)
    (P : Poly) : Function.Periodic (fun x => riccatiJetEvaluation u x P) 1 :=
  riccatiJetEvaluation_periodic_of_smooth_periodicNativeRecovery u hu hper P

lemma evalJet_bound38 (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (hper : Function.Periodic u 1)
    (P : Poly) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖riccatiJetEvaluation u x P‖ ≤ M := by
  obtain ⟨x₀, hx₀⟩ := periodic_norm_attains38 (evalJet_continuous38 u hu P)
    (evalJet_periodic38 u hu hper P)
  exact ⟨_, norm_nonneg _, hx₀⟩

/-- The truncation `Γ_K(x) = Σ_{k=1}^K p_k(x) (-2η)^{-k}`. -/
def riccatiTrunc38 (u : ℝ → ℂ) (K : ℕ) (η : ℝ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 K, riccatiJetEvaluation u x (p k) * (-2 * (η : ℂ))⁻¹ ^ k

/-- Its `x`-derivative (termwise). -/
def riccatiTruncD38 (u : ℝ → ℂ) (K : ℕ) (η : ℝ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 K, riccatiJetEvaluation u x (spatialD (p k)) * (-2 * (η : ℂ))⁻¹ ^ k

lemma riccatiTrunc38_hasDerivAt (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (K : ℕ) (η : ℝ) (x : ℝ) :
    HasDerivAt (riccatiTrunc38 u K η) (riccatiTruncD38 u K η x) x := by
  unfold riccatiTrunc38 riccatiTruncD38
  exact HasDerivAt.fun_sum fun k _ =>
    (riccatiJetEvaluation_hasDerivAt u hu (p k) x).mul_const _

lemma sum_periodic38 (f : ℕ → ℝ → ℂ) (c : ℂ) (K : ℕ) (hf : ∀ k, Function.Periodic (f k) 1) :
    Function.Periodic (fun x => ∑ k ∈ Finset.Icc 1 K, f k x * c ^ k) 1 := by
  intro x
  exact Finset.sum_congr rfl fun k _ => by rw [hf k x]

lemma sum_continuous38 (f : ℕ → ℝ → ℂ) (c : ℂ) (K : ℕ) (hf : ∀ k, Continuous (f k)) :
    Continuous (fun x => ∑ k ∈ Finset.Icc 1 K, f k x * c ^ k) :=
  continuous_finsetSum _ fun k _ => (hf k).mul continuous_const

lemma riccatiResidual38 (u : ℝ → ℂ) (K : ℕ) {η : ℝ} (hη : 0 < η) (x : ℝ) :
    riccatiTruncD38 u K η x - (-2 * (η : ℂ)) * riccatiTrunc38 u K η x - star (u x)
        + u x * riccatiTrunc38 u K η x ^ 2
      = (if K = 0 then -star (u x) else 0) +
          riccatiJetEvaluation u x (spatialD (p K)) * (-2 * (η : ℂ))⁻¹ ^ K +
          u x * ∑ n ∈ Finset.Icc K (2 * K),
            (PowerSeries.trunc (K + 1) (PowerSeries.mk fun k => riccatiJetEvaluation u x (p k)) *
              PowerSeries.trunc (K + 1)
                (PowerSeries.mk fun k => riccatiJetEvaluation u x (p k))).coeff n *
              (-2 * (η : ℂ))⁻¹ ^ n := by
  have hne : (-2 * (η : ℂ)) ≠ 0 := by
    have : (η : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
    simpa using this
  exact residual_scalar38 (fun k => riccatiJetEvaluation u x (p k))
    (fun k => riccatiJetEvaluation u x (spatialD (p k))) (star (u x)) (u x)
    ((-2 * (η : ℂ))⁻¹) (-2 * (η : ℂ)) (mul_inv_cancel₀ hne) (by simp [p, riccatiJetEvaluation])
    (by simp [p, riccatiJetEvaluation]) (evalJet_recursion38 u x) K

theorem riccatiPeriodicSolution_asymptotic38 (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) (K : ℕ) :
    ∃ η₀ C : ℝ, 0 < η₀ ∧ ∀ η : ℝ, η₀ ≤ η → ∃ Γ : ℝ → ℂ, Continuous Γ ∧
      Function.Periodic Γ 1 ∧
      (∀ x, HasDerivAt Γ (-(2 * η) * Γ x + star (u x) - u x * Γ x ^ 2) x) ∧
      (∀ x, ‖Γ x - ∑ k ∈ Finset.Icc 1 K,
        riccatiJetEvaluation u x (p k) * (-2 * (η : ℂ))⁻¹ ^ k‖ ≤ C * η⁻¹ ^ (K + 1)) := by
  classical
  choose bd hbd0 hbd using fun P : Poly => evalJet_bound38 u hu hper P
  set M : ℝ := ∑ k ∈ Finset.range (K + 1), bd (p k) + bd (spatialD (p K)) +
    bd (MvPolynomial.X (false, 0)) + bd (MvPolynomial.X (true, 0)) with hMdef
  have hsum0 : 0 ≤ ∑ k ∈ Finset.range (K + 1), bd (p k) :=
    Finset.sum_nonneg fun k _ => hbd0 _
  have hM0 : 0 ≤ M := by
    have := hbd0 (spatialD (p K)); have := hbd0 (MvPolynomial.X (false, 0))
    have := hbd0 (MvPolynomial.X (true, 0)); linarith
  have ha : ∀ k, k ≤ K → ∀ x, ‖riccatiJetEvaluation u x (p k)‖ ≤ M := by
    intro k hk x
    have h1 : bd (p k) ≤ ∑ j ∈ Finset.range (K + 1), bd (p j) :=
      Finset.single_le_sum (f := fun j => bd (p j)) (fun j _ => hbd0 _)
        (Finset.mem_range.mpr (by omega))
    have := hbd0 (spatialD (p K)); have := hbd0 (MvPolynomial.X (false, 0))
    have := hbd0 (MvPolynomial.X (true, 0))
    linarith [hbd (p k) x]
  have hb : ∀ x, ‖riccatiJetEvaluation u x (spatialD (p K))‖ ≤ M := by
    intro x
    have := hbd0 (MvPolynomial.X (false, 0)); have := hbd0 (MvPolynomial.X (true, 0))
    linarith [hbd (spatialD (p K)) x]
  have hu₀ : ∀ x, ‖u x‖ ≤ M := by
    intro x
    have := hbd0 (MvPolynomial.X (true, 0))
    have := hbd0 (spatialD (p K))
    have h := hbd (MvPolynomial.X (false, 0)) x
    simp [riccatiJetFunction] at h
    linarith
  set Cres : ℝ := M + M + M * (((K : ℝ) + 1) * ((2 * K + 1) * M ^ 2)) with hCres
  have hCres0 : 0 ≤ Cres := by positivity
  refine ⟨max 1 (max (K * M) (max (4 * M) Cres)), Cres, lt_of_lt_of_le one_pos (le_max_left _ _),
    fun η hη => ?_⟩
  have hη1 : 1 ≤ η := (le_max_left _ _).trans hη
  have hηKM : (K : ℝ) * M ≤ η := ((le_max_left _ _).trans (le_max_right _ _)).trans hη
  have hη4 : 4 * M ≤ η :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hη
  have hηC : Cres ≤ η :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hη
  have hηpos : 0 < η := lt_of_lt_of_le one_pos hη1
  set T : ℂ := (-2 * (η : ℂ))⁻¹ with hTdef
  have hTn : ‖T‖ = (2 * η)⁻¹ := by
    rw [hTdef, norm_inv, norm_mul]
    simp [abs_of_pos hηpos]
  have hT1 : ‖T‖ ≤ 1 := by
    rw [hTn]; exact inv_le_one_of_one_le₀ (by linarith)
  have hTη : ‖T‖ ≤ η⁻¹ := by
    rw [hTn]
    exact inv_anti₀ hηpos (by linarith)
  set S := riccatiTrunc38 u K η with hSdef
  set S' := riccatiTruncD38 u K η with hS'def
  set ρ : ℝ → ℂ := fun x => S' x - (-2 * (η : ℂ)) * S x - star (u x) + u x * S x ^ 2 with hρdef
  -- regularity
  have hSc : Continuous S := sum_continuous38 _ T K fun k => evalJet_continuous38 u hu (p k)
  have hSp : Function.Periodic S 1 := sum_periodic38 _ T K fun k => evalJet_periodic38 u hu hper (p k)
  have hS'c : Continuous S' :=
    sum_continuous38 _ T K fun k => evalJet_continuous38 u hu (spatialD (p k))
  have hS'p : Function.Periodic S' 1 :=
    sum_periodic38 _ T K fun k => evalJet_periodic38 u hu hper (spatialD (p k))
  have huc : Continuous u := hu.continuous
  have hustarc : Continuous fun x => star (u x) := continuous_star.comp huc
  have hρc : Continuous ρ := by
    simp only [hρdef]; fun_prop
  have hρp : Function.Periodic ρ 1 := by
    intro x
    simp only [hρdef, hS'p x, hSp x, hper x]
  -- bounds
  have hρb : ∀ x, ‖ρ x‖ ≤ Cres * η⁻¹ ^ K := by
    intro x
    have h1 := riccatiResidual38 u K hηpos x
    have h2 := residual_rhs_bound38 (fun k => riccatiJetEvaluation u x (p k))
      (fun k => riccatiJetEvaluation u x (spatialD (p k))) (star (u x)) (u x) T K hM0
      (fun k hk => ha k hk x) (hb x) (by rw [norm_star]; exact hu₀ x) (hu₀ x) hT1
    have h3 : ρ x = _ := h1
    rw [h3]
    refine h2.trans ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hTη K) hCres0
  have hS1 : ∀ x, ‖S x‖ ≤ 1 := by
    intro x
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k ∈ Finset.Icc 1 K, ‖riccatiJetEvaluation u x (p k) * T ^ k‖
        ≤ ∑ k ∈ Finset.Icc 1 K, M * ‖T‖ := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk' := Finset.mem_Icc.mp hk
          rw [norm_mul, norm_pow]
          refine mul_le_mul (ha k hk'.2 x) ?_ (by positivity) hM0
          calc ‖T‖ ^ k ≤ ‖T‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg _) hT1 hk'.1
            _ = ‖T‖ := pow_one _
      _ = K * M * ‖T‖ := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; simp; ring
      _ ≤ 1 := by
          rw [hTn, ← div_eq_mul_inv, div_le_one (by positivity)]
          linarith
  set δ : ℝ := Cres * η⁻¹ ^ (K + 1) with hδdef
  have hδ0 : 0 ≤ δ := by positivity
  have hδ1 : δ ≤ 1 := by
    have hinv : η⁻¹ ^ (K + 1) ≤ η⁻¹ := by
      calc η⁻¹ ^ (K + 1) ≤ η⁻¹ ^ 1 :=
            pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hη1) (by omega)
        _ = η⁻¹ := pow_one _
    calc δ ≤ Cres * η⁻¹ := mul_le_mul_of_nonneg_left hinv hCres0
      _ ≤ 1 := by
          rw [← div_eq_mul_inv, div_le_one hηpos]; exact hηC
  have hρδ : ∀ x, ‖ρ x‖ ≤ η * δ := by
    intro x
    refine (hρb x).trans (le_of_eq ?_)
    rw [hδdef, pow_succ]
    field_simp
  obtain ⟨R, hRc, hRp, hRb, hRd⟩ := riccati_correction_exists38 hηpos huc hSc hρc hper hSp hρp
    (le_trans (norm_nonneg _) (hu₀ 0)) hu₀ hS1 hη4 hδ0 hδ1 hρδ
  refine ⟨fun x => S x + R x, hSc.add hRc, fun x => by simp only [hSp x, hRp x], fun x => ?_,
    fun x => ?_⟩
  · have := (riccatiTrunc38_hasDerivAt u hu K η x).add (hRd x)
    convert this using 1
    simp only [hρdef] at *
    push_cast
    ring
  · have : S x + R x - ∑ k ∈ Finset.Icc 1 K,
        riccatiJetEvaluation u x (p k) * (-2 * (η : ℂ))⁻¹ ^ k = R x := by
      simp [hSdef, riccatiTrunc38]
    rw [this]
    exact hRb x

/-- Same statement with the comparison sum written as `(-(2 * η) : ℂ)⁻¹ ^ k`. -/
theorem riccatiPeriodicSolution_asymptotic38' (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) (K : ℕ) :
    ∃ η₀ C : ℝ, 0 < η₀ ∧ ∀ η : ℝ, η₀ ≤ η → ∃ Γ : ℝ → ℂ, Continuous Γ ∧
      Function.Periodic Γ 1 ∧
      (∀ x, HasDerivAt Γ (-(2 * η) * Γ x + star (u x) - u x * Γ x ^ 2) x) ∧
      (∀ x, ‖Γ x - ∑ k ∈ Finset.Icc 1 K,
        riccatiJetEvaluation u x (p k) * ((-(2 * η) : ℂ))⁻¹ ^ k‖ ≤ C * η⁻¹ ^ (K + 1)) := by
  obtain ⟨η₀, C, h0, h⟩ := riccatiPeriodicSolution_asymptotic38 u hu hper K
  refine ⟨η₀, C, h0, fun η hη => ?_⟩
  obtain ⟨Γ, h1, h2, h3, h4⟩ := h η hη
  exact ⟨Γ, h1, h2, h3, by simpa only [neg_mul] using h4⟩

/-- Sup bound `≤ C / η` for the periodic solution (case `K = 0`). -/
theorem riccatiPeriodicSolution_sup_le38 (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) :
    ∃ η₀ C : ℝ, 0 < η₀ ∧ ∀ η : ℝ, η₀ ≤ η → ∃ Γ : ℝ → ℂ, Continuous Γ ∧
      Function.Periodic Γ 1 ∧
      (∀ x, HasDerivAt Γ (-(2 * η) * Γ x + star (u x) - u x * Γ x ^ 2) x) ∧
      (∀ x, ‖Γ x‖ ≤ C / η) := by
  obtain ⟨η₀, C, h0, h⟩ := riccatiPeriodicSolution_asymptotic38 u hu hper 0
  refine ⟨η₀, C, h0, fun η hη => ?_⟩
  obtain ⟨Γ, h1, h2, h3, h4⟩ := h η hη
  refine ⟨Γ, h1, h2, h3, fun x => ?_⟩
  have := h4 x
  simpa [div_eq_mul_inv] using this

/-- Small-ball uniqueness: for `η` large (depending on `b`), two continuous 1-periodic
solutions with sup-norm `≤ b` coincide. -/
theorem riccatiPeriodicSolution_unique38 (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) (b : ℝ) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, η₀ ≤ η → ∀ Γ₁ Γ₂ : ℝ → ℂ,
      Continuous Γ₁ → Continuous Γ₂ → Function.Periodic Γ₁ 1 → Function.Periodic Γ₂ 1 →
      (∀ x, HasDerivAt Γ₁ (-(2 * η) * Γ₁ x + star (u x) - u x * Γ₁ x ^ 2) x) →
      (∀ x, HasDerivAt Γ₂ (-(2 * η) * Γ₂ x + star (u x) - u x * Γ₂ x ^ 2) x) →
      (∀ x, ‖Γ₁ x‖ ≤ b) → (∀ x, ‖Γ₂ x‖ ≤ b) → Γ₁ = Γ₂ := by
  obtain ⟨Mu, hMu0, hMu⟩ := evalJet_bound38 u hu hper (MvPolynomial.X (false, 0))
  have hMu' : ∀ x, ‖u x‖ ≤ Mu := fun x => by simpa [riccatiJetFunction] using hMu x
  refine ⟨Mu * max b 0 + 1, by positivity, fun η hη Γ₁ Γ₂ hc₁ hc₂ hp₁ hp₂ hd₁ hd₂ hb₁ hb₂ => ?_⟩
  have hηpos : 0 < η := lt_of_lt_of_le (by positivity) hη
  have hlt : Mu * b < η := by
    have : Mu * b ≤ Mu * max b 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) hMu0
    linarith
  funext x
  exact riccati_unique_abstract38 hηpos (v := fun x => star (u x)) hu.continuous
    (fun x => by simpa using hper x) hMu' hb₁ hb₂ hlt hc₁ hc₂ hp₁ hp₂ hd₁ hd₂ x


end Asymptotic38


end
end NlsGge.HierarchyRiccati.Core
