import Mathlib
import NlsGge.Definitions.PilotInterfaces
import NlsGge.Sobolev.PeriodicBridge
import NlsGge.Weights.SpatialJensen
import NlsGge.Hierarchy.RiccatiLocalRemainderPaperForm38

/-! Covariance tail (paper/v2.tex C:eq:covariance, lines 751-756) and Bernstein on `F_N` (lines 765-766). -/
set_option autoImplicit false
noncomputable section
namespace NlsGge.HierarchyRiccati.Core

open NlsGge.Pilot MeasureTheory

theorem inv_pow_telescope38 (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (hx : 1 ≤ x) :
    (k : ℝ) / (x + 1) ^ (k + 1) ≤ 1 / x ^ k - 1 / (x + 1) ^ k := by
  have hx0 : 0 < x := by linarith
  have hb : 1 + (k : ℝ) * (1 / x) ≤ (1 + 1 / x) ^ k :=
    one_add_mul_le_pow (by have : 0 < 1 / x := by positivity
                           linarith) k
  have h1 : (1 + 1 / x) = (x + 1) / x := by field_simp
  rw [h1, div_pow] at hb
  have hp : 0 < (x + 1) ^ k := by positivity
  have hxk : 0 < x ^ k := by positivity
  have h2 : 1 / x ^ k - 1 / (x + 1) ^ k = ((x + 1) ^ k / x ^ k - 1) / (x + 1) ^ k := by
    field_simp
  rw [h2, le_div_iff₀ hp]
  have h3 : (k : ℝ) / (x + 1) ^ (k + 1) * (x + 1) ^ k = (k : ℝ) / (x + 1) := by
    rw [pow_succ]; field_simp
  rw [h3]
  have h4 : (k : ℝ) / (x + 1) ≤ (k : ℝ) * (1 / x) := by
    rw [← mul_one_div]
    exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hx0 (by linarith)) (by positivity)
  linarith

/-- partial sums of the tail of `n^{-(k+1)}` past `N`. -/
theorem tail_partial_sum38 (k : ℕ) (hk : 1 ≤ k) (N : ℕ) (hN : 1 ≤ N) (M : ℕ) :
    ∑ n ∈ Finset.range M, (if N < n then 1 / (n : ℝ) ^ (k + 1) else 0)
      ≤ 1 / (k : ℝ) / (N : ℝ) ^ k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have key : ∀ M : ℕ, N + 1 ≤ M →
      ∑ n ∈ Finset.range M, (if N < n then 1 / (n : ℝ) ^ (k + 1) else 0)
        ≤ (1 / (k : ℝ)) * (1 / (N : ℝ) ^ k - 1 / ((M : ℝ) - 1) ^ k) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base =>
      have : ∑ n ∈ Finset.range (N + 1), (if N < n then 1 / (n : ℝ) ^ (k + 1) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro n hn
        have : ¬ N < n := by have := Finset.mem_range.1 hn; omega
        simp [this]
      rw [this]; simp
    | succ M hM ih =>
      rw [Finset.sum_range_succ]
      have hMN : N < M := by omega
      simp only [hMN, ite_true]
      have hMr : (1 : ℝ) ≤ (M : ℝ) - 1 := by
        have : (N : ℝ) + 1 ≤ M := by exact_mod_cast hM
        have : (1 : ℝ) ≤ N := by exact_mod_cast hN
        linarith
      have t := inv_pow_telescope38 k hk ((M : ℝ) - 1) hMr
      have e : (M : ℝ) - 1 + 1 = M := by ring
      rw [e] at t
      push_cast
      have e2 : (M : ℝ) + 1 - 1 = M := by ring
      rw [e2]
      have : 1 / (M : ℝ) ^ (k + 1) ≤ 1 / (k : ℝ) * (1 / ((M : ℝ) - 1) ^ k - 1 / (M : ℝ) ^ k) := by
        rw [one_div_mul_eq_div, le_div_iff₀ hk0]
        calc 1 / (M : ℝ) ^ (k + 1) * k = (k : ℝ) / (M : ℝ) ^ (k + 1) := by ring
          _ ≤ _ := t
      nlinarith
  by_cases h : N + 1 ≤ M
  · refine (key M h).trans ?_
    have hr : (1 : ℝ) ≤ (M : ℝ) - 1 := by
      have : (N : ℝ) + 1 ≤ M := by exact_mod_cast h
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    have : 0 ≤ 1 / ((M : ℝ) - 1) ^ k := by positivity
    rw [div_eq_mul_one_div (1 / (k : ℝ))]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · have : ∑ n ∈ Finset.range M, (if N < n then 1 / (n : ℝ) ^ (k + 1) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have : ¬ N < n := by have := Finset.mem_range.1 hn; omega
      simp [this]
    rw [this]; positivity

theorem int_sum_of_nat_bound38 (H : ℕ → ℝ) (h0 : ∀ n, 0 ≤ H n) (hH0 : H 0 = 0) (T : ℝ)
    (hT : ∀ M : ℕ, ∑ n ∈ Finset.range M, H n ≤ T) :
    Summable (fun n : ℤ => H n.natAbs) ∧ ∑' n : ℤ, H n.natAbs ≤ 2 * T := by
  have hs : Summable H := summable_of_sum_range_le h0 hT
  have ht : ∑' n, H n ≤ T := Real.tsum_le_of_sum_range_le h0 hT
  have hs1 : Summable (fun n : ℕ => H (n + 1)) := (summable_nat_add_iff 1).2 hs
  have ht1 : ∑' n : ℕ, H (n + 1) ≤ T := by
    refine Real.tsum_le_of_sum_range_le (fun n => h0 _) fun M => ?_
    have := hT (M + 1)
    rw [Finset.sum_range_succ', hH0, add_zero] at this
    exact this
  have e1 : (fun n : ℕ => H ((n : ℤ)).natAbs) = H := by
    funext n; simp
  have e2 : (fun n : ℕ => H (-((n : ℤ) + 1)).natAbs) = fun n => H (n + 1) := by
    funext n
    have : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
    rw [this]
  have hs' : Summable (fun n : ℤ => H n.natAbs) :=
    Summable.of_nat_of_neg_add_one (by rw [e1]; exact hs) (by rw [e2]; exact hs1)
  refine ⟨hs', ?_⟩
  rw [tsum_of_nat_of_neg_add_one (by rw [e1]; exact hs) (by rw [e2]; exact hs1), e1, e2]
  linarith

theorem covariance_tail38 (m a b N : ℕ) (hm : 1 ≤ m) (ha : a ≤ m - 1) (hb : b ≤ m - 1)
    (c : ℝ) (hc : 0 < c) (r : ℤ → ℝ)
    (hr : ∀ n : ℤ, c * (1 + (2 * Real.pi * |(n : ℝ)|) ^ (2 * m)) ≤ r n) (hN : 1 ≤ N) :
    Summable (fun n : ℤ =>
      if (N : ℤ) < |n| then (2 * Real.pi * |(n : ℝ)|) ^ (a + b) / r n else 0) ∧
    ∑' n : ℤ, (if (N : ℤ) < |n| then (2 * Real.pi * |(n : ℝ)|) ^ (a + b) / r n else 0)
      ≤ (2 / c) * (N : ℝ) ^ ((a : ℤ) + b - 2 * m + 1) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = 2 * m - a - b - 1 := ⟨_, rfl⟩
  have hk1 : 1 ≤ k := by omega
  have hkab : a + b + (k + 1) = 2 * m := by omega
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set H : ℕ → ℝ := fun j => if N < j then 1 / (j : ℝ) ^ (k + 1) else 0 with hHdef
  have hHn : ∀ j, 0 ≤ H j := fun j => by simp only [hHdef]; split_ifs <;> positivity
  have hH0 : H 0 = 0 := by simp [hHdef]
  obtain ⟨hsum, htsum⟩ := int_sum_of_nat_bound38 H hHn hH0 (1 / (k : ℝ) / (N : ℝ) ^ k)
    (fun M => tail_partial_sum38 k hk1 N hN M)
  -- pointwise bounds
  have hpt : ∀ n : ℤ, 0 ≤ (if (N : ℤ) < |n| then (2 * Real.pi * |(n : ℝ)|) ^ (a + b) / r n else 0)
      ∧ (if (N : ℤ) < |n| then (2 * Real.pi * |(n : ℝ)|) ^ (a + b) / r n else 0)
        ≤ (1 / c) * H n.natAbs := by
    intro n
    by_cases hn : (N : ℤ) < |n|
    · have hna : N < n.natAbs := by rw [Int.abs_eq_natAbs] at hn; omega
      have hx : (n.natAbs : ℝ) = |(n : ℝ)| := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
        rw [← hx]; exact_mod_cast (by omega : 1 ≤ n.natAbs)
      have hxpos : 0 < 2 * Real.pi * |(n : ℝ)| := by positivity
      have hpi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
      have hge : |(n : ℝ)| ≤ 2 * Real.pi * |(n : ℝ)| := by nlinarith
      set x := 2 * Real.pi * |(n : ℝ)| with hxdef
      have hrn : c * x ^ (2 * m) ≤ r n := by
        have := hr n
        have : 0 ≤ c * 1 := by positivity
        nlinarith [hr n, pow_nonneg hxpos.le (2 * m)]
      have hrpos : 0 < r n := lt_of_lt_of_le (by positivity) hrn
      simp only [hn, ite_true, hHdef, hna]
      refine ⟨by positivity, ?_⟩
      have hxm : x ^ (2 * m) = x ^ (a + b) * x ^ (k + 1) := by rw [← hkab, pow_add]
      calc x ^ (a + b) / r n ≤ x ^ (a + b) / (c * (x ^ (a + b) * x ^ (k + 1))) := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            rw [← hxm]; exact hrn
        _ = 1 / (c * x ^ (k + 1)) := by
            field_simp
        _ ≤ 1 / c * (1 / (n.natAbs : ℝ) ^ (k + 1)) := by
            rw [one_div_mul_one_div, hx]
            apply one_div_le_one_div_of_le (by positivity)
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hge _) hc.le
    · have hna : ¬ N < n.natAbs := by rw [Int.abs_eq_natAbs] at hn; omega
      simp only [hn, hHdef, hna, ite_false, mul_zero]
      exact ⟨le_refl _, le_refl _⟩
  refine ⟨?_, ?_⟩
  · exact Summable.of_nonneg_of_le (fun n => (hpt n).1) (fun n => (hpt n).2)
      (hsum.mul_left (1 / c))
  · have h1 := Summable.tsum_le_tsum (fun n => (hpt n).2)
      (Summable.of_nonneg_of_le (fun n => (hpt n).1) (fun n => (hpt n).2) (hsum.mul_left (1 / c)))
      (hsum.mul_left (1 / c))
    rw [tsum_mul_left] at h1
    refine h1.trans ((mul_le_mul_of_nonneg_left htsum (by positivity)).trans ?_)
    have hexp : ((a : ℤ) + b - 2 * m + 1) = -(k : ℤ) := by omega
    rw [hexp, zpow_neg, zpow_natCast]
    have : 1 / c * (2 * (1 / (k : ℝ) / (N : ℝ) ^ k)) = (2 / c) * ((N : ℝ) ^ k)⁻¹ * (1 / k) := by
      field_simp
    rw [this]
    have hinv : 0 ≤ (2 / c) * ((N : ℝ) ^ k)⁻¹ := by positivity
    have : (1 : ℝ) / k ≤ 1 := by
      rw [div_le_one hk0]; exact_mod_cast hk1
    nlinarith

/-- Instance: `a_{m,n} = W_m(2πn)` with `β_0, β_m > 0` and `β_j ≥ 0`
satisfies `a_{m,n} ≥ c (1 + (2π|n|)^{2m})` with `c = min β_0 β_m`. -/
theorem finiteHierarchyRate38_lower (M : ℕ) (β : ℕ → ℝ) (hβ : ∀ j ≤ M, 0 ≤ β j)
    (hM1 : 1 ≤ M) (n : ℤ) :
    min (β 0) (β M) * (1 + (2 * Real.pi * |(n : ℝ)|) ^ (2 * M)) ≤
      finiteHierarchyRate38 M β n := by
  have hM1 : 1 ≤ M := hM1
  set x := 2 * Real.pi * |(n : ℝ)| with hx
  have hx0 : 0 ≤ x := by positivity
  have hterm : ∀ j, (2 * Real.pi * (n : ℝ)) ^ (2 * j) = x ^ (2 * j) :=
    fun j => (two_pi_abs_pow_even38 n j).symm
  have hW : finiteHierarchyRate38 M β n = ∑ j ∈ Finset.range (M + 1), β j * x ^ (2 * j) := by
    simp only [finiteHierarchyRate38, finiteHierarchyW38, hterm]
  rw [hW]
  have hne : (0 : ℕ) ≠ M := by omega
  have hsub : ({0, M} : Finset ℕ) ⊆ Finset.range (M + 1) := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl <;> simp [Finset.mem_range]
  have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun j => β j * x ^ (2 * j))
    (fun j hj _ => mul_nonneg (hβ j (by simpa [Finset.mem_range, Nat.lt_succ_iff] using hj))
      (pow_nonneg hx0 _))
  rw [Finset.sum_pair hne] at h1
  simp only [mul_zero, pow_zero, mul_one] at h1
  have hm1 : min (β 0) (β M) ≤ β 0 := min_le_left _ _
  have hm2 : min (β 0) (β M) ≤ β M := min_le_right _ _
  have : 0 ≤ x ^ (2 * M) := pow_nonneg hx0 _
  nlinarith [mul_le_mul_of_nonneg_right hm2 this]

theorem finiteHierarchyRate38_exists_c (M : ℕ) (β : ℕ → ℝ) (hβ : ∀ j ≤ M, 0 ≤ β j)
    (hM1 : 1 ≤ M) (h0 : 0 < β 0) (hM : 0 < β M) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℤ,
      c * (1 + (2 * Real.pi * |(n : ℝ)|) ^ (2 * M)) ≤ finiteHierarchyRate38 M β n :=
  ⟨min (β 0) (β M), lt_min h0 hM, finiteHierarchyRate38_lower M β hβ hM1⟩

/-- Covariance tail for the actual hierarchy rates `a_{m,n}` (source `C:eq:covariance`). -/
theorem covariance_tail_finiteHierarchy38 (m a b N : ℕ) (hm : 1 ≤ m) (ha : a ≤ m - 1)
    (hb : b ≤ m - 1) (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 ≤ β j) (h0 : 0 < β 0) (hM : 0 < β m)
    (hN : 1 ≤ N) :
    Summable (fun n : ℤ =>
      if (N : ℤ) < |n| then
        (2 * Real.pi * |(n : ℝ)|) ^ (a + b) / finiteHierarchyRate38 m β n else 0) ∧
    ∑' n : ℤ, (if (N : ℤ) < |n| then
        (2 * Real.pi * |(n : ℝ)|) ^ (a + b) / finiteHierarchyRate38 m β n else 0)
      ≤ (2 / min (β 0) (β m)) * (N : ℝ) ^ ((a : ℤ) + b - 2 * m + 1) :=
  covariance_tail38 m a b N hm ha hb _ (lt_min h0 hM) _
    (finiteHierarchyRate38_lower m β hβ hm) hN

/-! ### Bernstein inequalities on `F_N` -/

theorem iterate_derivativePlane38 (N : ℕ) (z : FourierPlane N) (a : ℕ) (i : Fin (2 * N + 1)) :
    ((derivativePlane N)^[a] z) i = z i * (2 * Real.pi * Complex.I * (modeIndex N i : ℂ)) ^ a := by
  induction a generalizing z with
  | zero => simp
  | succ a ih =>
    rw [Function.iterate_succ_apply, ih]
    simp only [derivativePlane]
    ring

theorem iterate_derivativePlane_norm_le38 (N : ℕ) (z : FourierPlane N) (a : ℕ)
    (i : Fin (2 * N + 1)) :
    ‖((derivativePlane N)^[a] z) i‖ ≤ (2 * Real.pi * N) ^ a * ‖z i‖ := by
  rw [iterate_derivativePlane38, norm_mul, norm_pow]
  have hb := modeIndex_bounds N i
  have hk : ‖(2 * Real.pi * Complex.I * (modeIndex N i : ℂ))‖ ≤ 2 * Real.pi * N := by
    simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_intCast, Complex.norm_ofNat, mul_one, abs_of_pos Real.pi_pos]
    have : |(modeIndex N i : ℝ)| ≤ N := by
      rw [abs_le]; constructor <;> [skip; skip] <;> exact_mod_cast (by omega)
    nlinarith [Real.pi_pos]
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hk a) (norm_nonneg _)

theorem planeReal_integral_norm_sq38 (N : ℕ) (w : FourierPlane N) :
    ∫ x in (0 : ℝ)..1, ‖planeReal N w x‖ ^ 2 = ∑ i : Fin (2 * N + 1), ‖w i‖ ^ 2 := by
  have h := AddCircle.intervalIntegral_preimage (1 : ℝ) 0
    (fun x : PhysicalCircle => ‖planeField N w x‖ ^ 2)
  rw [zero_add] at h
  have h2 := AddCircle.integral_haarAddCircle (T := (1 : ℝ))
    (f := fun x : PhysicalCircle => ‖planeField N w x‖ ^ 2)
  rw [← NlsGge.Weights.plane_mass_integral_eq_sum N w]
  unfold spatialMeasure
  rw [h2, inv_one, one_smul]
  exact h

theorem planeReal_sup_le38 (N : ℕ) (w : FourierPlane N) (x : ℝ) :
    ‖planeReal N w x‖ ≤ Real.sqrt (2 * N + 1) * Real.sqrt (∑ i, ‖w i‖ ^ 2) := by
  have h1 : ‖planeReal N w x‖ ≤ ∑ i : Fin (2 * N + 1), ‖w i‖ := by
    unfold planeReal planeField
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul]
    have : ‖fourier (modeIndex N i) (x : PhysicalCircle)‖ = 1 := by
      simp only [fourier_coe_apply]
      have e : (2 * (Real.pi : ℂ) * Complex.I * (modeIndex N i : ℂ) * (x : ℂ)) =
          ((2 * Real.pi * modeIndex N i * x : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      simp only [Complex.ofReal_one, div_one]
      rw [show (2 * (Real.pi : ℂ) * Complex.I * (modeIndex N i : ℂ) * (x : ℂ)) = _ from e]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [this, mul_one]
  refine h1.trans ?_
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun i => ‖w i‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at this
  rw [← Real.sqrt_mul (by positivity)]
  apply Real.le_sqrt_of_sq_le
  have e : ((2 * N + 1 : ℕ) : ℝ) = 2 * N + 1 := by push_cast; ring
  rw [e] at this
  exact this

/-- `‖v^(a)‖²_{L²(0,1)} ≤ (2πN)^{2a} ‖v‖²_{L²(0,1)}` for `v = planeReal N z`. -/
theorem bernstein_L2_sq38 (N : ℕ) (z : FourierPlane N) (a : ℕ) :
    ∫ x in (0 : ℝ)..1, ‖iteratedDeriv a (planeReal N z) x‖ ^ 2 ≤
      ((2 * Real.pi * N) ^ a) ^ 2 * ∫ x in (0 : ℝ)..1, ‖planeReal N z x‖ ^ 2 := by
  rw [iteratedDeriv_planeReal]
  simp only [planeReal_integral_norm_sq38]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have := iterate_derivativePlane_norm_le38 N z a i
  calc ‖((derivativePlane N)^[a] z) i‖ ^ 2 ≤ ((2 * Real.pi * N) ^ a * ‖z i‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) this 2
    _ = _ := by ring

/-- L² form: `‖v^(a)‖_{L²(0,1)} ≤ (2πN)^a ‖v‖_{L²(0,1)}`. -/
theorem bernstein_L2_38 (N : ℕ) (z : FourierPlane N) (a : ℕ) :
    Real.sqrt (∫ x in (0 : ℝ)..1, ‖iteratedDeriv a (planeReal N z) x‖ ^ 2) ≤
      (2 * Real.pi * N) ^ a * Real.sqrt (∫ x in (0 : ℝ)..1, ‖planeReal N z x‖ ^ 2) := by
  have h := bernstein_L2_sq38 N z a
  have hp : 0 ≤ (2 * Real.pi * N) ^ a := by positivity
  calc _ ≤ Real.sqrt (((2 * Real.pi * N) ^ a) ^ 2 * ∫ x in (0 : ℝ)..1, ‖planeReal N z x‖ ^ 2) :=
        Real.sqrt_le_sqrt h
    _ = _ := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hp]

/-- Sup form: `sup_x |v^(a)(x)| ≤ (2πN)^a √(2N+1) ‖v‖_{L²(0,1)}`. -/
theorem bernstein_sup_38 (N : ℕ) (z : FourierPlane N) (a : ℕ) (x : ℝ) :
    ‖iteratedDeriv a (planeReal N z) x‖ ≤
      (2 * Real.pi * N) ^ a * Real.sqrt (2 * N + 1) *
        Real.sqrt (∫ y in (0 : ℝ)..1, ‖planeReal N z y‖ ^ 2) := by
  rw [iteratedDeriv_planeReal]
  refine (planeReal_sup_le38 N _ x).trans ?_
  have hS : Real.sqrt (∑ i, ‖((derivativePlane N)^[a] z) i‖ ^ 2) ≤
      (2 * Real.pi * N) ^ a * Real.sqrt (∑ i, ‖z i‖ ^ 2) := by
    have hp : 0 ≤ (2 * Real.pi * N) ^ a := by positivity
    rw [← Real.sqrt_sq hp, ← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    calc _ ≤ ((2 * Real.pi * N) ^ a * ‖z i‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (iterate_derivativePlane_norm_le38 N z a i) 2
      _ = _ := by ring
  rw [planeReal_integral_norm_sq38]
  calc Real.sqrt (2 * N + 1) * Real.sqrt (∑ i, ‖((derivativePlane N)^[a] z) i‖ ^ 2)
      ≤ Real.sqrt (2 * N + 1) * ((2 * Real.pi * N) ^ a * Real.sqrt (∑ i, ‖z i‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hS (Real.sqrt_nonneg _)
    _ = _ := by ring

end NlsGge.HierarchyRiccati.Core
