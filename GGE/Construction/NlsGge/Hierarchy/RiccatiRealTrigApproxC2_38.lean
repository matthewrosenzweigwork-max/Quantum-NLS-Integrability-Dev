import NlsGge.Hierarchy.RiccatiPeriodicFourierDerivativeCoefficientRecovery29Second
import NlsGge.Hierarchy.RiccatiPeriodicIteratedDerivClosurePrerequisite
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open NlsGge.Pilot
open MeasureTheory
open scoped ContDiff

/-- Real trigonometric polynomials of period one, with frequencies `0,…,N`. -/
def IsRealTrigPoly38 (P : ℝ → ℝ) : Prop :=
  ∃ N : ℕ, ∃ a b : ℕ → ℝ, ∀ x,
    P x = ∑ k ∈ Finset.range (N + 1),
      (a k * Real.cos (2 * Real.pi * k * x) + b k * Real.sin (2 * Real.pi * k * x))

theorem IsRealTrigPoly38.contDiff {P : ℝ → ℝ} (h : IsRealTrigPoly38 P) :
    ContDiff ℝ ∞ P := by
  obtain ⟨N, a, b, hP⟩ := h
  have : P = fun x => ∑ k ∈ Finset.range (N + 1),
      (a k * Real.cos (2 * Real.pi * k * x) + b k * Real.sin (2 * Real.pi * k * x)) :=
    funext hP
  rw [this]
  refine ContDiff.sum fun k _ => ?_
  fun_prop

theorem IsRealTrigPoly38.periodic {P : ℝ → ℝ} (h : IsRealTrigPoly38 P) :
    Function.Periodic P 1 := by
  obtain ⟨N, a, b, hP⟩ := h
  intro x
  rw [hP, hP]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : 2 * Real.pi * (k : ℝ) * (x + 1) = 2 * Real.pi * k * x + (k : ℕ) * (2 * Real.pi) := by
    ring
  rw [h1, Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi]

/-- Symmetric partial Fourier sum with coefficient sequence `d`. -/
def trigSum38 (d : ℤ → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) N, fourierRealTerm n (d n) x

theorem fourierRealTerm_eq_exp38 (n : ℤ) (z : ℂ) (x : ℝ) :
    fourierRealTerm n z x = z * Complex.exp (((2 * Real.pi * n * x : ℝ) : ℂ) * Complex.I) := by
  unfold fourierRealTerm
  rw [fourier_coe_apply]
  congr 2
  push_cast
  ring

theorem fourierRealTerm_re38 (n : ℤ) (z : ℂ) (x : ℝ) :
    (fourierRealTerm n z x).re =
      z.re * Real.cos (2 * Real.pi * n * x) - z.im * Real.sin (2 * Real.pi * n * x) := by
  rw [fourierRealTerm_eq_exp38, Complex.mul_re, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]

theorem sum_Icc_symm38 (g : ℤ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Icc (-(N : ℤ)) N, g n =
      g 0 + ∑ k ∈ Finset.range N, (g ((k : ℤ) + 1) + g (-((k : ℤ) + 1))) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hset : Finset.Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ) =
        insert (-((N : ℤ) + 1)) (insert ((N : ℤ) + 1) (Finset.Icc (-(N : ℤ)) N)) := by
      ext m
      simp only [Finset.mem_Icc, Finset.mem_insert]
      push_cast
      omega
    rw [hset, Finset.sum_insert, Finset.sum_insert, ih, Finset.sum_range_succ]
    · ring
    · simp
    · simp only [Finset.mem_insert, Finset.mem_Icc]
      omega

theorem isRealTrigPoly_re_trigSum38 (d : ℤ → ℂ) (N : ℕ) :
    IsRealTrigPoly38 (fun x => (trigSum38 d N x).re) := by
  refine ⟨N, fun k => (d k).re + (if k = 0 then 0 else (d (-(k : ℤ))).re),
    fun k => -(d k).im + (if k = 0 then 0 else (d (-(k : ℤ))).im), ?_⟩
  intro x
  beta_reduce
  unfold trigSum38
  rw [Complex.re_sum]
  simp_rw [fourierRealTerm_re38]
  rw [sum_Icc_symm38 (fun n : ℤ => (d n).re * Real.cos (2 * Real.pi * n * x) -
    (d n).im * Real.sin (2 * Real.pi * n * x)) N, Finset.sum_range_succ' _ N]
  simp only [Int.cast_zero, mul_zero, Real.cos_zero, Real.sin_zero, mul_one, sub_zero,
    Nat.cast_zero, ite_true, add_zero, zero_mul, Nat.cast_add, Nat.cast_one]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Int.cast_add, Int.cast_natCast, Int.cast_one, Int.cast_neg]
  have h1 : (k + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero k
  simp only [h1, ite_false]
  have e1 : 2 * Real.pi * -((k : ℝ) + 1) * x = -(2 * Real.pi * ((k : ℝ) + 1) * x) := by ring
  rw [e1, Real.cos_neg, Real.sin_neg]
  ring

theorem hasDerivAt_trigSum38 (d : ℤ → ℂ) (N : ℕ) (x : ℝ) :
    HasDerivAt (trigSum38 d N)
      (trigSum38 (fun n => d n * fourierMultiplier n) N x) x := by
  unfold trigSum38
  exact HasDerivAt.fun_sum fun n _ => hasDerivAt_fourierRealTerm n (d n) x

theorem hasDerivAt_re_trigSum38 (d : ℤ → ℂ) (N : ℕ) (x : ℝ) :
    HasDerivAt (fun y => (trigSum38 d N y).re)
      (trigSum38 (fun n => d n * fourierMultiplier n) N x).re x := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_trigSum38 d N x)
  exact h

theorem deriv_re_trigSum38 (d : ℤ → ℂ) (N : ℕ) :
    deriv (fun y => (trigSum38 d N y).re) =
      fun x => (trigSum38 (fun n => d n * fourierMultiplier n) N x).re :=
  funext fun x => (hasDerivAt_re_trigSum38 d N x).deriv

theorem iteratedDeriv_two_re_trigSum38 (d : ℤ → ℂ) (N : ℕ) :
    iteratedDeriv 2 (fun y => (trigSum38 d N y).re) =
      fun x => (trigSum38 (fun n => d n * fourierMultiplier n * fourierMultiplier n) N x).re := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_re_trigSum38, deriv_re_trigSum38]

theorem unitCircle_liftIoc_coe38 (u : ℝ → ℂ) (hper : Function.Periodic u 1) (x : ℝ) :
    AddCircle.liftIoc (1 : ℝ) 0 u (x : AddCircle (1 : ℝ)) = u x := by
  have hmem := toIocMod_mem_Ioc (one_pos : (0 : ℝ) < 1) 0 x
  have h1 : ((toIocMod (one_pos : (0 : ℝ) < 1) 0 x : ℝ) : AddCircle (1 : ℝ)) =
      (x : AddCircle (1 : ℝ)) := by
    rw [← self_sub_toIocDiv_zsmul (one_pos : (0 : ℝ) < 1) 0 x]
    simp
  rw [← h1, AddCircle.liftIoc_coe_apply (by simpa using hmem)]
  rw [← self_sub_toIocDiv_zsmul (one_pos : (0 : ℝ) < 1) 0 x]
  simpa using hper.sub_zsmul_eq (toIocDiv (one_pos : (0 : ℝ) < 1) 0 x) 

theorem eventually_uniform_partial_sum38 (u : ℝ → ℂ) (hu : Continuous u)
    (hper : Function.Periodic u 1) (d : ℤ → ℂ)
    (hd : ∀ n, d n = fourierCoeffOn (by norm_num : (0 : ℝ) < 1) u n)
    (hsum : Summable d) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ x : ℝ, ‖trigSum38 d N x - u x‖ ≤ ε := by
  obtain rfl : d = fun n => fourierCoeffOn (by norm_num : (0 : ℝ) < 1) u n := funext hd
  let F : C(AddCircle (1 : ℝ), ℂ) :=
    ⟨AddCircle.liftIoc 1 0 u,
      AddCircle.liftIoc_continuous (by simpa using (hper 0).symm) hu.continuousOn⟩
  have hF : ∀ x : ℝ, F (x : AddCircle (1 : ℝ)) = u x := fun x =>
    unitCircle_liftIoc_coe38 u hper x
  have hcoef : ∀ n : ℤ, fourierCoeff F n =
      fourierCoeffOn (by norm_num : (0 : ℝ) < 1) u n := by
    intro n
    change fourierCoeff (AddCircle.liftIoc (1 : ℝ) 0 u) n = _
    have h := fourierCoeff_liftIoc_eq (T := (1 : ℝ)) (a := (0 : ℝ)) u n
    simpa only [zero_add] using h
  have hsumF : Summable (fourierCoeff F) := by
    have : fourierCoeff F = fun n : ℤ => fourierCoeffOn (by norm_num : (0 : ℝ) < 1) u n :=
      funext hcoef
    rw [this]; exact hsum
  have hHS := hasSum_fourier_series_of_summable hsumF
  have hmono : Monotone (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ)) := by
    intro a b hab m hm
    simp only [Finset.mem_Icc] at hm ⊢
    omega
  have hcof : Filter.Tendsto (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ)) Filter.atTop
      Filter.atTop := by
    refine Filter.tendsto_atTop_finset_of_monotone hmono fun m => ⟨m.natAbs, ?_⟩
    simp only [Finset.mem_Icc]
    omega
  have htend := hHS.comp hcof
  have hev := (Metric.tendsto_nhds.1 htend) ε hε
  filter_upwards [hev] with N hN x
  rw [dist_eq_norm] at hN
  let S : C(AddCircle (1 : ℝ), ℂ) :=
    ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), fourierCoeff F n • fourier n
  have hle := ContinuousMap.norm_coe_le_norm (S - F) (x : AddCircle (1 : ℝ))
  have hval : (S - F) (x : AddCircle (1 : ℝ)) =
      trigSum38 (fun n => fourierCoeffOn (by norm_num : (0 : ℝ) < 1) u n) N x - u x := by
    simp only [S]
    rw [ContinuousMap.sub_apply, ContinuousMap.coe_sum, Finset.sum_apply, hF]
    unfold trigSum38 fourierRealTerm
    simp only [hcoef, ContinuousMap.smul_apply, smul_eq_mul]
  rw [hval] at hle
  exact hle.trans hN.le

theorem norm_fourierCoeffOn_le38 (g : ℝ → ℂ) (M : ℝ) (hM : ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖g x‖ ≤ M)
    (n : ℤ) : ‖fourierCoeffOn (by norm_num : (0 : ℝ) < 1) g n‖ ≤ M := by
  rw [fourierCoeffOn_eq_integral]
  simp only [sub_zero, div_one, one_smul]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := M)
    (f := fun x : ℝ => fourier (-n) (x : AddCircle (1 : ℝ)) • g x) (by
      intro x hx
      rw [Set.uIoc_of_le zero_le_one] at hx
      have hn1 : ‖fourier (-n) (x : AddCircle (1 : ℝ))‖ = 1 := by
        rw [fourier_apply]; exact Circle.norm_coe _
      rw [norm_smul, hn1, one_mul]
      exact hM x ⟨hx.1.le, hx.2⟩)
  simpa using h

theorem summable_multiplier_coeff38 (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) (k : ℕ) (hk : k ≤ 2) :
    Summable (fun n : ℤ => fourierMultiplier n ^ k *
      fourierCoeffOn (by norm_num : (0 : ℝ) < 1) u n) := by
  have hw : ContDiff ℝ ∞ (iteratedDeriv 4 u) := by
    rw [iteratedDeriv_eq_iterate]
    exact ContDiff.iterate_deriv 4 hu
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := iteratedDeriv 4 u) (s := Set.Icc (0 : ℝ) 1) hw.continuous.continuousOn
  have hcoeff4 : ∀ n : ℤ, ‖fourierMultiplier n ^ 4 *
      fourierCoeffOn (by norm_num : (0 : ℝ) < 1) u n‖ ≤ M := by
    intro n
    rw [← riccatiFourierCoeffOn_iteratedDeriv_periodOneRecovery29 u hu hper 4 n]
    exact norm_fourierCoeffOn_le38 _ M hM n
  have hsumM : Summable (fun n : ℤ => M * (1 / (n : ℝ) ^ 2)) :=
    (Real.summable_one_div_int_pow.2 (by norm_num : 1 < 2)).mul_left M
  refine Summable.of_norm_bounded_eventually hsumM ?_
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with n hn
  set c := fourierCoeffOn (by norm_num : (0 : ℝ) < 1) u n with hc
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
    have h2 : ((1 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast this
    simpa using h2
  set a : ℝ := ‖fourierMultiplier n‖ with ha
  have ha' : a = 2 * Real.pi * |(n : ℝ)| := norm_fourierMultiplier n
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have ha1 : (1 : ℝ) ≤ a := by rw [ha']; nlinarith
  have han : |(n : ℝ)| ≤ a := by rw [ha']; nlinarith [abs_nonneg (n : ℝ)]
  have hn2 : (n : ℝ) ^ 2 ≤ a ^ 2 := by
    rw [← sq_abs (n : ℝ)]
    exact pow_le_pow_left₀ (abs_nonneg _) han 2
  have hnpos : (0 : ℝ) < (n : ℝ) ^ 2 := by
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    positivity
  have h4 : a ^ 4 * ‖c‖ ≤ M := by
    have := hcoeff4 n
    rwa [norm_mul, norm_pow] at this
  have hexp : a ^ 2 ≤ a ^ (4 - k) := pow_le_pow_right₀ ha1 (by omega)
  have hsplit : a ^ k * ‖c‖ * a ^ (4 - k) = a ^ 4 * ‖c‖ := by
    rw [mul_right_comm, ← pow_add, Nat.add_sub_cancel' (by omega)]
  have hkey : (a ^ k * ‖c‖) * (n : ℝ) ^ 2 ≤ M := by
    calc (a ^ k * ‖c‖) * (n : ℝ) ^ 2 ≤ (a ^ k * ‖c‖) * a ^ (4 - k) :=
          mul_le_mul_of_nonneg_left (hn2.trans hexp) (by positivity)
      _ = a ^ 4 * ‖c‖ := hsplit
      _ ≤ M := h4
  rw [norm_mul, norm_pow]
  change a ^ k * ‖c‖ ≤ _
  rw [mul_one_div, le_div_iff₀ hnpos]
  exact hkey

private theorem iteratedDeriv_ofRealTrig38 (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (k : ℕ) :
    iteratedDeriv k (fun x => (g x : ℂ)) = fun x => ((iteratedDeriv k g x : ℝ) : ℂ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hd : Differentiable ℝ (iteratedDeriv k g) := by
      rw [iteratedDeriv_eq_iterate]
      exact (ContDiff.iterate_deriv k hg).differentiable (by simp)
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
    funext x
    exact ((hd x).hasDerivAt.ofReal_comp).deriv

/-- Uniform `C²` approximation of a smooth period-one real function by real
trigonometric polynomials (symmetric partial Fourier sums). -/
theorem exists_realTrigPoly_C2_close38 (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hper : Function.Periodic f 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ P : ℝ → ℝ, IsRealTrigPoly38 P ∧ ∀ x,
      |P x - f x| ≤ δ ∧ |deriv P x - deriv f x| ≤ δ ∧
        |iteratedDeriv 2 P x - iteratedDeriv 2 f x| ≤ δ := by
  set fC : ℝ → ℂ := fun x => (f x : ℂ) with hfC
  have hfCd : ContDiff ℝ ∞ fC := Complex.ofRealCLM.contDiff.comp hf
  have hCper : Function.Periodic fC 1 := fun x => by simp [fC, hper x]
  set c : ℤ → ℂ := fun n => fourierCoeffOn (by norm_num : (0 : ℝ) < 1) fC n with hc
  have hk : ∀ k : ℕ, k ≤ 2 → ∀ᶠ N : ℕ in Filter.atTop, ∀ x : ℝ,
      ‖trigSum38 (fun n => fourierMultiplier n ^ k * c n) N x - iteratedDeriv k fC x‖ ≤ δ := by
    intro k hk2
    have hcont : ContDiff ℝ ∞ (iteratedDeriv k fC) := by
      rw [iteratedDeriv_eq_iterate]
      exact ContDiff.iterate_deriv k hfCd
    exact eventually_uniform_partial_sum38 (iteratedDeriv k fC) hcont.continuous
      (periodic_iteratedDeriv_of_contDiff fC hfCd hCper k)
      (fun n => fourierMultiplier n ^ k * c n)
      (fun n => (riccatiFourierCoeffOn_iteratedDeriv_periodOneRecovery29 fC hfCd hCper k n).symm)
      (summable_multiplier_coeff38 fC hfCd hCper k hk2) δ hδ
  obtain ⟨N, h0, h1, h2⟩ := ((hk 0 (by norm_num)).and
    ((hk 1 (by norm_num)).and (hk 2 le_rfl))).exists
  refine ⟨fun x => (trigSum38 c N x).re, isRealTrigPoly_re_trigSum38 c N, fun x => ?_⟩
  have e1 : (fun n => c n * fourierMultiplier n) = fun n => fourierMultiplier n ^ 1 * c n := by
    funext n; ring
  have e2 : (fun n => c n * fourierMultiplier n * fourierMultiplier n) =
      fun n => fourierMultiplier n ^ 2 * c n := by
    funext n; ring
  have hI : ∀ k : ℕ, iteratedDeriv k fC = fun x => ((iteratedDeriv k f x : ℝ) : ℂ) :=
    iteratedDeriv_ofRealTrig38 f hf
  have key : ∀ (S : ℂ) (k : ℕ) (r : ℝ), ‖S - iteratedDeriv k fC x‖ ≤ δ →
      iteratedDeriv k f x = r → |S.re - r| ≤ δ := by
    intro S k r hS hr
    have : S.re - r = (S - iteratedDeriv k fC x).re := by
      rw [hI k, Complex.sub_re, Complex.ofReal_re, hr]
    rw [this]
    exact (Complex.abs_re_le_norm _).trans hS
  refine ⟨?_, ?_, ?_⟩
  · refine key _ 0 (f x) ?_ (by simp)
    simpa only [pow_zero, one_mul] using h0 x
  · rw [deriv_re_trigSum38, e1]
    refine key _ 1 (deriv f x) ?_ (by simp)
    exact h1 x
  · rw [iteratedDeriv_two_re_trigSum38, e2]
    exact key _ 2 _ (h2 x) rfl

end NlsGge.HierarchyRiccati.Core

end
