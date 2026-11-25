import NlsGge.Hierarchy.ALExteriorBranch38
import NlsGge.Analysis.EvenLogDisk38
import NlsGge.Hierarchy.ALLaurent38
import NlsGge.Hierarchy.ALBoundaryKappa38

/-! Batch 38: Laurent expansion and Fourier identities for the AL exterior branch
(paper/v2.tex `D:eq:pAL`, `D:prop:ALmoments`). -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.AblowitzLadik

open Filter Topology Metric Set MeasureTheory
open NlsGge.Analysis

/-! ### Orthogonality -/

theorem integral_cos_int38 (j : ℤ) (hj : j ≠ 0) :
    ∫ θ in (0:ℝ)..(2 * Real.pi), Real.cos (2 * j * θ) = 0 := by
  have hc : (2 * (j:ℝ)) ≠ 0 := by
    have : (j:ℝ) ≠ 0 := by exact_mod_cast hj
    positivity
  have := intervalIntegral.integral_comp_mul_left (a := 0) (b := 2 * Real.pi)
    (fun x => Real.cos x) hc
  simp only [mul_zero] at this
  rw [this, integral_cos]
  have : Real.sin (2 * j * (2 * Real.pi)) = 0 := by
    rw [show 2 * (j:ℝ) * (2 * Real.pi) = ((4 * j : ℤ) : ℝ) * Real.pi by push_cast; ring]
    exact Real.sin_int_mul_pi _
  simp [this]

theorem integral_sin_int38 (j : ℤ) :
    ∫ θ in (0:ℝ)..(2 * Real.pi), Real.sin (2 * j * θ) = 0 := by
  by_cases hj : j = 0
  · simp [hj]
  have hc : (2 * (j:ℝ)) ≠ 0 := by
    have : (j:ℝ) ≠ 0 := by exact_mod_cast hj
    positivity
  have := intervalIntegral.integral_comp_mul_left (a := 0) (b := 2 * Real.pi)
    (fun x => Real.sin x) hc
  simp only [mul_zero] at this
  rw [this, integral_sin]
  have : Real.cos (2 * j * (2 * Real.pi)) = 1 := by
    rw [show 2 * (j:ℝ) * (2 * Real.pi) = ((2 * j : ℤ) : ℝ) * (2 * Real.pi) by push_cast; ring]
    exact Real.cos_int_mul_two_pi _
  simp [this]

theorem integral_cos_mul_cos38 (n k : ℕ) :
    ∫ θ in (0:ℝ)..(2 * Real.pi), Real.cos (2 * n * θ) * Real.cos (2 * k * θ) =
      if n = k then (if n = 0 then 2 * Real.pi else Real.pi) else 0 := by
  have e : ∀ θ : ℝ, Real.cos (2 * n * θ) * Real.cos (2 * k * θ) =
      (Real.cos (2 * ((n:ℤ) - k : ℤ) * θ) + Real.cos (2 * ((n:ℤ) + k : ℤ) * θ)) / 2 := by
    intro θ
    push_cast
    rw [show 2 * ((n:ℝ) - k) * θ = 2 * n * θ - 2 * k * θ by ring,
      show 2 * ((n:ℝ) + k) * θ = 2 * n * θ + 2 * k * θ by ring, Real.cos_sub, Real.cos_add]
    ring
  simp_rw [e]
  have hi : ∀ j : ℤ, IntervalIntegrable (fun θ : ℝ => Real.cos (2 * j * θ)) volume 0 (2 * Real.pi) :=
    fun j => (by fun_prop : Continuous fun θ : ℝ => Real.cos (2 * j * θ)).intervalIntegrable _ _
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add (hi _) (hi _)]
  by_cases hnk : n = k
  · subst hnk
    have h1 : ∫ θ in (0:ℝ)..(2 * Real.pi), Real.cos (2 * (((n:ℤ) - n : ℤ) : ℝ) * θ) =
        2 * Real.pi := by simp
    by_cases h0 : n = 0
    · subst h0; simp
    · rw [h1, integral_cos_int38 ((n:ℤ) + n) (by omega)]
      simp [h0]
  · rw [integral_cos_int38 _ (by omega)]
    rcases Nat.eq_zero_or_pos (n + k) with h | h
    · omega
    · rw [integral_cos_int38 _ (by omega)]; simp [hnk]

theorem integral_sin_mul_cos38 (n k : ℕ) :
    ∫ θ in (0:ℝ)..(2 * Real.pi), Real.sin (2 * n * θ) * Real.cos (2 * k * θ) = 0 := by
  have e : ∀ θ : ℝ, Real.sin (2 * n * θ) * Real.cos (2 * k * θ) =
      (Real.sin (2 * ((n:ℤ) + k : ℤ) * θ) + Real.sin (2 * ((n:ℤ) - k : ℤ) * θ)) / 2 := by
    intro θ
    push_cast
    rw [show 2 * ((n:ℝ) - k) * θ = 2 * n * θ - 2 * k * θ by ring,
      show 2 * ((n:ℝ) + k) * θ = 2 * n * θ + 2 * k * θ by ring, Real.sin_sub, Real.sin_add]
    ring
  simp_rw [e]
  have hi : ∀ j : ℤ, IntervalIntegrable (fun θ : ℝ => Real.sin (2 * j * θ)) volume 0 (2 * Real.pi) :=
    fun j => (by fun_prop : Continuous fun θ : ℝ => Real.sin (2 * j * θ)).intervalIntegrable _ _
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add (hi _) (hi _),
    integral_sin_int38, integral_sin_int38]
  simp


/-! ### Fourier coefficients of an even analytic function on a circle -/

theorem re_term38 (c : ℂ) (r : ℝ) (n : ℕ) (θ : ℝ) :
    (c * ((r : ℂ) * Complex.exp (-(θ * Complex.I))) ^ (2 * n)).re =
      r ^ (2 * n) * (c.re * Real.cos (2 * n * θ) + c.im * Real.sin (2 * n * θ)) := by
  have h : ((r : ℂ) * Complex.exp (-(θ * Complex.I))) ^ (2 * n) =
      ((r ^ (2 * n) : ℝ) : ℂ) * Complex.exp (((-(2 * n * θ) : ℝ) : ℂ) * Complex.I) := by
    rw [mul_pow, ← Complex.exp_nat_mul]
    push_cast
    congr 2
    push_cast; ring
  rw [h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
    Complex.sub_re, Complex.sub_im, Real.cos_neg, Real.sin_neg, Complex.one_re]
  ring

theorem circle_mem_ball38 {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (θ : ℝ) :
    (r : ℂ) * Complex.exp (-(θ * Complex.I)) ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, norm_mul, Complex.norm_exp]
  simp [abs_of_pos hr0, hr1]

theorem fourier_even_circle38 {ℓ : ℂ → ℂ} (hℓ : DifferentiableOn ℂ ℓ (ball (0:ℂ) 1))
    (hev : ∀ ζ ∈ ball (0:ℂ) 1, ℓ (-ζ) = ℓ ζ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (k : ℕ) :
    ∫ θ in (0:ℝ)..(2 * Real.pi),
        (ℓ ((r : ℂ) * Complex.exp (-(θ * Complex.I)))).re * Real.cos (2 * k * θ) =
      if k = 0 then 2 * Real.pi * (ℓ 0).re
      else Real.pi * (evenLogCoeff38 ℓ (k - 1)).re * r ^ (2 * k) := by
  set c : ℕ → ℂ := evenLogCoeff38 ℓ with hc
  have hcont : Continuous fun θ : ℝ => ℓ ((r : ℂ) * Complex.exp (-(θ * Complex.I))) := by
    have h1 : Continuous fun θ : ℝ => (r : ℂ) * Complex.exp (-(θ * Complex.I)) := by fun_prop
    exact hℓ.continuousOn.comp_continuous h1 (circle_mem_ball38 hr0 hr1)
  have hcos : Continuous fun θ : ℝ => Real.cos (2 * k * θ) := by fun_prop
  have hint1 : IntervalIntegrable (fun θ : ℝ =>
      (ℓ ((r : ℂ) * Complex.exp (-(θ * Complex.I)))).re * Real.cos (2 * k * θ)) volume 0
      (2 * Real.pi) :=
    ((Complex.continuous_re.comp hcont).mul hcos).intervalIntegrable _ _
  -- summability of norms
  have hsum0 := (hasSum_even_taylor38 hℓ hev (circle_mem_ball38 hr0 hr1 0)).summable
  have hsumr : Summable fun m : ℕ => ‖c m * ((r : ℂ)) ^ (2 * (m + 1))‖ := by
    have := (hasSum_even_taylor38 hℓ hev (ζ := (r : ℂ)) (by
      simpa using circle_mem_ball38 hr0 hr1 0)).summable
    exact this.norm
  set F : ℕ → ℝ → ℝ := fun m θ =>
    (c m * ((r : ℂ) * Complex.exp (-(θ * Complex.I))) ^ (2 * (m + 1))).re *
      Real.cos (2 * k * θ) with hF
  have hFcont : ∀ m, Continuous (F m) := by
    intro m; simp only [hF]
    exact (Complex.continuous_re.comp (by fun_prop)).mul hcos
  have hlim := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := 0) (b := 2 * Real.pi) (F := F)
    (f := fun θ => ((ℓ ((r : ℂ) * Complex.exp (-(θ * Complex.I)))).re - (ℓ 0).re) *
      Real.cos (2 * k * θ))
    (fun m _ => ‖c m * ((r : ℂ)) ^ (2 * (m + 1))‖)
    (fun m => (hFcont m).aestronglyMeasurable)
    (fun m => Filter.Eventually.of_forall fun θ _ => by
      simp only [hF]
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |(c m * ((r : ℂ) * Complex.exp (-(θ * Complex.I))) ^ (2 * (m + 1))).re| ≤
          ‖c m * (r : ℂ) ^ (2 * (m + 1))‖ := by
        refine (Complex.abs_re_le_norm _).trans ?_
        have he : ‖Complex.exp (-((θ:ℂ) * Complex.I))‖ = 1 := by
          rw [Complex.norm_exp]; simp
        rw [norm_mul, norm_mul (c m), mul_pow, norm_mul, norm_pow (Complex.exp _), he]
        simp
      have h2 : |Real.cos (2 * k * θ)| ≤ 1 := Real.abs_cos_le_one _
      calc _ ≤ ‖c m * (r : ℂ) ^ (2 * (m + 1))‖ * 1 :=
            mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
        _ = _ := mul_one _)
    (Filter.Eventually.of_forall fun θ _ => hsumr)
    (intervalIntegrable_const)
    (Filter.Eventually.of_forall fun θ _ => by
      have h := hasSum_even_taylor38 hℓ hev (circle_mem_ball38 hr0 hr1 θ)
      have h2 := (Complex.reCLM.hasSum h).mul_right (Real.cos (2 * k * θ))
      simpa [hF, Complex.sub_re] using h2)
  -- the integral of each term
  have hterm : ∀ m : ℕ, ∫ θ in (0:ℝ)..(2 * Real.pi), F m θ =
      if k = m + 1 then Real.pi * (c m).re * r ^ (2 * k) else 0 := by
    intro m
    have e : ∀ θ, F m θ = r ^ (2 * (m + 1)) * ((c m).re *
        (Real.cos (2 * ((m + 1 : ℕ) : ℝ) * θ) * Real.cos (2 * k * θ)) + (c m).im *
        (Real.sin (2 * ((m + 1 : ℕ) : ℝ) * θ) * Real.cos (2 * k * θ))) := by
      intro θ; simp only [hF]; rw [re_term38]; ring
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
      ((by fun_prop : Continuous fun θ : ℝ => (c m).re *
        (Real.cos (2 * ((m + 1 : ℕ) : ℝ) * θ) * Real.cos (2 * k * θ))).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun θ : ℝ => (c m).im *
        (Real.sin (2 * ((m + 1 : ℕ) : ℝ) * θ) * Real.cos (2 * k * θ))).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_cos_mul_cos38, integral_sin_mul_cos38]
    by_cases h : m + 1 = k
    · subst h; simp; ring
    · rw [if_neg h, if_neg (fun h' => h h'.symm)]; simp
  have hlim2 : HasSum (fun m : ℕ => if k = m + 1 then Real.pi * (c m).re * r ^ (2 * k) else 0)
      (∫ θ in (0:ℝ)..(2 * Real.pi), ((ℓ ((r : ℂ) * Complex.exp (-(θ * Complex.I)))).re -
        (ℓ 0).re) * Real.cos (2 * k * θ)) := by
    simpa only [hterm] using hlim
  have hsplit : ∫ θ in (0:ℝ)..(2 * Real.pi),
        (ℓ ((r : ℂ) * Complex.exp (-(θ * Complex.I)))).re * Real.cos (2 * k * θ) =
      (∫ θ in (0:ℝ)..(2 * Real.pi), ((ℓ ((r : ℂ) * Complex.exp (-(θ * Complex.I)))).re -
        (ℓ 0).re) * Real.cos (2 * k * θ)) +
      (ℓ 0).re * ∫ θ in (0:ℝ)..(2 * Real.pi), Real.cos (2 * k * θ) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add]
    · congr 1; ext θ; ring
    · exact (((Complex.continuous_re.comp hcont).sub continuous_const).mul hcos).intervalIntegrable
        _ _
    · exact (continuous_const.mul hcos).intervalIntegrable _ _
  rw [hsplit]
  by_cases hk : k = 0
  · subst hk
    have : (∫ θ in (0:ℝ)..(2 * Real.pi), ((ℓ ((r : ℂ) * Complex.exp (-(θ * Complex.I)))).re -
        (ℓ 0).re) * Real.cos (2 * ((0:ℕ):ℝ) * θ)) = 0 := by
      refine hlim2.unique ?_
      simp only [if_neg (Nat.succ_ne_zero _).symm]
      · exact hasSum_zero
    rw [this]
    simp; ring
  · have hv : (∫ θ in (0:ℝ)..(2 * Real.pi), ((ℓ ((r : ℂ) * Complex.exp (-(θ * Complex.I)))).re -
        (ℓ 0).re) * Real.cos (2 * k * θ)) = Real.pi * (c (k - 1)).re * r ^ (2 * k) := by
      refine hlim2.unique ?_
      have := hasSum_ite_eq (k - 1) (Real.pi * (c (k - 1)).re * r ^ (2 * k))
      convert this using 2 with m
      have : (k = m + 1) ↔ (m = k - 1) := by omega
      simp only [this]
      by_cases hm : m = k - 1
      · subst hm; rfl
      · simp [hm]
    have h0 := integral_cos_int38 (k : ℤ) (by exact_mod_cast hk)
    simp only [Int.cast_natCast] at h0
    rw [hv, h0, if_neg hk]; simp


/-! ### The real-part identity -/

theorem re_p_identity38 {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) {z : ℂ}
    (hz : 1 < ‖z‖) :
    Real.log ‖z‖ + (1 / (L : ℝ)) * (alLog38 α (1 / z)).re =
      (1 / (L : ℝ)) * Real.log ‖alExtW38 α (1 / z)‖ := by
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
  have hmem : (1 / z) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, one_div, norm_inv]; exact inv_lt_one_of_one_lt₀ hz
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have hg : ‖alExteriorG38 α (1 / z)‖ = Real.exp (alLog38 α (1 / z)).re := by
    rw [← (alLog38_spec hα).2.1 _ hmem, Complex.norm_exp]
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hnorm : ‖alExtW38 α (1 / z)‖ =
      (‖z‖ ^ L) * Real.exp (alLog38 α (1 / z)).re := by
    unfold alExtW38
    rw [norm_mul, norm_inv, norm_pow, hg, one_div, norm_inv, inv_pow, inv_inv]
  rw [hnorm, Real.log_mul (pow_ne_zero _ hzpos.ne') (Real.exp_pos _).ne', Real.log_pow,
    Real.log_exp]
  field_simp

/-! ### Fixed-radius formula -/

theorem circle_formula38 {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) {ρ : ℝ}
    (hρ : 1 < ρ) (θ : ℝ) :
    (1 / (L : ℝ)) * Real.log ‖alExtW38 α (1 / ((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))‖ =
      Real.log ρ + (1 / (L : ℝ)) *
        (alLog38 α (((ρ⁻¹ : ℝ) : ℂ) * Complex.exp (-((θ : ℂ) * Complex.I)))).re := by
  have hρ0 : (0 : ℝ) < ρ := by linarith
  have hn : ‖(ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = ρ := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I]; simp [abs_of_pos hρ0]
  have h := re_p_identity38 hα (z := (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) (by rw [hn]; exact hρ)
  rw [hn] at h
  rw [← h]
  congr 4
  have : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ0.ne'
  rw [one_div, mul_inv, ← Complex.exp_neg]
  push_cast; rfl

theorem fourier_circle_kappa38 {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) {ρ : ℝ}
    (hρ : 1 < ρ) (k : ℕ) :
    ∫ θ in (0:ℝ)..(2 * Real.pi),
        (1 / (L : ℝ)) * Real.log ‖alExtW38 α (1 / ((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))‖
          * Real.cos (2 * k * θ) =
      if k = 0 then 2 * Real.pi * Real.log ρ + (1 / (L : ℝ)) * (2 * Real.pi * (alLog38 α 0).re)
      else (1 / (L : ℝ)) * (Real.pi * (alC38 α k).re * (ρ⁻¹) ^ (2 * k)) := by
  have hρ0 : (0 : ℝ) < ρ := by linarith
  have hr0 : 0 < ρ⁻¹ := inv_pos.mpr hρ0
  have hr1 : ρ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hρ
  have hs := alLog38_spec hα
  have hF := fourier_even_circle38 hs.1.differentiableOn hs.2.2.2 hr0 hr1 k
  have hcont : Continuous fun θ : ℝ =>
      (alLog38 α (((ρ⁻¹ : ℝ) : ℂ) * Complex.exp (-((θ : ℂ) * Complex.I)))) := by
    have h1 : Continuous fun θ : ℝ => ((ρ⁻¹ : ℝ) : ℂ) * Complex.exp (-((θ : ℂ) * Complex.I)) := by
      fun_prop
    exact hs.1.continuousOn.comp_continuous h1 (circle_mem_ball38 hr0 hr1)
  have hcos : Continuous fun θ : ℝ => Real.cos (2 * k * θ) := by fun_prop
  have e : ∀ θ : ℝ, (1 / (L : ℝ)) * Real.log ‖alExtW38 α (1 / ((ρ : ℂ) *
        Complex.exp ((θ : ℂ) * Complex.I)))‖ * Real.cos (2 * k * θ) =
      Real.log ρ * Real.cos (2 * k * θ) + (1 / (L : ℝ)) *
        ((alLog38 α (((ρ⁻¹ : ℝ) : ℂ) * Complex.exp (-((θ : ℂ) * Complex.I)))).re *
          Real.cos (2 * k * θ)) := by
    intro θ; rw [circle_formula38 hα hρ]; ring
  simp only [e]
  have i1 : IntervalIntegrable (fun θ : ℝ => Real.log ρ * Real.cos (2 * k * θ)) volume 0
      (2 * Real.pi) := (continuous_const.mul hcos).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun θ : ℝ => (1 / (L : ℝ)) *
        ((alLog38 α (((ρ⁻¹ : ℝ) : ℂ) * Complex.exp (-((θ : ℂ) * Complex.I)))).re *
          Real.cos (2 * k * θ))) volume 0 (2 * Real.pi) :=
    (continuous_const.mul ((Complex.continuous_re.comp hcont).mul hcos)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add i1 i2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hF]
  by_cases hk : k = 0
  · subst hk
    simp; ring
  · have h0 := integral_cos_int38 (k : ℤ) (by exact_mod_cast hk)
    simp only [Int.cast_natCast] at h0
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    rw [h0, if_neg hk, if_neg hk, ← alC38_succ]
    simp


/-! ### Boundary Fourier identities -/

theorem fourier_kappa38 {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) (k : ℕ) :
    ∫ θ in (0:ℝ)..(2 * Real.pi), alKappa38 α θ * Real.cos (2 * k * θ) =
      if k = 0 then Real.pi * alMass38 L α / L
      else Real.pi * (alC38 α k).re / L := by
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  obtain ⟨B, hB⟩ := alKappa38_uniform_bound hα
  have hs := alLog38_spec hα
  set G : ℝ → ℝ := fun ρ => ∫ θ in (0:ℝ)..(2 * Real.pi),
        (1 / (L : ℝ)) * Real.log ‖alExtW38 α (1 / ((ρ : ℂ) *
          Complex.exp ((θ : ℂ) * Complex.I)))‖ * Real.cos (2 * k * θ) with hG
  have hlim : Tendsto G (𝓝[>] 1) (𝓝 (∫ θ in (0:ℝ)..(2 * Real.pi),
      alKappa38 α θ * Real.cos (2 * k * θ))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => B) ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards [self_mem_nhdsWithin] with ρ hρ
      have hρ' : (1:ℝ) < ρ := hρ
      refine (Continuous.aestronglyMeasurable ?_)
      have hρ0 : (0 : ℝ) < ρ := by linarith
      have hcont : Continuous fun θ : ℝ =>
          (alLog38 α (((ρ⁻¹ : ℝ) : ℂ) * Complex.exp (-((θ : ℂ) * Complex.I)))) := by
        have h1 : Continuous fun θ : ℝ =>
            ((ρ⁻¹ : ℝ) : ℂ) * Complex.exp (-((θ : ℂ) * Complex.I)) := by fun_prop
        exact hs.1.continuousOn.comp_continuous h1
          (circle_mem_ball38 (inv_pos.mpr hρ0) (inv_lt_one_of_one_lt₀ hρ'))
      have : Continuous fun θ : ℝ => (1 / (L : ℝ)) * Real.log ‖alExtW38 α (1 / ((ρ : ℂ) *
          Complex.exp ((θ : ℂ) * Complex.I)))‖ := by
        simp_rw [circle_formula38 hα hρ']
        exact continuous_const.add (continuous_const.mul (Complex.continuous_re.comp hcont))
      exact this.mul (by fun_prop)
    · filter_upwards [Ioc_mem_nhdsGT (show (1:ℝ) < 2 by norm_num)] with ρ hρ
      refine Filter.Eventually.of_forall fun θ _ => ?_
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      calc _ ≤ B * 1 := mul_le_mul (hB ρ hρ θ) (Real.abs_cos_le_one _) (abs_nonneg _)
            ((abs_nonneg _).trans (hB ρ hρ θ))
        _ = B := mul_one _
    · refine Filter.Eventually.of_forall fun θ _ => ?_
      exact (tendsto_alKappa38 hα θ).mul_const _
  have hev : ∀ᶠ ρ in 𝓝[>] (1:ℝ), G ρ =
      if k = 0 then 2 * Real.pi * Real.log ρ + (1 / (L : ℝ)) * (2 * Real.pi * (alLog38 α 0).re)
      else (1 / (L : ℝ)) * (Real.pi * (alC38 α k).re * (ρ⁻¹) ^ (2 * k)) := by
    filter_upwards [self_mem_nhdsWithin] with ρ hρ
    exact fourier_circle_kappa38 hα hρ k
  have hlim2 : Tendsto (fun ρ : ℝ => if k = 0 then
      2 * Real.pi * Real.log ρ + (1 / (L : ℝ)) * (2 * Real.pi * (alLog38 α 0).re)
      else (1 / (L : ℝ)) * (Real.pi * (alC38 α k).re * (ρ⁻¹) ^ (2 * k))) (𝓝[>] 1)
      (𝓝 (if k = 0 then Real.pi * alMass38 L α / L
        else Real.pi * (alC38 α k).re / L)) := by
    by_cases hk : k = 0
    · simp only [hk, if_true]
      have h1 : Tendsto (fun ρ : ℝ => 2 * Real.pi * Real.log ρ +
          (1 / (L : ℝ)) * (2 * Real.pi * (alLog38 α 0).re)) (𝓝 1)
          (𝓝 (2 * Real.pi * Real.log 1 + (1 / (L : ℝ)) * (2 * Real.pi * (alLog38 α 0).re))) :=
        ((Real.continuousAt_log one_ne_zero).tendsto.const_mul _).add_const _
      have e : 2 * Real.pi * Real.log 1 + (1 / (L : ℝ)) * (2 * Real.pi * (alLog38 α 0).re) =
          Real.pi * alMass38 L α / L := by
        rw [hs.2.2.1, Real.log_one]
        simp
        field_simp
      rw [e] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    · simp only [hk, if_false]
      have h1 : Tendsto (fun ρ : ℝ => (1 / (L : ℝ)) * (Real.pi * (alC38 α k).re * (ρ⁻¹) ^ (2 * k)))
          (𝓝 1) (𝓝 ((1 / (L : ℝ)) * (Real.pi * (alC38 α k).re * ((1:ℝ)⁻¹) ^ (2 * k)))) := by
        have : ContinuousAt (fun ρ : ℝ => (1 / (L : ℝ)) *
            (Real.pi * (alC38 α k).re * (ρ⁻¹) ^ (2 * k))) 1 := by
          have := (continuousAt_inv₀ (one_ne_zero : (1:ℝ) ≠ 0))
          fun_prop (disch := exact one_ne_zero)
        exact this.tendsto
      have e : (1 / (L : ℝ)) * (Real.pi * (alC38 α k).re * ((1:ℝ)⁻¹) ^ (2 * k)) =
          Real.pi * (alC38 α k).re / L := by
        simp; ring
      rw [e] at h1
      exact h1.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique hlim (hlim2.congr' (hev.mono fun ρ h => h.symm))

theorem integral_alKappa38 {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) :
    ∫ θ in (0:ℝ)..(2 * Real.pi), alKappa38 α θ = Real.pi * alMass38 L α / L := by
  have := fourier_kappa38 hα 0
  simpa using this

theorem integral_alKappa38_cos {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α)
    {k : ℕ} (hk : 1 ≤ k) :
    ∫ θ in (0:ℝ)..(2 * Real.pi), alKappa38 α θ * Real.cos (2 * k * θ) =
      Real.pi * (alC38 α k).re / L := by
  have := fourier_kappa38 hα k
  rwa [if_neg (by omega)] at this

end NlsGge.AblowitzLadik
end
