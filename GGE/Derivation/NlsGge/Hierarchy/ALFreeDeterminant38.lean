import NlsGge.Hierarchy.ALCorrector38

set_option autoImplicit false

namespace NlsGge.AblowitzLadik

open NlsGge.Weights MeasureTheory Filter
open scoped Topology

section Riemann

/-- Right-endpoint Riemann sums `h Σ_{j=1}^N g(j h)`, `h = 1/(2N+1)`, converge to `∫_0^{1/2} g`
for continuous `g`. -/
theorem alRiemann_tendsto38 (g : ℝ → ℝ) (hg : Continuous g) :
    Tendsto (fun N : ℕ => alMeshStep38 N * ∑ j ∈ Finset.Icc 1 N, g ((j : ℝ) * alMeshStep38 N))
      atTop (𝓝 (∫ x in (0 : ℝ)..1 / 2, g x)) := by
  have hNh : Tendsto (fun N : ℕ => (N : ℝ) * alMeshStep38 N) atTop (𝓝 (1 / 2)) := by
    have h1 : Tendsto (fun N : ℕ => (1 / 2 : ℝ) - (1 / 2) * alMeshStep38 N) atTop (𝓝 (1 / 2)) := by
      simpa using tendsto_const_nhds.sub (alMeshStep_tendsto38.const_mul (1 / 2 : ℝ))
    refine h1.congr (fun N => ?_)
    unfold alMeshStep38
    have : (2 * (N : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  have hprim : Tendsto (fun N : ℕ => ∫ x in (0 : ℝ)..((N : ℝ) * alMeshStep38 N), g x) atTop
      (𝓝 (∫ x in (0 : ℝ)..1 / 2, g x)) :=
    ((intervalIntegral.continuous_primitive (fun a b => hg.intervalIntegrable a b) 0).tendsto
      (1 / 2)).comp hNh
  have hdiff : Tendsto (fun N : ℕ => alMeshStep38 N *
      ∑ j ∈ Finset.Icc 1 N, g ((j : ℝ) * alMeshStep38 N) -
      ∫ x in (0 : ℝ)..((N : ℝ) * alMeshStep38 N), g x) atTop (𝓝 0) := by
    have huc := IsCompact.uniformContinuousOn_of_continuous (isCompact_Icc (a := (0 : ℝ)) (b := 1))
      hg.continuousOn
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1 huc (ε / 2) (half_pos hε)
    filter_upwards [alMeshStep_tendsto38.eventually (gt_mem_nhds hδ),
      eventually_ge_atTop 1] with N hN hN1
    set h := alMeshStep38 N with hh
    have hh0 : 0 < h := alMeshStep_pos38 N
    have hNh1 : (N : ℝ) * h ≤ 1 / 2 := by
      rw [hh]; unfold alMeshStep38
      have : (0 : ℝ) < 2 * (N : ℝ) + 1 := by positivity
      rw [mul_one_div, div_le_div_iff₀ this (by norm_num)]; nlinarith
    have hsplit : ∫ x in (0 : ℝ)..((N : ℝ) * h), g x =
        ∑ j ∈ Finset.range N, ∫ x in ((j : ℝ) * h)..(((j + 1 : ℕ) : ℝ) * h), g x := by
      have := intervalIntegral.sum_integral_adjacent_intervals (f := g) (μ := volume)
        (a := fun k : ℕ => (k : ℝ) * h) (n := N) (fun k _ => hg.intervalIntegrable _ _)
      simpa using this.symm
    have hsum : ∑ j ∈ Finset.Icc 1 N, g ((j : ℝ) * h) =
        ∑ j ∈ Finset.range N, g (((j + 1 : ℕ) : ℝ) * h) := by
      have e : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by ext; simp
      rw [e, Finset.sum_Ico_eq_sum_range]
      simp [add_comm]
    have hterm : ∀ j ∈ Finset.range N,
        |h * g (((j + 1 : ℕ) : ℝ) * h) - ∫ x in ((j : ℝ) * h)..(((j + 1 : ℕ) : ℝ) * h), g x|
          ≤ ε / 2 * h := by
      intro j hj
      have hjN : j + 1 ≤ N := Finset.mem_range.1 hj
      have hjN' : ((j + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hjN
      have hb : ((j + 1 : ℕ) : ℝ) * h ≤ 1 / 2 := le_trans (by gcongr) hNh1
      have hj0 : (0 : ℝ) ≤ (j : ℝ) * h := by positivity
      have hlt : (j : ℝ) * h ≤ ((j + 1 : ℕ) : ℝ) * h := by push_cast; nlinarith
      have e1 : h * g (((j + 1 : ℕ) : ℝ) * h) - ∫ x in ((j : ℝ) * h)..(((j + 1 : ℕ) : ℝ) * h), g x
          = ∫ x in ((j : ℝ) * h)..(((j + 1 : ℕ) : ℝ) * h),
              (g (((j + 1 : ℕ) : ℝ) * h) - g x) := by
        rw [intervalIntegral.integral_sub (by simp) (hg.intervalIntegrable _ _)]
        simp only [intervalIntegral.integral_const, smul_eq_mul]
        push_cast; ring_nf
      rw [e1]
      have := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (j : ℝ) * h) (b := ((j + 1 : ℕ) : ℝ) * h) (C := ε / 2)
        (f := fun x => g (((j + 1 : ℕ) : ℝ) * h) - g x) (by
          intro x hx
          rw [Set.uIoc_of_le hlt] at hx
          have hx1 : x ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
          have hy1 : ((j + 1 : ℕ) : ℝ) * h ∈ Set.Icc (0 : ℝ) 1 :=
            ⟨by positivity, by linarith⟩
          have hd : dist (((j + 1 : ℕ) : ℝ) * h) x < δ := by
            rw [Real.dist_eq, abs_lt]
            have : ((j + 1 : ℕ) : ℝ) * h - x ≤ h := by
              have : ((j + 1 : ℕ) : ℝ) * h - (j : ℝ) * h = h := by push_cast; ring
              linarith [hx.1]
            constructor <;> linarith [hx.1, hx.2]
          have := hδ' _ hy1 x hx1 hd
          rw [Real.dist_eq] at this
          rw [Real.norm_eq_abs]; exact this.le)
      have hl : |((j + 1 : ℕ) : ℝ) * h - (j : ℝ) * h| = h := by
        rw [show ((j + 1 : ℕ) : ℝ) * h - (j : ℝ) * h = h by push_cast; ring, abs_of_pos hh0]
      rw [Real.norm_eq_abs, hl] at this
      exact this
    rw [Real.dist_eq, sub_zero, hsplit, hsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    calc |∑ j ∈ Finset.range N, (h * g (((j + 1 : ℕ) : ℝ) * h) -
          ∫ x in ((j : ℝ) * h)..(((j + 1 : ℕ) : ℝ) * h), g x)|
        ≤ ∑ j ∈ Finset.range N, |h * g (((j + 1 : ℕ) : ℝ) * h) -
          ∫ x in ((j : ℝ) * h)..(((j + 1 : ℕ) : ℝ) * h), g x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.range N, ε / 2 * h := Finset.sum_le_sum hterm
      _ = ε / 2 * ((N : ℝ) * h) := by simp; ring
      _ < ε := by nlinarith
  simpa using hdiff.add hprim |>.congr (fun N => by ring)

end Riemann

section Integrand

/-- The integrand `√(2 sin(π x)) − √(2π x)` of D:eq:freedet. -/
noncomputable def alFreeDetIntegrand38 (x : ℝ) : ℝ :=
  Real.sqrt (2 * Real.sin (Real.pi * x)) - Real.sqrt (2 * Real.pi * x)

theorem alFreeDetIntegrand_continuous38 : Continuous alFreeDetIntegrand38 := by
  unfold alFreeDetIntegrand38
  fun_prop

/-- The integral in D:eq:freedet is strictly negative. -/
theorem alFreeDetIntegral_neg38 : ∫ x in (0 : ℝ)..1 / 2, alFreeDetIntegrand38 x < 0 := by
  have h := intervalIntegral.intervalIntegral_pos_of_pos_on
    (f := fun x => -alFreeDetIntegrand38 x) (a := 0) (b := 1 / 2)
    (alFreeDetIntegrand_continuous38.neg.intervalIntegrable _ _) (by
      intro x hx
      obtain ⟨hx0, hx1⟩ := hx
      have hs : 0 < Real.sin (Real.pi * x) :=
        Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
      have hlt : Real.sin (Real.pi * x) < Real.pi * x := Real.sin_lt (by positivity)
      have : Real.sqrt (2 * Real.sin (Real.pi * x)) < Real.sqrt (2 * Real.pi * x) :=
        Real.sqrt_lt_sqrt (by positivity) (by nlinarith)
      simp only [alFreeDetIntegrand38]; linarith) (by norm_num)
  rw [intervalIntegral.integral_neg] at h
  linarith

end Integrand

section EvenSum

theorem sum_Icc_even38 (f : ℤ → ℝ) (hf : ∀ k, f (-k) = f k) (N : ℕ) :
    ∑ k ∈ Finset.Icc (-(N : ℤ)) N, f k = f 0 + 2 * ∑ j ∈ Finset.Icc 1 N, f (j : ℤ) := by
  induction N with
  | zero => simp
  | succ n ih =>
    have e : Finset.Icc (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ) =
        insert (-((n + 1 : ℕ) : ℤ)) (insert ((n + 1 : ℕ) : ℤ) (Finset.Icc (-(n : ℤ)) n)) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    have e2 : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [e, Finset.sum_insert, Finset.sum_insert, ih, e2, Finset.sum_insert, hf]
    · ring
    · simp
    · simp only [Finset.mem_Icc]; push_cast; omega
    · simp only [Finset.mem_insert, Finset.mem_Icc]; push_cast; omega

end EvenSum

section Rates

variable {lower upper : ℝ} {c : ℕ → ℝ}

theorem alOmegaFree_neg38 (N : ℕ) (k : ℤ) : alOmegaFree38 N (-k) = -alOmegaFree38 N k := by
  unfold alOmegaFree38
  push_cast
  rw [show Real.pi * -(k : ℝ) * alMeshStep38 N = -(Real.pi * (k : ℝ) * alMeshStep38 N) by ring,
    Real.sin_neg]
  ring

theorem alRateFree_neg38 (c : ℕ → ℝ) (N : ℕ) (k : ℤ) :
    alRateFree38 c N (-k) = alRateFree38 c N k := by
  unfold alRateFree38
  rw [alOmegaFree_neg38, weight_even]

theorem alRateCont_neg38 (c : ℕ → ℝ) (k : ℤ) : alRateCont38 c (-k) = alRateCont38 c k := by
  unfold alRateCont38
  push_cast
  rw [show 2 * Real.pi * -(k : ℝ) = -(2 * Real.pi * (k : ℝ)) by ring, weight_even]

/-- `log W(r) = 4 √r + O(1 + log(1+r))`, from D:eq:Wasymp. -/
theorem log_weight_size38 (hA : AdmissibleWeight38 lower upper c) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ r : ℝ, 0 ≤ r →
      |Real.log (weight c r) - 4 * Real.sqrt r| ≤ D + 3 / 4 * Real.log (1 + r) := by
  obtain ⟨hl, hb, hu⟩ := hA
  have hlu : lower ≤ upper := (hb 0).trans (hu 0)
  obtain ⟨A, B, hA0, hB0, hAB⟩ := weight_two_sided_size lower upper hl hlu
  refine ⟨max |Real.log A| |Real.log B|, le_max_of_le_left (abs_nonneg _), fun r hr => ?_⟩
  obtain ⟨h1, h2⟩ := hAB c hb hu r
  rw [abs_of_nonneg hr] at h1 h2
  have hp : 0 < (1 + r) ^ (-3 / 4 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hW := weight_pos lower upper c hl hb hu r
  have l1 := Real.log_le_log (by positivity) h1
  have l2 := Real.log_le_log hW h2
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_mul hA0.ne' hp.ne',
    Real.log_rpow (by linarith), Real.log_exp] at l1
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_mul hB0.ne' hp.ne',
    Real.log_rpow (by linarith), Real.log_exp] at l2
  have m1 : |Real.log A| ≤ max |Real.log A| |Real.log B| := le_max_left _ _
  have m2 : |Real.log B| ≤ max |Real.log A| |Real.log B| := le_max_right _ _
  rw [abs_le]
  have hl0 : 0 ≤ Real.log (1 + r) := Real.log_nonneg (by linarith)
  constructor <;> nlinarith [neg_abs_le (Real.log A), le_abs_self (Real.log B)]

end Rates

section TermError

variable {lower upper : ℝ} {c : ℕ → ℝ}

theorem alMeshStep_mul_le38 (N j : ℕ) (hj : j ≤ N) : (j : ℝ) * alMeshStep38 N ≤ 1 / 2 := by
  unfold alMeshStep38
  have h0 : (0 : ℝ) < 2 * (N : ℝ) + 1 := by positivity
  have : (j : ℝ) ≤ N := by exact_mod_cast hj
  rw [mul_one_div, div_le_div_iff₀ h0 (by norm_num)]
  nlinarith

theorem alOmegaFree_bounds38 (N j : ℕ) (hj : j ≤ N) :
    0 ≤ alOmegaFree38 N (j : ℤ) ∧ alOmegaFree38 N (j : ℤ) ≤ 2 * Real.pi * j := by
  have hh := alMeshStep_pos38 N
  have hjh := alMeshStep_mul_le38 N j hj
  have hθ0 : 0 ≤ Real.pi * (j : ℝ) * alMeshStep38 N := by positivity
  have hθ1 : Real.pi * (j : ℝ) * alMeshStep38 N ≤ Real.pi := by
    nlinarith [Real.pi_pos]
  unfold alOmegaFree38
  push_cast
  constructor
  · exact div_nonneg (by have := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 hθ1; linarith) hh.le
  · rw [div_le_iff₀ hh]
    have := Real.sin_le hθ0
    nlinarith

/-- Termwise comparison of `log (a_{h,j}/a_j)` with `4(√ω_{h,j} − √(2πj))`, uniformly in `j ≤ N`. -/
theorem alFreeDetTerm_error38 (hA : AdmissibleWeight38 lower upper c) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ N : ℕ in atTop, ∀ j : ℕ, j ≤ N →
      |Real.log (alRateFree38 c N (j : ℤ) / alRateCont38 c (j : ℤ)) -
          4 * (Real.sqrt (alOmegaFree38 N (j : ℤ)) - Real.sqrt (2 * Real.pi * j))| ≤
        D + 3 / 2 * Real.log (1 + 2 * Real.pi * N) := by
  obtain ⟨hl, hb, hu⟩ := hA
  have hA' : AdmissibleWeight38 lower upper c := ⟨hl, hb, hu⟩
  obtain ⟨D0, hD0, hD⟩ := log_weight_size38 hA'
  refine ⟨Real.log 2 + 2 * D0, by positivity, ?_⟩
  filter_upwards [alMeshStep_tendsto38.eventually (gt_mem_nhds (half_pos hl))] with N hN j hj
  obtain ⟨hω0, hω1⟩ := alOmegaFree_bounds38 N j hj
  set ω := alOmegaFree38 N (j : ℤ) with hω
  have hh := alMeshStep_pos38 N
  have hjN : (j : ℝ) ≤ N := by exact_mod_cast hj
  have hWl := weight_lower lower upper c hl hb hu ω
  have hWp := weight_pos lower upper c hl hb hu ω
  have hRc : alRateCont38 c (j : ℤ) = weight c (2 * Real.pi * j) := by
    unfold alRateCont38; push_cast; rfl
  have hRp := weight_pos lower upper c hl hb hu (2 * Real.pi * j)
  have ha : alRateFree38 c N (j : ℤ) = weight c ω - alMeshStep38 N := rfl
  have ha1 : weight c ω / 2 ≤ alRateFree38 c N (j : ℤ) := by rw [ha]; linarith
  have ha2 : alRateFree38 c N (j : ℤ) ≤ weight c ω := by rw [ha]; linarith
  have hap : 0 < alRateFree38 c N (j : ℤ) := by linarith
  have hlog1 : |Real.log (alRateFree38 c N (j : ℤ)) - Real.log (weight c ω)| ≤ Real.log 2 := by
    have u := Real.log_le_log hap ha2
    have v := Real.log_le_log (by positivity) ha1
    rw [Real.log_div hWp.ne' (by norm_num)] at v
    rw [abs_le]; constructor <;> linarith
  have hpi := Real.pi_pos
  have hlogN : Real.log (1 + ω) ≤ Real.log (1 + 2 * Real.pi * N) := by
    apply Real.log_le_log (by linarith)
    nlinarith
  have hlogN' : Real.log (1 + 2 * Real.pi * j) ≤ Real.log (1 + 2 * Real.pi * N) := by
    apply Real.log_le_log (by positivity)
    nlinarith
  have d1 := hD ω hω0
  have d2 := hD (2 * Real.pi * j) (by positivity)
  rw [Real.log_div hap.ne' (by rw [hRc]; exact hRp.ne'), hRc]
  have key : Real.log (alRateFree38 c N (j : ℤ)) - Real.log (weight c (2 * Real.pi * j)) -
      4 * (Real.sqrt ω - Real.sqrt (2 * Real.pi * j)) =
      (Real.log (alRateFree38 c N (j : ℤ)) - Real.log (weight c ω)) +
      (Real.log (weight c ω) - 4 * Real.sqrt ω) -
      (Real.log (weight c (2 * Real.pi * j)) - 4 * Real.sqrt (2 * Real.pi * j)) := by ring
  rw [key]
  rw [abs_le] at hlog1 d1 d2 ⊢
  constructor <;> nlinarith [hlog1.1, hlog1.2, d1.1, d1.2, d2.1, d2.2]

end TermError

section Assembly

variable {lower upper : ℝ} {c : ℕ → ℝ}

/-- `log ∏_{|k|≤N} a_{h,k}/a_k` with `h = 1/(2N+1)` (the left side of D:eq:freedet). -/
noncomputable def alFreeLogDet38 (c : ℕ → ℝ) (N : ℕ) : ℝ :=
  Real.log (∏ k ∈ Finset.Icc (-(N : ℤ)) N, alRateFree38 c N k / alRateCont38 c k)

theorem alMeshStep_rpow_three_halves38 (N : ℕ) :
    alMeshStep38 N ^ (3 / 2 : ℝ) = alMeshStep38 N * alMeshStep38 N ^ (1 / 2 : ℝ) := by
  have := alMeshStep_pos38 N
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add this, Real.rpow_one]

theorem alSmallError_tendsto38 (D : ℝ) (hD : 0 ≤ D) :
    Tendsto (fun N : ℕ => alMeshStep38 N ^ (1 / 2 : ℝ) *
      (D + 3 / 2 * Real.log (1 + 2 * Real.pi * N))) atTop (𝓝 0) := by
  have hx : Tendsto (fun N : ℕ => 2 * (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
  have t1 : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num)).tendsto_div_nhds_zero
  have t2 : Tendsto (fun x : ℝ => (x ^ (1 / 2 : ℝ))⁻¹) atTop (𝓝 0) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).inv_tendsto_atTop
  have t3 : Tendsto (fun N : ℕ => (D + 3 / 2 * Real.log Real.pi) *
      ((2 * (N : ℝ) + 1) ^ (1 / 2 : ℝ))⁻¹ + 3 / 2 * (Real.log (2 * (N : ℝ) + 1) /
        (2 * (N : ℝ) + 1) ^ (1 / 2 : ℝ))) atTop (𝓝 0) := by
    have := ((t2.comp hx).const_mul (D + 3 / 2 * Real.log Real.pi)).add
      ((t1.comp hx).const_mul (3 / 2 : ℝ))
    simpa using this
  refine squeeze_zero (fun N => ?_) (fun N => ?_) t3
  · have h0 : (0 : ℝ) ≤ 2 * Real.pi * N := by positivity
    have : 0 ≤ Real.log (1 + 2 * Real.pi * N) := Real.log_nonneg (by linarith)
    unfold alMeshStep38
    positivity
  · have hx0 : (0 : ℝ) < 2 * (N : ℝ) + 1 := by positivity
    have hlog : Real.log (1 + 2 * Real.pi * N) ≤ Real.log Real.pi + Real.log (2 * (N : ℝ) + 1) := by
      rw [← Real.log_mul Real.pi_pos.ne' hx0.ne']
      apply Real.log_le_log (by positivity)
      nlinarith [Real.pi_pos, Real.pi_gt_three]
    have hs : alMeshStep38 N ^ (1 / 2 : ℝ) = ((2 * (N : ℝ) + 1) ^ (1 / 2 : ℝ))⁻¹ := by
      unfold alMeshStep38
      rw [one_div, Real.inv_rpow hx0.le]
    have hp : 0 < (2 * (N : ℝ) + 1) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx0 _
    rw [hs]
    have : ((2 * (N : ℝ) + 1) ^ (1 / 2 : ℝ))⁻¹ * (D + 3 / 2 * Real.log (1 + 2 * Real.pi * N)) ≤
        ((2 * (N : ℝ) + 1) ^ (1 / 2 : ℝ))⁻¹ *
          (D + 3 / 2 * (Real.log Real.pi + Real.log (2 * (N : ℝ) + 1))) := by
      gcongr
    refine this.trans (le_of_eq ?_)
    field_simp
    ring

/-- **D:eq:freedet (asymptotic).** With `h = 1/(2N+1)`,
`h^{3/2} log ∏_{|k|≤N} a_{h,k}/a_k → 8 ∫_0^{1/2} [√(2 sin πx) − √(2πx)] dx`,
i.e. the logarithm equals `8 h^{-3/2} ∫ … + o(h^{-3/2})`. -/
theorem alFreeDeterminant_tendsto38 (hA : AdmissibleWeight38 lower upper c) :
    Tendsto (fun N : ℕ => alMeshStep38 N ^ (3 / 2 : ℝ) * alFreeLogDet38 c N) atTop
      (𝓝 (8 * ∫ x in (0 : ℝ)..1 / 2,
        (Real.sqrt (2 * Real.sin (Real.pi * x)) - Real.sqrt (2 * Real.pi * x)))) := by
  obtain ⟨D, hD, hDev⟩ := alFreeDetTerm_error38 hA
  have hR := (alRiemann_tendsto38 alFreeDetIntegrand38 alFreeDetIntegrand_continuous38).const_mul 8
  have hI : (fun x : ℝ => Real.sqrt (2 * Real.sin (Real.pi * x)) - Real.sqrt (2 * Real.pi * x)) =
      alFreeDetIntegrand38 := rfl
  rw [hI]
  refine hR.congr_dist (squeeze_zero' (Eventually.of_forall fun N => dist_nonneg) ?_
    (alSmallError_tendsto38 D hD))
  filter_upwards [hDev, alRateFree_pos_eventually38 hA] with N hN hpos
  set h := alMeshStep38 N with hh
  have hh0 : 0 < h := alMeshStep_pos38 N
  set E := D + 3 / 2 * Real.log (1 + 2 * Real.pi * N) with hE
  set F : ℤ → ℝ := fun k => Real.log (alRateFree38 c N k / alRateCont38 c k) with hF
  have hL : alFreeLogDet38 c N = ∑ k ∈ Finset.Icc (-(N : ℤ)) N, F k := by
    unfold alFreeLogDet38
    rw [Real.log_prod]
    intro k hk
    have hk' : |k| ≤ (N : ℤ) := abs_le.2 (Finset.mem_Icc.1 hk)
    have := hpos k hk'
    have h2 := weight_pos lower upper c hA.1 hA.2.1 hA.2.2 (2 * Real.pi * (k : ℝ))
    exact (div_pos this h2).ne'
  have hFe : ∀ k, F (-k) = F k := fun k => by
    simp only [hF, alRateFree_neg38, alRateCont_neg38]
  rw [hL, sum_Icc_even38 F hFe N]
  set m : ℕ → ℝ := fun j => 4 * (Real.sqrt (alOmegaFree38 N (j : ℤ)) - Real.sqrt (2 * Real.pi * j))
    with hm
  have hm0 : m 0 = 0 := by simp [hm, alOmegaFree38]
  have he : ∀ j ∈ Finset.Icc 1 N, |F (j : ℤ) - m j| ≤ E := fun j hj => by
    have := hN j (Finset.mem_Icc.1 hj).2
    simpa [hF, hm] using this
  have he0 : |F 0 - m 0| ≤ E := by
    have := hN 0 (Nat.zero_le _)
    simpa [hF, hm] using this
  have hg : ∀ j ∈ Finset.Icc 1 N, h ^ (3 / 2 : ℝ) * m j = 4 * (h * alFreeDetIntegrand38 (j * h)) := by
    intro j hj
    have hjN := (Finset.mem_Icc.1 hj).2
    obtain ⟨hω0, _⟩ := alOmegaFree_bounds38 N j hjN
    have hs0 : 0 ≤ 2 * Real.sin (Real.pi * (j : ℝ) * h) := by
      have hjh := alMeshStep_mul_le38 N j hjN
      have hθ0 : 0 ≤ Real.pi * (j : ℝ) * h := by positivity
      have := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by nlinarith [Real.pi_pos])
      linarith
    have hω : alOmegaFree38 N (j : ℤ) = 2 * Real.sin (Real.pi * (j : ℝ) * h) / h := by
      simp [alOmegaFree38, hh]
    have hr : 2 * Real.pi * (j : ℝ) = 2 * Real.pi * ((j : ℝ) * h) / h := by field_simp
    have hsh : 0 < Real.sqrt h := Real.sqrt_pos.2 hh0
    have hsq : h ^ (1 / 2 : ℝ) = Real.sqrt h := (Real.sqrt_eq_rpow h).symm
    simp only [hm, alFreeDetIntegrand38]
    rw [hω, alMeshStep_rpow_three_halves38, ← hh, hsq]
    rw [hr]
    rw [Real.sqrt_div hs0, Real.sqrt_div (by positivity)]
    rw [mul_comm Real.pi (j : ℝ)]
    field_simp
  have h1 : h ^ (3 / 2 : ℝ) * ∑ j ∈ Finset.Icc 1 N, m j =
      4 * (h * ∑ j ∈ Finset.Icc 1 N, alFreeDetIntegrand38 (j * h)) := by
    rw [Finset.mul_sum, Finset.sum_congr rfl hg, ← Finset.mul_sum, ← Finset.mul_sum]
  have hsplit : ∑ j ∈ Finset.Icc 1 N, F (j : ℤ) =
      ∑ j ∈ Finset.Icc 1 N, (F (j : ℤ) - m j) + ∑ j ∈ Finset.Icc 1 N, m j := by
    rw [← Finset.sum_add_distrib]; simp
  have hid : 8 * (h * ∑ j ∈ Finset.Icc 1 N, alFreeDetIntegrand38 (j * h)) -
      h ^ (3 / 2 : ℝ) * (F 0 + 2 * ∑ j ∈ Finset.Icc 1 N, F (j : ℤ)) =
      -(h ^ (3 / 2 : ℝ) * ((F 0 - m 0) + 2 * ∑ j ∈ Finset.Icc 1 N, (F (j : ℤ) - m j))) := by
    rw [hsplit, hm0]
    have := h1
    linear_combination (-2) * this
  have hRb : |(F 0 - m 0) + 2 * ∑ j ∈ Finset.Icc 1 N, (F (j : ℤ) - m j)| ≤ (2 * N + 1) * E := by
    have hs : |∑ j ∈ Finset.Icc 1 N, (F (j : ℤ) - m j)| ≤ N * E := by
      calc _ ≤ ∑ j ∈ Finset.Icc 1 N, |F (j : ℤ) - m j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j ∈ Finset.Icc 1 N, E := Finset.sum_le_sum he
        _ = N * E := by simp
    calc _ ≤ |F 0 - m 0| + |2 * ∑ j ∈ Finset.Icc 1 N, (F (j : ℤ) - m j)| := abs_add_le _ _
      _ ≤ E + 2 * (N * E) := by
        rw [abs_mul, abs_two]; linarith
      _ = _ := by ring
  have hhN : h * (2 * N + 1) = 1 := by
    rw [hh]; unfold alMeshStep38; field_simp
  rw [Real.dist_eq, hid, abs_neg, abs_mul, abs_of_nonneg (Real.rpow_nonneg hh0.le _),
    alMeshStep_rpow_three_halves38]
  calc h * h ^ (1 / 2 : ℝ) * |(F 0 - m 0) + 2 * ∑ j ∈ Finset.Icc 1 N, (F (j : ℤ) - m j)|
      ≤ h * h ^ (1 / 2 : ℝ) * ((2 * N + 1) * E) := by gcongr
    _ = h ^ (1 / 2 : ℝ) * E * (h * (2 * N + 1)) := by ring
    _ = _ := by rw [hhN]; ring


/-- **D:eq:freedet (full statement).** Both the asymptotic
`h^{3/2} log ∏_{|k|≤N} a_{h,k}/a_k → 8 ∫_0^{1/2} [√(2 sin πx) − √(2πx)] dx` and the strict
negativity of the integral. -/
theorem alFreeDeterminant38 (hA : AdmissibleWeight38 lower upper c) :
    Tendsto (fun N : ℕ => alMeshStep38 N ^ (3 / 2 : ℝ) * alFreeLogDet38 c N) atTop
      (𝓝 (8 * ∫ x in (0 : ℝ)..1 / 2,
        (Real.sqrt (2 * Real.sin (Real.pi * x)) - Real.sqrt (2 * Real.pi * x)))) ∧
    (∫ x in (0 : ℝ)..1 / 2,
        (Real.sqrt (2 * Real.sin (Real.pi * x)) - Real.sqrt (2 * Real.pi * x))) < 0 :=
  ⟨alFreeDeterminant_tendsto38 hA, alFreeDetIntegral_neg38⟩

end Assembly

end NlsGge.AblowitzLadik

