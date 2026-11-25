import Mathlib

                                                                                                   
                                                                                             
                                                                                                       
                                                                                           
                                                                                                               
                                                                                                             
                                                                                                               
                                                                                  
                                                                                                             
                             
                                                                                                                  
                                                                                  

set_option autoImplicit false
open Set Filter Topology Metric Complex
open scoped Real

namespace NlsGge.ThirdConsultation.M017Cx

theorem cint_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) {c : ℂ} {R : ℝ}
    (h : ∀ i ∈ s, CircleIntegrable (f i) c R) :
    ∮ z in C(c, R), ∑ i ∈ s, f i z = ∑ i ∈ s, ∮ z in C(c, R), f i z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [circleIntegral]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [circleIntegral.integral_add (h a (Finset.mem_insert_self a s)) ?_]
    · rw [ih fun i hi => h i (Finset.mem_insert_of_mem hi)]
    · have := CircleIntegrable.sum s fun i hi => h i (Finset.mem_insert_of_mem hi)
      simpa [Finset.sum_fn] using this

theorem cint_zpow (ρ : ℝ) (hρ : 0 < ρ) (m : ℤ) :
    (∮ z in C(0, ρ), z ^ m) = if m = -1 then 2 * π * I else 0 := by
  split_ifs with hm
  · subst hm
    have := circleIntegral.integral_sub_inv_of_mem_ball (c := 0) (w := 0) (R := ρ) (mem_ball_self hρ)
    simpa using this
  · have := circleIntegral.integral_sub_zpow_of_ne hm 0 0 ρ
    simpa using this

theorem sphere_ne_zero {ρ : ℝ} (hρ : 0 < ρ) {z : ℂ} (hz : z ∈ sphere (0 : ℂ) ρ) : z ≠ 0 := by
  intro h
  rw [h, mem_sphere, dist_self] at hz
  linarith

theorem two_I_ne : (2 * I : ℂ) ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero

theorem circle_poly_coeff (N k : ℕ) (hk : 2 ≤ k) (hkN : k ≤ N + 1) (ρ : ℝ) (hρ : 0 < ρ)
    (H : (j : ℕ) → 1 ≤ j ∧ j ≤ N + 1 → ℂ) (c1 : ℂ) :
    (∮ z in C(0, ρ), z ^ (k - 1) * (-(I * z) - c1 / (2 * I * z) +
      ∑ j ∈ Finset.Icc 2 k, (if hj : 1 ≤ j ∧ j ≤ N + 1 then H j hj / (2 * I * z) ^ j else 0))) =
      2 * π * I * (H k ⟨by omega, hkN⟩ / (2 * I) ^ k) := by
  have hρ0 : 0 ≤ ρ := hρ.le
  -- pieces
  set A : ℂ → ℂ := fun z => z ^ (k - 1) * (-(I * z)) with hA
  set B : ℂ → ℂ := fun z => z ^ (k - 1) * (c1 / (2 * I * z)) with hB
  set D : ℕ → ℂ → ℂ := fun j z => z ^ (k - 1) *
    (if hj : 1 ≤ j ∧ j ≤ N + 1 then H j hj / (2 * I * z) ^ j else 0) with hDdef
  have hAc : ContinuousOn A (sphere 0 ρ) := by
    apply Continuous.continuousOn; simp only [hA]; fun_prop
  have hBc : ContinuousOn B (sphere 0 ρ) := by
    intro z hz
    have hz0 := sphere_ne_zero hρ hz
    apply ContinuousAt.continuousWithinAt
    simp only [hB]
    exact (continuousAt_id.pow _).mul (continuousAt_const.div (by fun_prop)
      (mul_ne_zero two_I_ne hz0))
  have hDc : ∀ j, ContinuousOn (D j) (sphere 0 ρ) := by
    intro j z hz
    have hz0 := sphere_ne_zero hρ hz
    apply ContinuousAt.continuousWithinAt
    simp only [hDdef]
    by_cases hj : 1 ≤ j ∧ j ≤ N + 1
    · simp only [dif_pos hj]
      exact (continuousAt_id.pow _).mul (continuousAt_const.div (by fun_prop)
        (pow_ne_zero _ (mul_ne_zero two_I_ne hz0)))
    · simp only [dif_neg hj, mul_zero]
      exact continuousAt_const
  have hsplit : (fun z : ℂ => z ^ (k - 1) * (-(I * z) - c1 / (2 * I * z) +
      ∑ j ∈ Finset.Icc 2 k, (if hj : 1 ≤ j ∧ j ≤ N + 1 then H j hj / (2 * I * z) ^ j else 0))) =
      fun z => (A z - B z) + ∑ j ∈ Finset.Icc 2 k, D j z := by
    funext z
    simp only [hA, hB, hDdef]
    rw [mul_add, mul_sub, Finset.mul_sum]
  have hiAB : CircleIntegrable (fun z : ℂ => A z - B z) 0 ρ :=
    ContinuousOn.circleIntegrable hρ0 (by apply ContinuousOn.sub hAc hBc)
  have hiD : CircleIntegrable (fun z : ℂ => ∑ j ∈ Finset.Icc 2 k, D j z) 0 ρ :=
    ContinuousOn.circleIntegrable hρ0 (by
      apply continuousOn_finset_sum _ fun j _ => hDc j)
  have hiA : CircleIntegrable (fun z : ℂ => A z) 0 ρ := ContinuousOn.circleIntegrable hρ0 hAc
  have hiB : CircleIntegrable (fun z : ℂ => B z) 0 ρ := ContinuousOn.circleIntegrable hρ0 hBc
  rw [hsplit, circleIntegral.integral_add hiAB hiD, circleIntegral.integral_sub hiA hiB,
    cint_finset_sum _ _ fun j _ => (hDc j).circleIntegrable hρ0]
  -- A integrates to 0
  have hAint : (∮ z in C(0, ρ), A z) = 0 := by
    have hpt : A = fun z => (-I) * z ^ ((k : ℕ) : ℤ) := by
      funext z
      simp only [hA, zpow_natCast]
      rw [show k = (k - 1) + 1 by omega, pow_succ]
      simp only [Nat.add_sub_cancel]
      ring
    rw [hpt, circleIntegral.integral_const_mul, cint_zpow ρ hρ, if_neg (by omega), mul_zero]
  -- B integrates to 0
  have hBint : (∮ z in C(0, ρ), B z) = 0 := by
    have hpt : EqOn B (fun z => (c1 / (2 * I)) * z ^ (((k - 2 : ℕ)) : ℤ)) (sphere 0 ρ) := by
      intro z hz
      have hz0 := sphere_ne_zero hρ hz
      simp only [hB, zpow_natCast]
      rw [show k - 1 = (k - 2) + 1 by omega, pow_succ]
      field_simp
    rw [circleIntegral.integral_congr hρ0 hpt, circleIntegral.integral_const_mul, cint_zpow ρ hρ,
      if_neg (by omega), mul_zero]
  -- D_j
  have hDint : ∀ j ∈ Finset.Icc 2 k, (∮ z in C(0, ρ), D j z) =
      if j = k then 2 * π * I * (H k ⟨by omega, hkN⟩ / (2 * I) ^ k) else 0 := by
    intro j hjm
    rw [Finset.mem_Icc] at hjm
    have hj : 1 ≤ j ∧ j ≤ N + 1 := ⟨by omega, by omega⟩
    have hpt : EqOn (D j) (fun z => (H j hj / (2 * I) ^ j) * z ^ (((k - 1 : ℕ) : ℤ) - (j : ℤ)))
        (sphere 0 ρ) := by
      intro z hz
      have hz0 := sphere_ne_zero hρ hz
      simp only [hDdef, dif_pos hj]
      rw [zpow_sub₀ hz0, zpow_natCast, zpow_natCast, mul_pow]
      field_simp
    rw [circleIntegral.integral_congr hρ0 hpt, circleIntegral.integral_const_mul, cint_zpow ρ hρ]
    by_cases hjk : j = k
    · subst hjk
      rw [if_pos (by omega), if_pos rfl]
      ring
    · rw [if_neg (by omega), if_neg hjk, mul_zero]
  rw [hAint, hBint, Finset.sum_congr rfl hDint, Finset.sum_ite_eq' (Finset.Icc 2 k) k,
    if_pos (Finset.mem_Icc.2 ⟨hk, le_rfl⟩)]
  ring

theorem trace_from_laurent (N k : ℕ) (hk : 2 ≤ k) (hkN : k ≤ N + 1)
    (F G : ℂ → ℂ) (H : (j : ℕ) → 1 ≤ j ∧ j ≤ N + 1 → ℂ) (C R0 : ℝ)
    (hF : ∀ z : ℂ, R0 ≤ ‖z‖ →
      ‖F z + I * z + H 1 ⟨le_rfl, Nat.succ_le_succ (Nat.zero_le N)⟩ / (2 * I * z) -
        ∑ j ∈ Finset.Icc 2 k,
          (if hj : 1 ≤ j ∧ j ≤ N + 1 then H j hj / (2 * I * z) ^ j else 0)‖ ≤
        C / ‖z‖ ^ (k + 1))
    (ρ : ℕ → ℝ) (hρ : Tendsto ρ atTop atTop)
    (hder : ∀ᶠ ν in atTop, ∀ z ∈ sphere (0 : ℂ) (ρ ν), HasDerivAt F (G z) z)
    (hGc : ∀ᶠ ν in atTop, ContinuousOn G (sphere (0 : ℂ) (ρ ν)))
    (T : ℂ)
    (hT : ∀ᶠ ν in atTop, T = (k : ℂ)⁻¹ * ((1 / (π : ℂ)) * ∮ z in C(0, ρ ν), z ^ k * G z)) :
    T = -((2 * I) ^ (k - 1))⁻¹ * H k ⟨by omega, hkN⟩ := by
  set c1 : ℂ := H 1 ⟨le_rfl, Nat.succ_le_succ (Nat.zero_le N)⟩ with hc1
  set P : ℂ → ℂ := fun z => -(I * z) - c1 / (2 * I * z) +
    ∑ j ∈ Finset.Icc 2 k, (if hj : 1 ≤ j ∧ j ≤ N + 1 then H j hj / (2 * I * z) ^ j else 0) with hPdef
  set L : ℂ := 2 * π * I * (H k ⟨by omega, hkN⟩ / (2 * I) ^ k) with hL
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  -- the eventual facts
  have hev := (hρ.eventually (eventually_ge_atTop (max R0 1))).and (hder.and (hGc.and hT))
  -- remainder bound and the value of T along the sequence
  have hmain : ∀ᶠ ν in atTop,
      T = -(1 / (π : ℂ)) * (L + ∮ z in C(0, ρ ν), z ^ (k - 1) * (F z - P z)) ∧
      ‖∮ z in C(0, ρ ν), z ^ (k - 1) * (F z - P z)‖ ≤ 2 * π * C / ρ ν := by
    filter_upwards [hev] with ν hν
    obtain ⟨hρν, hd, hg, hTν⟩ := hν
    set r := ρ ν with hr
    have hr1 : 1 ≤ r := le_trans (le_max_right _ _) hρν
    have hrR : R0 ≤ r := le_trans (le_max_left _ _) hρν
    have hr0 : 0 < r := by linarith
    have hrabs : |r| = r := abs_of_pos hr0
    have hFc : ContinuousOn F (sphere 0 r) := fun z hz => (hd z hz).continuousAt.continuousWithinAt
    have hPc : ContinuousOn P (sphere 0 r) := by
      intro z hz
      have hz0 := sphere_ne_zero hr0 hz
      apply ContinuousAt.continuousWithinAt
      simp only [hPdef]
      refine ((continuousAt_const.mul continuousAt_id).neg.sub (continuousAt_const.div (by fun_prop)
        (mul_ne_zero two_I_ne hz0))).add ?_
      have hterm : ∀ j : ℕ, ContinuousAt (fun z : ℂ =>
          (if hj : 1 ≤ j ∧ j ≤ N + 1 then H j hj / (2 * I * z) ^ j else 0)) z := by
        intro j
        by_cases hj : 1 ≤ j ∧ j ≤ N + 1
        · simp only [dif_pos hj]
          exact continuousAt_const.div (by fun_prop) (pow_ne_zero _ (mul_ne_zero two_I_ne hz0))
        · simp only [dif_neg hj]
          exact continuousAt_const
      exact tendsto_finset_sum _ fun j _ => hterm j
    have hpow : ∀ m : ℕ, ContinuousOn (fun z : ℂ => z ^ m) (sphere 0 r) :=
      fun m => (continuous_pow m).continuousOn
    -- integration by parts on the circle
    have hparts : (∮ z in C(0, r), z ^ k * G z) = -(k : ℂ) * ∮ z in C(0, r), z ^ (k - 1) * F z := by
      have h0 := circleIntegral.integral_eq_zero_of_hasDerivWithinAt' (c := 0) (R := r)
        (f := fun z => z ^ k * F z) (f' := fun z => ((k : ℂ) * z ^ (k - 1)) * F z + z ^ k * G z)
        (fun z hz => by
          rw [hrabs] at hz
          exact ((hasDerivAt_pow k z).mul (hd z hz)).hasDerivWithinAt)
      have hi1 : CircleIntegrable (fun z : ℂ => ((k : ℂ) * z ^ (k - 1)) * F z) 0 r :=
        ContinuousOn.circleIntegrable hr0.le (by
          apply ContinuousOn.mul _ hFc
          exact (continuous_const.mul (continuous_pow _)).continuousOn)
      have hi2 : CircleIntegrable (fun z : ℂ => z ^ k * G z) 0 r :=
        ContinuousOn.circleIntegrable hr0.le (by
          apply ContinuousOn.mul _ hg
          exact hpow k)
      rw [circleIntegral.integral_add hi1 hi2] at h0
      have h1 : (∮ z in C(0, r), ((k : ℂ) * z ^ (k - 1)) * F z) =
          (k : ℂ) * ∮ z in C(0, r), z ^ (k - 1) * F z := by
        rw [← circleIntegral.integral_const_mul]
        congr 1
        funext z
        ring
      rw [h1] at h0
      linear_combination h0
    -- split F = P + (F − P)
    have hsplitF : (∮ z in C(0, r), z ^ (k - 1) * F z) =
        L + ∮ z in C(0, r), z ^ (k - 1) * (F z - P z) := by
      have e : (fun z => z ^ (k - 1) * F z) = fun z => z ^ (k - 1) * P z + z ^ (k - 1) * (F z - P z) := by
        funext z; ring
      have hi1 : CircleIntegrable (fun z : ℂ => z ^ (k - 1) * P z) 0 r :=
        ContinuousOn.circleIntegrable hr0.le (by
          apply ContinuousOn.mul _ hPc
          exact hpow _)
      have hi2 : CircleIntegrable (fun z : ℂ => z ^ (k - 1) * (F z - P z)) 0 r :=
        ContinuousOn.circleIntegrable hr0.le (by
          apply ContinuousOn.mul _ (hFc.sub hPc)
          exact hpow _)
      rw [e, circleIntegral.integral_add hi1 hi2]
      congr 1
      exact circle_poly_coeff N k hk hkN r hr0 H c1
    refine ⟨?_, ?_⟩
    · rw [hTν, hparts, hsplitF]
      field_simp
    · have hb : ∀ z ∈ sphere (0 : ℂ) r, ‖z ^ (k - 1) * (F z - P z)‖ ≤ r ^ (k - 1) * (C / r ^ (k + 1)) := by
        intro z hz
        have hzn : ‖z‖ = r := by simpa using hz
        rw [norm_mul, norm_pow, hzn]
        have hE : ‖F z - P z‖ ≤ C / r ^ (k + 1) := by
          have := hF z (by rw [hzn]; exact hrR)
          rw [hzn] at this
          have e : F z - P z = F z + I * z + c1 / (2 * I * z) - ∑ j ∈ Finset.Icc 2 k,
              (if hj : 1 ≤ j ∧ j ≤ N + 1 then H j hj / (2 * I * z) ^ j else 0) := by
            simp only [hPdef]; ring
          rw [e]; exact this
        exact mul_le_mul_of_nonneg_left hE (by positivity)
      have := circleIntegral.norm_integral_le_of_norm_le_const hr0.le hb
      calc _ ≤ 2 * π * r * (r ^ (k - 1) * (C / r ^ (k + 1))) := this
        _ = 2 * π * C / r := by
          have hrk : r ^ (k + 1) = r * r ^ (k - 1) * r := by
            rw [show k + 1 = (k - 1) + 1 + 1 by omega, pow_succ, pow_succ]; ring
          rw [hrk]
          field_simp
  -- limit
  have hC : Tendsto (fun ν => 2 * π * C / ρ ν) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hρ
  have hE : Tendsto (fun ν => ∮ z in C(0, ρ ν), z ^ (k - 1) * (F z - P z)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (hmain.mono fun ν h => h.2) hC
  have hlim : Tendsto (fun ν => -(1 / (π : ℂ)) * (L + ∮ z in C(0, ρ ν), z ^ (k - 1) * (F z - P z)))
      atTop (𝓝 (-(1 / (π : ℂ)) * (L + 0))) := (tendsto_const_nhds.add hE).const_mul _
  have hTv : T = -(1 / (π : ℂ)) * (L + 0) :=
    tendsto_nhds_unique (tendsto_const_nhds.congr' (hmain.mono fun ν h => h.1)) hlim
  rw [hTv, add_zero, hL]
  have hpk : (2 * I : ℂ) ^ k = (2 * I) ^ (k - 1) * (2 * I) := by
    rw [← pow_succ, show k - 1 + 1 = k by omega]
  rw [hpk]
  have h2 : (2 * I : ℂ) ^ (k - 1) ≠ 0 := pow_ne_zero _ two_I_ne
  field_simp <;> ring

theorem circle_zero_of_punctured (c a : ℂ) (R : ℝ) (hR : 0 < R) (f g : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (ball c R)) (ha : a ∈ ball c R)
    (hfg : ∀ z ∈ ball c R, z ≠ a → f z = g z)
    (hg : ∀ z ∈ sphere c R, AnalyticAt ℂ g z) :
    (∮ z in C(c, R), g z) = 0 := by
  classical
  set h : ℂ → ℂ := fun z => if z ∈ ball c R then f z else g z with hh
  have hdiff : ∀ z ∈ closedBall c R, DifferentiableAt ℂ h z := by
    intro z hz
    by_cases hzb : z ∈ ball c R
    · have : h =ᶠ[𝓝 z] f := by
        filter_upwards [isOpen_ball.mem_nhds hzb] with w hw
        simp only [hh, if_pos hw]
      exact ((hf z hzb).differentiableAt).congr_of_eventuallyEq this
    · have hzs : z ∈ sphere c R := by
        rw [mem_sphere]; rw [mem_closedBall] at hz; rw [mem_ball] at hzb
        linarith
      have hza : z ≠ a := by
        rintro rfl; exact hzb ha
      have : h =ᶠ[𝓝 z] g := by
        filter_upwards [isOpen_ne.mem_nhds hza] with w hw
        simp only [hh]
        split_ifs with hwb
        · exact hfg w hwb hw
        · rfl
      exact ((hg z hzs).differentiableAt).congr_of_eventuallyEq this
  have h0 : (∮ z in C(c, R), h z) = 0 :=
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le countable_empty
      (fun z hz => (hdiff z hz).continuousAt.continuousWithinAt)
      (fun z hz => hdiff z (ball_subset_closedBall hz.1))
  rw [← h0]
  refine circleIntegral.integral_congr hR.le fun z hz => ?_
  have hzb : z ∉ ball c R := by
    rw [mem_sphere] at hz; rw [mem_ball]; linarith
  simp only [hh, if_neg hzb]

end NlsGge.ThirdConsultation.M017Cx
