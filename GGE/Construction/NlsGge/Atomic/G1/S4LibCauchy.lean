import Mathlib

                                                                                              
                                                                          
                                                                 
                                                                                                  
                                                                                           
set_option autoImplicit false
open Metric Set

namespace NlsGge.S4Lib

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- First-derivative Cauchy estimate on a closed ball. -/
theorem norm_fderiv_apply_le_of_analyticOnNhd_closedBall
    {f : E → F} {a y : E} {R R' M : ℝ} (hR' : R' < R)
    (hf : AnalyticOnNhd ℂ f (closedBall a R)) (hM : ∀ z ∈ closedBall a R, ‖f z‖ ≤ M)
    (hy : y ∈ closedBall a R') (w : E) :
    ‖fderiv ℂ f y w‖ ≤ M * ‖w‖ / (R - R') := by
  have hr : 0 < R - R' := by linarith
  by_cases hw : w = 0
  · subst hw; simp only [map_zero, norm_zero, mul_zero, zero_div]; exact le_rfl
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  set ρ : ℝ := (R - R') / ‖w‖ with hρ
  have hρpos : 0 < ρ := div_pos hr hwpos
  have hmem : ∀ s : ℂ, ‖s‖ ≤ ρ → y + s • w ∈ closedBall a R := by
    intro s hs
    rw [mem_closedBall, dist_eq_norm] at hy ⊢
    calc ‖y + s • w - a‖ = ‖(y - a) + s • w‖ := by congr 1; abel
      _ ≤ ‖y - a‖ + ‖s • w‖ := norm_add_le _ _
      _ ≤ R' + ρ * ‖w‖ := by
        rw [norm_smul]; gcongr
      _ = R := by rw [hρ]; field_simp; ring
  have hya : y ∈ closedBall a R := by
    have := hmem 0 (by simp [hρpos.le])
    simpa using this
  have hlin : ∀ s : ℂ, AnalyticAt ℂ (fun s : ℂ => y + s • w) s := by
    intro s
    exact analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hφ : DifferentiableOn ℂ (fun s : ℂ => f (y + s • w)) (closedBall (0 : ℂ) ρ) := by
    intro s hs
    rw [mem_closedBall, dist_zero_right] at hs
    exact (DifferentiableAt.comp s (g := f) (f := fun s : ℂ => y + s • w)
      (hf _ (hmem s hs)).differentiableAt (hlin s).differentiableAt).differentiableWithinAt
  have hdc : DiffContOnCl ℂ (fun s : ℂ => f (y + s • w)) (ball (0 : ℂ) ρ) := by
    refine ⟨hφ.mono ball_subset_closedBall, ?_⟩
    rw [closure_ball _ hρpos.ne']
    exact hφ.continuousOn
  have hsph : ∀ s ∈ sphere (0 : ℂ) ρ, ‖f (y + s • w)‖ ≤ M := by
    intro s hs
    rw [mem_sphere, dist_zero_right] at hs
    exact hM _ (hmem s hs.le)
  have hd := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρpos hdc hsph
  have hfd : DifferentiableAt ℂ f y := (hf y hya).differentiableAt
  have h1 : HasDerivAt (fun s : ℂ => y + s • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const w).const_add y
  have h2 : HasDerivAt (fun s : ℂ => f (y + s • w)) (fderiv ℂ f y w) 0 := by
    have h1' : HasDerivAt (fun s : ℂ => y + s • w) w 0 := h1
    have hfd' : HasFDerivAt f (fderiv ℂ f y) (y + (0 : ℂ) • w) := by
      simpa using hfd.hasFDerivAt
    exact hfd'.comp_hasDerivAt 0 h1'
  rw [h2.deriv] at hd
  calc ‖fderiv ℂ f y w‖ ≤ M / ρ := hd
    _ = M * ‖w‖ / (R - R') := by rw [hρ]; field_simp

/-- Closed-ball Cauchy estimate for the `n`-th derivative: `‖D^n f(a)‖ R^n ≤ M n^n`. -/
theorem norm_iteratedFDeriv_mul_pow_le_closedBall (n : ℕ) :
    ∀ {f : E → F} {a : E} {R M : ℝ}, 0 ≤ R → AnalyticOnNhd ℂ f (closedBall a R) →
      (∀ z ∈ closedBall a R, ‖f z‖ ≤ M) →
      ‖iteratedFDeriv ℂ n f a‖ * R ^ n ≤ M * (n : ℝ) ^ n := by
  induction n with
  | zero =>
    intro f a R M hR hf hM
    have := hM a (mem_closedBall_self hR)
    simpa using this
  | succ n ih =>
    intro f a R M hR hf hM
    have hMa : 0 ≤ M := (norm_nonneg _).trans (hM a (mem_closedBall_self hR))
    rcases hR.eq_or_lt with h0 | hpos
    · have h00 : (0 : ℝ) ^ (n + 1) = 0 := by simp
      rw [← h0, h00, mul_zero]; positivity
    · have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      set R' : ℝ := R * n / (n + 1) with hR'
      have hR'0 : 0 ≤ R' := by positivity
      have hR'lt : R' < R := by
        rw [hR', div_lt_iff₀ hn1]; nlinarith
      have hRR' : R - R' = R / (n + 1) := by rw [hR']; field_simp; ring
      have hfd : AnalyticOnNhd ℂ (fderiv ℂ f) (closedBall a R) := hf.fderiv
      -- bound for the derivative family
      have key : ∀ w : E, ‖iteratedFDeriv ℂ n (fun y => fderiv ℂ f y w) a‖ * R ^ n ≤
          (M * ‖w‖ * ((n : ℝ) + 1) / R) * ((n : ℝ) + 1) ^ n := by
        intro w
        have hg : AnalyticOnNhd ℂ (fun y => fderiv ℂ f y w) (closedBall a R') := by
          intro y hy
          have hy' : AnalyticAt ℂ (fderiv ℂ f) y :=
            hfd y (closedBall_subset_closedBall hR'lt.le hy)
          exact ((ContinuousLinearMap.apply ℂ F w).analyticAt _).comp hy'
        have hgb : ∀ z ∈ closedBall a R', ‖fderiv ℂ f z w‖ ≤ M * ‖w‖ * ((n : ℝ) + 1) / R := by
          intro z hz
          have := norm_fderiv_apply_le_of_analyticOnNhd_closedBall hR'lt hf hM hz w
          rw [hRR'] at this
          calc ‖fderiv ℂ f z w‖ ≤ M * ‖w‖ / (R / ((n : ℝ) + 1)) := this
            _ = M * ‖w‖ * ((n : ℝ) + 1) / R := by field_simp
        have H := ih hR'0 hg hgb
        rcases Nat.eq_zero_or_pos n with hn | hn
        · subst hn; simpa using H
        · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
          have hRp : R' ^ n = R ^ n * (n : ℝ) ^ n / ((n : ℝ) + 1) ^ n := by
            rw [hR', div_pow, mul_pow]
          rw [hRp] at H
          have hnn : (0 : ℝ) < (n : ℝ) ^ n := by positivity
          have hn1n : (0 : ℝ) < ((n : ℝ) + 1) ^ n := by positivity
          set X := ‖iteratedFDeriv ℂ n (fun y => fderiv ℂ f y w) a‖
          set Mg := M * ‖w‖ * ((n : ℝ) + 1) / R
          have : X * R ^ n * (n : ℝ) ^ n ≤ Mg * ((n : ℝ) + 1) ^ n * (n : ℝ) ^ n := by
            have h2 : X * (R ^ n * (n : ℝ) ^ n / ((n : ℝ) + 1) ^ n) * ((n : ℝ) + 1) ^ n
                ≤ Mg * (n : ℝ) ^ n * ((n : ℝ) + 1) ^ n :=
              mul_le_mul_of_nonneg_right H hn1n.le
            have e1 : X * (R ^ n * (n : ℝ) ^ n / ((n : ℝ) + 1) ^ n) * ((n : ℝ) + 1) ^ n
                = X * R ^ n * (n : ℝ) ^ n := by field_simp
            nlinarith [h2, e1]
          exact le_of_mul_le_mul_right this hnn
      -- assemble the operator norm bound
      set C : ℝ := M * ((n : ℝ) + 1) ^ (n + 1) / R ^ (n + 1) with hC
      have hC0 : 0 ≤ C := by positivity
      have hop : ‖iteratedFDeriv ℂ (n + 1) f a‖ ≤ C := by
        refine ContinuousMultilinearMap.opNorm_le_bound hC0 (fun m => ?_)
        have hcd : ContDiffAt ℂ n (fderiv ℂ f) a :=
          (hfd a (mem_closedBall_self hR)).contDiffAt
        have hL := (ContinuousLinearMap.apply ℂ F (m (Fin.last n))).iteratedFDeriv_comp_left
          hcd le_rfl
        have hm : iteratedFDeriv ℂ (n + 1) f a m =
            iteratedFDeriv ℂ n (fun y => fderiv ℂ f y (m (Fin.last n))) a (Fin.init m) := by
          have hL' : iteratedFDeriv ℂ n (fun y => fderiv ℂ f y (m (Fin.last n))) a =
              (ContinuousLinearMap.apply ℂ F (m (Fin.last n))).compContinuousMultilinearMap
                (iteratedFDeriv ℂ n (fderiv ℂ f) a) := hL
          rw [iteratedFDeriv_succ_apply_right, hL']
          rfl
        rw [hm]
        have h1 := (iteratedFDeriv ℂ n (fun y => fderiv ℂ f y (m (Fin.last n))) a).le_opNorm
          (Fin.init m)
        have h2 := key (m (Fin.last n))
        have hRn : (0 : ℝ) < R ^ n := by positivity
        have h3 : ‖iteratedFDeriv ℂ n (fun y => fderiv ℂ f y (m (Fin.last n))) a‖ ≤
            C * ‖m (Fin.last n)‖ := by
          have : ‖iteratedFDeriv ℂ n (fun y => fderiv ℂ f y (m (Fin.last n))) a‖ ≤
              (M * ‖m (Fin.last n)‖ * ((n : ℝ) + 1) / R) * ((n : ℝ) + 1) ^ n / R ^ n := by
            rw [le_div_iff₀ hRn]; exact h2
          refine this.trans (le_of_eq ?_)
          rw [hC]; field_simp; ring
        rw [Fin.prod_univ_castSucc]
        calc ‖iteratedFDeriv ℂ n (fun y => fderiv ℂ f y (m (Fin.last n))) a (Fin.init m)‖
            ≤ ‖iteratedFDeriv ℂ n (fun y => fderiv ℂ f y (m (Fin.last n))) a‖ *
              ∏ i, ‖Fin.init m i‖ := h1
          _ ≤ (C * ‖m (Fin.last n)‖) * ∏ i : Fin n, ‖m (Fin.castSucc i)‖ := by
            gcongr with i hi
            exact le_of_eq rfl
          _ = C * ((∏ i : Fin n, ‖m (Fin.castSucc i)‖) * ‖m (Fin.last n)‖) := by ring
      have hRn1 : (0 : ℝ) < R ^ (n + 1) := by positivity
      calc ‖iteratedFDeriv ℂ (n + 1) f a‖ * R ^ (n + 1) ≤ C * R ^ (n + 1) :=
            mul_le_mul_of_nonneg_right hop hRn1.le
        _ = M * ((n + 1 : ℕ) : ℝ) ^ (n + 1) := by
            rw [hC]; push_cast; field_simp

/-- Open-ball Cauchy estimate for the `n`-th derivative of an analytic map bounded on a ball:
`‖D^n f(a)‖ R^n ≤ M n^n`. -/
theorem norm_iteratedFDeriv_mul_pow_le (n : ℕ) {f : E → F} {a : E} {R M : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (ball a R)) (hM : ∀ z ∈ ball a R, ‖f z‖ ≤ M) :
    ‖iteratedFDeriv ℂ n f a‖ * R ^ n ≤ M * (n : ℝ) ^ n := by
  have hev : ∀ᶠ t in nhdsWithin R (Set.Iio R), ‖iteratedFDeriv ℂ n f a‖ * t ^ n ≤ M * (n : ℝ) ^ n := by
    filter_upwards [Ioo_mem_nhdsLT hR] with t ht
    exact norm_iteratedFDeriv_mul_pow_le_closedBall n ht.1.le
      (hf.mono (closedBall_subset_ball ht.2)) (fun z hz => hM z (closedBall_subset_ball ht.2 hz))
  have hcont : Filter.Tendsto (fun t : ℝ => ‖iteratedFDeriv ℂ n f a‖ * t ^ n)
      (nhdsWithin R (Set.Iio R)) (nhds (‖iteratedFDeriv ℂ n f a‖ * R ^ n)) :=
    ((continuous_const.mul (continuous_pow n)).tendsto R).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto hcont hev

/-- Cauchy coefficient estimate with absolute constant `e`:
`‖D^n f(a)‖ ≤ n! * e^n * M / R^n`. -/
theorem norm_iteratedFDeriv_le_factorial_mul_exp_pow (n : ℕ) {f : E → F} {a : E} {R M : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (ball a R)) (hM : ∀ z ∈ ball a R, ‖f z‖ ≤ M) :
    ‖iteratedFDeriv ℂ n f a‖ ≤ (n.factorial : ℝ) * Real.exp 1 ^ n * M / R ^ n := by
  have h := norm_iteratedFDeriv_mul_pow_le n hR hf hM
  have hMa : 0 ≤ M := by
    have := hM a (mem_ball_self hR)
    exact (norm_nonneg _).trans this
  have hRn : (0 : ℝ) < R ^ n := by positivity
  have hnn : (n : ℝ) ^ n ≤ (n.factorial : ℝ) * Real.exp 1 ^ n := by
    have h1 := Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) n
    have hf0 : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
    rw [div_le_iff₀ hf0] at h1
    have h2 : Real.exp (n : ℝ) = Real.exp 1 ^ n := by
      rw [← Real.exp_nat_mul, mul_one]
    rw [h2] at h1; linarith
  rw [le_div_iff₀ hRn]
  calc ‖iteratedFDeriv ℂ n f a‖ * R ^ n ≤ M * (n : ℝ) ^ n := h
    _ ≤ M * ((n.factorial : ℝ) * Real.exp 1 ^ n) := mul_le_mul_of_nonneg_left hnn hMa
    _ = (n.factorial : ℝ) * Real.exp 1 ^ n * M := by ring

/-- Taylor coefficient form: `‖(n!)⁻¹ • D^n f(a)‖ ≤ M (e / R)^n`. -/
theorem norm_inv_factorial_smul_iteratedFDeriv_le (n : ℕ) {f : E → F} {a : E} {R M : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (ball a R)) (hM : ∀ z ∈ ball a R, ‖f z‖ ≤ M) :
    ‖((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n f a‖ ≤ M * (Real.exp 1 / R) ^ n := by
  have h := norm_iteratedFDeriv_le_factorial_mul_exp_pow n hR hf hM
  have hf0 : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  rw [norm_smul, norm_inv, Complex.norm_natCast, div_pow]
  rw [inv_mul_le_iff₀ hf0]
  calc ‖iteratedFDeriv ℂ n f a‖ ≤ (n.factorial : ℝ) * Real.exp 1 ^ n * M / R ^ n := h
    _ = (n.factorial : ℝ) * (M * (Real.exp 1 ^ n / R ^ n)) := by ring

end

end NlsGge.S4Lib
