import Mathlib

/-! # Normally convergent series of analytic functions on a normed `ℂ`-space (batch 38, L02b-3a)

Mathlib has no several-variable "uniform limit of holomorphic is analytic" theorem.  We prove
`analyticAt_tsum_of_bound38`: if `f j` are `ℂ`-analytic on `closedBall x r` with
`‖f j‖ ≤ m j` there and `m` is summable, then `y ↦ ∑' j, f j y` is analytic at `x`.
Route: iterated Cauchy estimates `‖Dⁿ f(x) m‖ rⁿ ≤ M nⁿ ∏‖mᵢ‖` (by induction, using the one-variable
Cauchy estimate for `fderiv`), Taylor coefficients `q n = (n!)⁻¹ Dⁿ f(x)` with
`‖q n‖ ≤ M (e/r)ⁿ` (`nⁿ/n! ≤ eⁿ`), identity theorem to show `q` is the power series of `f` on
`ball x (r/e)`, then summation of the series (no polarization needed). -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.AnalyticTsum38

open Metric Set Filter Topology
open scoped Nat

universe u

section Cauchy

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- One-variable Cauchy estimate for the Fréchet derivative. -/
theorem norm_fderiv_le_of_closedBall38 [CompleteSpace F] {f : E → F} {x y : E} {r r' R M : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall x r))
    (hb : ∀ z ∈ closedBall x r, ‖f z‖ ≤ M) (hy : y ∈ closedBall x r') (hR : 0 < R)
    (hrr : r' + R ≤ r) : ‖fderiv ℂ f y‖ ≤ M / R := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hb y (closedBall_subset_closedBall (by linarith [hR]) hy))
  refine ContinuousLinearMap.opNorm_le_of_unit_norm (div_nonneg hM hR.le) ?_
  intro v hv
  have hmem : ∀ t : ℂ, ‖t‖ ≤ R → y + t • v ∈ closedBall x r := by
    intro t ht
    rw [mem_closedBall, dist_eq_norm] at hy ⊢
    calc ‖y + t • v - x‖ = ‖(y - x) + t • v‖ := by congr 1; abel
      _ ≤ ‖y - x‖ + ‖t • v‖ := norm_add_le _ _
      _ ≤ r' + R := by rw [norm_smul, hv]; linarith
      _ ≤ r := hrr
  set g : ℂ → F := fun t => f (y + t • v) with hg
  have hgd : ∀ t : ℂ, ‖t‖ ≤ R → HasDerivAt g (fderiv ℂ f (y + t • v) v) t := by
    intro t ht
    have h1 : HasFDerivAt f (fderiv ℂ f (y + t • v)) (y + t • v) :=
      ((hf _ (hmem t ht)).differentiableAt).hasFDerivAt
    have h2 : HasDerivAt (fun t : ℂ => y + t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add y
    exact h1.comp_hasDerivAt t h2
  have hdiff : DiffContOnCl ℂ g (ball (0 : ℂ) R) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball _ hR.ne']
    intro t ht
    exact (hgd t (by simpa using ht)).differentiableAt.differentiableWithinAt
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hdiff (C := M) (by
    intro t ht
    have : ‖t‖ = R := by simpa using ht
    exact hb _ (hmem t this.le))
  have hd0 : deriv g 0 = fderiv ℂ f y v := by
    have := (hgd 0 (by simp [hR.le])).deriv
    simpa using this
  rwa [hd0] at this

omit [NormedAddCommGroup F] [NormedSpace ℂ F] in
/-- Iterated Cauchy estimates: `‖Dⁿ f(x)(m)‖ rⁿ ≤ M nⁿ ∏‖mᵢ‖`. -/
theorem norm_iteratedFDeriv_le38 :
    ∀ (n : ℕ) {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
      [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
      (f : E → F) (x : E) (r M : ℝ), 0 ≤ r → AnalyticOnNhd ℂ f (closedBall x r) →
      (∀ z ∈ closedBall x r, ‖f z‖ ≤ M) → ∀ m : Fin n → E,
      ‖iteratedFDeriv ℂ n f x m‖ * r ^ n ≤ M * (n : ℝ) ^ n * ∏ i, ‖m i‖ := by
  intro n
  induction n with
  | zero =>
    intro E F _ _ _ _ _ f x r M hr hf hb m
    have := hb x (mem_closedBall_self hr)
    simpa using this
  | succ n ih =>
    intro E F _ _ _ _ _ f x r M hr hf hb m
    have hM : 0 ≤ M := (norm_nonneg _).trans (hb x (mem_closedBall_self hr))
    rcases hr.eq_or_lt with h0 | hpos
    · subst h0
      simp only [zero_pow (Nat.succ_ne_zero n), mul_zero]
      positivity
    set R : ℝ := r / (n + 1) with hR
    set r' : ℝ := r * n / (n + 1) with hr'
    have hn1 : (0:ℝ) < n + 1 := by positivity
    have hRpos : 0 < R := by positivity
    have hr'0 : 0 ≤ r' := by positivity
    have hrr : r' + R = r := by rw [hr', hR]; field_simp
    have hsub : closedBall x r' ⊆ closedBall x r := closedBall_subset_closedBall (by linarith)
    have hfd : AnalyticOnNhd ℂ (fderiv ℂ f) (closedBall x r') := (hf.fderiv).mono hsub
    have hbd : ∀ z ∈ closedBall x r', ‖fderiv ℂ f z‖ ≤ M / R := fun z hz =>
      norm_fderiv_le_of_closedBall38 hf hb hz hRpos hrr.le
    have key := ih (fun y => fderiv ℂ f y) x r' (M / R) hr'0 hfd hbd (Fin.init m)
    rw [iteratedFDeriv_succ_apply_right]
    have h1 : ‖iteratedFDeriv ℂ n (fun y => fderiv ℂ f y) x (Fin.init m) (m (Fin.last n))‖ ≤
        ‖iteratedFDeriv ℂ n (fun y => fderiv ℂ f y) x (Fin.init m)‖ * ‖m (Fin.last n)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have hnn : (0:ℝ) < (n:ℝ) ^ n := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · exact pow_pos (by exact_mod_cast hn) _
    have hrn : r ^ n * (n:ℝ) ^ n = r' ^ n * ((n:ℝ) + 1) ^ n := by
      rw [hr', div_pow, mul_pow]; field_simp
    have hprod : ∏ i : Fin (n+1), ‖m i‖ = (∏ i : Fin n, ‖Fin.init m i‖) * ‖m (Fin.last n)‖ := by
      rw [Fin.prod_univ_castSucc]; rfl
    rw [hprod]
    set A := ‖iteratedFDeriv ℂ n (fun y => fderiv ℂ f y) x (Fin.init m)‖
    set P := ∏ i : Fin n, ‖Fin.init m i‖
    set a := ‖m (Fin.last n)‖
    have hA : 0 ≤ A := norm_nonneg _
    have hP : 0 ≤ P := Finset.prod_nonneg fun i _ => norm_nonneg _
    have ha : 0 ≤ a := norm_nonneg _
    have hrR : r / R = (n:ℝ) + 1 := by rw [hR]; field_simp
    have hA1 : A * r ^ (n+1) * (n:ℝ) ^ n ≤ M * ((n:ℝ) + 1) ^ (n + 1) * P * (n:ℝ) ^ n := by
      have e1 : A * r ^ (n+1) * (n:ℝ) ^ n = r * (A * r' ^ n) * ((n:ℝ) + 1) ^ n := by
        calc A * r ^ (n+1) * (n:ℝ) ^ n = r * A * (r ^ n * (n:ℝ) ^ n) := by ring
          _ = _ := by rw [hrn]; ring
      rw [e1]
      calc r * (A * r' ^ n) * ((n:ℝ) + 1) ^ n
          ≤ r * (M / R * (n:ℝ) ^ n * P) * ((n:ℝ) + 1) ^ n := by gcongr
        _ = (r / R) * M * (n:ℝ) ^ n * P * ((n:ℝ) + 1) ^ n := by ring
        _ = _ := by rw [hrR]; ring
    have hA2 : A * r ^ (n+1) ≤ M * ((n:ℝ) + 1) ^ (n + 1) * P := le_of_mul_le_mul_right hA1 hnn
    have hD : ‖iteratedFDeriv ℂ n (fun y => fderiv ℂ f y) x (Fin.init m) (m (Fin.last n))‖ * r ^ (n+1)
        ≤ A * a * r ^ (n+1) := mul_le_mul_of_nonneg_right h1 (by positivity)
    push_cast
    calc _ ≤ A * a * r ^ (n+1) := hD
      _ = (A * r ^ (n+1)) * a := by ring
      _ ≤ (M * ((n:ℝ) + 1) ^ (n + 1) * P) * a := mul_le_mul_of_nonneg_right hA2 ha
      _ = _ := by ring


variable [CompleteSpace F]

/-- Normalised iterated derivatives: the Taylor coefficient series at `x`. -/
def taylorCoeff38 (f : E → F) (x : E) (n : ℕ) : E [×n]→L[ℂ] F :=
  ((n ! : ℂ)⁻¹) • iteratedFDeriv ℂ n f x

theorem norm_taylorCoeff_le38 {f : E → F} {x : E} {r M : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (closedBall x r)) (hb : ∀ z ∈ closedBall x r, ‖f z‖ ≤ M) (n : ℕ) :
    ‖taylorCoeff38 f x n‖ ≤ M * (Real.exp 1 / r) ^ n := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hb x (mem_closedBall_self hr.le))
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
  have h := norm_iteratedFDeriv_le38 n f x r M hr.le hf hb m
  have hfac : (0:ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hrn : 0 < r ^ n := pow_pos hr n
  have hexp : (n:ℝ) ^ n / (n ! : ℝ) ≤ Real.exp 1 ^ n := by
    have := Real.pow_div_factorial_le_exp (n:ℝ) (Nat.cast_nonneg n) n
    calc (n:ℝ) ^ n / (n ! : ℝ) ≤ Real.exp n := this
      _ = Real.exp 1 ^ n := by rw [← Real.exp_nat_mul]; simp
  have hP : 0 ≤ ∏ i, ‖m i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
  have e1 : ‖taylorCoeff38 f x n m‖ = ‖iteratedFDeriv ℂ n f x m‖ / (n ! : ℝ) := by
    simp [taylorCoeff38, norm_smul, div_eq_inv_mul]
  rw [e1, div_le_iff₀ hfac]
  have h2 : ‖iteratedFDeriv ℂ n f x m‖ ≤ M * (n:ℝ) ^ n * (∏ i, ‖m i‖) / r ^ n := by
    rw [le_div_iff₀ hrn]; exact h
  calc ‖iteratedFDeriv ℂ n f x m‖ ≤ M * (n:ℝ) ^ n * (∏ i, ‖m i‖) / r ^ n := h2
    _ = M * ((n:ℝ) ^ n / (n ! : ℝ)) / r ^ n * (∏ i, ‖m i‖) * (n ! : ℝ) := by
        field_simp
    _ ≤ M * (Real.exp 1 ^ n) / r ^ n * (∏ i, ‖m i‖) * (n ! : ℝ) := by gcongr
    _ = _ := by rw [div_pow]; ring

theorem hasSum_taylor38 {f : E → F} {x : E} {r M : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (closedBall x r)) (hb : ∀ z ∈ closedBall x r, ‖f z‖ ≤ M)
    {y : E} (hy : ‖y‖ < r / Real.exp 1) :
    HasSum (fun n => taylorCoeff38 f x n (fun _ => y)) (f (x + y)) := by
  have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.2 one_pos
  set ρ : ℝ := r / Real.exp 1 with hρ
  have hρpos : 0 < ρ := by positivity
  have hρr : ρ < r := by rw [hρ, div_lt_iff₀ (by positivity)]; nlinarith
  set q : FormalMultilinearSeries ℂ E F := taylorCoeff38 f x with hq
  have hrad : ENNReal.ofReal ρ ≤ q.radius := by
    have := q.le_radius_of_bound (r := ⟨ρ, hρpos.le⟩) (C := M) (fun n => by
      have := norm_taylorCoeff_le38 hr hf hb n
      calc ‖q n‖ * ((⟨ρ, hρpos.le⟩ : NNReal) : ℝ) ^ n ≤ M * (Real.exp 1 / r) ^ n * ρ ^ n := by
            gcongr
        _ = M := by
            rw [mul_assoc, ← mul_pow, hρ]
            have : Real.exp 1 / r * (r / Real.exp 1) = 1 := by field_simp
            rw [this]; simp)
    rwa [ENNReal.ofReal_eq_coe_nnreal hρpos.le]
  have hqpos : 0 < q.radius := lt_of_lt_of_le (by simpa using hρpos) hrad
  have hball := q.hasFPowerSeriesOnBall hqpos
  -- identity theorem
  have hU : AnalyticOnNhd ℂ q.sum (ball (0 : E) ρ) := by
    refine hball.analyticOnNhd.mono ?_
    intro z hz
    refine lt_of_lt_of_le ?_ hrad
    rw [edist_zero_right]; rw [mem_ball_zero_iff] at hz
    rw [← ofReal_norm] ; exact ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hz, hρpos⟩
  have hV : AnalyticOnNhd ℂ (fun z => f (x + z)) (ball (0 : E) ρ) := by
    intro z hz
    refine (hf (x + z) ?_).comp (analyticAt_const.add analyticAt_id)
    rw [mem_closedBall, dist_eq_norm]; simp only [add_sub_cancel_left]
    rw [mem_ball_zero_iff] at hz; linarith
  obtain ⟨p, r0, hp⟩ := (hf x (mem_closedBall_self hr.le))
  have hloc : q.sum =ᶠ[𝓝 (0:E)] fun z => f (x + z) := by
    filter_upwards [Metric.eball_mem_nhds (0:E) hp.r_pos] with z hz
    have hs := hp.hasSum hz
    have hqp : ∀ n, q n (fun _ => z) = p n (fun _ => z) := by
      intro n
      have h1 := hp.factorial_smul (y := z) n
      have hfac : ((n ! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero n)
      simp only [hq, taylorCoeff38, smul_apply]
      rw [← h1, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hfac, one_smul]
    have : HasSum (fun n => q n (fun _ => z)) (f (x + z)) := by
      simpa only [hqp] using hs
    exact this.tsum_eq
  have heq := hU.eqOn_of_preconnected_of_eventuallyEq hV (convex_ball _ _).isPreconnected
    (mem_ball_self hρpos) hloc
  have hy' : y ∈ ball (0:E) ρ := by rwa [mem_ball_zero_iff]
  have hmem : y ∈ Metric.eball (0:E) q.radius := by
    refine lt_of_lt_of_le ?_ hrad
    rw [edist_zero_right, ← ofReal_norm]
    exact ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hy, hρpos⟩
  have := q.hasSum hmem
  rwa [heq hy'] at this

omit [CompleteSpace F] in
theorem norm_taylorCoeff_apply_le38 {n : ℕ} (c : E [×n]→L[ℂ] F) (y : E) :
    ‖c (fun _ => y)‖ ≤ ‖c‖ * ‖y‖ ^ n := by
  have := c.le_opNorm (fun _ => y)
  simpa [Finset.prod_const] using this

/-- Generic several-variable lemma: a normally convergent series of analytic functions
(bounded termwise by a summable sequence on a closed ball) is analytic. -/
theorem analyticAt_tsum_of_bound38 {f : ℕ → E → F} {x : E} {r : ℝ} (hr : 0 < r)
    (hf : ∀ j, AnalyticOnNhd ℂ (f j) (closedBall x r)) {m : ℕ → ℝ} (hm : Summable m)
    (hb : ∀ j, ∀ z ∈ closedBall x r, ‖f j z‖ ≤ m j) :
    AnalyticAt ℂ (fun y => ∑' j, f j y) x := by
  have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.2 one_pos
  set ρ : ℝ := r / Real.exp 1 with hρ
  have hρpos : 0 < ρ := by positivity
  have hm0 : ∀ j, 0 ≤ m j := fun j =>
    (norm_nonneg _).trans (hb j x (mem_closedBall_self hr.le))
  have hbd : ∀ j n, ‖taylorCoeff38 (f j) x n‖ ≤ m j * (Real.exp 1 / r) ^ n :=
    fun j n => norm_taylorCoeff_le38 hr (hf j) (hb j) n
  have hsumQ : ∀ n, Summable (fun j => taylorCoeff38 (f j) x n) := fun n =>
    Summable.of_norm_bounded (hm.mul_right _) (fun j => hbd j n)
  set Q : FormalMultilinearSeries ℂ E F := fun n => ∑' j, taylorCoeff38 (f j) x n with hQ
  have hQb : ∀ n, ‖Q n‖ ≤ (∑' j, m j) * (Real.exp 1 / r) ^ n := fun n =>
    tsum_of_norm_bounded (hm.hasSum.mul_right _) (fun j => hbd j n)
  have hrad : ENNReal.ofReal ρ ≤ Q.radius := by
    have := Q.le_radius_of_bound (r := ⟨ρ, hρpos.le⟩) (C := ∑' j, m j) (fun n => by
      calc ‖Q n‖ * ((⟨ρ, hρpos.le⟩ : NNReal) : ℝ) ^ n
          ≤ (∑' j, m j) * (Real.exp 1 / r) ^ n * ρ ^ n := by gcongr; exact hQb n
        _ = ∑' j, m j := by
            rw [mul_assoc, ← mul_pow, hρ]
            have : Real.exp 1 / r * (r / Real.exp 1) = 1 := by field_simp
            rw [this]; simp)
    rwa [ENNReal.ofReal_eq_coe_nnreal hρpos.le]
  refine ⟨Q, ENNReal.ofReal ρ, ⟨hrad, by simpa using hρpos, ?_⟩⟩
  intro y hy
  have hyn : ‖y‖ < ρ := by
    rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm] at hy
    exact (ENNReal.ofReal_lt_ofReal_iff hρpos).1 hy
  set θ : ℝ := Real.exp 1 / r * ‖y‖ with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ < 1 := by
    have : θ = ‖y‖ / ρ := by rw [hθ, hρ]; field_simp
    rw [this, div_lt_one hρpos]; exact hyn
  set a : ℕ → ℕ → F := fun j n => taylorCoeff38 (f j) x n (fun _ => y) with ha
  have hay : ∀ j n, ‖a j n‖ ≤ m j * θ ^ n := by
    intro j n
    calc ‖a j n‖ ≤ ‖taylorCoeff38 (f j) x n‖ * ‖y‖ ^ n := norm_taylorCoeff_apply_le38 _ _
      _ ≤ m j * (Real.exp 1 / r) ^ n * ‖y‖ ^ n := by gcongr; exact hbd j n
      _ = m j * θ ^ n := by rw [hθ, mul_pow]; ring
  have hsumθ : Summable (fun n : ℕ => θ ^ n) := summable_geometric_of_lt_one hθ0 hθ1
  have hprod : Summable (fun p : ℕ × ℕ => m p.1 * θ ^ p.2) :=
    Summable.mul_of_nonneg hm hsumθ hm0 (fun n => pow_nonneg hθ0 n)
  have hsa : Summable (fun p : ℕ × ℕ => a p.1 p.2) :=
    Summable.of_norm_bounded hprod (fun p => hay p.1 p.2)
  have hrow : ∀ j, HasSum (fun n => a j n) (f j (x + y)) := fun j =>
    hasSum_taylor38 hr (hf j) (hb j) (by rw [← hρ]; exact hyn)
  have hS1 : HasSum (fun j => f j (x + y)) (∑' p : ℕ × ℕ, a p.1 p.2) :=
    hsa.hasSum.prod_fiberwise hrow
  have hsa' : HasSum (fun p : ℕ × ℕ => a p.2 p.1) (∑' p : ℕ × ℕ, a p.1 p.2) := by
    have := (Equiv.prodComm ℕ ℕ).hasSum_iff.2 hsa.hasSum
    simpa [Function.comp_def] using this
  have hcol : ∀ n, HasSum (fun j => a j n) (Q n (fun _ => y)) := by
    intro n
    have := ((hsumQ n).hasSum).mapL (ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => E) F (fun _ => y))
    simpa [ha, hQ] using this
  have hS2 : HasSum (fun n => Q n (fun _ => y)) (∑' p : ℕ × ℕ, a p.1 p.2) :=
    hsa'.prod_fiberwise hcol
  rw [← hS1.tsum_eq] at hS2
  exact hS2

end Cauchy
end NlsGge.AnalyticTsum38
