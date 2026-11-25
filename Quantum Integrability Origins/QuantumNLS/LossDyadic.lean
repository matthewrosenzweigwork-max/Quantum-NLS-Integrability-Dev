import Mathlib
import QuantumNLS.LossDifference

/-!
# R-8C922B25 `lem:loss` (`DYNAMICS_LEMMAS.tex:13`), part 3: the dyadic summation (Step 1 of the printed proof)

`dyadic_step` (one dyadic step): for two difference quotients `q0 = Q_{j,h}`, `q1 = Q_{j,h/2}` of the `Y^S`-valued `g` with `‖ι q − D^jf‖_{Y^0} ≤ C j h` and
`‖q‖_{Y^S} ≤ 2^j M h^{-j}`, the interpolation inequality gives `‖q0 − q1‖_{Y^q} ≤ K h^{1−(j+1)q/S}` (printed: `C h^{1-(j+1)q/S}`).
`dyadic_lift` sums these over `h = h₀, h₀/2, …` (geometric, strictly positive exponent iff `(j+1)q/S < 1`), obtains the Cauchy sequence in the complete level `Y^q`,
identifies its limit with `D^jf(x)[v_1,…,v_j]` through the injective embedding into `Y^0`, with a uniform norm bound for `x` in a ball and unit directions.
The three spaces are abstract (`ιSp : W → Z`, `ιp0 : Z → F`, interpolation hypothesis `hint`); `Z` complete.  No EXT-025 contract: mathlib calculus plus the printed
interpolation inequality.
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option linter.unusedSectionVars false
open scoped ContDiff
open Filter Topology Set Metric
noncomputable section
namespace QuantumNLS.Loss

open QuantumNLS.Loss

variable {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem interp_alg {θ c1 c2 h : ℝ} (j : ℕ) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hh : 0 < h) :
    (c1 * h) ^ (1 - θ) * (c2 * (h ^ j)⁻¹) ^ θ = (c1 ^ (1 - θ) * c2 ^ θ) * h ^ (1 - ((j : ℝ) + 1) * θ) := by
  have hj : 0 ≤ (h ^ j)⁻¹ := by positivity
  rw [Real.mul_rpow hc1 hh.le, Real.mul_rpow hc2 hj, Real.inv_rpow (by positivity)]
  have e1 : (h ^ j) ^ θ = h ^ ((j : ℝ) * θ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hh.le]
  have e2 : h ^ (1 - ((j : ℝ) + 1) * θ) = h ^ (1 - θ) * (h ^ ((j : ℝ) * θ))⁻¹ := by
    rw [← Real.rpow_neg hh.le, ← Real.rpow_add hh]
    congr 1; ring
  rw [e1, e2]
  ring

theorem rpow_mul_rpow_le {a b α β θ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (haα : a ≤ α) (hbβ : b ≤ β)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) : a ^ (1 - θ) * b ^ θ ≤ α ^ (1 - θ) * β ^ θ := by
  have hα : 0 ≤ α := ha.trans haα
  have hβ : 0 ≤ β := hb.trans hbβ
  exact mul_le_mul (Real.rpow_le_rpow ha haα (by linarith)) (Real.rpow_le_rpow hb hbβ hθ0)
    (by positivity) (by positivity)

section Dyadic

variable {Z W : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- **One dyadic step** (printed: `‖Q_{j,h} − Q_{j,h/2}‖_{Y^q} ≤ C h^{1−(j+1)q/S}`), mixed form. -/
theorem dyadic_step (ιSp : W →L[ℝ] Z) (ιp0 : Z →L[ℝ] F) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hint : ∀ y : W, ‖ιSp y‖ ≤ ‖ιp0 (ιSp y)‖ ^ (1 - θ) * ‖y‖ ^ θ)
    (j : ℕ) (T : F) (q0 q1 : W) {C M h : ℝ} (hh : 0 < h) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (h0 : ‖ιp0 (ιSp q0) - T‖ ≤ C * j * h) (h1 : ‖ιp0 (ιSp q1) - T‖ ≤ C * j * (h / 2))
    (b0 : ‖q0‖ ≤ 2 ^ j * M * (h ^ j)⁻¹) (b1 : ‖q1‖ ≤ 2 ^ j * M * ((h / 2) ^ j)⁻¹) :
    ‖ιSp (q0 - q1)‖ ≤ ((2 * C * j) ^ (1 - θ) * (2 ^ (2 * j + 1) * M) ^ θ) * h ^ (1 - ((j : ℝ) + 1) * θ) := by
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have a1 : ‖ιp0 (ιSp (q0 - q1))‖ ≤ (2 * C * j) * h := by
    have : ιp0 (ιSp (q0 - q1)) = (ιp0 (ιSp q0) - T) - (ιp0 (ιSp q1) - T) := by simp
    rw [this]
    refine (norm_sub_le _ _).trans ?_
    nlinarith [mul_nonneg hC hj0, hh]
  have a2 : ‖q0 - q1‖ ≤ (2 ^ (2 * j + 1) * M) * (h ^ j)⁻¹ := by
    refine (norm_sub_le _ _).trans ?_
    have e : ((h / 2) ^ j)⁻¹ = 2 ^ j * (h ^ j)⁻¹ := by
      rw [div_pow, inv_div, div_eq_mul_inv, mul_comm]
    have hp : 0 ≤ (h ^ j)⁻¹ := by positivity
    have : 2 ^ j * M * (h ^ j)⁻¹ + 2 ^ j * M * ((h / 2) ^ j)⁻¹ = 2 ^ j * M * (h ^ j)⁻¹ * (1 + 2 ^ j) := by
      rw [e]; ring
    have h2j : (1 + 2 ^ j : ℝ) ≤ 2 ^ (j + 1) := by
      have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
      rw [pow_succ]; linarith
    calc ‖q0‖ + ‖q1‖ ≤ 2 ^ j * M * (h ^ j)⁻¹ + 2 ^ j * M * ((h / 2) ^ j)⁻¹ := add_le_add b0 b1
      _ = 2 ^ j * M * (h ^ j)⁻¹ * (1 + 2 ^ j) := this
      _ ≤ 2 ^ j * M * (h ^ j)⁻¹ * 2 ^ (j + 1) := by
          have : 0 ≤ 2 ^ j * M * (h ^ j)⁻¹ := by positivity
          exact mul_le_mul_of_nonneg_left h2j this
      _ = (2 ^ (2 * j + 1) * M) * (h ^ j)⁻¹ := by
          have : (2 : ℝ) ^ (2 * j + 1) = 2 ^ j * 2 ^ (j + 1) := by rw [← pow_add]; congr 1; ring
          rw [this]; ring
  have hi := hint (q0 - q1)
  refine hi.trans ?_
  have hc1 : 0 ≤ 2 * C * j := by positivity
  have hc2 : 0 ≤ 2 ^ (2 * j + 1) * M := by positivity
  calc ‖ιp0 (ιSp (q0 - q1))‖ ^ (1 - θ) * ‖q0 - q1‖ ^ θ
      ≤ ((2 * C * j) * h) ^ (1 - θ) * ((2 ^ (2 * j + 1) * M) * (h ^ j)⁻¹) ^ θ :=
        rpow_mul_rpow_le (norm_nonneg _) (norm_nonneg _) a1 a2 hθ0.le hθ1.le
    _ = _ := interp_alg j hc1 hc2 hh

end Dyadic

section DyadicLift

variable {Z W : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- **Step 1 of the printed proof** (existence of the `Y^q`-valued derivative with a uniform bound), mixed form: for `j ≤ k` and
`(j+1)θ < 1` (`θ = q/S`), the `j`-th Taylor coefficient of `f = ι g` applied to unit vectors lies in the image of the lower level with uniform norm. -/
theorem dyadic_lift (ιSp : W →L[ℝ] Z) (ιp0 : Z →L[ℝ] F) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hint : ∀ y : W, ‖ιSp y‖ ≤ ‖ιp0 (ιSp y)‖ ^ (1 - θ) * ‖y‖ ^ θ)
    {U : Set X} (g : X → W) (P : X → FormalMultilinearSeries ℝ X F) {k : ℕ}
    (hP : HasFTaylorSeriesUpToOn ((k + 1 : ℕ) : ℕ∞ω) (fun x => ιp0 (ιSp (g x))) P U)
    {x0 : X} {r : ℝ} (hr : 0 < r) (hball : ball x0 r ⊆ U) {M C A : ℝ}
    (hM : ∀ y ∈ ball x0 r, ‖g y‖ ≤ M) (j : ℕ) (hj : j ≤ k) (hjθ : ((j : ℝ) + 1) * θ < 1)
    (hC : ∀ y ∈ ball x0 r, ‖P y (j + 1)‖ ≤ C) (hA : ∀ y ∈ ball x0 r, ‖P y j‖ ≤ A) :
    ∃ B : ℝ, ∀ x ∈ ball x0 (r / 2), ∀ v : Fin j → X, (∀ i, ‖v i‖ ≤ 1) →
      ∃ L : Z, ιp0 L = P x j v ∧ ‖L‖ ≤ B := by
  have hMnn : 0 ≤ M := (norm_nonneg _).trans (hM x0 (mem_ball_self hr))
  have hCnn : 0 ≤ C := (norm_nonneg _).trans (hC x0 (mem_ball_self hr))
  have hAnn : 0 ≤ A := (norm_nonneg _).trans (hA x0 (mem_ball_self hr))
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  set h0 : ℝ := r / (2 * ((k : ℝ) + 1)) with hh0
  have hh0pos : 0 < h0 := by positivity
  have hjh0 : (j : ℝ) * h0 < r / 2 := by
    have hjk : (j : ℝ) ≤ k := by exact_mod_cast hj
    calc (j : ℝ) * h0 ≤ k * h0 := mul_le_mul_of_nonneg_right hjk hh0pos.le
      _ < r / 2 := by
        rw [hh0, mul_div_assoc', div_lt_div_iff₀ (by positivity) (by positivity)]
        nlinarith
  set ε : ℝ := 1 - ((j : ℝ) + 1) * θ with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  set ρ : ℝ := (1 / 2 : ℝ) ^ ε with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hε0
  set K : ℝ := (2 * C * j) ^ (1 - θ) * (2 ^ (2 * j + 1) * M) ^ θ with hK
  have hKnn : 0 ≤ K := by positivity
  refine ⟨(A + C * j * h0) ^ (1 - θ) * (2 ^ j * M * (h0 ^ j)⁻¹) ^ θ + K * h0 ^ ε * (1 - ρ)⁻¹, ?_⟩
  intro x hx v hv
  have hx' : ‖x - x0‖ < r / 2 := by simpa [dist_eq_norm] using hx
  set T : F := P x j v with hT
  have hsum : ∀ h : ℝ, 0 < h → ∑ i, ‖h • v i‖ ≤ j * h := by
    intro h hh
    calc ∑ i, ‖h • v i‖ ≤ ∑ _i : Fin j, h := Finset.sum_le_sum (fun i _ => by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]; exact mul_le_of_le_one_right hh.le (hv i))
      _ = j * h := by simp
  have hprod : ∀ h : ℝ, 0 < h → ∏ i, ‖h • v i‖ ≤ h ^ j := by
    intro h hh
    calc ∏ i, ‖h • v i‖ ≤ ∏ _i : Fin j, h := Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]; exact mul_le_of_le_one_right hh.le (hv i))
      _ = h ^ j := by simp
  have hsub : ∀ h : ℝ, 0 < h → h ≤ h0 → closedBall x (∑ i, ‖h • v i‖) ⊆ ball x0 r := by
    intro h hh hhle y hy
    rw [mem_closedBall, dist_eq_norm] at hy
    rw [mem_ball, dist_eq_norm]
    have h1 : (j : ℝ) * h ≤ j * h0 := mul_le_mul_of_nonneg_left hhle (Nat.cast_nonneg j)
    have h2 := hsum h hh
    calc ‖y - x0‖ = ‖(y - x) + (x - x0)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖y - x‖ + ‖x - x0‖ := norm_add_le _ _
      _ < r := by linarith
  let Qg : ℝ → W := fun h => (h ^ j)⁻¹ • mdiff j (fun i => h • v i) g x
  have hQ : ∀ h, ιp0 (ιSp (Qg h)) =
      (h ^ j)⁻¹ • mdiff j (fun i => h • v i) (fun y => ιp0 (ιSp (g y))) x := by
    intro h
    simp only [Qg, map_smul]
    congr 1
    exact (mdiff_map (ιp0.comp ιSp) j (fun i => h • v i) g x).symm
  have hest : ∀ h : ℝ, 0 < h → h ≤ h0 → ‖ιp0 (ιSp (Qg h)) - T‖ ≤ C * j * h := by
    intro h hh hhle
    have hT1 := taylor_mdiff j (fun y => ιp0 (ιSp (g y))) P (ball x0 r) C isOpen_ball (convex_ball x0 r)
      ((hP.of_le (by exact_mod_cast Nat.succ_le_succ hj)).mono hball) hC (fun i => h • v i) x (hsub h hh hhle)
    have hscale : P x j (fun i => h • v i) = (h ^ j) • T := by
      have := (P x j).map_smul_univ (fun _ => h) v
      simpa using this
    rw [hscale] at hT1
    have hhj : 0 < h ^ j := pow_pos hh j
    have e : ιp0 (ιSp (Qg h)) - T = (h ^ j)⁻¹ • (mdiff j (fun i => h • v i) (fun y => ιp0 (ιSp (g y))) x - (h ^ j) • T) := by
      rw [hQ, smul_sub, smul_smul, inv_mul_cancel₀ hhj.ne', one_smul]
    rw [e, norm_smul, norm_inv, norm_pow, Real.norm_eq_abs, abs_of_pos hh]
    have hPnn : 0 ≤ ∏ i, ‖h • v i‖ := Finset.prod_nonneg (fun i _ => norm_nonneg _)
    have hSnn : 0 ≤ ∑ i, ‖h • v i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
    calc (h ^ j)⁻¹ * ‖mdiff j (fun i => h • v i) (fun y => ιp0 (ιSp (g y))) x - (h ^ j) • T‖
        ≤ (h ^ j)⁻¹ * (C * (∏ i, ‖h • v i‖) * ∑ i, ‖h • v i‖) := mul_le_mul_of_nonneg_left hT1 (by positivity)
      _ ≤ (h ^ j)⁻¹ * (C * h ^ j * (j * h)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul (mul_le_mul_of_nonneg_left (hprod h hh) hCnn) (hsum h hh) hSnn (by positivity)
      _ = C * j * h := by field_simp
  have hbd : ∀ h : ℝ, 0 < h → h ≤ h0 → ‖Qg h‖ ≤ 2 ^ j * M * (h ^ j)⁻¹ := by
    intro h hh hhle
    have := mdiff_bound j (fun i => h • v i) g x M (fun y hy => hM y (hsub h hh hhle (by simpa [dist_eq_norm] using hy)))
    simp only [Qg, norm_smul, norm_inv, norm_pow, Real.norm_eq_abs, abs_of_pos hh]
    have hp : 0 ≤ (h ^ j)⁻¹ := by positivity
    calc (h ^ j)⁻¹ * ‖mdiff j (fun i => h • v i) g x‖ ≤ (h ^ j)⁻¹ * (2 ^ j * M) :=
          mul_le_mul_of_nonneg_left this hp
      _ = 2 ^ j * M * (h ^ j)⁻¹ := by ring
  -- the dyadic sequence
  set t : ℕ → ℝ := fun m => h0 * (1 / 2 : ℝ) ^ m with ht
  have htpos : ∀ m, 0 < t m := fun m => by positivity
  have htle : ∀ m, t m ≤ h0 := fun m => by
    have : (1 / 2 : ℝ) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    calc t m = h0 * (1 / 2 : ℝ) ^ m := rfl
      _ ≤ h0 * 1 := mul_le_mul_of_nonneg_left this hh0pos.le
      _ = h0 := mul_one _
  have htsucc : ∀ m, t (m + 1) = t m / 2 := fun m => by
    simp only [ht, pow_succ]; ring
  set a : ℕ → Z := fun m => ιSp (Qg (t m)) with ha
  have hstep : ∀ m, dist (a m) (a (m + 1)) ≤ (K * h0 ^ ε) * ρ ^ m := by
    intro m
    have hm := htpos m
    have hm2 : 0 < t m / 2 := by positivity
    have hm2le : t m / 2 ≤ h0 := by linarith [htle m]
    have := dyadic_step ιSp ιp0 hθ0 hθ1 hint j T (Qg (t m)) (Qg (t m / 2)) hm hCnn hMnn
      (hest (t m) hm (htle m)) (hest (t m / 2) hm2 hm2le) (hbd (t m) hm (htle m)) (hbd (t m / 2) hm2 hm2le)
    rw [dist_eq_norm]
    show ‖ιSp (Qg (t m)) - ιSp (Qg (t (m + 1)))‖ ≤ _
    rw [htsucc, ← map_sub]
    refine this.trans (le_of_eq ?_)
    have hr1 : (t m) ^ ε = h0 ^ ε * ρ ^ m := by
      rw [ht, Real.mul_rpow hh0pos.le (by positivity), hρ, ← Real.rpow_natCast, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num)]
      rw [mul_comm (m : ℝ) ε]
    rw [hr1]; ring
  have hcau : CauchySeq a := cauchySeq_of_le_geometric ρ (K * h0 ^ ε) hρ1 hstep
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcau
  have ht0 : Tendsto t atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).const_mul h0
    simpa [ht] using this
  have hT0 : Tendsto (fun m => ιp0 (a m)) atTop (𝓝 T) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun m => norm_nonneg _) (fun m => hest (t m) (htpos m) (htle m)) ?_
    simpa using ht0.const_mul (C * j)
  have hLT : ιp0 L = T := tendsto_nhds_unique ((ιp0.continuous.tendsto L).comp hL) hT0
  refine ⟨L, hLT, ?_⟩
  -- the bound
  have hsumm : Summable (fun m : ℕ => (K * h0 ^ ε) * ρ ^ m) :=
    (summable_geometric_of_lt_one hρ0.le hρ1).mul_left _
  have hdist := dist_le_tsum_of_dist_le_of_tendsto (fun m => (K * h0 ^ ε) * ρ ^ m) hstep hsumm hL 0
  have htsum : ∑' m : ℕ, (K * h0 ^ ε) * ρ ^ (0 + m) = (K * h0 ^ ε) * (1 - ρ)⁻¹ := by
    simp only [zero_add]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0.le hρ1]
  rw [htsum] at hdist
  have ha0 : ‖a 0‖ ≤ (A + C * j * h0) ^ (1 - θ) * (2 ^ j * M * (h0 ^ j)⁻¹) ^ θ := by
    have h00 : t 0 = h0 := by simp [ht]
    have e1 : ‖ιp0 (a 0)‖ ≤ A + C * j * h0 := by
      have h1 := hest (t 0) (htpos 0) (htle 0)
      rw [h00] at h1
      have hTn : ‖T‖ ≤ A := by
        have h2 := (P x j).le_opNorm v
        have h3 : ∏ i, ‖v i‖ ≤ 1 := Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => hv i)
        calc ‖T‖ ≤ ‖P x j‖ * ∏ i, ‖v i‖ := h2
          _ ≤ A * 1 := mul_le_mul (hA x (by
                rw [mem_ball, dist_eq_norm]; linarith)) h3 (Finset.prod_nonneg fun i _ => norm_nonneg _) hAnn
          _ = A := mul_one _
      have h00' : a 0 = ιSp (Qg h0) := by simp [ha, h00]
      rw [h00']
      calc ‖ιp0 (ιSp (Qg h0))‖ ≤ ‖T‖ + ‖ιp0 (ιSp (Qg h0)) - T‖ := by
            calc _ = ‖T + (ιp0 (ιSp (Qg h0)) - T)‖ := by rw [add_sub_cancel]
              _ ≤ _ := norm_add_le _ _
        _ ≤ A + C * j * h0 := by linarith
    have e2 : ‖Qg h0‖ ≤ 2 ^ j * M * (h0 ^ j)⁻¹ := hbd h0 hh0pos le_rfl
    have h00' : a 0 = ιSp (Qg h0) := by simp [ha, h00]
    rw [h00']
    refine (hint (Qg h0)).trans ?_
    refine rpow_mul_rpow_le (norm_nonneg _) (norm_nonneg _) ?_ e2 hθ0.le hθ1.le
    simpa [h00'] using e1
  calc ‖L‖ ≤ ‖a 0‖ + dist (a 0) L := by
        calc ‖L‖ = ‖a 0 - (a 0 - L)‖ := by rw [sub_sub_cancel]
          _ ≤ ‖a 0‖ + ‖a 0 - L‖ := norm_sub_le _ _
          _ = _ := by rw [dist_eq_norm]
    _ ≤ _ := add_le_add ha0 hdist

end DyadicLift

end QuantumNLS.Loss

#print axioms QuantumNLS.Loss.dyadic_step
#print axioms QuantumNLS.Loss.dyadic_lift
