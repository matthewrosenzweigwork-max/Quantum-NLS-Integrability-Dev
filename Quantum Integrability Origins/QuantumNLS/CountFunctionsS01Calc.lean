import QuantumNLS.CountFunctionsS01Ops

/-!
# CountFunctionsS01Calc: the first-order estimate behind eq:finite-difference

PRINTED SOURCE `source-text/chapters/core/canonical_algebra.tex:45-46`:
  "A fixed `C²` extension to a neighborhood of the cube gives `N[f(x+h/N)-f(x)] = ∂_h f(x) + O(N^{-1})` uniformly on
   the cube. Combining this operator-norm estimate with the strong Cartesian and continuous-count symbols yields the
   bracket with `f(a_J)`."

`C2Near J f` is the printed class (`C²` on a neighborhood of `[0,1]^J`).  This module proves the uniform estimate with
`o(1)` in place of `O(N^{-1})` (`C²` implies `C¹`, and `C¹` near the cube suffices for the strong convergence of the
scaled bracket and for the uniform scaled bound), at the level of the coefficient carrier:
`‖N • (E_{ab} (f(B+h/N)-f(B))) - E_{ab} ∂_h f(B)‖ → 0`.  No acceptance claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open scoped InnerProductSpace ComplexConjugate ENNReal
open QuantumNLS Occupation OccupationHilbert BetheCoefficientTransform BetheOccupationGauge
open QuantumNLS.CountFunctionsS01Ops

namespace QuantumNLS.CountFunctionsS01Calc

lemma isCompact_cube (J : Finset ℤ) : IsCompact (cube J) := by
  have : cube J = Set.pi Set.univ (fun _ : ↥J => Set.Icc (0 : ℝ) 1) := by
    ext x; simp [cube, Set.pi]
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_Icc

/-- Uniform modulus of continuity on the cube. -/
lemma modulus_cube {J : Finset ℤ} {f : (↥J → ℝ) → ℂ} (hf : ContinuousOn f (cube J)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ cube J, ∀ y ∈ cube J, (∀ j, |x j - y j| < δ) → ‖f x - f y‖ ≤ ε := by
  have hu := (isCompact_cube J).uniformContinuousOn_of_continuous hf
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuousOn_iff.1 hu ε hε
  refine ⟨δ, hδ, fun x hx y hy hxy => ?_⟩
  have hd : dist x y < δ := by
    rw [dist_pi_lt_iff hδ]
    intro j
    rw [Real.dist_eq]
    exact hxy j
  have := h x hx y hy hd
  rw [dist_eq_norm] at this
  exact this.le

/-- The printed class: `f` is `C²` on a neighborhood of the cube `[0,1]^J`. -/
def C2Near (J : Finset ℤ) (f : (↥J → ℝ) → ℂ) : Prop :=
  ∃ U : Set (↥J → ℝ), IsOpen U ∧ cube J ⊆ U ∧ ContDiffOn ℝ 2 f U

lemma C2Near.continuousOn {J : Finset ℤ} {f : (↥J → ℝ) → ℂ} (hf : C2Near J f) : ContinuousOn f (cube J) := by
  obtain ⟨U, hU, hcU, hC⟩ := hf
  exact (hC.continuousOn).mono hcU

/-- The directional derivative `∂_h f`, `h = e_b - e_a`. -/
def dirDeriv (J : Finset ℤ) (f : (↥J → ℝ) → ℂ) (a b : ↥J) : (↥J → ℝ) → ℂ :=
  fun x => fderiv ℝ f x (hvec J a b)

lemma C2Near.dirDeriv_continuousOn {J : Finset ℤ} {f : (↥J → ℝ) → ℂ} (hf : C2Near J f) (a b : ↥J) :
    ContinuousOn (dirDeriv J f a b) (cube J) := by
  obtain ⟨U, hU, hcU, hC⟩ := hf
  have h1 : ContinuousOn (fderiv ℝ f) U := hC.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have h2 : ContinuousOn (fun x => fderiv ℝ f x (hvec J a b)) U :=
    (ContinuousLinearMap.apply ℝ ℂ (hvec J a b)).continuous.comp_continuousOn h1
  exact h2.mono hcU

/-- The uniform first-order Taylor estimate on the cube. -/
theorem C2Near.taylor1 {J : Finset ℤ} {f : (↥J → ℝ) → ℂ} (hf : C2Near J f) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ cube J, ∀ k : ↥J → ℝ, ‖k‖ ≤ δ →
      ‖f (x + k) - f x - fderiv ℝ f x k‖ ≤ ε * ‖k‖ := by
  obtain ⟨U, hU, hcU, hC⟩ := hf
  have hdiff : ∀ y ∈ U, DifferentiableAt ℝ f y := fun y hy =>
    (hC.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hy)
  have hcont : ContinuousOn (fderiv ℝ f) U := hC.continuousOn_fderiv_of_isOpen hU (by norm_num)
  obtain ⟨r, hr, hrU⟩ := (isCompact_cube J).exists_cthickening_subset_open hU hcU
  have hKc : IsCompact (Metric.cthickening r (cube J)) := (isCompact_cube J).cthickening
  have hu := hKc.uniformContinuousOn_of_continuous (hcont.mono hrU)
  obtain ⟨δ₀, hδ₀, hmod⟩ := Metric.uniformContinuousOn_iff.1 hu ε hε
  refine ⟨min (δ₀ / 2) r, lt_min (by positivity) hr, fun x hx k hk => ?_⟩
  have hkr : ‖k‖ ≤ r := hk.trans (min_le_right _ _)
  have hkδ : ‖k‖ < δ₀ := lt_of_le_of_lt (hk.trans (min_le_left _ _)) (by linarith)
  set φ : (↥J → ℝ) → ℂ := fun y => f y - fderiv ℝ f x y with hφ
  have hball : Metric.closedBall x ‖k‖ ⊆ Metric.cthickening r (cube J) := by
    intro y hy
    refine Metric.mem_cthickening_of_dist_le y x r (cube J) hx ?_
    exact (Metric.mem_closedBall.1 hy).trans hkr
  have hdφ : ∀ y ∈ Metric.closedBall x ‖k‖, DifferentiableAt ℝ φ y := fun y hy =>
    (hdiff y (hrU (hball hy))).sub (fderiv ℝ f x).differentiableAt
  have hbd : ∀ y ∈ Metric.closedBall x ‖k‖, ‖fderiv ℝ φ y‖ ≤ ε := by
    intro y hy
    have hyU : y ∈ U := hrU (hball hy)
    have e : fderiv ℝ φ y = fderiv ℝ f y - fderiv ℝ f x :=
      ((hdiff y hyU).hasFDerivAt.sub (fderiv ℝ f x).hasFDerivAt).fderiv
    rw [e]
    have hy' : dist y x < δ₀ := lt_of_le_of_lt (Metric.mem_closedBall.1 hy) hkδ
    have := hmod y (hball hy) x (Metric.self_subset_cthickening _ hx |> fun h => h) hy'
    rw [dist_eq_norm] at this
    exact this.le
  have hxs : x ∈ Metric.closedBall x ‖k‖ := Metric.mem_closedBall_self (norm_nonneg _)
  have hys : x + k ∈ Metric.closedBall x ‖k‖ := by simp
  have key := (convex_closedBall x ‖k‖).norm_image_sub_le_of_norm_fderiv_le hdφ hbd hxs hys
  have e2 : φ (x + k) - φ x = f (x + k) - f x - fderiv ℝ f x k := by
    simp only [hφ, map_add]
    ring
  rw [e2] at key
  simpa using key

/-! ### The scaled finite difference on the coefficient carrier -/

lemma dg_smul {N : ℕ} {c : Arr N → ℂ} (hc : Bdd c) (z : ℂ) :
    z • dg c = dg (fun m => z * c m) := by
  ext v m
  have hzc : Bdd (fun m => z * c m) := bdd_mul (bdd_const z) hc
  rw [ContinuousLinearMap.smul_apply, lp.coeFn_smul, Pi.smul_apply, dg_apply hc, dg_apply hzc, smul_eq_mul]
  ring

/-- The transfer annihilates every vector supported on empty-donor arrays. -/
lemma E_dg_donor {N : ℕ} {c : Arr N → ℂ} (hc : Bdd c) (a b : ℤ) :
    E N a b * dg c = E N a b * dg (fun m => if DonorOK a m.1 then c m else 0) := by
  have hc' : Bdd (fun m : Arr N => if DonorOK a m.1 then c m else 0) := by
    obtain ⟨C, hC, h⟩ := hc
    exact ⟨C, hC, fun m => by
      show ‖if DonorOK a m.1 then c m else 0‖ ≤ C
      split_ifs <;> simp [hC, h m]⟩
  apply ext_basis
  intro m
  rw [show (E N a b * dg c) (lp.single 2 m 1) = E N a b (dg c (lp.single 2 m 1)) from rfl,
    show (E N a b * dg (fun m => if DonorOK a m.1 then c m else 0)) (lp.single 2 m 1) =
      E N a b (dg (fun m => if DonorOK a m.1 then c m else 0) (lp.single 2 m 1)) from rfl,
    dg_single hc, dg_single hc']
  by_cases hd : DonorOK a m.1
  · simp [hd]
  · rw [E_single N a b m, E_single N a b m]
    simp [hd]

/-- **The scaled finite difference converges to the directional derivative**, in operator norm, after `E_{ab}`:
`‖N • E_{ab}(f(B+h/N) - f(B)) - E_{ab} ∂_h f(B)‖ → 0`. -/
theorem fd_scaled_close_H {J : Finset ℤ} {f : (↥J → ℝ) → ℂ} (hf : C2Near J f) (a c : ↥J) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 0 < N →
      ‖(N : ℂ) • (E N (a : ℤ) (c : ℤ) * dg (fdiffCoef N J f a c)) -
          E N (a : ℤ) (c : ℤ) * cntH N J (dirDeriv J f a c)‖ ≤ ε := by
  have hfb : BddOn J f := BddOn.of_continuousOn hf.continuousOn
  have hdb : BddOn J (dirDeriv J f a c) := BddOn.of_continuousOn (hf.dirDeriv_continuousOn a c)
  obtain ⟨δ, hδ, htay⟩ := hf.taylor1 hε
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (1 / δ)
  refine ⟨N₀, fun N hN hpos => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hpos
  have hNδ : 1 / δ ≤ (N : ℝ) := hN₀.trans (by exact_mod_cast hN)
  have hk : (N : ℝ)⁻¹ ≤ δ := by
    have : 1 / (N : ℝ) ≤ δ := by
      rw [div_le_iff₀ hNpos]
      have := (div_le_iff₀ hδ).1 hNδ
      linarith
    simpa using this
  -- the coefficient family
  have hdb' : Bdd (fun m : Arr N => (N : ℂ) * fdiffCoef N J f a c m - dirDeriv J f a c (pt J N m.1)) :=
    bdd_sub (bdd_mul (bdd_const _) (bdd_fdiff hfb a c)) (bdd_cnt hdb)
  have e1 : (N : ℂ) • (E N (a : ℤ) (c : ℤ) * dg (fdiffCoef N J f a c)) -
      E N (a : ℤ) (c : ℤ) * cntH N J (dirDeriv J f a c) =
      E N (a : ℤ) (c : ℤ) * dg (fun m : Arr N => (N : ℂ) * fdiffCoef N J f a c m - dirDeriv J f a c (pt J N m.1)) := by
    calc (N : ℂ) • (E N (a : ℤ) (c : ℤ) * dg (fdiffCoef N J f a c)) -
          E N (a : ℤ) (c : ℤ) * cntH N J (dirDeriv J f a c)
        = E N (a : ℤ) (c : ℤ) * ((N : ℂ) • dg (fdiffCoef N J f a c)) -
          E N (a : ℤ) (c : ℤ) * cntH N J (dirDeriv J f a c) := by rw [mul_smul_comm]
      _ = E N (a : ℤ) (c : ℤ) * ((N : ℂ) • dg (fdiffCoef N J f a c) - cntH N J (dirDeriv J f a c)) :=
          (mul_sub _ _ _).symm
      _ = _ := by
          rw [dg_smul (bdd_fdiff hfb a c)]
          unfold cntH
          rw [dg_sub (bdd_mul (bdd_const _) (bdd_fdiff hfb a c)) (bdd_cnt hdb)]
  rw [e1, E_dg_donor hdb']
  have hbound : ∀ m : Arr N, ‖(if DonorOK (a : ℤ) m.1 then
      (N : ℂ) * fdiffCoef N J f a c m - dirDeriv J f a c (pt J N m.1) else 0)‖ ≤ ε := by
    intro m
    by_cases hdon : DonorOK (a : ℤ) m.1
    · simp only [hdon, if_true]
      have hx := pt_mem_cube J m.2
      have hkn : ‖(N : ℝ)⁻¹ • hvec J a c‖ ≤ δ := by
        rw [norm_smul, norm_inv, Real.norm_natCast]
        calc (N : ℝ)⁻¹ * ‖hvec J a c‖ ≤ (N : ℝ)⁻¹ * 1 :=
              mul_le_mul_of_nonneg_left (norm_hvec_le J a c) (by positivity)
          _ ≤ δ := by simpa using hk
      have ht := htay _ hx _ hkn
      have hnk : ‖(N : ℝ)⁻¹ • hvec J a c‖ ≤ (N : ℝ)⁻¹ := by
        rw [norm_smul, norm_inv, Real.norm_natCast]
        calc (N : ℝ)⁻¹ * ‖hvec J a c‖ ≤ (N : ℝ)⁻¹ * 1 :=
              mul_le_mul_of_nonneg_left (norm_hvec_le J a c) (by positivity)
          _ = (N : ℝ)⁻¹ := mul_one _
      have e : (N : ℂ) * fdiffCoef N J f a c m - dirDeriv J f a c (pt J N m.1) =
          (N : ℂ) * (f (pt J N m.1 + (N : ℝ)⁻¹ • hvec J a c) - f (pt J N m.1) -
            fderiv ℝ f (pt J N m.1) ((N : ℝ)⁻¹ • hvec J a c)) := by
        simp only [fdiffCoef, hdon, if_true, dirDeriv, map_smul, Complex.real_smul]
        have : (N : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
        push_cast
        field_simp
      rw [e, norm_mul, Complex.norm_natCast]
      calc (N : ℝ) * ‖f (pt J N m.1 + (N : ℝ)⁻¹ • hvec J a c) - f (pt J N m.1) -
            fderiv ℝ f (pt J N m.1) ((N : ℝ)⁻¹ • hvec J a c)‖
          ≤ (N : ℝ) * (ε * ‖(N : ℝ)⁻¹ • hvec J a c‖) := mul_le_mul_of_nonneg_left ht hNpos.le
        _ ≤ (N : ℝ) * (ε * (N : ℝ)⁻¹) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnk hε.le) hNpos.le
        _ = ε := by field_simp
    · simp [hdon, hε.le]
  have hbddon : Bdd (fun m : Arr N => if DonorOK (a : ℤ) m.1 then
      (N : ℂ) * fdiffCoef N J f a c m - dirDeriv J f a c (pt J N m.1) else 0) := by
    refine ⟨ε, hε.le, hbound⟩
  calc ‖E N (a : ℤ) (c : ℤ) * dg (fun m : Arr N => if DonorOK (a : ℤ) m.1 then
        (N : ℂ) * fdiffCoef N J f a c m - dirDeriv J f a c (pt J N m.1) else 0)‖
      ≤ ‖E N (a : ℤ) (c : ℤ)‖ * ‖dg (fun m : Arr N => if DonorOK (a : ℤ) m.1 then
        (N : ℂ) * fdiffCoef N J f a c m - dirDeriv J f a c (pt J N m.1) else 0)‖ := norm_mul_le _ _
    _ ≤ 1 * ε := mul_le_mul (E_norm_le N _ _) (dg_norm_le hε.le hbound) (norm_nonneg _) zero_le_one
    _ = ε := one_mul _

end QuantumNLS.CountFunctionsS01Calc
