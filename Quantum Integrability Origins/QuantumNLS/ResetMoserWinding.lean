import QuantumNLS.ResetMoserAngular
import QuantumNLS.ResetMoserHypFlow

/-!
# `thm:reset-moser` (LOCAL-017), stage 3a (item 2(a)): the winding vector of the loop `s ↦ φ_j^s(z)`

Source: `symplectic_correction.tex`, "The periods of a radial primitive": "The loop `s ↦ φ_j^s(z)`, `0 ≤ s ≤ 2π`, on that torus has
winding vector `−e_j`. Indeed the winding vector is integer valued and locally constant as the point varies in the connected open
subset of `ℋ_F ∩ B_r` with all these coordinates nonzero. [...] Uniform closeness therefore identifies the winding for small positive
`ε`, and hence everywhere in the connected set. This argument does not require that `2π` be a least period."

Formalization (the `k`th winding number of the loop, `k` with `z_k ≠ 0`; `ang S j k w = Im(conj(w_k)(X_j)_k(w))/|w_k|²`
is the angular velocity of the `k`th coordinate):
* `Hyp.Xn_coord_eq`: `(X_j)_k(w) = i · ang · w_k` (since `dq_k(w) X_j(w) = 0`);
* `Hyp.gamma_coord`: `φ_j^s(z)_k = z_k exp(i ∫_0^s ang(φ_j^u z) du)` (the angle lift of the `k`th coordinate);
* `Hyp.winding_int`: the winding `∫_0^{2π} ang(φ_j^s z) ds` is an integer multiple of `2π`, because `φ_j^{2π} = id`
  (no least-period assumption);
* `Hyp.winding_cont`: it is continuous in the point along the ray `ε ↦ ε z` (dominated convergence; `|ang(w)| ≤ 2|w_j|/|w_k|` and the
  flow is differentiable at every point of the ball, `Hyp.diffAt_flow`);
* `Hyp.winding`: it equals `−2π δ_{jk}`. The connected set used is the ray `{ε z : 0 < ε < ρ/‖z‖}` inside the connected open set
  of the source (a sub-argument of it); the small-`ε` identification uses the exact quadratic bound `ang_bound` (no linearization
  limit), valid for every `z ∈ B_ρ` with `z_k ≠ 0`, finitely supported or not.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology ENNReal
open Filter Set Metric
open scoped Interval

namespace QuantumNLS.ResetMoser

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.RealAnalyticDef
open QuantumNLS.ResetMoserFlow

/-- The angular velocity of the `k`th coordinate under the `j`th field. -/
def ang (S : Hyp) (j k : ℤ) (w : K) : ℝ := (conj (w k) * (Xn S.Ω j w) k).im / ‖w k‖ ^ 2

theorem Hyp.re_zero (S : Hyp) {w : K} (hw : w ∈ ball (0 : K) S.R) (j k : ℤ) :
    (conj (w k) * (Xn S.Ω j w) k).re = 0 := by
  have h0 := S.dq_Xn hw k j
  rw [fderiv_q_apply] at h0
  linarith

theorem Hyp.Xn_coord_eq (S : Hyp) {w : K} (hw : w ∈ ball (0 : K) S.R) (j k : ℤ) (hk : w k ≠ 0) :
    (Xn S.Ω j w) k = Complex.I * (ang S j k w : ℂ) * w k := by
  have hre := S.re_zero hw j k
  set c := conj (w k) * (Xn S.Ω j w) k with hc
  have hcI : c = Complex.I * (c.im : ℂ) := by
    apply Complex.ext <;> simp [hre]
  have hn : (‖w k‖ : ℂ) ^ 2 = conj (w k) * w k := by
    rw [Complex.conj_mul']
  have hnz : (‖w k‖ : ℂ) ^ 2 ≠ 0 := by
    have : (0 : ℝ) < ‖w k‖ := norm_pos_iff.2 hk
    exact pow_ne_zero 2 (by exact_mod_cast this.ne')
  have hcc : conj (w k) ≠ 0 := by simpa using hk
  unfold ang
  rw [← hc]
  push_cast
  have key : (Xn S.Ω j w k) * ((‖w k‖ : ℂ) ^ 2) = Complex.I * (c.im : ℂ) * w k := by
    rw [hn]
    have : conj (w k) * (Xn S.Ω j w k) = Complex.I * (c.im : ℂ) := by rw [← hcI]
    calc (Xn S.Ω j w k) * (conj (w k) * w k) = (conj (w k) * (Xn S.Ω j w k)) * w k := by ring
      _ = Complex.I * (c.im : ℂ) * w k := by rw [this]
  have e2 : Complex.I * ((c.im : ℂ) / (‖w k‖ : ℂ) ^ 2) * w k = (Complex.I * (c.im : ℂ) * w k) / (‖w k‖ : ℂ) ^ 2 := by
    ring
  rw [e2, eq_div_iff hnz]
  exact key

theorem Hyp.gamma_hasDerivAt (S : Hyp) {z : K} (hz : z ∈ ball (0 : K) S.R) (j k : ℤ) (s : ℝ) :
    HasDerivAt (fun r => S.φ j r z k) ((Xn S.Ω j (S.φ j s z)) k) s := by
  have := (evalR k).hasFDerivAt.comp_hasDerivAt s (S.φ_deriv j z hz s)
  exact this

theorem Hyp.gamma_norm_coord (S : Hyp) {z : K} (hz : z ∈ ball (0 : K) S.R) (j k : ℤ) (s : ℝ) :
    ‖S.φ j s z k‖ = ‖z k‖ := by
  have h := S.flow_q hz k j s
  unfold q at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by norm_num : (2 : ℕ) ≠ 0)).1 h

theorem Hyp.gamma_continuous (S : Hyp) {z : K} (hz : z ∈ ball (0 : K) S.R) (j : ℤ) :
    Continuous (fun s => S.φ j s z) :=
  continuous_iff_continuousAt.2 fun s => (S.φ_deriv j z hz s).continuousAt

theorem Hyp.ang_continuousAt (S : Hyp) {w : K} (hw : w ∈ ball (0 : K) S.R) (j k : ℤ) (hk : w k ≠ 0) :
    ContinuousAt (ang S j k) w := by
  have hX : ContinuousAt (Xn S.Ω j) w := (S.Xn_contDiffAt hw j).continuousAt
  have hev : Continuous (fun v : K => v k) := (evalR k).continuous
  have h1 : ContinuousAt (fun v : K => (conj (v k) * (Xn S.Ω j v) k).im) w := by
    refine Complex.continuous_im.continuousAt.comp ?_
    refine ((Complex.continuous_conj.comp hev).continuousAt).mul ?_
    exact (hev.continuousAt).comp hX
  have h2 : ContinuousAt (fun v : K => ‖v k‖ ^ 2) w :=
    ((hev.norm).pow 2).continuousAt
  unfold ang
  exact h1.div h2 (pow_ne_zero 2 (norm_ne_zero_iff.2 hk))

theorem Hyp.ang_abs_le (S : Hyp) {w : K} (hw : w ∈ ball (0 : K) S.R) (j k : ℤ) (hk : w k ≠ 0) :
    |ang S j k w| ≤ 2 * ‖w j‖ / ‖w k‖ := by
  have hk0 : 0 < ‖w k‖ := norm_pos_iff.2 hk
  have hX := norm_Xn_le S hw j
  have hXk : ‖(Xn S.Ω j w) k‖ ≤ ‖Xn S.Ω j w‖ := lp.norm_apply_le_norm (by norm_num) _ k
  unfold ang
  rw [abs_div, abs_of_pos (by positivity : 0 < ‖w k‖ ^ 2), div_le_div_iff₀ (by positivity) hk0]
  have h1 : |(conj (w k) * (Xn S.Ω j w) k).im| ≤ ‖w k‖ * ‖(Xn S.Ω j w) k‖ := by
    refine (Complex.abs_im_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
  have h2 : ‖w k‖ * ‖(Xn S.Ω j w) k‖ ≤ ‖w k‖ * (2 * ‖w j‖) :=
    mul_le_mul_of_nonneg_left (hXk.trans hX) hk0.le
  nlinarith [h1, h2]

theorem Hyp.ang_gamma_continuous (S : Hyp) {z : K} (hz : z ∈ ball (0 : K) S.R) (j k : ℤ) (hk : z k ≠ 0) :
    Continuous (fun s => ang S j k (S.φ j s z)) := by
  refine continuous_iff_continuousAt.2 fun s => ?_
  have hk' : S.φ j s z k ≠ 0 := by
    intro h
    have := S.gamma_norm_coord hz j k s
    rw [h, norm_zero] at this
    exact hk (norm_eq_zero.1 this.symm)
  exact ContinuousAt.comp (g := ang S j k) (f := fun s => S.φ j s z) (x := s)
    (S.ang_continuousAt (S.φ_mem j z hz s) j k hk') (S.gamma_continuous hz j).continuousAt

/-- The angle lift of the `k`th coordinate of the loop. -/
theorem Hyp.gamma_coord (S : Hyp) {z : K} (hz : z ∈ ball (0 : K) S.R) (j k : ℤ) (hk : z k ≠ 0) (s : ℝ) :
    S.φ j s z k = z k * Complex.exp (Complex.I * ((∫ u in (0 : ℝ)..s, ang S j k (S.φ j u z) : ℝ) : ℂ)) := by
  set θ : ℝ → ℝ := fun s => ∫ u in (0 : ℝ)..s, ang S j k (S.φ j u z) with hθ
  have hcont := S.ang_gamma_continuous hz j k hk
  have hθd : ∀ s, HasDerivAt θ (ang S j k (S.φ j s z)) s := fun s =>
    (hcont.integral_hasStrictDerivAt 0 s).hasDerivAt
  have hg : ∀ s : ℝ, HasDerivAt (fun r => S.φ j r z k * Complex.exp (-(Complex.I * (θ r : ℂ)))) 0 s := by
    intro s
    have h1 := S.gamma_hasDerivAt hz j k s
    have h2 : HasDerivAt (fun r => -(Complex.I * (θ r : ℂ))) (-(Complex.I * (ang S j k (S.φ j s z) : ℂ))) s :=
      (((hθd s).ofReal_comp).const_mul Complex.I).neg
    have h3 := h2.cexp
    have h4 := h1.mul h3
    refine h4.congr_deriv ?_
    have hk' : S.φ j s z k ≠ 0 := by
      intro h
      have := S.gamma_norm_coord hz j k s
      rw [h, norm_zero] at this
      exact hk (norm_eq_zero.1 this.symm)
    rw [S.Xn_coord_eq (S.φ_mem j z hz s) j k hk']
    ring
  have hdiff : Differentiable ℝ (fun r => S.φ j r z k * Complex.exp (-(Complex.I * (θ r : ℂ)))) :=
    fun s => (hg s).differentiableAt
  have hconst := is_const_of_deriv_eq_zero hdiff (fun s => (hg s).deriv) s 0
  have h0 : θ 0 = 0 := by simp [hθ]
  simp only [S.φ_zero, h0] at hconst
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, mul_one] at hconst
  have hne : Complex.exp (-(Complex.I * (θ s : ℂ))) ≠ 0 := Complex.exp_ne_zero _
  have : S.φ j s z k = z k * Complex.exp (Complex.I * (θ s : ℂ)) := by
    have h5 : S.φ j s z k = z k * (Complex.exp (-(Complex.I * (θ s : ℂ))))⁻¹ := by
      field_simp
      exact hconst
    rw [h5, ← Complex.exp_neg, neg_neg]
  exact this

/-- The winding is an integer multiple of `2π`: only `φ_j^{2π} = id` is used. -/
theorem Hyp.winding_int (S : Hyp) {z : K} (hz : z ∈ ball (0 : K) S.R) (j k : ℤ) (hk : z k ≠ 0) :
    ∃ n : ℤ, ∫ s in (0 : ℝ)..(2 * Real.pi), ang S j k (S.φ j s z) = 2 * Real.pi * n := by
  have h := S.gamma_coord hz j k hk (2 * Real.pi)
  rw [S.φ_period j z hz] at h
  have h1 : Complex.exp (Complex.I * ((∫ u in (0 : ℝ)..(2 * Real.pi), ang S j k (S.φ j u z) : ℝ) : ℂ)) = 1 := by
    have : z k * Complex.exp (Complex.I * ((∫ u in (0 : ℝ)..(2 * Real.pi), ang S j k (S.φ j u z) : ℝ) : ℂ)) =
        z k * 1 := by rw [mul_one]; exact h.symm
    exact mul_left_cancel₀ hk this
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h1
  refine ⟨n, ?_⟩
  have h2 : Complex.I * ((∫ u in (0 : ℝ)..(2 * Real.pi), ang S j k (S.φ j u z) : ℝ) : ℂ) =
      Complex.I * ((2 * Real.pi * n : ℝ) : ℂ) := by
    rw [hn]; push_cast; ring
  have h3 := mul_left_cancel₀ Complex.I_ne_zero h2
  exact_mod_cast h3

/-- A continuous function on an open interval with values in `2πℤ` is constant. -/
theorem const_of_two_pi_int {a b : ℝ} {g : ℝ → ℝ} (hg : ContinuousOn g (Ioo a b))
    (hint : ∀ x ∈ Ioo a b, ∃ n : ℤ, g x = 2 * Real.pi * n) {x y : ℝ} (hx : x ∈ Ioo a b)
    (hy : y ∈ Ioo a b) : g x = g y := by
  have key : ∀ {x y : ℝ}, x ∈ Ioo a b → y ∈ Ioo a b → x ≤ y → g x = g y := by
    intro x y hx hy hxy
    by_contra hne
    obtain ⟨m, hm⟩ := hint x hx
    obtain ⟨n, hn⟩ := hint y hy
    have hsub : Icc x y ⊆ Ioo a b := fun t ht => ⟨lt_of_lt_of_le hx.1 ht.1, lt_of_le_of_lt ht.2 hy.2⟩
    have hcont : ContinuousOn g (Icc x y) := hg.mono hsub
    have hmn : m ≠ n := by
      intro h; apply hne; rw [hm, hn, h]
    have hpi := Real.pi_pos
    rcases lt_or_gt_of_ne hmn with hlt | hgt
    · have hlt' : (m : ℝ) < n := by exact_mod_cast hlt
      have hxy' : g x ≤ g y := by rw [hm, hn]; nlinarith
      have hmem : g x + Real.pi ∈ Icc (g x) (g y) := by
        refine ⟨by linarith, ?_⟩
        rw [hm, hn]
        have : (m : ℝ) + 1 ≤ n := by exact_mod_cast hlt
        nlinarith
      obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc hxy hcont hmem
      obtain ⟨p, hp⟩ := hint t (hsub ht)
      rw [hp, hm] at hgt
      have : (2 * (p : ℝ) - 2 * m : ℝ) = 1 := by
        have : 2 * Real.pi * p = 2 * Real.pi * m + Real.pi := hgt
        nlinarith
      have h2 : (2 * (p - m) : ℤ) = 1 := by exact_mod_cast (by linarith : (2 * ((p : ℝ) - m)) = 1)
      omega
    · have hgt' : (n : ℝ) < m := by exact_mod_cast hgt
      have hxy' : g y ≤ g x := by rw [hm, hn]; nlinarith
      have hmem : g y + Real.pi ∈ Icc (g y) (g x) := by
        refine ⟨by linarith, ?_⟩
        rw [hm, hn]
        have : (n : ℝ) + 1 ≤ m := by exact_mod_cast hgt
        nlinarith
      obtain ⟨t, ht, hgt2⟩ := intermediate_value_Icc' hxy hcont hmem
      obtain ⟨p, hp⟩ := hint t (hsub ht)
      rw [hp, hn] at hgt2
      have h2 : (2 * (p - n) : ℤ) = 1 := by
        have : 2 * Real.pi * p = 2 * Real.pi * n + Real.pi := hgt2
        exact_mod_cast (by nlinarith : (2 * ((p : ℝ) - n)) = 1)
      omega
  rcases le_total x y with h | h
  · exact key hx hy h
  · exact (key hy hx h).symm

theorem norm_rsmul_coord {ε : ℝ} (hε : 0 ≤ ε) (z : K) (n : ℤ) : ‖(ε • z) n‖ = ε * ‖z n‖ := by
  rw [rsmul_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg hε]

theorem ray_mem {ρ c : ℝ} {z : K} (hz0 : 0 < ‖z‖) (hc : c * ‖z‖ ≤ ρ) {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) c) :
    ε • z ∈ ball (0 : K) ρ := by
  rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hε.1.le]
  have : ε * ‖z‖ < c * ‖z‖ := mul_lt_mul_of_pos_right hε.2 hz0
  linarith

theorem ray_coord_ne {z : K} {k : ℤ} (hk : z k ≠ 0) {ε : ℝ} (hε : 0 < ε) : (ε • z) k ≠ 0 := by
  rw [rsmul_apply]
  exact mul_ne_zero (Complex.ofReal_ne_zero.2 hε.ne') hk

theorem Hyp.gamma_coord_ne (S : Hyp) {z : K} (hz : z ∈ ball (0 : K) S.R) (j k : ℤ) (hk : z k ≠ 0) (s : ℝ) :
    S.φ j s z k ≠ 0 := by
  intro h
  have := S.gamma_norm_coord hz j k s
  rw [h, norm_zero] at this
  exact hk (norm_eq_zero.1 this.symm)

/-- Continuity of the winding along the ray `ε ↦ ε z`, `0 < ε < c`, `c‖z‖ ≤ ρ`. -/
theorem Hyp.winding_cont (S : Hyp) {ρ : ℝ} (hρ : ρ ≤ S.R) {z : K} (j k : ℤ) (hk : z k ≠ 0) {c : ℝ}
    (hc : c * ‖z‖ ≤ ρ) :
    ContinuousOn (fun ε : ℝ => ∫ s in (0 : ℝ)..(2 * Real.pi), ang S j k (S.φ j s (ε • z))) (Ioo 0 c) := by
  have hz0 : 0 < ‖z‖ := by
    refine norm_pos_iff.2 ?_
    rintro rfl
    simp at hk
  intro ε₀ hε₀
  refine ContinuousAt.continuousWithinAt ?_
  have hT : Ioo (0 : ℝ) c ∈ 𝓝 ε₀ := isOpen_Ioo.mem_nhds hε₀
  refine intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun _ => 2 * ‖z j‖ / ‖z k‖) ?_ ?_ ?_ ?_
  · filter_upwards [hT] with ε hε
    have hzε := ball_subset_ball hρ (ray_mem hz0 hc hε)
    exact (S.ang_gamma_continuous hzε j k (ray_coord_ne hk hε.1)).aestronglyMeasurable
  · filter_upwards [hT] with ε hε
    refine Filter.Eventually.of_forall fun s _ => ?_
    have hzε := ball_subset_ball hρ (ray_mem hz0 hc hε)
    have hk2 := S.gamma_coord_ne hzε j k (ray_coord_ne hk hε.1) s
    have h1 := S.ang_abs_le (S.φ_mem j _ hzε s) j k hk2
    rw [Real.norm_eq_abs]
    refine h1.trans (le_of_eq ?_)
    rw [S.gamma_norm_coord hzε j k s, S.gamma_norm_coord hzε j j s, norm_rsmul_coord hε.1.le,
      norm_rsmul_coord hε.1.le]
    have : 0 < ε := hε.1
    have hzk : 0 < ‖z k‖ := norm_pos_iff.2 hk
    field_simp
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall fun s _ => ?_
    have hzε := ball_subset_ball hρ (ray_mem hz0 hc hε₀)
    have hdiff : ContinuousAt (S.φ j s) (ε₀ • z) :=
      (S.diffAt_flow hρ j (ray_mem hz0 hc hε₀) s).continuousAt
    have hcomp : ContinuousAt (fun ε : ℝ => S.φ j s (ε • z)) ε₀ :=
      ContinuousAt.comp (g := S.φ j s) (f := fun ε : ℝ => ε • z) (x := ε₀) hdiff
        (continuous_id.smul continuous_const).continuousAt
    have hk2 := S.gamma_coord_ne hzε j k (ray_coord_ne hk hε₀.1) s
    exact ContinuousAt.comp (g := ang S j k) (f := fun ε : ℝ => S.φ j s (ε • z)) (x := ε₀)
      (S.ang_continuousAt (S.φ_mem j _ hzε s) j k hk2) hcomp

/-- **The winding vector of the loop `s ↦ φ_j^s(z)` is `−e_j`**: for `z ∈ B_ρ` with `z_k ≠ 0`,
`∫_0^{2π} ang_k(φ_j^s z) ds = −2π δ_{jk}`. -/
theorem Hyp.winding (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) {z : K} (hz : z ∈ ball (0 : K) ρ) (j k : ℤ)
    (hk : z k ≠ 0) :
    ∫ s in (0 : ℝ)..(2 * Real.pi), ang S j k (S.φ j s z) = -(2 * Real.pi) * (if k = j then 1 else 0) := by
  have hρ := hL.ρR
  have hz0 : 0 < ‖z‖ := by
    refine norm_pos_iff.2 ?_
    rintro rfl
    simp at hk
  have hzn : ‖z‖ < ρ := mem_ball_zero_iff.1 hz
  set c := ρ / ‖z‖ with hcdef
  have hc : c * ‖z‖ ≤ ρ := by rw [hcdef, div_mul_cancel₀ _ hz0.ne']
  have hc1 : 1 < c := by rw [hcdef, lt_div_iff₀ hz0]; simpa using hzn
  set W : ℝ → ℝ := fun ε => ∫ s in (0 : ℝ)..(2 * Real.pi), ang S j k (S.φ j s (ε • z)) with hW
  have hcont := S.winding_cont hρ j k hk hc
  have hint : ∀ ε ∈ Ioo (0 : ℝ) c, ∃ n : ℤ, W ε = 2 * Real.pi * n := fun ε hε =>
    S.winding_int (ball_subset_ball hρ (ray_mem hz0 hc hε)) j k (ray_coord_ne hk hε.1)
  have h1 : (1 : ℝ) ∈ Ioo (0 : ℝ) c := ⟨one_pos, hc1⟩
  have hW1 : W 1 = ∫ s in (0 : ℝ)..(2 * Real.pi), ang S j k (S.φ j s z) := by simp [hW]
  set B : ℝ := M * ‖z‖ ^ 2 * ‖z j‖ / ‖z k‖ with hB
  have hB0 : 0 ≤ B := by
    have := hL.M0
    positivity
  set ε : ℝ := min (c / 2) (1 / (2 * (B + 1))) with hεdef
  have hεpos : 0 < ε := lt_min (by linarith) (by positivity)
  have hεc : ε < c := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hεT : ε ∈ Ioo (0 : ℝ) c := ⟨hεpos, hεc⟩
  have hε1 : ε ≤ 1 / (2 * (B + 1)) := min_le_right _ _
  have hBε : B * ε ^ 2 < 1 / 2 := by
    have hε1' : ε ≤ 1 / 2 := by
      refine hε1.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have : B * ε ^ 2 ≤ B * ε := by
      have : ε ^ 2 ≤ ε := by nlinarith
      exact mul_le_mul_of_nonneg_left this hB0
    have h2 : B * ε ≤ B * (1 / (2 * (B + 1))) := mul_le_mul_of_nonneg_left hε1 hB0
    have h3 : B * (1 / (2 * (B + 1))) < 1 / 2 := by
      rw [← mul_div_assoc, mul_one, div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hzε : ε • z ∈ ball (0 : K) ρ := ray_mem hz0 hc hεT
  have hkε := ray_coord_ne hk hεpos
  have hpt : ∀ s, |ang S j k (S.φ j s (ε • z)) + (if k = j then 1 else 0)| ≤ B * ε ^ 2 := by
    intro s
    have hwρ : S.φ j s (ε • z) ∈ ball (0 : K) ρ := by
      rw [mem_ball_zero_iff, S.norm_flow (ball_subset_ball hρ hzε) j s]
      exact mem_ball_zero_iff.1 hzε
    have hwk := S.gamma_coord_ne (ball_subset_ball hρ hzε) j k hkε s
    have h1 := ang_bound S hL hwρ j k hwk
    refine h1.trans (le_of_eq ?_)
    rw [S.norm_flow (ball_subset_ball hρ hzε) j s, S.gamma_norm_coord (ball_subset_ball hρ hzε) j j s,
      S.gamma_norm_coord (ball_subset_ball hρ hzε) j k s, norm_smul, norm_rsmul_coord hεpos.le,
      norm_rsmul_coord hεpos.le, Real.norm_of_nonneg hεpos.le, hB]
    have hzk : 0 < ‖z k‖ := norm_pos_iff.2 hk
    field_simp
  have hcs := S.ang_gamma_continuous (ball_subset_ball hρ hzε) j k hkε
  have hsum : ‖∫ s in (0 : ℝ)..(2 * Real.pi), (ang S j k (S.φ j s (ε • z)) + (if k = j then 1 else 0))‖ ≤
      B * ε ^ 2 * |2 * Real.pi - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun s _ => ?_
    rw [Real.norm_eq_abs]
    exact hpt s
  rw [intervalIntegral.integral_add (hcs.intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const] at hsum
  simp only [sub_zero, smul_eq_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hsum
  obtain ⟨n, hn⟩ := hint ε hεT
  have hWε : W ε = ∫ s in (0 : ℝ)..(2 * Real.pi), ang S j k (S.φ j s (ε • z)) := rfl
  rw [← hWε, hn] at hsum
  have hpi := Real.pi_pos
  have hlt : |2 * Real.pi * n + 2 * Real.pi * (if k = j then 1 else 0)| < Real.pi := by
    have : B * ε ^ 2 * (2 * Real.pi) < 1 / 2 * (2 * Real.pi) :=
      mul_lt_mul_of_pos_right hBε (by positivity)
    rw [Real.norm_eq_abs] at hsum
    linarith
  have hWeq : W ε = W 1 := const_of_two_pi_int hcont hint hεT h1
  rw [← hW1, ← hWeq, hn]
  by_cases hkj : k = j
  · simp only [hkj, if_true] at hlt ⊢
    rw [abs_lt] at hlt
    have h1' : (n : ℝ) + 1 < 1 := by nlinarith
    have h2' : (-1 : ℝ) < (n : ℝ) + 1 := by nlinarith
    have h3 : n + 1 < 1 := by exact_mod_cast h1'
    have h4 : -1 < n + 1 := by exact_mod_cast h2'
    have : n = -1 := by omega
    subst this
    push_cast
    ring
  · simp only [hkj, if_false] at hlt ⊢
    rw [abs_lt] at hlt
    have h1' : (n : ℝ) < 1 := by nlinarith
    have h2' : (-1 : ℝ) < (n : ℝ) := by nlinarith
    have h3 : n < 1 := by exact_mod_cast h1'
    have h4 : -1 < n := by exact_mod_cast h2'
    have : n = 0 := by omega
    subst this
    simp

end QuantumNLS.ResetMoser

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ResetMoser.Hyp.Xn_coord_eq
#print axioms QuantumNLS.ResetMoser.Hyp.gamma_coord
#print axioms QuantumNLS.ResetMoser.Hyp.winding_int
#print axioms QuantumNLS.ResetMoser.const_of_two_pi_int
#print axioms QuantumNLS.ResetMoser.Hyp.winding_cont
#print axioms QuantumNLS.ResetMoser.Hyp.winding
