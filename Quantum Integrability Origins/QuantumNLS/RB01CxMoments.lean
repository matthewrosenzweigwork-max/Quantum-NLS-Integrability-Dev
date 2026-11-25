import Mathlib
import QuantumNLS.RB01Moments
import QuantumNLS.RB01ParamInt

/-! R-EC25334D (`thm:global-B01-actions`), stage RB01-20: the contour moments `s_{j,n}`, `α_n`, `τ_n` and the
Cauchy quotient `H_n` as bounded holomorphic families on one complex neighborhood, for all high labels (source
`collective_actions.tex:377-411`: "These are bounded holomorphic families, with `α_n, c_n, τ_n` uniformly small
when the chosen trace accuracy is small"; eq. `GB01-H`; "On the outer circle the quotient `f_n/𝒫_n` is as close to
`h_0` as desired ... Cauchy's formula on the inner disk ... gives `|H_n(w, q) + L²| < L²/4`"; "All assertions here
are uniform bounded holomorphic-family assertions").

Objects: the frozen `RB01Moments.mom`, `alphaC`, `cC`, `tauC`, `PC`, `HC` on every complexified field
`x = (u, v) ∈ L²(𝕋_L) × L²(𝕋_L)`; `fx κ u v n w = cxDisc κ u v (p_n + w)² − 4` (RB01CxGauge).
* `analytic_fx_joint`, `analytic_fx_x`: `(x, w) ↦ fx` is entire (frozen `ComplexifiedDiscriminant.analyticOnNhd_cxDisc`);
  `analytic_dfx`: `x ↦ ∂_w fx(x, w)` is entire (Cauchy's formula for the derivative + `RB01ParamInt`);
* free part: `freeF L w = w² G₀(w)` with `G₀` entire and `≠ 0` on `|w| ≤ 3d`, so the free moments vanish
  (`mom_free`, via the frozen `RB01Moments.moment_of_factor`); `freeF_near`: `|freeF + (Lw)²| ≤ (10/96)|Lw|⁴`;
* `logderiv_diff` (generic Cauchy estimates): `|f'/f − F'/F| ≤ (ε/r)/(b−ε) + (A/r)ε/(b(b−ε))`;
* **`cx_moments`**: for every `u₀` there are `N`, `ρ > 0` such that for `|n| > N`, on the ball `B((u₀, ū₀), ρ)`
  (`RB01CxGauge.cx_prep`): `x ↦ mom κ x n j` (every `j`), `alphaC`, `tauC` are complex analytic;
  `|alphaC| ≤ d/16`, `|tauC| ≤ d²/9` (perturbation from the free moments, which vanish; no Rouché);
  `(x, w) ↦ HC` is complex analytic on `B × {|w| < 3d}`; `|𝒫_n| ≥ 8d²` on `|ξ| = 3d`;
  `|HC(x, w) + L²| ≤ L²/2` for `|w| ≤ 17d/8`; `|fx| ≤ 6/5` on `|w| ≤ 4d`. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Filter Topology Set Metric

namespace QuantumNLS.RB01CxMoments

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.RB01RootPrep (freeF freeF_eq freeF_lower dd ε₀ dd_pos)
open QuantumNLS.RB01CxGauge (fx cx_prep)
open QuantumNLS.RB01Moments (mom alphaC cC tauC PC HC moment_of_factor)
open QuantumNLS.ComplexifiedDiscriminant (cxDisc analyticOnNhd_cxDisc cxDisc_local)
open QuantumNLS.RB01ParamInt (analyticOnNhd_circleIntegral norm_circleIntegral_le)

/-! ## Generic one-variable estimates -/

theorem norm_deriv_le {f : ℂ → ℂ} (hf : Differentiable ℂ f) {w : ℂ} {r C : ℝ} (hr : 0 < r)
    (hC : ∀ z ∈ closedBall w r, ‖f z‖ ≤ C) : ‖deriv f w‖ ≤ C / r :=
  Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hf.diffContOnCl
    (fun z hz => hC z (sphere_subset_closedBall hz))

/-- Difference of logarithmic derivatives (Cauchy estimates). -/
theorem logderiv_diff {f F : ℂ → ℂ} (hf : Differentiable ℂ f) (hF : Differentiable ℂ F) {w : ℂ} {r ε A b : ℝ}
    (hr : 0 < r) (hδ : ∀ z ∈ closedBall w r, ‖f z - F z‖ ≤ ε) (hA : ∀ z ∈ closedBall w r, ‖F z‖ ≤ A)
    (hb : b ≤ ‖F w‖) (hεb : ε < b) :
    ‖deriv f w / f w - deriv F w / F w‖ ≤ (ε / r) / (b - ε) + (A / r) * ε / (b * (b - ε)) := by
  have hw := mem_closedBall_self (x := w) hr.le
  have hδw := hδ w hw
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hδw
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA w hw)
  have hb0 : 0 < b - ε := by linarith
  have hfw : b - ε ≤ ‖f w‖ := by
    have h1 := norm_sub_le (f w) (f w - F w)
    rw [sub_sub_cancel] at h1
    linarith
  have hfne : f w ≠ 0 := norm_pos_iff.1 (by linarith)
  have hFne : F w ≠ 0 := norm_pos_iff.1 (by linarith)
  have hd : ‖deriv (fun z => f z - F z) w‖ ≤ ε / r := norm_deriv_le (hf.sub hF) hr hδ
  have hF' : ‖deriv F w‖ ≤ A / r := norm_deriv_le hF hr hA
  have key : deriv f w / f w - deriv F w / F w =
      deriv (fun z => f z - F z) w / f w - deriv F w * (f w - F w) / (f w * F w) := by
    have hds : deriv (fun z => f z - F z) w = deriv f w - deriv F w := deriv_sub (hf w) (hF w)
    rw [hds]
    field_simp
    ring
  rw [key]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_div, norm_div, norm_mul, norm_mul]
  have h1 : ‖deriv (fun z => f z - F z) w‖ / ‖f w‖ ≤ (ε / r) / (b - ε) :=
    div_le_div₀ (by positivity) hd hb0 hfw
  have h2 : ‖deriv F w‖ * ‖f w - F w‖ / (‖f w‖ * ‖F w‖) ≤ (A / r) * ε / (b * (b - ε)) := by
    apply div_le_div₀ (by positivity) (mul_le_mul hF' hδw (norm_nonneg _) (by positivity))
      (mul_pos (by linarith) hb0)
    rw [mul_comm b]
    exact mul_le_mul hfw hb (by linarith) (norm_nonneg _)
  linarith

theorem ball_in {E : Type*} [NormedAddCommGroup E] {x₀ x : E} {ρ : ℝ} (hx : x ∈ ball x₀ ρ) :
    0 < ρ - dist x x₀ ∧ ball x (ρ - dist x x₀) ⊆ ball x₀ ρ :=
  ⟨sub_pos.2 hx, ball_subset_ball' (by linarith)⟩

variable {L κ : ℝ} [Fact (0 < L)]

/-! ## Analyticity of `fx` and of its `w`-derivative in the field -/

theorem analytic_fx_joint (κ : ℝ) (n : ℤ) :
    AnalyticOnNhd ℂ (fun p : (L2T L × L2T L) × ℂ => fx κ p.1.1 p.1.2 n p.2) univ := by
  intro p _
  have hg : AnalyticAt ℂ (fun p : (L2T L × L2T L) × ℂ =>
      (p.1.1, p.1.2, (QuantumNLS.LocalSpectral.pm L n : ℂ) + p.2)) p :=
    ((analyticAt_fst.comp analyticAt_fst).prod ((analyticAt_snd.comp analyticAt_fst).prod
      (analyticAt_const.add analyticAt_snd)))
  have h := (analyticOnNhd_cxDisc (L := L) κ _ (mem_univ _)).comp hg
  exact (h.pow 2).sub analyticAt_const

theorem analytic_fx_x (κ : ℝ) (n : ℤ) (w : ℂ) :
    AnalyticOnNhd ℂ (fun x : L2T L × L2T L => fx κ x.1 x.2 n w) univ := by
  intro x _
  have h := (analytic_fx_joint κ n (x, w) (mem_univ _)).comp (f := fun y : L2T L × L2T L => (y, w)) (x := x)
    (analyticAt_id.prod analyticAt_const)
  exact h

theorem differentiable_fx (κ : ℝ) (u v : L2T L) (n : ℤ) : Differentiable ℂ (fx κ u v n) := by
  intro w
  have h := (analytic_fx_joint κ n ((u, v), w) (mem_univ _)).comp (f := fun z : ℂ => ((u, v), z)) (x := w)
    (analyticAt_const.prod analyticAt_id)
  exact h.differentiableAt

theorem fx_locbound (κ : ℝ) (n : ℤ) (x : L2T L × L2T L) (w : ℂ) (R : ℝ) :
    ∃ M : ℝ, ∀ y ∈ ball x 1, ∀ ξ ∈ closedBall w R, ‖fx κ y.1 y.2 n ξ‖ ≤ M := by
  obtain ⟨M, -, -, hM, -⟩ := cxDisc_local (L := L) κ
    (x.1, x.2, (QuantumNLS.LocalSpectral.pm L n : ℂ) + w) (|R| + 1)
  refine ⟨M ^ 2 + 4, fun y hy ξ hξ => ?_⟩
  have hmem : (y.1, y.2, (QuantumNLS.LocalSpectral.pm L n : ℂ) + ξ) ∈
      ball (x.1, x.2, (QuantumNLS.LocalSpectral.pm L n : ℂ) + w) (|R| + 1) := by
    rw [mem_ball, Prod.dist_eq, max_lt_iff] at hy
    rw [mem_closedBall] at hξ
    simp only [mem_ball, Prod.dist_eq, max_lt_iff, dist_add_left]
    refine ⟨by linarith [abs_nonneg R], by linarith [abs_nonneg R], by linarith [le_abs_self R]⟩
  have h := hM _ hmem
  unfold fx
  calc ‖cxDisc κ y.1 y.2 ((QuantumNLS.LocalSpectral.pm L n : ℂ) + ξ) ^ 2 - 4‖
      ≤ ‖cxDisc κ y.1 y.2 ((QuantumNLS.LocalSpectral.pm L n : ℂ) + ξ)‖ ^ 2 + ‖(4 : ℂ)‖ :=
        (norm_sub_le _ _).trans (by rw [norm_pow])
    _ ≤ M ^ 2 + 4 := by
        have h0 := norm_nonneg (cxDisc κ y.1 y.2 ((QuantumNLS.LocalSpectral.pm L n : ℂ) + ξ))
        have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
        rw [h4]
        nlinarith

theorem two_pi_I_ne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
  have := Real.pi_pos
  simp [Real.pi_ne_zero, Complex.I_ne_zero]

theorem deriv_fx_eq (κ : ℝ) (u v : L2T L) (n : ℤ) (w : ℂ) :
    deriv (fx κ u v n) w =
      (2 * Real.pi * Complex.I)⁻¹ * ∮ ξ in C(w, 1), (1 / (ξ - w) ^ 2) * fx κ u v n ξ := by
  have h := ((differentiable_fx κ u v n).differentiableOn (s := closedBall w 1)).deriv_eq_smul_circleIntegral
    one_pos
  simp only [smul_eq_mul] at h
  rw [h, ← mul_assoc, inv_mul_cancel₀ two_pi_I_ne, one_mul]

theorem analytic_dfx (κ : ℝ) (n : ℤ) (w : ℂ) :
    AnalyticOnNhd ℂ (fun x : L2T L × L2T L => deriv (fx κ x.1 x.2 n) w) univ := by
  have heq : (fun x : L2T L × L2T L => deriv (fx κ x.1 x.2 n) w) =
      fun x => (2 * Real.pi * Complex.I)⁻¹ * ∮ ξ in C(w, 1), (1 / (ξ - w) ^ 2) * fx κ x.1 x.2 n ξ :=
    funext fun x => deriv_fx_eq κ x.1 x.2 n w
  rw [heq]
  intro x hx
  refine analyticAt_const.mul (analyticOnNhd_circleIntegral zero_le_one (fun ξ _ => ?_) (fun y _ => ?_)
    (fun y _ => ?_) x hx)
  · exact fun y _ => analyticAt_const.mul (analytic_fx_x κ n ξ y (mem_univ _))
  · refine (continuousOn_const.div ((continuousOn_id.sub continuousOn_const).pow 2) ?_).mul
      (differentiable_fx κ y.1 y.2 n).continuous.continuousOn
    intro ξ hξ
    exact pow_ne_zero 2 (sub_ne_zero.2 (ne_of_mem_sphere hξ one_ne_zero))
  · obtain ⟨M, hM⟩ := fx_locbound κ n y w 1
    refine ⟨1, one_pos, M, subset_univ _, fun z hz ξ hξ => ?_⟩
    have hn : ‖ξ - w‖ = 1 := by rw [← dist_eq_norm]; exact mem_sphere.1 hξ
    rw [norm_mul, norm_div, norm_pow, hn, norm_one, one_pow, div_one, one_mul]
    exact hM z hz ξ (sphere_subset_closedBall hξ)

/-! ## The free function -/

/-- `sin(Lw/2)/w`, extended by `L/2` at `0`. -/
def Sfree (L : ℝ) : ℂ → ℂ := dslope (fun w : ℂ => Complex.sin (L * w / 2)) 0

/-- `G₀ = freeF / w²` (entire). -/
def Gfree (L : ℝ) (w : ℂ) : ℂ := -4 * Sfree L w ^ 2

theorem differentiable_Gfree : Differentiable ℂ (Gfree L) := by
  have hS : DifferentiableOn ℂ (Sfree L) univ :=
    (Complex.differentiableOn_dslope univ_mem).2 (by fun_prop)
  have hS' : Differentiable ℂ (Sfree L) := differentiableOn_univ.1 hS
  unfold Gfree
  fun_prop

theorem Sfree_of_ne {w : ℂ} (hw : w ≠ 0) : Sfree L w = w⁻¹ * Complex.sin (L * w / 2) := by
  unfold Sfree
  rw [dslope_of_ne _ hw, slope_def_module]
  simp

theorem Sfree_zero : Sfree L 0 = (L : ℂ) / 2 := by
  unfold Sfree
  rw [dslope_same]
  have h : HasDerivAt (fun w : ℂ => Complex.sin (L * w / 2)) (Complex.cos (L * 0 / 2) * (L * 1 / 2)) 0 :=
    (((hasDerivAt_id (0 : ℂ)).const_mul (L : ℂ)).div_const 2).csin
  rw [h.deriv]
  simp

theorem freeF_factor (w : ℂ) : freeF L w = (w - 0) * (w - 0) * Gfree L w := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [freeF]
    norm_num
  · rw [freeF_eq, Gfree, Sfree_of_ne hw]
    field_simp
    ring

theorem Gfree_ne {w : ℂ} (hw : ‖w‖ ≤ 4 * dd L) : Gfree L w ≠ 0 := by
  have hL : 0 < L := Fact.out
  rcases eq_or_ne w 0 with rfl | hw0
  · rw [Gfree, Sfree_zero]
    have : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hL.ne'
    simp [this]
  · intro h
    have hF := freeF_factor (L := L) w
    rw [h, mul_zero] at hF
    have hle : ‖w‖ ≤ 1 / L := by
      have : 4 * dd L = 1 / L := by unfold dd; field_simp
      linarith
    have hlow := freeF_lower (L := L) hle
    rw [hF, norm_zero] at hlow
    have : 0 < (L * ‖w‖) ^ 2 / 4 := by
      have := norm_pos_iff.2 hw0
      positivity
    linarith

theorem differentiable_freeF : Differentiable ℂ (freeF L) := by
  unfold freeF
  fun_prop

/-- The free moments vanish for `j ≥ 1` (double zero at `0`). -/
theorem mom_free {j : ℕ} (hj : 1 ≤ j) :
    (2 * Real.pi * Complex.I)⁻¹ * ∮ w in C(0, 3 * dd L), w ^ j * (deriv (freeF L) w / freeF L w) = 0 := by
  have hd := dd_pos (L := L)
  have h := moment_of_factor (F := freeF L) (G := Gfree L) (β₁ := 0) (β₂ := 0) (r := 3 * dd L) (by positivity)
    differentiable_Gfree freeF_factor (by simp; positivity) (by simp; positivity)
    (fun w hw => Gfree_ne (by rw [mem_closedBall, dist_zero_right] at hw; linarith)) j
  rw [h, zero_pow (by omega), add_zero]

/-- `freeF L w = 2 cos(Lw) − 2`, so `|freeF + (Lw)²| ≤ (10/96)|Lw|⁴` for `|Lw| ≤ 1`. -/
theorem freeF_near {w : ℂ} (hw : ‖(L : ℂ) * w‖ ≤ 1) :
    ‖freeF L w + ((L : ℂ) * w) ^ 2‖ ≤ ‖(L : ℂ) * w‖ ^ 4 * (10 / 96) := by
  have hc := Complex.cos_bound hw
  have he : freeF L w + ((L : ℂ) * w) ^ 2 = 2 * (Complex.cos ((L : ℂ) * w) - (1 - ((L : ℂ) * w) ^ 2 / 2)) := by
    have h2 : Complex.cos ((L : ℂ) * w) = 2 * Complex.cos ((L : ℂ) * w / 2) ^ 2 - 1 := by
      rw [← Complex.cos_two_mul]; ring_nf
    unfold freeF
    rw [h2]
    ring
  rw [he, norm_mul, Complex.norm_two]
  linarith

theorem norm_Lw {w : ℂ} : ‖(L : ℂ) * w‖ = L * ‖w‖ := by
  have hL : 0 < L := Fact.out
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]

theorem Ld : L * dd L = 1 / 4 := by
  have hL : 0 < L := Fact.out
  unfold dd; field_simp

theorem L2_eq : L ^ 2 = 1 / (16 * dd L ^ 2) := by
  have hd := dd_pos (L := L)
  have h4 : L ^ 2 * (16 * dd L ^ 2) = 1 := by
    rw [show L ^ 2 * (16 * dd L ^ 2) = 16 * (L * dd L) ^ 2 by ring, Ld]; norm_num
  rw [eq_div_iff (by positivity)]
  exact h4

theorem freeF_upper {w : ℂ} (hw : ‖w‖ ≤ 4 * dd L) : ‖freeF L w‖ ≤ 9 / 8 := by
  have hL : 0 < L := Fact.out
  have h1 : ‖(L : ℂ) * w‖ ≤ 1 := by
    rw [norm_Lw]
    have := mul_le_mul_of_nonneg_left hw hL.le
    rw [show L * (4 * dd L) = 4 * (L * dd L) by ring, Ld] at this
    linarith
  have hn := freeF_near h1
  have h0 := norm_nonneg ((L : ℂ) * w)
  have hsq : ‖((L : ℂ) * w) ^ 2‖ ≤ 1 := by rw [norm_pow]; nlinarith
  have h4 : ‖(L : ℂ) * w‖ ^ 4 ≤ 1 := pow_le_one₀ h0 h1
  have := norm_sub_le (freeF L w + ((L : ℂ) * w) ^ 2) (((L : ℂ) * w) ^ 2)
  rw [add_sub_cancel_right] at this
  have h5 : ‖(L : ℂ) * w‖ ^ 4 * (10 / 96) ≤ 10 / 96 := by nlinarith
  linarith

/-! ## Quantitative estimates at a good field -/

/-- The estimates of `RB01CxGauge.cx_prep` at one field and label. -/
def Good (κ : ℝ) (n : ℤ) (x : L2T L × L2T L) : Prop :=
  (∀ w : ℂ, ‖w‖ ≤ 4 * dd L → ‖fx κ x.1 x.2 n w - freeF L w‖ ≤ 7 * ε₀) ∧
  (∀ w : ℂ, dd L / 8 ≤ ‖w‖ → ‖w‖ ≤ 4 * dd L → 9 / 65536 ≤ ‖fx κ x.1 x.2 n w‖)

theorem ε₀_eq : ε₀ = 1 / 65536 := rfl

theorem fx_upper {n : ℤ} {x : L2T L × L2T L} (hx : Good κ n x) {w : ℂ} (hw : ‖w‖ ≤ 4 * dd L) :
    ‖fx κ x.1 x.2 n w‖ ≤ 6 / 5 := by
  have h1 := hx.1 w hw
  have h2 := freeF_upper hw
  have h3 := norm_le_insert' (fx κ x.1 x.2 n w) (freeF L w)
  rw [ε₀_eq] at h1
  linarith

theorem dfx_upper {n : ℤ} {x : L2T L × L2T L} (hx : Good κ n x) {w : ℂ} (hw : ‖w‖ ≤ 3 * dd L) :
    ‖deriv (fx κ x.1 x.2 n) w‖ ≤ 6 / 5 / dd L := by
  have hd := dd_pos (L := L)
  refine norm_deriv_le (differentiable_fx κ x.1 x.2 n) hd fun z hz => fx_upper hx ?_
  rw [mem_closedBall, dist_eq_norm] at hz
  have := norm_le_insert' z w
  have := norm_sub_rev z w
  linarith [norm_le_insert' z w, norm_sub_norm_le z w]

theorem sphere_norm {w : ℂ} (hw : w ∈ sphere (0 : ℂ) (3 * dd L)) : ‖w‖ = 3 * dd L := by
  rwa [mem_sphere, dist_zero_right] at hw

theorem fx_ne_sphere {n : ℤ} {x : L2T L × L2T L} (hx : Good κ n x) {w : ℂ} (hw : w ∈ sphere (0 : ℂ) (3 * dd L)) :
    fx κ x.1 x.2 n w ≠ 0 := by
  have hd := dd_pos (L := L)
  have h := hx.2 w (by rw [sphere_norm hw]; linarith) (by rw [sphere_norm hw]; linarith)
  exact norm_pos_iff.1 (lt_of_lt_of_le (by norm_num) h)

theorem freeF_sphere_lower {w : ℂ} (hw : ‖w‖ = 3 * dd L) : 9 / 64 ≤ ‖freeF L w‖ := by
  have hL : 0 < L := Fact.out
  have hle : ‖w‖ ≤ 1 / L := by
    rw [hw]; have := Ld (L := L)
    have : 3 * dd L = 3 / 4 * (1 / L) := by unfold dd; field_simp
    rw [this]
    have : 0 < 1 / L := by positivity
    linarith
  have h := freeF_lower (L := L) hle
  rw [hw, show L * (3 * dd L) = 3 * (L * dd L) by ring, Ld] at h
  norm_num at h
  linarith

/-- The logarithmic-derivative perturbation bound on `|w| = 3d`. -/
theorem logderiv_sphere {n : ℤ} {x : L2T L × L2T L} (hx : Good κ n x) {w : ℂ} (hw : ‖w‖ = 3 * dd L) :
    ‖deriv (fx κ x.1 x.2 n) w / fx κ x.1 x.2 n w - deriv (freeF L) w / freeF L w‖ ≤ 1 / (140 * dd L) := by
  have hd := dd_pos (L := L)
  have hsub : ∀ z ∈ closedBall w (dd L), ‖z‖ ≤ 4 * dd L := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    have := norm_le_insert' z w
    have h2 := norm_sub_rev z w
    linarith [norm_sub_norm_le z w]
  have h := logderiv_diff (differentiable_fx κ x.1 x.2 n) differentiable_freeF hd
    (fun z hz => hx.1 z (hsub z hz)) (fun z hz => freeF_upper (hsub z hz)) (freeF_sphere_lower hw)
    (by rw [ε₀_eq]; norm_num)
  refine h.trans ?_
  · rw [ε₀_eq]
    have e : (7 * (1 / 65536) / dd L) / (9 / 64 - 7 * (1 / 65536)) +
        (9 / 8 / dd L) * (7 * (1 / 65536)) / (9 / 64 * (9 / 64 - 7 * (1 / 65536))) =
        ((7 / 9209 : ℝ) + 9 / 8 * 7 / 65536 / (9 / 64 * (9209 / 65536))) * (1 / dd L) := by
      field_simp
      ring
    rw [e]
    have hc : (7 / 9209 : ℝ) + 9 / 8 * 7 / 65536 / (9 / 64 * (9209 / 65536)) ≤ 1 / 140 := by norm_num
    calc _ ≤ (1 / 140) * (1 / dd L) := by gcongr
      _ = 1 / (140 * dd L) := by field_simp

theorem circleIntegrable_logderiv {f : ℂ → ℂ} (hf : Differentiable ℂ f) {R : ℝ} (hR : 0 ≤ R)
    (hne : ∀ w ∈ sphere (0 : ℂ) R, f w ≠ 0) (j : ℕ) :
    CircleIntegrable (fun w => w ^ j * (deriv f w / f w)) 0 R := by
  apply ContinuousOn.circleIntegrable hR
  have hd : Continuous (deriv f) := by
    rw [continuous_iff_continuousAt]
    exact fun z => ((hf.analyticAt z).deriv).continuousAt
  exact (continuousOn_id.pow j).mul (hd.continuousOn.div hf.continuous.continuousOn hne)

/-- Moment bounds at a good field. -/
theorem mom_bound {n : ℤ} {x : L2T L × L2T L} (hx : Good κ n x) {j : ℕ} (hj : 1 ≤ j) :
    ‖mom κ x.1 x.2 n j‖ ≤ 3 * dd L * ((3 * dd L) ^ j * (1 / (140 * dd L))) := by
  have hd := dd_pos (L := L)
  have hR : (0 : ℝ) ≤ 3 * dd L := by positivity
  have hFne : ∀ w ∈ sphere (0 : ℂ) (3 * dd L), freeF L w ≠ 0 := fun w hw =>
    norm_pos_iff.1 (lt_of_lt_of_le (by norm_num) (freeF_sphere_lower (sphere_norm hw)))
  have hA := circleIntegrable_logderiv (differentiable_fx κ x.1 x.2 n) hR (fun w hw => fx_ne_sphere hx hw) j
  have hB := circleIntegrable_logderiv (differentiable_freeF (L := L)) hR hFne j
  have h0 := mom_free (L := L) hj
  have hm : mom κ x.1 x.2 n j = (2 * Real.pi * Complex.I)⁻¹ * ∮ w in C(0, 3 * dd L),
      (w ^ j * (deriv (fx κ x.1 x.2 n) w / fx κ x.1 x.2 n w) - w ^ j * (deriv (freeF L) w / freeF L w)) := by
    rw [circleIntegral.integral_sub hA hB, mul_sub, h0, sub_zero]
    rfl
  rw [hm]
  refine norm_circleIntegral_le hR fun w hw => ?_
  rw [← mul_sub, norm_mul, norm_pow, sphere_norm hw]
  exact mul_le_mul_of_nonneg_left (logderiv_sphere hx (sphere_norm hw)) (by positivity)

theorem alpha_tau_bound {n : ℤ} {x : L2T L × L2T L} (hx : Good κ n x) :
    ‖alphaC κ x.1 x.2 n‖ ≤ dd L / 16 ∧ ‖tauC κ x.1 x.2 n‖ ≤ dd L ^ 2 / 9 := by
  have hd := dd_pos (L := L)
  have h1 := mom_bound hx (j := 1) le_rfl
  have h2 := mom_bound hx (j := 2) (by norm_num)
  have e1 : 3 * dd L * ((3 * dd L) ^ 1 * (1 / (140 * dd L))) = 9 / 140 * dd L := by field_simp; ring
  have e2 : 3 * dd L * ((3 * dd L) ^ 2 * (1 / (140 * dd L))) = 27 / 140 * dd L ^ 2 := by field_simp; ring
  rw [e1] at h1
  rw [e2] at h2
  set m1 := mom κ x.1 x.2 n 1
  set m2 := mom κ x.1 x.2 n 2
  have ha : ‖alphaC κ x.1 x.2 n‖ ≤ 9 / 280 * dd L := by
    change ‖m1 / 2‖ ≤ _
    rw [norm_div, Complex.norm_two]
    linarith
  refine ⟨by linarith, ?_⟩
  have hc : ‖cC κ x.1 x.2 n‖ ≤ ((9 / 140 * dd L) ^ 2 + 27 / 140 * dd L ^ 2) / 2 := by
    change ‖(m1 ^ 2 - m2) / 2‖ ≤ _
    rw [norm_div, Complex.norm_two]
    have := norm_sub_le (m1 ^ 2) m2
    rw [norm_pow] at this
    have : ‖m1‖ ^ 2 ≤ (9 / 140 * dd L) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    linarith
  change ‖alphaC κ x.1 x.2 n ^ 2 - cC κ x.1 x.2 n‖ ≤ _
  have := norm_sub_le (alphaC κ x.1 x.2 n ^ 2) (cC κ x.1 x.2 n)
  rw [norm_pow] at this
  have : ‖alphaC κ x.1 x.2 n‖ ^ 2 ≤ (9 / 280 * dd L) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ha 2
  nlinarith

/-- `|𝒫_n| ≥ 8d²` on `|ξ| = 3d` and `|𝒫_n(ξ) − ξ²| ≤ d²/2` there. -/
theorem PC_sphere {n : ℤ} {x : L2T L × L2T L} (hx : Good κ n x) {ξ : ℂ} (hξ : ‖ξ‖ = 3 * dd L) :
    8 * dd L ^ 2 ≤ ‖PC κ x.1 x.2 n ξ‖ ∧ ‖PC κ x.1 x.2 n ξ - ξ ^ 2‖ ≤ dd L ^ 2 / 2 := by
  have hd := dd_pos (L := L)
  obtain ⟨ha, ht⟩ := alpha_tau_bound hx
  set α := alphaC κ x.1 x.2 n
  set τ := tauC κ x.1 x.2 n
  have hP : PC κ x.1 x.2 n ξ = (ξ - α) ^ 2 - τ := rfl
  constructor
  · rw [hP]
    have h1 : 3 * dd L - dd L / 16 ≤ ‖ξ - α‖ := by
      have := norm_sub_norm_le ξ α
      linarith
    have h2 := norm_sub_norm_le ((ξ - α) ^ 2) τ
    rw [norm_pow] at h2
    have h3 : (3 * dd L - dd L / 16) ^ 2 ≤ ‖ξ - α‖ ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
    nlinarith
  · rw [hP, show (ξ - α) ^ 2 - τ - ξ ^ 2 = -(2 * ξ * α) + α ^ 2 - τ by ring]
    have h1 := norm_sub_le (-(2 * ξ * α) + α ^ 2) τ
    have h2 := norm_add_le (-(2 * ξ * α)) (α ^ 2)
    rw [norm_neg, norm_mul, norm_mul, Complex.norm_two, hξ] at h2
    rw [norm_pow] at h2
    have h3 : ‖α‖ ^ 2 ≤ (dd L / 16) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ha 2
    have h4 : 2 * (3 * dd L) * ‖α‖ ≤ 2 * (3 * dd L) * (dd L / 16) := by gcongr
    nlinarith

/-- `|f_n/𝒫_n + L²| ≤ L²/7.5` on `|ξ| = 3d`. -/
theorem quot_sphere {n : ℤ} {x : L2T L × L2T L} (hx : Good κ n x) {ξ : ℂ} (hξ : ‖ξ‖ = 3 * dd L) :
    ‖fx κ x.1 x.2 n ξ / PC κ x.1 x.2 n ξ + (L : ℂ) ^ 2‖ ≤ 1 / (120 * dd L ^ 2) := by
  have hL : 0 < L := Fact.out
  have hd := dd_pos (L := L)
  obtain ⟨hP1, hP2⟩ := PC_sphere hx hξ
  have hPne : PC κ x.1 x.2 n ξ ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le (by positivity) hP1)
  have hLd := Ld (L := L)
  have hLξ : ‖(L : ℂ) * ξ‖ = 3 / 4 := by rw [norm_Lw, hξ, show L * (3 * dd L) = 3 * (L * dd L) by ring, hLd]; norm_num
  have hnear := freeF_near (L := L) (w := ξ) (by rw [hLξ]; norm_num)
  rw [hLξ] at hnear
  have hδ := hx.1 ξ (by rw [hξ]; linarith)
  rw [ε₀_eq] at hδ
  have hL2 := L2_eq (L := L)
  have hnum : ‖fx κ x.1 x.2 n ξ + (L : ℂ) ^ 2 * PC κ x.1 x.2 n ξ‖ ≤ 1 / 15 := by
    have e : fx κ x.1 x.2 n ξ + (L : ℂ) ^ 2 * PC κ x.1 x.2 n ξ =
        (fx κ x.1 x.2 n ξ - freeF L ξ) + (freeF L ξ + ((L : ℂ) * ξ) ^ 2) +
          (L : ℂ) ^ 2 * (PC κ x.1 x.2 n ξ - ξ ^ 2) := by ring
    rw [e]
    have h1 := norm_add₃_le (a := fx κ x.1 x.2 n ξ - freeF L ξ) (b := freeF L ξ + ((L : ℂ) * ξ) ^ 2)
      (c := (L : ℂ) ^ 2 * (PC κ x.1 x.2 n ξ - ξ ^ 2))
    have h3 : ‖(L : ℂ) ^ 2 * (PC κ x.1 x.2 n ξ - ξ ^ 2)‖ ≤ 1 / 32 := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL, hL2]
      calc 1 / (16 * dd L ^ 2) * ‖PC κ x.1 x.2 n ξ - ξ ^ 2‖ ≤ 1 / (16 * dd L ^ 2) * (dd L ^ 2 / 2) := by
            gcongr
        _ = 1 / 32 := by field_simp; ring
    norm_num at hnear
    linarith
  have e2 : fx κ x.1 x.2 n ξ / PC κ x.1 x.2 n ξ + (L : ℂ) ^ 2 =
      (fx κ x.1 x.2 n ξ + (L : ℂ) ^ 2 * PC κ x.1 x.2 n ξ) / PC κ x.1 x.2 n ξ := by
    field_simp
  rw [e2, norm_div]
  calc _ ≤ (1 / 15) / (8 * dd L ^ 2) := div_le_div₀ (by norm_num) hnum (by positivity) hP1
    _ = 1 / (120 * dd L ^ 2) := by field_simp; ring

/-- `|H_n(w) + L²| ≤ L²/2` on `|w| ≤ 17d/8` (Cauchy's formula on `|ξ| = 3d`). -/
theorem HC_bound {n : ℤ} {x : L2T L × L2T L} (hx : Good κ n x) {w : ℂ} (hw : ‖w‖ ≤ 17 * dd L / 8) :
    ‖HC κ x.1 x.2 n w + (L : ℂ) ^ 2‖ ≤ L ^ 2 / 2 := by
  have hL : 0 < L := Fact.out
  have hd := dd_pos (L := L)
  have hR : (0 : ℝ) ≤ 3 * dd L := by positivity
  have hwb : w ∈ ball (0 : ℂ) (3 * dd L) := by rw [mem_ball, dist_zero_right]; linarith
  have hne : ∀ ξ ∈ sphere (0 : ℂ) (3 * dd L), ξ - w ≠ 0 := by
    intro ξ hξ h
    rw [sub_eq_zero] at h
    rw [← h, sphere_norm hξ] at hw
    linarith
  have hPne : ∀ ξ ∈ sphere (0 : ℂ) (3 * dd L), PC κ x.1 x.2 n ξ ≠ 0 := fun ξ hξ =>
    norm_pos_iff.1 (lt_of_lt_of_le (by positivity) (PC_sphere hx (sphere_norm hξ)).1)
  have hPc : Continuous (PC κ x.1 x.2 n) := by unfold PC; fun_prop
  have hinv : ContinuousOn (fun ξ : ℂ => (ξ - w)⁻¹) (sphere 0 (3 * dd L)) :=
    (continuousOn_id.sub continuousOn_const).inv₀ hne
  have hA : CircleIntegrable (fun ξ => (ξ - w)⁻¹ • (fx κ x.1 x.2 n ξ / PC κ x.1 x.2 n ξ)) 0 (3 * dd L) :=
    ContinuousOn.circleIntegrable hR (hinv.smul ((differentiable_fx κ x.1 x.2 n).continuous.continuousOn.div
      hPc.continuousOn hPne))
  have hB : CircleIntegrable (fun ξ => (ξ - w)⁻¹ • (L : ℂ) ^ 2) 0 (3 * dd L) :=
    ContinuousOn.circleIntegrable hR (hinv.smul continuousOn_const)
  have hone : (2 * Real.pi * Complex.I)⁻¹ * ∮ ξ in C(0, 3 * dd L), (ξ - w)⁻¹ • (L : ℂ) ^ 2 = (L : ℂ) ^ 2 := by
    rw [circleIntegral.integral_smul_const, circleIntegral.integral_sub_inv_of_mem_ball hwb, smul_eq_mul,
      ← mul_assoc, inv_mul_cancel₀ two_pi_I_ne, one_mul]
  have he : HC κ x.1 x.2 n w + (L : ℂ) ^ 2 = (2 * Real.pi * Complex.I)⁻¹ * ∮ ξ in C(0, 3 * dd L),
      (ξ - w)⁻¹ • (fx κ x.1 x.2 n ξ / PC κ x.1 x.2 n ξ + (L : ℂ) ^ 2) := by
    conv_lhs => rw [← hone]
    unfold HC
    rw [← mul_add, ← circleIntegral.integral_add hA hB]
    simp only [smul_add]
  rw [he]
  have hb : ∀ ξ ∈ sphere (0 : ℂ) (3 * dd L),
      ‖(ξ - w)⁻¹ • (fx κ x.1 x.2 n ξ / PC κ x.1 x.2 n ξ + (L : ℂ) ^ 2)‖ ≤
        (8 / (7 * dd L)) * (1 / (120 * dd L ^ 2)) := by
    intro ξ hξ
    rw [norm_smul, norm_inv]
    have h1 : 7 * dd L / 8 ≤ ‖ξ - w‖ := by
      have := norm_sub_norm_le ξ w
      rw [sphere_norm hξ] at this
      linarith
    have h2 : ‖ξ - w‖⁻¹ ≤ 8 / (7 * dd L) := by
      rw [show 8 / (7 * dd L) = (7 * dd L / 8)⁻¹ by field_simp]
      exact inv_anti₀ (by positivity) h1
    exact mul_le_mul h2 (quot_sphere hx (sphere_norm hξ)) (norm_nonneg _) (by positivity)
  refine (norm_circleIntegral_le hR hb).trans ?_
  have hL2 := L2_eq (L := L)
  rw [hL2]
  have e : 3 * dd L * (8 / (7 * dd L) * (1 / (120 * dd L ^ 2))) = (1 / 35) * (1 / dd L ^ 2) := by
    field_simp; ring
  rw [e]
  have e2 : 1 / (16 * dd L ^ 2) / 2 = (1 / 32) * (1 / dd L ^ 2) := by field_simp; ring
  rw [e2]
  gcongr
  norm_num

/-! ## Holomorphy on the complex neighborhood -/

theorem mem_ball_prod {u₀ : L2T L} {ρ : ℝ} {x : L2T L × L2T L} (hx : x ∈ ball (u₀, star u₀) ρ) :
    ‖x.1 - u₀‖ < ρ ∧ ‖x.2 - star u₀‖ < ρ := by
  rw [mem_ball, Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm] at hx
  exact hx

/-- **Bounded holomorphic moments, `α_n`, `τ_n`, `H_n` on one complex neighborhood, all high labels.** -/
theorem cx_moments (κ : ℝ) (u₀ : L2T L) :
    ∃ N : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ∀ n : ℤ, (N : ℝ) < |(n : ℝ)| →
      (∀ x ∈ ball (u₀, star u₀) ρ, Good κ n x) ∧
      (∀ j : ℕ, AnalyticOnNhd ℂ (fun x : L2T L × L2T L => mom κ x.1 x.2 n j) (ball (u₀, star u₀) ρ)) ∧
      AnalyticOnNhd ℂ (fun x : L2T L × L2T L => alphaC κ x.1 x.2 n) (ball (u₀, star u₀) ρ) ∧
      AnalyticOnNhd ℂ (fun x : L2T L × L2T L => tauC κ x.1 x.2 n) (ball (u₀, star u₀) ρ) ∧
      (∀ x ∈ ball (u₀, star u₀) ρ, ‖alphaC κ x.1 x.2 n‖ ≤ dd L / 16 ∧ ‖tauC κ x.1 x.2 n‖ ≤ dd L ^ 2 / 9) ∧
      AnalyticOnNhd ℂ (fun p : (L2T L × L2T L) × ℂ => HC κ p.1.1 p.1.2 n p.2)
        (ball (u₀, star u₀) ρ ×ˢ ball (0 : ℂ) (3 * dd L)) ∧
      (∀ x ∈ ball (u₀, star u₀) ρ, ∀ w : ℂ, ‖w‖ ≤ 17 * dd L / 8 →
        ‖HC κ x.1 x.2 n w + (L : ℂ) ^ 2‖ ≤ L ^ 2 / 2) := by
  have hL : 0 < L := Fact.out
  have hd := dd_pos (L := L)
  have hR : (0 : ℝ) ≤ 3 * dd L := by positivity
  obtain ⟨N, ρ, hρ, h⟩ := cx_prep (L := L) κ u₀
  refine ⟨N, ρ, hρ, fun n hn => ?_⟩
  set B := ball ((u₀, star u₀) : L2T L × L2T L) ρ with hB
  have hgood : ∀ x ∈ B, Good κ n x := fun x hx =>
    h n hn x.1 x.2 (mem_ball_prod hx).1 (mem_ball_prod hx).2
  -- moments
  have hmom : ∀ j : ℕ, AnalyticOnNhd ℂ (fun x : L2T L × L2T L => mom κ x.1 x.2 n j) B := by
    intro j x hx
    refine analyticAt_const.mul (analyticOnNhd_circleIntegral (U := B) hR (fun w hw => ?_) (fun y hy => ?_)
      (fun y hy => ?_) x hx)
    · intro y hy
      exact analyticAt_const.mul ((analytic_dfx κ n w y (mem_univ _)).div (analytic_fx_x κ n w y (mem_univ _))
        (fx_ne_sphere (hgood y hy) hw))
    · have hdc : Continuous (deriv (fx κ y.1 y.2 n)) := by
        rw [continuous_iff_continuousAt]
        exact fun z => (((differentiable_fx κ y.1 y.2 n).analyticAt z).deriv).continuousAt
      exact (continuousOn_id.pow j).mul (hdc.continuousOn.div
        (differentiable_fx κ y.1 y.2 n).continuous.continuousOn fun w hw => fx_ne_sphere (hgood y hy) hw)
    · obtain ⟨hr, hsub⟩ := ball_in hy
      refine ⟨_, hr, (3 * dd L) ^ j * ((6 / 5 / dd L) / (9 / 65536)), hsub, fun z hz w hw => ?_⟩
      have hzg := hgood z (hsub hz)
      have hwn := sphere_norm hw
      rw [norm_mul, norm_div, norm_pow, hwn]
      have hlow := hzg.2 w (by rw [hwn]; linarith) (by rw [hwn]; linarith)
      have hup := dfx_upper hzg (le_of_eq hwn)
      gcongr
  have halpha : AnalyticOnNhd ℂ (fun x : L2T L × L2T L => alphaC κ x.1 x.2 n) B :=
    fun x hx => (hmom 1 x hx).div_const
  have hc : AnalyticOnNhd ℂ (fun x : L2T L × L2T L => cC κ x.1 x.2 n) B :=
    fun x hx => (((hmom 1 x hx).pow 2).sub (hmom 2 x hx)).div_const
  have htau : AnalyticOnNhd ℂ (fun x : L2T L × L2T L => tauC κ x.1 x.2 n) B :=
    fun x hx => ((halpha x hx).pow 2).sub (hc x hx)
  refine ⟨hgood, hmom, halpha, htau, fun x hx => alpha_tau_bound (hgood x hx), ?_,
    fun x hx w hw => HC_bound (hgood x hx) hw⟩
  -- the Cauchy quotient
  have hU : ∀ p ∈ B ×ˢ ball (0 : ℂ) (3 * dd L), p.1 ∈ B ∧ ‖p.2‖ < 3 * dd L := by
    intro p hp
    obtain ⟨h1, h2⟩ := mem_prod.1 hp
    exact ⟨h1, by rwa [mem_ball, dist_zero_right] at h2⟩
  intro p hp
  refine analyticAt_const.mul (analyticOnNhd_circleIntegral (U := B ×ˢ ball (0 : ℂ) (3 * dd L)) hR
    (fun ξ hξ => ?_) (fun q hq => ?_) (fun q hq => ?_) p hp)
  · intro q hq
    obtain ⟨hq1, hq2⟩ := hU q hq
    have hξw : ξ - q.2 ≠ 0 := by
      intro h0; rw [sub_eq_zero] at h0; rw [← h0, sphere_norm hξ] at hq2; linarith
    have hPC : AnalyticAt ℂ (fun q : (L2T L × L2T L) × ℂ => PC κ q.1.1 q.1.2 n ξ) q :=
      ((analyticAt_const.sub ((halpha q.1 hq1).comp analyticAt_fst)).pow 2).sub ((htau q.1 hq1).comp analyticAt_fst)
    have hPne : PC κ q.1.1 q.1.2 n ξ ≠ 0 :=
      norm_pos_iff.1 (lt_of_lt_of_le (by positivity) (PC_sphere (hgood q.1 hq1) (sphere_norm hξ)).1)
    exact ((analyticAt_const.sub analyticAt_snd).inv hξw).smul
      (((analytic_fx_x κ n ξ q.1 (mem_univ _)).comp analyticAt_fst).div hPC hPne)
  · obtain ⟨hq1, hq2⟩ := hU q hq
    have hne : ∀ ξ ∈ sphere (0 : ℂ) (3 * dd L), ξ - q.2 ≠ 0 := by
      intro ξ hξ h0; rw [sub_eq_zero] at h0; rw [← h0, sphere_norm hξ] at hq2; linarith
    have hPne : ∀ ξ ∈ sphere (0 : ℂ) (3 * dd L), PC κ q.1.1 q.1.2 n ξ ≠ 0 := fun ξ hξ =>
      norm_pos_iff.1 (lt_of_lt_of_le (by positivity) (PC_sphere (hgood q.1 hq1) (sphere_norm hξ)).1)
    have hPc : Continuous (PC κ q.1.1 q.1.2 n) := by unfold PC; fun_prop
    exact ((continuousOn_id.sub continuousOn_const).inv₀ hne).smul
      ((differentiable_fx κ q.1.1 q.1.2 n).continuous.continuousOn.div hPc.continuousOn hPne)
  · obtain ⟨hq1, hq2⟩ := hU q hq
    obtain ⟨hr1, hsub1⟩ := ball_in hq1
    set s := min (ρ - dist q.1 (u₀, star u₀)) ((3 * dd L - ‖q.2‖) / 2) with hs
    have hs0 : 0 < s := lt_min hr1 (by linarith)
    refine ⟨s, hs0, (2 / (3 * dd L - ‖q.2‖)) * ((6 / 5) / (8 * dd L ^ 2)), ?_, fun z hz ξ hξ => ?_⟩
    · intro z hz
      rw [mem_ball, Prod.dist_eq, max_lt_iff] at hz
      refine mem_prod.2 ⟨hsub1 (mem_ball.2 (lt_of_lt_of_le hz.1 (min_le_left _ _))), ?_⟩
      rw [mem_ball, dist_zero_right]
      have h1 := lt_of_lt_of_le hz.2 (min_le_right _ _)
      rw [dist_eq_norm] at h1
      have := norm_le_insert' z.2 q.2
      have := norm_sub_norm_le z.2 q.2
      linarith
    · rw [mem_ball, Prod.dist_eq, max_lt_iff] at hz
      have hz1 : z.1 ∈ B := hsub1 (mem_ball.2 (lt_of_lt_of_le hz.1 (min_le_left _ _)))
      have hz2 := lt_of_lt_of_le hz.2 (min_le_right _ _)
      rw [dist_eq_norm] at hz2
      have hzg := hgood z.1 hz1
      have hξn := sphere_norm hξ
      have hdist : (3 * dd L - ‖q.2‖) / 2 ≤ ‖ξ - z.2‖ := by
        have h1 := norm_sub_norm_le ξ z.2
        have h2 := norm_sub_norm_le z.2 q.2
        linarith
      have hpos : 0 < (3 * dd L - ‖q.2‖) / 2 := by linarith
      rw [norm_smul, norm_inv, norm_div]
      have h1 : ‖ξ - z.2‖⁻¹ ≤ 2 / (3 * dd L - ‖q.2‖) := by
        rw [show 2 / (3 * dd L - ‖q.2‖) = ((3 * dd L - ‖q.2‖) / 2)⁻¹ by field_simp]
        exact inv_anti₀ hpos hdist
      have h2 : ‖fx κ z.1.1 z.1.2 n ξ‖ / ‖PC κ z.1.1 z.1.2 n ξ‖ ≤ (6 / 5) / (8 * dd L ^ 2) :=
        div_le_div₀ (by norm_num) (fx_upper hzg (by rw [hξn]; linarith)) (by positivity)
          (PC_sphere hzg hξn).1
      exact mul_le_mul h1 h2 (by positivity) (by positivity)

end QuantumNLS.RB01CxMoments

#print axioms QuantumNLS.RB01CxMoments.logderiv_diff
#print axioms QuantumNLS.RB01CxMoments.analytic_fx_joint
#print axioms QuantumNLS.RB01CxMoments.analytic_dfx
#print axioms QuantumNLS.RB01CxMoments.mom_free
#print axioms QuantumNLS.RB01CxMoments.mom_bound
#print axioms QuantumNLS.RB01CxMoments.HC_bound
#print axioms QuantumNLS.RB01CxMoments.cx_moments
