import Mathlib
import QuantumNLS.RB01Density
import QuantumNLS.RB01CxMoments
import QuantumNLS.ComplexifiedConjugation

/-! R-EC25334D (`thm:global-B01-actions`), stage RB01-21: the density factor `D_n` and `r_n` as bounded holomorphic
families on one complex neighborhood, for all high labels; `r` as one bounded holomorphic `ℓ∞`-valued map; real
analyticity of `u ↦ r(u)` on the real slice (source `collective_actions.tex:405-464`: "All assertions here are
uniform bounded holomorphic-family assertions, with values in `ℓ∞`"; eq. `GB01-D`, eq. `GB01-r`; theorem clause
"`r : U → ℓ∞({|n| > N})` real analytic ... bounded holomorphic extensions on a complexification").

Objects: the frozen `RB01Density.DC` (eq. `GB01-D` with `RB01Moments.HC`, `PC`), `RB01Density.Ev`, `rC`
(recorded route choice: even part on `|ξ| = 2d`), `rn` (real slice).
* `DC_analytic`: `(x, w) ↦ DC κ x n w` is complex analytic on `B × {|w| < 17d/8}` (`−HC ∈ slitPlane`, principal
  square root; `|𝒫·HC/4| ≤ 15/128`, `χ` analytic on the unit disk); `DC_bound`: one bound, independent of `n`;
* `EvF_analytic`, `EvF_bound`: `(x, σ) ↦ Ev(DC(alphaC + ·))(σ)` on `B × {|σ| < 2d²}` (`RB01ParamInt`);
* **`cx_density`**: for every `u₀` there are `N`, `ρ > 0`, `M` such that every `x ↦ rC κ x n`, `|n| > N`, is complex
  analytic on `B((u₀, ū₀), ρ)` and bounded by `M` there;
* **`r_linf`** (with `κ > 0`): there are `N`, `ρ > 0`, `M ≥ 0` and `G : L²×L² → ℓ∞(ℤ)`, complex analytic on
  `B((u₀, ū₀), ρ)`, `‖G‖ ≤ M` there, `G(x)_n = rC κ x n` for `|n| > N` and `0` otherwise; `u ↦ G(u, ū)` is real
  analytic at every `‖u − u₀‖ < ρ`, with `G(u, ū)_n = r_n(u)` (`RB01Density.rn`), `Im r_n = 0`,
  `1/2 < Re r_n < 3/2` for `|n| > N` (RB01Density (e), (g)). -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Filter Topology Set Metric

namespace QuantumNLS.RB01CxDensity

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.RB01RootPrep (dd ε₀ dd_pos)
open QuantumNLS.RB01Moments (alphaC tauC PC HC)
open QuantumNLS.RB01Density (chi differentiableOn_chi Dgen DC Ev rgen rC rn DensityFacts density)
open QuantumNLS.RB01CxMoments (Good cx_moments ball_in Ld L2_eq)
open QuantumNLS.RB01ParamInt (analyticOnNhd_circleIntegral analyticOnNhd_integral norm_circleIntegral_le)
open QuantumNLS.RB01LinfLift (Linf linf_lift)

/-! ## `χ` -/

theorem chi_analyticAt {s : ℂ} (hs : ‖s‖ < 1) : AnalyticAt ℂ chi s :=
  differentiableOn_chi.analyticAt (isOpen_ball.mem_nhds (by rwa [mem_ball, dist_zero_right]))

theorem chi_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, ‖s‖ ≤ 1 / 2 → ‖chi s‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) (1 / 2)).exists_bound_of_continuousOn
    (differentiableOn_chi.continuousOn.mono (closedBall_subset_ball (by norm_num)))
  exact ⟨max C 0, le_max_right _ _, fun s hs =>
    (hC s (by rwa [mem_closedBall, dist_zero_right])).trans (le_max_left _ _)⟩

variable {L κ : ℝ} [Fact (0 < L)]

/-- The conclusions of `RB01CxMoments.cx_moments` on a set `B` of complexified fields, one label. -/
def MomFacts (κ : ℝ) (n : ℤ) (B : Set (L2T L × L2T L)) : Prop :=
  (∀ x ∈ B, Good κ n x) ∧
  AnalyticOnNhd ℂ (fun x : L2T L × L2T L => alphaC κ x.1 x.2 n) B ∧
  AnalyticOnNhd ℂ (fun x : L2T L × L2T L => tauC κ x.1 x.2 n) B ∧
  (∀ x ∈ B, ‖alphaC κ x.1 x.2 n‖ ≤ dd L / 16 ∧ ‖tauC κ x.1 x.2 n‖ ≤ dd L ^ 2 / 9) ∧
  AnalyticOnNhd ℂ (fun p : (L2T L × L2T L) × ℂ => HC κ p.1.1 p.1.2 n p.2) (B ×ˢ ball (0 : ℂ) (3 * dd L)) ∧
  (∀ x ∈ B, ∀ w : ℂ, ‖w‖ ≤ 17 * dd L / 8 → ‖HC κ x.1 x.2 n w + (L : ℂ) ^ 2‖ ≤ L ^ 2 / 2)

section Facts

variable {n : ℤ} {B : Set (L2T L × L2T L)}

theorem PC_bound (h : MomFacts κ n B) {x : L2T L × L2T L} (hx : x ∈ B) {w : ℂ} (hw : ‖w‖ ≤ 17 * dd L / 8) :
    ‖PC κ x.1 x.2 n w‖ ≤ 5 * dd L ^ 2 := by
  have hd := dd_pos (L := L)
  obtain ⟨ha, ht⟩ := h.2.2.2.1 x hx
  have hP : PC κ x.1 x.2 n w = (w - alphaC κ x.1 x.2 n) ^ 2 - tauC κ x.1 x.2 n := rfl
  rw [hP]
  have h1 := norm_sub_le ((w - alphaC κ x.1 x.2 n) ^ 2) (tauC κ x.1 x.2 n)
  have h2 := norm_sub_le w (alphaC κ x.1 x.2 n)
  rw [norm_pow] at h1
  have h3 : ‖w - alphaC κ x.1 x.2 n‖ ≤ 35 * dd L / 16 := by linarith
  have h4 : ‖w - alphaC κ x.1 x.2 n‖ ^ 2 ≤ (35 * dd L / 16) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
  nlinarith

theorem HC_norm (h : MomFacts κ n B) {x : L2T L × L2T L} (hx : x ∈ B) {w : ℂ} (hw : ‖w‖ ≤ 17 * dd L / 8) :
    ‖HC κ x.1 x.2 n w‖ ≤ 3 * L ^ 2 / 2 := by
  have hb := h.2.2.2.2.2 x hx w hw
  have h1 := norm_sub_le (HC κ x.1 x.2 n w + (L : ℂ) ^ 2) ((L : ℂ) ^ 2)
  rw [add_sub_cancel_right, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h1
  linarith

theorem arg_bound (h : MomFacts κ n B) {x : L2T L × L2T L} (hx : x ∈ B) {w : ℂ} (hw : ‖w‖ ≤ 17 * dd L / 8) :
    ‖PC κ x.1 x.2 n w * HC κ x.1 x.2 n w / 4‖ ≤ 15 / 128 := by
  have hd := dd_pos (L := L)
  have hL : 0 < L := Fact.out
  have h1 := PC_bound h hx hw
  have h2 := HC_norm h hx hw
  rw [norm_div, norm_mul, show ‖(4 : ℂ)‖ = 4 by norm_num]
  have hLd : (L * dd L) ^ 2 = 1 / 16 := by rw [Ld]; norm_num
  have h3 : ‖PC κ x.1 x.2 n w‖ * ‖HC κ x.1 x.2 n w‖ ≤ 5 * dd L ^ 2 * (3 * L ^ 2 / 2) :=
    mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
  have h4 : 5 * dd L ^ 2 * (3 * L ^ 2 / 2) = 15 / 32 := by
    rw [show 5 * dd L ^ 2 * (3 * L ^ 2 / 2) = 15 / 2 * (L * dd L) ^ 2 by ring, hLd]; norm_num
  rw [h4] at h3
  linarith

theorem slit (h : MomFacts κ n B) {x : L2T L × L2T L} (hx : x ∈ B) {w : ℂ} (hw : ‖w‖ ≤ 17 * dd L / 8) :
    -HC κ x.1 x.2 n w ∈ Complex.slitPlane := by
  have hL : 0 < L := Fact.out
  have hb := h.2.2.2.2.2 x hx w hw
  have hre := Complex.abs_re_le_norm (HC κ x.1 x.2 n w + (L : ℂ) ^ 2)
  have e : (HC κ x.1 x.2 n w + (L : ℂ) ^ 2).re = (HC κ x.1 x.2 n w).re + L ^ 2 := by
    rw [Complex.add_re, ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [e] at hre
  refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
  rw [Complex.neg_re]
  have := (abs_le.1 (hre.trans hb)).2
  nlinarith [sq_nonneg L, mul_pos hL hL]

/-- `D_n` is jointly holomorphic in the complexified field and `w`. -/
theorem DC_analytic (h : MomFacts κ n B) :
    AnalyticOnNhd ℂ (fun p : (L2T L × L2T L) × ℂ => DC κ p.1.1 p.1.2 n p.2)
      (B ×ˢ ball (0 : ℂ) (17 * dd L / 8)) := by
  intro p hp
  obtain ⟨hp1, hp2⟩ := mem_prod.1 hp
  rw [mem_ball, dist_zero_right] at hp2
  have hd := dd_pos (L := L)
  have hp3 : p ∈ B ×ˢ ball (0 : ℂ) (3 * dd L) :=
    mem_prod.2 ⟨hp1, by rw [mem_ball, dist_zero_right]; linarith⟩
  have hH := h.2.2.2.2.1 p hp3
  have hP : AnalyticAt ℂ (fun p : (L2T L × L2T L) × ℂ => PC κ p.1.1 p.1.2 n p.2) p :=
    ((analyticAt_snd.sub ((h.2.1 p.1 hp1).comp analyticAt_fst)).pow 2).sub
      ((h.2.2.1 p.1 hp1).comp analyticAt_fst)
  have hs : ‖PC κ p.1.1 p.1.2 n p.2 * HC κ p.1.1 p.1.2 n p.2 / 4‖ < 1 :=
    lt_of_le_of_lt (arg_bound h hp1 hp2.le) (by norm_num)
  have h1 : AnalyticAt ℂ (fun p : (L2T L × L2T L) × ℂ => (-HC κ p.1.1 p.1.2 n p.2) ^ (1 / 2 : ℂ)) p :=
    hH.neg.cpow analyticAt_const (slit h hp1 hp2.le)
  have h2 : AnalyticAt ℂ
      (fun p : (L2T L × L2T L) × ℂ => chi (PC κ p.1.1 p.1.2 n p.2 * HC κ p.1.1 p.1.2 n p.2 / 4)) p :=
    (chi_analyticAt hs).comp (f := fun p : (L2T L × L2T L) × ℂ =>
      PC κ p.1.1 p.1.2 n p.2 * HC κ p.1.1 p.1.2 n p.2 / 4) ((hP.mul hH).div_const)
  exact (h1.div_const).mul h2

theorem DC_bound (h : MomFacts κ n B) {Cχ : ℝ} (hχ : ∀ s : ℂ, ‖s‖ ≤ 1 / 2 → ‖chi s‖ ≤ Cχ)
    {x : L2T L × L2T L} (hx : x ∈ B) {w : ℂ} (hw : ‖w‖ ≤ 17 * dd L / 8) :
    ‖DC κ x.1 x.2 n w‖ ≤ (3 * L ^ 2 / 2) ^ (1 / 2 : ℝ) / 2 * Cχ := by
  have hc := hχ _ ((arg_bound h hx hw).trans (by norm_num))
  have hC0 : 0 ≤ Cχ := (norm_nonneg _).trans hc
  change ‖(-HC κ x.1 x.2 n w) ^ (1 / 2 : ℂ) / 2 * chi (PC κ x.1 x.2 n w * HC κ x.1 x.2 n w / 4)‖ ≤ _
  have e : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [norm_mul, norm_div, e, Complex.norm_cpow_real, norm_neg, Complex.norm_two]
  have h1 : ‖HC κ x.1 x.2 n w‖ ^ (1 / 2 : ℝ) ≤ (3 * L ^ 2 / 2) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (norm_nonneg _) (HC_norm h hx hw) (by norm_num)
  have h2 : 0 ≤ ‖HC κ x.1 x.2 n w‖ ^ (1 / 2 : ℝ) := by positivity
  have h3 : 0 ≤ (3 * L ^ 2 / 2) ^ (1 / 2 : ℝ) := by positivity
  calc ‖HC κ x.1 x.2 n w‖ ^ (1 / 2 : ℝ) / 2 * ‖chi (PC κ x.1 x.2 n w * HC κ x.1 x.2 n w / 4)‖
      ≤ (3 * L ^ 2 / 2) ^ (1 / 2 : ℝ) / 2 * Cχ := by gcongr

/-- `Ev(DC(alphaC + ·))(σ)` as a function of the complexified field and `σ`. -/
def EvF (κ : ℝ) (n : ℤ) (p : (L2T L × L2T L) × ℂ) : ℂ :=
  Ev (fun ξ => DC κ p.1.1 p.1.2 n (alphaC κ p.1.1 p.1.2 n + ξ)) (2 * dd L) p.2

theorem shift_mem (h : MomFacts κ n B) {x : L2T L × L2T L} (hx : x ∈ B) {ξ : ℂ} (hξ : ‖ξ‖ = 2 * dd L) :
    ‖alphaC κ x.1 x.2 n + ξ‖ < 17 * dd L / 8 := by
  have hd := dd_pos (L := L)
  have h1 := (h.2.2.2.1 x hx).1
  have h2 := norm_add_le (alphaC κ x.1 x.2 n) ξ
  linarith

theorem kernel_bound {ξ σ : ℂ} (hξ : ‖ξ‖ = 2 * dd L) (hσ : ‖σ‖ < 2 * dd L ^ 2) :
    ξ ^ 2 - σ ≠ 0 ∧ ‖ξ / (ξ ^ 2 - σ)‖ ≤ 1 / dd L := by
  have hd := dd_pos (L := L)
  have h1 : 2 * dd L ^ 2 ≤ ‖ξ ^ 2 - σ‖ := by
    have := norm_sub_norm_le (ξ ^ 2) σ
    rw [norm_pow, hξ] at this
    nlinarith
  have hne : ξ ^ 2 - σ ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le (by positivity) h1)
  refine ⟨hne, ?_⟩
  rw [norm_div, hξ]
  calc 2 * dd L / ‖ξ ^ 2 - σ‖ ≤ 2 * dd L / (2 * dd L ^ 2) := div_le_div_of_nonneg_left (by positivity)
        (by positivity) h1
    _ = 1 / dd L := by field_simp

theorem EvF_kernel (h : MomFacts κ n B) {Cχ : ℝ} (hχ : ∀ s : ℂ, ‖s‖ ≤ 1 / 2 → ‖chi s‖ ≤ Cχ)
    {q : (L2T L × L2T L) × ℂ} (hq1 : q.1 ∈ B) (hq2 : ‖q.2‖ < 2 * dd L ^ 2) {ξ : ℂ} (hξ : ‖ξ‖ = 2 * dd L) :
    ‖(ξ / (ξ ^ 2 - q.2)) * DC κ q.1.1 q.1.2 n (alphaC κ q.1.1 q.1.2 n + ξ)‖ ≤
      1 / dd L * ((3 * L ^ 2 / 2) ^ (1 / 2 : ℝ) / 2 * Cχ) := by
  have hd := dd_pos (L := L)
  rw [norm_mul]
  exact mul_le_mul (kernel_bound hξ hq2).2 (DC_bound h hχ hq1 (shift_mem h hq1 hξ).le) (norm_nonneg _)
    (by positivity)

theorem EvF_bound (h : MomFacts κ n B) {Cχ : ℝ} (hχ : ∀ s : ℂ, ‖s‖ ≤ 1 / 2 → ‖chi s‖ ≤ Cχ)
    {q : (L2T L × L2T L) × ℂ} (hq1 : q.1 ∈ B) (hq2 : ‖q.2‖ < 2 * dd L ^ 2) :
    ‖EvF κ n q‖ ≤ 2 * ((3 * L ^ 2 / 2) ^ (1 / 2 : ℝ) / 2 * Cχ) := by
  have hd := dd_pos (L := L)
  change ‖(2 * Real.pi * Complex.I)⁻¹ * ∮ ξ in C(0, 2 * dd L),
    (ξ / (ξ ^ 2 - q.2)) * DC κ q.1.1 q.1.2 n (alphaC κ q.1.1 q.1.2 n + ξ)‖ ≤ _
  refine (norm_circleIntegral_le (by positivity) fun ξ hξ =>
    EvF_kernel h hχ hq1 hq2 (by rwa [mem_sphere, dist_zero_right] at hξ)).trans (le_of_eq ?_)
  rw [show 2 * dd L * (1 / dd L * ((3 * L ^ 2 / 2) ^ (1 / 2 : ℝ) / 2 * Cχ)) =
      2 * ((3 * L ^ 2 / 2) ^ (1 / 2 : ℝ) / 2 * Cχ) * (dd L / dd L) by ring, div_self hd.ne', mul_one]

theorem EvF_analytic (hB : IsOpen B) (h : MomFacts κ n B) :
    AnalyticOnNhd ℂ (EvF κ n) (B ×ˢ ball (0 : ℂ) (2 * dd L ^ 2)) := by
  have hd := dd_pos (L := L)
  have hR : (0 : ℝ) ≤ 2 * dd L := by positivity
  have hDC := DC_analytic h
  have hU : ∀ q ∈ B ×ˢ ball (0 : ℂ) (2 * dd L ^ 2), q.1 ∈ B ∧ ‖q.2‖ < 2 * dd L ^ 2 := by
    intro q hq
    obtain ⟨h1, h2⟩ := mem_prod.1 hq
    exact ⟨h1, mem_ball_zero_iff.1 h2⟩
  have hmem : ∀ q ∈ B ×ˢ ball (0 : ℂ) (2 * dd L ^ 2), ∀ ξ ∈ sphere (0 : ℂ) (2 * dd L),
      (q.1, alphaC κ q.1.1 q.1.2 n + ξ) ∈ B ×ˢ ball (0 : ℂ) (17 * dd L / 8) := by
    intro q hq ξ hξ
    refine mem_prod.2 ⟨(hU q hq).1, ?_⟩
    rw [mem_ball, dist_zero_right]
    exact shift_mem h (hU q hq).1 (by rwa [mem_sphere, dist_zero_right] at hξ)
  intro p hp
  change AnalyticAt ℂ (fun q : (L2T L × L2T L) × ℂ => (2 * Real.pi * Complex.I)⁻¹ *
    ∮ ξ in C(0, 2 * dd L), (ξ / (ξ ^ 2 - q.2)) * DC κ q.1.1 q.1.2 n (alphaC κ q.1.1 q.1.2 n + ξ)) p
  refine analyticAt_const.mul (analyticOnNhd_circleIntegral hR (fun ξ hξ => ?_) (fun q hq => ?_)
    (fun q hq => ?_) p hp)
  · intro q hq
    have hξn : ‖ξ‖ = 2 * dd L := by rwa [mem_sphere, dist_zero_right] at hξ
    obtain ⟨hne, -⟩ := kernel_bound hξn (hU q hq).2
    have hmap : AnalyticAt ℂ (fun q : (L2T L × L2T L) × ℂ => (q.1, alphaC κ q.1.1 q.1.2 n + ξ)) q :=
      analyticAt_fst.prod (((h.2.1 q.1 (hU q hq).1).comp analyticAt_fst).add analyticAt_const)
    have hc := AnalyticAt.comp (g := fun p : (L2T L × L2T L) × ℂ => DC κ p.1.1 p.1.2 n p.2)
      (f := fun q : (L2T L × L2T L) × ℂ => (q.1, alphaC κ q.1.1 q.1.2 n + ξ)) (hDC _ (hmem q hq ξ hξ)) hmap
    exact (analyticAt_const.div (analyticAt_const.sub analyticAt_snd) hne).mul hc
  · have hk : ContinuousOn (fun ξ : ℂ => ξ / (ξ ^ 2 - q.2)) (sphere 0 (2 * dd L)) :=
      continuousOn_id.div ((continuousOn_id.pow 2).sub continuousOn_const) fun ξ hξ =>
        (kernel_bound (by rwa [mem_sphere, dist_zero_right] at hξ) (hU q hq).2).1
    refine hk.mul fun ξ hξ => ?_
    have hc := (hDC _ (hmem q hq ξ hξ)).continuousAt
    exact (hc.comp (f := fun ξ : ℂ => (q.1, alphaC κ q.1.1 q.1.2 n + ξ))
      (continuousAt_const.prodMk (continuousAt_const.add continuousAt_id))).continuousWithinAt
  · obtain ⟨Cχ, -, hχ⟩ := chi_bound
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 (hB.prod isOpen_ball) q hq
    refine ⟨r, hr, 1 / dd L * ((3 * L ^ 2 / 2) ^ (1 / 2 : ℝ) / 2 * Cχ), hsub, fun z hz ξ hξ => ?_⟩
    have hz' := hU z (hsub hz)
    exact EvF_kernel h hχ hz'.1 hz'.2 (by rwa [mem_sphere, dist_zero_right] at hξ)

theorem rC_eq (x : L2T L × L2T L) : rC κ x.1 x.2 n = 4 / (Real.pi * L) * ∫ s in (-1 : ℝ)..1,
    ((√(1 - s ^ 2) : ℝ) : ℂ) * EvF κ n (x, tauC κ x.1 x.2 n * (s : ℂ) ^ 2) := rfl

theorem sigma_mem (h : MomFacts κ n B) {x : L2T L × L2T L} (hx : x ∈ B) {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    (x, tauC κ x.1 x.2 n * (s : ℂ) ^ 2) ∈ B ×ˢ ball (0 : ℂ) (2 * dd L ^ 2) := by
  have hd := dd_pos (L := L)
  refine mem_prod.2 ⟨hx, ?_⟩
  rw [mem_ball, dist_zero_right, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have h1 := (h.2.2.2.1 x hx).2
  have h2 : |s| ^ 2 ≤ 1 := by rw [sq_abs]; nlinarith [hs.1, hs.2]
  calc ‖tauC κ x.1 x.2 n‖ * |s| ^ 2 ≤ dd L ^ 2 / 9 * 1 :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ < 2 * dd L ^ 2 := by nlinarith

theorem sqrt_norm_le {s : ℝ} : ‖((√(1 - s ^ 2) : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_one.2 (by nlinarith [sq_nonneg s])

/-- **`r_n` is holomorphic** on the complex neighborhood. -/
theorem rC_analytic (hB : IsOpen B) (h : MomFacts κ n B) :
    AnalyticOnNhd ℂ (fun x : L2T L × L2T L => rC κ x.1 x.2 n) B := by
  have hd := dd_pos (L := L)
  obtain ⟨Cχ, -, hχ⟩ := chi_bound
  have hEv := EvF_analytic hB h
  have heq : (fun x : L2T L × L2T L => rC κ x.1 x.2 n) = fun x => 4 / (Real.pi * L) * ∫ s in (-1 : ℝ)..1,
      ((√(1 - s ^ 2) : ℝ) : ℂ) * EvF κ n (x, tauC κ x.1 x.2 n * (s : ℂ) ^ 2) := rfl
  rw [heq]
  intro x hx
  refine analyticAt_const.mul (analyticOnNhd_integral (by norm_num) (fun s hs => ?_) (fun y hy => ?_)
    (fun y hy => ?_) x hx)
  · intro y hy
    have hmap : AnalyticAt ℂ (fun y : L2T L × L2T L => (y, tauC κ y.1 y.2 n * (s : ℂ) ^ 2)) y :=
      analyticAt_id.prod ((h.2.2.1 y hy).mul analyticAt_const)
    exact analyticAt_const.mul (AnalyticAt.comp (g := EvF κ n)
      (f := fun y : L2T L × L2T L => (y, tauC κ y.1 y.2 n * (s : ℂ) ^ 2)) (hEv _ (sigma_mem h hy hs)) hmap)
  · have hc : Continuous fun s : ℝ => ((√(1 - s ^ 2) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2)))
    refine hc.continuousOn.mul fun s hs => ?_
    have hm : ContinuousAt (fun s : ℝ => (y, tauC κ y.1 y.2 n * (s : ℂ) ^ 2)) s :=
      continuousAt_const.prodMk (continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.pow 2))
    exact ((hEv _ (sigma_mem h hy hs)).continuousAt.comp
      (f := fun s : ℝ => (y, tauC κ y.1 y.2 n * (s : ℂ) ^ 2)) hm).continuousWithinAt
  · obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 hB y hy
    refine ⟨r, hr, 2 * ((3 * L ^ 2 / 2) ^ (1 / 2 : ℝ) / 2 * Cχ), hsub, fun z hz s hs => ?_⟩
    have hm := mem_prod.1 (sigma_mem h (hsub hz) hs)
    rw [norm_mul]
    calc _ ≤ 1 * (2 * ((3 * L ^ 2 / 2) ^ (1 / 2 : ℝ) / 2 * Cχ)) :=
          mul_le_mul sqrt_norm_le (EvF_bound h hχ hm.1 (mem_ball_zero_iff.1 hm.2)) (norm_nonneg _) zero_le_one
      _ = _ := one_mul _

theorem rC_bound (h : MomFacts κ n B) {Cχ : ℝ} (hχ : ∀ s : ℂ, ‖s‖ ≤ 1 / 2 → ‖chi s‖ ≤ Cχ)
    {x : L2T L × L2T L} (hx : x ∈ B) :
    ‖rC κ x.1 x.2 n‖ ≤ 4 / (Real.pi * L) * (2 * (2 * ((3 * L ^ 2 / 2) ^ (1 / 2 : ℝ) / 2 * Cχ))) := by
  have hL : 0 < L := Fact.out
  rw [rC_eq, norm_mul]
  have hn : ‖(4 / (Real.pi * L) : ℂ)‖ = 4 / (Real.pi * L) := by
    rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, abs_of_pos hL]
    norm_num
  rw [hn]
  gcongr
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := (-1 : ℝ)) (b := 1)
    (C := 2 * ((3 * L ^ 2 / 2) ^ (1 / 2 : ℝ) / 2 * Cχ))
    (f := fun s : ℝ => ((√(1 - s ^ 2) : ℝ) : ℂ) * EvF κ n (x, tauC κ x.1 x.2 n * (s : ℂ) ^ 2))
    (fun s hs => by
      have hs' : s ∈ Icc (-1 : ℝ) 1 := by
        rw [uIoc_of_le (by norm_num)] at hs
        exact ⟨hs.1.le, hs.2⟩
      have hm := mem_prod.1 (sigma_mem h hx hs')
      rw [norm_mul]
      calc _ ≤ 1 * (2 * ((3 * L ^ 2 / 2) ^ (1 / 2 : ℝ) / 2 * Cχ)) :=
            mul_le_mul sqrt_norm_le (EvF_bound h hχ hm.1 (mem_ball_zero_iff.1 hm.2)) (norm_nonneg _)
              zero_le_one
        _ = _ := one_mul _)
  rw [show |(1 : ℝ) - -1| = 2 by norm_num] at hi
  linarith

end Facts

/-! ## The complex neighborhood, all high labels -/

theorem momFacts_of (κ : ℝ) (u₀ : L2T L) :
    ∃ N : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ∀ n : ℤ, (N : ℝ) < |(n : ℝ)| →
      MomFacts κ n (ball ((u₀, star u₀) : L2T L × L2T L) ρ) := by
  obtain ⟨N, ρ, hρ, h⟩ := cx_moments (L := L) κ u₀
  refine ⟨N, ρ, hρ, fun n hn => ?_⟩
  obtain ⟨a, -, b, c, d, e, f⟩ := h n hn
  exact ⟨a, b, c, d, e, f⟩

/-- **`r_n` is a bounded holomorphic family** on one complex neighborhood of `(u₀, ū₀)`, all high labels. -/
theorem cx_density (κ : ℝ) (u₀ : L2T L) :
    ∃ N : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℤ, (N : ℝ) < |(n : ℝ)| →
      AnalyticOnNhd ℂ (fun x : L2T L × L2T L => rC κ x.1 x.2 n) (ball (u₀, star u₀) ρ) ∧
      ∀ x ∈ ball ((u₀, star u₀) : L2T L × L2T L) ρ, ‖rC κ x.1 x.2 n‖ ≤ M := by
  have hL : 0 < L := Fact.out
  obtain ⟨N, ρ, hρ, h⟩ := momFacts_of (L := L) κ u₀
  obtain ⟨Cχ, hC0, hχ⟩ := chi_bound
  have hM : 0 ≤ 4 / (Real.pi * L) * (2 * (2 * ((3 * L ^ 2 / 2) ^ (1 / 2 : ℝ) / 2 * Cχ))) := by
    have := Real.pi_pos
    positivity
  exact ⟨N, ρ, hρ, _, hM, fun n hn =>
    ⟨rC_analytic isOpen_ball (h n hn), fun x hx => rC_bound (h n hn) hχ hx⟩⟩

/-! ## The real slice -/

/-- `u ↦ (u, ū)` as a bounded real-linear map. -/
def sliceL : L2T L →L[ℝ] L2T L × L2T L :=
  LinearMap.mkContinuous
    { toFun := fun u => (u, star u)
      map_add' := fun u v => by
        simp only [ComplexifiedConjugation.star_add', Prod.mk_add_mk]
      map_smul' := fun c u => by
        simp only [RingHom.id_apply, Prod.smul_mk]
        congr 1
        rw [← algebraMap_smul ℂ c u, ComplexifiedConjugation.star_smul', ← algebraMap_smul ℂ c (star u)]
        congr 1
        simp }
    1 (fun u => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul, Prod.norm_def, ComplexifiedConjugation.norm_star',
        max_self, le_refl])

theorem sliceL_apply (u : L2T L) : sliceL u = (u, star u) := rfl

theorem star_sub_norm (u u₀ : L2T L) : ‖star u - star u₀‖ = ‖u - u₀‖ := by
  have h : star u = star (u - u₀) + star u₀ := by rw [← ComplexifiedConjugation.star_add', sub_add_cancel]
  rw [h, add_sub_cancel_right, ComplexifiedConjugation.norm_star']

/-- **`r` as one bounded holomorphic `ℓ∞(ℤ)`-valued map, real analytic on the real slice.** -/
theorem r_linf (hκ : 0 < κ) (u₀ : L2T L) :
    ∃ N : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ∃ M : ℝ, 0 ≤ M ∧ ∃ G : L2T L × L2T L → Linf ℤ,
      AnalyticOnNhd ℂ G (ball (u₀, star u₀) ρ) ∧
      (∀ x ∈ ball ((u₀, star u₀) : L2T L × L2T L) ρ, ‖G x‖ ≤ M) ∧
      (∀ x ∈ ball ((u₀, star u₀) : L2T L × L2T L) ρ, ∀ n : ℤ, (N : ℝ) < |(n : ℝ)| →
        G x n = rC κ x.1 x.2 n) ∧
      (∀ x ∈ ball ((u₀, star u₀) : L2T L × L2T L) ρ, ∀ n : ℤ, ¬ (N : ℝ) < |(n : ℝ)| → G x n = 0) ∧
      (∀ u : L2T L, ‖u - u₀‖ < ρ → AnalyticAt ℝ (fun u' : L2T L => G (u', star u')) u) ∧
      (∀ u : L2T L, ‖u - u₀‖ < ρ → ∀ n : ℤ, (N : ℝ) < |(n : ℝ)| →
        G (u, star u) n = rn hκ u n ∧ (rn hκ u n).im = 0 ∧ 1 / 2 < (rn hκ u n).re ∧ (rn hκ u n).re < 3 / 2) := by
  classical
  obtain ⟨N₁, ρ₁, hρ₁, M, hM, h⟩ := cx_density (L := L) κ u₀
  obtain ⟨N₂, ρ₂, hρ₂, hD⟩ := density hκ u₀
  set N := max N₁ N₂ with hNdef
  have hN1 : ∀ n : ℤ, (N : ℝ) < |(n : ℝ)| → (N₁ : ℝ) < |(n : ℝ)| := fun n hn =>
    lt_of_le_of_lt (by exact_mod_cast le_max_left N₁ N₂) hn
  have hN2 : ∀ n : ℤ, (N : ℝ) < |(n : ℝ)| → (N₂ : ℝ) < |(n : ℝ)| := fun n hn =>
    lt_of_le_of_lt (by exact_mod_cast le_max_right N₁ N₂) hn
  let Φ : ℤ → L2T L × L2T L → ℂ := fun n x => if (N : ℝ) < |(n : ℝ)| then rC κ x.1 x.2 n else 0
  have han : ∀ n, AnalyticOnNhd ℂ (Φ n) (ball (u₀, star u₀) ρ₁) := by
    intro n
    by_cases hn : (N : ℝ) < |(n : ℝ)|
    · simp only [Φ, if_pos hn]; exact (h n (hN1 n hn)).1
    · simp only [Φ, if_neg hn]; exact analyticOnNhd_const
  have hb : ∀ n, ∀ x ∈ ball ((u₀, star u₀) : L2T L × L2T L) ρ₁, ‖Φ n x‖ ≤ M := by
    intro n x hx
    by_cases hn : (N : ℝ) < |(n : ℝ)|
    · simp only [Φ, if_pos hn]; exact (h n (hN1 n hn)).2 x hx
    · simp only [Φ, if_neg hn, norm_zero]; exact hM
  obtain ⟨G, hG, hGb, -, hGan⟩ := linf_lift hρ₁ hM han hb
  have hρ : 0 < min (ρ₁ / Real.exp 1) ρ₂ := lt_min (by positivity) hρ₂
  have hsub : ball ((u₀, star u₀) : L2T L × L2T L) (min (ρ₁ / Real.exp 1) ρ₂) ⊆
      ball (u₀, star u₀) (ρ₁ / Real.exp 1) := ball_subset_ball (min_le_left _ _)
  have hsub1 : ball ((u₀, star u₀) : L2T L × L2T L) (ρ₁ / Real.exp 1) ⊆ ball (u₀, star u₀) ρ₁ :=
    ball_subset_ball (div_le_self hρ₁.le (Real.one_le_exp zero_le_one))
  have hslice : ∀ u : L2T L, ‖u - u₀‖ < min (ρ₁ / Real.exp 1) ρ₂ →
      ((u, star u) : L2T L × L2T L) ∈ ball (u₀, star u₀) (min (ρ₁ / Real.exp 1) ρ₂) := by
    intro u hu
    rw [mem_ball, Prod.dist_eq, dist_eq_norm, dist_eq_norm, star_sub_norm, max_self]
    exact hu
  refine ⟨N, min (ρ₁ / Real.exp 1) ρ₂, hρ, M, hM, G, hGan.mono hsub, fun x hx => hGb x (hsub1 (hsub hx)),
    fun x hx n hn => ?_, fun x hx n hn => ?_, fun u hu => ?_, fun u hu n hn => ?_⟩
  · rw [hG x (hsub1 (hsub hx)) n]
    simp only [Φ, if_pos hn]
  · rw [hG x (hsub1 (hsub hx)) n]
    simp only [Φ, if_neg hn]
  · have hm := hsub (hslice u hu)
    have hc := AnalyticAt.comp (g := G) (f := ⇑(sliceL (L := L))) (x := u)
      ((hGan _ hm).restrictScalars (𝕜 := ℝ)) ((sliceL (L := L)).analyticAt u)
    exact hc
  · have hu2 : ‖u - u₀‖ < ρ₂ := lt_of_lt_of_le hu (min_le_right _ _)
    have hF := hD n (hN2 n hn) u hu2 1 ⟨zero_le_one, le_rfl⟩
    rw [one_smul] at hF
    obtain ⟨-, -, -, -, ⟨-, him, hlo, hhi⟩, -, -, hrC⟩ := hF
    refine ⟨?_, him, hlo, hhi⟩
    rw [hG _ (hsub1 (hsub (hslice u hu))) n]
    simp only [Φ, if_pos hn]
    exact hrC

end QuantumNLS.RB01CxDensity

#print axioms QuantumNLS.RB01CxDensity.DC_analytic
#print axioms QuantumNLS.RB01CxDensity.EvF_analytic
#print axioms QuantumNLS.RB01CxDensity.rC_analytic
#print axioms QuantumNLS.RB01CxDensity.cx_density
#print axioms QuantumNLS.RB01CxDensity.r_linf
