import NlsGge.Spectral.ActualQuasimomentumFullInfinityE02_38
import NlsGge.Spectral.WindowGapStructureE02_38
import NlsGge.Spectral.GapSemicircleActionPrerequisiteV3
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set
open scoped Topology ComplexConjugate
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-! # E02.03/E02.04 (campaign 38): labelled high gaps, `p = πn` on gaps, actions

Labels are given by the window `[nπ - 1/2, nπ + 1/2]`. The structural theorems hold under a
quantitative box hypothesis on the half trace and a window hypothesis on the quasimomentum;
both are realized for every rough `u` and all `|n| ≥ N(u)`. -/

/-! ## Schwarz reflection of the actual half trace -/

theorem actualPhysicalUnitHalfTrace32_conj_E02_38 (u : PhysicalL2) (z : ℂ) :
    actualPhysicalUnitHalfTrace32 u (conj z) = conj (actualPhysicalUnitHalfTrace32 u z) := by
  let D := actualPhysicalUnitHalfTrace32 u
  have hD : Differentiable ℂ D := fun w =>
    ((analyticOnNhd_actualPhysicalUnitHalfTrace32 u) w (Set.mem_univ _)).differentiableAt
  let F : ℂ → ℂ := fun w => conj (D (conj w))
  have hF : Differentiable ℂ F := fun w => by
    have := (hD (conj w)).conj_conj
    rw [Complex.conj_conj] at this
    exact this
  have hDa : AnalyticOnNhd ℂ D Set.univ := fun w _ => (hD.analyticAt w)
  have hFa : AnalyticOnNhd ℂ F Set.univ := fun w _ => (hF.analyticAt w)
  have hreal : ∀ r : ℝ, F r = D r := by
    intro r
    simp only [F, Complex.conj_ofReal]
    exact Complex.conj_eq_iff_im.mpr (actualPhysicalUnitHalfTrace32_ofReal_im_E02_38 u r)
  have hfreq : ∃ᶠ w in 𝓝[≠] (0:ℂ), F w = D w := by
    rw [Filter.frequently_iff]
    intro U hU
    obtain ⟨r, hr, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hU
    refine ⟨((r/2 : ℝ) : ℂ), hsub ⟨?_, ?_⟩, hreal _⟩
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      linarith
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
      exact ne_of_gt (by positivity)
  have heq := hFa.eqOn_of_preconnected_of_frequently_eq hDa isPreconnected_univ
    (Set.mem_univ 0) hfreq
  have h := heq (Set.mem_univ (conj z))
  simp only [F, Complex.conj_conj] at h
  exact h.symm

/-! ## Box and window hypotheses and their realization -/

/-- Quantitative box hypothesis: the actual half trace is `δ`-close to `cos` on the box
`|Re z - nπ| ≤ 1`, `|Im z| ≤ 1`. -/
def ActualHalfTraceBoxE02_38 (u : PhysicalL2) (n : ℤ) (δ : ℝ) : Prop :=
  ∀ z : ℂ, |z.re - n*Real.pi| ≤ 1 → |z.im| ≤ 1 →
    ‖actualPhysicalUnitHalfTrace32 u z - Complex.cos z‖ ≤ δ

/-- Window hypothesis on the concrete quasimomentum above the window. -/
def ActualQuasimomentumWindowE02_38 (u : PhysicalL2) (n : ℤ) : Prop :=
  ∀ z : ℂ, 0 < z.im → z.im ≤ 1 → |z.re - n*Real.pi| ≤ 1/2 →
    ‖actualQuasimomentumE02_38 u z - z‖ < 1/4

theorem exists_actualHalfTraceBox_window_E02_38 (u : PhysicalL2) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℝ, ∀ n : ℤ, N ≤ |(n:ℝ)| →
      ActualHalfTraceBoxE02_38 u n δ ∧ ActualQuasimomentumWindowE02_38 u n := by
  have hev := actualPhysicalUnitHalfTrace_couplingStrip_cosineAsymptotic_E02_38 u 1
    zero_le_one δ hδ
  rw [cocompact_eq_atBot_atTop, eventually_sup] at hev
  obtain ⟨a, ha⟩ := eventually_atBot.mp hev.1
  obtain ⟨b, hb⟩ := eventually_atTop.mp hev.2
  obtain ⟨R, hR, hk⟩ := actualQuasimomentumE02_38_sub_tendsto_zero u (1/4) (by norm_num)
  have h1u : (((1:ℝ):ℂ) • u) = u := by simp
  have hzrep : ∀ z : ℂ, z = ((z.re:ℝ):ℂ) + Complex.I*((z.im:ℝ):ℂ) := by
    intro z; apply Complex.ext <;> simp
  -- upper part of the box from the strip
  have hup : ∀ z : ℂ, (z.re ≤ a ∨ b ≤ z.re) → 0 ≤ z.im → z.im ≤ 1 →
      ‖actualPhysicalUnitHalfTrace32 u z - Complex.cos z‖ ≤ δ := by
    intro z hre h0 h1
    rcases hre with h | h
    · have := ha z.re h 1 (by simp) z.im ⟨h0, h1⟩
      rw [h1u, ← hzrep z] at this; exact this.le
    · have := hb z.re h 1 (by simp) z.im ⟨h0, h1⟩
      rw [h1u, ← hzrep z] at this; exact this.le
  refine ⟨max (max (|a| + 2) (|b| + 2)) (R + 2), ?_⟩
  intro n hn
  have hπ1 : (1:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hnπ : |(n:ℝ)| ≤ |(n:ℝ) * Real.pi| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]; nlinarith [abs_nonneg (n:ℝ)]
  constructor
  · intro z hzr hzi
    have hfar : z.re ≤ a ∨ b ≤ z.re := by
      have hA : |a| + 2 ≤ |(n:ℝ)| := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
      have hB : |b| + 2 ≤ |(n:ℝ)| := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
      rcases le_or_gt 0 ((n:ℝ) * Real.pi) with hp | hp
      · right
        rw [abs_of_nonneg hp] at hnπ
        have := abs_le.mp hzr
        linarith [le_abs_self b]
      · left
        rw [abs_of_neg hp] at hnπ
        have := abs_le.mp hzr
        linarith [neg_abs_le a]
    rcases le_or_gt 0 z.im with h0 | h0
    · exact hup z hfar h0 (abs_le.mp hzi).2
    · have hc := hup (conj z) (by simpa using hfar) (by simp; linarith)
        (by simp; linarith [(abs_le.mp hzi).1])
      rw [actualPhysicalUnitHalfTrace32_conj_E02_38, Complex.cos_conj, ← map_sub,
        Complex.norm_conj] at hc
      exact hc
  · intro z hz0 hz1 hzr
    apply hk z hz0
    have hR2 : R + 2 ≤ |(n:ℝ)| := le_trans (le_max_right _ _) hn
    have hre : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    have := abs_sub_abs_le_abs_sub (n * Real.pi) z.re
    rw [abs_sub_comm] at hzr
    linarith

/-! ## Labelled endpoints, gap, action -/

/-- The set of window points where `|Δh| ≥ 1`. -/
def actualGapClosedSetE02_38 (u : PhysicalL2) (n : ℤ) : Set ℝ :=
  {x : ℝ | x ∈ Set.Icc ((n:ℝ)*Real.pi - 1/2) ((n:ℝ)*Real.pi + 1/2) ∧
    1 ≤ ‖actualPhysicalUnitHalfTrace32 u (x:ℂ)‖}

def actualGapLowerE02_38 (u : PhysicalL2) (n : ℤ) : ℝ := sInf (actualGapClosedSetE02_38 u n)

def actualGapUpperE02_38 (u : PhysicalL2) (n : ℤ) : ℝ := sSup (actualGapClosedSetE02_38 u n)

/-- The labelled open gap `g_n = (λ_n^-, λ_n^+)`. -/
def actualGapE02_38 (u : PhysicalL2) (n : ℤ) : Set ℝ :=
  Set.Ioo (actualGapLowerE02_38 u n) (actualGapUpperE02_38 u n)

/-- The gap action `I_n = (2/π) ∫_{g_n} v`. -/
def actualGapActionE02_38 (u : PhysicalL2) (n : ℤ) : ℝ :=
  (2/Real.pi) * ∫ x in (actualGapLowerE02_38 u n)..(actualGapUpperE02_38 u n),
    actualGapHeightE02_38 u x


theorem real_cos_int_mul_pi_sq_E02_38 (n : ℤ) : Real.cos ((n:ℝ)*Real.pi)^2 = 1 := by
  have h := Real.sin_sq_add_cos_sq ((n:ℝ)*Real.pi)
  rw [Real.sin_int_mul_pi] at h
  linarith

/-- At a point above the window where `Re k = nπ`, `cos(nπ)·Δh = cosh(Im k) ≥ 1`. -/
theorem one_le_cos_mul_halfTrace_of_re_eq_E02_38 (u : PhysicalL2) (n : ℤ) (z : ℂ)
    (hz : 0 < z.im) (hre : (actualQuasimomentumE02_38 u z).re = (n:ℝ)*Real.pi) :
    1 ≤ Real.cos ((n:ℝ)*Real.pi) * (actualPhysicalUnitHalfTrace32 u z).re := by
  have hk := isActualQuasimomentumBranch_actualQuasimomentumE02_38 u
  rw [← hk.2.1 z hz]
  set w := actualQuasimomentumE02_38 u z
  have hw : w = (((n:ℝ)*Real.pi : ℝ) : ℂ) + ((w.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre]
  rw [hw, Complex.cos_add_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    ← Complex.ofReal_cosh, ← Complex.ofReal_sinh, Real.sin_int_mul_pi]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_zero, zero_mul, mul_zero, sub_zero]
  have h1 := real_cos_int_mul_pi_sq_E02_38 n
  have h2 := Real.one_le_cosh w.im
  nlinarith

/-- The window hypothesis forces a point of the closed window with `cos(nπ)·Δh ≥ 1`. -/
theorem exists_one_le_cos_mul_halfTrace_window_E02_38 (u : PhysicalL2) (n : ℤ)
    (hwin : ActualQuasimomentumWindowE02_38 u n) :
    ∃ x ∈ Set.Icc ((n:ℝ)*Real.pi - 1/2) ((n:ℝ)*Real.pi + 1/2),
      1 ≤ Real.cos ((n:ℝ)*Real.pi) * (actualPhysicalUnitHalfTrace32 u (x:ℂ)).re := by
  have hk := isActualQuasimomentumBranch_actualQuasimomentumE02_38 u
  set W := Set.Icc ((n:ℝ)*Real.pi - 1/2) ((n:ℝ)*Real.pi + 1/2) with hW
  let H : ℝ × ℝ → ℝ := fun p =>
    Real.cos ((n:ℝ)*Real.pi) * (actualPhysicalUnitHalfTrace32 u ((p.1:ℂ) + Complex.I*(p.2:ℂ))).re
  have hD : Continuous (actualPhysicalUnitHalfTrace32 u) :=
    (analyticOnNhd_actualPhysicalUnitHalfTrace32 u).continuousOn.comp_continuous
      continuous_id (fun _ => Set.mem_univ _)
  have hH : Continuous H := by
    apply continuous_const.mul
    apply Complex.continuous_re.comp
    apply hD.comp
    fun_prop
  let C : Set (ℝ × ℝ) := (W ×ˢ Set.Icc (0:ℝ) 1) ∩ {p | 1 ≤ H p}
  have hC : IsCompact C :=
    (isCompact_Icc.prod isCompact_Icc).inter_right (isClosed_le continuous_const hH)
  have hCl : IsClosed (Prod.snd '' C) := (hC.image continuous_snd).isClosed
  have hmem : ∀ m : ℕ, (1/((m:ℝ)+1)) ∈ Prod.snd '' C := by
    intro m
    set ε : ℝ := 1/((m:ℝ)+1) with hε
    have hε0 : 0 < ε := by positivity
    have hε1 : ε ≤ 1 := by
      rw [hε, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
    let φ : ℝ → ℝ := fun x => (actualQuasimomentumE02_38 u ((x:ℂ) + Complex.I*(ε:ℂ))).re
    have hφ : ContinuousOn φ W := by
      apply Complex.continuous_re.comp_continuousOn
      apply hk.1.continuousOn.comp
        (show Continuous (fun x : ℝ => (x:ℂ) + Complex.I*(ε:ℂ)) by fun_prop).continuousOn
      intro x _; simp [hε0]
    have hend : ∀ x : ℝ, |x - (n:ℝ)*Real.pi| ≤ 1/2 → |φ x - x| < 1/4 := by
      intro x hx
      have hz := hwin ((x:ℂ) + Complex.I*(ε:ℂ)) (by simp [hε0]) (by simp [hε1])
        (by simpa using hx)
      have hre := Complex.abs_re_le_norm
        (actualQuasimomentumE02_38 u ((x:ℂ) + Complex.I*(ε:ℂ)) - ((x:ℂ) + Complex.I*(ε:ℂ)))
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero,
        add_zero] at hre
      exact lt_of_le_of_lt hre hz
    have hl := hend ((n:ℝ)*Real.pi - 1/2) (by rw [show (n:ℝ)*Real.pi - 1/2 - n*Real.pi = -(1/2)
      by ring, abs_neg, abs_of_pos (by norm_num)])
    have hr := hend ((n:ℝ)*Real.pi + 1/2) (by rw [show (n:ℝ)*Real.pi + 1/2 - n*Real.pi = 1/2
      by ring, abs_of_pos (by norm_num)])
    have hab : (n:ℝ)*Real.pi - 1/2 ≤ (n:ℝ)*Real.pi + 1/2 := by linarith
    obtain ⟨x, hxW, hx⟩ := intermediate_value_Icc hab hφ
      (show (n:ℝ)*Real.pi ∈ Set.Icc (φ ((n:ℝ)*Real.pi - 1/2)) (φ ((n:ℝ)*Real.pi + 1/2)) from
        ⟨by linarith [(abs_lt.mp hl).2], by linarith [(abs_lt.mp hr).1]⟩)
    refine ⟨(x, ε), ⟨⟨hxW, hε0.le, hε1⟩, ?_⟩, rfl⟩
    exact one_le_cos_mul_halfTrace_of_re_eq_E02_38 u n _ (by simp [hε0]) (by simpa [φ] using hx)
  have h0 : (0:ℝ) ∈ Prod.snd '' C :=
    hCl.mem_of_tendsto tendsto_one_div_add_atTop_nhds_zero_nat (Eventually.of_forall hmem)
  obtain ⟨⟨x, y⟩, ⟨⟨hxW, -⟩, hx⟩, rfl⟩ := h0
  refine ⟨x, hxW, ?_⟩
  simpa [H] using hx

/-- Structure of the labelled gap under the box and window hypotheses. -/
theorem actualGapStructureE02_38 (u : PhysicalL2) (n : ℤ) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1/1000) (hbox : ActualHalfTraceBoxE02_38 u n δ)
    (hwin : ActualQuasimomentumWindowE02_38 u n) :
    actualGapLowerE02_38 u n ≤ actualGapUpperE02_38 u n ∧
    |actualGapLowerE02_38 u n - (n:ℝ)*Real.pi| ≤ 2*Real.sqrt δ ∧
    |actualGapUpperE02_38 u n - (n:ℝ)*Real.pi| ≤ 2*Real.sqrt δ ∧
    actualPhysicalUnitHalfTrace32 u (actualGapLowerE02_38 u n : ℂ) =
      (Real.cos ((n:ℝ)*Real.pi) : ℂ) ∧
    actualPhysicalUnitHalfTrace32 u (actualGapUpperE02_38 u n : ℂ) =
      (Real.cos ((n:ℝ)*Real.pi) : ℂ) ∧
    {x : ℝ | x ∈ Set.Icc ((n:ℝ)*Real.pi - 1/2) ((n:ℝ)*Real.pi + 1/2) ∧
        1 < ‖actualPhysicalUnitHalfTrace32 u (x:ℂ)‖} = actualGapE02_38 u n ∧
    (∀ x ∈ Set.Icc ((n:ℝ)*Real.pi - 1/2) ((n:ℝ)*Real.pi + 1/2),
      ‖actualPhysicalUnitHalfTrace32 u (x:ℂ)‖ = 1 ↔
        x = actualGapLowerE02_38 u n ∨ x = actualGapUpperE02_38 u n) := by
  set D := actualPhysicalUnitHalfTrace32 u with hDdef
  have hDd : Differentiable ℂ D := fun w =>
    ((analyticOnNhd_actualPhysicalUnitHalfTrace32 u) w (Set.mem_univ _)).differentiableAt
  have hreal : ∀ x : ℝ, (D x).im = 0 := actualPhysicalUnitHalfTrace32_ofReal_im_E02_38 u
  have hW3 := windowGapStructure_E02_38 D hDd hreal n δ hδ0 hδ hbox
  simp only at hW3
  obtain ⟨hconc, hgc, hgl, hgr, hgneg, hgnorm, hloc⟩ := hW3
  set c := Real.cos ((n:ℝ)*Real.pi) with hc
  set W := Set.Icc ((n:ℝ)*Real.pi - 1/2) ((n:ℝ)*Real.pi + 1/2) with hW
  let g : ℝ → ℝ := fun x => c * (D x).re
  set A := actualGapClosedSetE02_38 u n with hA
  have hAg : ∀ x, x ∈ A ↔ x ∈ W ∧ 1 ≤ g x := by
    intro x
    constructor
    · rintro ⟨hx, h1⟩
      refine ⟨hx, ?_⟩
      have := hgnorm x hx
      rw [this] at h1
      rcases le_abs'.mp h1 with h | h
      · linarith [hgneg x hx]
      · exact h
    · rintro ⟨hx, h1⟩
      refine ⟨hx, ?_⟩
      show 1 ≤ ‖D x‖
      rw [hgnorm x hx]; exact h1.trans (le_abs_self _)
  obtain ⟨x₀, hx₀W, hx₀⟩ := exists_one_le_cos_mul_halfTrace_window_E02_38 u n hwin
  have hx₀A : x₀ ∈ A := (hAg x₀).mpr ⟨hx₀W, hx₀⟩
  have hAne : A.Nonempty := ⟨x₀, hx₀A⟩
  have hAbdd : BddBelow A := ⟨(n:ℝ)*Real.pi - 1/2, fun x hx => hx.1.1⟩
  have hAbddA : BddAbove A := ⟨(n:ℝ)*Real.pi + 1/2, fun x hx => hx.1.2⟩
  have hgcont : Continuous g := hgc
  have hAcl : IsClosed A := by
    have : A = W ∩ {x | 1 ≤ g x} := by ext x; exact hAg x
    rw [this]; exact isClosed_Icc.inter (isClosed_le continuous_const hgcont)
  have hlA : actualGapLowerE02_38 u n ∈ A := hAcl.csInf_mem hAne hAbdd
  have huA : actualGapUpperE02_38 u n ∈ A := hAcl.csSup_mem hAne hAbddA
  set l := actualGapLowerE02_38 u n with hl
  set r := actualGapUpperE02_38 u n with hr
  have hlr : l ≤ r := le_trans (csInf_le hAbdd hx₀A) (le_csSup hAbddA hx₀A)
  have hAsub : ∀ x ∈ A, l ≤ x ∧ x ≤ r := fun x hx => ⟨csInf_le hAbdd hx, le_csSup hAbddA hx⟩
  -- strict concavity inside
  have hinner : ∀ x, l < x → x < r → 1 < g x := by
    intro x hlx hxr
    have hrl : r - l ≠ 0 := ne_of_gt (by linarith)
    have hlW := ((hAg l).mp hlA).1
    have hrW := ((hAg r).mp huA).1
    have ht : x = ((r - x)/(r - l)) • l + ((x - l)/(r - l)) • r := by
      simp only [smul_eq_mul]; field_simp; ring
    have hsum : (r - x)/(r - l) + (x - l)/(r - l) = 1 := by field_simp; ring
    have h := hconc.2 hlW hrW (ne_of_lt (lt_trans hlx hxr)) (div_pos (by linarith) (by linarith))
      (div_pos (by linarith) (by linarith)) hsum
    rw [← ht] at h
    simp only [smul_eq_mul] at h
    have h1 := ((hAg l).mp hlA).2
    have h2 := ((hAg r).mp huA).2
    have hp1 : 0 < (r - x)/(r - l) := div_pos (by linarith) (by linarith)
    have hp2 : 0 < (x - l)/(r - l) := div_pos (by linarith) (by linarith)
    nlinarith
  -- endpoint values
  have hWl : (n:ℝ)*Real.pi - 1/2 < l := by
    rcases lt_or_eq_of_le ((hAg l).mp hlA).1.1 with h | h
    · exact h
    · exfalso; have := ((hAg l).mp hlA).2; rw [← h] at this; linarith
  have hWr : r < (n:ℝ)*Real.pi + 1/2 := by
    rcases lt_or_eq_of_le ((hAg r).mp huA).1.2 with h | h
    · exact h
    · exfalso; have := ((hAg r).mp huA).2; rw [h] at this; linarith
  have hgl1 : g l = 1 := by
    by_contra hne
    have hgt : 1 < g l := lt_of_le_of_ne ((hAg l).mp hlA).2 (Ne.symm hne)
    have hev : ∀ᶠ y in 𝓝 l, 1 < g y := hgcont.continuousAt.eventually (lt_mem_nhds hgt)
    have hev2 : ∀ᶠ y in 𝓝 l, (n:ℝ)*Real.pi - 1/2 < y := lt_mem_nhds hWl
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hev.and hev2)
    have hy : dist (l - ε/2) l < ε := by
      rw [Real.dist_eq, show l - ε/2 - l = -(ε/2) by ring, abs_neg, abs_of_pos (by linarith)]
      linarith
    obtain ⟨h1, h2⟩ := hball hy
    have hyA : l - ε/2 ∈ A := (hAg _).mpr ⟨⟨h2.le, by linarith [((hAg l).mp hlA).1.2]⟩, h1.le⟩
    linarith [(hAsub _ hyA).1]
  have hgr1 : g r = 1 := by
    by_contra hne
    have hgt : 1 < g r := lt_of_le_of_ne ((hAg r).mp huA).2 (Ne.symm hne)
    have hev : ∀ᶠ y in 𝓝 r, 1 < g y := hgcont.continuousAt.eventually (lt_mem_nhds hgt)
    have hev2 : ∀ᶠ y in 𝓝 r, y < (n:ℝ)*Real.pi + 1/2 := gt_mem_nhds hWr
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hev.and hev2)
    have hy : dist (r + ε/2) r < ε := by
      rw [Real.dist_eq, show r + ε/2 - r = ε/2 by ring, abs_of_pos (by linarith)]
      linarith
    obtain ⟨h1, h2⟩ := hball hy
    have hyA : r + ε/2 ∈ A := (hAg _).mpr ⟨⟨by linarith [((hAg r).mp huA).1.1], h2.le⟩, h1.le⟩
    linarith [(hAsub _ hyA).2]
  have hc2 : c^2 = 1 := real_cos_int_mul_pi_sq_E02_38 n
  have hval : ∀ y : ℝ, g y = 1 → D y = (c:ℂ) := by
    intro y hy
    apply Complex.ext
    · simp only [Complex.ofReal_re]
      have : c * (c * (D y).re) = c := by simp only [g] at hy; rw [hy, mul_one]
      calc (D y).re = c^2 * (D y).re := by rw [hc2, one_mul]
        _ = c * (c * (D y).re) := by ring
        _ = c := this
    · simp [hreal y]
  refine ⟨hlr, hloc l ((hAg l).mp hlA).1 hlA.2, hloc r ((hAg r).mp huA).1 huA.2,
    hval l hgl1, hval r hgr1, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨hxW, hx1⟩
      have hxA : x ∈ A := ⟨hxW, hx1.le⟩
      obtain ⟨h1, h2⟩ := hAsub x hxA
      have hgx : 1 < g x := by
        rw [hgnorm x hxW] at hx1
        rcases lt_abs.mp hx1 with h | h
        · exact h
        · linarith [hgneg x hxW]
      refine ⟨lt_of_le_of_ne h1 ?_, lt_of_le_of_ne h2 ?_⟩
      · intro h; rw [← h] at hgx; simp only [g] at hgl1; linarith
      · intro h; rw [h] at hgx; simp only [g] at hgr1; linarith
    · rintro ⟨h1, h2⟩
      have hxW : x ∈ W := ⟨by linarith, by linarith⟩
      refine ⟨hxW, ?_⟩
      rw [hgnorm x hxW]
      exact lt_of_lt_of_le (hinner x h1 h2) (le_abs_self _)
  · intro x hxW
    constructor
    · intro h1
      have hgx : g x = 1 := by
        rw [hgnorm x hxW] at h1
        rcases abs_eq (zero_le_one) |>.mp h1 with h | h
        · exact h
        · linarith [hgneg x hxW]
      obtain ⟨hlx, hxr⟩ := hAsub x ((hAg x).mpr ⟨hxW, hgx.ge⟩)
      by_contra hne
      push Not at hne
      have := hinner x (lt_of_le_of_ne hlx (Ne.symm hne.1)) (lt_of_le_of_ne hxr hne.2)
      linarith
    · rintro (h | h)
      · rw [hgnorm _ hxW, h]; have := hgl1; simp only [g] at this; rw [this, abs_one]
      · rw [hgnorm _ hxW, h]; have := hgr1; simp only [g] at this; rw [this, abs_one]


theorem complex_cos_im_E02_38 (w : ℂ) :
    (Complex.cos w).im = -(Real.sin w.re * Real.sinh w.im) := by
  have hw : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := (Complex.re_add_im w).symm
  conv_lhs => rw [hw]
  rw [Complex.cos_add_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sinh]
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero, mul_one, zero_sub]
  rw [← Complex.ofReal_mul, Complex.ofReal_re]

/-- Source `p|_{g_n} = πn`: on the labelled open gap the real part of the boundary value of
the quasimomentum is `nπ`. -/
theorem tendsto_re_actualQuasimomentum_gap_E02_38 (u : PhysicalL2) (n : ℤ) (δ : ℝ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1/1000) (hbox : ActualHalfTraceBoxE02_38 u n δ)
    (hwin : ActualQuasimomentumWindowE02_38 u n) (x : ℝ) (hx : x ∈ actualGapE02_38 u n) :
    Tendsto (fun ε : ℝ => (actualQuasimomentumE02_38 u ((x:ℂ) + Complex.I*(ε:ℂ))).re)
      (𝓝[>] 0) (𝓝 ((n:ℝ)*Real.pi)) := by
  have hk := isActualQuasimomentumBranch_actualQuasimomentumE02_38 u
  obtain ⟨-, -, -, -, -, hset, -⟩ := actualGapStructureE02_38 u n δ hδ0 hδ hbox hwin
  rw [← hset] at hx
  obtain ⟨hxW, hx1⟩ := hx
  set K : ℝ → ℂ := fun ε => actualQuasimomentumE02_38 u ((x:ℂ) + Complex.I*(ε:ℂ)) with hK
  set c := Real.cos ((n:ℝ)*Real.pi) with hc
  -- imaginary part tends to v(x) > 0
  have hv : 0 < actualGapHeightE02_38 u x := by
    unfold actualGapHeightE02_38
    rw [max_eq_right hx1.le]
    exact Real.arcosh_pos hx1
  have him : Tendsto (fun ε => (K ε).im) (𝓝[>] 0) (𝓝 (actualGapHeightE02_38 u x)) :=
    tendsto_im_actualQuasimomentumE02_38 u x
  have hsinh : Tendsto (fun ε => Real.sinh (K ε).im) (𝓝[>] 0)
      (𝓝 (Real.sinh (actualGapHeightE02_38 u x))) :=
    (Real.continuous_sinh.tendsto _).comp him
  have hsv : 0 < Real.sinh (actualGapHeightE02_38 u x) := Real.sinh_pos_iff.mpr hv
  -- imaginary part of cos(k - nπ) tends to zero
  have hD : Continuous (actualPhysicalUnitHalfTrace32 u) :=
    (analyticOnNhd_actualPhysicalUnitHalfTrace32 u).continuousOn.comp_continuous
      continuous_id (fun _ => Set.mem_univ _)
  have hDlim : Tendsto (fun ε : ℝ => (actualPhysicalUnitHalfTrace32 u
      ((x:ℂ) + Complex.I*(ε:ℂ))).im) (𝓝[>] 0) (𝓝 0) := by
    have h : Continuous (fun ε : ℝ => (actualPhysicalUnitHalfTrace32 u
        ((x:ℂ) + Complex.I*(ε:ℂ))).im) := Complex.continuous_im.comp (hD.comp (by fun_prop))
    have h0 := (h.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    simpa [actualPhysicalUnitHalfTrace32_ofReal_im_E02_38 u x] using h0
  have hcosim : ∀ ε : ℝ, 0 < ε →
      (Complex.cos (K ε - ((n:ℝ)*Real.pi : ℝ))).im =
        c * (actualPhysicalUnitHalfTrace32 u ((x:ℂ) + Complex.I*(ε:ℂ))).im := by
    intro ε hε
    have hz : 0 < ((x:ℂ) + Complex.I*(ε:ℂ)).im := by simpa using hε
    rw [Complex.cos_sub, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.sin_int_mul_pi,
      hK, hk.2.1 _ hz]
    simp only [Complex.ofReal_zero, mul_zero, add_zero, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im]
    rw [hc]; ring
  have hsin : ∀ ε : ℝ, 0 < ε →
      Real.sin ((K ε).re - (n:ℝ)*Real.pi) =
        -(c * (actualPhysicalUnitHalfTrace32 u ((x:ℂ) + Complex.I*(ε:ℂ))).im) /
          Real.sinh (K ε).im := by
    intro ε hε
    have hz : 0 < ((x:ℂ) + Complex.I*(ε:ℂ)).im := by simpa using hε
    have hpos : 0 < Real.sinh (K ε).im := Real.sinh_pos_iff.mpr (hk.2.2.1 _ hz)
    rw [← hcosim ε hε, complex_cos_im_E02_38]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
    field_simp
  have hsinlim : Tendsto (fun ε => Real.sin ((K ε).re - (n:ℝ)*Real.pi)) (𝓝[>] 0) (𝓝 0) := by
    have h := ((hDlim.const_mul c).neg).div hsinh hsv.ne'
    simp only [mul_zero, neg_zero, zero_div] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hsin ε hε).symm
  -- the real part stays within π/2 of nπ for small heights
  have hbd : ∀ᶠ ε in 𝓝[>] (0:ℝ), |(K ε).re - (n:ℝ)*Real.pi| ≤ Real.pi/2 := by
    have hlt : ∀ᶠ ε in 𝓝[>] (0:ℝ), ε < 1 := nhdsWithin_le_nhds (gt_mem_nhds one_pos)
    filter_upwards [self_mem_nhdsWithin, hlt] with ε hε hε1
    have hxn : |x - (n:ℝ)*Real.pi| ≤ 1/2 := abs_le.mpr ⟨by linarith [hxW.1], by linarith [hxW.2]⟩
    have hw := hwin ((x:ℂ) + Complex.I*(ε:ℂ)) (by simpa using hε) (by simp; linarith)
      (by simpa using hxn)
    have hre := Complex.abs_re_le_norm
      (actualQuasimomentumE02_38 u ((x:ℂ) + Complex.I*(ε:ℂ)) - ((x:ℂ) + Complex.I*(ε:ℂ)))
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero,
      add_zero] at hre
    have h1 : |(K ε).re - x| < 1/4 := lt_of_le_of_lt hre hw
    have h2 : |(K ε).re - (n:ℝ)*Real.pi| ≤ |(K ε).re - x| + |x - (n:ℝ)*Real.pi| := by
      have := abs_add_le ((K ε).re - x) (x - (n:ℝ)*Real.pi)
      rwa [show (K ε).re - x + (x - (n:ℝ)*Real.pi) = (K ε).re - (n:ℝ)*Real.pi by ring] at this
    linarith [Real.pi_gt_three]
  have harc := (Real.continuous_arcsin.tendsto 0).comp hsinlim
  rw [Real.arcsin_zero] at harc
  have hre0 : Tendsto (fun ε => (K ε).re - (n:ℝ)*Real.pi) (𝓝[>] 0) (𝓝 0) := by
    refine harc.congr' ?_
    filter_upwards [hbd] with ε hε
    obtain ⟨h1, h2⟩ := abs_le.mp hε
    exact Real.arcsin_sin h1 h2
  have := hre0.add_const ((n:ℝ)*Real.pi)
  simpa using this

/-! ## Actions -/

theorem actualGapActionE02_38_nonneg (u : PhysicalL2) (n : ℤ)
    (hlr : actualGapLowerE02_38 u n ≤ actualGapUpperE02_38 u n) :
    0 ≤ actualGapActionE02_38 u n := by
  unfold actualGapActionE02_38
  apply mul_nonneg (div_nonneg zero_le_two Real.pi_pos.le)
  exact intervalIntegral.integral_nonneg hlr (fun x _ => actualGapHeightE02_38_nonneg u x)

/-- The gap height is interval integrable (it is continuous). -/
theorem intervalIntegrable_actualGapHeightE02_38 (u : PhysicalL2) (a b : ℝ) :
    IntervalIntegrable (actualGapHeightE02_38 u) MeasureTheory.volume a b :=
  (continuous_actualGapHeightE02_38 u).intervalIntegrable a b

/-- NEW-E01 reduction: the pointwise semicircle bound on the labelled gap gives the exact
action lower bound `I_n ≥ |g_n|²/4` (closed gaps included). -/
theorem actualGapAction_lowerBound_of_semicircle_E02_38 (u : PhysicalL2) (n : ℤ)
    (hlr : actualGapLowerE02_38 u n ≤ actualGapUpperE02_38 u n)
    (hsemi : ∀ x ∈ Set.Icc (actualGapLowerE02_38 u n) (actualGapUpperE02_38 u n),
      gapSemicircle (actualGapLowerE02_38 u n) (actualGapUpperE02_38 u n) x ≤
        actualGapHeightE02_38 u x) :
    (actualGapUpperE02_38 u n - actualGapLowerE02_38 u n)^2 / 4 ≤ actualGapActionE02_38 u n := by
  set a := actualGapLowerE02_38 u n
  set b := actualGapUpperE02_38 u n
  have hsc : Continuous (gapSemicircle a b) := by
    unfold gapSemicircle; fun_prop
  have hint : ∫ x in a..b, gapSemicircle a b x ≤ ∫ x in a..b, actualGapHeightE02_38 u x :=
    intervalIntegral.integral_mono_on hlr (hsc.intervalIntegrable a b)
      (intervalIntegrable_actualGapHeightE02_38 u a b) hsemi
  rw [integral_gapSemicircle a b hlr] at hint
  unfold actualGapActionE02_38
  have hpi := Real.pi_pos
  calc (b - a)^2/4 = (2/Real.pi) * ((Real.pi/8) * (b-a)^2) := by field_simp; ring
    _ ≤ (2/Real.pi) * ∫ x in a..b, actualGapHeightE02_38 u x :=
      mul_le_mul_of_nonneg_left hint (by positivity)

end NlsGge.SpectralFoundations
end
