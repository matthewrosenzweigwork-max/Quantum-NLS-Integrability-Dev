import NlsGge.Hierarchy.ALExteriorBranch38
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! Batch 38, boundary function `κ` of the AL exterior branch (paper/v2.tex `D:eq:kappa`,
l.1887-1890): `κ(θ) = L⁻¹ arcosh (max 1 |tr M(e^{iθ})/2|)`, and
`L⁻¹ log |w₊(1/(ρ e^{iθ}))| → κ(θ)` as `ρ ↓ 1`, with a uniform bound on `1 < ρ ≤ 2`. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.AblowitzLadik

open Filter Topology Metric Set

/-- `κ(θ) = (1/L) arcosh (max 1 ‖tr M(e^{iθ}) / 2‖)`. -/
def alKappa38 {L : ℕ} (α : ZMod L → ℂ) (θ : ℝ) : ℝ :=
  (1 / (L : ℝ)) *
    Real.arcosh (max 1 ‖Matrix.trace (alMonodromy38 α (Complex.exp ((θ : ℂ) * Complex.I))) / 2‖)

/-- Ellipse parameter `(‖t/2 - 1‖ + ‖t/2 + 1‖)/2`. -/
def alEllipse38 {L : ℕ} (α : ZMod L → ℂ) (z : ℂ) : ℝ :=
  (‖Matrix.trace (alMonodromy38 α z) / 2 - 1‖ + ‖Matrix.trace (alMonodromy38 α z) / 2 + 1‖) / 2

/-! ### Elementary lemmas -/

theorem norm_sub_one_sq_add_norm_add_one_sq38 (w : ℂ) :
    ‖w - 1‖ ^ 2 + ‖w + 1‖ ^ 2 = 2 * ‖w‖ ^ 2 + 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.add_re,
    Complex.one_re, Complex.sub_im, Complex.add_im, Complex.one_im]
  ring

theorem ellipse_sum_norm38 (w a : ℂ) (hw : w ≠ 0) (ha : w + w⁻¹ = 2 * a) :
    ‖a - 1‖ + ‖a + 1‖ = ‖w‖ + ‖w‖⁻¹ := by
  have ha' : a = (w + w⁻¹) / 2 := by linear_combination -ha / 2
  have h1 : a - 1 = (w - 1) ^ 2 * (2 * w)⁻¹ := by rw [ha']; field_simp; ring
  have h2 : a + 1 = (w + 1) ^ 2 * (2 * w)⁻¹ := by rw [ha']; field_simp; ring
  have hr : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have e1 : ‖a - 1‖ = ‖w - 1‖ ^ 2 / (2 * ‖w‖) := by
    rw [h1, norm_mul, norm_pow, norm_inv, norm_mul, Complex.norm_ofNat]; ring
  have e2 : ‖a + 1‖ = ‖w + 1‖ ^ 2 / (2 * ‖w‖) := by
    rw [h2, norm_mul, norm_pow, norm_inv, norm_mul, Complex.norm_ofNat]; ring
  rw [e1, e2, ← add_div, norm_sub_one_sq_add_norm_add_one_sq38]
  field_simp

theorem real_ellipse38 (x : ℝ) : (|x / 2 - 1| + |x / 2 + 1|) / 2 = max 1 |x / 2| := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg (by linarith : 0 ≤ x / 2) ]
    rcases le_total (x / 2) 1 with h1 | h1
    · rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith), max_eq_left h1]; ring
    · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), max_eq_right h1]; ring
  · rw [abs_of_nonpos (by linarith : x / 2 ≤ 0)]
    rcases le_total (-(x / 2)) 1 with h1 | h1
    · rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith), max_eq_left h1]; ring
    · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), max_eq_right h1]; ring

theorem alEllipse38_ge_one {L : ℕ} (α : ZMod L → ℂ) (z : ℂ) : 1 ≤ alEllipse38 α z := by
  unfold alEllipse38
  have h := norm_sub_le (Matrix.trace (alMonodromy38 α z) / 2 + 1)
    (Matrix.trace (alMonodromy38 α z) / 2 - 1)
  have e : Matrix.trace (alMonodromy38 α z) / 2 + 1 - (Matrix.trace (alMonodromy38 α z) / 2 - 1)
      = 2 := by ring
  rw [e] at h
  simp only [Complex.norm_ofNat] at h
  linarith

/-- On the unit circle, the ellipse parameter is `max 1 ‖t/2‖`. -/
theorem alEllipse38_circle {L : ℕ} (α : ZMod L → ℂ) {z : ℂ} (hz : ‖z‖ = 1) :
    alEllipse38 α z = max 1 ‖Matrix.trace (alMonodromy38 α z) / 2‖ := by
  have him := alMonodromy38_trace_im α hz
  set t := Matrix.trace (alMonodromy38 α z) with ht
  have htr : t = ((t.re : ℝ) : ℂ) := Complex.ext (by simp) (by simpa using him)
  unfold alEllipse38
  rw [← ht, htr]
  have e1 : ((t.re : ℝ) : ℂ) / 2 - 1 = ((t.re / 2 - 1 : ℝ) : ℂ) := by push_cast; ring
  have e2 : ((t.re : ℝ) : ℂ) / 2 + 1 = ((t.re / 2 + 1 : ℝ) : ℂ) := by push_cast; ring
  have e3 : ((t.re : ℝ) : ℂ) / 2 = ((t.re / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e1, e2, e3, Complex.norm_real, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, Real.norm_eq_abs]
  exact real_ellipse38 _

/-! ### Key identity -/

theorem alExtW38_norm_add_inv38 {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) {z : ℂ}
    (hz : 1 < ‖z‖) :
    1 < ‖alExtW38 α (1 / z)‖ ∧
      ‖alExtW38 α (1 / z)‖ + ‖alExtW38 α (1 / z)‖⁻¹ = 2 * alEllipse38 α z := by
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
  have hmem : (1 / z) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, one_div, norm_inv]; exact inv_lt_one_of_one_lt₀ hz
  have hne : (1 / z) ≠ 0 := by simpa using hz0
  obtain ⟨-, hroot, hgt⟩ := alExteriorG38_multiplier hα hmem hne
  have hinv : (1 / z)⁻¹ = z := by simp
  rw [hinv] at hroot
  change alExtW38 α (1 / z) ^ 2 - _ * alExtW38 α (1 / z) + 1 = 0 at hroot
  change 1 < ‖alExtW38 α (1 / z)‖ at hgt
  refine ⟨hgt, ?_⟩
  set w := alExtW38 α (1 / z)
  have hw : w ≠ 0 := norm_pos_iff.mp (by linarith)
  have hsum : w + w⁻¹ = 2 * (Matrix.trace (alMonodromy38 α z) / 2) := by
    field_simp
    linear_combination hroot
  rw [← ellipse_sum_norm38 w _ hw hsum]
  unfold alEllipse38
  ring

theorem log_norm_alExtW38_eq_arcosh38 {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α)
    {z : ℂ} (hz : 1 < ‖z‖) :
    Real.log ‖alExtW38 α (1 / z)‖ = Real.arcosh (alEllipse38 α z) := by
  obtain ⟨h1, h2⟩ := alExtW38_norm_add_inv38 hα hz
  set r := ‖alExtW38 α (1 / z)‖
  have hr : 0 < r := by linarith
  have : alEllipse38 α z = Real.cosh (Real.log r) := by
    rw [Real.cosh_eq, Real.exp_log hr, Real.exp_neg, Real.exp_log hr]
    linarith
  rw [this, Real.arcosh_cosh (Real.log_nonneg h1.le)]

/-! ### Continuity of the trace -/

theorem continuousOn_trace38 {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) :
    ContinuousOn (fun z : ℂ => Matrix.trace (alMonodromy38 α z)) {0}ᶜ := by
  have h : ContinuousOn (fun z : ℂ => ∑ k ∈ Finset.range (L + 1),
      alExtCoeff38 α k * z ^ ((L : ℤ) - 2 * k)) {0}ᶜ :=
    continuousOn_finsetSum _ fun k _ => continuousOn_const.mul (continuousOn_zpow₀ _)
  exact h.congr fun z hz => (alExtCoeff38_spec hα).1 z hz

theorem continuousOn_alEllipse38 {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) :
    ContinuousOn (alEllipse38 α) {0}ᶜ := by
  have h := continuousOn_trace38 hα
  unfold alEllipse38
  have h2 : ContinuousOn (fun z : ℂ => Matrix.trace (alMonodromy38 α z) / 2) {0}ᶜ :=
    h.div_const 2
  exact (((h2.sub continuousOn_const).norm).add ((h2.add continuousOn_const).norm)).div_const 2

theorem continuous_alKappa38 {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) :
    Continuous (alKappa38 α) := by
  unfold alKappa38
  refine continuous_const.mul ?_
  have hc : Continuous fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I) := by fun_prop
  have h1 : Continuous fun θ : ℝ =>
      Matrix.trace (alMonodromy38 α (Complex.exp ((θ : ℂ) * Complex.I))) :=
    (continuousOn_trace38 hα).comp_continuous hc (fun θ => Complex.exp_ne_zero _)
  have h2 : Continuous fun θ : ℝ => max 1
      ‖Matrix.trace (alMonodromy38 α (Complex.exp ((θ : ℂ) * Complex.I))) / 2‖ :=
    continuous_const.max (h1.div_const 2).norm
  exact Real.continuousOn_arcosh.comp_continuous h2 (fun θ => mem_Ici.2 (le_max_left _ _))

theorem alKappa38_nonneg {L : ℕ} (α : ZMod L → ℂ) (θ : ℝ) : 0 ≤ alKappa38 α θ := by
  unfold alKappa38
  exact mul_nonneg (by positivity) (Real.arcosh_nonneg (le_max_left _ _))

theorem alKappa38_eq_zero_iff {L : ℕ} [NeZero L] (α : ZMod L → ℂ) (θ : ℝ) :
    alKappa38 α θ = 0 ↔
      ‖Matrix.trace (alMonodromy38 α (Complex.exp ((θ : ℂ) * Complex.I)))‖ ≤ 2 := by
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  unfold alKappa38
  rw [mul_eq_zero, Real.arcosh_eq_zero_iff (le_max_left _ _)]
  have : (1 / (L : ℝ)) ≠ 0 := by simpa using hL
  simp only [this, false_or]
  rw [max_eq_left_iff, norm_div, Complex.norm_ofNat]
  · constructor <;> intro h
    · set x := ‖Matrix.trace (alMonodromy38 α (Complex.exp ((θ : ℂ) * Complex.I)))‖
      linarith
    · set x := ‖Matrix.trace (alMonodromy38 α (Complex.exp ((θ : ℂ) * Complex.I)))‖
      linarith

theorem alKappa38_add_pi_odd {L : ℕ} (hL : Odd L) (α : ZMod L → ℂ) (θ : ℝ) :
    alKappa38 α (θ + Real.pi) = alKappa38 α θ := by
  unfold alKappa38
  have e : Complex.exp (((θ + Real.pi : ℝ) : ℂ) * Complex.I) =
      -Complex.exp ((θ : ℂ) * Complex.I) := by
    push_cast
    rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]; ring
  rw [e, trace_alMonodromy38_neg_odd hL, neg_div, norm_neg]

/-! ### Boundary limit and uniform bound -/

theorem alKappa38_eq_arcosh_ellipse {L : ℕ} (α : ZMod L → ℂ) (θ : ℝ) :
    alKappa38 α θ =
      (1 / (L : ℝ)) * Real.arcosh (alEllipse38 α (Complex.exp ((θ : ℂ) * Complex.I))) := by
  unfold alKappa38
  rw [alEllipse38_circle α (Complex.norm_exp_ofReal_mul_I θ)]

theorem tendsto_alKappa38 {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) (θ : ℝ) :
    Tendsto (fun ρ : ℝ => (1 / (L : ℝ)) *
      Real.log ‖alExtW38 α (1 / ((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))‖)
      (𝓝[>] 1) (𝓝 (alKappa38 α θ)) := by
  have hc : Continuous fun ρ : ℝ => (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by fun_prop
  have hne : ∀ ρ : ℝ, ρ ≠ 0 → (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 :=
    fun ρ h => mul_ne_zero (by exact_mod_cast h) (Complex.exp_ne_zero _)
  have hE : ContinuousOn (fun ρ : ℝ => alEllipse38 α ((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
      {0}ᶜ :=
    (continuousOn_alEllipse38 hα).comp hc.continuousOn (fun ρ hρ => hne ρ hρ)
  have hA : ContinuousOn (fun ρ : ℝ =>
      Real.arcosh (alEllipse38 α ((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))) {0}ᶜ :=
    Real.continuousOn_arcosh.comp hE (fun ρ _ => alEllipse38_ge_one α _)
  have h1 : (1 : ℝ) ∈ ({0}ᶜ : Set ℝ) := by simp
  have hcont := (hA.continuousAt (isOpen_compl_singleton.mem_nhds h1))
  have hlim : Tendsto (fun ρ : ℝ => (1 / (L : ℝ)) *
      Real.arcosh (alEllipse38 α ((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))))
      (𝓝[>] 1) (𝓝 (alKappa38 α θ)) := by
    have := (hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (1 : ℝ)))).const_mul (1 / (L : ℝ))
    rw [alKappa38_eq_arcosh_ellipse]
    simpa using this
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ρ hρ
  have hρ' : (1 : ℝ) < ρ := hρ
  have hn : 1 < ‖(ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
    exact hρ'
  rw [log_norm_alExtW38_eq_arcosh38 hα hn]

theorem alKappa38_uniform_bound {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) :
    ∃ B : ℝ, ∀ ρ ∈ Ioc (1 : ℝ) 2, ∀ θ : ℝ,
      |(1 / (L : ℝ)) *
        Real.log ‖alExtW38 α (1 / ((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))‖| ≤ B := by
  have hK : IsCompact (closedBall (0 : ℂ) 2 \ ball (0 : ℂ) 1) :=
    (isCompact_closedBall _ _).diff isOpen_ball
  have hsub : closedBall (0 : ℂ) 2 \ ball (0 : ℂ) 1 ⊆ {0}ᶜ := by
    intro z hz h0
    apply hz.2
    rw [Set.mem_singleton_iff.mp h0]; exact mem_ball_self one_pos
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn ((continuousOn_trace38 hα).mono hsub)
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  refine ⟨(1 / (L : ℝ)) * (C + 2), fun ρ hρ θ => ?_⟩
  set z : ℂ := (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) with hz
  have hzn : ‖z‖ = ρ := by
    rw [hz, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith [hρ.1])]
  have hzK : z ∈ closedBall (0 : ℂ) 2 \ ball (0 : ℂ) 1 := by
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall_zero_iff, hzn]; exact hρ.2
    · rw [mem_ball_zero_iff, hzn]; exact not_lt.mpr hρ.1.le
  have hT := hC z hzK
  have hz1 : 1 < ‖z‖ := by rw [hzn]; exact hρ.1
  obtain ⟨hr1, hsum⟩ := alExtW38_norm_add_inv38 hα hz1
  set r := ‖alExtW38 α (1 / z)‖
  have hrpos : 0 < r := by linarith
  have hE : alEllipse38 α z ≤ (C + 2) / 2 := by
    unfold alEllipse38
    have h1 := norm_sub_le (Matrix.trace (alMonodromy38 α z) / 2) 1
    have h2 := norm_add_le (Matrix.trace (alMonodromy38 α z) / 2) 1
    rw [norm_div, Complex.norm_ofNat] at h1 h2
    rw [norm_one] at h1 h2
    linarith
  have hr : r ≤ C + 2 := by
    have : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr1.le
    have h3 : 0 < r⁻¹ := inv_pos.mpr hrpos
    linarith
  have hlog0 : 0 ≤ Real.log r := Real.log_nonneg hr1.le
  have hlog : Real.log r ≤ r - 1 := Real.log_le_sub_one_of_pos hrpos
  rw [abs_of_nonneg (mul_nonneg (by positivity) hlog0)]
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

end NlsGge.AblowitzLadik

end
