import NlsGge.Spectral.ActualPhysicalUniformHighHeightNormalizedCosine35V2
import NlsGge.Spectral.ComplexLogarithmUpperStripIntegerConstancy35V1
import NlsGge.Spectral.ActualRealParameterDysonConjugationV3
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-! # E02.02 (campaign 38): the concrete quasimomentum and its imaginary boundary value

`actualPhysicalUnitHalfTrace32 u` is HALF the period-one monodromy trace; the source's
`v = arcosh(max{1,|Δ|/2})` (full trace `Δ`) is `arcosh(max 1 ‖Δh‖)` here. -/

/-! ## Elementary complex trigonometry -/

theorem complex_normSq_sin_add_cos_aux_E02_38 (x y : ℝ) :
    ‖Complex.sin ((x:ℂ) + (y:ℂ)*Complex.I)‖^2 + ‖Complex.cos ((x:ℂ) + (y:ℂ)*Complex.I)‖^2 =
      Real.cosh (2*y) := by
  rw [Complex.sin_add_mul_I, Complex.cos_add_mul_I]
  rw [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.sub_re, Complex.sub_im]
  rw [Real.cosh_two_mul]
  have h1 := Real.sin_sq_add_cos_sq x
  have h2 := Real.cosh_sq y
  nlinarith [h1, h2]

theorem complex_normSq_sin_add_cos_E02_38 (w : ℂ) :
    ‖Complex.sin w‖^2 + ‖Complex.cos w‖^2 = Real.cosh (2*w.im) := by
  have h := complex_normSq_sin_add_cos_aux_E02_38 w.re w.im
  rwa [Complex.re_add_im] at h

/-- Ellipse identity: `|cos w - 1| + |cos w + 1| = 2 cosh (Im w)`. -/
theorem complex_cos_ellipse_E02_38 (w : ℂ) :
    ‖Complex.cos w - 1‖ + ‖Complex.cos w + 1‖ = 2 * Real.cosh w.im := by
  have hm : Complex.cos w - 1 = -2 * Complex.sin (w/2)^2 := by
    have := Complex.cos_sq (w/2)
    rw [show 2*(w/2) = w by ring] at this
    have h2 := Complex.sin_sq_add_cos_sq (w/2)
    linear_combination 2 * h2 - 2 * this
  have hp : Complex.cos w + 1 = 2 * Complex.cos (w/2)^2 := by
    have := Complex.cos_sq (w/2)
    rw [show 2*(w/2) = w by ring] at this
    linear_combination -2 * this
  rw [hm, hp, norm_mul, norm_mul, norm_neg, norm_pow, norm_pow]
  have h := complex_normSq_sin_add_cos_E02_38 (w/2)
  have him : (w/2).im = w.im/2 := by simp
  rw [him, show 2*(w.im/2) = w.im by ring] at h
  simp only [Complex.norm_ofNat]
  linarith

/-- For a real number the ellipse parameter is `max 1 |c|`. -/
theorem ellipseParameter_ofReal_E02_38 (c : ℂ) (hc : c.im = 0) :
    (‖c - 1‖ + ‖c + 1‖)/2 = max 1 ‖c‖ := by
  have hc' : c = (c.re : ℂ) := Complex.ext rfl (by simpa using hc)
  rw [hc']
  rw [show (c.re:ℂ) - 1 = ((c.re - 1 : ℝ) : ℂ) by push_cast; ring,
    show (c.re:ℂ) + 1 = ((c.re + 1 : ℝ) : ℂ) by push_cast; ring]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  rcases le_total 0 c.re with h | h
  · rcases le_total c.re 1 with h1 | h1
    · rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg h,
        max_eq_left h1]; ring
    · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg h,
        max_eq_right h1]; ring
  · rcases le_total (-1) c.re with h1 | h1
    · rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith), abs_of_nonpos h,
        max_eq_left (by linarith)]; ring
    · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos h,
        max_eq_right (by linarith)]; ring

theorem one_le_ellipseParameter_E02_38 (c : ℂ) : 1 ≤ (‖c - 1‖ + ‖c + 1‖)/2 := by
  have h : ‖(c + 1) - (c - 1)‖ ≤ ‖c + 1‖ + ‖c - 1‖ := norm_sub_le _ _
  have h2 : (c + 1) - (c - 1) = 2 := by ring
  rw [h2, Complex.norm_ofNat] at h
  linarith

/-! ## The branch predicate, existence, uniqueness, definition -/

/-- An actual quasimomentum branch: analytic on the open upper half-plane, `cos k = Δh`,
`Im k > 0`, and `k(z) - z → 0` uniformly in `Re z` as `Im z → ∞`. -/
def IsActualQuasimomentumBranchE02_38 (u : PhysicalL2) (k : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ k {z : ℂ | 0 < z.im} ∧
  (∀ z : ℂ, 0 < z.im → Complex.cos (k z) = actualPhysicalUnitHalfTrace32 u z) ∧
  (∀ z : ℂ, 0 < z.im → 0 < (k z).im) ∧
  (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ Y : ℝ, R ≤ Y → ∀ x : ℝ,
      ‖k ((x:ℂ) + Complex.I*(Y:ℂ)) - ((x:ℂ) + Complex.I*(Y:ℂ))‖ < ε)

theorem exists_isActualQuasimomentumBranchE02_38 (u : PhysicalL2) :
    ∃ k : ℂ → ℂ, IsActualQuasimomentumBranchE02_38 u k :=
  exists_actualPhysicalUniformHighHeightNormalizedCosine35V2 u

/-- Any two actual quasimomentum branches coincide on the upper half-plane. -/
theorem IsActualQuasimomentumBranchE02_38.eqOn {u : PhysicalL2} {k₁ k₂ : ℂ → ℂ}
    (h₁ : IsActualQuasimomentumBranchE02_38 u k₁)
    (h₂ : IsActualQuasimomentumBranchE02_38 u k₂) :
    Set.EqOn k₁ k₂ {z : ℂ | 0 < z.im} := by
  obtain ⟨ha₁, hc₁, hi₁, hn₁⟩ := h₁
  obtain ⟨ha₂, hc₂, hi₂, hn₂⟩ := h₂
  let g : ℂ → ℂ := fun z => (k₁ z - k₂ z) * Complex.I
  have hg : ContinuousOn g {z : ℂ | 0 < z.im} :=
    ((ha₁.continuousOn.sub ha₂.continuousOn).mul continuousOn_const)
  have he : ∀ z ∈ {z : ℂ | 0 < z.im}, Complex.exp (g z) = 1 := by
    intro z hz
    have hcos : Complex.cos (k₂ z) = Complex.cos (k₁ z) := by
      rw [hc₁ z hz, hc₂ z hz]
    obtain ⟨m, hm | hm⟩ := Complex.cos_eq_cos_iff.mp hcos
    · rw [Complex.exp_eq_one_iff]
      refine ⟨m, ?_⟩
      simp only [g, hm]
      push_cast
      ring
    · exfalso
      have him := congrArg Complex.im hm
      have h1 := hi₁ z hz
      have h2 := hi₂ z hz
      simp at him
      linarith
  obtain ⟨m, hm⟩ := complexLogarithmUpperStrip_integer_constant35 0 g hg he
  obtain ⟨R₁, hR₁, hb₁⟩ := hn₁ 1 one_pos
  obtain ⟨R₂, hR₂, hb₂⟩ := hn₂ 1 one_pos
  set z₀ : ℂ := ((0:ℝ):ℂ) + Complex.I*((max R₁ R₂ : ℝ):ℂ) with hz₀
  have hz₀im : 0 < z₀.im := by
    simp [z₀]; exact Or.inl hR₁
  have e₁ := hb₁ (max R₁ R₂) (le_max_left _ _) 0
  have e₂ := hb₂ (max R₁ R₂) (le_max_right _ _) 0
  have hd : ‖k₁ z₀ - k₂ z₀‖ < 2 := by
    calc ‖k₁ z₀ - k₂ z₀‖ = ‖(k₁ z₀ - z₀) - (k₂ z₀ - z₀)‖ := by ring_nf
      _ ≤ ‖k₁ z₀ - z₀‖ + ‖k₂ z₀ - z₀‖ := norm_sub_le _ _
      _ < 1 + 1 := add_lt_add e₁ e₂
      _ = 2 := by norm_num
  have hkm : ∀ z ∈ {z : ℂ | 0 < z.im}, k₁ z - k₂ z = (m:ℂ) * (2*Real.pi) := by
    intro z hz
    have h := hm z hz
    simp only [g] at h
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    apply mul_right_cancel₀ hI
    rw [h]; ring
  have hm0 : m = 0 := by
    have h := hkm z₀ hz₀im
    rw [h] at hd
    rw [norm_mul, Complex.norm_intCast] at hd
    have hpi : ‖((2*Real.pi : ℝ) : ℂ)‖ = 2*Real.pi := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hpi' : ‖(2*(Real.pi:ℂ))‖ = 2*Real.pi := by
      rw [← hpi]; push_cast; rfl
    rw [hpi'] at hd
    by_contra hne
    have h1 : (1:ℝ) ≤ |(m:ℝ)| := by
      have : (1:ℤ) ≤ |m| := Int.one_le_abs hne
      exact_mod_cast this
    have : 2*Real.pi ≤ |(m:ℝ)| * (2*Real.pi) := by nlinarith [Real.pi_pos]
    linarith [Real.pi_gt_three]
  intro z hz
  have h := hkm z hz
  rw [hm0] at h
  simpa [sub_eq_zero] using h

/-- The concrete quasimomentum of the actual rough potential `u`. By
`IsActualQuasimomentumBranchE02_38.eqOn` its values on the UHP do not depend on the choice. -/
def actualQuasimomentumE02_38 (u : PhysicalL2) : ℂ → ℂ :=
  Classical.choose (exists_isActualQuasimomentumBranchE02_38 u)

theorem isActualQuasimomentumBranch_actualQuasimomentumE02_38 (u : PhysicalL2) :
    IsActualQuasimomentumBranchE02_38 u (actualQuasimomentumE02_38 u) :=
  Classical.choose_spec (exists_isActualQuasimomentumBranchE02_38 u)

theorem actualQuasimomentumE02_38_eqOn_of_isBranch (u : PhysicalL2) (k : ℂ → ℂ)
    (hk : IsActualQuasimomentumBranchE02_38 u k) :
    Set.EqOn (actualQuasimomentumE02_38 u) k {z : ℂ | 0 < z.im} :=
  (isActualQuasimomentumBranch_actualQuasimomentumE02_38 u).eqOn hk

/-- Exact imaginary part of the quasimomentum through the half trace. -/
theorem actualQuasimomentumE02_38_cosh_im (u : PhysicalL2) (z : ℂ) (hz : 0 < z.im) :
    Real.cosh (actualQuasimomentumE02_38 u z).im =
      (‖actualPhysicalUnitHalfTrace32 u z - 1‖ + ‖actualPhysicalUnitHalfTrace32 u z + 1‖)/2 := by
  have h := complex_cos_ellipse_E02_38 (actualQuasimomentumE02_38 u z)
  rw [(isActualQuasimomentumBranch_actualQuasimomentumE02_38 u).2.1 z hz] at h
  linarith

theorem actualQuasimomentumE02_38_im_eq_arcosh (u : PhysicalL2) (z : ℂ) (hz : 0 < z.im) :
    (actualQuasimomentumE02_38 u z).im =
      Real.arcosh ((‖actualPhysicalUnitHalfTrace32 u z - 1‖ +
        ‖actualPhysicalUnitHalfTrace32 u z + 1‖)/2) := by
  rw [← actualQuasimomentumE02_38_cosh_im u z hz, Real.arcosh_cosh
    ((isActualQuasimomentumBranch_actualQuasimomentumE02_38 u).2.2.1 z hz).le]

/-! ## Imaginary boundary value: the gap height `v` -/

/-- The actual half trace is real on the real axis. -/
theorem actualPhysicalUnitHalfTrace32_ofReal_im_E02_38 (u : PhysicalL2) (r : ℝ) :
    (actualPhysicalUnitHalfTrace32 u (r:ℂ)).im = 0 := by
  have h := actualPhysicalL2ZsFullTrace_real u r 1
  have h' : (starRingEnd ℂ) (actualPhysicalUnitHalfTrace32 u (r:ℂ)) =
      actualPhysicalUnitHalfTrace32 u (r:ℂ) := by
    simp only [actualPhysicalUnitHalfTrace32, map_div₀]
    rw [show (starRingEnd ℂ) (2:ℂ) = 2 from Complex.conj_ofNat 2]
    exact congrArg (· / (2:ℂ)) h
  exact Complex.conj_eq_iff_im.mp h'

/-- Source gap height `v(λ) = arcosh(max{1, |Δ(λ)|/2})`, with `Δh = Δ/2`. -/
def actualGapHeightE02_38 (u : PhysicalL2) (lam : ℝ) : ℝ :=
  Real.arcosh (max 1 ‖actualPhysicalUnitHalfTrace32 u (lam : ℂ)‖)

theorem actualGapHeightE02_38_nonneg (u : PhysicalL2) (lam : ℝ) :
    0 ≤ actualGapHeightE02_38 u lam :=
  Real.arcosh_nonneg (le_max_left _ _)

theorem actualGapHeightE02_38_eq_zero_iff (u : PhysicalL2) (lam : ℝ) :
    actualGapHeightE02_38 u lam = 0 ↔ ‖actualPhysicalUnitHalfTrace32 u (lam : ℂ)‖ ≤ 1 := by
  unfold actualGapHeightE02_38
  rw [Real.arcosh_eq_zero_iff (le_max_left _ _), max_eq_left_iff]

theorem continuous_actualGapHeightE02_38 (u : PhysicalL2) :
    Continuous (actualGapHeightE02_38 u) := by
  have hΔ : Continuous (fun lam : ℝ => actualPhysicalUnitHalfTrace32 u (lam : ℂ)) :=
    ((analyticOnNhd_actualPhysicalUnitHalfTrace32 u).continuousOn.comp_continuous
      Complex.continuous_ofReal (fun _ => Set.mem_univ _))
  have hm : Continuous (fun lam : ℝ => max 1 ‖actualPhysicalUnitHalfTrace32 u (lam : ℂ)‖) :=
    continuous_const.max hΔ.norm
  exact Real.continuousOn_arcosh.comp_continuous hm (fun _ => Set.mem_Ici.mpr (le_max_left _ _))

/-- `Im k(λ + iε) → v(λ)` as `ε → 0⁺`, at EVERY real `λ` (bands, gaps, closed gaps). -/
theorem tendsto_im_actualQuasimomentumE02_38 (u : PhysicalL2) (lam : ℝ) :
    Tendsto (fun ε : ℝ => (actualQuasimomentumE02_38 u ((lam : ℂ) + Complex.I*(ε:ℂ))).im)
      (𝓝[>] 0) (𝓝 (actualGapHeightE02_38 u lam)) := by
  let D := actualPhysicalUnitHalfTrace32 u
  let P : ℂ → ℝ := fun c => (‖c - 1‖ + ‖c + 1‖)/2
  have hD : Continuous D :=
    (analyticOnNhd_actualPhysicalUnitHalfTrace32 u).continuousOn.comp_continuous
      continuous_id (fun _ => Set.mem_univ _)
  have hpath : Continuous (fun ε : ℝ => (lam : ℂ) + Complex.I*(ε:ℂ)) := by fun_prop
  have hP : Continuous P := by
    simp only [P]; fun_prop
  have hcomp : Continuous (fun ε : ℝ => Real.arcosh (P (D ((lam : ℂ) + Complex.I*(ε:ℂ))))) :=
    Real.continuousOn_arcosh.comp_continuous (hP.comp (hD.comp hpath))
      (fun _ => Set.mem_Ici.mpr (one_le_ellipseParameter_E02_38 _))
  have hlim := (hcomp.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have h0 : Real.arcosh (P (D ((lam : ℂ) + Complex.I*((0:ℝ):ℂ)))) = actualGapHeightE02_38 u lam := by
    simp only [Complex.ofReal_zero, mul_zero, add_zero, P, D]
    rw [ellipseParameter_ofReal_E02_38 _ (actualPhysicalUnitHalfTrace32_ofReal_im_E02_38 u lam)]
    rfl
  rw [h0] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hz : 0 < ((lam : ℂ) + Complex.I*(ε:ℂ)).im := by simpa using hε
  exact (actualQuasimomentumE02_38_im_eq_arcosh u _ hz).symm

end NlsGge.SpectralFoundations
end
