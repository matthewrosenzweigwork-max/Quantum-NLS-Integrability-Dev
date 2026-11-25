import Mathlib

set_option autoImplicit false

namespace NlsGge.SpectralFoundations

open Complex

/-- Maximum modulus principle for `exp Φ`, stated for the real part of `Φ`. -/
lemma re_le_of_frontier_E02_38 {U : Set ℂ} {Φ : ℂ → ℂ} (hU : Bornology.IsBounded U)
    (hd : DifferentiableOn ℂ Φ U) (hc : ContinuousOn Φ (closure U)) {C : ℝ}
    (hC : ∀ z ∈ frontier U, (Φ z).re ≤ C) {z : ℂ} (hz : z ∈ closure U) : (Φ z).re ≤ C := by
  have h := Complex.norm_le_of_forall_mem_frontier_norm_le (f := fun w => cexp (Φ w)) (U := U) hU
    ⟨hd.cexp, hc.cexp⟩ (C := Real.exp C) (fun w hw => by
      rw [Complex.norm_exp]; exact Real.exp_le_exp.2 (hC w hw)) hz
  rw [Complex.norm_exp] at h
  exact Real.exp_le_exp.1 h

/-- Case `E = ∅` (no exceptional boundary points): if `F` is holomorphic in the open upper half-plane,
continuous on the closed one, has nonnegative imaginary part on `ℝ` and tends to `0` at infinity in the
closed half-plane, then `Im F ≥ 0` on the upper half-plane. Proof: maximum modulus for `exp (i F)` on half-discs. -/
theorem halfPlane_im_nonneg_of_boundary_noExceptions_E02_38 (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F {z | 0 < z.im})
    (hc : ContinuousOn F {z | 0 ≤ z.im})
    (hbd : ∀ x : ℝ, 0 ≤ (F x).im)
    (hinf : ∀ ε > 0, ∃ R, ∀ z : ℂ, 0 ≤ z.im → R ≤ ‖z‖ → ‖F z‖ < ε) :
    ∀ z : ℂ, 0 < z.im → 0 ≤ (F z).im := by
  intro z₀ hz₀
  by_contra hneg
  push Not at hneg
  set η : ℝ := -(F z₀).im with hη
  have hηpos : 0 < η := by rw [hη]; linarith
  obtain ⟨R₀, hR₀⟩ := hinf (η / 4) (by positivity)
  set R : ℝ := |R₀| + ‖z₀‖ + 1 with hR
  set U : Set ℂ := {z : ℂ | 0 < z.im ∧ ‖z‖ < R} with hU
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt continuous_norm continuous_const)
  have hCclosed : IsClosed {z : ℂ | 0 ≤ z.im ∧ ‖z‖ ≤ R} :=
    (isClosed_le continuous_const Complex.continuous_im).inter
      (isClosed_le continuous_norm continuous_const)
  have hUC : U ⊆ {z : ℂ | 0 ≤ z.im ∧ ‖z‖ ≤ R} := fun z hz => ⟨hz.1.le, hz.2.le⟩
  have hclC : closure U ⊆ {z : ℂ | 0 ≤ z.im ∧ ‖z‖ ≤ R} := closure_minimal hUC hCclosed
  have hbounded : Bornology.IsBounded U :=
    (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset
      (fun z hz => by rw [mem_closedBall_zero_iff]; exact hz.2.le)
  have hz₀U : z₀ ∈ U := ⟨hz₀, by rw [hR]; have := abs_nonneg R₀; linarith⟩
  have hd : DifferentiableOn ℂ (fun z => I * F z) U :=
    (hF.mono (fun z hz => hz.1)).const_mul I
  have hcont : ContinuousOn (fun z => I * F z) (closure U) :=
    continuousOn_const.mul (hc.mono (fun z hz => (hclC hz).1))
  have hre : ∀ z : ℂ, (I * F z).re = -(F z).im := by
    intro z; simp [Complex.mul_re]
  have key := re_le_of_frontier_E02_38 (C := η / 4) hbounded hd hcont (z := z₀)
    (fun z hz => by
      rw [hUopen.frontier_eq] at hz
      obtain ⟨hzc, hzU⟩ := hz
      obtain ⟨him, hnorm⟩ := hclC hzc
      rw [hre]
      by_cases h1 : 0 < z.im
      · have h2 : ¬ ‖z‖ < R := fun h2 => hzU ⟨h1, h2⟩
        have h3 : R₀ ≤ ‖z‖ := by
          have h7 : R ≤ ‖z‖ := not_lt.1 h2
          have h8 := le_abs_self R₀
          have h9 := norm_nonneg z₀
          have h10 : R = |R₀| + ‖z₀‖ + 1 := hR
          linarith
        have h4 := hR₀ z him h3
        have h5 := abs_im_le_norm (F z)
        have h6 := neg_abs_le (F z).im
        linarith
      · have h0 : z.im = 0 := le_antisymm (not_lt.1 h1) him
        have hzr : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [h0])
        have := hbd z.re
        rw [← hzr] at this
        linarith)
    (subset_closure hz₀U)
  rw [hre] at key
  linarith


/-- A positive number below all the positive numbers `r e`, `e ∈ E`. -/
lemma exists_pos_lt_finset_E02_38 (E : Finset ℝ) (r : ℝ → ℝ) (hr : ∀ e ∈ E, 0 < r e) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ e ∈ E, ρ < r e := by
  classical
  induction E using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a s ha ih =>
    obtain ⟨ρ, hρ, h⟩ := ih (fun e he => hr e (Finset.mem_insert_of_mem he))
    refine ⟨min ρ (r a / 2), lt_min hρ (half_pos (hr a (Finset.mem_insert_self _ _))), ?_⟩
    intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    · exact lt_of_le_of_lt (min_le_right _ _)
        (half_lt_self (hr _ (Finset.mem_insert_self _ _)))
    · exact lt_of_le_of_lt (min_le_left _ _) (h e he)

/-- The barrier argument `w_e(z) = -i (z - e) / R'`, which maps the closed upper half-plane minus `e`
into the slit plane (`Re w = Im z / R' ≥ 0`, `Im w = -(Re z - e)/R'`). The barrier added to `i F` is
`δ Σ_e log w_e`, whose real part is `δ Σ_e log (|z - e| / R')`. -/
noncomputable def barrierArg_E02_38 (R' e : ℝ) (z : ℂ) : ℂ := -I * (z - (e : ℂ)) / (R' : ℂ)

lemma barrierArg_re_E02_38 (R' e : ℝ) (z : ℂ) : (barrierArg_E02_38 R' e z).re = z.im / R' := by
  unfold barrierArg_E02_38
  rw [Complex.div_ofReal_re]
  simp

lemma barrierArg_im_E02_38 (R' e : ℝ) (z : ℂ) :
    (barrierArg_E02_38 R' e z).im = -(z.re - e) / R' := by
  unfold barrierArg_E02_38
  rw [Complex.div_ofReal_im]
  simp

lemma barrierArg_norm_E02_38 {R' : ℝ} (hR' : 0 < R') (e : ℝ) (z : ℂ) :
    ‖barrierArg_E02_38 R' e z‖ = ‖z - (e : ℂ)‖ / R' := by
  unfold barrierArg_E02_38
  rw [norm_div, norm_mul]
  simp [abs_of_pos hR']

lemma barrierArg_continuous_E02_38 (R' e : ℝ) : Continuous (barrierArg_E02_38 R' e) := by
  unfold barrierArg_E02_38
  fun_prop

lemma barrierArg_differentiable_E02_38 (R' e : ℝ) : Differentiable ℂ (barrierArg_E02_38 R' e) := by
  unfold barrierArg_E02_38
  fun_prop

lemma barrierArg_slit_E02_38 {R' e : ℝ} (hR' : 0 < R') {z : ℂ} (hz : 0 ≤ z.im) (hne : z ≠ (e : ℂ)) :
    barrierArg_E02_38 R' e z ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff, barrierArg_re_E02_38, barrierArg_im_E02_38]
  by_cases h : 0 < z.im
  · exact Or.inl (div_pos h hR')
  · right
    have h0 : z.im = 0 := le_antisymm (not_lt.1 h) hz
    intro h'
    apply hne
    have : z.re - e = 0 := by
      rw [div_eq_zero_iff] at h'
      rcases h' with h' | h'
      · linarith
      · exact absurd h' hR'.ne'
    exact Complex.ext (by simp; linarith) (by simp [h0])

lemma barrierPhi_re_E02_38 (F : ℂ → ℂ) (E : Finset ℝ) (δ R' : ℝ) (z : ℂ) :
    (I * F z + (δ : ℂ) * ∑ e ∈ E, Complex.log (barrierArg_E02_38 R' e z)).re =
      -(F z).im + δ * ∑ e ∈ E, Real.log ‖barrierArg_E02_38 R' e z‖ := by
  simp [Complex.mul_re, Complex.re_sum, Complex.log_re]

/-- General case: finitely many exceptional real points `E` at which `F` is only assumed bounded
(and not continuous up to the boundary). The proof applies the maximum modulus principle to
`exp (i F + δ Σ_{e ∈ E} log (-i (z - e)/R'))` on the half-disc `{Im z > 0, |z| < R}` with the small
half-discs `|z - e| ≤ ρ` removed; the barrier `δ Σ log (|z-e|/R')` is `≤ 0` on the closed half-disc,
tends to `-∞` at each `e`, and `δ` is chosen small after `R` (so the effect at the fixed point is `≤ η/2`). -/
theorem halfPlane_im_nonneg_of_boundary_E02_38 (F : ℂ → ℂ) (E : Finset ℝ)
    (hF : DifferentiableOn ℂ F {z | 0 < z.im})
    (hc : ContinuousOn F ({z | 0 ≤ z.im} \ ((fun e : ℝ => (e : ℂ)) '' (E : Set ℝ))))
    (hbdd : ∀ e ∈ E, ∃ r > 0, ∃ M : ℝ, ∀ z : ℂ, 0 < z.im → ‖z - (e : ℂ)‖ < r → ‖F z‖ ≤ M)
    (hbd : ∀ x : ℝ, x ∉ E → 0 ≤ (F x).im)
    (hinf : ∀ ε > 0, ∃ R : ℝ, ∀ z : ℂ, 0 ≤ z.im → R ≤ ‖z‖ →
      (z ∉ (fun e : ℝ => (e : ℂ)) '' (E : Set ℝ)) → ‖F z‖ < ε) :
    ∀ z : ℂ, 0 < z.im → 0 ≤ (F z).im := by
  classical
  intro z₀ hz₀
  by_contra hneg
  push Not at hneg
  set η : ℝ := -(F z₀).im with hη
  have hηpos : 0 < η := by rw [hη]; linarith
  choose! r hr M hM using hbdd
  obtain ⟨R₀, hR₀⟩ := hinf (η / 4) (by positivity)
  set T : ℝ := ∑ e ∈ E, |e| with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg (fun e _ => abs_nonneg e)
  have heT : ∀ e ∈ E, |e| ≤ T := fun e he =>
    Finset.single_le_sum (f := fun e : ℝ => |e|) (fun e _ => abs_nonneg e) he
  set R : ℝ := |R₀| + ‖z₀‖ + T + 1 with hR
  set R' : ℝ := R + T with hR'
  have hRpos : 0 < R := by
    have := abs_nonneg R₀; have := norm_nonneg z₀; rw [hR]; linarith
  have hR'pos : 0 < R' := by rw [hR']; linarith
  set L : ℝ := ∑ e ∈ E, |M e| with hL
  have hL0 : 0 ≤ L := Finset.sum_nonneg (fun e _ => abs_nonneg _)
  have hML : ∀ e ∈ E, M e ≤ L := fun e he =>
    (le_abs_self (M e)).trans
      (Finset.single_le_sum (f := fun e : ℝ => |M e|) (fun e _ => abs_nonneg _) he)
  set D : ℝ := ∑ e ∈ E, |Real.log ‖barrierArg_E02_38 R' e z₀‖| with hD
  have hD0 : 0 ≤ D := Finset.sum_nonneg (fun e _ => abs_nonneg _)
  set δ : ℝ := η / (2 * (1 + D)) with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hδD : δ * D ≤ η / 2 := by
    have h1 : δ * (1 + D) = η / 2 := by rw [hδ]; field_simp
    have h2 : δ * D ≤ δ * (1 + D) := mul_le_mul_of_nonneg_left (by linarith) hδpos.le
    linarith
  obtain ⟨ρ₁, hρ₁, hρ₁r⟩ := exists_pos_lt_finset_E02_38 E r (fun e he => hr e he)
  set ρ : ℝ := min (min ρ₁ (z₀.im / 2)) (R' * Real.exp (-L / δ)) with hρ
  have hρpos : 0 < ρ := lt_min (lt_min hρ₁ (by linarith)) (by positivity)
  have hρr : ∀ e ∈ E, ρ < r e := fun e he =>
    lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _)) (hρ₁r e he)
  have hρim : ρ ≤ z₀.im / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hρexp : ρ ≤ R' * Real.exp (-L / δ) := min_le_right _ _
  set U : Set ℂ := {z : ℂ | 0 < z.im ∧ ‖z‖ < R ∧ ∀ e ∈ E, ρ < ‖z - (e : ℂ)‖} with hU
  set C : Set ℂ := {z : ℂ | 0 ≤ z.im ∧ ‖z‖ ≤ R ∧ ∀ e ∈ E, ρ ≤ ‖z - (e : ℂ)‖} with hC
  have hset : {z : ℂ | ∀ e ∈ E, ρ < ‖z - (e : ℂ)‖} = ⋂ e ∈ E, {z : ℂ | ρ < ‖z - (e : ℂ)‖} := by
    ext z; simp
  have hset' : {z : ℂ | ∀ e ∈ E, ρ ≤ ‖z - (e : ℂ)‖} = ⋂ e ∈ E, {z : ℂ | ρ ≤ ‖z - (e : ℂ)‖} := by
    ext z; simp
  have hopen3 : IsOpen {z : ℂ | ∀ e ∈ E, ρ < ‖z - (e : ℂ)‖} := by
    rw [hset]
    exact isOpen_biInter_finset (fun e _ =>
      isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const)))
  have hclosed3 : IsClosed {z : ℂ | ∀ e ∈ E, ρ ≤ ‖z - (e : ℂ)‖} := by
    rw [hset']
    exact isClosed_biInter (fun e _ =>
      isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const)))
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      ((isOpen_lt continuous_norm continuous_const).inter hopen3)
  have hCclosed : IsClosed C :=
    (isClosed_le continuous_const Complex.continuous_im).inter
      ((isClosed_le continuous_norm continuous_const).inter hclosed3)
  have hUC : U ⊆ C := fun z hz => ⟨hz.1.le, hz.2.1.le, fun e he => (hz.2.2 e he).le⟩
  have hclC : closure U ⊆ C := closure_minimal hUC hCclosed
  have hbounded : Bornology.IsBounded U :=
    (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset
      (fun z hz => by rw [mem_closedBall_zero_iff]; exact hz.2.1.le)
  have hz₀U : z₀ ∈ U := by
    refine ⟨hz₀, ?_, ?_⟩
    · have := abs_nonneg R₀; rw [hR]; linarith
    · intro e he
      have h1 := abs_im_le_norm (z₀ - (e : ℂ))
      have h2 : (z₀ - (e : ℂ)).im = z₀.im := by simp
      rw [h2, abs_of_pos hz₀] at h1
      linarith
  -- points of `C` avoid `E`
  have hCne : ∀ z ∈ C, ∀ e ∈ E, z ≠ (e : ℂ) := by
    intro z hz e he h
    have := hz.2.2 e he
    rw [h, sub_self, norm_zero] at this
    linarith
  -- each barrier term is nonpositive on `C`
  have hterm : ∀ z ∈ C, ∀ e ∈ E, Real.log ‖barrierArg_E02_38 R' e z‖ ≤ 0 := by
    intro z hz e he
    apply Real.log_nonpos (norm_nonneg _)
    rw [barrierArg_norm_E02_38 hR'pos, div_le_one hR'pos]
    have h1 : ‖z - (e : ℂ)‖ ≤ ‖z‖ + ‖(e : ℂ)‖ := norm_sub_le _ _
    have h2 : ‖(e : ℂ)‖ = |e| := by simp
    have h3 := heT e he
    have h4 := hz.2.1
    rw [hR']; linarith
  have hsum : ∀ z ∈ C, ∑ e ∈ E, Real.log ‖barrierArg_E02_38 R' e z‖ ≤ 0 := fun z hz =>
    Finset.sum_nonpos (fun e he => hterm z hz e he)
  have hdiff : DifferentiableOn ℂ
      (fun z => I * F z + (δ : ℂ) * ∑ e ∈ E, Complex.log (barrierArg_E02_38 R' e z)) U := by
    refine ((hF.mono (fun z hz => hz.1)).const_mul I).add ?_
    refine DifferentiableOn.const_mul ?_ _
    have : DifferentiableOn ℂ (∑ e ∈ E, fun z => Complex.log (barrierArg_E02_38 R' e z)) U :=
      DifferentiableOn.sum (fun e he =>
        ((barrierArg_differentiable_E02_38 R' e).differentiableOn).clog
          (fun z hz => barrierArg_slit_E02_38 hR'pos (hz.1.le) (hCne z (hUC hz) e he)))
    convert this using 1
    ext z
    simp [Finset.sum_apply]
  have hcont : ContinuousOn
      (fun z => I * F z + (δ : ℂ) * ∑ e ∈ E, Complex.log (barrierArg_E02_38 R' e z)) (closure U) := by
    have hFc : ContinuousOn F (closure U) := by
      refine hc.mono (fun z hz => ⟨(hclC hz).1, ?_⟩)
      rintro ⟨e, he, rfl⟩
      exact hCne _ (hclC hz) e he rfl
    refine (continuousOn_const.mul hFc).add (continuousOn_const.mul ?_)
    refine continuousOn_finsetSum E (fun e he => ?_)
    exact (barrierArg_continuous_E02_38 R' e).continuousOn.clog
      (fun z hz => barrierArg_slit_E02_38 hR'pos (hclC hz).1 (hCne z (hclC hz) e he))
  -- frontier estimate
  have hfront : ∀ z ∈ frontier U,
      (I * F z + (δ : ℂ) * ∑ e ∈ E, Complex.log (barrierArg_E02_38 R' e z)).re ≤ η / 4 := by
    intro z hz
    rw [hUopen.frontier_eq] at hz
    obtain ⟨hzc, hzU⟩ := hz
    have hzC := hclC hzc
    obtain ⟨him, hnorm, hdist⟩ := id hzC
    rw [barrierPhi_re_E02_38]
    have hS := hsum z hzC
    have hδS : δ * ∑ e ∈ E, Real.log ‖barrierArg_E02_38 R' e z‖ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hδpos.le hS
    -- the real axis case, used twice
    have hreal : ¬ 0 < z.im → 0 ≤ (F z).im := by
      intro h1
      have h0 : z.im = 0 := le_antisymm (not_lt.1 h1) him
      have hzr : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [h0])
      have hnot : z.re ∉ E := by
        intro hmem
        have := hdist z.re hmem
        rw [← hzr, sub_self, norm_zero] at this
        linarith
      have := hbd z.re hnot
      rwa [← hzr] at this
    by_cases h1 : 0 < z.im
    · by_cases h2 : ‖z‖ < R
      · -- near an exceptional point
        have h3 : ∃ e ∈ E, ‖z - (e : ℂ)‖ ≤ ρ := by
          by_contra hcon
          push Not at hcon
          exact hzU ⟨h1, h2, hcon⟩
        obtain ⟨e₀, he₀, hle⟩ := h3
        have hFz : -(F z).im ≤ L := by
          have h4 := hM e₀ he₀ z h1 (lt_of_le_of_lt hle (hρr e₀ he₀))
          have h5 := abs_im_le_norm (F z)
          have h6 := neg_abs_le (F z).im
          have h7 := hML e₀ he₀
          linarith
        have hpos : 0 < ‖barrierArg_E02_38 R' e₀ z‖ := by
          rw [barrierArg_norm_E02_38 hR'pos]
          exact div_pos (lt_of_lt_of_le hρpos (hdist e₀ he₀)) hR'pos
        have hlog : Real.log ‖barrierArg_E02_38 R' e₀ z‖ ≤ -L / δ := by
          rw [Real.log_le_iff_le_exp hpos, barrierArg_norm_E02_38 hR'pos, div_le_iff₀ hR'pos]
          calc ‖z - (e₀ : ℂ)‖ ≤ ρ := hle
            _ ≤ R' * Real.exp (-L / δ) := hρexp
            _ = Real.exp (-L / δ) * R' := mul_comm _ _
        have hsingle : ∑ e ∈ E, Real.log ‖barrierArg_E02_38 R' e z‖ ≤
            Real.log ‖barrierArg_E02_38 R' e₀ z‖ := by
          have := Finset.single_le_sum (f := fun e : ℝ => -Real.log ‖barrierArg_E02_38 R' e z‖)
            (s := E) (fun e he => neg_nonneg.2 (hterm z hzC e he)) he₀
          rw [Finset.sum_neg_distrib] at this
          linarith
        have h8 : δ * ∑ e ∈ E, Real.log ‖barrierArg_E02_38 R' e z‖ ≤ -L := by
          calc δ * ∑ e ∈ E, Real.log ‖barrierArg_E02_38 R' e z‖
              ≤ δ * (-L / δ) :=
                mul_le_mul_of_nonneg_left (hsingle.trans hlog) hδpos.le
            _ = -L := by field_simp
        linarith
      · have h3 : R₀ ≤ ‖z‖ := by
          have h7 : R ≤ ‖z‖ := not_lt.1 h2
          have h8 := le_abs_self R₀
          have h9 := norm_nonneg z₀
          have h10 : R = |R₀| + ‖z₀‖ + T + 1 := hR
          linarith
        have hzE : z ∉ (fun e : ℝ => (e : ℂ)) '' (E : Set ℝ) := by
          rintro ⟨e, he, rfl⟩
          have h7 : R ≤ ‖(e : ℂ)‖ := not_lt.1 h2
          have h8 : ‖(e : ℂ)‖ = |e| := by simp
          have h9 := heT e he
          have h10 := abs_nonneg R₀
          have h11 := norm_nonneg z₀
          have h12 : R = |R₀| + ‖z₀‖ + T + 1 := hR
          linarith
        have h4 := hR₀ z him h3 hzE
        have h5 := abs_im_le_norm (F z)
        have h6 := neg_abs_le (F z).im
        linarith
    · have := hreal h1
      linarith
  have key := re_le_of_frontier_E02_38 hbounded hdiff hcont hfront (subset_closure hz₀U)
  rw [barrierPhi_re_E02_38] at key
  have hS0 : -D ≤ ∑ e ∈ E, Real.log ‖barrierArg_E02_38 R' e z₀‖ := by
    have h1 : -(∑ e ∈ E, |Real.log ‖barrierArg_E02_38 R' e z₀‖|) ≤
        ∑ e ∈ E, Real.log ‖barrierArg_E02_38 R' e z₀‖ := by
      have := Finset.abs_sum_le_sum_abs (fun e : ℝ => Real.log ‖barrierArg_E02_38 R' e z₀‖) E
      have := neg_abs_le (∑ e ∈ E, Real.log ‖barrierArg_E02_38 R' e z₀‖)
      linarith
    exact h1
  have h2 : δ * (-D) ≤ δ * ∑ e ∈ E, Real.log ‖barrierArg_E02_38 R' e z₀‖ :=
    mul_le_mul_of_nonneg_left hS0 hδpos.le
  have h3 : -(F z₀).im = η := by rw [hη]
  nlinarith

end NlsGge.SpectralFoundations
