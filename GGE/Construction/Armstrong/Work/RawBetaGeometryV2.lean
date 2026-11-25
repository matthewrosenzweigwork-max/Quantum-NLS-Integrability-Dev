import Armstrong.Frozen.RawBeta.GKOriginalSlit38
import NlsGge.GK38.IsolatingFamily

/-! Actual unrooted geometry in the original isolating ball.  A quadratic
Bezier route from the actual lower tip to the actual Dirichlet endpoint stays
in that same ball.  Its control point is either the endpoint or a small
normal displacement of the lower tip.  The affine-line coordinate of the cut
handles arbitrary complex endpoints; the collapsed cut is treated separately.
-/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

def rawBetaBezierCurve38 (a μ p : ℂ) (t : ℝ) : ℂ :=
  a + t • (μ - a) + (t * (1 - t)) • (p - a)

theorem rawBetaBezierFormula38 (a μ p : ℂ) (t : ℝ) :
    rawBetaBezierCurve38 a μ p t =
      AffineMap.lineMap (AffineMap.lineMap a p t) μ t := by
  simp only [rawBetaBezierCurve38, AffineMap.lineMap_apply_module,
    smul_add, smul_sub, Complex.real_smul]
  push_cast
  ring_nf

theorem rawBetaSegmentRatioImZero38 {a b z : ℂ} (hab : a ≠ b)
    (hz : z ∈ segment ℝ a b) : ((z - a) / (b - a)).im = 0 := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  rw [segment_eq_image_lineMap ℝ a b] at hz
  rcases hz with ⟨s, hs, hzs⟩
  have hquot : (AffineMap.lineMap a b s - a) / (b - a) = (s : ℂ) := by
    rw [AffineMap.lineMap_apply_module]
    simp only [Complex.real_smul]
    push_cast
    field_simp [hba]
    ring
  rw [← hzs, hquot]
  simp

theorem rawBetaBezierCurveFacts38 (a μ p c : ℂ) (r : ℝ)
    (ha : a ∈ ball c r) (hμ : μ ∈ ball c r) (hp : p ∈ ball c r) :
    ContinuousOn (rawBetaBezierCurve38 a μ p) (Icc (0 : ℝ) 1) ∧
    ContDiffOn ℝ 1 (rawBetaBezierCurve38 a μ p) (Icc (0 : ℝ) 1) ∧
    rawBetaBezierCurve38 a μ p 0 = a ∧
    rawBetaBezierCurve38 a μ p 1 = μ ∧
    (∀ t ∈ Icc (0 : ℝ) 1, rawBetaBezierCurve38 a μ p t ∈ ball c r) := by
  have hsmooth : ContDiff ℝ 1 (rawBetaBezierCurve38 a μ p) := by
    unfold rawBetaBezierCurve38
    fun_prop
  have hball (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      rawBetaBezierCurve38 a μ p t ∈ ball c r := by
    rw [rawBetaBezierFormula38]
    apply (convex_ball c r).segment_subset
    · exact (convex_ball c r).segment_subset ha hp
        (lineMap_mem_segment ℝ a p ht)
    · exact hμ
    · exact lineMap_mem_segment ℝ _ _ ht
  exact ⟨hsmooth.continuous.continuousOn, hsmooth.contDiffOn,
    by simp [rawBetaBezierCurve38], by simp [rawBetaBezierCurve38], hball⟩

theorem rawBetaUnrootedBezier38 (a b μ c : ℂ) (r : ℝ)
    (ha : a ∈ ball c r) (hμ : μ ∈ ball c r) :
    ∃ γ : ℝ → ℂ,
      ContinuousOn γ (Icc (0 : ℝ) 1) ∧
      ContDiffOn ℝ 1 γ (Icc (0 : ℝ) 1) ∧
      γ 0 = a ∧ γ 1 = μ ∧
      (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ ball c r) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, γ t ∉ segment ℝ a b) := by
  have hgap : 0 < r - ‖a - c‖ := by
    exact sub_pos.mpr (mem_ball_iff_norm.mp ha)
  let η : ℝ := (r - ‖a - c‖) / (2 * (‖b - a‖ + 1))
  have hden : 2 * (‖b - a‖ + 1) ≠ 0 := by positivity
  have hη : 0 < η := by
    dsimp [η]
    exact div_pos hgap (mul_pos (by norm_num) (by positivity))
  have hnear (v : ℂ) (hv : ‖v‖ ≤ ‖b - a‖ + 1) :
      a + (η : ℂ) * v ∈ ball c r := by
    apply mem_ball_iff_norm.mpr
    have hsmall : ‖(η : ℂ) * v‖ < r - ‖a - c‖ := by
      calc
        ‖(η : ℂ) * v‖ = η * ‖v‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη]
        _ ≤ η * (‖b - a‖ + 1) := mul_le_mul_of_nonneg_left hv hη.le
        _ = (r - ‖a - c‖) / 2 := by
          dsimp [η]
          field_simp [hden]
        _ < r - ‖a - c‖ := by linarith
    have hdiff : a + (η : ℂ) * v - c = (a - c) + (η : ℂ) * v := by abel
    rw [hdiff]
    calc
      ‖(a - c) + (η : ℂ) * v‖ ≤ ‖a - c‖ + ‖(η : ℂ) * v‖ := norm_add_le _ _
      _ < ‖a - c‖ + (r - ‖a - c‖) := by linarith [hsmall]
      _ = r := by ring
  by_cases hcollapsed : b = a
  · subst b
    by_cases hterminal : μ = a
    · let p : ℂ := a + (η : ℂ)
      have hp : p ∈ ball c r := by
        simpa [p] using hnear (1 : ℂ) (by simp)
      have hfacts := rawBetaBezierCurveFacts38 a μ p c r ha hμ hp
      rcases hfacts with ⟨hcont, hcd, h0, h1, hball⟩
      let γ : ℝ → ℂ := rawBetaBezierCurve38 a μ p
      have havoid : ∀ t ∈ Ioo (0 : ℝ) 1, γ t ∉ segment ℝ a a := by
        intro t ht
        have hdiff : γ t - a = ((t * (1 - t) * η : ℝ) : ℂ) := by
          simp [γ, p, rawBetaBezierCurve38, hterminal, Complex.real_smul] <;>
            push_cast <;> ring
        have hpos : 0 < t * (1 - t) * η :=
          mul_pos (mul_pos ht.1 (sub_pos.mpr ht.2)) hη
        have hneq : γ t ≠ a := by
          intro heq
          have hz : γ t - a = 0 := sub_eq_zero.mpr heq
          rw [hdiff] at hz
          exact (Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)) hz
        simpa [segment_same] using hneq
      exact ⟨γ, hcont, hcd, h0, h1, hball, havoid⟩
    · let p : ℂ := μ
      have hp : p ∈ ball c r := by simpa [p] using hμ
      have hfacts := rawBetaBezierCurveFacts38 a μ p c r ha hμ hp
      rcases hfacts with ⟨hcont, hcd, h0, h1, hball⟩
      let γ : ℝ → ℂ := rawBetaBezierCurve38 a μ p
      have havoid : ∀ t ∈ Ioo (0 : ℝ) 1, γ t ∉ segment ℝ a a := by
        intro t ht
        have hdiff : γ t - a = ((t * (2 - t) : ℝ) : ℂ) * (μ - a) := by
          simp [γ, p, rawBetaBezierCurve38] <;> push_cast <;> ring
        have hpos : 0 < t * (2 - t) := mul_pos ht.1 (by linarith [ht.2])
        have hprod : ((t * (2 - t) : ℝ) : ℂ) * (μ - a) ≠ 0 :=
          mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hpos))
            (sub_ne_zero.mpr hterminal)
        have hneq : γ t ≠ a := by
          intro heq
          have hz : γ t - a = 0 := sub_eq_zero.mpr heq
          rw [hdiff] at hz
          exact hprod hz
        simpa [segment_same] using hneq
      exact ⟨γ, hcont, hcd, h0, h1, hball, havoid⟩
  · have hba : b - a ≠ 0 := sub_ne_zero.mpr hcollapsed
    have hab : a ≠ b := Ne.symm hcollapsed
    let w : ℂ := (μ - a) / (b - a)
    have hwcoord : (μ - a) / (b - a) = w := rfl
    by_cases hw : w.im = 0
    · let v : ℂ := Complex.I * (b - a)
      let p : ℂ := a + (η : ℂ) * v
      have hv : ‖v‖ ≤ ‖b - a‖ + 1 := by
        calc
          ‖v‖ = ‖b - a‖ := by simp [v]
          _ ≤ ‖b - a‖ + 1 := le_add_of_nonneg_right (by norm_num)
      have hp : p ∈ ball c r := by
        simpa [p] using hnear v hv
      have hfacts := rawBetaBezierCurveFacts38 a μ p c r ha hμ hp
      rcases hfacts with ⟨hcont, hcd, h0, h1, hball⟩
      let γ : ℝ → ℂ := rawBetaBezierCurve38 a μ p
      have hpc : (p - a) / (b - a) = (η : ℂ) * Complex.I := by
        apply (div_eq_iff hba).mpr
        dsimp [p, v]
        push_cast
        ring
      have hγcoord (t : ℝ) : (γ t - a) / (b - a) =
          (t : ℂ) * ((μ - a) / (b - a)) +
            ((t * (1 - t) : ℝ) : ℂ) * ((p - a) / (b - a) : ℂ) := by
        apply (div_eq_iff hba).mpr
        simp only [γ, rawBetaBezierCurve38, Complex.real_smul]
        push_cast
        field_simp [hba]
        ring
      have hγimag (t : ℝ) : ((γ t - a) / (b - a)).im = t * (1 - t) * η := by
        rw [hγcoord t, hwcoord, hpc]
        simp [Complex.mul_im, hw]
      have havoid : ∀ t ∈ Ioo (0 : ℝ) 1, γ t ∉ segment ℝ a b := by
        intro t ht hz
        have hzero := rawBetaSegmentRatioImZero38 hab hz
        rw [hγimag t] at hzero
        have hpos : 0 < t * (1 - t) * η :=
          mul_pos (mul_pos ht.1 (sub_pos.mpr ht.2)) hη
        exact (ne_of_gt hpos) hzero
      exact ⟨γ, hcont, hcd, h0, h1, hball, havoid⟩
    · let p : ℂ := μ
      have hp : p ∈ ball c r := by simpa [p] using hμ
      have hfacts := rawBetaBezierCurveFacts38 a μ p c r ha hμ hp
      rcases hfacts with ⟨hcont, hcd, h0, h1, hball⟩
      let γ : ℝ → ℂ := rawBetaBezierCurve38 a μ p
      have hpc : (p - a) / (b - a) = w := by simp [p, w]
      have hγcoord (t : ℝ) : (γ t - a) / (b - a) =
          (t : ℂ) * ((μ - a) / (b - a)) +
            ((t * (1 - t) : ℝ) : ℂ) * ((p - a) / (b - a) : ℂ) := by
        apply (div_eq_iff hba).mpr
        simp only [γ, rawBetaBezierCurve38, Complex.real_smul]
        push_cast
        field_simp [hba]
        ring
      have hγimag (t : ℝ) : ((γ t - a) / (b - a)).im = t * (2 - t) * w.im := by
        rw [hγcoord t, hwcoord]
        simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im]
        ring
      have havoid : ∀ t ∈ Ioo (0 : ℝ) 1, γ t ∉ segment ℝ a b := by
        intro t ht hz
        have hzero := rawBetaSegmentRatioImZero38 hab hz
        rw [hγimag t] at hzero
        have hpos : 0 < t * (2 - t) := mul_pos ht.1 (by linarith [ht.2])
        have hne : t * (2 - t) * w.im ≠ 0 := mul_ne_zero (ne_of_gt hpos) hw
        exact hne hzero
      exact ⟨γ, hcont, hcd, h0, h1, hball, havoid⟩

theorem rawBetaUnrootedCurveExists38 (φ : GKPotential38) (m : ℤ) :
    ∃ γ : ℝ → ℂ,
      ContinuousOn γ (Icc (0 : ℝ) 1) ∧
      ContDiffOn ℝ 1 γ (Icc (0 : ℝ) 1) ∧
      γ 0 = lamMinus φ.1 m ∧ γ 1 = muSeq φ.1 m ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        γ t ∈ ball (discC φ.1 m) (discR φ.1 m)) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, γ t ∈ GKOriginalSlit38 φ m) := by
  obtain ⟨_, _, _, hspec⟩ := isolating_family38 φ.1 φ.2
  let a : ℂ := lamMinus φ.1 m
  let b : ℂ := lamPlus φ.1 m
  let μ : ℂ := muSeq φ.1 m
  let c : ℂ := discC φ.1 m
  let r : ℝ := discR φ.1 m
  have hcut : segment ℝ a b ⊆ ball c r := by
    simpa [a, b, c, r] using (hspec.1 m).1
  have ha : a ∈ ball c r := hcut (left_mem_segment ℝ a b)
  have hμ : μ ∈ ball c r := by
    simpa [μ, c, r] using (hspec.1 m).2.1
  obtain ⟨γ, hcont, hcd, h0, h1, hball, havoid⟩ :=
    rawBetaUnrootedBezier38 a b μ c r ha hμ
  refine ⟨γ, hcont, hcd, ?_, ?_, ?_, ?_⟩
  · simpa [a] using h0
  · simpa [μ] using h1
  · intro t ht
    simpa [c, r] using hball t ht
  · intro t ht
    change γ t ∈ ball (discC φ.1 m) (discR φ.1 m) \
      segment ℝ (lamMinus φ.1 m) (lamPlus φ.1 m)
    refine ⟨?_, ?_⟩
    · exact hball t ⟨ht.1.le, ht.2.le⟩
    · simpa [a, b] using havoid t ht

end
end NlsGge.GK38

#check @NlsGge.GK38.rawBetaBezierCurve38
#print axioms NlsGge.GK38.rawBetaBezierCurve38
#check @NlsGge.GK38.rawBetaBezierFormula38
#print axioms NlsGge.GK38.rawBetaBezierFormula38
#check @NlsGge.GK38.rawBetaSegmentRatioImZero38
#print axioms NlsGge.GK38.rawBetaSegmentRatioImZero38
#check @NlsGge.GK38.rawBetaBezierCurveFacts38
#print axioms NlsGge.GK38.rawBetaBezierCurveFacts38
#check @NlsGge.GK38.rawBetaUnrootedBezier38
#print axioms NlsGge.GK38.rawBetaUnrootedBezier38
#check @NlsGge.GK38.rawBetaUnrootedCurveExists38
#print axioms NlsGge.GK38.rawBetaUnrootedCurveExists38
