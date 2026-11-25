import NlsGge.Spectral.ActualGapActionAllNE02_38
import NlsGge.Spectral.ActualGapsActionsE02_38
import NlsGge.Spectral.ActualGapHeightSemicircleE02_38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- Window bound for the boundary value: `|p(x) - x| ≤ 1/4` on the closed window. -/
theorem boundary_sub_le_window_E02_38 (u : PhysicalL2) (n : ℤ)
    (hwin : ActualQuasimomentumWindowE02_38 u n) (x : ℝ)
    (hx : |x - (n:ℝ)*Real.pi| ≤ 1/2) :
    ‖actualQuasimomentumBoundaryE02_38 u x - x‖ ≤ 1/4 := by
  have hlim : Tendsto (fun ε : ℝ => ‖actualQuasimomentumE02_38 u ((x:ℂ) + Complex.I*(ε:ℂ)) -
      ((x:ℂ) + Complex.I*(ε:ℂ))‖) (𝓝[>] 0)
      (𝓝 ‖actualQuasimomentumBoundaryE02_38 u x - x‖) := by
    have h1 := (tendsto_actualQuasimomentumBoundaryE02_38 u x).comp
      (vertical_tendsto_upper_E02_38 x)
    have h2 : Tendsto (fun ε : ℝ => (x:ℂ) + Complex.I*(ε:ℂ)) (𝓝[>] 0) (𝓝 (x:ℂ)) :=
      (vertical_tendsto_upper_E02_38 x).mono_right nhdsWithin_le_nhds
    exact (h1.sub h2).norm
  apply le_of_tendsto hlim
  have hlt : ∀ᶠ ε in 𝓝[>] (0:ℝ), ε < 1 := nhdsWithin_le_nhds (gt_mem_nhds one_pos)
  filter_upwards [self_mem_nhdsWithin, hlt] with ε hε hε1
  exact (hwin _ (by simpa using hε) (by simp; linarith) (by simpa using hx)).le

theorem actualGapLabels_agree_E02_38 (u : PhysicalL2) (n : ℤ) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1/1000)
    (hbox : ActualHalfTraceBoxE02_38 u n δ) (hwin : ActualQuasimomentumWindowE02_38 u n) :
    actualGapLowerE02_38 u n = actualGapLowerAllE02_38 u n ∧
    actualGapUpperE02_38 u n = actualGapUpperAllE02_38 u n ∧
    actualGapActionE02_38 u n = actualGapActionAllE02_38 u n := by
  have hmono := monotone_actualQuasimomentumRealPartE02_38 u
  have hπ := Real.pi_gt_three
  have hset : actualGapClosedSetE02_38 u n = actualGapLevelSetE02_38 u n := by
    obtain ⟨hlr, hl, hu, hDl, hDu, hopen, hnorm⟩ :=
      actualGapStructureE02_38 u n δ hδ0 hδ hbox hwin
    have hsq : Real.sqrt δ ≤ 1/16 := by
      rw [Real.sqrt_le_left (by norm_num)]; nlinarith
    ext x
    constructor
    · rintro ⟨hxW, hx1⟩
      have hxW' : |x - (n:ℝ)*Real.pi| ≤ 1/2 :=
        abs_le.mpr ⟨by linarith [hxW.1], by linarith [hxW.2]⟩
      show actualQuasimomentumRealPartE02_38 u x = (n:ℝ)*Real.pi
      rcases hx1.lt_or_eq with hlt | heq
      · have hxg : x ∈ actualGapE02_38 u n := by rw [← hopen]; exact ⟨hxW, hlt⟩
        exact boundaryLimit_re_gap_E02_38 u n δ hδ0 hδ hbox hwin x hxg _
          (tendsto_actualQuasimomentumBoundaryE02_38 u x)
      · have hend := (hnorm x hxW).mp heq.symm
        have hxn : |x - (n:ℝ)*Real.pi| ≤ 2*Real.sqrt δ := by
          rcases hend with h | h
          · rw [h]; exact hl
          · rw [h]; exact hu
        have hDx : actualPhysicalUnitHalfTrace32 u (x:ℂ) = (Real.cos ((n:ℝ)*Real.pi) : ℂ) := by
          rcases hend with h | h
          · rw [h]; exact hDl
          · rw [h]; exact hDu
        have hv : (actualQuasimomentumBoundaryE02_38 u x).im = 0 := by
          rw [boundaryLimit_im_E02_38 u x _ (tendsto_actualQuasimomentumBoundaryE02_38 u x)]
          unfold actualGapHeightE02_38
          rw [← heq, max_self, Real.arcosh_zero]
        set B := actualQuasimomentumBoundaryE02_38 u x with hB
        have hBr : B = ((B.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hv])
        have hcos : Real.cos B.re = Real.cos ((n:ℝ)*Real.pi) := by
          have := actualQuasimomentumBoundaryE02_38_cos u x
          rw [← hB, hDx, hBr, ← Complex.ofReal_cos] at this
          exact_mod_cast this
        have hb : ‖B - (x:ℂ)‖ ≤ 1/4 := boundary_sub_le_window_E02_38 u n hwin x hxW'
        have hre := Complex.abs_re_le_norm (B - x)
        simp only [Complex.sub_re, Complex.ofReal_re] at hre
        have hbt := abs_le.mp (hre.trans hb)
        have hxn' := abs_le.mp hxn
        set t := B.re - (n:ℝ)*Real.pi with ht
        have hc1 : Real.cos t = 1 := by
          have h1 : Real.cos B.re = Real.cos t * Real.cos ((n:ℝ)*Real.pi) := by
            have : B.re = t + (n:ℝ)*Real.pi := by rw [ht]; ring
            rw [this, Real.cos_add, Real.sin_int_mul_pi]; ring
          have hc2 := real_cos_int_mul_pi_sq_E02_38 n
          rw [hcos] at h1
          have hne : Real.cos ((n:ℝ)*Real.pi) ≠ 0 := by
            intro h; rw [h] at hc2; norm_num at hc2
          have := mul_right_cancel₀ hne (by linarith : 1 * Real.cos ((n:ℝ)*Real.pi) =
            Real.cos t * Real.cos ((n:ℝ)*Real.pi))
          exact this.symm
        have := (Real.cos_eq_one_iff_of_lt_of_lt (x := t) (by linarith) (by linarith)).mp hc1
        show B.re = _
        linarith
    · intro hx
      have hxp : actualQuasimomentumRealPartE02_38 u x = (n:ℝ)*Real.pi := hx
      have hbd : ∀ y : ℝ, |y - (n:ℝ)*Real.pi| ≤ 1/2 →
          |actualQuasimomentumRealPartE02_38 u y - y| ≤ 1/4 := by
        intro y hy
        have hb := boundary_sub_le_window_E02_38 u n hwin y hy
        have hre := Complex.abs_re_le_norm (actualQuasimomentumBoundaryE02_38 u y - y)
        simp only [Complex.sub_re, Complex.ofReal_re] at hre
        exact hre.trans hb
      have hxW : x ∈ Set.Icc ((n:ℝ)*Real.pi - 1/2) ((n:ℝ)*Real.pi + 1/2) := by
        constructor
        · by_contra h
          push Not at h
          have h1 := hmono h.le
          have h2 := abs_le.mp (hbd ((n:ℝ)*Real.pi - 1/2)
            (by rw [show (n:ℝ)*Real.pi - 1/2 - n*Real.pi = -(1/2) by ring]; norm_num))
          linarith
        · by_contra h
          push Not at h
          have h1 := hmono h.le
          have h2 := abs_le.mp (hbd ((n:ℝ)*Real.pi + 1/2)
            (by rw [show (n:ℝ)*Real.pi + 1/2 - n*Real.pi = 1/2 by ring]; norm_num))
          linarith
      refine ⟨hxW, ?_⟩
      set B := actualQuasimomentumBoundaryE02_38 u x with hB
      have hre : B.re = (n:ℝ)*Real.pi := hxp
      have hw : B = (((n:ℝ)*Real.pi : ℝ) : ℂ) + ((B.im : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [hre]
      have hcos := actualQuasimomentumBoundaryE02_38_cos u x
      rw [← hB] at hcos
      rw [← hcos]
      have hr : (Complex.cos B).re = Real.cos ((n:ℝ)*Real.pi) * Real.cosh B.im := by
        conv_lhs => rw [hw]
        rw [Complex.cos_add_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
          ← Complex.ofReal_cosh, ← Complex.ofReal_sinh, Real.sin_int_mul_pi]
        simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, Complex.ofReal_zero, zero_mul, mul_zero, sub_zero]
      have h1 := real_cos_int_mul_pi_sq_E02_38 n
      have h2 := Real.one_le_cosh B.im
      have hab : |Real.cos ((n:ℝ)*Real.pi)| = 1 := by
        have := sq_abs (Real.cos ((n:ℝ)*Real.pi)); rw [h1] at this
        nlinarith [abs_nonneg (Real.cos ((n:ℝ)*Real.pi))]
      calc (1:ℝ) ≤ |(Complex.cos B).re| := by
            rw [hr, abs_mul, hab, one_mul, abs_of_pos (by linarith)]; exact h2
        _ ≤ ‖Complex.cos B‖ := Complex.abs_re_le_norm _
  refine ⟨?_, ?_, ?_⟩
  · unfold actualGapLowerE02_38 actualGapLowerAllE02_38; rw [hset]
  · unfold actualGapUpperE02_38 actualGapUpperAllE02_38; rw [hset]
  · unfold actualGapActionE02_38 actualGapActionAllE02_38
    unfold actualGapLowerE02_38 actualGapUpperE02_38 actualGapLowerAllE02_38
      actualGapUpperAllE02_38
    rw [hset]


end NlsGge.SpectralFoundations
end
