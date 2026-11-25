import NlsGge.Spectral.ComplexUpperStripUniformLogNormalization35V2
import NlsGge.Spectral.ActualPhysicalSmallBranchUniformScaled35V1
import NlsGge.Spectral.ActualPhysicalUnitAnalyticSmallBranch33V5
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot

/-- The actual physical cosine branch is normalized uniformly over all real
frequencies in the high-height region. One branch and one integer precede
every tolerance and height. Bounded-height escape, the full source infinity
condition, real boundary and signed spectral ordering remain separate. -/
theorem exists_actualPhysicalUniformHighHeightNormalizedCosine35V2 (u : PhysicalL2) :
    ∃ k : ℂ → ℂ, AnalyticOnNhd ℂ k {z : ℂ | 0 < z.im} ∧
      (∀ z : ℂ, 0 < z.im → Complex.cos (k z)=actualPhysicalUnitHalfTrace32 u z) ∧
      (∀ z : ℂ, 0 < z.im → 0 < (k z).im) ∧
      (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
        ∀ Y : ℝ, R ≤ Y → ∀ x : ℝ,
          ‖k ((x : ℂ)+Complex.I*(Y : ℂ))-
            ((x : ℂ)+Complex.I*(Y : ℂ))‖ < ε) := by
  obtain ⟨s, ℓ, hs, hl, hsq, he, hsmall, hu⟩ :=
    exists_actualPhysicalSmallBranch_uniformScaledHighHeight35 u
  have hw : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
      ∀ Y : ℝ, R ≤ Y → ∀ x : ℝ,
        ‖Complex.exp (ℓ ((x : ℂ)+Complex.I*(Y : ℂ))-
          Complex.I*((x : ℂ)+Complex.I*(Y : ℂ)))-1‖ < ε := by
    intro ε hε
    obtain ⟨R, hR, hbound⟩ := hu ε hε
    refine ⟨R, hR, ?_⟩
    intro Y hY x
    have hz : 0 < ((x : ℂ)+Complex.I*(Y : ℂ)).im := by
      simpa using hR.trans_le hY
    rw [Complex.exp_sub, he _ hz]
    exact hbound Y hY x
  obtain ⟨m, hm⟩ := complexUpperStrip_uniformLogNormalization35V2 ℓ hl.continuousOn hw
  let k : ℂ → ℂ := fun z => -Complex.I*(ℓ z-(m : ℂ)*(2*Real.pi*Complex.I))
  have hem : Complex.exp ((m : ℂ)*(2*Real.pi*Complex.I))=1 := by
    have h := (Complex.exp_eq_exp_iff_exists_int
      (x := (m : ℂ)*(2*Real.pi*Complex.I)) (y := 0)).mpr ⟨m, by ring⟩
    simpa only [Complex.exp_zero] using h
  refine ⟨k, analyticOnNhd_const.mul (hl.sub analyticOnNhd_const), ?_, ?_, ?_⟩
  · intro z hz
    have he0 : Complex.exp (ℓ z-(m : ℂ)*(2*Real.pi*Complex.I))=
        actualPhysicalUnitHalfTrace32 u z+s z := by
      rw [Complex.exp_sub, he z hz, hem, div_one]
    exact actualPhysicalUnitCosine_of_squareRoot_log32 u z (s z)
      (ℓ z-(m : ℂ)*(2*Real.pi*Complex.I)) (hsq z hz) he0
  · intro z hz
    have hneg : (ℓ z).re < 0 := by
      apply Real.exp_lt_one_iff.mp
      simpa only [← he z hz, Complex.norm_exp] using hsmall z hz
    simpa [k, Complex.mul_im, Complex.mul_re, Complex.sub_re] using neg_pos.mpr hneg
  · intro ε hε
    obtain ⟨R, hR, hbound⟩ := hm ε hε
    refine ⟨R, hR, ?_⟩
    intro Y hY x
    have h := hbound Y hY x
    have heq : k ((x : ℂ)+Complex.I*(Y : ℂ))-((x : ℂ)+Complex.I*(Y : ℂ)) =
        -Complex.I*(ℓ ((x : ℂ)+Complex.I*(Y : ℂ))-
          Complex.I*((x : ℂ)+Complex.I*(Y : ℂ))-
          (m : ℂ)*(2*Real.pi*Complex.I)) := by
      dsimp [k]
      simp only [sub_eq_add_neg, mul_add, mul_neg, neg_mul, ← mul_assoc, Complex.I_mul_I]
      ring
    rw [heq, norm_mul]
    simpa only [norm_neg, Complex.norm_I, one_mul] using h

end NlsGge.SpectralFoundations
end
