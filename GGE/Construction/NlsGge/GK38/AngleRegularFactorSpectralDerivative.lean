import NlsGge.GK38.AngleRegularFactor
import NlsGge.GK38.AngleRatioSpectralPartialAnalytic

/-! Source-only literal spectral derivative of the ACTUAL regular factor.
The reciprocal-square term has a PLUS sign. Denominator nonzero and genuine
ratio differentiability precede all derivative identities and weighted bounds. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

theorem angleRegularFactor_spectral_hasDerivAt38 (n m : ℤ)
    (p : PotPair × Lib.L2Seq) (z : ℂ)
    (hp : (p.1,z) ∈ a5OmittedRootDomain38 m)
    (hden : Lib.sigmaOf p.2 n-z ≠ 0) :
    HasDerivAt (fun w => angleRegularFactor38 n m (p,w))
      (Complex.I*(deriv (fun w => p2OmittedRatio38 m (p,w)) z/
          (Lib.sigmaOf p.2 n-z)+
        p2OmittedRatio38 m (p,z)/(Lib.sigmaOf p.2 n-z)^2)) z := by
  have hratio : DifferentiableAt ℂ (fun w => p2OmittedRatio38 m (p,w)) z :=
    ((p2OmittedRatio_analytic38 m (p,z) hp).comp
      (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hd : HasDerivAt (fun w : ℂ => Lib.sigmaOf p.2 n-w) (-1) z := by
    exact (hasDerivAt_id z).const_sub (Lib.sigmaOf p.2 n)
  have h := (hratio.hasDerivAt.const_mul Complex.I).div hd hden
  apply h.congr_deriv
  field_simp [hden]
  ring

theorem angleRegularFactor_weighted_deriv_bound38
    (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (hspec : IsolatingSpectral38 φ C R)
    (n m : ℤ) (hnm : n ≠ m) (s : Lib.L2Seq)
    (hσ : Lib.sigmaOf s n ∈ closedBall (C n) (R n))
    (z : ℂ) (hz : z ∈ closedBall (C m) (R m)) :
    ‖(((n-m : ℤ) : ℂ))*deriv (fun w => angleRegularFactor38 n m ((φ,s),w)) z‖ ≤
      c*‖deriv (fun w => p2OmittedRatio38 m ((φ,s),w)) z‖+
        (c^2/|((n-m : ℤ) : ℝ)|)*‖p2OmittedRatio38 m ((φ,s),z)‖ := by
  have hc : 0 ≤ c := (by norm_num : (0 : ℝ) ≤ 1).trans hg.2.2.1
  have hH : 0 < |((n-m : ℤ) : ℝ)| := abs_pos.mpr (by exact_mod_cast sub_ne_zero.mpr hnm)
  obtain ⟨hden,hweighted⟩ := p2OwnSigma_denominator38 C R c N hg n m hnm s hσ z hz
  have hD : 0 < ‖Lib.sigmaOf s n-z‖ := norm_pos_iff.mpr hden
  have hrecip : 1/‖Lib.sigmaOf s n-z‖ ≤ c/|((n-m : ℤ) : ℝ)| := by
    have hw : |((n-m : ℤ) : ℝ)|/‖Lib.sigmaOf s n-z‖ ≤ c := by
      simpa only [norm_div,Complex.norm_intCast] using hweighted
    apply (div_le_div_iff₀ hD hH).mpr
    simpa only [one_mul] using (div_le_iff₀ hD).mp hw
  have hp := a5OwnClosedBall_omittedDomain38 φ hφ C R ⟨c,N,hg,hspec⟩ m z hz
  rw [(angleRegularFactor_spectral_hasDerivAt38 n m (φ,s) z hp hden).deriv]
  let q : ℂ := p2OmittedRatio38 m ((φ,s),z)
  let q' : ℂ := deriv (fun w => p2OmittedRatio38 m ((φ,s),w)) z
  let D : ℂ := Lib.sigmaOf s n-z
  let k : ℂ := ((n-m : ℤ) : ℂ)
  have he : k*(Complex.I*(q'/D+q/D^2))=
      Complex.I*((k/D)*q'+((k/D)/D)*q) := by
    dsimp only [D]
    field_simp [hden]
  change ‖k*(Complex.I*(q'/D+q/D^2))‖ ≤ c*‖q'‖+(c^2/|((n-m : ℤ) : ℝ)|)*‖q‖
  rw [he,norm_mul,Complex.norm_I,one_mul]
  calc
    _ ≤ ‖(k/D)*q'‖+‖((k/D)/D)*q‖ := norm_add_le _ _
    _ = ‖k/D‖*‖q'‖+(‖k/D‖*(1/‖D‖))*‖q‖ := by
      simp only [norm_mul,norm_div]
      ring
    _ ≤ c*‖q'‖+(c*(c/|((n-m : ℤ) : ℝ)|))*‖q‖ := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hweighted (norm_nonneg _))
        (mul_le_mul_of_nonneg_right
          (mul_le_mul hweighted hrecip (by positivity) hc) (norm_nonneg _))
    _ = _ := by ring

end
end NlsGge.GK38
