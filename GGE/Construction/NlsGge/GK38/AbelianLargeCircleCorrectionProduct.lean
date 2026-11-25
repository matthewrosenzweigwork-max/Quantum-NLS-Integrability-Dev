import NlsGge.GK38.AbelianLargeCircleRootCorrection
import NlsGge.GK38.XiSqConvolutionUniform

/-! Full ordinary root correction and its exact canonical-root factorization.
The full integer symmetric product and the leading 2*I are retained literally. -/
set_option autoImplicit false
open Filter Topology SummationFilter
namespace NlsGge.GK38
noncomputable section

def p6FullRootCorrection38 (σ g : ℤ → ℂ) (z : ℂ) : ℂ :=
  ∏' m : ℤ, Complex.sqrt (1-(g m/4)/(σ m-z)^2)

theorem p6LargeCircle_root_correction_product38 (σ g : ℤ → ℂ)
    (hσ : Summable (fun m : ℤ => ‖σ m-(m : ℂ)*(Real.pi : ℂ)‖^2))
    (hg : Summable (fun m : ℤ => ‖g m‖^2)) :
    ∀ ε > 0, ∃ N : ℕ, ∀ ν : ℕ, N ≤ ν → ∀ z : ℂ,
      ‖z‖=ν*Real.pi+Real.pi/2 →
      Multipliable (fun m : ℤ => Complex.sqrt (1-(g m/4)/(σ m-z)^2)) ∧
      ‖p6FullRootCorrection38 σ g z-1‖ ≤ ε := by
  intro ε hε
  have hlog : 0 < Real.log (1+ε) := Real.log_pos (by linarith)
  obtain ⟨N,hN⟩ := p6LargeCircle_root_correction_errors38 σ g hσ hg _ hlog
  refine ⟨N,fun ν hν z hz => ?_⟩
  obtain ⟨hs,hb⟩ := hN ν hν z hz
  have he : (fun m : ℤ => 1+(Complex.sqrt (1-(g m/4)/(σ m-z)^2)-1))=
      (fun m : ℤ => Complex.sqrt (1-(g m/4)/(σ m-z)^2)) := by
    funext m; ring
  have hm := multipliable_one_add_of_summable hs
  have hp := Lib.norm_tprod_one_add_sub_one_le hs
  rw [he] at hm hp
  refine ⟨hm,hp.trans ?_⟩
  change Real.exp (∑' m : ℤ, ‖Complex.sqrt (1-(g m/4)/(σ m-z)^2)-1‖)-1 ≤ ε
  have hx := Real.exp_le_exp.mpr hb
  rw [Real.exp_log (by linarith : 0 < 1+ε)] at hx
  linarith

theorem p6Actual_canonical_root_full_correction38 (φ : PotPair) (hφ : φ ∈ gkW)
    (z : ℂ)
    (hQ : Summable (fun m : ℤ =>
      ‖Complex.sqrt (1-(gamma2 φ m/4)/(tauN φ m-z)^2)-1‖)) :
    Multipliable (fun m : ℤ => rootFactor38 m (φ,z)) (symmetricIcc ℤ) ∧
    canonRoot38 φ z=2*Complex.I*
      (∏'[symmetricIcc ℤ] m : ℤ, (tauN φ m-z)/(Lib.piN m : ℂ))*
      p6FullRootCorrection38 (tauN φ) (gamma2 φ) z := by
  have hτsq : Summable (fun m : ℤ => ‖Lib.prodDev (tauN φ) m‖^2) := by
    simpa only [Lib.prodDev,← a5TauShift_value38 φ hφ] using
      (Lib.hasSum_sq_l2 (a5TauShift38 φ)).summable
  have hτ := (Lib.multipliable_prodFactor hτsq z).hasProd
  have he : (fun m : ℤ => 1+(Complex.sqrt (1-(gamma2 φ m/4)/(tauN φ m-z)^2)-1))=
      (fun m : ℤ => Complex.sqrt (1-(gamma2 φ m/4)/(tauN φ m-z)^2)) := by
    funext m; ring
  have hQprod := multipliable_one_add_of_summable hQ
  rw [he] at hQprod
  have hQsym := hQprod.hasProd.mono_left (symmetricIcc ℤ).le_atTop
  have hf : (fun m : ℤ => Lib.prodFactor (tauN φ) z m*
      Complex.sqrt (1-(gamma2 φ m/4)/(tauN φ m-z)^2))=
      (fun m : ℤ => rootFactor38 m (φ,z)) := by
    funext m
    dsimp [Lib.prodFactor,rootFactor38,stdRoot38]
    ring
  have hp := hτ.mul hQsym
  rw [hf] at hp
  refine ⟨hp.multipliable,?_⟩
  unfold canonRoot38 p6FullRootCorrection38
  rw [hp.tprod_eq]
  simp only [Lib.prodFactor,mul_assoc]

end
end NlsGge.GK38
