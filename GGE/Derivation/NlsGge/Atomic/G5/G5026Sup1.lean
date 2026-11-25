import Mathlib
import NlsGge.Atomic.G5.G5018Sup1
import NlsGge.Atomic.G5.G5018Host
import NlsGge.Atomic.G5.G5024
import NlsGge.Atomic.G2.G2029
import NlsGge.ThirdConsultation.G2.G2072Host
import NlsGge.ThirdConsultation.G5.G5017Support1

/- G5-026 SUPPORT 1 `G5026Sup1` (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G5/G5026Sup1.lean, namespace NlsGge.GKDefinitionDesign.G5026Sup1.
   `core26`: the contour-integration argument of G5-026 (GK 18.3).  Landed inputs taken as parameters (instantiated by the final G5026):
     (h25)  the G5025 identity  2 {Delta_lam, theta_n} = psi_n(lam) for all lam   [landed G5025];
     (hper) the Abelian period of psi_n on the m-th gap: 2 pi if m = n else 0      [landed G2_075].
   Concrete steps: dI_m = -(1/pi) oint gradRootQuotient (landed G2_029); the Poisson pairing with theta_n is minus evaluation on the
   Hamiltonian vector X_theta (antisymmetry); evaluation commutes with the circle integral (landed clm_circleIntegral_comm);
   gradDiscrimCLM phi z X_theta = psi_n(z)/2 by h25; hence the pairing is (1/(2 pi)) * abelianPeriod38. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.ActionGradient

namespace NlsGge.GKDefinitionDesign
namespace G5026Sup1
noncomputable section

theorem circleIntegral_const_mul' (c : ℂ) (g : ℂ → ℂ) (cc : ℂ) (R : ℝ) :
    circleIntegral (fun z => c * g z) cc R = c * circleIntegral g cc R := by
  unfold circleIntegral
  simp only [smul_eq_mul, mul_left_comm _ c]
  exact intervalIntegral.integral_const_mul c _

theorem core26 (u : PhysicalL2) (n m : ℤ)
    (h25 : ∀ lam : ℂ, 2 * pairPoissonCLM (fderiv ℂ (fun φ => discrim φ lam) (realSlice u))
      (angleDerivative n (realSlice u)) = psiAt n lam (realSlice u))
    (hper : abelianPeriod38 m (realSlice u) (psi n (realSlice u)) =
      if m = n then 2 * (Real.pi : ℂ) else 0) :
    pairPoissonCLM (angleDerivative n (realSlice u))
      (fderiv ℂ (fun φ => gkActionC38 φ m) (realSlice u)) = if m = n then 1 else 0 := by
  have hφ : realSlice u ∈ gkW := realSlice_mem_gkW u
  obtain ⟨hint, hfd, -⟩ := G2_029 (realSlice u) hφ m
  rw [hfd.fderiv]
  have e : ∀ M : PotPair →L[ℂ] ℂ, pairPoissonCLM (angleDerivative n (realSlice u)) M =
      -(M (-Complex.I • (pairGradientCLM (angleDerivative n (realSlice u))).2,
        Complex.I • (pairGradientCLM (angleDerivative n (realSlice u))).1)) := fun M => by
    rw [pairPoissonCLM_antisymm]
    rfl
  rw [e]
  set X : PotPair := (-Complex.I • (pairGradientCLM (angleDerivative n (realSlice u))).2,
    Complex.I • (pairGradientCLM (angleDerivative n (realSlice u))).1) with hX
  have hgd : ∀ z : ℂ, gradDiscrimCLM (realSlice u) z X = psiAt n z (realSlice u) / 2 := by
    intro z
    have h := h25 z
    have e1 : pairPoissonCLM (fderiv ℂ (fun φ => discrim φ z) (realSlice u))
        (angleDerivative n (realSlice u)) = gradDiscrimCLM (realSlice u) z X := by
      rw [(hasFDerivAt_gradDiscrimCLM (realSlice u) z).fderiv]
      rfl
    rw [e1] at h
    linear_combination h / 2
  have hcomm := NlsGge.ThirdConsultation.G5017Support1.clm_circleIntegral_comm
    (ContinuousLinearMap.apply ℂ ℂ X) hint
  simp only [ContinuousLinearMap.apply_apply] at hcomm
  have hfun : (fun z => gradRootQuotient (realSlice u) z X) =
      fun z => (1 / 2 : ℂ) * (psi n (realSlice u) z / canonRoot38 (realSlice u) z) := by
    funext z
    simp only [gradRootQuotient, ContinuousLinearMap.smul_apply, smul_eq_mul, hgd]
    show (canonRoot38 (realSlice u) z)⁻¹ * (psiAt n z (realSlice u) / 2) = _
    have : psi n (realSlice u) z = psiAt n z (realSlice u) := rfl
    rw [this]
    ring
  have hI : (circleIntegral (gradRootQuotient (realSlice u)) (discC (realSlice u) m)
      (discR (realSlice u) m)) X = (1 / 2 : ℂ) * abelianPeriod38 m (realSlice u) (psi n (realSlice u)) := by
    rw [hcomm, hfun, circleIntegral_const_mul']
    rfl
  rw [ContinuousLinearMap.smul_apply, hI, hper, smul_eq_mul]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  split_ifs
  · field_simp
  · simp

end
end G5026Sup1
end NlsGge.GKDefinitionDesign
