import Mathlib
import NlsGge.GK38.Defs
import NlsGge.ThirdConsultation.G5.G5017Support1

/- G5-031 SUPPORT 2 `G5031Sup2` (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G5/G5031Sup2.lean, namespace NlsGge.GKDefinitionDesign.G5031Sup2.
   (1) Every potential pair is `realSlice a + I • realSlice b` (the potential space is the complexification of the real slice).
   (2) A complex-differentiable function that is locally constant along the real slice near u has zero derivative at `realSlice u`. -/
set_option autoImplicit false

open Set Filter Topology
open NlsGge.Pilot NlsGge.GK38
open NlsGge.ThirdConsultation.G5017Support1

namespace NlsGge.GKDefinitionDesign
namespace G5031Sup2
noncomputable section

theorem exists_realSlice_decomp (v : PotPair) :
    ∃ a b : PhysicalL2, v = realSlice a + Complex.I • realSlice b := by
  refine ⟨(1 / 2 : ℂ) • (v.1 + star v.2), (-Complex.I / 2) • (v.1 - star v.2), ?_⟩
  have h1 : Complex.I * (-Complex.I / 2) = 1 / 2 := by
    rw [show Complex.I * (-Complex.I / 2) = -(Complex.I * Complex.I) / 2 by ring, Complex.I_mul_I]
    ring
  have h2 : Complex.I * (Complex.I / 2) = -(1 / 2) := by
    rw [show Complex.I * (Complex.I / 2) = (Complex.I * Complex.I) / 2 by ring, Complex.I_mul_I]
    ring
  have hc : starRingEnd ℂ (-Complex.I / 2) = Complex.I / 2 := by
    rw [map_div₀, map_neg, Complex.conj_I, map_ofNat]
    ring
  have hc2 : starRingEnd ℂ (1 / 2 : ℂ) = 1 / 2 := by
    rw [map_div₀, map_one, map_ofNat]
  have hsub : ∀ f g : PhysicalL2, star (f - g) = star f - star g := fun f g => starLp.map_sub f g
  refine Prod.ext ?_ ?_
  · simp only [realSlice_apply, Prod.fst_add, Prod.smul_fst]
    rw [smul_smul, h1]
    module
  · simp only [realSlice_apply, Prod.snd_add, Prod.smul_snd]
    rw [star_smul_lp, star_smul_lp, star_add_lp, hsub, star_star, hc, hc2, smul_smul, h2]
    module

theorem fderiv_eq_zero_of_real_const (h : PotPair → ℂ) (u : PhysicalL2) (c : ℂ)
    (hd : DifferentiableAt ℂ h (realSlice u))
    (hc : ∀ᶠ w in 𝓝 u, h (realSlice w) = c) :
    fderiv ℂ h (realSlice u) = 0 := by
  have hreal : ∀ a : PhysicalL2, fderiv ℂ h (realSlice u) (realSlice a) = 0 := by
    intro a
    have h1 : HasFDerivAt (fun w : PhysicalL2 => h (realSlice w))
        ((fderiv ℂ h (realSlice u)).restrictScalars ℝ ∘L realSlice) u :=
      (hd.hasFDerivAt.restrictScalars ℝ).comp u realSlice.hasFDerivAt
    have h2 : HasFDerivAt (fun w : PhysicalL2 => h (realSlice w)) (0 : PhysicalL2 →L[ℝ] ℂ) u :=
      (hasFDerivAt_const c u).congr_of_eventuallyEq hc
    have h3 := h1.unique h2
    simpa using congrArg (fun L => L a) h3
  refine ContinuousLinearMap.ext fun v => ?_
  obtain ⟨a, b, rfl⟩ := exists_realSlice_decomp v
  rw [ContinuousLinearMap.zero_apply, map_add, map_smul, hreal a, hreal b, smul_zero, add_zero]

end
end G5031Sup2
end NlsGge.GKDefinitionDesign
