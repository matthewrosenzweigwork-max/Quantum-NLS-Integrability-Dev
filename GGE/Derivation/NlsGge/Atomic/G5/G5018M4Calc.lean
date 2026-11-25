import Mathlib

/- G5-018 M4 SUPPORT `G5018M4Calc` (proof development, AUTHOR; not self-reviewed). Target NlsGge/Atomic/G5/G5018M4Calc.lean.
   Pure calculus lemmas (no spectral input): (1) derivative along a line of a joint function F(psi, z) when the z-argument moves
   and the phi-partial in direction v vanishes; (2) differential of an analytic function with a locally-algebraic relation. -/
set_option autoImplicit false

open Set Filter Topology

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g5018m4_joint_line_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : E × ℂ → ℂ} {φ0 v : E} {z0 : ℂ} {Z : ℂ → ℂ} {Z' : ℂ}
    (hF : DifferentiableAt ℂ F (φ0, z0)) (hZ : HasDerivAt Z Z' 0) (hZ0 : Z 0 = z0)
    (hφ : fderiv ℂ (fun ψ : E => F (ψ, z0)) φ0 v = 0) :
    HasDerivAt (fun w : ℂ => F (φ0 + w • v, Z w))
      (Z' * deriv (fun z : ℂ => F (φ0, z)) z0) 0 := by
  have hc : HasDerivAt (fun w : ℂ => (φ0 + w • v, Z w)) (v, Z') 0 := by
    have h1 : HasDerivAt (fun w : ℂ => φ0 + w • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add φ0
    exact h1.prodMk hZ
  have hF' : HasFDerivAt F (fderiv ℂ F (φ0, z0)) ((fun w : ℂ => (φ0 + w • v, Z w)) 0) := by
    simpa [hZ0] using hF.hasFDerivAt
  have hD := hF'.comp_hasDerivAt (0 : ℂ) hc
  have hsplit : fderiv ℂ F (φ0, z0) (v, Z') =
      fderiv ℂ F (φ0, z0) (v, 0) + Z' * deriv (fun z : ℂ => F (φ0, z)) z0 := by
    have hz : deriv (fun z : ℂ => F (φ0, z)) z0 = fderiv ℂ F (φ0, z0) (0, 1) := by
      have hi : HasDerivAt (fun z : ℂ => (φ0, z)) (0, 1) z0 :=
        (hasDerivAt_const z0 φ0).prodMk (hasDerivAt_id z0)
      exact ((hF.hasFDerivAt).comp_hasDerivAt z0 hi).deriv
    have e : ((v, Z') : E × ℂ) = (v, 0) + Z' • ((0, 1) : E × ℂ) := by
      ext <;> simp
    rw [e, map_add, map_smul, hz, smul_eq_mul]
  have hpart : fderiv ℂ F (φ0, z0) (v, 0) = 0 := by
    have hc2 : HasFDerivAt (fun ψ : E => (ψ, z0))
        ((ContinuousLinearMap.id ℂ E).prod (0 : E →L[ℂ] ℂ)) φ0 :=
      (hasFDerivAt_id φ0).prodMk (hasFDerivAt_const z0 φ0)
    have h2 := hF.hasFDerivAt.comp φ0 hc2
    have h3 : fderiv ℂ (fun ψ : E => F (ψ, z0)) φ0 =
        (fderiv ℂ F (φ0, z0)).comp ((ContinuousLinearMap.id ℂ E).prod (0 : E →L[ℂ] ℂ)) :=
      h2.fderiv
    have := congrArg (fun T => T v) h3
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply] at this
    rw [← this]
    exact hφ
  have hD' : HasDerivAt (fun w : ℂ => F (φ0 + w • v, Z w))
      (fderiv ℂ F (φ0, z0) (v, Z')) 0 := hD
  rw [hsplit, hpart, zero_add] at hD'
  exact hD'

end
end NlsGge.GKDefinitionDesign
