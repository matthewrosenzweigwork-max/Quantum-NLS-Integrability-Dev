import Mathlib
import NlsGge.GK38.GradFundamentalDefs

                                                                                                                             
                                                                                                                            
                                                                                                                       
set_option autoImplicit false

open Set Filter Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g5003_chain_abs {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g : E × ℂ → ℂ) (φ : E) (m : E → ℂ)
    (hg : DifferentiableAt ℂ g (φ, m φ)) (hm : DifferentiableAt ℂ m φ) :
    HasFDerivAt (fun ψ : E => g (ψ, m ψ))
      (fderiv ℂ (fun ψ : E => g (ψ, m φ)) φ +
        deriv (fun z : ℂ => g (φ, z)) (m φ) • fderiv ℂ m φ) φ := by
  have hgd : HasFDerivAt g (fderiv ℂ g (φ, m φ)) (φ, m φ) := hg.hasFDerivAt
  have h1 : HasFDerivAt (fun ψ : E => (ψ, m ψ))
      ((ContinuousLinearMap.id ℂ E).prod (fderiv ℂ m φ)) φ :=
    (hasFDerivAt_id φ).prodMk hm.hasFDerivAt
  have hc : HasFDerivAt (fun ψ : E => g (ψ, m ψ))
      ((fderiv ℂ g (φ, m φ)).comp ((ContinuousLinearMap.id ℂ E).prod (fderiv ℂ m φ))) φ :=
    HasFDerivAt.comp (g := g) φ hgd h1
  have h2 : HasFDerivAt (fun ψ : E => g (ψ, m φ))
      ((fderiv ℂ g (φ, m φ)).comp ((ContinuousLinearMap.id ℂ E).prod 0)) φ :=
    HasFDerivAt.comp (g := g) φ hgd ((hasFDerivAt_id φ).prodMk (hasFDerivAt_const (m φ) φ))
  have h3 : HasFDerivAt (fun z : ℂ => g (φ, z))
      ((fderiv ℂ g (φ, m φ)).comp ((0 : ℂ →L[ℂ] E).prod (ContinuousLinearMap.id ℂ ℂ))) (m φ) :=
    HasFDerivAt.comp (g := g) (m φ) hgd ((hasFDerivAt_const φ (m φ)).prodMk (hasFDerivAt_id (m φ)))
  have hderiv : deriv (fun z : ℂ => g (φ, z)) (m φ) = fderiv ℂ g (φ, m φ) ((0 : E), (1 : ℂ)) := by
    have := h3.hasDerivAt.deriv
    simpa using this
  have heq : (fderiv ℂ g (φ, m φ)).comp ((ContinuousLinearMap.id ℂ E).prod (fderiv ℂ m φ)) =
      fderiv ℂ (fun ψ : E => g (ψ, m φ)) φ +
        deriv (fun z : ℂ => g (φ, z)) (m φ) • fderiv ℂ m φ := by
    rw [h2.fderiv, hderiv]
    refine ContinuousLinearMap.ext fun x => ?_
    have hsplit : (x, fderiv ℂ m φ x) =
        ((x, (0 : ℂ)) : E × ℂ) + (fderiv ℂ m φ x) • (((0 : E), (1 : ℂ)) : E × ℂ) := by
      ext <;> simp
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.zero_apply]
    rw [hsplit, map_add, map_smul, smul_eq_mul, smul_eq_mul, mul_comm]
  exact hc.congr_fderiv heq

theorem g5003_chain (φ : PotPair) (m : PotPair → ℂ) (hm : DifferentiableAt ℂ m φ) :
    HasFDerivAt (fun ψ : PotPair => antiDiscrim ψ (m ψ))
      (fderiv ℂ (fun ψ : PotPair => antiDiscrim ψ (m φ)) φ +
        deriv (antiDiscrim φ) (m φ) • fderiv ℂ m φ) φ :=
  g5003_chain_abs (fun p : PotPair × ℂ => antiDiscrim p.1 p.2) φ m
    ((analyticOnNhd_antiDiscrim (φ, m φ) (Set.mem_univ _)).differentiableAt) hm

end
end NlsGge.GKDefinitionDesign
