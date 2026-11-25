import Mathlib
import NlsGge.ThirdConsultation.PDE.Round14Action

                                                                                                                
                                                                                                                   
                                                                                                                 
                                      
                                                                                                                     
                                                                                                          
                                                                                                                     
                                                                                                                        
                                               
set_option autoImplicit false
open Set Filter Topology
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GKDefinitionDesign
namespace NlsGge.ThirdConsultation.PDE

theorem action_frequency_extension_independent
    (F G : WeightedActionSpace → ℝ) (I : PositiveActionSpace) (n : ℤ)
    (hF : LocalActionExtension F I) (hG : LocalActionExtension G I) :
  fderiv ℝ F I.val (lp.single 1 n (1 : ℝ)) =
    fderiv ℝ G I.val (lp.single 1 n (1 : ℝ)) := by
  obtain ⟨U, hU, hIU, hFa, hFeq⟩ := hF
  obtain ⟨V, hV, hIV, hGa, hGeq⟩ := hG
  set e : WeightedActionSpace := lp.single 1 n (1 : ℝ) with he
  set γ : ℝ → WeightedActionSpace := fun s => I.val + s • e with hγdef
  have hγ : HasDerivAt γ e 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add I.val
    rw [one_smul] at h
    exact h
  have hγ0 : γ 0 = I.val := by simp [hγdef]
  have hFd : HasDerivAt (F ∘ γ) (fderiv ℝ F I.val e) 0 :=
    (hFa I.val hIU).differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0 hγ hγ0.symm
  have hGd : HasDerivAt (G ∘ γ) (fderiv ℝ G I.val e) 0 :=
    (hGa I.val hIV).differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0 hγ hγ0.symm
  have hcont : Continuous γ := continuous_const.add (continuous_id.smul continuous_const)
  have hU' : γ ⁻¹' U ∈ 𝓝 (0 : ℝ) :=
    hcont.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hIU)
  have hV' : γ ⁻¹' V ∈ 𝓝 (0 : ℝ) :=
    hcont.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hV.mem_nhds hIV)
  have hev : (F ∘ γ) =ᶠ[𝓝[Ici 0] 0] (G ∘ γ) := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hU',
      mem_nhdsWithin_of_mem_nhds hV'] with s hs hsU hsV
    have hnn : ∀ m : ℤ, 0 ≤ (γ s) m := by
      intro m
      simp only [hγdef, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, he,
        lp.single_apply]
      refine add_nonneg (I.2 m) (mul_nonneg hs ?_)
      by_cases hm : m = n
      · subst hm; simp
      · simp [Pi.single_apply, hm]
    show F (γ s) = G (γ s)
    rw [hFeq ⟨γ s, hnn⟩ hsU, hGeq ⟨γ s, hnn⟩ hsV]
  have h1 := hFd.hasDerivWithinAt (s := Ici (0 : ℝ))
  have h2 : HasDerivWithinAt (F ∘ γ) (fderiv ℝ G I.val e) (Ici 0) 0 :=
    hGd.hasDerivWithinAt.congr_of_eventuallyEq hev (hev.eq_of_nhdsWithin (Set.mem_Ici.2 le_rfl))
  exact (uniqueDiffWithinAt_Ici 0).eq_deriv _ h1 h2

end NlsGge.ThirdConsultation.PDE
