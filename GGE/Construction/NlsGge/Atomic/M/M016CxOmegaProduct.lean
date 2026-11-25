import Mathlib
import NlsGge.ThirdConsultation.G2.G2037Support2
import NlsGge.Atomic.M.M007

                                                                                                            
                                                                                                     
                                                                                                                     
                                                                                                               
                                                                                                       
                                                                                                          
                                                                                                                 
                                                                                                        
                                                                                       
                                                                                 
                                                                                                                 
                                                                                                                   
                                                                            
set_option autoImplicit false
open Set Filter Topology Metric SummationFilter
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.ThirdConsultation.M

theorem finitegap_pair_omega_eq_product
    (φ : PotPair) (hW : φ ∈ gkW) (S : Finset ℤ)
    (hS : ∀ n : ℤ, n ∈ S ↔
      NlsGge.GKDefinitionDesign.gap φ n ≠ 0)
    (z : ℂ) (hz : (φ, z) ∈ rootDomain38) :
    omega φ z = -Complex.I * ∏ n ∈ S,
      (lamDot φ n - z) /
        NlsGge.GKDefinitionDesign.standardRoot φ n z := by
  have hzg : z ∉ gapSegments38 φ := hz.2
  have hseg : ∀ k : ℤ, z ∉ segment ℝ (lamMinus φ k) (lamPlus φ k) :=
    fun k hk => hzg (Set.mem_iUnion.2 ⟨k, hk⟩)
  have hmul : Multipliable (fun n : ℤ => rootFactor38 n (φ, z)) (symmetricIcc ℤ) :=
    root_multipliable38 (φ, z) hz
  have hCne : canonRoot38 φ z ≠ 0 := canonRoot_ne_zero38 φ hW z hzg
  have hh1 : ∀ k : ℤ, k ∉ S →
      (lamDot φ k - z) / NlsGge.GKDefinitionDesign.standardRoot φ k z = 1 := by
    intro k hk
    have hgap0 : lamPlus φ k - lamMinus φ k = 0 := by
      by_contra hne
      exact hk ((hS k).2 hne)
    have hg2 : gamma2 φ k = 0 := by
      show gamma2N38 discC discR φ k = 0
      rw [gamma2_pair_gap38 discC discR isolating_selectors_admissible38 φ hW k, hgap0]
      norm_num
    have hlam : lamDot φ k = tauN φ k :=
      gamma2_zero_critical_eq_tau38 discC discR isolating_selectors_admissible38 φ hW k hg2
    have hsr : NlsGge.GKDefinitionDesign.standardRoot φ k z ≠ 0 := by
      rw [NlsGge.GKDefinitionDesign.g2037s1_std_eq]
      exact mul_ne_zero (a5RootFactor_ne_zero38 k (φ, z) hW (hseg k))
        (by exact_mod_cast Lib.piN_ne_zero k)
    have hstd : NlsGge.GKDefinitionDesign.standardRoot φ k z = tauN φ k - z := by
      unfold NlsGge.GKDefinitionDesign.standardRoot stdRoot38
      rw [hg2]
      simp
    have htne : tauN φ k - z ≠ 0 := by
      rw [← hstd]
      exact hsr
    rw [hlam, hstd]
    exact div_self htne
  have hfac : ∀ k : ℤ, (lamDot φ k - z) / (πn k : ℂ)
      = rootFactor38 k (φ, z)
        * ((lamDot φ k - z) / NlsGge.GKDefinitionDesign.standardRoot φ k z) := by
    intro k
    have hg0 : rootFactor38 k (φ, z) ≠ 0 := a5RootFactor_ne_zero38 k (φ, z) hW (hseg k)
    rw [NlsGge.GKDefinitionDesign.g2037s1_std_eq, mul_div_assoc', mul_div_mul_left _ _ hg0]
  have hsplit := NlsGge.GKDefinitionDesign.g2037s2_tprod_split
    (fun k => (lamDot φ k - z) / (πn k : ℂ))
    (fun k => rootFactor38 k (φ, z))
    (fun k => (lamDot φ k - z) / NlsGge.GKDefinitionDesign.standardRoot φ k z) S hfac hmul hh1
  try dsimp only at hsplit
  have hD := discrimDeriv_product φ z
  have hCne' : 2 * Complex.I * (∏'[symmetricIcc ℤ] k : ℤ, rootFactor38 k (φ, z)) ≠ 0 := by
    unfold canonRoot38 at hCne
    exact hCne
  unfold omega canonRoot38
  rw [hD, hsplit]
  exact NlsGge.GKDefinitionDesign.g2037s2_alg _ _ _ Complex.I_mul_I hCne'

end NlsGge.ThirdConsultation.M
