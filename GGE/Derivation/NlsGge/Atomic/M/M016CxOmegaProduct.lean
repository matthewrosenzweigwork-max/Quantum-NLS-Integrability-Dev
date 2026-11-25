import Mathlib
import NlsGge.ThirdConsultation.G2.G2037Support2
import NlsGge.Atomic.M.M007

/- M016CX OMEGA PRODUCT PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Proposed target
   NlsGge/Atomic/M/M016CxOmegaProduct.lean. Support for the COMPLEX M-016 head, round-16 §1.1 support
   `finitegap_pair_omega_eq_product` (PRO_DEFINITION_RESPONSE_FP80_16.md L67-79; BINDING_INDEX_FP80_16 support entry,
   namespace NlsGge.ThirdConsultation.M); head VERBATIM. Proof = round-16 §3 step 1, i.e. the landed real proof
   G2037Support2.g2037s2_deriv_eq_fgd with the real restriction removed: collapse is read directly from
   `gap φ k = lamPlus - lamMinus = 0` (G2046), then gamma2_pair_gap38 / gamma2_zero_critical_eq_tau38 give
   lamDot = tauN and standardRoot = tauN - z, so every omitted ratio is 1; nonvanishing of the standard root from
   g2037s1_std_eq + a5RootFactor_ne_zero38 (generic). Reuses landed g2037s1_std_eq, g2037s2_tprod_split,
   g2037s2_alg (generic in complex scalars) and discrimDeriv_product; `omega` is M007's
   `deriv (discrim φ) z / canonRoot38 φ z`. No new definition, no new hypothesis.
   Own imports: G2037Support2 (-> Support1 -> G2046 gap, G2019 standardRoot, GK38 product/root anchors) and M007.
   Needs ROOT MAIN PROBE (G2037Support1/2, G2046, M007 absent from mirror); the proof text is lane-checked verbatim
   in M016CX_OMEGA_SELFTEST01 with verbatim copies of those landed items. -/
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
