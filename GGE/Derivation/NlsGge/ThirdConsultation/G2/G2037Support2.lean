import NlsGge.GK38.ProductRepr
import NlsGge.GK38.StdRootBranchesConvergence
import NlsGge.GK38.StdRootBranchesProducts
import NlsGge.GK38.TauGammaContourGlue
import NlsGge.GK38.TauGammaCriticalFactor
import NlsGge.GK38.RealTypeSpectrum
import NlsGge.GK38.XiSqOmittedRoot
import NlsGge.ThirdConsultation.KO.Basic
import NlsGge.ThirdConsultation.G2.G2037Host
import NlsGge.ThirdConsultation.G2.G2037Support1

/- G2-037 SUPPORT S2 (proof development, AUTHOR; not self-reviewed; SUPPORTING, not the packet).
   Proves conjunct (3) of G2_037 (STATEMENTS/G2.md):
     deriv (discrim (realSlice u)) z / canonRoot38 (realSlice u) z = finiteGapDifferential u S z
   on rootDomain38, for S = {n | lower n ≠ upper n}. Route: discrimDeriv_product and the
   symmetric product of canonRoot38 are split factor by factor; a non-cut factor is 1 because a
   collapsed gap has gamma2 = 0 and lamDot = tauN, so the standard root equals tau - z.
   Also records the partial bundle `g2037_partial_conjuncts` (conjuncts 1, 2, 3, 4a, 4b for n ∉ S);
   it is NOT the head: (4c) for n ∈ S and (5) remain open. -/
set_option autoImplicit false
-- proof development repair (REVIEW_G2037SUPPORT_01 F3): explicit KO.Basic import added; nothing else changed.

open Set Filter Topology Metric MeasureTheory SummationFilter
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-- Splitting a symmetric product whose second factor is finitely supported. -/
theorem g2037s2_tprod_split (f g h : ℤ → ℂ) (S : Finset ℤ) (hfgh : ∀ k, f k = g k * h k)
    (hg : Multipliable g (symmetricIcc ℤ)) (hh1 : ∀ k, k ∉ S → h k = 1) :
    ∏'[symmetricIcc ℤ] k, f k = (∏'[symmetricIcc ℤ] k, g k) * ∏ k ∈ S, h k := by
  have hmh : Multipliable h (symmetricIcc ℤ) := multipliable_of_ne_finset_one (s := S) hh1
  have hf : ∏'[symmetricIcc ℤ] k, f k = ∏'[symmetricIcc ℤ] k, (g k * h k) := tprod_congr hfgh
  rw [hf, hg.tprod_mul hmh, tprod_eq_prod hh1]

/-- Field algebra for the final ratio. -/
theorem g2037s2_alg (P Q I : ℂ) (hI : I * I = -1) (hP : 2 * I * P ≠ 0) :
    2 * (P * Q) / (2 * I * P) = -I * Q := by
  rw [div_eq_iff hP]
  linear_combination (2 * P * Q) * hI

/-- Conjunct (3): the discriminant-derivative quotient equals the finite product on rootDomain38. -/
theorem g2037s2_deriv_eq_fgd (u : PhysicalL2) (S : Finset ℤ)
    (hS : ∀ n : ℤ, n ∈ S ↔ actualGapLowerAllE02_38 u n ≠ actualGapUpperAllE02_38 u n)
    (z : ℂ) (hz : (realSlice u, z) ∈ rootDomain38) :
    deriv (discrim (realSlice u)) z / canonRoot38 (realSlice u) z
      = finiteGapDifferential u S z := by
  have hφ : realSlice u ∈ gkW := hz.1
  have hzg : z ∉ gapSegments38 (realSlice u) := hz.2
  have hmul : Multipliable (fun n : ℤ => rootFactor38 n (realSlice u, z)) (symmetricIcc ℤ) :=
    root_multipliable38 (realSlice u, z) hz
  have hCne : canonRoot38 (realSlice u) z ≠ 0 := canonRoot_ne_zero38 (realSlice u) hφ z hzg
  have hh1 : ∀ k : ℤ, k ∉ S →
      (lamDot (realSlice u) k - z) / standardRoot (realSlice u) k z = 1 := by
    intro k hk
    have hcol : actualGapLowerAllE02_38 u k = actualGapUpperAllE02_38 u k := by
      by_contra hne
      exact hk ((hS k).2 hne)
    have hlp : lamMinus (realSlice u) k = lamPlus (realSlice u) k := by
      rw [(lamPlus_real u k).1, (lamPlus_real u k).2, hcol]
    have hg2 : gamma2 (realSlice u) k = 0 := by
      show gamma2N38 discC discR (realSlice u) k = 0
      rw [gamma2_pair_gap38 discC discR isolating_selectors_admissible38 (realSlice u) hφ k,
        ← hlp, sub_self]
      norm_num
    have hlam : lamDot (realSlice u) k = tauN (realSlice u) k :=
      gamma2_zero_critical_eq_tau38 discC discR isolating_selectors_admissible38
        (realSlice u) hφ k hg2
    have hne : z ∉ segment ℝ (lamMinus (realSlice u) k) (lamPlus (realSlice u) k) := by
      intro hseg
      exact hzg (Set.mem_iUnion.2 ⟨k, hseg⟩)
    have hsr : standardRoot (realSlice u) k z ≠ 0 :=
      (g2037s1_factor (realSlice u) hφ k z hne).2
    have hstd : standardRoot (realSlice u) k z = tauN (realSlice u) k - z := by
      unfold standardRoot stdRoot38
      rw [hg2]
      simp
    have htne : tauN (realSlice u) k - z ≠ 0 := by
      rw [← hstd]
      exact hsr
    rw [hlam, hstd]
    exact div_self htne
  have hfac : ∀ k : ℤ, (lamDot (realSlice u) k - z) / (πn k : ℂ)
      = rootFactor38 k (realSlice u, z)
        * ((lamDot (realSlice u) k - z) / standardRoot (realSlice u) k z) := by
    intro k
    have hne : z ∉ segment ℝ (lamMinus (realSlice u) k) (lamPlus (realSlice u) k) :=
      fun hseg => hzg (Set.mem_iUnion.2 ⟨k, hseg⟩)
    have hg0 : rootFactor38 k (realSlice u, z) ≠ 0 :=
      a5RootFactor_ne_zero38 k (realSlice u, z) hφ hne
    have hsr : standardRoot (realSlice u) k z
        = rootFactor38 k (realSlice u, z) * (Lib.piN k : ℂ) :=
      g2037s1_std_eq (realSlice u) k z
    rw [hsr, mul_div_assoc', mul_div_mul_left _ _ hg0]
  have hsplit := g2037s2_tprod_split
    (fun k => (lamDot (realSlice u) k - z) / (πn k : ℂ))
    (fun k => rootFactor38 k (realSlice u, z))
    (fun k => (lamDot (realSlice u) k - z) / standardRoot (realSlice u) k z) S hfac hmul hh1
  try dsimp only at hsplit
  have hD := discrimDeriv_product (realSlice u) z
  have hCne' : 2 * Complex.I * (∏'[symmetricIcc ℤ] k : ℤ, rootFactor38 k (realSlice u, z)) ≠ 0 := by
    unfold canonRoot38 at hCne
    exact hCne
  unfold canonRoot38 finiteGapDifferential
  rw [hD, hsplit]
  exact g2037s2_alg _ _ _ Complex.I_mul_I hCne'

/-- PARTIAL bundle (supporting, not the head): conjuncts (1), (2), (3), (4a) and (4b for n ∉ S). -/
theorem g2037_partial_conjuncts (u : PhysicalL2) (hfg : NlsGge.ThirdConsultation.finiteGap u) :
    ∃ S : Finset ℤ,
      (∀ n : ℤ, n ∈ S ↔ actualGapLowerAllE02_38 u n ≠ actualGapUpperAllE02_38 u n) ∧
      AnalyticOnNhd ℂ (finiteGapDifferential u S) (finiteGapCuts u S)ᶜ ∧
      (∀ z : ℂ, (realSlice u, z) ∈ rootDomain38 →
        deriv (discrim (realSlice u)) z / canonRoot38 (realSlice u) z
          = finiteGapDifferential u S z) ∧
      (∀ (C : ℤ → ℂ) (R : ℤ → ℝ), IsolatingFamily38 (realSlice u) C R →
        ∀ n : ℤ, CircleIntegrable (finiteGapDifferential u S) (C n) (R n) ∧
          (n ∉ S → circleIntegral (finiteGapDifferential u S) (C n) (R n) = 0)) := by
  obtain ⟨S, hS⟩ := g2037s1_finite_mem u hfg
  exact ⟨S, hS, g2037s1_fgd_analyticOn u S,
    fun z hz => g2037s2_deriv_eq_fgd u S hS z hz,
    fun C R hCR n => ⟨g2037s1_circleIntegrable u S C R hCR n,
      fun hn => g2037s1_zero_period_off u S C R hCR n hn⟩⟩

end
end NlsGge.GKDefinitionDesign
