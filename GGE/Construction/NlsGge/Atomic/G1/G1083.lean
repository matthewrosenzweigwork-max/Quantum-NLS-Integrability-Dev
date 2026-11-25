import Mathlib
import NlsGge.Atomic.G1.G1083Host
import NlsGge.Atomic.G1.G1083Sup2
import NlsGge.Atomic.G1.G1082Sup5
import NlsGge.Atomic.G1.G1082Sup6
import NlsGge.GK38.RealTypeMultiplicityRealDeriv

                                                                                                                                    
                                                                              
                                                                                                                                         
                                                                                                                                            
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GKDefinitionDesign

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem isospectral_trans' {u v w : PhysicalL2} (h1 : isospectral u v) (h2 : isospectral v w) :
    isospectral u w := fun z => (h2 z).trans (h1 z)

theorem gapCircle_of_isospectral {u v : PhysicalL2} (h : isospectral u v) (n : ℤ) :
    gapCircle v n = gapCircle u n := by
  ext p
  simp only [gapCircle, Set.mem_setOf_eq, isospectral_gapLower_eq h n, isospectral_gapUpper_eq h n,
    show ∀ z, discrim (realSlice v) z = discrim (realSlice u) z from h]

theorem gapCircle_collapsed_singleton (u : PhysicalL2) (n : ℤ)
    (hc : ¬ actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n) (p : ℝ × ℝ)
    (hp : p ∈ gapCircle u n) : p = signedDirichletData u n := by
  push Not at hc
  have hm := gkMu_mem_gap38 u n
  have hp1 : p.1 = gkMu u n := by linarith [hp.1, hp.2.1, hm.1, hm.2]
  have hv := gap_discrim_endpoint_values38 u n
  have hc2 := real_cos_int_mul_pi_sq_E02_38 n
  have hlo : (discrim (realSlice u) (actualGapLowerAllE02_38 u n : ℂ)).re ^ 2 - 4 = 0 := by
    rw [hv.1, show (2 : ℂ) * (Real.cos ((n : ℝ) * Real.pi) : ℂ) =
      ((2 * Real.cos ((n : ℝ) * Real.pi) : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
    nlinarith [hc2]
  have hg : gkMu u n = actualGapLowerAllE02_38 u n := by linarith [hm.1, hm.2]
  have hN : (discrim (realSlice u) (gkMu u n : ℂ)).re ^ 2 - 4 = 0 := by rw [hg]; exact hlo
  have h1 : p.2 ^ 2 = 0 := by have := hp.2.2; rw [hp1] at this; linarith
  have h2 : deltaMu u n ^ 2 = 0 := by rw [← deltaMu_squared38]; exact hN
  refine Prod.ext hp1 ?_
  show p.2 = deltaMu u n
  rw [pow_eq_zero_iff (by norm_num) |>.mp h1, pow_eq_zero_iff (by norm_num) |>.mp h2]

theorem exists_flow_hit (n : ℤ) (u : PhysicalL2) (p : ℝ × ℝ) (hp : p ∈ gapCircle u n) :
    ∃ t : ℝ, signedDirichletData (singleGapFlow n t u) n = p := by
  by_cases ho : actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n
  · exact NlsGge.Atomic.G1083Sup2.orbit_covers_gapCircle n u ho p hp
  · exact ⟨0, by rw [NlsGge.Atomic.G1081Sup5.singleGapFlow_zero, gapCircle_collapsed_singleton u n ho p hp]⟩

theorem G1_083 (u : PhysicalL2) (F : Finset ℤ)
    (p : ℤ → ℝ × ℝ) (hp : ∀ n ∈ F, p n ∈ gapCircle u n) :
    ∃ v : PhysicalL2, v ∈ isospectralSet u ∧
      (∀ n ∈ F, signedDirichletData v n = p n) ∧
      (∀ n : ℤ, n ∉ F → signedDirichletData v n = signedDirichletData u n) := by
  induction F using Finset.induction_on with
  | empty => exact ⟨u, fun z => rfl, by simp, fun n _ => rfl⟩
  | insert a F ha ih =>
    obtain ⟨v1, hv1, hv1F, hv1o⟩ := ih (fun n hn => hp n (Finset.mem_insert_of_mem hn))
    have hpa : p a ∈ gapCircle v1 a := by
      rw [gapCircle_of_isospectral hv1 a]; exact hp a (Finset.mem_insert_self a F)
    obtain ⟨t, ht⟩ := exists_flow_hit a v1 (p a) hpa
    refine ⟨singleGapFlow a t v1, isospectral_trans' hv1 (NlsGge.Atomic.G1081Sup6.singleGapFlow_isospectral a t v1),
      fun n hn => ?_, fun n hn => ?_⟩
    · by_cases hna : n = a
      · subst hna; exact ht
      · have hnF : n ∈ F := (Finset.mem_insert.1 hn).resolve_left hna
        rw [show signedDirichletData (singleGapFlow a t v1) n = signedDirichletData v1 n from
          NlsGge.Atomic.G1082Sup6.signed_data_flow_other a n hna v1 t]
        exact hv1F n hnF
    · have hna : n ≠ a := fun e => hn (e ▸ Finset.mem_insert_self _ _)
      have hnF : n ∉ F := fun h => hn (Finset.mem_insert_of_mem h)
      rw [show signedDirichletData (singleGapFlow a t v1) n = signedDirichletData v1 n from
        NlsGge.Atomic.G1082Sup6.signed_data_flow_other a n hna v1 t]
      exact hv1o n hnF

end
end NlsGge.GKDefinitionDesign
