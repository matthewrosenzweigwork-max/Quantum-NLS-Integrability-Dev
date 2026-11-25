import Mathlib
import NlsGge.Atomic.M.M010Support1
import NlsGge.Atomic.M.M012Support1
import NlsGge.Atomic.M.M016CanonRootBase
import NlsGge.Atomic.M.M016Density

                                                                                                  
                                                                                                        
                                                                                                         
                                                                                                                        
                                                                                                          
                                                                                                                  
                                                                                                                            
                                                                                                               
                                                        
                                                                                                               
                                                                                                                  

set_option autoImplicit false
open Set Filter Topology

namespace NlsGge.ThirdConsultation.M016ChartAux

/-- **Step 4, generic form** (Pro R16 §3.4): `H = (Δ+s)/2` satisfies `H' / H = Δ'/s = F'`, so `H e^{-F}` is constant
on the preconnected open set; the boundary normalization `F → 0, Δ → 2, s → 0` makes it `1`; then
`e^{F} = (Δ+s)/2`, `e^{-F} = (Δ-s)/2`, hence `2 cosh F = Δ`. -/
theorem cosh_identity_generic (C : Set ℂ) (hC : IsOpen C) (hpc : IsPreconnected C)
    (D s F D' s' : ℂ → ℂ)
    (hD : ∀ z ∈ C, HasDerivAt D (D' z) z) (hs : ∀ z ∈ C, HasDerivAt s (s' z) z)
    (hss : ∀ z ∈ C, s z ^ 2 = D z ^ 2 - 4) (hs0 : ∀ z ∈ C, s z ≠ 0)
    (hsd : ∀ z ∈ C, s z * s' z = D z * D' z)
    (hF : ∀ z ∈ C, HasDerivAt F (D' z / s z) z)
    (e : ℂ) (hne : (𝓝[C] e).NeBot) (hFe : Tendsto F (𝓝[C] e) (𝓝 0))
    (hDe : Tendsto D (𝓝[C] e) (𝓝 2)) (hse : Tendsto s (𝓝[C] e) (𝓝 0)) :
    ∀ z ∈ C, 2 * Complex.cosh (F z) = D z := by
  set Φ : ℂ → ℂ := fun z => (D z + s z) / 2 * Complex.exp (-F z) with hΦ
  have hΦd : ∀ z ∈ C, HasDerivAt Φ 0 z := by
    intro z hz
    have h := (((hD z hz).add (hs z hz)).div_const 2).mul ((hF z hz).neg.cexp)
    convert h using 1
    have h0 := hs0 z hz
    have hk := hsd z hz
    simp only [Pi.add_apply]
    field_simp
    linear_combination (-(Complex.exp (-F z))) * hk
  obtain ⟨a, ha⟩ := hC.exists_is_const_of_deriv_eq_zero hpc
    (fun z hz => (hΦd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hΦd z hz).deriv)
  have hlim : Tendsto Φ (𝓝[C] e) (𝓝 ((2 + 0) / 2 * Complex.exp (-0))) :=
    ((hDe.add hse).div_const 2).mul ((hFe.neg).cexp)
  have hlima : Tendsto Φ (𝓝[C] e) (𝓝 a) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun z hz => (ha z hz).symm)
  have ha1 : a = 1 := by
    have := tendsto_nhds_unique hlima hlim
    rw [this]; simp
  intro z hz
  have hA : (D z + s z) / 2 * Complex.exp (-F z) = 1 := by rw [← ha1]; exact ha z hz
  have hB : Complex.exp (F z) * Complex.exp (-F z) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hC' := hss z hz
  have hE : Complex.exp (F z) = (D z + s z) / 2 := by
    linear_combination (-(Complex.exp (F z))) * hA + ((D z + s z) / 2) * hB
  have hE' : Complex.exp (-F z) = (D z - s z) / 2 := by
    linear_combination (Complex.exp (-F z) / 4) * hC' + ((D z - s z) / 2) * hA
  rw [Complex.two_cosh, hE, hE']
  ring

end NlsGge.ThirdConsultation.M016ChartAux

namespace NlsGge.ThirdConsultation.M

open NlsGge.Pilot NlsGge.GK38 NlsGge.ThirdConsultation.MPrimitive NlsGge.ThirdConsultation.M016ChartAux

theorem primitive_discriminant_identity_of (φ : PotPair) (hW : φ ∈ gkW)
    (hpc : IsPreconnected (cutFreeFiber φ))
    (hΔ : discrim φ (lamMinus φ 0) = 2)
    (hdense : ∀ z ∈ endpointClosureFiber φ, (𝓝[cutFreeFiber φ] z).NeBot)
    (z : ℂ) (hz : z ∈ endpointClosureFiber φ) :
    2 * Complex.cosh (primitive ⟨(φ, z), ⟨hW, hz⟩⟩) = discrim φ z := by
  obtain ⟨P, L, hP, hPL, hval⟩ := symmetric_value_data_lim φ hW
  set k : ℂ := L (lamMinus φ 0)
  have hCo := cutFreeFiber_isOpen φ hW
  have hLP : ∀ w ∈ cutFreeFiber φ, L w = P w := fun w hw => by
    have h1 := hPL w (Or.inl hw)
    rw [nhdsWithin_eq_nhds.mpr (hCo.mem_nhds hw)] at h1
    exact tendsto_nhds_unique h1 (hP w hw).continuousAt.tendsto
  have he : lamMinus φ 0 ∈ endpointClosureFiber φ := lower_endpoint_mem φ 0
  have hcut : ∀ w ∈ cutFreeFiber φ, 2 * Complex.cosh (L w - k) = discrim φ w :=
    cosh_identity_generic (cutFreeFiber φ) hCo hpc (discrim φ) (canonRoot38 φ) (fun w => L w - k)
      (deriv (discrim φ)) (deriv (canonRoot38 φ))
      (fun w _ => ((analyticOnNhd_discrim_z φ) w (mem_univ w)).differentiableAt.hasDerivAt)
      (fun w hw => (NlsGge.ThirdConsultation.M012Aux.canonRoot_mul_deriv hW hw).1)
      (fun w hw => (canonRoot_sq38 φ hW w hw).trans (perChar_eq φ w))
      (fun w hw => canonRoot_ne_zero38 φ hW w hw)
      (fun w hw => (NlsGge.ThirdConsultation.M012Aux.canonRoot_mul_deriv hW hw).2)
      (fun w hw => by
        have h := (hP w hw).sub_const k
        refine h.congr_of_eventuallyEq ?_
        filter_upwards [hCo.mem_nhds hw] with v hv
        rw [hLP v hv])
      (lamMinus φ 0) (hdense _ he)
      (by
        have h := (hPL _ he).sub_const k
        rw [sub_self] at h
        exact h.congr' (eventually_nhdsWithin_of_forall fun w hw => by
          show P w - k = L w - k
          rw [hLP w hw]))
      (by
        have h := ((analyticOnNhd_discrim_z φ) (lamMinus φ 0) (mem_univ _)).continuousAt.tendsto
        rw [hΔ] at h
        exact h.mono_left nhdsWithin_le_nhds)
      (canonRoot_tendsto_base φ hW)
  have hne := hdense z hz
  have h1 : Tendsto (fun w => 2 * Complex.cosh (P w - k)) (𝓝[cutFreeFiber φ] z)
      (𝓝 (2 * Complex.cosh (L z - k))) :=
    ((Complex.continuous_cosh.tendsto _).comp ((hPL z hz).sub_const k)).const_mul 2
  have h2 : Tendsto (fun w => 2 * Complex.cosh (P w - k)) (𝓝[cutFreeFiber φ] z) (𝓝 (discrim φ z)) := by
    refine (((analyticOnNhd_discrim_z φ) z (mem_univ z)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds).congr' (eventually_nhdsWithin_of_forall fun w hw => ?_)
    show NlsGge.GK38.discrim φ w = 2 * Complex.cosh (P w - k)
    rw [← hLP w hw, hcut w hw]
  have hprim : primitive ⟨(φ, z), ⟨hW, hz⟩⟩ = L z - k := hval z hz
  rw [hprim]
  exact tendsto_nhds_unique h1 h2

/-- Step 4 with the density hypothesis discharged (`M016Density`); remaining interfaces: (S4a), (S4c). -/
theorem primitive_discriminant_identity_of_S4 (φ : PotPair) (hW : φ ∈ gkW)
    (hpc : IsPreconnected (cutFreeFiber φ))
    (hΔ : discrim φ (lamMinus φ 0) = 2)
    (z : ℂ) (hz : z ∈ endpointClosureFiber φ) :
    2 * Complex.cosh (primitive ⟨(φ, z), ⟨hW, hz⟩⟩) = discrim φ z :=
  primitive_discriminant_identity_of φ hW hpc hΔ (fun w hw => cutFree_nhdsWithin_neBot φ hW w hw) z hz

end NlsGge.ThirdConsultation.M
