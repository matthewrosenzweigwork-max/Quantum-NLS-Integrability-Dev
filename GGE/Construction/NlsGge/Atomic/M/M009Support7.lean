import Mathlib
import NlsGge.Atomic.M.M009Host
import NlsGge.Atomic.M.M009Support2
import NlsGge.Atomic.M.M009Support3
import NlsGge.Atomic.M.M009Support4
import NlsGge.Atomic.M.M009Support5
import NlsGge.Atomic.M.M009Support6

                                                                                                                     
                                                                                       
                                                                                                                        
                                                                           
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology BigOperators
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.MPrimitive
noncomputable section

theorem baseEndpoint_false (φ : PotPair) : baseEndpoint φ false = lamMinus φ 0 := by
  simp [baseEndpoint]

theorem baseEndpoint_true (φ : PotPair) : baseEndpoint φ true = lamPlus φ 0 := by
  simp [baseEndpoint]

theorem symmetric_value_data (φ : PotPair) (hφ : φ ∈ gkW) :
    ∃ (P L : ℂ → ℂ),
      (∀ z ∈ cutFreeFiber φ, HasDerivAt P (MContour.omega φ z) z) ∧
      (∀ z ∈ cutFreeFiber φ, L z = P z) ∧
      L (lamMinus φ 0) = L (lamPlus φ 0) ∧
      (∀ z ∈ endpointClosureFiber φ,
        HasSymmetricPrimitiveValue φ z (L z - L (lamMinus φ 0)) ∧
        (∀ (A : ℂ), HasSymmetricPrimitiveValue φ z A → A = L z - L (lamMinus φ 0)) ∧
        ∀ (upper : Bool) (m : ℕ) (c : Fin (m + 1) → ℝ → ℂ),
          AdmissiblePrimitiveChain φ (baseEndpoint φ upper) z m c →
          MContour.HasFiniteChainIntegral φ m c (L z - L (lamMinus φ 0))) := by
  obtain ⟨P, hP⟩ := fiber_omega_primitive φ hφ
  obtain ⟨L, hLspec, hLchain⟩ := fiber_primitive_chain_values φ hφ hP
  have hbase : L (lamMinus φ 0) = L (lamPlus φ 0) :=
    fiber_primitive_gap_values_eq φ hφ hP 0 (hLspec _ (lower_endpoint_mem φ 0))
      (hLspec _ (upper_endpoint_mem φ 0))
  have hLP : ∀ z ∈ cutFreeFiber φ, L z = P z := by
    intro z hz
    haveI := fiber_neBot φ hφ (Or.inl hz : z ∈ endpointClosureFiber φ)
    exact tendsto_nhds_unique (hLspec z (Or.inl hz))
      ((hP z hz).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  -- value of every base-endpoint chain
  have hval : ∀ (z : ℂ), z ∈ endpointClosureFiber φ → ∀ (upper : Bool) (A : ℂ),
      HasBaseEndpointIntegral φ upper z A → A = L z - L (lamMinus φ 0) := by
    intro z hz upper A ⟨m, p, hp, hA⟩
    have hbe : baseEndpoint φ upper ∈ endpointClosureFiber φ := by
      cases upper
      · rw [baseEndpoint_false]; exact lower_endpoint_mem φ 0
      · rw [baseEndpoint_true]; exact upper_endpoint_mem φ 0
    have h := hLchain _ _ hbe hz m p hp
    rw [finite_chain_integral_unique φ m p A _ hA h]
    cases upper
    · rw [baseEndpoint_false]
    · rw [baseEndpoint_true, hbase]
  have hbe : ∀ upper : Bool, baseEndpoint φ upper ∈ endpointClosureFiber φ := by
    intro upper
    cases upper
    · rw [baseEndpoint_false]; exact lower_endpoint_mem φ 0
    · rw [baseEndpoint_true]; exact upper_endpoint_mem φ 0
  have hchain : ∀ (z : ℂ), z ∈ endpointClosureFiber φ → ∀ (upper : Bool) (m : ℕ)
      (c : Fin (m + 1) → ℝ → ℂ), AdmissiblePrimitiveChain φ (baseEndpoint φ upper) z m c →
      MContour.HasFiniteChainIntegral φ m c (L z - L (lamMinus φ 0)) := by
    intro z hz upper m c hc
    have h := hLchain _ _ (hbe upper) hz m c hc
    cases upper
    · rw [baseEndpoint_false] at h; exact h
    · rw [baseEndpoint_true, ← hbase] at h; exact h
  have hex : ∀ (z : ℂ), z ∈ endpointClosureFiber φ → ∀ (upper : Bool),
      HasBaseEndpointIntegral φ upper z (L z - L (lamMinus φ 0)) := by
    intro z hz upper
    obtain ⟨m, p, hp⟩ := exists_admissible_chain φ hφ (hbe upper) hz
    exact ⟨m, p, hp, hchain z hz upper m p hp⟩
  refine ⟨P, L, hP, hLP, hbase, fun z hz => ⟨?_, ?_, hchain z hz⟩⟩
  · refine ⟨hφ, hz, L z - L (lamMinus φ 0), L z - L (lamMinus φ 0), hex z hz false, hex z hz true, ?_⟩
    ring
  · rintro A ⟨-, -, Am, Ap, hAm, hAp, rfl⟩
    rw [hval z hz false Am hAm, hval z hz true Ap hAp]
    ring

/-- Pro round 13 section 11 Stage 1 (head verbatim). -/
theorem symmetric_primitive_exists_unique (p : PrimitivePoint) :
  ∃! A : ℂ, HasSymmetricPrimitiveValue p.1.1 p.1.2 A := by
  obtain ⟨P, L, -, -, -, hL⟩ := symmetric_value_data p.1.1 p.2.1
  obtain ⟨h1, h2, -⟩ := hL p.1.2 p.2.2
  exact ⟨_, h1, h2⟩

end
end NlsGge.ThirdConsultation.MPrimitive
