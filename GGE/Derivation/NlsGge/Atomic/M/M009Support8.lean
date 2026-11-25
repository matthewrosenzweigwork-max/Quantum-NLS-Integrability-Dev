import Mathlib
import NlsGge.Atomic.M.M007
import NlsGge.Atomic.M.M009Host
import NlsGge.Atomic.M.M009Support2
import NlsGge.Atomic.M.M009Support4
import NlsGge.Atomic.M.M009Support7

/- M-009 SUPPORT08 (proof development, AUTHOR; not reviewed).  Pro round 13 section 11 Stage 2, admitted only now that the exact
   source well-definedness theorem `symmetric_primitive_exists_unique` (M009Support7) is proved: the accessor
   `symmetricPrimitive` and its complete characterization (one semantic unit), the local-representative derivative
   theorem, the base normalization, and the public aliases of "Public aliases and downstream transport"
   (heads and bodies verbatim from Pro round 13 section 11). -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology BigOperators
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.MPrimitive
noncomputable section
attribute [local instance] Classical.propDecidable

def symmetricPrimitive (p : PrimitivePoint) : ℂ :=
  Classical.choose (symmetric_primitive_exists_unique p).exists

-- This theorem and the definition are one semantic unit and must be admitted
-- together. Every downstream use depends on this characterization export.
theorem symmetric_primitive_characterization (p : PrimitivePoint) :
  HasSymmetricPrimitiveValue p.1.1 p.1.2 (symmetricPrimitive p) ∧
  (∀ A : ℂ, HasSymmetricPrimitiveValue p.1.1 p.1.2 A →
    A = symmetricPrimitive p) ∧
  (∀ (upper : Bool) (m : ℕ)
      (c : Fin (m + 1) → ℝ → ℂ),
    AdmissiblePrimitiveChain p.1.1 (baseEndpoint p.1.1 upper) p.1.2 m c →
      MContour.HasFiniteChainIntegral p.1.1 m c (symmetricPrimitive p)) := by
  have hspec : HasSymmetricPrimitiveValue p.1.1 p.1.2 (symmetricPrimitive p) :=
    Classical.choose_spec (symmetric_primitive_exists_unique p).exists
  have huniq : ∀ A : ℂ, HasSymmetricPrimitiveValue p.1.1 p.1.2 A → A = symmetricPrimitive p :=
    fun A hA => (symmetric_primitive_exists_unique p).unique hA hspec
  refine ⟨hspec, huniq, fun upper m c hc => ?_⟩
  obtain ⟨P, L, -, -, -, hL⟩ := symmetric_value_data p.1.1 p.2.1
  obtain ⟨h1, -, h3⟩ := hL p.1.2 p.2.2
  have := h3 upper m c hc
  rwa [huniq _ h1] at this

theorem symmetric_primitive_value_eq {φ : PotPair} (hφ : φ ∈ gkW) {L : ℂ → ℂ}
    (hL : ∀ z ∈ endpointClosureFiber φ,
      HasSymmetricPrimitiveValue φ z (L z - L (lamMinus φ 0)))
    (z : ℂ) (hz : z ∈ endpointClosureFiber φ) :
    symmetricPrimitive ⟨(φ, z), ⟨hφ, hz⟩⟩ = L z - L (lamMinus φ 0) :=
  ((symmetric_primitive_characterization ⟨(φ, z), ⟨hφ, hz⟩⟩).2.1 _ (hL z hz)).symm

theorem symmetric_primitive_hasDerivAt
    (φ : PotPair) (hφ : φ ∈ gkW)
    (z : ℂ) (hz : z ∈ cutFreeFiber φ) :
  ∃ (U : Set ℂ) (hU : IsOpen U), z ∈ U ∧
    ∃ hUD : U ⊆ cutFreeFiber φ,
    ∃ F : ℂ → ℂ,
      (∀ (w : ℂ) (hw : w ∈ U),
        F w = symmetricPrimitive
          ⟨(φ, w), ⟨hφ, Or.inl (hUD hw)⟩⟩) ∧
      (∀ w ∈ U, HasDerivAt F (MContour.omega φ w) w) := by
  obtain ⟨P, L, hP, hLP, -, hL⟩ := symmetric_value_data φ hφ
  refine ⟨cutFreeFiber φ, cutFreeFiber_isOpen φ hφ, hz, subset_rfl,
    fun w => P w - L (lamMinus φ 0), fun w hw => ?_, fun w hw => (hP w hw).sub_const _⟩
  rw [symmetric_primitive_value_eq hφ (fun z hz => (hL z hz).1) w (Or.inl hw), hLP w hw]

-- Exact base normalization; endpoint membership is supplied by the
-- separately proved literal geometric membership leaves, not a new premise.
theorem symmetric_primitive_base_values
    (φ : PotPair) (hφ : φ ∈ gkW) :
  symmetricPrimitive
    ⟨(φ, lamMinus φ 0), ⟨hφ, lower_endpoint_mem φ 0⟩⟩ = 0 ∧
  symmetricPrimitive
    ⟨(φ, lamPlus φ 0), ⟨hφ, upper_endpoint_mem φ 0⟩⟩ = 0 := by
  obtain ⟨P, L, -, -, hbase, hL⟩ := symmetric_value_data φ hφ
  refine ⟨?_, ?_⟩
  · rw [symmetric_primitive_value_eq hφ (fun z hz => (hL z hz).1) _ (lower_endpoint_mem φ 0)]
    exact sub_self _
  · rw [symmetric_primitive_value_eq hφ (fun z hz => (hL z hz).1) _ (upper_endpoint_mem φ 0), hbase]
    exact sub_self _

end
end NlsGge.ThirdConsultation.MPrimitive

namespace NlsGge.ThirdConsultation.M

abbrev PrimitivePoint := MPrimitive.PrimitivePoint

def primitiveDomain : Set (PotPair × ℂ) := MPrimitive.cutFreeDomain

noncomputable def primitive (p : PrimitivePoint) : ℂ := MPrimitive.symmetricPrimitive p

end NlsGge.ThirdConsultation.M
