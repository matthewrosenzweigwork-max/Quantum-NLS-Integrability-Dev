import QuantumNLS.Ext025LROOT02
/-! integrator-authored trusted spec for EXT-025 contract_ROOT02 (terra_review r234 ACCEPT): headline statement(s) copied verbatim from Ext025LROOT02 (QuantumNLS.Ext025L). -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
namespace QuantumNLS.X25ROOT02Spec
open QuantumNLS.Ext025L
open QuantumNLS.Ext025A in

set_option maxHeartbeats 8000000 in
theorem contract_ROOT02_spec :
    -- pointwise decay for one integrable density, every nonzero frequency scaling
    (∀ (f : ℝ → ℂ), Integrable f (volume : Measure ℝ) → ∀ c : ℝ, c ≠ 0 →
      Tendsto (fun ω : ℝ => ∫ x : ℝ, Complex.exp (-Complex.I * ((c * ω * x : ℝ) : ℂ)) * f x)
        (cocompact ℝ) (𝓝 0)) ∧
    -- extension by zero: integrable on a measurable set, integral over the set
    (∀ (s : Set ℝ) (_hs : MeasurableSet s) (f : ℝ → ℂ), IntegrableOn f s (volume : Measure ℝ) →
      ∀ c : ℝ, c ≠ 0 →
      Tendsto (fun ω : ℝ => ∫ x in s, Complex.exp (-Complex.I * ((c * ω * x : ℝ) : ℂ)) * f x)
        (cocompact ℝ) (𝓝 0)) ∧
    -- uniform decay on every L¹-compact family
    (∀ K : Set (Lp ℂ 1 (volume : Measure ℝ)), IsCompact K → ∀ c : ℝ, c ≠ 0 →
      TendstoUniformly
        (fun ω : ℝ => fun f : K => ∫ x : ℝ,
          Complex.exp (-Complex.I * ((c * ω * x : ℝ) : ℂ)) * (f.1 : ℝ → ℂ) x)
        (fun _ => 0) (cocompact ℝ)) := by
  exact QuantumNLS.Ext025L.contract_ROOT02 

end QuantumNLS.X25ROOT02Spec
#print axioms QuantumNLS.X25ROOT02Spec.contract_ROOT02_spec
