import QuantumNLS.Def035MomentsR24m
/-! integrator-authored trusted spec for DEF-035 (realized under owner decision D2; review r232 FULL): headline statement(s) copied verbatim from Def035MomentsR24m (QuantumNLS.Def035MomentsR24m). -/
set_option autoImplicit false
noncomputable section
open Filter MeasureTheory Topology
open scoped ENNReal
namespace QuantumNLS.D35Spec
open QuantumNLS.Def035MomentsR24m
open QuantumNLS.Def035TruncationR24m
variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
  (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
  {Ω' : Type*} [MeasurableSpace Ω'] (ν : Measure Ω') [IsProbabilityMeasure ν]

set_option maxHeartbeats 8000000 in
theorem DEF035_distribution_spec (X : ∀ n, Ω n → ℝ) (Y : Ω' → ℝ) (p : ℝ) (hp : 0 < p)
    (hX : ∀ n x, 0 ≤ X n x) (hY : ∀ x, 0 ≤ Y x)
    (hd : TendstoInDistribution X atTop Y μ ν) (hui : UniformPowerTail μ X p) :
    (∀ n, Integrable (fun x => (X n x) ^ p) (μ n)) ∧
    Integrable (fun x => (Y x) ^ p) ν ∧
    Tendsto (fun n => ∫ x, (X n x) ^ p ∂μ n) atTop (𝓝 (∫ x, (Y x) ^ p ∂ν)) := by
  first
  | exact QuantumNLS.Def035MomentsR24m.DEF035_distribution
  | (apply QuantumNLS.Def035MomentsR24m.DEF035_distribution <;> assumption)

set_option maxHeartbeats 8000000 in
theorem zero_power_spec (p : ℝ) (hp : 0 < p) : (0 : ℝ) ^ p = 0 := by
  first
  | exact QuantumNLS.Def035MomentsR24m.zero_power
  | (apply QuantumNLS.Def035MomentsR24m.zero_power <;> assumption)

set_option maxHeartbeats 8000000 in
theorem DEF035_probability_spec {S : Type*} [MeasurableSpace S]
    (P : Measure S) [IsProbabilityMeasure P] (X : ℕ → S → ℝ) (Y : S → ℝ)
    (p : ℝ) (hp : 0 < p) (hX : ∀ n x, 0 ≤ X n x) (hY : ∀ x, 0 ≤ Y x)
    (hm : ∀ n, AEMeasurable (X n) P) (hc : TendstoInMeasure P X atTop Y)
    (hui : UniformPowerTail (fun _ => P) X p) :
    (∀ n, Integrable (fun x => (X n x) ^ p) P) ∧
    Integrable (fun x => (Y x) ^ p) P ∧
    Tendsto (fun n => ∫ x, (X n x) ^ p ∂P) atTop (𝓝 (∫ x, (Y x) ^ p ∂P)) := by
  first
  | exact QuantumNLS.Def035MomentsR24m.DEF035_probability
  | (apply QuantumNLS.Def035MomentsR24m.DEF035_probability <;> assumption)

theorem pin_UniformPowerTail {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, MeasureTheory.Measure (Ω n)) (X : ∀ n, Ω n → ℝ) (p : ℝ) :
    QuantumNLS.Def035TruncationR24m.UniformPowerTail μ X p ↔
      QuantumNLS.Def035TruncationR24m.TailUI μ (fun n x => (X n x) ^ p) := Iff.rfl

end QuantumNLS.D35Spec
#print axioms QuantumNLS.D35Spec.DEF035_distribution_spec
#print axioms QuantumNLS.D35Spec.zero_power_spec
#print axioms QuantumNLS.D35Spec.DEF035_probability_spec
