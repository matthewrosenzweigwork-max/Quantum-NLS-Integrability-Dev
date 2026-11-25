import QuantumNLS.FullBetheTransform
/-! integrator-authored trusted spec for R-098A4CF1 A03:unitary (Terra r134 ACCEPT): full Bethe transform unitary with expansion/synthesis/Parseval: frozen statements of FullBetheTransform restated verbatim. -/
namespace RF098Spec
open scoped BigOperators InnerProductSpace
open QuantumNLS.PhysicalTensor QuantumNLS.BetheLabels QuantumNLS.BetheCoefficientTransform QuantumNLS.BetheOccupationGauge
open QuantumNLS QuantumNLS.FullBetheTransform

set_option maxHeartbeats 4000000 in
theorem expansion_spec (L : ℝ) [Fact (0 < L)] (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c) (g : QuantumNLS.BetheOccupationGauge.Gauge) (f : physSector L N) :
    HasSum (fun m => ⟪basis L N hN c hc g m, f⟫_ℂ • occupation N m)
      (transform L N hN c hc g f) := by
  apply QuantumNLS.FullBetheTransform.expansion <;> assumption

set_option maxHeartbeats 4000000 in
theorem synthesis_spec (L : ℝ) [Fact (0 < L)] (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c) (g : QuantumNLS.BetheOccupationGauge.Gauge) (a : lp (fun _ : MArr N => ℂ) 2) :
    HasSum (fun m => a m • basis L N hN c hc g m)
      ((coefficientTransform (basis L N hN c hc g)).symm a) := by
  apply QuantumNLS.FullBetheTransform.synthesis <;> assumption

set_option maxHeartbeats 4000000 in
theorem inverse_expansion_spec (L : ℝ) [Fact (0 < L)] (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c) (g : QuantumNLS.BetheOccupationGauge.Gauge) (v : OccupationUnitary.Boson N) :
    HasSum (fun m => OccupationUnitary.U4 N v (marrArr N m) • basis L N hN c hc g m)
      ((transform L N hN c hc g).symm v) := by
  apply QuantumNLS.FullBetheTransform.inverse_expansion <;> assumption

set_option maxHeartbeats 4000000 in
theorem synthesis_transform_spec (L : ℝ) [Fact (0 < L)] (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c) (g : QuantumNLS.BetheOccupationGauge.Gauge) (a : lp (fun _ : MArr N => ℂ) 2) :
    HasSum (fun m => a m • occupation N m)
      (transform L N hN c hc g ((coefficientTransform (basis L N hN c hc g)).symm a)) := by
  apply QuantumNLS.FullBetheTransform.synthesis_transform <;> assumption

set_option maxHeartbeats 4000000 in
theorem inverse_series_spec (L : ℝ) [Fact (0 < L)] (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c) (g : QuantumNLS.BetheOccupationGauge.Gauge) (a : lp (fun _ : MArr N => ℂ) 2)
    (v : OccupationUnitary.Boson N) (hv : HasSum (fun m => a m • occupation N m) v) :
    HasSum (fun m => a m • basis L N hN c hc g m) ((transform L N hN c hc g).symm v) := by
  apply QuantumNLS.FullBetheTransform.inverse_series <;> assumption

set_option maxHeartbeats 4000000 in
theorem parseval_spec (L : ℝ) [Fact (0 < L)] (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c) (g : QuantumNLS.BetheOccupationGauge.Gauge) (f : physSector L N) :
    HasSum (fun m => ‖⟪basis L N hN c hc g m, f⟫_ℂ‖ ^ 2) (‖f‖ ^ 2) := by
  apply QuantumNLS.FullBetheTransform.parseval <;> assumption

set_option maxHeartbeats 4000000 in
theorem synthesis_parseval_spec (L : ℝ) [Fact (0 < L)] (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c) (g : QuantumNLS.BetheOccupationGauge.Gauge) (a : lp (fun _ : MArr N => ℂ) 2) :
    HasSum (fun m => ‖a m‖ ^ 2)
      (‖(coefficientTransform (basis L N hN c hc g)).symm a‖ ^ 2) := by
  apply QuantumNLS.FullBetheTransform.synthesis_parseval <;> assumption

set_option maxHeartbeats 4000000 in
theorem full_unitary_spec (L : ℝ) [Fact (0 < L)] (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c) (g : QuantumNLS.BetheOccupationGauge.Gauge) : Function.Surjective (transform L N hN c hc g) ∧
    (∀ f, ‖transform L N hN c hc g f‖ = ‖f‖) ∧
    (∀ f v, ⟪transform L N hN c hc g f, transform L N hN c hc g v⟫_ℂ = ⟪f,v⟫_ℂ) := by
  apply QuantumNLS.FullBetheTransform.full_unitary <;> assumption

end RF098Spec
#print axioms RF098Spec.expansion_spec
#print axioms RF098Spec.synthesis_spec
#print axioms RF098Spec.inverse_expansion_spec
#print axioms RF098Spec.synthesis_transform_spec
#print axioms RF098Spec.inverse_series_spec
#print axioms RF098Spec.parseval_spec
#print axioms RF098Spec.synthesis_parseval_spec
#print axioms RF098Spec.full_unitary_spec
