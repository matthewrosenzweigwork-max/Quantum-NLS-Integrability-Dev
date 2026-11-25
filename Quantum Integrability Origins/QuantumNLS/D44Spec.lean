import QuantumNLS.Bind7BDEF044H02
/-! integrator trusted spec: verbatim mirror of DEF044Final plus a field-wise construction from the reviewed DEF044_final. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Filter MeasureTheory Topology
namespace QuantumNLS.D44Spec
open QuantumNLS.Bind7BDEF044H02
open QuantumNLS.PhysicalTensor QuantumNLS.ClassicalCharges QuantumNLS.HierarchyFlow
open QuantumNLS.Def033HierarchyR24m (Smooth physical)
open QuantumNLS.Def033CoreR24m (ActiveFrequency phase)
open QuantumNLS.Def044InterfacesR51a (windowError regularity_mono)
open QuantumNLS.Q07TailBindingR24 (regularity)
open QuantumNLS.SmoothScalarMomentsPhysical (smoothL2)
variable {L κ : ℝ} [Fact (0 < L)]

structure MirrorDEF044Final (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1) : Type where
  /-- The three printed clauses, exactly the frozen H01 value. -/
  mixed : QuantumNLS.Def044BindingR26m.MixedInterface hκ u hu
  mixed_eq : mixed = QuantumNLS.Bind7BDEF044H01.DEF044_bound hκ u hu
  /-- (a) The chart of the mixed interface is the actual DEF-021 chart, and it is a printed chart. -/
  chart_is_actual : mixed.chart.chart = QuantumNLS.Def021ChartR41b.chart L κ hκ
  printed_chart : QuantumNLS.REF88PrintedChart.PrintedChart hκ mixed.chart.chart.Φ
  /-- (a) Every printed chart (the chart parameter of DEF-033) is this chart. -/
  chart_unique : ∀ w : L2T L → QuantumNLS.REF88Chart.K,
    QuantumNLS.REF88PrintedChart.PrintedChart hκ w → w = mixed.chart.chart.Φ
  /-- (a) All printed DEF-033 clauses, at the chart of DEF-044. -/
  def033 : QuantumNLS.Bind7BDEF033H02.DEF033Package hκ mixed.chart.chart.Φ
  /-- (a) The DEF-044 action is the DEF-033 indexed mass. -/
  action_eq : ∀ (v : L2T L) (n : ℤ),
    QuantumNLS.Def044ChartR51a.action hκ v n = (QuantumNLS.RootIndexedMasses.masses hκ v).1 n
  /-- (a) Same physical trajectory: every family of smooth Hamiltonian flows of the DEF-044 hierarchy
  (orders `r ≥ 2`) is the DEF-033 flow. -/
  same_flow : ∀ (Φ' : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ))
    (_ : ∀ r, 2 ≤ r → IsHamFlow L (hamiltonian L κ r) (Φ' r)) (r : ℕ), 2 ≤ r →
    ∀ (v : Smooth L) (t : ℝ), Φ' r t v.val = def033.flow r t v.val
  /-- (a) Endpoint frequencies on the same trajectory and chart: for positive-action endpoints the DEF-044
  `ActiveTarget` along any DEF-044 hierarchy flow is exactly the DEF-033 target `ω_{r,b}(v) - ω_{r,a}(v)`,
  and it is the only one. -/
  endpoints : ∀ (Φ' : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ))
    (hΦ' : ∀ r, 2 ≤ r → IsHamFlow L (hamiltonian L κ r) (Φ' r)) (r : ℕ) (hr : 2 ≤ r)
    (v : Smooth L) (a b : ℤ),
    0 < QuantumNLS.Def044ChartR51a.action hκ (physical v) a →
    0 < QuantumNLS.Def044ChartR51a.action hκ (physical v) b →
    QuantumNLS.Def044BindingR26m.ActiveTarget
      (fun n t => mixed.chart.chart.Φ (physical ⟨Φ' r t v.val, ((hΦ' r hr v.val v.property).2.2 t).1⟩) n)
      (fun n => mixed.chart.chart.Φ (physical v) n) a b
      (QuantumNLS.Def033CoreR24m.target (def033.ω r v) a b) ∧
    ∀ c : ℝ, QuantumNLS.Def044BindingR26m.ActiveTarget
      (fun n t => mixed.chart.chart.Φ (physical ⟨Φ' r t v.val, ((hΦ' r hr v.val v.property).2.2 t).1⟩) n)
      (fun n => mixed.chart.chart.Φ (physical v) n) a b c →
      c = QuantumNLS.Def033CoreR24m.target (def033.ω r v) a b
  /-- (a) Receiver-minus-donor sign of the quantum phase ratio. -/
  phase_sign : ∀ r (v : Smooth L) (a b : ℤ) (t : ℝ),
    0 < QuantumNLS.Def044ChartR51a.action hκ (physical v) a →
    0 < QuantumNLS.Def044ChartR51a.action hκ (physical v) b →
    phase t (def033.ω r v b) / phase t (def033.ω r v a) =
      phase t (QuantumNLS.Def033CoreR24m.target (def033.ω r v) a b)
  /-- (a) The DEF-044 total/adjacent abbreviations and the original Born law are the DEF-033 ones. -/
  adjacent_eq : ∀ (N r : ℕ) (a b : ℤ) (m : QuantumNLS.BetheLabels.MArr N)
    (hd : QuantumNLS.Occupation.DonorOK a (QuantumNLS.BetheCoefficientTransform.marrArr N m).1),
    QuantumNLS.Def044BindingR26m.adjacent (L := L) (κ := κ) N r a b m hd =
      QuantumNLS.TerraMultiRound12Definitions.adjacentDifference L κ N r a b m hd
  total_eq : ∀ (N r : ℕ) (a b : ℤ) (missing : QuantumNLS.BetheLabels.MArr N → ℝ)
    (m : QuantumNLS.BetheLabels.MArr N),
    QuantumNLS.Def044BindingR26m.total (L := L) (κ := κ) N r a b missing m =
      QuantumNLS.Def033CoreR24m.withMissing L κ N r a b missing m
  born_eq : ∀ (v : L2T L) (hv : ‖v‖ = 1) (N : ℕ),
    QuantumNLS.Def044BindingR26m.originalBorn hκ v hv N = QuantumNLS.Def033CoreR24m.originalBorn hκ v hv N
  /-- (b) The window-functional identification. -/
  window_identification : WindowIdentification (L := L) hκ

noncomputable def DEF044_final_mirror (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1) : MirrorDEF044Final hκ u hu :=
  let P := QuantumNLS.Bind7BDEF044H02.DEF044_final hκ u hu
  ⟨P.mixed, P.mixed_eq, P.chart_is_actual, P.printed_chart, P.chart_unique, P.def033, P.action_eq, P.same_flow, P.endpoints, P.phase_sign, P.adjacent_eq, P.total_eq, P.born_eq, P.window_identification⟩

theorem pin_WindowIdentification (hκ : 0 < κ) :
    QuantumNLS.Bind7BDEF044H02.WindowIdentification (L := L) hκ ↔
  ∀ (d r : ℕ) (hr : r ≤ d) (h : ℝ) (l : ℕ) (u : Sobolev.H02 L (regularity d))
    (f : ℝ → ℂ) (hf : SmoothPeriodic L f), u.val = smoothL2 hf →
    windowError hκ d r hr h l u = (charge L κ f (r + 1)).re -
      QuantumNLS.Q07IntegratedHessiansR16.windowContour hκ r (QuantumNLS.PROP017UniformN.cutSeq L l) h u.val := Iff.rfl

end QuantumNLS.D44Spec
#print axioms QuantumNLS.D44Spec.DEF044_final_mirror
