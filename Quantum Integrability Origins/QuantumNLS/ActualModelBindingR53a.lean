import QuantumNLS.ActualModelInterfacesR52a
import QuantumNLS.Def044BindingR26m
import QuantumNLS.Prop025OInputs
import QuantumNLS.REF88PrintedChartLocal

/-! The accepted DEF-021 chart supplies the normalized chart antecedent of
the shared R25m hierarchy and the OInputs window statement. Construct DEF-044
in the R26m carrier, using the physical spectral witnesses from R52a. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter Topology MeasureTheory Set
namespace QuantumNLS.ActualModelBindingR53a
open PhysicalTensor Def033HierarchyR24m
open ResetNormalizationUniqueness (Cphys)
variable {L κ : ℝ} [Fact (0 < L)]

abbrev chart (hκ : 0 < κ) := Def021ChartR41b.chart L κ hκ

theorem printed_chart (hκ : 0 < κ) :
    REF88PrintedChart.PrintedChart hκ (chart (L := L) hκ).Φ := by
  let C := chart (L := L) hκ
  let c := Def021ChartR41b.localChart L
  have hρ : 0 < c.d / Real.sqrt κ := div_pos c.positive (Real.sqrt_pos.2 hκ)
  have hball : ∀ᶠ u in 𝓝 (0 : L2T L), u ∈ Metric.ball (0 : L2T L) (c.d / Real.sqrt κ) :=
    Metric.ball_mem_nhds _ hρ
  have hagree : C.Φ =ᶠ[𝓝 (0 : L2T L)] c.Φ κ :=
    hball.mono C.local_agreement
  have hs : StrongSymplectic.IsStronglySymplectic C.Φ := by
    refine ⟨⟨C.Ψ, C.left_inverse, C.right_inverse, fun z =>
      (C.inverse_analytic z).differentiableAt⟩, fun u => (C.analytic u).differentiableAt, ?_, ?_⟩
    · intro u
      obtain ⟨e, he, _⟩ := C.differential u
      exact ⟨e, congrArg (fun f : L2T L →L[ℝ] REF88Chart.K => (f : L2T L → REF88Chart.K))
        he.fderiv.symm⟩
    · exact C.symplectic
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hFourier, _, _, hcov, _⟩ := c.spec.1 κ hκ
  apply REF88PrintedChartLocal.printedChart_of_local hκ
  refine ⟨hs, C.analytic, C.actions, ?_, ?_⟩
  · intro v
    rw [hagree.fderiv_eq]
    exact hFourier v
  · filter_upwards [hball] with u hu
    have hu' : Cphys L u ∈ Metric.ball (0 : L2T L) (c.d / Real.sqrt κ) := by
      simpa only [Metric.mem_ball, dist_zero_right, (Cphys L).norm_map] using hu
    rw [C.local_agreement u hu, C.local_agreement _ hu']
    apply lp.ext
    funext n
    rw [lp.star_apply]
    exact (hcov u hu n).2.2.2.2.2

theorem sobolev (hκ : 0 < κ) :
    HierarchyInputR25m.SobolevHomeomorphisms (chart (L := L) hκ).Φ := by
  intro s hs
  obtain ⟨E, hE, _⟩ := ActualModelChartR52a.sobolev_restrictions hκ (chart (L := L) hκ) s hs
  exact ⟨E, fun u n => (Reg015Setting.toBase_apply s hs (E u) n).symm.trans
    (congrArg (fun z : REF88Chart.K => z n) (hE u))⟩

theorem hierarchy_intermediate (hκ : 0 < κ)
    (HierarchyInput : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ) :
    HierarchyInputR25m.HierarchyConclusion (κ := κ) (chart (L := L) hκ).Φ
      (Def044ChartR51a.action hκ) :=
  HierarchyInput _ (printed_chart hκ) (sobolev hκ)
    (HierarchyInputR25m.scalar_uniqueness hκ) (HierarchyInputR25m.scalar_moments hκ)

/-- The actual three clauses in the R26m carrier from the one shared R25m
input, retaining the same map, scalar measure, and hierarchy. -/
def DEF044_intermediate (hκ : 0 < κ)
    (HierarchyInput : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (u : Smooth L) (hu : ‖physical u‖ = 1) :
    Def044BindingR26m.MixedInterface hκ u hu :=
  ⟨Classical.choice (ActualModelInterfacesR52a.spectral_interface hκ u hu),
    Def044ChartR26m.chart_interface hκ (chart (L := L) hκ),
    ⟨hierarchy_intermediate hκ HierarchyInput, Def044WindowR26m.window_differentials hκ⟩⟩

end QuantumNLS.ActualModelBindingR53a

#print axioms QuantumNLS.ActualModelBindingR53a.printed_chart
#print axioms QuantumNLS.ActualModelBindingR53a.hierarchy_intermediate
#print axioms QuantumNLS.ActualModelBindingR53a.DEF044_intermediate

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.ActualModelBindingR53a." ||
        n.toString.startsWith "_private.QuantumNLS.ActualModelBindingR53a." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 ||
          n.components.any (fun c => c.toString == "RegularCut") then
        throwError "Held dependency: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"R53a aggregate audit PASS: {own} own constants; {seen.size} transitive constants; standard only."
