import QuantumNLS.Local006TaylorBindingI
import QuantumNLS.Local006FirstJetF
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Termwise differentiation and transposition of the actual Taylor series
in operator norm, including the Fourier representation. This does not assert
boundedness of the entrywise-absolute Fourier matrix. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open Set Metric Filter Topology
open scoped BigOperators ENNReal InnerProductSpace
namespace QuantumNLS.Local006.KernelSeriesI
open QuantumNLS.PhysicalTensor QuantumNLS.Local006.CollectiveF
  QuantumNLS.Local006.FirstJetF

variable {L : ℝ} [Fact (0 < L)]

def fourierOperator (T : L2T L →L[ℝ] Seq) : Seq →L[ℝ] Seq :=
  T.comp (fourierR L).symm.toContinuousLinearMap

def fourierOperatorMap : (L2T L →L[ℝ] Seq) →L[ℝ] (Seq →L[ℝ] Seq) :=
  (ContinuousLinearMap.compL ℝ Seq (L2T L) Seq).flip (fourierR L).symm.toContinuousLinearMap

lemma derivative_series {G : L2T L → Seq}
    {p : FormalMultilinearSeries ℝ (L2T L) Seq} {r : ℝ≥0∞}
    (hp : HasFPowerSeriesOnBall G p 0 r) (u : L2T L) (hu : u ∈ eball (0 : L2T L) r) :
    Summable (fun d => ‖p.derivSeries d (fun _ => u)‖) ∧
      HasSum (fun d => p.derivSeries d (fun _ => u)) (fderiv ℝ G u) ∧
      Summable (fun d => ‖fourierOperator (p.derivSeries d (fun _ => u))‖) ∧
      HasSum (fun d => fourierOperator (p.derivSeries d (fun _ => u)))
        (fourierOperator (fderiv ℝ G u)) := by
  have hrad : u ∈ eball (0 : L2T L) p.derivSeries.radius :=
    eball_subset_eball (hp.r_le.trans p.radius_le_radius_derivSeries) hu
  have hn := p.derivSeries.summable_norm_apply hrad
  have hs := hp.fderiv.hasSum hu
  simp only [zero_add] at hs
  refine ⟨hn, hs, ?_, (fourierOperatorMap (L := L)).hasSum hs⟩
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun d => (fourierOperatorMap (L := L)).le_opNorm _) (hn.mul_left ‖fourierOperatorMap (L := L)‖)

/-- The transpose is taken on the real Hilbert space of complex Fourier
sequences. Both real directions in each Fourier coordinate are retained. -/
theorem actual_fourier_transpose_series {G : L2T L → Seq}
    {p : FormalMultilinearSeries ℝ (L2T L) Seq} {r : ℝ≥0∞}
    (hp : HasFPowerSeriesOnBall G p 0 r) (u : L2T L) (hu : u ∈ eball (0 : L2T L) r) :
    Summable (fun d => ‖ContinuousLinearMap.adjoint
      (fourierOperator (p.derivSeries d (fun _ => u)))‖) ∧
      HasSum (fun d => ContinuousLinearMap.adjoint
        (fourierOperator (p.derivSeries d (fun _ => u))))
        (ContinuousLinearMap.adjoint (fourierOperator (fderiv ℝ G u))) ∧
      (∀ i j : ℤ, ∀ z w : ℂ,
        ⟪lp.single 2 j z, (ContinuousLinearMap.adjoint (fourierOperator (fderiv ℝ G u)))
          (lp.single 2 i w)⟫_ℝ =
        ⟪fourierOperator (fderiv ℝ G u) (lp.single 2 j z), lp.single 2 i w⟫_ℝ) := by
  have h := derivative_series hp u hu
  refine ⟨by simpa only [ContinuousLinearMap.adjoint.norm_map] using h.2.2.1,
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap.hasSum h.2.2.2, ?_⟩
  intro i j z w
  exact ContinuousLinearMap.adjoint_inner_right _ _ _

/-- Actual-chart instantiation of termwise differentiation and real Fourier
transposition, on one full ball. Convergence here is in operator norm; the
entrywise-absolute Fourier-kernel operator bounds remain a separate obligation. -/
theorem actual_chart_kernel_series_stage {κ r : ℝ}
    (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < QuantumNLS.ResetFreeResolventLOCAL001.spacing L / 2) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ (G : L2T L → Seq) (p : FormalMultilinearSeries ℝ (L2T L) Seq),
      AnalyticOnNhd ℝ G (ball 0 ρ) ∧ HasFPowerSeriesAt G p 0 ∧
      (∀ u ∈ ball (0 : L2T L) ρ, ∀ n, G u n = scalarG L κ r u n) ∧
      ∀ u ∈ ball (0 : L2T L) ρ,
        Summable (fun d => ‖p.derivSeries d (fun _ => u)‖) ∧
        HasSum (fun d => p.derivSeries d (fun _ => u)) (fderiv ℝ G u) ∧
        Summable (fun d => ‖fourierOperator (p.derivSeries d (fun _ => u))‖) ∧
        HasSum (fun d => fourierOperator (p.derivSeries d (fun _ => u)))
          (fourierOperator (fderiv ℝ G u)) ∧
        Summable (fun d => ‖ContinuousLinearMap.adjoint
          (fourierOperator (p.derivSeries d (fun _ => u)))‖) ∧
        HasSum (fun d => ContinuousLinearMap.adjoint
          (fourierOperator (p.derivSeries d (fun _ => u))))
          (ContinuousLinearMap.adjoint (fourierOperator (fderiv ℝ G u))) ∧
        ∀ i j : ℤ, ∀ z w : ℂ,
          ⟪lp.single 2 j z, (ContinuousLinearMap.adjoint (fourierOperator (fderiv ℝ G u)))
            (lp.single 2 i w)⟫_ℝ =
          ⟪fourierOperator (fderiv ℝ G u) (lp.single 2 j z), lp.single 2 i w⟫_ℝ := by
  obtain ⟨ρ0, hρ0, G, p, hG, hp, hGe, -, -, -⟩ :=
    QuantumNLS.Local006.TaylorBindingI.actual_taylor_majorant_stage hL hκ hr hs
  obtain ⟨R, hpR⟩ := hp
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (eball_mem_nhds (0 : L2T L) hpR.r_pos)
  let ρ := min ρ0 ε
  have hρ : 0 < ρ := lt_min hρ0 hε
  have hsub : ball (0 : L2T L) ρ ⊆ ball 0 ρ0 := ball_subset_ball (min_le_left _ _)
  refine ⟨ρ, hρ, G, p, hG.mono hsub, ⟨R, hpR⟩, fun u hu => hGe u (hsub hu), ?_⟩
  intro u hu
  have hur : u ∈ eball (0 : L2T L) R := hεsub ((ball_subset_ball (min_le_right _ _)) hu)
  have hd := derivative_series hpR u hur
  have ht := actual_fourier_transpose_series hpR u hur
  exact ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2, ht.1, ht.2.1, ht.2.2⟩

end QuantumNLS.Local006.KernelSeriesI
#print axioms QuantumNLS.Local006.KernelSeriesI.derivative_series
#print axioms QuantumNLS.Local006.KernelSeriesI.actual_fourier_transpose_series

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local006.KernelSeriesI." ||
        n.toString.startsWith "_private.QuantumNLS.Local006KernelSeriesI" then
      pending := pending.push n
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"Local006KernelSeriesI audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."

#print axioms QuantumNLS.Local006.KernelSeriesI.actual_chart_kernel_series_stage
