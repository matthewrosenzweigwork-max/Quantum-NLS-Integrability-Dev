import QuantumNLS.Local006ChartKernelJ
import QuantumNLS.Local006G3Fourier

/-! All printed LOCAL-006 clauses for the actual normalized chart, including
 independent-slot absolute Fourier kernels of its derivative and real transpose. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal
namespace QuantumNLS.Local006.FinalJ
open QuantumNLS.PhysicalTensor QuantumNLS.Local002Bridge QuantumNLS.Local005
  QuantumNLS.Local006.CoefficientLiftE QuantumNLS.Local006.SequenceAlgebraE
  QuantumNLS.Local006.SequenceEvaluationE QuantumNLS.Local006.PositiveMajorantG
  QuantumNLS.Local006.SolidMajorantH QuantumNLS.Local006.PhysicalRegroupI
  QuantumNLS.Local006.TaylorBindingI QuantumNLS.Local006.NormalizedDerivativeJ
  QuantumNLS.Local006.ChartKernelJ QuantumNLS.Local006.CollectiveF
  QuantumNLS.Local006.FirstJetF QuantumNLS.Local006.G3Fourier
  QuantumNLS.ResetFreeResolventLOCAL001 QuantumNLS.ResetFreeResolventLOCAL001.CompletionB

variable {L r κ : ℝ} [Fact (0 < L)]

def TaylorClauses (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r) (hs : r < spacing L / 2)
    (G : L2T L → Seq) (p : FormalMultilinearSeries ℝ (L2T L) Seq) (u : L2T L) : Prop :=
  Summable (fun d => ‖physicalEnvelope hL hκ hr hs (toInterval L u) d‖) ∧
    HasSum (fun d => p d (fun _ => u)) (G u) ∧
    ∀ d, Positive (physicalEnvelope hL hκ hr hs (toInterval L u) d) ∧
      ∀ n, ‖p d (fun _ => u) n‖ ≤ ‖factor L κ‖ *
        (matrix (physicalEnvelope hL hκ hr hs (toInterval L u) d) n 1 0).re

theorem reset_collective_spectral (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ (G : L2T L → Seq)
      (p : FormalMultilinearSeries ℝ (L2T L) Seq)
      (e : OpenPartialHomeomorph (L2T L) Seq),
      AnalyticOnNhd ℝ G (ball 0 ρ) ∧ HasFPowerSeriesAt G p 0 ∧
      (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ, G u n = scalarG L κ r u n) ∧
      G 0 = 0 ∧ fderiv ℝ G 0 =
        (QuantumNLS.Local006.FirstJetF.fourierR L : L2T L →L[ℝ] Seq) ∧
      (e : L2T L → Seq) = G ∧ (0 : L2T L) ∈ e.source ∧ (0 : Seq) ∈ e.target ∧
      e.symm 0 = 0 ∧ AnalyticAt ℝ (e.symm : Seq → L2T L) 0 ∧
      (∀ k : ℕ, Even k → ∀ u : L2T L, p k (fun _ => u) = 0) ∧
      (∀ u ∈ ball (0 : L2T L) ρ,
        ‖G u - QuantumNLS.Local006.FirstJetF.fourierR L u - p 3 (fun _ => u)‖ ≤ C * ‖u‖ ^ 5) ∧
      (∀ u ∈ ball (0 : L2T L) ρ,
        ‖fderiv ℝ G u - (QuantumNLS.Local006.FirstJetF.fourierR L : L2T L →L[ℝ] Seq)‖ ≤
          C * ‖u‖ ^ 2) ∧
      (∀ (u : L2T L) (n : ℤ),
        p 3 (fun _ => u) n = printedG3 L κ (fun m => QuantumNLS.Fourier.fourierL2 L u m) n) ∧
      (∀ (u : L2T L) (n : ℤ),
        Summable (fun ab : ℤ × ℤ =>
          ‖doubleTerm L (fun m => QuantumNLS.Fourier.fourierL2 L u m) n ab‖) ∧
        Summable (fun a : ℤ =>
          ‖normTerm L (fun m => QuantumNLS.Fourier.fourierL2 L u m) n a‖)) ∧
      (∀ u ∈ ball (0 : L2T L) ρ, TaylorClauses hL hκ hr hs G p u ∧ KernelClauses hL hκ hr hs G u) := by
  have hr2 : r < 2 * Real.pi / L := by convert hs using 1; unfold spacing; ring
  obtain ⟨ρ0, hρ0, C, hC, G, p, e, hG, hp, hGe, hG0, hF, he, hes, het, hei, heai,
    heven, h5, hder, hg3, hsums⟩ :=
    QuantumNLS.Local006.G3Fourier.reset_collective_spectral_verified_part_g3 hL hκ hr hr2
  obtain ⟨ρk, hρk, hρk0, hρkR, hk⟩ := actual_chart_absolute_kernel_series hL hκ hr hs hρ0 hGe
  obtain ⟨R, hpR⟩ := hp
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (eball_mem_nhds (0 : L2T L) hpR.r_pos)
  let ρ := min ρk ε
  have hρ : 0 < ρ := lt_min hρk hε
  have hsubk : ball (0 : L2T L) ρ ⊆ ball 0 ρk := ball_subset_ball (min_le_left _ _)
  have hsub : ball (0 : L2T L) ρ ⊆ ball 0 ρ0 :=
    ball_subset_ball ((min_le_left _ _).trans hρk0)
  have hid := actual_taylor_coefficients hL hκ hr hs hρ0 ⟨R, hpR⟩ hGe
  refine ⟨ρ, hρ, C, hC, G, p, e, hG.mono hsub, ⟨R, hpR⟩,
    fun u hu => hGe u (hsub hu), hG0, hF, he, hes, het, hei, heai, heven,
    fun u hu => h5 u (hsub hu), fun u hu => hder u (hsub hu), hg3, hsums, ?_⟩
  intro u hu
  refine ⟨?_, hk u (hsubk hu)⟩
  have hus : ‖toInterval L u‖ < radius L r κ := by
    rw [norm_toInterval]
    exact (mem_ball_zero_iff.mp hu).trans_le ((min_le_left _ _).trans hρkR)
  have hrp := physical_regroup hL hκ hr hs (toInterval L u) (input_small hL hκ hr hus)
  refine ⟨hrp.1, ?_, ?_⟩
  · have hue : u ∈ eball (0 : L2T L) R := hεsub ((ball_subset_ball (min_le_right _ _)) hu)
    simpa only [zero_add] using hpR.hasSum hue
  · intro d
    have hd := hrp.2.2.2.2 d
    refine ⟨hd.1, ?_⟩
    intro n
    rw [hid u d, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hd.2 n 1 0) (norm_nonneg _)

end QuantumNLS.Local006.FinalJ
#print axioms QuantumNLS.Local006.FinalJ.reset_collective_spectral
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local006.FinalJ." ||
        n.toString.startsWith "_private.QuantumNLS.Local006FinalJ" then
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
  Lean.logInfo m!"Local006FinalJ audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."

