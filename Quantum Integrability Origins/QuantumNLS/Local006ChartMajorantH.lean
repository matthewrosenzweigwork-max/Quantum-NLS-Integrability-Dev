import QuantumNLS.Local006NormalizedBindingH
import QuantumNLS.Local006G3Expansion

/-! Binding the normalized Fourier envelope to the actual normalized chart.
This stage does not assert degree-by-degree Taylor or derivative-kernel
identification. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric
open scoped BigOperators ENNReal
namespace QuantumNLS.Local006.ChartMajorantH
open QuantumNLS.PhysicalTensor QuantumNLS.Local002Bridge
  QuantumNLS.Local006.CollectiveF QuantumNLS.Local006.SequenceAlgebraE
  QuantumNLS.Local006.SequenceEvaluationE QuantumNLS.Local006.PositiveMajorantG
  QuantumNLS.Local006.SourceBindingH QuantumNLS.Local006.OperatorMatrixH
  QuantumNLS.Local006.BinomialBindingH QuantumNLS.Local006.NormalizedBindingH
  QuantumNLS.LocalSpectral QuantumNLS.Local003Analytic QuantumNLS.Local005 QuantumNLS.Local005.SourceD
  QuantumNLS.ResetFreeResolventLOCAL001 QuantumNLS.ResetFreeResolventLOCAL001.CompletionB

variable {L r κ : ℝ} [Fact (0 < L)]

lemma scalarG_normalized (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (u : L2T L)
    (he : ∀ n, matrix (normalizedSource hL hκ hr hs (toInterval L u)) n =
      opMatrix (Bf L κ ((toInterval L u : ScalarInterval L) : ℝ → ℂ) n r -
        (pm L n : ℂ) • (1 : E2 →L[ℂ] E2))) (n : ℤ) :
    scalarG L κ r u n = factor L κ * matrix (normalizedSource hL hκ hr hs (toInterval L u)) n 1 0 := by
  rw [he n, opMatrix_apply]
  have hv : basisVec 0 = vec2 1 0 := by ext i; fin_cases i <;> rfl
  rw [hv]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, PiLp.sub_apply, PiLp.smul_apply, vec2]
  change scalarG L κ r u n = factor L κ *
    (Bf L κ ((toInterval L u : ScalarInterval L) : ℝ → ℂ) n r (vec2 1 0) 1 - (pm L n : ℂ) * 0)
  rw [mul_zero, sub_zero, QuantumNLS.Local003Odd.Bf_congr (toInterval_coe L u)]
  rfl

/-- The actual analytic chart is dominated in each Fourier coordinate and in
its collective l2 norm by the summed absolute source-normalization envelope,
on one full profile ball. The two nested word series are absolutely convergent. -/
theorem actual_chart_majorant_stage (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ G : L2T L → Seq,
      AnalyticOnNhd ℝ G (ball 0 ρ) ∧ ∀ u ∈ ball (0 : L2T L) ρ,
        (∀ n, G u n = scalarG L κ r u n) ∧
        Positive (normalizedEnvelope hL hκ hr hs (toInterval L u)) ∧
        Summable (fun jl => ‖envelopeWord (sourceEnvelope hL hκ hr hs .projection (toInterval L u))
          (sourceEnvelope hL hκ hr hs .moment (toInterval L u)) jl‖) ∧
        Summable (fun jl => ‖normalizedWord (sourceSum hL hκ hr hs .projection (toInterval L u))
          (sourceSum hL hκ hr hs .moment (toInterval L u)) jl‖) ∧
        HasSum (normalizedWord (sourceSum hL hκ hr hs .projection (toInterval L u))
          (sourceSum hL hκ hr hs .moment (toInterval L u)))
          (normalizedSource hL hκ hr hs (toInterval L u)) ∧
        G u = factor L κ • (normalizedSource hL hκ hr hs (toInterval L u)).2.2 ∧
        (∀ n, ‖G u n‖ ≤ ‖factor L κ‖ *
          (matrix (normalizedEnvelope hL hκ hr hs (toInterval L u)) n 1 0).re) ∧
        ‖G u‖ ≤ ‖factor L κ‖ * ‖normalizedEnvelope hL hκ hr hs (toInterval L u)‖ := by
  obtain ⟨ρa, hρa, ha⟩ := actual_normalized_majorant hL hκ hr hs
  have hr2 : r < 2 * Real.pi / L := by convert hs using 1; unfold spacing; ring
  obtain ⟨ρg, hρg, C, hC, G, hG, hGe, -, -⟩ := exists_chart hL hκ hr hr2
  let ρ := min ρa ρg
  have hρ : 0 < ρ := lt_min hρa hρg
  have hsub : ball (0 : L2T L) ρ ⊆ ball 0 ρg := ball_subset_ball (min_le_right _ _)
  refine ⟨ρ, hρ, G, hG.mono hsub, ?_⟩
  intro u hu
  have hui : ‖toInterval L u‖ < ρa := by
    rw [norm_toInterval]
    exact (mem_ball_zero_iff.mp hu).trans_le (min_le_left _ _)
  obtain ⟨hp, henv, hw, hsum, hm, he⟩ := ha (toInterval L u) hui
  have hentry := scalarG_normalized hL hκ hr hs u he
  have heG : G u = factor L κ • (normalizedSource hL hκ hr hs (toInterval L u)).2.2 := by
    apply lp.ext
    funext n
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hGe u (hsub hu) n, hentry n]
    rfl
  have hnorm : ‖normalizedSource hL hκ hr hs (toInterval L u)‖ ≤
      ‖normalizedEnvelope hL hκ hr hs (toInterval L u)‖ := by
    apply solid_norm (a := normalizedEnvelope hL hκ hr hs (toInterval L u))
      (b := normalizedSource hL hκ hr hs (toInterval L u)) hp
    intro n i j
    have h := hm n i j
    dsimp only at h
    rw [← he n] at h
    exact h
  refine ⟨fun n => hGe u (hsub hu) n, hp, henv, hw, hsum, heG, ?_, ?_⟩
  · intro n
    rw [hGe u (hsub hu) n, hentry n, norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have h := hm n 1 0
    dsimp only at h
    rw [← he n] at h
    exact h
  · rw [heG, norm_smul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (QuantumNLS.Local006.SequenceAlgebraE.component_bounds
      (normalizedSource hL hκ hr hs (toInterval L u))).2.2.2.trans hnorm

end QuantumNLS.Local006.ChartMajorantH
#print axioms QuantumNLS.Local006.ChartMajorantH.actual_chart_majorant_stage

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local006.ChartMajorantH." ||
        n.toString.startsWith "_private.QuantumNLS.Local006ChartMajorantH" then
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
  Lean.logInfo m!"Local006ChartMajorantH audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
