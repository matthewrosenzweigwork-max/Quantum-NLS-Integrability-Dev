import QuantumNLS.Local006DegreeRegroupI

/-! Bind total-degree regrouping to the frozen physical Fourier source words,
including coefficientwise positive envelopes on one full profile ball. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric
open scoped BigOperators ENNReal
namespace QuantumNLS.Local006.PhysicalRegroupI
open QuantumNLS.PhysicalTensor QuantumNLS.Local002Bridge QuantumNLS.Local005
  QuantumNLS.Local005.SourceD QuantumNLS.Local006.CoefficientLiftE
  QuantumNLS.Local006.SequenceAlgebraE QuantumNLS.Local006.SequenceEvaluationE
  QuantumNLS.Local006.PositiveMajorantG QuantumNLS.Local006.SourceMajorantG
  QuantumNLS.Local006.NormalizedMajorantG QuantumNLS.Local006.SolidMajorantH
  QuantumNLS.Local006.SourceBindingH QuantumNLS.Local006.BinomialBindingH
  QuantumNLS.Local006.NormalizedBindingH QuantumNLS.Local006.ChartMajorantH
  QuantumNLS.Local006.WordExpansionI QuantumNLS.Local006.DegreeRegroupI
  QuantumNLS.Local006.CollectiveF
  QuantumNLS.ResetFreeResolventLOCAL001 QuantumNLS.ResetFreeResolventLOCAL001.CompletionB

variable {L r κ : ℝ} [Fact (0 < L)]

lemma sourceAbs_norm_sum (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (kind : WordKind) (u : ScalarInterval L)
    (hu : wordConstant L r κ * ‖u‖ < 1 / 8) :
    (∑' d, ‖sourceAbs hL hκ hr hs kind u d‖) ≤ 1 / 7 := by
  have hq : 0 ≤ wordConstant L r κ * ‖u‖ :=
    mul_nonneg (wordConstant_pos hL hr hκ).le (norm_nonneg _)
  have hg : Summable (fun d : ℕ => (1 / 8 : ℝ) ^ (d + 1)) := by
    simpa only [pow_succ] using
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 8)
        (by norm_num : (1 / 8 : ℝ) < 1)).mul_right (1 / 8)
  calc
    _ ≤ ∑' d : ℕ, (1 / 8 : ℝ) ^ (d + 1) :=
      (sourceAbs_summable hL hκ hr hs kind u hu).1.tsum_le_tsum
        (fun d => (sourceAbs_spec hL hκ hr hs kind u d).2.1.trans
          (pow_le_pow_left₀ hq hu.le _)) hg
    _ = 1 / 7 := by
      simp only [pow_succ, tsum_mul_right]
      rw [tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 8)
        (by norm_num : (1 / 8 : ℝ) < 1)]
      norm_num

def physicalEnvelope (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (u : ScalarInterval L) : ℕ → Mixed :=
  degreeEnvelope (sourceAbs hL hκ hr hs .projection u) (sourceAbs hL hκ hr hs .moment u)

def physicalCoefficient (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (u : ScalarInterval L) : ℕ → Mixed :=
  degreeCoefficient (actualCoeff hL hκ hr hs .projection u) (actualCoeff hL hκ hr hs .moment u)

lemma actualCoeff_majorized (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (kind : WordKind) (u : ScalarInterval L) (d : ℕ) :
    Majorizes (sourceAbs hL hκ hr hs kind u d) (matrix (actualCoeff hL hκ hr hs kind u d)) := by
  intro n i j
  rw [(actualCoeff_spec hL hκ hr hs kind u d).1]
  exact (sourceAbs_spec hL hκ hr hs kind u d).2.2.2 n i j

/-- Actual normalized coefficients, grouped by total source degree. No
summability hypothesis on the physical input or conclusion about derivatives
is assumed. The positive Fourier envelope is retained in each degree. -/
theorem physical_regroup (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (u : ScalarInterval L)
    (hu : wordConstant L r κ * ‖u‖ < 1 / 8) :
    Summable (fun d => ‖physicalEnvelope hL hκ hr hs u d‖) ∧
      Summable (fun d => ‖physicalCoefficient hL hκ hr hs u d‖) ∧
      HasSum (physicalEnvelope hL hκ hr hs u) (normalizedEnvelope hL hκ hr hs u) ∧
      HasSum (physicalCoefficient hL hκ hr hs u) (normalizedSource hL hκ hr hs u) ∧
      ∀ d, Positive (physicalEnvelope hL hκ hr hs u d) ∧
        Majorizes (physicalEnvelope hL hκ hr hs u d)
          (matrix (physicalCoefficient hL hκ hr hs u d)) := by
  have hn := sourceAbs_norm_sum hL hκ hr hs .projection u hu
  have hsmall : 2 * (∑' d, ‖sourceAbs hL hκ hr hs .projection u d‖) < 1 := by linarith
  exact regroup_majorized _ _ _ _
    (sourceAbs_summable hL hκ hr hs .projection u hu).1
    (sourceAbs_summable hL hκ hr hs .moment u hu).1
    (fun d => (sourceAbs_spec hL hκ hr hs .projection u d).1)
    (fun d => (sourceAbs_spec hL hκ hr hs .moment u d).1)
    (actualCoeff_majorized hL hκ hr hs .projection u)
    (actualCoeff_majorized hL hκ hr hs .moment u) hsmall

/-- One full ball carries the actual analytic chart, its absolutely convergent
total-degree series, and coefficientwise absolute Fourier-path envelopes. -/
theorem chart_degree_regroup (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ G : L2T L → Seq,
      AnalyticOnNhd ℝ G (ball 0 ρ) ∧ ∀ u ∈ ball (0 : L2T L) ρ,
        (∀ n, G u n = scalarG L κ r u n) ∧
        Summable (fun d => ‖physicalEnvelope hL hκ hr hs (toInterval L u) d‖) ∧
        Summable (fun d => ‖physicalCoefficient hL hκ hr hs (toInterval L u) d‖) ∧
        HasSum (physicalCoefficient hL hκ hr hs (toInterval L u))
          (normalizedSource hL hκ hr hs (toInterval L u)) ∧
        HasSum (fun d => factor L κ • (physicalCoefficient hL hκ hr hs (toInterval L u) d).2.2)
          (G u) ∧
        ∀ d, Positive (physicalEnvelope hL hκ hr hs (toInterval L u) d) ∧
          Majorizes (physicalEnvelope hL hκ hr hs (toInterval L u) d)
            (matrix (physicalCoefficient hL hκ hr hs (toInterval L u) d)) := by
  obtain ⟨ρ0, hρ0, G, hG, hGa⟩ := actual_chart_majorant_stage hL hκ hr hs
  let C := wordConstant L r κ
  have hC : 0 < C := wordConstant_pos hL hr hκ
  let ρ := min ρ0 (1 / (8 * C))
  have hρ : 0 < ρ := lt_min hρ0 (by positivity)
  have hsub : ball (0 : L2T L) ρ ⊆ ball 0 ρ0 := ball_subset_ball (min_le_left _ _)
  refine ⟨ρ, hρ, G, hG.mono hsub, ?_⟩
  intro u hu
  have hq : C * ‖toInterval L u‖ < 1 / 8 := by
    rw [norm_toInterval]
    have h := mul_lt_mul_of_pos_left
      ((mem_ball_zero_iff.mp hu).trans_le (min_le_right _ _)) hC
    have he : C * (1 / (8 * C)) = 1 / 8 := by field_simp
    rwa [he] at h
  obtain ⟨henv, hcoeff, -, hsum, hmajor⟩ := physical_regroup hL hκ hr hs (toInterval L u) hq
  have hchart := hGa u (hsub hu)
  let extract : Mixed →L[ℂ] Seq := (ContinuousLinearMap.snd ℂ Seq2 Seq2).comp
    (ContinuousLinearMap.snd ℂ (SeqInf × SeqInf) (Seq2 × Seq2))
  have he := (extract.hasSum hsum).const_smul (factor L κ)
  refine ⟨hchart.1, henv, hcoeff, hsum, ?_, hmajor⟩
  change HasSum (fun d => factor L κ • (physicalCoefficient hL hκ hr hs (toInterval L u) d).2.2)
    (factor L κ • (normalizedSource hL hκ hr hs (toInterval L u)).2.2) at he
  rwa [← hchart.2.2.2.2.2.1] at he

end QuantumNLS.Local006.PhysicalRegroupI
#print axioms QuantumNLS.Local006.PhysicalRegroupI.physical_regroup
#print axioms QuantumNLS.Local006.PhysicalRegroupI.chart_degree_regroup

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local006.PhysicalRegroupI." ||
        n.toString.startsWith "_private.QuantumNLS.Local006PhysicalRegroupI" then
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
  Lean.logInfo m!"Local006PhysicalRegroupI audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
