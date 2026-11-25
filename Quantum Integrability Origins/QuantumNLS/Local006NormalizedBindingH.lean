import QuantumNLS.Local006OperatorMatrixH
import QuantumNLS.Local006BinomialBindingH

/-! Absolute source Fourier envelopes bound the actual fully normalized
spectral matrix on one full ball. Taylor-degree regrouping and the differentiated
independent-slot Fourier kernel identification remain separate obligations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Metric
open scoped BigOperators ENNReal Matrix.Norms.Elementwise
namespace QuantumNLS.Local006.NormalizedBindingH
open QuantumNLS.LocalSpectral QuantumNLS.Local003Analytic QuantumNLS.Local003Isometry QuantumNLS.Local005
  QuantumNLS.Local005.SourceC QuantumNLS.Local005.SourceD
  QuantumNLS.Local006.CoefficientLiftE QuantumNLS.Local006.SequenceAlgebraE
  QuantumNLS.Local006.SequenceEvaluationE QuantumNLS.Local006.PositiveMajorantG
  QuantumNLS.Local006.SourceBindingH QuantumNLS.Local006.OperatorMatrixH
  QuantumNLS.Local006.BinomialBindingH QuantumNLS.Local006.CompressionE
  QuantumNLS.ResetFreeResolventLOCAL001 QuantumNLS.ResetFreeResolventLOCAL001.CompletionB

variable {L r κ : ℝ} [Fact (0 < L)]

def normalizedSource (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (u : ScalarInterval L) : Mixed :=
  mul (mul (inverseSqrt (sourceSum hL hκ hr hs .projection u))
    (sourceSum hL hκ hr hs .moment u))
    (inverseSqrt (sourceSum hL hκ hr hs .projection u))

def normalizedEnvelope (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (u : ScalarInterval L) : Mixed :=
  ∑' jl, envelopeWord (sourceEnvelope hL hκ hr hs .projection u)
    (sourceEnvelope hL hκ hr hs .moment u) jl

/-- An actual-map majorant stage: every source envelope is the frozen absolute
Fourier path sum; all normalization words sum absolutely in the mixed space;
and their sum dominates the actual normalized spectral matrix. -/
theorem actual_normalized_majorant (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ u : ScalarInterval L, ‖u‖ < ρ →
      Positive (normalizedEnvelope hL hκ hr hs u) ∧
      Summable (fun jl => ‖envelopeWord (sourceEnvelope hL hκ hr hs .projection u)
        (sourceEnvelope hL hκ hr hs .moment u) jl‖) ∧
      Summable (fun jl => ‖normalizedWord (sourceSum hL hκ hr hs .projection u)
        (sourceSum hL hκ hr hs .moment u) jl‖) ∧
      HasSum (normalizedWord (sourceSum hL hκ hr hs .projection u)
        (sourceSum hL hκ hr hs .moment u)) (normalizedSource hL hκ hr hs u) ∧
      Majorizes (normalizedEnvelope hL hκ hr hs u)
        (fun n => opMatrix (Bf L κ (u : ℝ → ℂ) n r -
          (pm L n : ℂ) • (1 : E2 →L[ℂ] E2))) ∧
      ∀ n, matrix (normalizedSource hL hκ hr hs u) n =
        opMatrix (Bf L κ (u : ℝ → ℂ) n r - (pm L n : ℂ) • (1 : E2 →L[ℂ] E2)) := by
  obtain ⟨ρ0, hρ0, hsource⟩ := actual_source_majorants hL hκ hr hs
  have hr2 : r < 2 * Real.pi / L := by
    convert hs using 1
    unfold spacing
    ring
  refine ⟨min ρ0 (goodRadius κ L r), lt_min hρ0 (goodRadius_pos κ L r), ?_⟩
  intro u hu
  have hu0 := hu.trans_le (min_le_left _ _)
  have hug := hu.trans_le (min_le_right _ _)
  obtain ⟨ha, hna, hns, hma, hsa⟩ := hsource u hu0 .projection
  obtain ⟨hb, hnb, hnk, hmb, hsk⟩ := hsource u hu0 .moment
  let s := sourceSum hL hκ hr hs .projection u
  let k := sourceSum hL hκ hr hs .moment u
  let a := sourceEnvelope hL hκ hr hs .projection u
  let b := sourceEnvelope hL hκ hr hs .moment u
  have hasmall : 2 * ‖a‖ < 1 := by dsimp [a]; linarith
  have hssmall : 2 * ‖s‖ < 1 := by dsimp [s]; linarith
  have hmas : Majorizes a (matrix s) := by
    intro n i j
    have h := hma n i j
    dsimp only at h
    rw [← hsa n i j] at h
    exact h
  have hmbk : Majorizes b (matrix k) := by
    intro n i j
    have h := hmb n i j
    dsimp only at h
    rw [← hsk n i j] at h
    exact h
  obtain ⟨hw, hsum, hp, hm⟩ := normalization_majorant
    (a := a) (b := b) (s := s) (k := k) ha hb hmas hmbk hasmall
  have hsM (n : ℤ) : matrix s n = opMatrix (compressionMatrix L κ (u : ℝ → ℂ) n r - 1) := by
    ext i j
    change matrix (sourceSum hL hκ hr hs .projection u) n i j = _
    rw [hsa n i j, sourceCompressed_projection_entry hL hr hs,
      sourceWord_zero_entry hL hκ hr hs]
    simp only [map_sub, opMatrix_one, Matrix.sub_apply, Matrix.one_apply]
  have hkM (n : ℤ) : matrix k n = opMatrix (momentMatrix L κ (u : ℝ → ℂ) n r) := by
    ext i j
    change matrix (sourceSum hL hκ hr hs .moment u) n i j = _
    rw [hsk n i j, sourceCompressed_moment_entry hL hr hs,
      sourceWord_zero_entry hL hκ hr hs, sub_zero]
  have hiM (n : ℤ) : matrix (inverseSqrt s) n =
      opMatrix (invSqrtM (compressionMatrix L κ (u : ℝ → ℂ) n r)) := by
    have h1 := matrix_inverse_sqrt_hasSum s hssmall n
    have h2 := opMatrix.hasSum (hasSum_invSqrtM (ctx_of_ball hL hr hr2 n u hug).hsmall)
    simp only [map_smul, opMatrix_pow, ← hsM n] at h2
    exact h1.unique h2
  have he (n : ℤ) : matrix (normalizedSource hL hκ hr hs u) n =
      opMatrix (Bf L κ (u : ℝ → ℂ) n r - (pm L n : ℂ) • (1 : E2 →L[ℂ] E2)) := by
    rw [reduced_matrix_compression hL hr hr2 n u (ctx_of_ball hL hr hr2 n u hug),
      opMatrix_mul, opMatrix_mul]
    change matrix (mul (mul (inverseSqrt s) k) (inverseSqrt s)) n = _
    rw [matrix_mul, matrix_mul, hiM n, hkM n]
  refine ⟨hp, normalization_words_summable a b hasmall, hw, hsum, ?_, he⟩
  intro n i j
  have h := hm n i j
  change ‖matrix (normalizedSource hL hκ hr hs u) n i j‖ ≤ _ at h
  rw [he n] at h
  exact h

end QuantumNLS.Local006.NormalizedBindingH
#print axioms QuantumNLS.Local006.NormalizedBindingH.actual_normalized_majorant

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local006.NormalizedBindingH." ||
        n.toString.startsWith "_private.QuantumNLS.Local006NormalizedBindingH" then
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
  Lean.logInfo m!"Local006NormalizedBindingH audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
