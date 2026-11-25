import QuantumNLS.Local006SourceMajorantG

/-! Summing the actual source absolute Fourier majorants on a full ball,
then propagating them through both binomial normalization factors. This module
does not identify a differentiated or transposed normalized Taylor series. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open scoped BigOperators ENNReal
namespace QuantumNLS.Local006.NormalizedMajorantG
open QuantumNLS.Local005 QuantumNLS.Local005.SourceD
  QuantumNLS.Local006.CoefficientLiftE QuantumNLS.Local006.SequenceAlgebraE
  QuantumNLS.Local006.SequenceEvaluationE QuantumNLS.Local006.PositiveMajorantG
  QuantumNLS.Local006.SourceMajorantG
  QuantumNLS.ResetFreeResolventLOCAL001 QuantumNLS.ResetFreeResolventLOCAL001.CompletionB

variable {L r κ : ℝ} [Fact (0 < L)]

def sourceAbs (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r) (hs : r < spacing L / 2)
    (kind : WordKind) (u : ScalarInterval L) (d : ℕ) : Mixed :=
  Classical.choose (physical_majorant hL hκ hr hs (by omega : 1 ≤ d + 1)
    kind (fun _ : Fin (d + 1) => u))

lemma sourceAbs_spec (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r) (hs : r < spacing L / 2)
    (kind : WordKind) (u : ScalarInterval L) (d : ℕ) :
    Positive (sourceAbs hL hκ hr hs kind u d) ∧
      ‖sourceAbs hL hκ hr hs kind u d‖ ≤ (wordConstant L r κ * ‖u‖) ^ (d + 1) ∧
      (∀ n i j, matrix (sourceAbs hL hκ hr hs kind u d) n i j =
        if i = componentAfter (d + 1) j then
          (physicalMajorant L r κ kind (d + 1)
            (extendInputs (fun _ : Fin (d + 1) => u)) n : ℂ) else 0) ∧
      Majorizes (sourceAbs hL hκ hr hs kind u d)
        (fun n i j => coefficient hL hκ hr hs (d + 1) kind
          (fun _ : Fin (d + 1) => u) i j n) := by
  have h := Classical.choose_spec (physical_majorant hL hκ hr hs (by omega : 1 ≤ d + 1)
    kind (fun _ : Fin (d + 1) => u))
  simpa only [sourceAbs, Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow] using h

lemma sourceAbs_projection_zero (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (u : ScalarInterval L) : sourceAbs hL hκ hr hs .projection u 0 = 0 :=
  first_projection_majorant_zero hL hκ hr hs _ _ (sourceAbs_spec hL hκ hr hs .projection u 0).2.2.1

lemma sourceAbs_summable (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (kind : WordKind) (u : ScalarInterval L)
    (hu : wordConstant L r κ * ‖u‖ < 1 / 8) :
    Summable (fun d => ‖sourceAbs hL hκ hr hs kind u d‖) ∧
      ‖∑' d, sourceAbs hL hκ hr hs kind u d‖ ≤ 1 / 7 := by
  have hq : 0 ≤ wordConstant L r κ * ‖u‖ :=
    mul_nonneg (wordConstant_pos hL hr hκ).le (norm_nonneg _)
  have hg : Summable (fun d : ℕ => (1 / 8 : ℝ) ^ (d + 1)) := by
    simpa only [pow_succ] using
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 8) (by norm_num : (1 / 8 : ℝ) < 1)).mul_right (1 / 8)
  have hb : ∀ d, ‖sourceAbs hL hκ hr hs kind u d‖ ≤ (1 / 8 : ℝ) ^ (d + 1) := by
    intro d
    exact (sourceAbs_spec hL hκ hr hs kind u d).2.1.trans (pow_le_pow_left₀ hq hu.le _)
  have hsum := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hg
  refine ⟨hsum, (norm_tsum_le_tsum_norm hsum).trans ?_⟩
  calc
    ∑' d, ‖sourceAbs hL hκ hr hs kind u d‖ ≤ ∑' d : ℕ, (1 / 8 : ℝ) ^ (d + 1) :=
      hsum.tsum_le_tsum hb hg
    _ = 1 / 7 := by
      simp only [pow_succ, tsum_mul_right]
      rw [tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 8) (by norm_num : (1 / 8 : ℝ) < 1)]
      norm_num

/-- One positive full radius supports the actual absolute source-word sums
and the complete double series of positive normalization words. -/
theorem source_normalization_majorants (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ u : ScalarInterval L, ‖u‖ < ρ →
      ∃ a b : Mixed,
        a = ∑' d, sourceAbs hL hκ hr hs .projection u d ∧
        b = ∑' d, sourceAbs hL hκ hr hs .moment u d ∧
        Positive a ∧ Positive b ∧ ‖a‖ ≤ 1 / 7 ∧ ‖b‖ ≤ 1 / 7 ∧
        Summable (fun d => ‖sourceAbs hL hκ hr hs .projection u d‖) ∧
        Summable (fun d => ‖sourceAbs hL hκ hr hs .moment u d‖) ∧
        Summable (fun jl : ℕ × ℕ => ‖mul (mul (power a jl.1) b) (power a jl.2)‖) ∧
        ∀ n i j, Summable (fun jl : ℕ × ℕ =>
          ‖matrix (mul (mul (power a jl.1) b) (power a jl.2)) n i j‖) := by
  let C := wordConstant L r κ
  have hC : 0 < C := wordConstant_pos hL hr hκ
  refine ⟨1 / (8 * C), by positivity, ?_⟩
  intro u hu
  have hq : C * ‖u‖ < 1 / 8 := by
    have h := mul_lt_mul_of_pos_left hu hC
    have he : C * (1 / (8 * C)) = 1 / 8 := by field_simp
    rwa [he] at h
  obtain ⟨hsa, hna⟩ := sourceAbs_summable hL hκ hr hs .projection u hq
  obtain ⟨hsb, hnb⟩ := sourceAbs_summable hL hκ hr hs .moment u hq
  let a := ∑' d, sourceAbs hL hκ hr hs .projection u d
  let b := ∑' d, sourceAbs hL hκ hr hs .moment u d
  have ha : 2 * ‖a‖ < 1 := by dsimp [a]; linarith
  exact ⟨a, b, rfl, rfl,
    positive_tsum hsa.of_norm (fun d => (sourceAbs_spec hL hκ hr hs .projection u d).1),
    positive_tsum hsb.of_norm (fun d => (sourceAbs_spec hL hκ hr hs .moment u d).1),
    hna, hnb, hsa, hsb, normalization_words_summable a b ha,
    normalization_coordinate_summable a b ha⟩

end QuantumNLS.Local006.NormalizedMajorantG
#print axioms QuantumNLS.Local006.NormalizedMajorantG.sourceAbs_spec
#print axioms QuantumNLS.Local006.NormalizedMajorantG.source_normalization_majorants

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local006.NormalizedMajorantG." ||
        n.toString.startsWith "_private.QuantumNLS.Local006NormalizedMajorantG" then
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
  Lean.logInfo m!"Local006NormalizedMajorantG audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
