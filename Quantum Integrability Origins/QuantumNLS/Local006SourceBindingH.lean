import QuantumNLS.Local006SolidMajorantH

/-! The positive degree sum is the actual centered frozen source compression.
This is an operator-series identification, not a scalar size bound. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open scoped BigOperators ENNReal
namespace QuantumNLS.Local006.SourceBindingH
open QuantumNLS.Local005 QuantumNLS.Local005.SourceC QuantumNLS.Local005.SourceD
  QuantumNLS.Local006.CoefficientLiftE QuantumNLS.Local006.SequenceAlgebraE
  QuantumNLS.Local006.SequenceEvaluationE QuantumNLS.Local006.PositiveMajorantG
  QuantumNLS.Local006.SourceMajorantG QuantumNLS.Local006.NormalizedMajorantG
  QuantumNLS.Local006.SolidMajorantH
  QuantumNLS.ResetFreeResolventLOCAL001 QuantumNLS.ResetFreeResolventLOCAL001.CompletionB

variable {L r κ : ℝ} [Fact (0 < L)]

def sourceSum (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r) (hs : r < spacing L / 2)
    (kind : WordKind) (u : ScalarInterval L) : Mixed :=
  ∑' d, actualCoeff hL hκ hr hs kind u d

def sourceEnvelope (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r) (hs : r < spacing L / 2)
    (kind : WordKind) (u : ScalarInterval L) : Mixed :=
  ∑' d, sourceAbs hL hκ hr hs kind u d

lemma sourceSum_majorizes (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (kind : WordKind) (u : ScalarInterval L)
    (hu : wordConstant L r κ * ‖u‖ < 1 / 8) :
    Positive (sourceEnvelope hL hκ hr hs kind u) ∧
      ‖sourceEnvelope hL hκ hr hs kind u‖ ≤ 1 / 7 ∧
      ‖sourceSum hL hκ hr hs kind u‖ ≤ 1 / 7 ∧
      Majorizes (sourceEnvelope hL hκ hr hs kind u) (matrix (sourceSum hL hκ hr hs kind u)) := by
  have ha := (sourceAbs_summable hL hκ hr hs kind u hu).1
  have hb := actualCoeff_summable hL hκ hr hs kind u hu
  have hm : Majorizes (sourceEnvelope hL hκ hr hs kind u) (matrix (sourceSum hL hκ hr hs kind u)) := by
    apply majorizes_tsum ha hb
    intro d n i j
    rw [(actualCoeff_spec hL hκ hr hs kind u d).1]
    exact (sourceAbs_spec hL hκ hr hs kind u d).2.2.2 n i j
  have hp : Positive (sourceEnvelope hL hκ hr hs kind u) :=
    positive_tsum ha.of_norm (fun d => (sourceAbs_spec hL hκ hr hs kind u d).1)
  have hn := (sourceAbs_summable hL hκ hr hs kind u hu).2
  obtain ⟨b, he, hbn⟩ := solid_lift hp hm
  have heq : b = sourceSum hL hκ hr hs kind u := matrix_ext (fun n i j => congrFun (congrFun (he n) i) j)
  exact ⟨hp, hn, heq ▸ hbn.trans hn, hm⟩

/-- The degree-zero term is removed explicitly; it is never silently dropped. -/
lemma sourceSum_entry (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (kind : WordKind) (u : ScalarInterval L)
    (hu : wordConstant L r κ * ‖u‖ < 1 / 8)
    (n : ℤ)
    (hsource : HasSum (sourceWord hL hκ hr hs kind u n)
      (sourceCompressed (κ := κ) (r := r) kind u n)) (i j : Fin 2) :
    matrix (sourceSum hL hκ hr hs kind u) n i j =
      entryFunctional n i j (sourceCompressed (κ := κ) (r := r) kind u n) -
        entryFunctional n i j (sourceWord hL hκ hr hs kind u n 0) := by
  have h := (entryFunctional n i j).hasSum hsource
  have ht : HasSum (fun d : ℕ => entryFunctional n i j
      (sourceWord hL hκ hr hs kind u n (d + 1)))
      (entryFunctional n i j (sourceCompressed (κ := κ) (r := r) kind u n) -
        entryFunctional n i j (sourceWord hL hκ hr hs kind u n 0)) := by
    simpa using (hasSum_nat_add_iff' 1).mpr h
  have hm := (entryCLM n i j).hasSum (actualCoeff_summable hL hκ hr hs kind u hu).of_norm.hasSum
  simp only [entryCLM_apply] at hm
  have hh : (fun d => matrix (actualCoeff hL hκ hr hs kind u d) n i j) =
      fun d => entryFunctional n i j (sourceWord hL hκ hr hs kind u n (d + 1)) := by
    funext d
    rw [(actualCoeff_spec hL hκ hr hs kind u d).1]
    unfold coefficient
    rw [orderedSourceWord_repeat]
  rw [hh] at hm
  exact hm.unique ht

/-- One full ball identifies both source sums with the actual frozen S/K
compressions and supplies their absolute Fourier path envelopes. -/
theorem actual_source_majorants (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ u : ScalarInterval L, ‖u‖ < ρ → ∀ kind : WordKind,
      Positive (sourceEnvelope hL hκ hr hs kind u) ∧
      ‖sourceEnvelope hL hκ hr hs kind u‖ ≤ 1 / 7 ∧
      ‖sourceSum hL hκ hr hs kind u‖ ≤ 1 / 7 ∧
      Majorizes (sourceEnvelope hL hκ hr hs kind u)
        (fun n i j => entryFunctional n i j (sourceCompressed (κ := κ) (r := r) kind u n) -
          entryFunctional n i j (sourceWord hL hκ hr hs kind u n 0)) ∧
      ∀ n i j, matrix (sourceSum hL hκ hr hs kind u) n i j =
        entryFunctional n i j (sourceCompressed (κ := κ) (r := r) kind u n) -
          entryFunctional n i j (sourceWord hL hκ hr hs kind u n 0) := by
  obtain ⟨ρ0, hρ0, hsource⟩ := source_series_on_ball hL hκ hr hs
  let C := wordConstant L r κ
  have hC : 0 < C := wordConstant_pos hL hr hκ
  refine ⟨min ρ0 (1 / (8 * C)), lt_min hρ0 (by positivity), ?_⟩
  intro u hu kind
  have hu0 := hu.trans_le (min_le_left _ _)
  have hq : C * ‖u‖ < 1 / 8 := by
    have h := mul_lt_mul_of_pos_left (hu.trans_le (min_le_right _ _)) hC
    have he : C * (1 / (8 * C)) = 1 / 8 := by field_simp
    rwa [he] at h
  obtain ⟨hp, hn, hsn, hm⟩ := sourceSum_majorizes hL hκ hr hs kind u hq
  have he := fun n i j => sourceSum_entry hL hκ hr hs kind u hq n (hsource n u hu0 kind) i j
  refine ⟨hp, hn, hsn, ?_, he⟩
  intro n i j
  have h := hm n i j
  rw [he n i j] at h
  exact h

end QuantumNLS.Local006.SourceBindingH
#print axioms QuantumNLS.Local006.SourceBindingH.actual_source_majorants

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local006.SourceBindingH." ||
        n.toString.startsWith "_private.QuantumNLS.Local006SourceBindingH" then
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
  Lean.logInfo m!"Local006SourceBindingH audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
