import QuantumNLS.Local006CompressionE

/-! LOCAL-006, lifting the actual ordered source coefficients into their Banach
sequence targets. Bounds and absolute majorants are supplied by the accepted
LOCAL-005 theorem. The scientific parameters remain exactly those of the
source. This module does not assert convergence of the normalized chart. -/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Metric
open scoped ENNReal InnerProductSpace BigOperators

namespace QuantumNLS.Local006.CoefficientLiftE
open QuantumNLS.LocalSpectral QuantumNLS.Local005 QuantumNLS.Local005.SourceC QuantumNLS.Local005.SourceD
  QuantumNLS.ResetFreeResolventLOCAL001 QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
  QuantumNLS.ResolventWordEstimateStage2LOCAL005

abbrev Seq2 := lp (fun _ : ℤ => ℂ) 2
abbrev SeqInf := lp (fun _ : ℤ => ℂ) ∞

/-- A square-summable absolute majorant gives an actual Banach-valued sequence,
with the same collective norm bound. -/
theorem lift_l2 (f : ℤ → ℂ) (M : ℤ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hs : Summable fun n => M n ^ 2)
    (hb : ∑' n, M n ^ 2 ≤ B ^ 2) (hf : ∀ n, ‖f n‖ ≤ M n) :
    ∃ F : Seq2, (∀ n, F n = f n) ∧ ‖F‖ ≤ B := by
  have hp : ∀ n, ‖f n‖ ^ 2 ≤ M n ^ 2 := by
    intro n
    exact pow_le_pow_left₀ (norm_nonneg _) (hf n) 2
  have hfs : Summable fun n => ‖f n‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _) hp hs
  have hmem : Memℓp f 2 := by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hfs
  refine ⟨⟨f, hmem⟩, fun n => rfl, ?_⟩
  apply lp.norm_le_of_tsum_le (by norm_num) hB
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (hfs.tsum_le_tsum hp hs).trans hb

/-- A uniform absolute majorant gives the actual bounded sequence. -/
theorem lift_linf (f : ℤ → ℂ) {B : ℝ} (hB : 0 ≤ B) (hf : ∀ n, ‖f n‖ ≤ B) :
    ∃ F : SeqInf, (∀ n, F n = f n) ∧ ‖F‖ ≤ B := by
  have hmem : Memℓp f ∞ := memℓp_infty ⟨B, by rintro _ ⟨n, rfl⟩; exact hf n⟩
  exact ⟨⟨f, hmem⟩, fun n => rfl, lp.norm_le_of_forall_le hB hf⟩

variable {L κ r : ℝ} [Fact (0 < L)]

/-- An actual ordered source coefficient, evaluated in the ordered free basis. -/
def coefficient (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (k : ℕ) (kind : WordKind)
    (u : Fin k → ScalarInterval L) (i j : Fin 2) (n : ℤ) : ℂ :=
  entryFunctional n i j
    (orderedSourceWord hL hκ hr hsmall kind (extendInputs u) n k)

/-- All positive source degrees, now as actual elements of the collective
Banach sequence spaces, retaining the same common absolute majorant for all
four entries. Constants, zero entries, and sequence membership are conclusions.
No finite-support or summability hypothesis is added to the physical inputs. -/
theorem source_coefficients_sequence_targets (hL : 0 < L) (hκ : 0 < κ)
    (hr : 0 < r) (hsmall : r < spacing L / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ), 1 ≤ k →
      ∀ (u : Fin k → ScalarInterval L) (kind : WordKind),
      (∀ n i j, ‖coefficient hL hκ hr hsmall k kind u i j n‖ ≤
        physicalMajorant L r κ kind k (extendInputs u) n) ∧
      (Odd k →
        (∀ n j, coefficient hL hκ hr hsmall k kind u j j n = 0) ∧
        ∀ i j, ∃ F : Seq2,
          (∀ n, F n = coefficient hL hκ hr hsmall k kind u i j n) ∧
          ‖F‖ ≤ C ^ k * ∏ t : Fin k, ‖u t‖) ∧
      (Even k →
        (∀ n i j, i ≠ j → coefficient hL hκ hr hsmall k kind u i j n = 0) ∧
        ∀ i j, ∃ F : SeqInf,
          (∀ n, F n = coefficient hL hκ hr hsmall k kind u i j n) ∧
          ‖F‖ ≤ C ^ k * ∏ t : Fin k, ‖u t‖) := by
  obtain ⟨C, hC, -, -, -, -, hb⟩ :=
    QuantumNLS.Local005.SourceD.reset_resolvent_word hL hκ hr hsmall
  refine ⟨C, hC, ?_⟩
  intro k hk u kind
  have h := hb k hk u kind
  have hnorm (n : ℤ) (i j : Fin 2) :
      ‖coefficient hL hκ hr hsmall k kind u i j n‖ ≤
        physicalMajorant L r κ kind k (extendInputs u) n := (h.1 n i j).2.2
  have hB : 0 ≤ C ^ k * ∏ t : Fin k, ‖u t‖ := by positivity
  refine ⟨hnorm, ?_, ?_⟩
  · intro ho
    have hh := h.2
    rw [if_pos ho] at hh
    refine ⟨hh.1, fun i j => ?_⟩
    exact lift_l2 _ _ hB hh.2.1 hh.2.2 (fun n => hnorm n i j)
  · intro he
    have hno : ¬ Odd k := Nat.not_odd_iff_even.mpr he
    have hh := h.2
    rw [if_neg hno] at hh
    refine ⟨hh.1, fun i j => ?_⟩
    exact lift_linf _ hB (fun n => (hnorm n i j).trans (hh.2 n))

end QuantumNLS.Local006.CoefficientLiftE

#print axioms QuantumNLS.Local006.CoefficientLiftE.lift_l2
#print axioms QuantumNLS.Local006.CoefficientLiftE.lift_linf
#print axioms QuantumNLS.Local006.CoefficientLiftE.source_coefficients_sequence_targets

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local006.CoefficientLiftE." ||
        n.toString.startsWith "_private.QuantumNLS.Local006CoefficientLiftE" then
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
  Lean.logInfo m!"Local006CoefficientLiftE audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
