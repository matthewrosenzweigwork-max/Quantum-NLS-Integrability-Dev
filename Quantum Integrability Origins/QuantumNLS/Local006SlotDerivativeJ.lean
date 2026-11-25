import QuantumNLS.Local006IndependentSlotsJ
import QuantumNLS.Local006TransposeMajorantG

/-! Exact differentiated independent source slots and positive Fourier-path
 envelopes. The formulas are in the actual mixed sequence target. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Metric Set
open scoped BigOperators ENNReal
namespace QuantumNLS.Local006.SlotDerivativeJ
open QuantumNLS.Local005 QuantumNLS.Local005.SourceC QuantumNLS.Local005.SourceD
  QuantumNLS.Local006.CoefficientLiftE QuantumNLS.Local006.SequenceAlgebraE
  QuantumNLS.Local006.SequenceEvaluationE QuantumNLS.Local006.PositiveMajorantG
  QuantumNLS.Local006.SourceMajorantG QuantumNLS.Local006.SolidMajorantH
  QuantumNLS.Local006.BinomialBindingH QuantumNLS.Local006.IndependentSlotsJ
  QuantumNLS.ResetFreeResolventLOCAL001 QuantumNLS.ResetFreeResolventLOCAL001.CompletionB

variable {L r κ : ℝ} [Fact (0 < L)]

def diagonal (k : ℕ) : ScalarInterval L →L[ℝ] (Fin k → ScalarInterval L) :=
  ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℝ (ScalarInterval L))

def sourceDerivative (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (kind : WordKind) (u : ScalarInterval L) (d : ℕ) :
    ScalarInterval L →L[ℝ] Mixed :=
  (sourceMultilinear hL hκ hr hs (Nat.succ_pos d) kind).linearDeriv (fun _ => u) ∘L diagonal (d+1)

lemma sourceDerivative_apply (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (kind : WordKind) (u v : ScalarInterval L) (d : ℕ) :
    sourceDerivative hL hκ hr hs kind u d v =
      ∑ i : Fin (d+1), sourceMultilinear hL hκ hr hs (Nat.succ_pos d) kind
        (Function.update (fun _ => u) i v) := by
  simp [sourceDerivative, ContinuousMultilinearMap.linearDeriv_apply, diagonal]

/-- Differentiate the genuine diagonal source coefficient. Every occurrence
of the input is retained, with its original order and conjugation. -/
theorem actualCoeff_hasFDerivAt (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (kind : WordKind) (u : ScalarInterval L) (d : ℕ) :
    HasFDerivAt (fun v => actualCoeff hL hκ hr hs kind v d)
      (sourceDerivative hL hκ hr hs kind u d) u := by
  have h := (sourceMultilinear hL hκ hr hs (Nat.succ_pos d) kind).hasFDerivAt (fun _ => u)
  have hc := h.comp u (diagonal (L := L) (d+1)).hasFDerivAt
  have hd : HasFDerivAt
      (fun v => sourceMultilinear hL hκ hr hs (Nat.succ_pos d) kind (fun _ => v))
      (sourceDerivative hL hκ hr hs kind u d) u := hc
  simpa only [sourceMultilinear_diagonal] using hd

/-- The actual differentiated Fourier entries, expressed in independent
physical slots. The series over each path is absolutely convergent by LOCAL-005. -/
theorem sourceDerivative_fourier (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (kind : WordKind) (u v : ScalarInterval L) (d : ℕ)
    (n : ℤ) (a b : Fin 2) :
    matrix (sourceDerivative hL hκ hr hs kind u d v) n a b =
      ∑ i : Fin (d+1), coefficientEntry L r κ kind (d+1)
        (physicalInputs b (Function.update (fun _ => u) i v)) n a b := by
  rw [sourceDerivative_apply]
  rw [← entryCLM_apply n a b, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [entryCLM_apply, sourceMultilinear_apply]
  exact (orderedSourceWord_entry_posdegree hL hκ hr hs n _ (Nat.succ_pos d) kind a b).trans
    (by simp only [extendInputs_apply_fin])

def slotEnvelope (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) {k : ℕ} (hk : 1 ≤ k) (kind : WordKind)
    (u : Fin k → ScalarInterval L) : Mixed :=
  (physical_majorant hL hκ hr hs hk kind u).choose

lemma slotEnvelope_spec (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) {k : ℕ} (hk : 1 ≤ k) (kind : WordKind)
    (u : Fin k → ScalarInterval L) :
    Positive (slotEnvelope hL hκ hr hs hk kind u) ∧
      ‖slotEnvelope hL hκ hr hs hk kind u‖ ≤ wordConstant L r κ ^ k * ∏ t, ‖u t‖ ∧
      (∀ n a b, matrix (slotEnvelope hL hκ hr hs hk kind u) n a b =
        if a = componentAfter k b then
          (physicalMajorant L r κ kind k (extendInputs u) n : ℂ) else 0) ∧
      Majorizes (slotEnvelope hL hκ hr hs hk kind u)
        (matrix (sourceMultilinear hL hκ hr hs hk kind u)) := by
  have h := (physical_majorant hL hκ hr hs hk kind u).choose_spec
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  intro n a b
  rw [sourceMultilinear_apply]
  exact h.2.2.2 n a b

def derivativeEnvelope (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (kind : WordKind) (u v : ScalarInterval L) (d : ℕ) : Mixed :=
  ∑ i : Fin (d+1), slotEnvelope hL hκ hr hs (Nat.succ_pos d) kind
    (Function.update (fun _ => u) i v)

lemma product_inserted_norm (u v : ScalarInterval L) (d : ℕ) (i : Fin (d+1)) :
    (∏ t : Fin (d+1), ‖Function.update (fun _ => u) i v t‖) = ‖v‖ * ‖u‖ ^ d := by
  classical
  have h : (fun t : Fin (d+1) => ‖Function.update (fun _ => u) i v t‖) =
      Function.update (fun _ => ‖u‖) i ‖v‖ := by
    funext t
    by_cases ht : t = i <;> simp [Function.update_apply, ht]
  rw [h, Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem (Finset.mem_univ i)]

theorem derivativeEnvelope_bound (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (kind : WordKind) (u v : ScalarInterval L) (d : ℕ) :
    ‖derivativeEnvelope hL hκ hr hs kind u v d‖ ≤
      (d+1 : ℝ) * wordConstant L r κ ^ (d+1) * ‖u‖ ^ d * ‖v‖ := by
  unfold derivativeEnvelope
  calc
    _ ≤ ∑ i : Fin (d+1), ‖slotEnvelope hL hκ hr hs (Nat.succ_pos d) kind
        (Function.update (fun _ => u) i v)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin (d+1), wordConstant L r κ ^ (d+1) * (‖v‖ * ‖u‖^d) :=
      Finset.sum_le_sum (fun i hi => (slotEnvelope_spec hL hκ hr hs (Nat.succ_pos d) kind _).2.1.trans_eq
        (by rw [product_inserted_norm]))
    _ = _ := by simp; ring

/-- An actual positive Fourier-path majorant for every differentiated source
coefficient, with the number of differentiated slots proved. -/
theorem derivativeEnvelope_spec (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (kind : WordKind) (u v : ScalarInterval L) (d : ℕ) :
    Positive (derivativeEnvelope hL hκ hr hs kind u v d) ∧
      Majorizes (derivativeEnvelope hL hκ hr hs kind u v d)
        (matrix (sourceDerivative hL hκ hr hs kind u d v)) := by
  have hsum : ∀ n a b, matrix (derivativeEnvelope hL hκ hr hs kind u v d) n a b =
      ∑ i : Fin (d+1), matrix (slotEnvelope hL hκ hr hs (Nat.succ_pos d) kind
        (Function.update (fun _ => u) i v)) n a b := by
    intro n a b
    rw [← entryCLM_apply n a b, derivativeEnvelope, map_sum]
    simp only [entryCLM_apply]
  constructor
  · intro n a b
    rw [hsum]
    exact ⟨by simp only [Complex.im_sum]; exact Finset.sum_eq_zero fun i hi =>
        ((slotEnvelope_spec hL hκ hr hs (Nat.succ_pos d) kind _).1 n a b).1,
      by simp only [Complex.re_sum]; exact Finset.sum_nonneg fun i hi =>
        ((slotEnvelope_spec hL hκ hr hs (Nat.succ_pos d) kind _).1 n a b).2⟩
  · intro n a b
    rw [sourceDerivative_apply]
    rw [← entryCLM_apply n a b, map_sum, hsum, Complex.re_sum]
    simp only [entryCLM_apply]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi =>
      (slotEnvelope_spec hL hκ hr hs (Nat.succ_pos d) kind _).2.2.2 n a b)

/-- The differentiated positive envelopes converge absolutely on a full
physical ball. This bound does not add summability of the input as a hypothesis. -/
theorem derivative_envelopes_summable (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (kind : WordKind) (u v : ScalarInterval L)
    (hu : wordConstant L r κ * ‖u‖ < 1) :
    Summable (fun d => ‖derivativeEnvelope hL hκ hr hs kind u v d‖) ∧
      Summable (fun d => ‖sourceDerivative hL hκ hr hs kind u d v‖) := by
  have hg := (QuantumNLS.Local006.TransposeMajorantG.differentiated_geometric_summable
    (wordConstant_pos hL hr hκ).le (norm_nonneg u) hu).mul_right ‖v‖
  have he : Summable (fun d => ‖derivativeEnvelope hL hκ hr hs kind u v d‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (derivativeEnvelope_bound hL hκ hr hs kind u v) hg
  refine ⟨he, Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun d => ?_) he⟩
  exact solid_norm (derivativeEnvelope_spec hL hκ hr hs kind u v d).1
    (derivativeEnvelope_spec hL hκ hr hs kind u v d).2

end QuantumNLS.Local006.SlotDerivativeJ

#print axioms QuantumNLS.Local006.SlotDerivativeJ.actualCoeff_hasFDerivAt
#print axioms QuantumNLS.Local006.SlotDerivativeJ.sourceDerivative_fourier
#print axioms QuantumNLS.Local006.SlotDerivativeJ.derivativeEnvelope_spec
#print axioms QuantumNLS.Local006.SlotDerivativeJ.derivative_envelopes_summable
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local006.SlotDerivativeJ." ||
        n.toString.startsWith "_private.QuantumNLS.Local006SlotDerivativeJ" then
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
  Lean.logInfo m!"Local006SlotDerivativeJ audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."

