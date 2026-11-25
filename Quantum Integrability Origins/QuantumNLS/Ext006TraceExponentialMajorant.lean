import QuantumNLS.Ext006FredholmTracePower
import Mathlib.Analysis.Normed.Algebra.Exponential

/-! A nonnegative coefficient expansion for exp(sum Tr(T^m)/(2m)).
Its weighted sum is finite for every positive trace-class strict contraction,
without smallness of Tr(T). This is scalar convergence support for the general
Fock exponential. The identification of these coefficients with squared norms
of the actual physical pair-creation terms is NOT proved or assumed here. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped ENNReal
namespace QuantumNLS.Ext006TraceExponentialMajorant
open Ext006FredholmTracePower TraceClass

/-- Ordered words of a fixed length; each letter denotes a positive degree. -/
def Word : ℕ → Type
  | 0 => PUnit
  | n+1 => ℕ × Word n

def wordDegree : (n : ℕ) → Word n → ℕ
  | 0, _ => 0
  | n+1, w => w.1+1 + wordDegree n w.2

def wordWeight (a : ℕ → ℝ≥0∞) : (n : ℕ) → Word n → ℝ≥0∞
  | 0, _ => 1
  | n+1, w => a w.1 * wordWeight a n w.2

lemma tsum_wordWeight (a : ℕ → ℝ≥0∞) (n : ℕ) :
    (∑' w : Word n, wordWeight a n w) = (∑' i, a i)^n := by
  induction n with
  | zero => simp [Word, wordWeight]
  | succ n ih =>
    change (∑' w : ℕ × Word n, a w.1 * wordWeight a n w.2) = _
    rw [ENNReal.tsum_prod']
    simp only [ENNReal.tsum_mul_left, ih, ENNReal.tsum_mul_right]
    rw [pow_succ, mul_comm]

abbrev AllWords := Σ n : ℕ, Word n

def degree (p : AllWords) : ℕ := wordDegree p.1 p.2

def family (a : ℕ → ℝ≥0∞) (p : AllWords) : ℝ≥0∞ :=
  ENNReal.ofReal ((p.1.factorial : ℝ)⁻¹) * wordWeight a p.1 p.2

/-- Coefficient obtained by collecting all ordered words of the given degree. -/
def coefficient (a : ℕ → ℝ≥0∞) (m : ℕ) : ℝ≥0∞ :=
  ∑' p : {p : AllWords // degree p = m}, family a p

lemma total_coefficient (a : ℕ → ℝ≥0∞) :
    (∑' m, coefficient a m) = ∑' p : AllWords, family a p :=
  ENNReal.tsum_fiberwise (family a) degree

lemma total_family (a : ℕ → ℝ≥0∞) :
    (∑' p : AllWords, family a p) =
      ∑' k : ℕ, ENNReal.ofReal ((k.factorial : ℝ)⁻¹) * (∑' i, a i)^k := by
  rw [ENNReal.tsum_sigma']
  apply tsum_congr
  intro k
  change (∑' w : Word k, ENNReal.ofReal ((k.factorial : ℝ)⁻¹) * wordWeight a k w) = _
  rw [ENNReal.tsum_mul_left, tsum_wordWeight]

/-- Exact scalar exponential identity; every summability premise refers to a. -/
theorem total_eq_exp (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (hs : Summable a) :
    (∑' m, coefficient (fun i => ENNReal.ofReal (a i)) m) =
      ENNReal.ofReal (Real.exp (∑' i, a i)) := by
  rw [total_coefficient, total_family,
    ← ENNReal.ofReal_tsum_of_nonneg ha hs]
  let s : ℝ := ∑' i, a i
  have hsn : 0 ≤ s := tsum_nonneg ha
  have he : HasSum (fun k : ℕ => s^k/(k.factorial : ℝ)) (Real.exp s) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp s
  calc
    (∑' k : ℕ, ENNReal.ofReal ((k.factorial : ℝ)⁻¹) * (ENNReal.ofReal s)^k) =
        ∑' k : ℕ, ENNReal.ofReal (s^k/(k.factorial : ℝ)) := by
      apply tsum_congr
      intro k
      rw [← ENNReal.ofReal_pow hsn, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    _ = ENNReal.ofReal (∑' k : ℕ, s^k/(k.factorial : ℝ)) :=
      (ENNReal.ofReal_tsum_of_nonneg (by intro k; positivity) he.summable).symm
    _ = ENNReal.ofReal (Real.exp s) := congrArg ENNReal.ofReal he.tsum_eq

lemma wordWeight_scaled (a : ℕ → ℝ≥0∞) (r : ℝ≥0∞) (n : ℕ) (w : Word n) :
    wordWeight (fun i => r^(i+1)*a i) n w = r^(wordDegree n w) * wordWeight a n w := by
  induction n with
  | zero => simp [wordWeight, wordDegree]
  | succ n ih =>
    change (r^(w.1+1)*a w.1) * wordWeight (fun i => r^(i+1)*a i) n w.2 =
      r^(w.1+1+wordDegree n w.2) * (a w.1 * wordWeight a n w.2)
    rw [ih, pow_add]
    ring

/-- Reweighting by total degree amounts to reweighting each letter. -/
theorem weighted_total (a : ℕ → ℝ≥0∞) (r : ℝ≥0∞) :
    (∑' m, r^m * coefficient a m) =
      ∑' m, coefficient (fun i => r^(i+1)*a i) m := by
  calc
    _ = ∑' m, ∑' p : {p : AllWords // degree p = m}, r^(degree p.val)*family a p := by
      apply tsum_congr
      intro m
      rw [coefficient, ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro p
      rw [p.property]
    _ = ∑' p : AllWords, r^(degree p)*family a p :=
      ENNReal.tsum_fiberwise (fun p => r^(degree p)*family a p) degree
    _ = ∑' p : AllWords, family (fun i => r^(i+1)*a i) p := by
      apply tsum_congr
      intro p
      simp only [family, wordWeight_scaled, degree]
      ring
    _ = _ := (total_coefficient _).symm

/-- An exact generating function, wherever the scaled scalar series converges. -/
theorem weighted_eq_exp (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i)
    (r : ℝ) (hr : 0 ≤ r) (hs : Summable (fun i => r^(i+1)*a i)) :
    (∑' m, (ENNReal.ofReal r)^m * coefficient (fun i => ENNReal.ofReal (a i)) m) =
      ENNReal.ofReal (Real.exp (∑' i, r^(i+1)*a i)) := by
  rw [weighted_total]
  have he : (fun i => (ENNReal.ofReal r)^(i+1) * ENNReal.ofReal (a i)) =
      fun i => ENNReal.ofReal (r^(i+1)*a i) := by
    funext i
    rw [← ENNReal.ofReal_pow hr, ENNReal.ofReal_mul (by positivity)]
  rw [he]
  exact total_eq_exp _ (fun i => mul_nonneg (pow_nonneg hr _) (ha i)) hs

section Trace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Half of the actual trace-power coefficient of T. -/
def traceLetter (T : H →L[ℂ] H) (n : ℕ) : ℝ := tracePowerTerm T n / 2

def traceCoefficient (T : H →L[ℂ] H) : ℕ → ℝ≥0∞ :=
  coefficient (fun i => ENNReal.ofReal (traceLetter T i))

lemma traceLetter_nonneg (T : H →L[ℂ] H) (i : ℕ) : 0 ≤ traceLetter T i := by
  exact div_nonneg (tracePowerTerm_nonneg T i) (by norm_num)

/-- Operator norm controls the radius; the trace norm need only be finite. -/
theorem scaled_trace_summable (T : H →L[ℂ] H) (hT : IsTraceClass T)
    (r : ℝ) (hr : 0 ≤ r) (hro : r*‖T‖ < 1) :
    Summable (fun i => r^(i+1)*traceLetter T i) := by
  apply Summable.of_nonneg_of_le (fun i => mul_nonneg (pow_nonneg hr _) (traceLetter_nonneg T i))
    (f := fun i => (r * (traceNorm T).toReal / 2) * (r*‖T‖)^i)
  · intro i
    have hb := tracePowerTerm_bound T hT i
    calc
      _ ≤ r^(i+1) * (‖T‖^i * (traceNorm T).toReal / 2) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hr _)
        exact div_le_div_of_nonneg_right hb (by norm_num)
      _ = _ := by rw [pow_succ, mul_pow]; ring
  · exact (summable_geometric_of_lt_one (mul_nonneg hr (norm_nonneg _)) hro).mul_left _

/-- General weighted scalar majorant, with no small-HS-norm hypothesis. -/
theorem trace_weighted_eq_exp (T : H →L[ℂ] H) (hT : IsTraceClass T)
    (r : ℝ) (hr : 0 ≤ r) (hro : r*‖T‖ < 1) :
    (∑' m, (ENNReal.ofReal r)^m * traceCoefficient T m) =
      ENNReal.ofReal (Real.exp (∑' i, r^(i+1)*traceLetter T i)) :=
  weighted_eq_exp _ (traceLetter_nonneg T) r hr (scaled_trace_summable T hT r hr hro)

/-- The scalar coefficient total is the inverse square root of the existing
trace-power determinant. This is not a physical Fock norm theorem. -/
theorem trace_total_eq_det (T : H →L[ℂ] H) (hT : IsTraceClass T) (hn : ‖T‖ < 1) :
    (∑' m, traceCoefficient T m) =
      ENNReal.ofReal ((fredholmDet T)^(-1/2 : ℝ)) := by
  have h := trace_weighted_eq_exp T hT 1 (by norm_num) (by simpa using hn)
  have he : Real.exp (∑' i, traceLetter T i) = (fredholmDet T)^(-1/2 : ℝ) := by
    rw [fredholmDet, ← Real.exp_mul]
    congr 1
    simp only [traceLetter, tsum_div_const]
    ring
  simpa only [ENNReal.ofReal_one, one_pow, one_mul, he] using h

/- A radius greater than one exists for every strict contraction. -/
omit [CompleteSpace H] in
theorem exists_trace_radius (T : H →L[ℂ] H) (hT : ‖T‖ < 1) :
    ∃ r : ℝ, 1 < r ∧ r*‖T‖ < 1 := by
  refine ⟨2/(1+‖T‖), ?_, ?_⟩
  · exact (lt_div_iff₀ (by positivity)).mpr (by linarith)
  · rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    linarith

/-- Finiteness of a weighted coefficient sum beyond the unit radius, for the
actual trace-class K* K. Relating it to physical Fock norms remains open. -/
theorem kernel_majorant_radius {ι : Type*} (b : HilbertBasis ι ℂ H)
    (K : H →L[ℂ] H) (hHS : hsSq b K ≠ ⊤) (hK : ‖K‖ < 1) :
    ∃ r : ℝ, 1 < r ∧
      (∑' m, (ENNReal.ofReal r)^m * traceCoefficient (K.adjoint ∘L K) m) ≠ ⊤ := by
  have hT := (Ext006Blocks.beta_adjoint_beta_traceClass b K hHS).1
  obtain ⟨r, hr, hro⟩ := exists_trace_radius _ (square_norm_lt_one K hK)
  refine ⟨r, hr, ?_⟩
  rw [trace_weighted_eq_exp _ hT r (by linarith) hro]
  exact ENNReal.ofReal_ne_top

end Trace
end QuantumNLS.Ext006TraceExponentialMajorant

#print axioms QuantumNLS.Ext006TraceExponentialMajorant.Word
#print axioms QuantumNLS.Ext006TraceExponentialMajorant.wordDegree
#print axioms QuantumNLS.Ext006TraceExponentialMajorant.wordWeight
#print axioms QuantumNLS.Ext006TraceExponentialMajorant.tsum_wordWeight
#print axioms QuantumNLS.Ext006TraceExponentialMajorant.AllWords
#print axioms QuantumNLS.Ext006TraceExponentialMajorant.degree
#print axioms QuantumNLS.Ext006TraceExponentialMajorant.family
#print axioms QuantumNLS.Ext006TraceExponentialMajorant.coefficient
#print axioms QuantumNLS.Ext006TraceExponentialMajorant.total_coefficient
#print axioms QuantumNLS.Ext006TraceExponentialMajorant.total_family
#print axioms QuantumNLS.Ext006TraceExponentialMajorant.total_eq_exp
#print axioms QuantumNLS.Ext006TraceExponentialMajorant.wordWeight_scaled
#print axioms QuantumNLS.Ext006TraceExponentialMajorant.weighted_total
#print axioms QuantumNLS.Ext006TraceExponentialMajorant.weighted_eq_exp
#print axioms QuantumNLS.Ext006TraceExponentialMajorant.traceLetter
#print axioms QuantumNLS.Ext006TraceExponentialMajorant.traceCoefficient
#print axioms QuantumNLS.Ext006TraceExponentialMajorant.traceLetter_nonneg
#print axioms QuantumNLS.Ext006TraceExponentialMajorant.scaled_trace_summable
#print axioms QuantumNLS.Ext006TraceExponentialMajorant.trace_weighted_eq_exp
#print axioms QuantumNLS.Ext006TraceExponentialMajorant.trace_total_eq_det
#print axioms QuantumNLS.Ext006TraceExponentialMajorant.exists_trace_radius
#print axioms QuantumNLS.Ext006TraceExponentialMajorant.kernel_majorant_radius

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006TraceExponentialMajorant." then
      pending := pending.push n
      roots := roots + 1
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
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
