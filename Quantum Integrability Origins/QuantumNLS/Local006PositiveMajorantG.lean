import QuantumNLS.Local006SequenceEvaluationE
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! Positive entrywise majorants in the frozen mixed sequence algebra.
These estimates retain Fourier-coordinate domination under multiplication,
powers, and the two binomial normalization factors. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators ENNReal Matrix.Norms.Elementwise
namespace QuantumNLS.Local006.PositiveMajorantG
open QuantumNLS.Local006.CoefficientLiftE QuantumNLS.Local006.SequenceAlgebraE
  QuantumNLS.Local006.SequenceEvaluationE QuantumNLS.LocalSpectral

abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ

def Positive (a : Mixed) : Prop :=
  ∀ n i j, (matrix a n i j).im = 0 ∧ 0 ≤ (matrix a n i j).re

def Majorizes (a : Mixed) (F : ℤ → Mat) : Prop :=
  ∀ n i j, ‖F n i j‖ ≤ (matrix a n i j).re

lemma positive_unit : Positive unit := by
  intro n i j
  rw [matrix_unit]
  fin_cases i <;> fin_cases j <;> simp

lemma positive_mul {a b : Mixed} (ha : Positive a) (hb : Positive b) :
    Positive (mul a b) := by
  intro n i j
  rw [matrix_mul, Matrix.mul_apply, Fin.sum_univ_two]
  constructor
  · simp only [Complex.add_im, Complex.mul_im, (ha n i 0).1, (ha n i 1).1,
      (hb n 0 j).1, (hb n 1 j).1, zero_mul, mul_zero, add_zero]
  · simp only [Complex.add_re, Complex.mul_re, (ha n i 0).1, (ha n i 1).1,
      (hb n 0 j).1, (hb n 1 j).1, zero_mul, sub_zero]
    exact add_nonneg (mul_nonneg (ha n i 0).2 (hb n 0 j).2)
      (mul_nonneg (ha n i 1).2 (hb n 1 j).2)

lemma majorizes_mul {a b : Mixed} {F H : ℤ → Mat}
    (ha : Positive a) (hb : Positive b) (hF : Majorizes a F) (hH : Majorizes b H) :
    Majorizes (mul a b) (fun n => F n * H n) := by
  intro n i j
  rw [matrix_mul, Matrix.mul_apply, Fin.sum_univ_two]
  calc
    ‖(F n * H n) i j‖ ≤ ‖F n i 0‖ * ‖H n 0 j‖ + ‖F n i 1‖ * ‖H n 1 j‖ := by
      simpa only [Matrix.mul_apply, Fin.sum_univ_two, norm_mul] using
        norm_add_le (F n i 0 * H n 0 j) (F n i 1 * H n 1 j)
    _ ≤ (matrix a n i 0).re * (matrix b n 0 j).re +
        (matrix a n i 1).re * (matrix b n 1 j).re :=
      add_le_add (mul_le_mul (hF n i 0) (hH n 0 j) (norm_nonneg _) (ha n i 0).2)
        (mul_le_mul (hF n i 1) (hH n 1 j) (norm_nonneg _) (ha n i 1).2)
    _ = _ := by simp [Complex.mul_re, (ha n i 0).1, (ha n i 1).1]

lemma positive_power {a : Mixed} (ha : Positive a) (k : ℕ) : Positive (power a k) := by
  induction k with
  | zero => exact positive_unit
  | succ k ih => exact positive_mul ha ih

lemma majorizes_power {a : Mixed} {F : ℤ → Mat} (ha : Positive a)
    (hF : Majorizes a F) (k : ℕ) : Majorizes (power a k) (fun n => F n ^ k) := by
  induction k with
  | zero =>
    intro n i j
    change ‖(F n ^ 0) i j‖ ≤ _
    rw [pow_zero, show power a 0 = unit from rfl, matrix_unit]
    fin_cases i <;> fin_cases j <;> simp
  | succ k ih =>
    simpa only [power, pow_succ'] using majorizes_mul ha (positive_power ha k) hF ih

/-- Both binomial coefficients have modulus at most one, including degree zero. -/
lemma normalized_word_majorizes {a b : Mixed} {F H : ℤ → Mat}
    (ha : Positive a) (hb : Positive b) (hF : Majorizes a F) (hH : Majorizes b H)
    (j l : ℕ) :
    Majorizes (mul (mul (power a j) b) (power a l))
      (fun n => ((invSqrtCoeff j : ℂ) • F n ^ j) * H n *
        ((invSqrtCoeff l : ℂ) • F n ^ l)) := by
  have hh := majorizes_mul (positive_mul (positive_power ha j) hb) (positive_power ha l)
    (majorizes_mul (positive_power ha j) hb (majorizes_power ha hF j) hH)
    (majorizes_power ha hF l)
  intro n i k
  have he : (((invSqrtCoeff j : ℂ) • F n ^ j) * H n *
      ((invSqrtCoeff l : ℂ) • F n ^ l)) i k =
      ((invSqrtCoeff j : ℂ) * (invSqrtCoeff l : ℂ)) * ((F n ^ j * H n * F n ^ l) i k) := by
    simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_eq_mul]
    ring
  change ‖(((invSqrtCoeff j : ℂ) • F n ^ j) * H n *
    ((invSqrtCoeff l : ℂ) • F n ^ l)) i k‖ ≤ _
  rw [he, norm_mul]
  have hc : ‖(invSqrtCoeff j : ℂ) * (invSqrtCoeff l : ℂ)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    nlinarith [abs_invSqrtCoeff_le j, abs_invSqrtCoeff_le l,
      abs_nonneg (invSqrtCoeff j), abs_nonneg (invSqrtCoeff l)]
  exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans (hh n i k)

/-- Absolute convergence of all pairs of normalization word lengths in the
mixed Banach sequence space. No scalar-coordinate summation substitutes for it. -/
theorem normalization_words_summable (a b : Mixed) (ha : 2 * ‖a‖ < 1) :
    Summable (fun jl : ℕ × ℕ => ‖mul (mul (power a jl.1) b) (power a jl.2)‖) := by
  have hg := summable_geometric_of_lt_one (by positivity : 0 ≤ 2 * ‖a‖) ha
  have hp := (hg.mul_of_nonneg hg (fun _ => by positivity) (fun _ => by positivity)).mul_left (4 * ‖b‖)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun jl => ?_) hp
  calc
    ‖mul (mul (power a jl.1) b) (power a jl.2)‖ ≤
        2 * (2 * ‖power a jl.1‖ * ‖b‖) * ‖power a jl.2‖ :=
      (mul_norm _ _).trans (by gcongr; exact mul_norm _ _)
    _ ≤ 4 * ‖b‖ * ((2 * ‖a‖) ^ jl.1 * (2 * ‖a‖) ^ jl.2) := by
      calc
        _ ≤ 2 * (2 * (2 * ‖a‖) ^ jl.1 * ‖b‖) * (2 * ‖a‖) ^ jl.2 := by
          gcongr <;> exact power_norm _ _
        _ = _ := by ring

/-- The majorant also sums in every individual Fourier coordinate. -/
theorem normalization_coordinate_summable (a b : Mixed) (ha : 2 * ‖a‖ < 1)
    (n : ℤ) (i j : Fin 2) :
    Summable (fun jl : ℕ × ℕ =>
      ‖matrix (mul (mul (power a jl.1) b) (power a jl.2)) n i j‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun jl => ?_)
    (normalization_words_summable a b ha)
  obtain ⟨h00, h11, h01, h10⟩ := component_bounds
    (mul (mul (power a jl.1) b) (power a jl.2))
  fin_cases i <;> fin_cases j
  · exact (lp.norm_apply_le_norm (by simp) _ n).trans h00
  · exact (lp.norm_apply_le_norm (by norm_num) _ n).trans h01
  · exact (lp.norm_apply_le_norm (by norm_num) _ n).trans h10
  · exact (lp.norm_apply_le_norm (by simp) _ n).trans h11

def entryCLM (n : ℤ) (i j : Fin 2) : Mixed →L[ℂ] ℂ :=
  if i = 0 then
    if j = 0 then (lp.evalCLM ℂ (fun _ : ℤ => ℂ) ∞ n).comp
      ((ContinuousLinearMap.fst ℂ SeqInf SeqInf).comp (ContinuousLinearMap.fst ℂ _ _))
    else (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).comp
      ((ContinuousLinearMap.fst ℂ Seq2 Seq2).comp (ContinuousLinearMap.snd ℂ _ _))
  else
    if j = 0 then (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).comp
      ((ContinuousLinearMap.snd ℂ Seq2 Seq2).comp (ContinuousLinearMap.snd ℂ _ _))
    else (lp.evalCLM ℂ (fun _ : ℤ => ℂ) ∞ n).comp
      ((ContinuousLinearMap.snd ℂ SeqInf SeqInf).comp (ContinuousLinearMap.fst ℂ _ _))

@[simp] lemma entryCLM_apply (n : ℤ) (i j : Fin 2) (a : Mixed) :
    entryCLM n i j a = matrix a n i j := by
  fin_cases i <;> fin_cases j <;> rfl

lemma positive_tsum {ι : Type*} {f : ι → Mixed} (hf : Summable f)
    (hp : ∀ k, Positive (f k)) : Positive (∑' k, f k) := by
  intro n i j
  have h := (entryCLM n i j).hasSum hf.hasSum
  simp only [entryCLM_apply] at h
  constructor
  · have hi := Complex.hasSum_im h
    have he := hi.tsum_eq
    simpa only [(hp _ n i j).1, tsum_zero] using he.symm
  · rw [← (Complex.hasSum_re h).tsum_eq]
    exact tsum_nonneg (fun k => (hp k n i j).2)

end QuantumNLS.Local006.PositiveMajorantG
#print axioms QuantumNLS.Local006.PositiveMajorantG.normalized_word_majorizes
#print axioms QuantumNLS.Local006.PositiveMajorantG.normalization_words_summable
#print axioms QuantumNLS.Local006.PositiveMajorantG.normalization_coordinate_summable

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local006.PositiveMajorantG." ||
        n.toString.startsWith "_private.QuantumNLS.Local006PositiveMajorantG" then
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
  Lean.logInfo m!"Local006PositiveMajorantG audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
