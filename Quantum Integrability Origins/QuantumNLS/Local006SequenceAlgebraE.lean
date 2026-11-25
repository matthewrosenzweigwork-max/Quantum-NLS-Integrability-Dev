import QuantumNLS.Local006CoefficientLiftE
import Mathlib.Analysis.Normed.Lp.lpHolder

/-! The mixed sequence algebra in the LOCAL-006 proof: bounded diagonal
entries and square-summable off-diagonal entries. We keep the ordinary product
norm, so multiplication has bound 2. The inverse-square-root construction
therefore converges on the explicit ball `2 * ‖x‖ < 1`. -/
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
noncomputable section
open scoped ENNReal NNReal BigOperators

namespace QuantumNLS.Local006.SequenceAlgebraE
open QuantumNLS.Local006.CoefficientLiftE QuantumNLS.LocalSpectral

abbrev Mixed := (SeqInf × SeqInf) × (Seq2 × Seq2)

def incl : Seq2 →L[ℂ] SeqInf :=
  (lp.linearMapOfLE ℂ (fun _ : ℤ => ℂ) (show (2 : ℝ≥0∞) ≤ ∞ by simp)).mkContinuous
    1 (fun x => by
      rw [one_mul]
      exact lp.norm_le_of_forall_le (norm_nonneg x)
        (fun n => lp.norm_apply_le_norm (by norm_num) x n))

@[simp] theorem incl_apply (x : Seq2) (n : ℤ) : incl x n = x n := rfl

lemma incl_norm (x : Seq2) : ‖incl x‖ ≤ ‖x‖ := by
  exact lp.norm_le_of_forall_le (norm_nonneg x)
    (fun n => lp.norm_apply_le_norm (by norm_num) x n)

def prodInf : SeqInf →L[ℂ] SeqInf →L[ℂ] SeqInf :=
  lp.holderL ∞ (fun _ : ℤ => ContinuousLinearMap.mul ℂ ℂ)
    (K := 1) (fun _ => ContinuousLinearMap.opNorm_mul_le ℂ ℂ)

def prodInf2 : SeqInf →L[ℂ] Seq2 →L[ℂ] Seq2 :=
  lp.holderL 2 (fun _ : ℤ => ContinuousLinearMap.mul ℂ ℂ)
    (K := 1) (fun _ => ContinuousLinearMap.opNorm_mul_le ℂ ℂ)

@[simp] theorem prodInf_apply (a b : SeqInf) (n : ℤ) : prodInf a b n = a n * b n := rfl
@[simp] theorem prodInf2_apply (a : SeqInf) (b : Seq2) (n : ℤ) : prodInf2 a b n = a n * b n := rfl

lemma bilinear_norm {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    (B : X →L[ℂ] Y →L[ℂ] Z) (hB : ‖B‖ ≤ 1) (x : X) (y : Y) :
    ‖B x y‖ ≤ ‖x‖ * ‖y‖ := by
  calc
    ‖B x y‖ ≤ ‖B‖ * ‖x‖ * ‖y‖ := B.le_opNorm₂ x y
    _ ≤ ‖x‖ * ‖y‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hB (norm_nonneg x)) (norm_nonneg y)

lemma prodInf_norm (a b : SeqInf) : ‖prodInf a b‖ ≤ ‖a‖ * ‖b‖ := by
  apply bilinear_norm
  simpa only [prodInf, NNReal.coe_one] using
    (lp.norm_holderL_le (p := ∞) (q := ∞) ∞
      (fun _ : ℤ => ContinuousLinearMap.mul ℂ ℂ) (K := (1 : ℝ≥0))
      (fun _ => ContinuousLinearMap.opNorm_mul_le ℂ ℂ))

lemma prodInf2_norm (a : SeqInf) (b : Seq2) : ‖prodInf2 a b‖ ≤ ‖a‖ * ‖b‖ := by
  apply bilinear_norm
  simpa only [prodInf2, NNReal.coe_one] using
    (lp.norm_holderL_le (p := ∞) (q := 2) 2
      (fun _ : ℤ => ContinuousLinearMap.mul ℂ ℂ) (K := (1 : ℝ≥0))
      (fun _ => ContinuousLinearMap.opNorm_mul_le ℂ ℂ))

def mul (x y : Mixed) : Mixed :=
  ((prodInf x.1.1 y.1.1 + prodInf (incl x.2.1) (incl y.2.2),
    prodInf (incl x.2.2) (incl y.2.1) + prodInf x.1.2 y.1.2),
   (prodInf2 x.1.1 y.2.1 + prodInf2 y.1.2 x.2.1,
    prodInf2 y.1.1 x.2.2 + prodInf2 x.1.2 y.2.2))

lemma component_bounds (x : Mixed) :
    ‖x.1.1‖ ≤ ‖x‖ ∧ ‖x.1.2‖ ≤ ‖x‖ ∧ ‖x.2.1‖ ≤ ‖x‖ ∧ ‖x.2.2‖ ≤ ‖x‖ :=
  ⟨(norm_fst_le x.1).trans (norm_fst_le x),
    (norm_snd_le x.1).trans (norm_fst_le x),
    (norm_fst_le x.2).trans (norm_snd_le x),
    (norm_snd_le x.2).trans (norm_snd_le x)⟩

lemma mul_norm (x y : Mixed) : ‖mul x y‖ ≤ 2 * ‖x‖ * ‖y‖ := by
  obtain ⟨x00, x11, x01, x10⟩ := component_bounds x
  obtain ⟨y00, y11, y01, y10⟩ := component_bounds y
  have xi01 := (incl_norm x.2.1).trans x01
  have xi10 := (incl_norm x.2.2).trans x10
  have yi01 := (incl_norm y.2.1).trans y01
  have yi10 := (incl_norm y.2.2).trans y10
  have hadd {X : Type} [NormedAddCommGroup X] (a b : X)
      (ha : ‖a‖ ≤ ‖x‖ * ‖y‖) (hb : ‖b‖ ≤ ‖x‖ * ‖y‖) :
      ‖a + b‖ ≤ 2 * ‖x‖ * ‖y‖ := by
    calc ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
      _ ≤ 2 * ‖x‖ * ‖y‖ := by linarith
  change max (max _ _) (max _ _) ≤ _
  refine max_le (max_le ?_ ?_) (max_le ?_ ?_)
  all_goals dsimp only [mul]
  · apply hadd
    · exact (prodInf_norm _ _).trans (mul_le_mul x00 y00 (norm_nonneg _) (norm_nonneg _))
    · exact (prodInf_norm _ _).trans (mul_le_mul xi01 yi10 (norm_nonneg _) (norm_nonneg _))
  · apply hadd
    · exact (prodInf_norm _ _).trans (mul_le_mul xi10 yi01 (norm_nonneg _) (norm_nonneg _))
    · exact (prodInf_norm _ _).trans (mul_le_mul x11 y11 (norm_nonneg _) (norm_nonneg _))
  · apply hadd
    · exact (prodInf2_norm _ _).trans (mul_le_mul x00 y01 (norm_nonneg _) (norm_nonneg _))
    · calc ‖prodInf2 y.1.2 x.2.1‖ ≤ ‖y.1.2‖ * ‖x.2.1‖ := prodInf2_norm _ _
        _ ≤ ‖y‖ * ‖x‖ := mul_le_mul y11 x01 (norm_nonneg _) (norm_nonneg _)
        _ = ‖x‖ * ‖y‖ := mul_comm _ _
  · apply hadd
    · calc ‖prodInf2 y.1.1 x.2.2‖ ≤ ‖y.1.1‖ * ‖x.2.2‖ := prodInf2_norm _ _
        _ ≤ ‖y‖ * ‖x‖ := mul_le_mul y00 x10 (norm_nonneg _) (norm_nonneg _)
        _ = ‖x‖ * ‖y‖ := mul_comm _ _
    · exact (prodInf2_norm _ _).trans (mul_le_mul x11 y10 (norm_nonneg _) (norm_nonneg _))

def unit : Mixed := ((1, 1), (0, 0))

lemma unit_norm : ‖unit‖ ≤ 1 := by
  have h : ‖(1 : SeqInf)‖ ≤ 1 := lp.norm_le_of_forall_le zero_le_one (fun n => by simp)
  simpa only [unit, Prod.norm_def, norm_zero, max_self, max_eq_left (norm_nonneg _)] using h

def power (x : Mixed) : ℕ → Mixed
  | 0 => unit
  | k + 1 => mul x (power x k)

lemma power_norm (x : Mixed) (k : ℕ) : ‖power x k‖ ≤ (2 * ‖x‖) ^ k := by
  induction k with
  | zero => simpa only [power, pow_zero] using unit_norm
  | succ k ih =>
    calc
      ‖power x (k + 1)‖ ≤ 2 * ‖x‖ * ‖power x k‖ := mul_norm _ _
      _ ≤ (2 * ‖x‖) * (2 * ‖x‖) ^ k :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ = (2 * ‖x‖) ^ (k + 1) := (pow_succ' _ _).symm

/-- Absolute norm convergence in the mixed Banach sequence space. -/
theorem inverse_sqrt_summable (x : Mixed) (hx : 2 * ‖x‖ < 1) :
    Summable (fun k : ℕ => ‖(invSqrtCoeff k : ℂ) • power x k‖) := by
  apply Summable.of_nonneg_of_le (fun k => norm_nonneg _)
    (fun k => ?_) (summable_geometric_of_lt_one (by positivity) hx)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul (abs_invSqrtCoeff_le k) (power_norm x k) (norm_nonneg _) zero_le_one).trans_eq
    (one_mul _)

def inverseSqrt (x : Mixed) : Mixed := ∑' k : ℕ, (invSqrtCoeff k : ℂ) • power x k

theorem inverse_sqrt_hasSum (x : Mixed) (hx : 2 * ‖x‖ < 1) :
    HasSum (fun k : ℕ => (invSqrtCoeff k : ℂ) • power x k) (inverseSqrt x) :=
  (inverse_sqrt_summable x hx).of_norm.hasSum

end QuantumNLS.Local006.SequenceAlgebraE

#print axioms QuantumNLS.Local006.SequenceAlgebraE.mul_norm
#print axioms QuantumNLS.Local006.SequenceAlgebraE.power_norm
#print axioms QuantumNLS.Local006.SequenceAlgebraE.inverse_sqrt_hasSum

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local006.SequenceAlgebraE." ||
        n.toString.startsWith "_private.QuantumNLS.Local006SequenceAlgebraE" then
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
  Lean.logInfo m!"Local006SequenceAlgebraE audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
