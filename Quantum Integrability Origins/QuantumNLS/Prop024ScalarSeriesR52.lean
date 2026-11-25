import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Sqrt
import QuantumNLS.Prop024ScalarEstimateR51

/-! Round 52 scalar preparation for the entire Wick remainder. This module
proves convergence of the source's square-root-factorial majorant and applies
the frozen cutoff/geometric-tail estimates from R51. It makes no operator
translation or domain claim. -/
noncomputable section
set_option autoImplicit false
namespace QuantumNLS.Prop024ScalarSeriesR52

open QuantumNLS.Prop024ScalarEstimateR51
open Filter Topology

/-- The summand in the finite constant S_B = sum_l B^l / sqrt(l!). -/
def factorialRootTerm (B : ℝ) (l : ℕ) : ℝ :=
  B ^ l / Real.sqrt (l.factorial : ℝ)

/-- The finite scalar series used after the even/odd reindexing. -/
def factorialRootSeries (B : ℝ) : ℝ := ∑' l : ℕ, factorialRootTerm B l

lemma factorialRootTerm_nonneg {B : ℝ} (hB : 0 ≤ B) (l : ℕ) :
    0 ≤ factorialRootTerm B l := by
  unfold factorialRootTerm
  positivity

lemma factorialRootTerm_sq (B : ℝ) (l : ℕ) :
    (factorialRootTerm B l) ^ 2 = (B ^ 2) ^ l / (l.factorial : ℝ) := by
  unfold factorialRootTerm
  have hp : (B ^ l) ^ 2 = (B ^ 2) ^ l := by
    calc
      (B ^ l) ^ 2 = B ^ (l * 2) := by rw [← pow_mul]
      _ = B ^ (2 * l) := by rw [Nat.mul_comm]
      _ = (B ^ 2) ^ l := by rw [← pow_mul]
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _), hp]

lemma factorialRootTerm_step_sq (B : ℝ) (l : ℕ) :
    (factorialRootTerm B (l + 1)) ^ 2 * ((l + 1 : ℕ) : ℝ) =
      B ^ 2 * (factorialRootTerm B l) ^ 2 := by
  rw [factorialRootTerm_sq, factorialRootTerm_sq]
  have hf : ((l + 1).factorial : ℝ) = ((l + 1 : ℕ) : ℝ) * (l.factorial : ℝ) := by
    simp [Nat.factorial_succ]
  rw [hf, pow_succ]
  have hn : ((l + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hfac : (l.factorial : ℝ) ≠ 0 := by positivity
  field_simp [hn, hfac]

lemma factorialRootTerm_step_le_half {B : ℝ} (hB : 0 ≤ B) (l : ℕ)
    (hcap : B ^ 2 ≤ ((l + 1 : ℕ) : ℝ) / 4) :
    factorialRootTerm B (l + 1) ≤ (1 / 2 : ℝ) * factorialRootTerm B l := by
  have hn : 0 < ((l + 1 : ℕ) : ℝ) := by positivity
  have h0 := factorialRootTerm_nonneg hB l
  have h1 := factorialRootTerm_nonneg hB (l + 1)
  have hratio : (factorialRootTerm B (l + 1)) ^ 2 =
      (B ^ 2 * (factorialRootTerm B l) ^ 2) / ((l + 1 : ℕ) : ℝ) := by
    rw [eq_div_iff hn.ne']
    nlinarith [factorialRootTerm_step_sq B l]
  have hprod := mul_le_mul_of_nonneg_right hcap (sq_nonneg (factorialRootTerm B l))
  have hsq : (factorialRootTerm B (l + 1)) ^ 2 ≤
      ((1 / 2 : ℝ) * factorialRootTerm B l) ^ 2 := by
    calc
      _ = (B ^ 2 * (factorialRootTerm B l) ^ 2) / ((l + 1 : ℕ) : ℝ) := hratio
      _ ≤ ((((l + 1 : ℕ) : ℝ) / 4) * (factorialRootTerm B l) ^ 2) /
          ((l + 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right hprod (le_of_lt hn)
      _ = ((1 / 2 : ℝ) * factorialRootTerm B l) ^ 2 := by
        field_simp [hn.ne']
        ring
  have hright : 0 ≤ (1 / 2 : ℝ) * factorialRootTerm B l := by positivity
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg h1,
    Real.sqrt_sq_eq_abs, abs_of_nonneg hright] at hsqrt
  exact hsqrt

/-- The square-root-factorial series is summable for every nonnegative B.
The ratio estimate follows directly from (l+1)! = (l+1) l!. -/
theorem factorialRootTerm_summable {B : ℝ} (hB : 0 ≤ B) :
    Summable (factorialRootTerm B) := by
  obtain ⟨K, hK⟩ := exists_nat_gt (4 * B ^ 2)
  apply summable_of_ratio_norm_eventually_le (r := (1 / 2 : ℝ)) (by norm_num)
  filter_upwards [Filter.eventually_atTop.2 ⟨K, fun l hl => hl⟩] with l hl
  have hKl : (K : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hK' : 4 * B ^ 2 < (K : ℝ) := by exact_mod_cast hK
  have hsucc : (l : ℝ) + 1 = ((l + 1 : ℕ) : ℝ) := by norm_cast
  have hcap : B ^ 2 ≤ ((l + 1 : ℕ) : ℝ) / 4 := by
    rw [← hsucc]
    nlinarith
  rw [Real.norm_eq_abs, abs_of_nonneg (factorialRootTerm_nonneg hB (l + 1)),
    Real.norm_eq_abs, abs_of_nonneg (factorialRootTerm_nonneg hB l)]
  exact factorialRootTerm_step_le_half hB l hcap

/-- The source's S_B series is summable at its value B = sqrt(2 A). -/
theorem source_factorial_series_summable (A : ℝ) :
    Summable (factorialRootTerm (Real.sqrt (2 * A))) :=
  factorialRootTerm_summable (Real.sqrt_nonneg _)

lemma factorialRootSeries_nonneg {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ factorialRootSeries B := by
  unfold factorialRootSeries
  exact tsum_nonneg (fun l => factorialRootTerm_nonneg hB l)

/-- The geometric tail after the source reindexing has precisely the
`M N^(-1/2) Q^(3/2)` scale. The square-root form is algebraically the same
as the source's `N^(-1/2) Q^(3/2)` convention. -/
theorem source_scale_geometric_tail (A Q N M : ℝ) (hA : 0 < A) (hQ : 1 ≤ Q)
    (hN : 256 * Real.exp 1 * A * Q ≤ N) (hM : 0 ≤ M) :
    M * N * factorialRootSeries (Real.sqrt (2 * A)) *
        (∑' j : ℕ, (wickRatio A Q N) ^ (j + 3)) ≤
      2 * factorialRootSeries (Real.sqrt (2 * A)) * (Real.sqrt (2 * A)) ^ 3 *
        (Real.sqrt (32 * Real.exp 1)) ^ 3 * M * (Real.sqrt Q) ^ 3 / Real.sqrt N := by
  let B : ℝ := Real.sqrt (2 * A)
  let D : ℝ := 32 * Real.exp 1
  let S : ℝ := factorialRootSeries B
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hS : 0 ≤ S := by dsimp [S]; exact factorialRootSeries_nonneg hB
  have hlow : 0 < 256 * Real.exp 1 * A * Q := by positivity
  have hNpos : 0 < N := by linarith
  have hroot : Real.sqrt (32 * Real.exp 1 * Q / N) =
      Real.sqrt D * Real.sqrt Q / Real.sqrt N := by
    rw [show 32 * Real.exp 1 * Q / N = (D * Q) / N by rfl,
      Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity)]
  have hr : wickRatio A Q N = B * (Real.sqrt D * Real.sqrt Q / Real.sqrt N) := by
    dsimp [wickRatio, B]
    rw [hroot]
  have hNsq : (Real.sqrt N) ^ 2 = N := Real.sq_sqrt (le_of_lt hNpos)
  have hNroot : Real.sqrt N ≠ 0 := (Real.sqrt_pos.2 hNpos).ne'
  have hr0 : 0 ≤ wickRatio A Q N := by
    dsimp [wickRatio]
    positivity
  have hrhalf := wickRatio_le_half A Q N hA hQ hN
  have htail := cubic_geometric_tail (wickRatio A Q N) hr0 hrhalf
  have hscale : 0 ≤ M * N * S := by positivity
  calc
    M * N * factorialRootSeries (Real.sqrt (2 * A)) *
        (∑' j : ℕ, (wickRatio A Q N) ^ (j + 3))
        = M * N * S * (∑' j : ℕ, (wickRatio A Q N) ^ (j + 3)) := by rfl
    _ ≤ M * N * S * (2 * (wickRatio A Q N) ^ 3) :=
      mul_le_mul_of_nonneg_left htail hscale
    _ = 2 * M * N * S * (wickRatio A Q N) ^ 3 := by ring
    _ = 2 * S * B ^ 3 * (Real.sqrt D) ^ 3 * M * (Real.sqrt Q) ^ 3 / Real.sqrt N := by
      rw [hr]
      field_simp [hNroot]
      rw [hNsq]
      ring

end QuantumNLS.Prop024ScalarSeriesR52

#print axioms QuantumNLS.Prop024ScalarSeriesR52.factorialRootTerm_summable
#print axioms QuantumNLS.Prop024ScalarSeriesR52.source_factorial_series_summable
#print axioms QuantumNLS.Prop024ScalarSeriesR52.source_scale_geometric_tail

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop024ScalarSeriesR52." ||
        n.toString.startsWith "_private.QuantumNLS.Prop024ScalarSeriesR52." then
      pending := pending.push n
  let roots := pending.size
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
  Lean.logInfo m!"PROP-024 R52 scalar audit PASS: {roots} own constants; {seen.size} transitive constants; standard axioms only."
