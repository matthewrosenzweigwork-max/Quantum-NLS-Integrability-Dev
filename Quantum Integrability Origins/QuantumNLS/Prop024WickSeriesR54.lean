import QuantumNLS.Prop024WickCellsR54
import QuantumNLS.Prop024DoubleSeriesR53

/-! Round 54 complete summability comparison for the physical contraction
cells. This bounds their candidate norm series, while leaving the Weyl
translation identification separate and explicit. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace ComplexConjugate

namespace QuantumNLS.Prop024WickSeriesR54

open Prop022FactorialCoefficientsR115
open Prop024ContractionsR54 Prop024WickCellsR54 Prop024DoubleSeriesR53
open Prop024ScalarEstimateR51 Prop024ScalarSeriesR52
open BetheCoefficientTransform PhysicalTensor Ext025B3PhysicalSectors

variable {L : ℝ} [Fact (0 < L)]
attribute [local instance] InnerProductSpace.complexToReal

/-- Sum of all fixed-degree physical contraction norms over the admissible
interaction-order and degree cells. -/
def contractedDoubleSeries (B : ∀ m, HN L m →L[ℂ] HN L m)
    (u : L2T L) (Q N : ℝ) : ℝ :=
  ∑' p : WickSourceIndex,
    contractedSliceCell p.val.1 p.val.2 B u Q N

lemma wickCell_nonneg_local (A Q N : ℝ) (hA : 0 ≤ A) (m j : ℕ) :
    0 ≤ wickCell A Q N m j := by
  unfold wickCell
  positivity

lemma contractedSliceCell_nonneg_local (m j : ℕ)
    (B : ∀ r, HN L r →L[ℂ] HN L r) (u : L2T L) (Q N : ℝ) :
    0 ≤ contractedSliceCell m j B u Q N := by
  unfold contractedSliceCell
  apply Finset.sum_nonneg
  intro a ha
  by_cases h₁ : a ≤ m
  · by_cases h₂ : j-a ≤ m
    · simp only [dif_pos h₁, dif_pos h₂]
      unfold contractedCell
      positivity
    · simp only [dif_pos h₁, dif_neg h₂]
      positivity
  · simp only [dif_neg h₁]
    positivity

/-- Summability of the frozen R53 scalar Wick cells on their source index. -/
lemma wickSourceCells_summable (A Q N : ℝ) (hA : 0 < A)
    (hQ : 1 ≤ Q) (hN : 256 * Real.exp 1 * A * Q ≤ N) :
    Summable (fun p : WickSourceIndex => wickCell A Q N p.val.1 p.val.2) := by
  let B0 : ℝ := Real.sqrt (2*A)
  let r : ℝ := wickRatio A Q N
  have hQ0 : 0 ≤ Q := by linarith
  have hr0 : 0 ≤ r := by dsimp [r, wickRatio]; positivity
  have hrhalf : r ≤ 1/2 := by
    dsimp [r]
    exact wickRatio_le_half A Q N hA hQ hN
  have hr1 : r < 1 := by linarith
  have hNpos : 0 < N := by
    have hlow : 0 < 256 * Real.exp 1 * A * Q := by positivity
    exact lt_of_lt_of_le hlow hN
  have hGeom : Summable (fun j : ℕ => r^j) :=
    summable_geometric_of_lt_one hr0 hr1
  have hTailGeom : Summable (fun j : WickTailIndex => r^j.1) :=
    hGeom.comp_injective (fun _ _ h => Subtype.ext h)
  have hB0 : 0 ≤ B0 := by dsimp [B0]; positivity
  have hFactorial : Summable (factorialRootTerm B0) :=
    factorialRootTerm_summable hB0
  have hTargetNonneg (p : WickTailIndex × ℕ) :
      0 ≤ wickTargetCell r B0 p := by
    dsimp [wickTargetCell]
    exact mul_nonneg (pow_nonneg hr0 _) (factorialRootTerm_nonneg hB0 _)
  have hTarget : Summable (wickTargetCell r B0) := by
    rw [summable_prod_of_nonneg hTargetNonneg]
    constructor
    · intro j
      exact (hFactorial.mul_left (r^j.1)).congr (by intro l; rfl)
    · have houter : Summable (fun j : WickTailIndex =>
          r^j.1 * factorialRootSeries B0) := hTailGeom.mul_right _
      have hinner (j : WickTailIndex) :
          (∑' l : ℕ, wickTargetCell r B0 (j,l)) =
            r^j.1 * factorialRootSeries B0 := by
        calc
          (∑' l : ℕ, wickTargetCell r B0 (j,l)) =
              ∑' l : ℕ, r^j.1 * factorialRootTerm B0 l := by
            exact tsum_congr (fun l => rfl)
          _ = r^j.1 * ∑' l : ℕ, factorialRootTerm B0 l := tsum_mul_left
          _ = r^j.1 * factorialRootSeries B0 := rfl
      exact houter.congr (by intro j; exact (hinner j).symm)
  have hTargetComp : Summable (fun p : WickSourceIndex =>
      wickTargetCell r B0 (wickSourceMap p)) :=
    hTarget.comp_injective wickSourceMap_injective
  have hSourceNonneg (p : WickSourceIndex) :
      0 ≤ wickCell A Q N p.val.1 p.val.2 :=
    wickCell_nonneg_local A Q N (le_of_lt hA) p.val.1 p.val.2
  have hSourceLeComp (p : WickSourceIndex) :
      wickCell A Q N p.val.1 p.val.2 ≤
        wickTargetCell r B0 (wickSourceMap p) := by
    have h := wickCell_le_reindexedCell A Q N hA hQ0 hNpos
      p.val.1 p.val.2 p.property.1 p.property.2
    simpa [wickTargetCell, wickSourceMap, reindexedCell,
      factorialRootTerm, B0, r] using h
  exact Summable.of_nonneg_of_le hSourceNonneg hSourceLeComp hTargetComp

/-- The entire admissible series of physical contraction-cell norms is
bounded by the scalar R53 Wick series, using only the source factorial
kernel bound and no Weyl-translation compatibility premise. -/
theorem contractedDoubleSeries_le_scalar (B : ∀ m, HN L m →L[ℂ] HN L m)
    (u : L2T L) (hu : ‖u‖ = 1) (M A Q N : ℝ)
    (hM : 0 ≤ M) (hA : 0 < A) (hQ : 1 ≤ Q)
    (hN : 256 * Real.exp 1 * A * Q ≤ N)
    (hB : FactorialBound B M A) :
    contractedDoubleSeries B u Q N ≤ M * wickDoubleSeries A Q N := by
  have hNpos : 0 < N := by
    have hlow : 0 < 256 * Real.exp 1 * A * Q := by positivity
    exact lt_of_lt_of_le hlow hN
  have hsource := wickSourceCells_summable A Q N hA hQ hN
  have hslice (p : WickSourceIndex) :
      contractedSliceCell p.val.1 p.val.2 B u Q N ≤
        M * wickCell A Q N p.val.1 p.val.2 :=
    contractedSliceCell_le_wickCell p.val.1 p.val.2 p.property.1 p.property.2
      B u hu M A Q N hM hA hB
  have hactual : Summable (fun p : WickSourceIndex =>
      contractedSliceCell p.val.1 p.val.2 B u Q N) :=
    Summable.of_nonneg_of_le
      (fun p => contractedSliceCell_nonneg_local p.val.1 p.val.2 B u Q N)
      hslice (hsource.mul_left M)
  calc
    contractedDoubleSeries B u Q N ≤
        ∑' p : WickSourceIndex, M * wickCell A Q N p.val.1 p.val.2 :=
      Summable.tsum_le_tsum hslice hactual (hsource.mul_left M)
    _ = M * wickDoubleSeries A Q N := by
      rw [tsum_mul_left]
      rfl

/-- R54's physical contraction-cell series obeys the exact frozen PROP-024
source-scale remainder estimate. These are candidate translated terms; the
Weyl-Taylor identity that identifies them with the actual conjugated
interaction remains a separate theorem. -/
theorem contractedDoubleSeries_source_bound
    (B : ∀ m, HN L m →L[ℂ] HN L m) (u : L2T L) (hu : ‖u‖ = 1)
    (M A Q N : ℝ) (hM : 0 ≤ M) (hA : 0 < A) (hQ : 1 ≤ Q)
    (hN : 256 * Real.exp 1 * A * Q ≤ N)
    (hB : FactorialBound B M A) :
    N * contractedDoubleSeries B u Q N ≤
      2 * factorialRootSeries (Real.sqrt (2*A)) * (Real.sqrt (2*A))^3 *
        (Real.sqrt (32 * Real.exp 1))^3 * M * (Real.sqrt Q)^3 / Real.sqrt N := by
  have hseries := contractedDoubleSeries_le_scalar B u hu M A Q N hM hA hQ hN hB
  have hNpos : 0 < N := by
    have hlow : 0 < 256 * Real.exp 1 * A * Q := by positivity
    exact lt_of_lt_of_le hlow hN
  calc
    N * contractedDoubleSeries B u Q N ≤
        N * (M * wickDoubleSeries A Q N) :=
      mul_le_mul_of_nonneg_left hseries (le_of_lt hNpos)
    _ = M * N * wickDoubleSeries A Q N := by ring
    _ ≤ 2 * factorialRootSeries (Real.sqrt (2*A)) * (Real.sqrt (2*A))^3 *
        (Real.sqrt (32 * Real.exp 1))^3 * M * (Real.sqrt Q)^3 / Real.sqrt N :=
      wickDoubleSeries_source_bound A Q N M hA hQ hN hM

end QuantumNLS.Prop024WickSeriesR54

#print axioms QuantumNLS.Prop024WickSeriesR54.contractedDoubleSeries_le_scalar
#print axioms QuantumNLS.Prop024WickSeriesR54.contractedDoubleSeries_source_bound

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop024WickSeriesR54." ||
        n.toString.startsWith "_private.QuantumNLS.Prop024WickSeriesR54." then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").any (fun s => s == "HeldGP14Tonelli" || s == "RegularCut") then
        throwError "Held identifier in dependency closure: {n}"
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
  Lean.logInfo m!"R54 operator-series aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
