import Mathlib.Data.Nat.Choose.Vandermonde
import QuantumNLS.Prop024ContractionsR54
import QuantumNLS.Prop024DoubleSeriesR53

/-! Round 54 operator-cell comparison. Each physical slot contraction,
weighted by its two binomial choices and the PROP-023 moment factor, is
bounded by the corresponding reindexed scalar cell from frozen R53. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace ComplexConjugate

namespace QuantumNLS.Prop024WickCellsR54

open BetheCoefficientTransform PhysicalTensor Prop022FactorialCoefficientsR115
open Prop024ContractionsR54 Prop024DoubleSeriesR53

variable {L : ℝ} [Fact (0 < L)]
attribute [local instance] InnerProductSpace.complexToReal

/-- A product of two m-slot binomial choices is one term in the Vandermonde
sum, hence no larger than the combined 2m-slot choice. -/
theorem choose_product_le_double (m a b : ℕ) :
    m.choose a * m.choose b ≤ (2*m).choose (a+b) := by
  have hv :
      ∑ s ∈ Finset.range (a+b+1), m.choose s * m.choose (a+b-s) =
        (m+m).choose (a+b) := by
    rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
      (fun ij : ℕ × ℕ => m.choose ij.1 * m.choose ij.2) (a+b),
      ← Nat.add_choose_eq]
  have ha : a ∈ Finset.range (a+b+1) := Finset.mem_range.mpr (by omega)
  have hs :
      m.choose a * m.choose (a+b-a) ≤
        ∑ s ∈ Finset.range (a+b+1), m.choose s * m.choose (a+b-s) :=
    Finset.single_le_sum (f := fun s => m.choose s * m.choose (a+b-s))
      (fun s hs => Nat.zero_le _) ha
  have hab : a+b-a=b := by omega
  rw [hab] at hs
  have htwo : m+m = 2*m := by omega
  rw [htwo] at hv
  exact hs.trans_eq hv

/-- Vandermonde's identity in the two contraction indices. -/
theorem choose_product_sum_eq (m j : ℕ) :
    ∑ a ∈ Finset.range (j+1), m.choose a * m.choose (j-a) =
      (2*m).choose j := by
  rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
    (fun ij : ℕ × ℕ => m.choose ij.1 * m.choose ij.2) j,
    ← Nat.add_choose_eq]
  simp [two_mul]

/-- The actual (a,b) contraction cell, including the source binomial
coefficients and PROP-023 square-root moment factor. -/
def contractedCell (m a b : ℕ) (ha : a ≤ m) (hb : b ≤ m)
    (B : ∀ r, HN L r →L[ℂ] HN L r) (u : L2T L) (Q N : ℝ) : ℝ :=
  (‖contractedKernel m a b ha hb B u‖ * (m.choose a : ℝ) * (m.choose b : ℝ)) *
    (Real.sqrt (32 * Q * (a+b) / N)) ^ (a+b)

/-- Sum the actual physical contraction norms at a fixed interaction order
and total Wick degree. Invalid slot choices are zero, matching the vanishing
binomial coefficients in Vandermonde's identity. -/
def contractedSliceCell (m j : ℕ)
    (B : ∀ r, HN L r →L[ℂ] HN L r) (u : L2T L) (Q N : ℝ) : ℝ :=
  ∑ a ∈ Finset.range (j+1),
    if ha : a ≤ m then
      if hb : j-a ≤ m then
        contractedCell m a (j-a) ha hb B u Q N
      else 0
    else 0

/-- Every actual physical contraction cell is bounded by its R53
factorial/geometric reindexing cell. -/
theorem contractedCell_le_reindexedCell (m a b : ℕ)
    (ha : a ≤ m) (hb : b ≤ m) (hm : 1 ≤ m)
    (B : ∀ r, HN L r →L[ℂ] HN L r) (u : L2T L) (hu : ‖u‖ = 1)
    (M A Q N : ℝ) (hM : 0 ≤ M) (hA : 0 < A)
    (hQ : 0 ≤ Q) (hN : 0 < N)
    (hB : FactorialBound B M A) (hj : 3 ≤ a+b) :
    contractedCell m a b ha hb B u Q N ≤
      M * reindexedCell A Q N (a+b) (2*m-(a+b)) := by
  have hjm : a+b ≤ 2*m := by omega
  have hkernel := contractedKernel_factorial_bound m a b ha hb B u hu M A hB hm
  have hchooseNat := choose_product_le_double m a b
  have hchoose : (m.choose a : ℝ) * (m.choose b : ℝ) ≤
      ((2*m).choose (a+b) : ℝ) := by exact_mod_cast hchooseNat
  have ha0 : 0 ≤ (m.choose a : ℝ) := Nat.cast_nonneg _
  have hb0 : 0 ≤ (m.choose b : ℝ) := Nat.cast_nonneg _
  have hmom0 : 0 ≤ (Real.sqrt (32 * Q * (a+b) / N)) ^ (a+b) := by positivity
  have hcoeff0 : 0 ≤ M * A^m / Real.sqrt ((2*m).factorial : ℝ) := by positivity
  have hcell := wickCell_le_reindexedCell A Q N hA hQ hN m (a+b) hj hjm
  unfold contractedCell
  calc
    (‖contractedKernel m a b ha hb B u‖ * (m.choose a : ℝ) *
        (m.choose b : ℝ)) *
        (Real.sqrt (32 * Q * (a+b) / N)) ^ (a+b) ≤
      ((M * A^m / Real.sqrt ((2*m).factorial : ℝ)) *
        (m.choose a : ℝ) * (m.choose b : ℝ)) *
        (Real.sqrt (32 * Q * (a+b) / N)) ^ (a+b) := by
      gcongr
    _ ≤ M * wickCell A Q N m (a+b) := by
      unfold wickCell
      simp only [Nat.cast_add]
      calc
        ((M * A^m / Real.sqrt ((2*m).factorial : ℝ)) *
            (m.choose a : ℝ) * (m.choose b : ℝ)) *
            (Real.sqrt (32 * Q * (a+b) / N)) ^ (a+b) =
          ((M * A^m / Real.sqrt ((2*m).factorial : ℝ)) *
            ((m.choose a : ℝ) * (m.choose b : ℝ))) *
            (Real.sqrt (32 * Q * (a+b) / N)) ^ (a+b) := by ring
        _ ≤ ((M * A^m / Real.sqrt ((2*m).factorial : ℝ)) *
            ((2*m).choose (a+b) : ℝ)) *
            (Real.sqrt (32 * Q * (a+b) / N)) ^ (a+b) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hchoose hcoeff0) hmom0
        _ = M *
            ((A^m / Real.sqrt ((2*m).factorial : ℝ)) *
              ((2*m).choose (a+b) : ℝ) *
              (Real.sqrt (32 * Q * (a+b) / N)) ^ (a+b)) := by
          ring
    _ ≤ M * reindexedCell A Q N (a+b) (2*m-(a+b)) :=
      by simpa only [Nat.cast_add] using (mul_le_mul_of_nonneg_left hcell hM)

/-- Summing all physical contractions with fixed total degree recovers the
single scalar Wick cell. This is the operator-side Vandermonde comparison
needed before the frozen R53 reindexing. -/
theorem contractedSliceCell_le_wickCell (m j : ℕ)
    (hj : 3 ≤ j) (hjm : j ≤ 2*m)
    (B : ∀ r, HN L r →L[ℂ] HN L r) (u : L2T L) (hu : ‖u‖ = 1)
    (M A Q N : ℝ) (hM : 0 ≤ M) (hA : 0 < A)
    (hB : FactorialBound B M A) :
    contractedSliceCell m j B u Q N ≤ M * wickCell A Q N m j := by
  have hm : 1 ≤ m := by omega
  have hmoment : 0 ≤ (Real.sqrt (32*Q*j/N))^j := by positivity
  have hchooseSum :
      ∑ a ∈ Finset.range (j+1),
        (m.choose a : ℝ) * (m.choose (j-a) : ℝ) =
        ((2*m).choose j : ℝ) := by
    exact_mod_cast choose_product_sum_eq m j
  unfold contractedSliceCell
  calc
    (∑ a ∈ Finset.range (j+1),
        if ha : a ≤ m then
          if hb : j-a ≤ m then
            contractedCell m a (j-a) ha hb B u Q N
          else 0
        else 0)
      ≤ ∑ a ∈ Finset.range (j+1),
          (M * (A^m / Real.sqrt ((2*m).factorial : ℝ)) *
            (m.choose a : ℝ) * (m.choose (j-a) : ℝ)) *
            (Real.sqrt (32*Q*j/N))^j := by
        apply Finset.sum_le_sum
        intro a haRange
        have haj : a ≤ j := by
          have h := Finset.mem_range.mp haRange
          omega
        have hsum : a + (j-a) = j := Nat.add_sub_of_le haj
        have hsumR : (a : ℝ) + ((j-a : ℕ) : ℝ) = (j : ℝ) := by
          exact_mod_cast hsum
        by_cases ha : a ≤ m
        · by_cases hb : j-a ≤ m
          · have hkernel := contractedKernel_factorial_bound m a (j-a) ha hb
              B u hu M A hB hm
            simp only [dif_pos ha, dif_pos hb]
            unfold contractedCell
            rw [hsum, hsumR]
            have hca : 0 ≤ (m.choose a : ℝ) := Nat.cast_nonneg _
            have hcb : 0 ≤ (m.choose (j-a) : ℝ) := Nat.cast_nonneg _
            have hfac : 0 ≤ (Real.sqrt (32*Q*j/N))^j := hmoment
            calc
              (‖contractedKernel m a (j-a) ha hb B u‖ *
                  (m.choose a : ℝ) * (m.choose (j-a) : ℝ)) *
                  (Real.sqrt (32*Q*j/N))^j
                ≤ ((M * A^m / Real.sqrt ((2*m).factorial : ℝ)) *
                    (m.choose a : ℝ) * (m.choose (j-a) : ℝ)) *
                    (Real.sqrt (32*Q*j/N))^j := by gcongr
              _ = (M * (A^m / Real.sqrt ((2*m).factorial : ℝ)) *
                    (m.choose a : ℝ) * (m.choose (j-a) : ℝ)) *
                    (Real.sqrt (32*Q*j/N))^j := by ring
          · simp only [dif_pos ha, dif_neg hb]
            positivity
        · simp only [dif_neg ha]
          positivity
    _ = (M * (A^m / Real.sqrt ((2*m).factorial : ℝ)) *
          ((2*m).choose j : ℝ)) * (Real.sqrt (32*Q*j/N))^j := by
        calc
          _ = ∑ a ∈ Finset.range (j+1),
                (M * (A^m / Real.sqrt ((2*m).factorial : ℝ)) *
                  (Real.sqrt (32*Q*j/N))^j) *
                  ((m.choose a : ℝ) * (m.choose (j-a) : ℝ)) := by
            apply Finset.sum_congr rfl
            intro a ha
            ring
          _ = (M * (A^m / Real.sqrt ((2*m).factorial : ℝ)) *
                (Real.sqrt (32*Q*j/N))^j) *
                ∑ a ∈ Finset.range (j+1),
                  (m.choose a : ℝ) * (m.choose (j-a) : ℝ) := by
            rw [Finset.mul_sum]
          _ = _ := by rw [hchooseSum]; ring
    _ = M * wickCell A Q N m j := by
        unfold wickCell
        ring

end QuantumNLS.Prop024WickCellsR54

#print axioms QuantumNLS.Prop024WickCellsR54.choose_product_le_double
#print axioms QuantumNLS.Prop024WickCellsR54.contractedCell_le_reindexedCell

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop024WickCellsR54." ||
        n.toString.startsWith "_private.QuantumNLS.Prop024WickCellsR54." then
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
  Lean.logInfo m!"R54 operator-cell aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
