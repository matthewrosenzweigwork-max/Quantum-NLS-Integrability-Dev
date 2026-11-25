import QuantumNLS.Ext005MomentEnergyR108

/-! R108: the absolutely convergent physical pair-sector weight-difference
series for every positive integer number moment. The diagonal expression
below is the sector expression needed for the commutator form. No evolution,
weak-solution uniqueness, or time-dependent commutator identity is asserted. -/
noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace
namespace QuantumNLS.Ext005PairCommutatorR108
open Ext025B3PhysicalSectors Ext005Moments Ext005PairSector
open Ext005MomentEnergyR108 BetheCoefficientTransform
variable {L : ℝ} [Fact (0 < L)]

def differenceConstant (j : ℕ) : ℝ := 2 * (j : ℝ) * 3 ^ (j - 1)

theorem differenceConstant_nonneg (j : ℕ) : 0 ≤ differenceConstant j := by
  unfold differenceConstant
  positivity

/-- Literal annihilation block matrix element times the moment difference. -/
def differenceTerm (j : ℕ) (b : HN L 2) (x : Fock L) (n : ℕ) : ℂ :=
  ((momentWeight j n - momentWeight j (n + 2) : ℝ) : ℂ) *
    ⟪x n, annihilation b n (x (2 + n))⟫_ℂ

theorem differenceTerm_bound (j : ℕ) (b : HN L 2) (x : Fock L) (n : ℕ) :
    ‖differenceTerm j b x n‖ ≤ differenceConstant j * ‖b‖ *
      (((n : ℝ) + 1) ^ (j - 1) *
        (Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) * ‖x n‖ * ‖x (n + 2)‖)) := by
  have hw : |momentWeight j n - momentWeight j (n + 2)| ≤
      differenceConstant j * ((n : ℝ) + 1) ^ (j - 1) := by
    simpa only [momentWeight, Nat.cast_add, Nat.cast_ofNat, show (n : ℝ) + 2 + 1 =
      (n : ℝ) + 3 by ring, differenceConstant] using Ext005PairBounds.weight_difference j n
  have he : ‖⟪x n, annihilation b n (x (2 + n))⟫_ℂ‖ ≤
      ‖b‖ * (Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) * ‖x n‖ * ‖x (n + 2)‖) := by
    calc
      _ ≤ ‖x n‖ * ‖annihilation b n (x (2 + n))‖ := norm_inner_le_norm _ _
      _ ≤ ‖x n‖ * (‖b‖ * Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) *
          ‖x (2 + n)‖) :=
        mul_le_mul_of_nonneg_left (annihilation_bound b n _) (norm_nonneg _)
      _ = _ := by rw [Nat.add_comm 2 n]; ring
  unfold differenceTerm
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ (differenceConstant j * ((n : ℝ) + 1) ^ (j - 1)) *
        (‖b‖ * (Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) * ‖x n‖ * ‖x (n + 2)‖)) :=
      mul_le_mul hw he (norm_nonneg _)
        (mul_nonneg (differenceConstant_nonneg j) (pow_nonneg (by positivity) _))
    _ = _ := by ring

/-- The weight difference is controlled by the j-th moment on its actual
maximal form domain, with no sector bound supplied as a hypothesis. -/
theorem difference_series_bound (j : ℕ) (hj : 1 ≤ j) (b : HN L 2)
    (x : momentDomain (L := L) j) :
    Summable (differenceTerm j b x.val) ∧
      ‖∑' n, differenceTerm j b x.val n‖ ≤ differenceConstant j * ‖b‖ * energy j x.val := by
  have hq := (momentDomain_iff j x.val).1 x.property
  have heq : j - 1 + 1 = j := by omega
  have hq' : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (j - 1 + 1) * ‖x.val n‖ ^ 2) := by
    simpa only [heq, momentWeight] using hq
  obtain ⟨hp, hb⟩ := Ext005PairBounds.weighted_pair_series (j - 1)
    (fun n => ‖x.val n‖) (fun n => norm_nonneg _) hq'
  have hb' : (∑' n : ℕ, ((n : ℝ) + 1) ^ (j - 1) *
      (Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) * ‖x.val n‖ * ‖x.val (n + 2)‖)) ≤
      energy j x.val := by
    simpa only [heq, energy, momentWeight] using hb
  have hm := hp.mul_left (differenceConstant j * ‖b‖)
  have habs : Summable (fun n => ‖differenceTerm j b x.val n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (differenceTerm_bound j b x.val) hm
  refine ⟨Summable.of_norm habs, ?_⟩
  calc
    _ ≤ ∑' n, ‖differenceTerm j b x.val n‖ := norm_tsum_le_tsum_norm habs
    _ ≤ ∑' n : ℕ, differenceConstant j * ‖b‖ *
        (((n : ℝ) + 1) ^ (j - 1) *
          (Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) * ‖x.val n‖ * ‖x.val (n + 2)‖)) :=
      habs.tsum_le_tsum (differenceTerm_bound j b x.val) hm
    _ = differenceConstant j * ‖b‖ * (∑' n : ℕ, ((n : ℝ) + 1) ^ (j - 1) *
        (Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) * ‖x.val n‖ * ‖x.val (n + 2)‖)) := by
      rw [tsum_mul_left]
    _ ≤ _ := mul_le_mul_of_nonneg_left hb'
      (mul_nonneg (differenceConstant_nonneg j) (norm_nonneg _))

/-- Diagonal sector expression for i[Q_pair,(Num+1)^j], with the report's
one-half normalization of Q_pair. Operator/core identification is separate. -/
def diagonalCommutator (j : ℕ) (b : HN L 2) (x : Fock L) : ℂ :=
  (Complex.I / 2) * (star (∑' n, differenceTerm j b x n) - ∑' n, differenceTerm j b x n)

theorem diagonalCommutator_real (j : ℕ) (b : HN L 2) (x : Fock L) :
    (diagonalCommutator j b x).im = 0 := by
  simp [diagonalCommutator, Complex.mul_im, Complex.div_ofNat]

theorem diagonalCommutator_bound (j : ℕ) (hj : 1 ≤ j) (b : HN L 2)
    (x : momentDomain (L := L) j) :
    ‖diagonalCommutator j b x.val‖ ≤ differenceConstant j * ‖b‖ * energy j x.val := by
  have hb := (difference_series_bound j hj b x).2
  let z := ∑' n, differenceTerm j b x.val n
  have hn : ‖star z - z‖ ≤ 2 * ‖z‖ := by
    calc
      _ ≤ ‖star z‖ + ‖z‖ := norm_sub_le _ _
      _ = _ := by rw [norm_star]; ring
  have hc : ‖Complex.I / 2‖ = (1 / 2 : ℝ) := by norm_num
  unfold diagonalCommutator
  rw [norm_mul, hc]
  change (1 / 2 : ℝ) * ‖star z - z‖ ≤ _
  change ‖z‖ ≤ _ at hb
  nlinarith

end QuantumNLS.Ext005PairCommutatorR108
#print axioms QuantumNLS.Ext005PairCommutatorR108.differenceTerm_bound
#print axioms QuantumNLS.Ext005PairCommutatorR108.difference_series_bound
#print axioms QuantumNLS.Ext005PairCommutatorR108.diagonalCommutator_bound
#print axioms QuantumNLS.Ext005PairCommutatorR108.diagonalCommutator_real

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005PairCommutatorR108." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005PairCommutatorR108." then
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
  Lean.logInfo m!"R108 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
