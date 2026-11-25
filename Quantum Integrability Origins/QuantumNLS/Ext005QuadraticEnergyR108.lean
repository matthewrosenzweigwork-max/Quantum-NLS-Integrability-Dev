import QuantumNLS.Ext005MomentEnergyR108
import QuantumNLS.PhysicalPlacements

/-! R108: static energy bounds for the literal physical quadratic sector
forms. The number-preserving operator is n times the average one-body
placement. This module does not construct a propagator or assume its energy
estimates. Time regularity and the energy-bounded weak evolution remain
separate obligations. -/
noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace
namespace QuantumNLS.Ext005QuadraticEnergyR108
open Ext025B3PhysicalSectors Ext005Moments Ext005PairSector
open Ext005MomentEnergyR108 BetheCoefficientTransform
variable {L : ℝ} [Fact (0 < L)]

/-- Actual number-preserving quadratic block; zero on the vacuum sector. -/
def numberBlock (a : HN L 1 →L[ℂ] HN L 1) (n : ℕ) : HN L n →L[ℂ] HN L n :=
  if hn : 1 ≤ n then (n : ℂ) • PhysicalPlacements.physicalQ_N_p L n 1 hn a else 0

theorem numberBlock_bound (a : HN L 1 →L[ℂ] HN L 1) (n : ℕ) (v : HN L n) :
    ‖numberBlock a n v‖ ≤ ‖a‖ * (n : ℝ) * ‖v‖ := by
  unfold numberBlock
  split_ifs with hn
  · simp only [smul_apply, norm_smul, Complex.norm_natCast]
    have h := PhysicalPlacements.norm_physicalQ_N_p_le L n 1 hn a
    calc
      _ ≤ (n : ℝ) * (‖PhysicalPlacements.physicalQ_N_p L n 1 hn a‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (Nat.cast_nonneg n)
      _ ≤ (n : ℝ) * (‖a‖ * ‖v‖) := by gcongr
      _ = _ := by ring
  · simp only [zero_apply, norm_zero]
    positivity

def numberTerm (a : HN L 1 →L[ℂ] HN L 1) (x : Fock L) (n : ℕ) : ℂ :=
  ⟪x n, numberBlock a n (x n)⟫_ℂ

def numberForm (a : HN L 1 →L[ℂ] HN L 1) (x : Fock L) : ℂ :=
  ∑' n, numberTerm a x n

theorem numberTerm_bound (a : HN L 1 →L[ℂ] HN L 1) (x : Fock L) (n : ℕ) :
    ‖numberTerm a x n‖ ≤ ‖a‖ * (momentWeight 1 n * ‖x n‖ ^ 2) := by
  calc
    _ ≤ ‖x n‖ * ‖numberBlock a n (x n)‖ := norm_inner_le_norm _ _
    _ ≤ ‖x n‖ * (‖a‖ * (n : ℝ) * ‖x n‖) :=
      mul_le_mul_of_nonneg_left (numberBlock_bound a n _) (norm_nonneg _)
    _ ≤ _ := by
      simp only [momentWeight, pow_one]
      nlinarith [mul_nonneg (norm_nonneg a) (sq_nonneg ‖x n‖)]

/-- The actual number-preserving form is absolutely convergent on Q(Num+1). -/
theorem numberForm_bound (a : HN L 1 →L[ℂ] HN L 1)
    (x : momentDomain (L := L) 1) :
    Summable (numberTerm a x.val) ∧ ‖numberForm a x.val‖ ≤ ‖a‖ * energy 1 x.val := by
  have hq := (momentDomain_iff 1 x.val).1 x.property
  have hm := hq.mul_left ‖a‖
  have hs : Summable (fun n => ‖numberTerm a x.val n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (numberTerm_bound a x.val) hm
  refine ⟨Summable.of_norm hs, ?_⟩
  calc
    _ ≤ ∑' n, ‖numberTerm a x.val n‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n, ‖a‖ * (momentWeight 1 n * ‖x.val n‖ ^ 2) :=
      hs.tsum_le_tsum (numberTerm_bound a x.val) hm
    _ = _ := by rw [tsum_mul_left]; rfl

/-- Full quadratic diagonal form, using the report's one-half coefficient. -/
def quadraticForm (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2)
    (x : momentDomain (L := L) 1) : ℂ :=
  numberForm a x.val + (1 / 2 : ℂ) * pairHamiltonian b x

theorem half_pair_bound (b : HN L 2) (x : momentDomain (L := L) 1) :
    ‖(1 / 2 : ℂ) * pairHamiltonian b x‖ ≤ ‖b‖ * energy 1 x.val := by
  have h := pairHamiltonian_bound b x
  rw [← energy_eq_root 1 x] at h
  rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num]
  linarith

theorem quadraticForm_bound (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2)
    (x : momentDomain (L := L) 1) :
    ‖quadraticForm a b x‖ ≤ (‖a‖ + ‖b‖) * energy 1 x.val := by
  calc
    _ ≤ ‖numberForm a x.val‖ + ‖(1 / 2 : ℂ) * pairHamiltonian b x‖ := norm_add_le _ _
    _ ≤ ‖a‖ * energy 1 x.val + ‖b‖ * energy 1 x.val :=
      add_le_add (numberForm_bound a x).2 (half_pair_bound b x)
    _ = _ := by ring

/-- Every positive number moment controls the full quadratic diagonal form. -/
theorem quadraticForm_bound_higher (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2)
    (j : ℕ) (hj : 1 ≤ j) (x : momentDomain (L := L) j) :
    ‖quadraticForm a b ⟨x.val, domain_mono hj x.property⟩‖ ≤
      (‖a‖ + ‖b‖) * energy j x.val := by
  exact (quadraticForm_bound a b ⟨x.val, domain_mono hj x.property⟩).trans
    (mul_le_mul_of_nonneg_left (energy_mono hj x.property) (by positivity))

/-- An explicit comparator constant satisfies the LNS lower form inequality
with A=B=(Num+1)^j. This is a form estimate, not an evolution estimate. -/
theorem quadraticForm_lower (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2)
    (j : ℕ) (hj : 1 ≤ j) (x : momentDomain (L := L) j) :
    (‖a‖ + ‖b‖ + 2)⁻¹ * energy j x.val -
      (‖a‖ + ‖b‖ + 2) * energy j x.val ≤
        (quadraticForm a b ⟨x.val, domain_mono hj x.property⟩).re := by
  have h := quadraticForm_bound_higher a b j hj x
  have hr := Complex.abs_re_le_norm (quadraticForm a b ⟨x.val, domain_mono hj x.property⟩)
  have hi : (‖a‖ + ‖b‖ + 2)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by linarith [norm_nonneg a, norm_nonneg b])
  apply lower_bound_with_equal_comparators (energy j x.val)
    (quadraticForm a b ⟨x.val, domain_mono hj x.property⟩).re
    (‖a‖ + ‖b‖) (‖a‖ + ‖b‖ + 2) (energy_nonneg j x.val)
  · linarith
  · have := neg_abs_le (quadraticForm a b ⟨x.val, domain_mono hj x.property⟩).re
    linarith

end QuantumNLS.Ext005QuadraticEnergyR108
#print axioms QuantumNLS.Ext005QuadraticEnergyR108.numberBlock_bound
#print axioms QuantumNLS.Ext005QuadraticEnergyR108.numberForm_bound
#print axioms QuantumNLS.Ext005QuadraticEnergyR108.quadraticForm_bound_higher
#print axioms QuantumNLS.Ext005QuadraticEnergyR108.quadraticForm_lower

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005QuadraticEnergyR108." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005QuadraticEnergyR108." then
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
