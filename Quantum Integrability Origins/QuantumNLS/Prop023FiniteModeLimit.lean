import QuantumNLS.Ext006PhysicalVacuum

/-! Literal finite-mode approximation of number expectations on physical Fock
space. This proves the limiting passage; it does not assume or prove that the
finite-mode distributions of a quasifree vacuum are the squeezed products. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped ENNReal
namespace QuantumNLS.Prop023FiniteModeLimit
open Occupation Ext006PhysicalVacuum Ext006NumberPhase Ext025B3PhysicalSectors
open BetheCoefficientTransform
variable {L : ℝ} [Fact (0 < L)]

/-- The number of particles in the indicated finite set of free Fourier modes. -/
def finiteNumber (s : Finset ℤ) (m : Occ) : ℕ := ∑ a ∈ s, m a

lemma finiteNumber_eq_total {s : Finset ℤ} {m : Occ} (h : m.support ⊆ s) :
    finiteNumber s m = total m := by
  symm
  apply Finset.sum_subset h
  intro a _ ha
  exact Finsupp.notMem_support_iff.mp ha

lemma finiteNumber_le_total (s : Finset ℤ) (m : Occ) : finiteNumber s m ≤ total m := by
  classical
  calc
    finiteNumber s m ≤ finiteNumber (s ∪ m.support) m :=
      Finset.sum_le_sum_of_subset Finset.subset_union_left
    _ = total m := finiteNumber_eq_total Finset.subset_union_right

/-- The physical occupation probability mass, with no normalization premise. -/
def mass (x : Fock L) (m : Occ) : ℝ≥0∞ := ENNReal.ofReal (‖coefficient x m‖^2)

lemma sector_mass (x : Fock L) (n : ℕ) :
    (∑' m : Arr n, mass x m.val) = ENNReal.ofReal (‖x n‖^2) := by
  let c := occupationCoefficient (freeBasis L n) (x n)
  have he : ∀ m : Arr n, coefficient x m.val = c m := by
    rintro ⟨m,hm⟩
    change total m = n at hm
    subst n
    rfl
  have hs := lp.hasSum_norm (p := 2) (by norm_num) c
  have hr : (∑' m, ‖c m‖^2) = ‖x n‖^2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, c, LinearIsometryEquiv.norm_map]
      using hs.tsum_eq
  calc
    (∑' m : Arr n, mass x m.val) = ∑' m, ENNReal.ofReal (‖c m‖^2) := by
      apply tsum_congr
      intro m
      rw [mass, he]
    _ = ENNReal.ofReal (∑' m, ‖c m‖^2) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _)
        (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs.summable)).symm
    _ = ENNReal.ofReal (‖x n‖^2) := congrArg ENNReal.ofReal hr

/-- Parseval and the grouping by exact total particle number identify the
occupation law with the existing physical number expectation. -/
theorem numberExpectation_eq_occupation (x : Fock L) (w : ℕ → ℝ≥0∞) :
    numberExpectation w x = ∑' m : Occ, w (total m) * mass x m := by
  have hf := ENNReal.tsum_fiberwise (fun m : Occ => w (total m) * mass x m) total
  rw [← hf]
  unfold numberExpectation
  apply tsum_congr
  intro n
  change w n * ENNReal.ofReal (‖x n‖^2) =
    ∑' m : Arr n, w (total m.val) * mass x m.val
  have he : (fun m : Arr n => w (total m.val) * mass x m.val) =
      fun m : Arr n => w n * mass x m.val := by
    funext m
    rw [show total m.val = n from m.property]
  rw [he, ENNReal.tsum_mul_left, sector_mass]

/-- Spectral expectation of the finite-mode number function. -/
def finiteExpectation (s : Finset ℤ) (w : ℕ → ℝ≥0∞) (x : Fock L) : ℝ≥0∞ :=
  ∑' m : Occ, w (finiteNumber s m) * mass x m

/-- Monotone convergence for all nonnegative increasing number weights,
proved using the actual finite support of every occupation array. -/
theorem numberExpectation_eq_iSup_finite (x : Fock L) (w : ℕ → ℝ≥0∞)
    (hw : Monotone w) :
    numberExpectation w x = ⨆ s : Finset ℤ, finiteExpectation s w x := by
  classical
  rw [numberExpectation_eq_occupation]
  apply le_antisymm
  · rw [ENNReal.tsum_eq_iSup_sum]
    apply iSup_le
    intro t
    let s : Finset ℤ := t.biUnion Finsupp.support
    apply le_iSup_of_le s
    unfold finiteExpectation
    calc
      (∑ m ∈ t, w (total m) * mass x m) =
          ∑ m ∈ t, w (finiteNumber s m) * mass x m := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [finiteNumber_eq_total (Finset.subset_biUnion_of_mem Finsupp.support hm)]
      _ ≤ ∑' m, w (finiteNumber s m) * mass x m := ENNReal.sum_le_tsum t
  · apply iSup_le
    intro s
    apply ENNReal.tsum_le_tsum
    intro m
    exact mul_le_mul' (hw (finiteNumber_le_total s m)) le_rfl

/-- The exact exponential observable in PROP-023 is the supremum of its
finite-mode expectations. This holds for every physical Fock vector. -/
theorem exponentialMoment_eq_iSup_finite (x : Fock L) (Q : ℝ) (hQ : 1 ≤ Q) :
    exponentialMoment Q x =
      ⨆ s : Finset ℤ, finiteExpectation s
        (fun n => ENNReal.ofReal (Real.exp ((n : ℝ)/(16*Q)))) x := by
  apply numberExpectation_eq_iSup_finite
  intro a b hab
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right (by exact_mod_cast hab) (by positivity)

end QuantumNLS.Prop023FiniteModeLimit

#print axioms QuantumNLS.Prop023FiniteModeLimit.finiteNumber_eq_total
#print axioms QuantumNLS.Prop023FiniteModeLimit.sector_mass
#print axioms QuantumNLS.Prop023FiniteModeLimit.numberExpectation_eq_occupation
#print axioms QuantumNLS.Prop023FiniteModeLimit.numberExpectation_eq_iSup_finite
#print axioms QuantumNLS.Prop023FiniteModeLimit.exponentialMoment_eq_iSup_finite

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop023FiniteModeLimit." then
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
