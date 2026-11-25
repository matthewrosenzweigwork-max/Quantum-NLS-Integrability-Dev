import QuantumNLS.Ext005PairSector
import QuantumNLS.Ext006ZeroVacuum

/-! Actual physical pair-creation exponential terms and truncations.
The recursion uses the frozen adjoint creation blocks, including the sign,
1/2 and factorial. It is defined for every physical two-particle tensor.
The bound below gives a local convergence disk in the pair-tensor norm.
It does not prove convergence at every HS strict operator contraction.
No summability, norm identity, or quasifree identification is assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Filter Topology
open scoped InnerProductSpace
namespace QuantumNLS.Ext006PhysicalExponentialTerms
open BetheCoefficientTransform Ext025B3PhysicalSectors Ext005PairSector
variable {L : ℝ} [Fact (0 < L)]

/-- Particle-sector transport, preserving the physical vector and its norm. -/
def sectorCast {n m : ℕ} (h : n = m) : HN L n ≃ₗᵢ[ℂ] HN L m := by
  subst m
  exact LinearIsometryEquiv.refl ℂ _

/-- The coefficient converting the n-th exponential term to the next. -/
def stepScalar (n : ℕ) : ℂ := ((-(2 * ((n : ℝ)+1))⁻¹ : ℝ) : ℂ)

lemma norm_stepScalar (n : ℕ) : ‖stepScalar n‖ = (2 * ((n : ℝ)+1))⁻¹ := by
  rw [stepScalar, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_inv,
    abs_of_pos (by positivity : 0 < 2*((n : ℝ)+1))]

/-- The literal homogeneous term (-a*(b)/2)^n Omega/n! in sector 2n.
There is no smallness or finite-rank restriction on b in this definition. -/
def term (b : HN L 2) : (n : ℕ) → HN L (2*n)
  | 0 => Ext006ZeroVacuum.sectorVacuum L
  | n+1 => sectorCast (by omega : 2+2*n = 2*(n+1))
      (stepScalar n • creation b (2*n) (term b n))

lemma term_zero (b : HN L 2) : term b 0 = Ext006ZeroVacuum.sectorVacuum L := rfl

lemma term_zero_norm (b : HN L 2) : ‖term b 0‖ = 1 :=
  Ext006ZeroVacuum.sectorVacuum_norm L

/-- The actual pair-creation recursion, with exact factorial denominator. -/
lemma term_step (b : HN L 2) (n : ℕ) :
    term b (n+1) = sectorCast (by omega : 2+2*n = 2*(n+1))
      (stepScalar n • creation b (2*n) (term b n)) := rfl

lemma step_ratio_le_one (n : ℕ) :
    (2*((n : ℝ)+1))⁻¹ * Real.sqrt (((2*n : ℕ) : ℝ)+1) *
      Real.sqrt (((2*n : ℕ) : ℝ)+2) ≤ 1 := by
  have h0 : 0 ≤ (((2*n : ℕ) : ℝ)+1) := by positivity
  have h1 : 0 ≤ (((2*n : ℕ) : ℝ)+2) := by positivity
  have hs0 := Real.sq_sqrt h0
  have hs1 := Real.sq_sqrt h1
  have hb : Real.sqrt (((2*n : ℕ) : ℝ)+1) ≤ Real.sqrt (((2*n : ℕ) : ℝ)+2) :=
    Real.sqrt_le_sqrt (by linarith)
  have hp : Real.sqrt (((2*n : ℕ) : ℝ)+1) *
      Real.sqrt (((2*n : ℕ) : ℝ)+2) ≤ 2*((n : ℝ)+1) := by
    have h := mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg (((2*n : ℕ) : ℝ)+2))
    push_cast at h hs1 ⊢
    nlinarith
  have hd : 0 < 2*((n : ℝ)+1) := by positivity
  calc
    _ = (2*((n : ℝ)+1))⁻¹ *
      (Real.sqrt (((2*n : ℕ) : ℝ)+1) * Real.sqrt (((2*n : ℕ) : ℝ)+2)) := by ring
    _ ≤ (2*((n : ℝ)+1))⁻¹ * (2*((n : ℝ)+1)) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = 1 := inv_mul_cancel₀ hd.ne'

/-- Unconditional bound on successive physical homogeneous terms. -/
theorem term_norm_step (b : HN L 2) (n : ℕ) :
    ‖term b (n+1)‖ ≤ ‖b‖ * ‖term b n‖ := by
  rw [term_step, LinearIsometryEquiv.norm_map, norm_smul, norm_stepScalar]
  calc
    _ ≤ (2*((n : ℝ)+1))⁻¹ *
      (‖b‖ * Real.sqrt ((((2*n : ℕ) : ℝ)+1)*(((2*n : ℕ) : ℝ)+2)) * ‖term b n‖) :=
      mul_le_mul_of_nonneg_left (creation_bound b (2*n) _) (by positivity)
    _ = ((2*((n : ℝ)+1))⁻¹ * Real.sqrt (((2*n : ℕ) : ℝ)+1) *
      Real.sqrt (((2*n : ℕ) : ℝ)+2)) * (‖b‖ * ‖term b n‖) := by
      rw [Real.sqrt_mul (by positivity)]
      ring
    _ ≤ 1 * (‖b‖ * ‖term b n‖) :=
      mul_le_mul_of_nonneg_right (step_ratio_le_one n) (by positivity)
    _ = _ := one_mul _

theorem term_norm_bound (b : HN L 2) (n : ℕ) : ‖term b n‖ ≤ ‖b‖^n := by
  induction n with
  | zero => rw [term_zero_norm, pow_zero]
  | succ n ih =>
    calc
      _ ≤ ‖b‖ * ‖term b n‖ := term_norm_step b n
      _ ≤ ‖b‖ * ‖b‖^n := mul_le_mul_of_nonneg_left ih (norm_nonneg b)
      _ = _ := by rw [pow_succ]; ring

/-- Embed the homogeneous term in the actual completed physical Fock space. -/
def fockTerm (b : HN L 2) (n : ℕ) : Fock L := inclusion L (2*n) (term b n)

lemma fockTerm_eq_single (b : HN L 2) (n : ℕ) :
    fockTerm b n = lp.single 2 (2*n) (term b n) := rfl

lemma fockTerm_norm (b : HN L 2) (n : ℕ) : ‖fockTerm b n‖ = ‖term b n‖ :=
  (inclusion L (2*n)).norm_map _

lemma fockTerm_other (b : HN L 2) (n m : ℕ) (hm : m ≠ 2*n) :
    fockTerm b n m = 0 := by
  rw [fockTerm_eq_single, lp.single_apply_ne _ _ _ hm]

lemma fockTerm_same (b : HN L 2) (n : ℕ) : fockTerm b n (2*n) = term b n := by
  rw [fockTerm_eq_single, lp.single_apply_self]

/-- Finite exponential polynomials; defined for every physical pair tensor. -/
def truncation (b : HN L 2) (M : ℕ) : Fock L := ∑ n ∈ Finset.range M, fockTerm b n

lemma truncation_odd (b : HN L 2) (M n : ℕ) : truncation b M (2*n+1) = 0 := by
  change (lp.evalCLM (E := fun n => HN L n) (p := 2) ℂ (2*n+1))
    (∑ k ∈ Finset.range M, fockTerm b k) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro k _
  exact fockTerm_other b k (2*n+1) (by omega)

lemma truncation_even (b : HN L 2) (M n : ℕ) (hn : n < M) :
    truncation b M (2*n) = term b n := by
  change (lp.evalCLM (E := fun n => HN L n) (p := 2) ℂ (2*n))
    (∑ k ∈ Finset.range M, fockTerm b k) = term b n
  rw [map_sum]
  rw [Finset.sum_eq_single_of_mem n (Finset.mem_range.mpr hn)]
  · exact fockTerm_same b n
  · intro k _ hkn
    exact fockTerm_other b k (2*n) (by omega)

/-- Orthogonality of distinct exponential degrees in the physical Fock space. -/
theorem fockTerm_orthogonal (b : HN L 2) {n m : ℕ} (hnm : n ≠ m) :
    inner ℂ (fockTerm b n) (fockTerm b m) = 0 := by
  rw [fockTerm_eq_single, lp.inner_single_left]
  rw [fockTerm_other b m (2*n) (by omega), inner_zero_right]

/-- A proved local disk, not the general operator-norm criterion of BD-02. -/
theorem local_summable (b : HN L 2) (t : ℂ) (ht : ‖t‖ * ‖b‖ < 1) :
    Summable (fun n => t^n • fockTerm b n) := by
  apply Summable.of_norm_bounded (g := fun n => (‖t‖*‖b‖)^n)
    (summable_geometric_of_lt_one (by positivity) ht)
  intro n
  rw [norm_smul, norm_pow, fockTerm_norm, mul_pow]
  exact mul_le_mul_of_nonneg_left (term_norm_bound b n) (by positivity)

/-- The local sum is a genuine physical Fock vector, not a postulated carrier. -/
def localExponential (b : HN L 2) (t : ℂ) : Fock L := ∑' n, t^n • fockTerm b n

lemma localExponential_even (b : HN L 2) (t : ℂ) (ht : ‖t‖*‖b‖ < 1) (n : ℕ) :
    localExponential b t (2*n) = t^n • term b n := by
  let ev := lp.evalCLM (E := fun n => HN L n) (p := 2) ℂ (2*n)
  have hs := ev.hasSum ((local_summable b t ht).hasSum)
  change HasSum _ (localExponential b t (2*n)) at hs
  rw [← hs.tsum_eq]
  rw [tsum_eq_single n]
  · change (t^n • fockTerm b n) (2*n) = t^n • term b n
    simp only [lp.coeFn_smul, Pi.smul_apply, fockTerm_same]
  · intro k hkn
    change (t^k • fockTerm b k) (2*n) = 0
    simp only [lp.coeFn_smul, Pi.smul_apply]
    rw [fockTerm_other b k (2*n) (by omega), smul_zero]

lemma localExponential_odd (b : HN L 2) (t : ℂ) (ht : ‖t‖*‖b‖ < 1) (n : ℕ) :
    localExponential b t (2*n+1) = 0 := by
  let ev := lp.evalCLM (E := fun n => HN L n) (p := 2) ℂ (2*n+1)
  have hs := ev.hasSum ((local_summable b t ht).hasSum)
  change HasSum _ (localExponential b t (2*n+1)) at hs
  rw [← hs.tsum_eq]
  have hz : ∀ k, ev (t^k • fockTerm b k) = 0 := by
    intro k
    change (t^k • fockTerm b k) (2*n+1) = 0
    simp only [lp.coeFn_smul, Pi.smul_apply]
    rw [fockTerm_other b k (2*n+1) (by omega), smul_zero]
  simp only [hz, tsum_zero]

theorem localExponential_ne_zero (b : HN L 2) (t : ℂ) (ht : ‖t‖*‖b‖ < 1) :
    localExponential b t ≠ 0 := by
  intro hz
  have he := localExponential_even b t ht 0
  rw [hz] at he
  have he' : (0 : HN L 0) = term b 0 := by simpa using he
  have hnorm : ‖term b 0‖ = 0 := norm_eq_zero.mpr he'.symm
  rw [term_zero_norm] at hnorm
  norm_num at hnorm

/-- Iterated physical creation without the exponential coefficient. -/
def power (b : HN L 2) : (n : ℕ) → HN L (2*n)
  | 0 => Ext006ZeroVacuum.sectorVacuum L
  | n+1 => sectorCast (by omega : 2+2*n = 2*(n+1))
      (creation b (2*n) (power b n))

lemma step_factorial (n : ℕ) :
    stepScalar n * ((-1/2 : ℂ)^n / (n.factorial : ℂ)) =
      (-1/2 : ℂ)^(n+1) / ((n+1).factorial : ℂ) := by
  have hn : (n : ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [stepScalar, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  push_cast
  field_simp

/-- Exact exponential coefficient, for every pair tensor and every degree. -/
theorem term_eq_power (b : HN L 2) (n : ℕ) :
    term b n = ((-1/2 : ℂ)^n / (n.factorial : ℂ)) • power b n := by
  induction n with
  | zero => simp only [term, power, pow_zero, Nat.factorial_zero, Nat.cast_one,
      div_one, one_smul]
  | succ n ih =>
    rw [term_step, ih]
    simp only [map_smul, smul_smul]
    rw [step_factorial]
    rfl

/-- Orthogonality of the entire even particle-sector inclusions. -/
lemma even_orthogonal : OrthogonalFamily ℂ (fun n => HN L (2*n))
    (fun n => inclusion L (2*n)) := by
  intro n m hnm x y
  change inner ℂ (lp.single 2 (2*n) x : Fock L) (lp.single 2 (2*m) y) = 0
  rw [lp.inner_single_left, lp.single_apply_ne _ _ _ (by omega), inner_zero_right]

/-- Exact finite Pythagoras formula; no convergence premise occurs. -/
theorem truncation_norm_sq (b : HN L 2) (M : ℕ) :
    ‖truncation b M‖^2 = ∑ n ∈ Finset.range M, ‖term b n‖^2 :=
  even_orthogonal.norm_sum (term b) (Finset.range M)

/-- Parseval for the constructed local physical exponential.
Identifying this sum with the Fredholm determinant remains open. -/
theorem localExponential_norm_sq (b : HN L 2) (t : ℂ) (ht : ‖t‖*‖b‖ < 1) :
    ‖localExponential b t‖^2 = ∑' n, ‖t‖^(2*n) * ‖term b n‖^2 := by
  have hs := lp.hasSum_norm (p := 2) (by norm_num) (localExponential b t)
  have hs' : Summable (fun k => ‖localExponential b t k‖^2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs.summable
  have he : Function.Injective (fun k : ℕ => 2*k) := by intro i j h; dsimp at h; omega
  have ho : Function.Injective (fun k : ℕ => 2*k+1) := by intro i j h; dsimp at h; omega
  have hsEq : (∑' k, ‖localExponential b t k‖^2) = ‖localExponential b t‖^2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs.tsum_eq
  rw [← hsEq, ← tsum_even_add_odd (hs'.comp_injective he) (hs'.comp_injective ho)]
  simp only [localExponential_even b t ht, localExponential_odd b t ht,
    norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, tsum_zero,
    add_zero, norm_smul, norm_pow, mul_pow, ← pow_mul, mul_comm 2]

end QuantumNLS.Ext006PhysicalExponentialTerms

#print axioms QuantumNLS.Ext006PhysicalExponentialTerms.sectorCast
#print axioms QuantumNLS.Ext006PhysicalExponentialTerms.stepScalar
#print axioms QuantumNLS.Ext006PhysicalExponentialTerms.norm_stepScalar
#print axioms QuantumNLS.Ext006PhysicalExponentialTerms.term
#print axioms QuantumNLS.Ext006PhysicalExponentialTerms.term_zero
#print axioms QuantumNLS.Ext006PhysicalExponentialTerms.term_zero_norm
#print axioms QuantumNLS.Ext006PhysicalExponentialTerms.term_step
#print axioms QuantumNLS.Ext006PhysicalExponentialTerms.step_ratio_le_one
#print axioms QuantumNLS.Ext006PhysicalExponentialTerms.term_norm_step
#print axioms QuantumNLS.Ext006PhysicalExponentialTerms.term_norm_bound
#print axioms QuantumNLS.Ext006PhysicalExponentialTerms.fockTerm
#print axioms QuantumNLS.Ext006PhysicalExponentialTerms.fockTerm_eq_single
#print axioms QuantumNLS.Ext006PhysicalExponentialTerms.fockTerm_norm
#print axioms QuantumNLS.Ext006PhysicalExponentialTerms.fockTerm_other
#print axioms QuantumNLS.Ext006PhysicalExponentialTerms.fockTerm_same
#print axioms QuantumNLS.Ext006PhysicalExponentialTerms.truncation
#print axioms QuantumNLS.Ext006PhysicalExponentialTerms.truncation_odd
#print axioms QuantumNLS.Ext006PhysicalExponentialTerms.truncation_even
#print axioms QuantumNLS.Ext006PhysicalExponentialTerms.fockTerm_orthogonal
#print axioms QuantumNLS.Ext006PhysicalExponentialTerms.local_summable
#print axioms QuantumNLS.Ext006PhysicalExponentialTerms.localExponential
#print axioms QuantumNLS.Ext006PhysicalExponentialTerms.localExponential_even
#print axioms QuantumNLS.Ext006PhysicalExponentialTerms.localExponential_odd
#print axioms QuantumNLS.Ext006PhysicalExponentialTerms.localExponential_ne_zero
#print axioms QuantumNLS.Ext006PhysicalExponentialTerms.power
#print axioms QuantumNLS.Ext006PhysicalExponentialTerms.step_factorial
#print axioms QuantumNLS.Ext006PhysicalExponentialTerms.term_eq_power
#print axioms QuantumNLS.Ext006PhysicalExponentialTerms.even_orthogonal
#print axioms QuantumNLS.Ext006PhysicalExponentialTerms.truncation_norm_sq
#print axioms QuantumNLS.Ext006PhysicalExponentialTerms.localExponential_norm_sq

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006PhysicalExponentialTerms." then
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
