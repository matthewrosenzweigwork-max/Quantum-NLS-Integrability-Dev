import QuantumNLS.Ext006VacuumMassR31a

/-! A uniform convergence lemma for the actual finite-core norm recurrence.
Only scalar estimates are proved here. In particular no HS-to-finite-compression
trace estimate or implementer existence is assumed as a theorem. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped ENNReal
namespace QuantumNLS.Ext006CoreMajorantR31a
open Occupation Ext006CoreNorm Ext006CoreLimit Ext006VacuumMassR31a

section Scalar
variable {I : Type*} (c t : I → ℕ → ℝ) (A : ℝ)
  (hA : 0 ≤ A) (hc : ∀ i n, 0 ≤ c i n) (ht : ∀ i n, 0 ≤ t i n)
  (h0 : ∀ i, c i 0 ≤ 1)
  (hrec : ∀ i (n : ℕ), ((n : ℝ)+1)*c i (n+1) =
    ∑ j ∈ Finset.range (n+1), t i j*c i (n-j))
  (hsum : ∀ i (n : ℕ), (∑ j ∈ Finset.range (n+1), t i j) ≤ A)

include hA hc ht h0 hrec hsum in
lemma coarse_bound (i : I) (n : ℕ) : c i n ≤ (A+1)^n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa using h0 i
    | succ n =>
      have hb : ((n : ℝ)+1)*c i (n+1) ≤ A*(A+1)^n := by
        rw [hrec]
        calc
          _ ≤ ∑ j ∈ Finset.range (n+1), t i j*(A+1)^n := by
            apply Finset.sum_le_sum
            intro j hj
            have hjn := Finset.mem_range.mp hj
            apply mul_le_mul_of_nonneg_left _ (ht i j)
            exact (ih (n-j) (by omega)).trans (pow_le_pow_right₀ (by linarith) (by omega))
          _ = (∑ j ∈ Finset.range (n+1), t i j)*(A+1)^n := (Finset.sum_mul ..).symm
          _ ≤ A*(A+1)^n := mul_le_mul_of_nonneg_right (hsum i n) (by positivity)
      have hl : c i (n+1) ≤ ((n : ℝ)+1)*c i (n+1) := by
        nlinarith [hc i (n+1), Nat.cast_nonneg (α := ℝ) n]
      apply (hl.trans hb).trans
      rw [pow_succ]
      nlinarith [pow_nonneg (by linarith : 0 ≤ A+1) n]

include hA hc ht h0 hrec hsum in
/-- A common bound for every member of a family. The recurrence's factor n
prevents growth beyond a finite degree, even when A is large. -/
theorem uniform_bound (N : ℕ) (hN : A ≤ N) :
    ∀ i n, c i n ≤ (A+1)^N := by
  intro i n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n ≤ N
    · exact (coarse_bound c t A hA hc ht h0 hrec hsum i n).trans
        (pow_le_pow_right₀ (by linarith) hn)
    · cases n with
      | zero => omega
      | succ n =>
        have hb : ((n : ℝ)+1)*c i (n+1) ≤ A*(A+1)^N := by
          rw [hrec]
          calc
            _ ≤ ∑ j ∈ Finset.range (n+1), t i j*(A+1)^N := by
              apply Finset.sum_le_sum
              intro j hj
              exact mul_le_mul_of_nonneg_left (ih (n-j) (by omega)) (ht i j)
            _ = (∑ j ∈ Finset.range (n+1), t i j)*(A+1)^N := (Finset.sum_mul ..).symm
            _ ≤ A*(A+1)^N := mul_le_mul_of_nonneg_right (hsum i n) (by positivity)
        have hAN : A ≤ (n : ℝ)+1 := hN.trans (by exact_mod_cast (by omega : N ≤ n+1))
        have hp : 0 < (n : ℝ)+1 := by positivity
        have hD : 0 ≤ (A+1)^N := by positivity
        nlinarith

end Scalar

/-- Exponential weighting of the literal finite-core recurrence. -/
theorem weighted_core_recurrence (K : ℤ → ℤ → ℂ) (hK : ∀ a b, K a b = K b a)
    (r : ℝ) (S : Finset ℤ) (n : ℕ) :
    ((n : ℝ)+1)*(r^(n+1)*(cc S K (n+1)).re) =
      ∑ j ∈ Finset.range (n+1),
        (r^(j+1)*(((Tm S K)^(j+1)).trace).re/2) * (r^(n-j)*(cc S K (n-j)).re) := by
  have he := rec_real S K (fun a _ b _ => hK a b) (n+1)
  simp only [Nat.cast_add, Nat.cast_one] at he
  calc
    _ = r^(n+1)/2 * (2*((n : ℝ)+1)*(cc S K (n+1)).re) := by ring
    _ = r^(n+1)/2 *
        ∑ j ∈ Finset.range (n+1), (cc S K (n-j)).re*(((Tm S K)^(j+1)).trace).re := by
          rw [he]; congr 1
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjn := Finset.mem_range.mp hj
      have hp : r^(n+1) = r^(j+1)*r^(n-j) := by
        rw [← pow_add]; congr 1; omega
      rw [hp]
      ring

/-- If the exponentially weighted compression traces have a common finite
bound, the formal vacuum is an actual normalized occupation Fock vacuum.
There is no smallness restriction on the size A of that trace bound. -/
theorem exists_normalized_of_weighted_trace_bound (K : ℤ → ℤ → ℂ)
    (hK : ∀ a b, K a b = K b a) (r A : ℝ) (hr : 1 < r) (hA : 0 ≤ A)
    (htrace : ∀ (S : Finset ℤ) (n : ℕ),
      (∑ j ∈ Finset.range (n+1), r^(j+1)*(((Tm S K)^(j+1)).trace).re/2) ≤ A) :
    ∃ x : Ext006VacuumRecurrence.Fock,
      Ext006VacuumRecurrence.WeakVacuum K x ∧ ‖x‖ = 1 := by
  let c : Finset ℤ → ℕ → ℝ := fun S n => r^n*(cc S K n).re
  let t : Finset ℤ → ℕ → ℝ := fun S j => r^(j+1)*(((Tm S K)^(j+1)).trace).re/2
  have hcc : ∀ S n, 0 ≤ (cc S K n).re := by
    intro S n
    rw [cc_re_eq]
    exact Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)
  have hc : ∀ S n, 0 ≤ c S n := fun S n => mul_nonneg (pow_nonneg (by linarith) n) (hcc S n)
  have ht : ∀ S n, 0 ≤ t S n := by
    intro S n
    apply div_nonneg _ (by norm_num)
    exact mul_nonneg (pow_nonneg (by linarith) _) ((trace_pow_nonneg_submul (Tm_posSemidef S K) (n+1) 0).1)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, A ≤ N := exists_nat_ge A
  have hb := uniform_bound c t A hA hc ht (by intro S; simp [c, cc_zero])
    (weighted_core_recurrence K hK r) htrace N hN
  let D := (A+1)^N
  have hr0 : 0 < r := by linarith
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hg : Summable (fun n : ℕ => D*(r⁻¹)^n) :=
    (summable_geometric_of_lt_one (by positivity) ((inv_lt_one₀ hr0).mpr hr)).mul_left D
  apply (exists_normalized_iff_uniform_core_bound hK).mpr
  refine ⟨ENNReal.ofReal (∑' n, D*(r⁻¹)^n), ENNReal.ofReal_ne_top, fun S => ?_⟩
  rw [ENNReal.ofReal_tsum_of_nonneg (by intro n; positivity) hg]
  apply ENNReal.tsum_le_tsum
  intro n
  apply ENNReal.ofReal_le_ofReal
  have hp : 0 < r^n := pow_pos hr0 n
  have hn := hb S n
  change r^n*(cc S K n).re ≤ D at hn
  rw [inv_pow, ← div_eq_mul_inv]
  exact (le_div_iff₀ hp).mpr (by simpa [mul_comm] using hn)

/- The remaining concrete operator input can be stated as a single geometric
trace estimate, with no restriction on its HS constant H. -/
theorem exists_normalized_of_compression_trace_bound (K : ℤ → ℤ → ℂ)
    (hK : ∀ a b, K a b = K b a) (H q : ℝ) (hH : 0 ≤ H) (hq : 0 ≤ q) (hq1 : q < 1)
    (hb : ∀ (S : Finset ℤ) (j : ℕ), (((Tm S K)^(j+1)).trace).re ≤ H*q^j) :
    ∃ x : Ext006VacuumRecurrence.Fock,
      Ext006VacuumRecurrence.WeakVacuum K x ∧ ‖x‖ = 1 := by
  let r : ℝ := 2/(1+q)
  have hr : 1 < r := (lt_div_iff₀ (by linarith)).mpr (by linarith)
  have hr0 : 0 ≤ r := by linarith
  have hrq : r*q < 1 := by
    dsimp [r]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    linarith
  let g : ℕ → ℝ := fun j => (H*r/2)*(r*q)^j
  have hg0 : ∀ j, 0 ≤ g j := by intro j; dsimp [g]; positivity
  have hgs : Summable g :=
    (summable_geometric_of_lt_one (mul_nonneg hr0 hq) hrq).mul_left (H*r/2)
  apply exists_normalized_of_weighted_trace_bound K hK r (∑' j, g j) hr (tsum_nonneg hg0)
  intro S n
  calc
    _ ≤ ∑ j ∈ Finset.range (n+1), g j := by
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ r^(j+1)*(H*q^j)/2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hb S j)
            (pow_nonneg hr0 _)) (by norm_num)
        _ = g j := by dsimp [g]; rw [pow_succ, mul_pow]; ring
    _ ≤ ∑' j, g j := hgs.sum_le_tsum _ (fun j _ => hg0 j)

end QuantumNLS.Ext006CoreMajorantR31a

#print axioms QuantumNLS.Ext006CoreMajorantR31a.coarse_bound
#print axioms QuantumNLS.Ext006CoreMajorantR31a.uniform_bound
#print axioms QuantumNLS.Ext006CoreMajorantR31a.weighted_core_recurrence
#print axioms QuantumNLS.Ext006CoreMajorantR31a.exists_normalized_of_weighted_trace_bound
#print axioms QuantumNLS.Ext006CoreMajorantR31a.exists_normalized_of_compression_trace_bound

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006CoreMajorantR31a." then
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
  Lean.logInfo m!"Round31a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
