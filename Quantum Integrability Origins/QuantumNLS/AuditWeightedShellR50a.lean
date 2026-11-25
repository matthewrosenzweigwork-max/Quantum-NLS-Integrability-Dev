import QuantumNLS.AuditWeightedTailR49a
import QuantumNLS.AuditWeightedProbabilityR49a

/-! Integer-shell domination on a bounded-root event. All expectations here
are of explicitly bounded finite shell sums, never untruncated moments. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators
namespace QuantumNLS.AuditWeightedShellR50a
open QuantumNLS.RootEvent QuantumNLS.AuditWeightedDetR49a

/-- The integer shell immediately below a positive real number. -/
theorem exists_shell {x : ℝ} (hx : 0 < x) :
    ∃ i : ℕ, (i : ℝ) < x ∧ x ≤ (i : ℝ)+1 := by
  refine ⟨⌈x⌉₊-1, ?_⟩
  have hc : 0 < ⌈x⌉₊ := Nat.ceil_pos.mpr hx
  have he : ((⌈x⌉₊-1 : ℕ) : ℝ) = (⌈x⌉₊ : ℝ)-1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  constructor
  · rw [he]
    exact sub_lt_iff_lt_add.mpr (Nat.ceil_lt_add_one hx.le)
  · rw [he]
    linarith [Nat.le_ceil x]

def shellWeight (b : ℕ) (s : ℝ) : ℝ := (1+(s+1)^2)^b

theorem shellWeight_nonneg (b : ℕ) (s : ℝ) : 0 ≤ shellWeight b s := by
  unfold shellWeight; positivity

theorem shellWeight_bound (b : ℕ) {s : ℝ} (hs : 1 ≤ s) :
    shellWeight b s ≤ 5^b*s^(2*b) := by
  have h : 1+(s+1)^2 ≤ 5*s^2 := by nlinarith
  have := pow_le_pow_left₀ (by positivity : 0 ≤ 1+(s+1)^2) h b
  simpa only [shellWeight, mul_pow, ← pow_mul] using this

/-- Finite majorant; only shells below K are inspected. -/
def shellMajorant {Ω : Type*} {N : ℕ} (q : Ω → Fin N → ℝ)
    (b K : ℕ) (R : ℝ) (ω : Ω) : ℝ :=
  (1+R^2)^b + ∑ i ∈ Finset.range (K+1),
    shellWeight b (R+i) * tailFraction q (R+i) ω

theorem tailFraction_nonneg {Ω : Type*} {N : ℕ} (q : Ω → Fin N → ℝ)
    (R : ℝ) (ω : Ω) : 0 ≤ tailFraction q R ω := by
  unfold tailFraction
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _)

theorem shellMajorant_nonneg {Ω : Type*} {N : ℕ} (q : Ω → Fin N → ℝ)
    (b K : ℕ) (R : ℝ) (ω : Ω) : 0 ≤ shellMajorant q b K R ω := by
  unfold shellMajorant
  exact add_nonneg (by positivity) (Finset.sum_nonneg fun _ _ =>
    mul_nonneg (shellWeight_nonneg _ _) (tailFraction_nonneg _ _ _))

/-- A pointwise shell estimate, including roots on integer boundaries. -/
theorem root_shell_bound (b K : ℕ) {R x : ℝ} (hR : 1 ≤ R)
    (hx : |x| ≤ R+K) :
    (1+x^2)^b ≤ (1+R^2)^b + ∑ i ∈ Finset.range (K+1),
      shellWeight b (R+i) * (if R+(i : ℝ)< |x| then 1 else 0) := by
  classical
  have hnn : ∀ i ∈ Finset.range (K+1),
      0 ≤ shellWeight b (R+i) * (if R+(i : ℝ)< |x| then 1 else 0) := by
    intro i _; exact mul_nonneg (shellWeight_nonneg _ _) (by split <;> norm_num)
  by_cases hsmall : |x| ≤ R
  · have hsq : x^2 ≤ R^2 := by nlinarith [sq_abs x, abs_nonneg x]
    exact (pow_le_pow_left₀ (by positivity) (by linarith : 1+x^2≤1+R^2) b).trans
      (le_add_of_nonneg_right (Finset.sum_nonneg hnn))
  · obtain ⟨i,hi,hix⟩ := exists_shell (by linarith : 0 < |x|-R)
    have hiK : i ∈ Finset.range (K+1) := by
      have : (i : ℝ)<K := by linarith
      have : i<K := by exact_mod_cast this
      simp only [Finset.mem_range]; omega
    have hterm : (1+x^2)^b ≤ shellWeight b (R+i) *
        (if R+(i : ℝ)< |x| then 1 else 0) := by
      rw [ite_eq_left (by linarith), mul_one]
      apply pow_le_pow_left₀ (by positivity)
      have hab : |x| ≤ R+(i : ℝ)+1 := by linarith
      have : x^2 ≤ (R+(i : ℝ)+1)^2 := by nlinarith [sq_abs x,abs_nonneg x]
      linarith
    exact (hterm.trans (Finset.single_le_sum hnn hiK)).trans (le_add_of_nonneg_left (by positivity))

theorem average_shell_bound {Ω : Type*} {N : ℕ} (hN : 0 < N)
    (q : Ω → Fin N → ℝ) (b K : ℕ) {R : ℝ} (hR : 1 ≤ R) (ω : Ω)
    (hmax : ∀ j, |q ω j| ≤ R+K) :
    (N : ℝ)⁻¹ * ∑ j, (1+(q ω j)^2)^b ≤ shellMajorant q b K R ω := by
  classical
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hh := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (s := Finset.univ) fun j _ => root_shell_bound b K hR (hmax j))
    (inv_nonneg.mpr (Nat.cast_nonneg N))
  convert hh using 1
  unfold shellMajorant tailFraction
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [mul_add, inv_mul_cancel_left₀ hNr, Finset.sum_comm]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [← Finset.mul_sum]
  ring

theorem integrable_tailFraction {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (q : Ω → Fin N → ℝ)
    (hq : Measurable q) (R : ℝ) : Integrable (tailFraction q R) P := by
  exact (integrable_finsetSum _ fun j _ => (integrable_const (1 : ℝ)).indicator
    (measurableSet_tail_j q hq R j)).const_mul _

theorem integrable_shellMajorant {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (q : Ω → Fin N → ℝ)
    (hq : Measurable q) (b K : ℕ) (R : ℝ) : Integrable (shellMajorant q b K R) P :=
  (integrable_const _).add (integrable_finsetSum _ fun _i _ =>
    (integrable_tailFraction P q hq _).const_mul _)

end QuantumNLS.AuditWeightedShellR50a

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.AuditWeightedShellR50a." ||
        n.toString.startsWith "_private.QuantumNLS.AuditWeightedShellR50a." then
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
  Lean.logInfo m!"Round50 aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
