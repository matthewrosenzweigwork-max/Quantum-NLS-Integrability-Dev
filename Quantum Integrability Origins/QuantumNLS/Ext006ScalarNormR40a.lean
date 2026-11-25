import QuantumNLS.Ext006ActualNormTraceR40a
import Mathlib.Analysis.Calculus.SmoothSeries

/-! Evaluate a summable nonnegative norm recurrence by a proved scalar ODE.
No norm, determinant or generating-function identity is assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Filter Topology Set
namespace QuantumNLS.Ext006ScalarNormR40a

def gen (c : ℕ → ℝ) (x : ℝ) : ℝ := ∑' n, c n*x^n

def pot (a : ℕ → ℝ) (x : ℝ) : ℝ := ∑' n, (a n/((n:ℝ)+1))*x^(n+1)

lemma power_bound (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (n : ℕ) (x : ℝ) (hx : |x| ≤ 1) :
    ‖c n*x^n‖ ≤ c n := by
  rw [norm_mul, Real.norm_of_nonneg (hc n), norm_pow, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg x) hx) (hc n)).trans_eq (mul_one _)

lemma gen_summable (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hs : Summable c)
    (x : ℝ) (hx : |x| ≤ 1) : Summable (fun n => c n*x^n) :=
  hs.of_norm_bounded (fun n => power_bound c hc n x hx)

lemma gen_continuousOn (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hs : Summable c) :
    ContinuousOn (gen c) (Icc (0:ℝ) 1) := by
  apply continuousOn_tsum (fun n => (by fun_prop)) hs
  intro n x hx
  exact power_bound c hc n x (abs_le.mpr ⟨by linarith [hx.1],hx.2⟩)

lemma deriv_bound (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (n : ℕ) (x : ℝ) (hx : |x| ≤ 1) :
    ‖c n*((n:ℝ)*x^(n-1))‖ ≤ (n:ℝ)*c n := by
  rw [norm_mul, Real.norm_of_nonneg (hc n), norm_mul, Real.norm_of_nonneg (Nat.cast_nonneg n),
    norm_pow, Real.norm_eq_abs]
  calc
    _ ≤ c n*((n:ℝ)*1) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg x) hx) (Nat.cast_nonneg n)) (hc n)
    _ = _ := by ring

lemma gen_deriv (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hs : Summable c)
    (hns : Summable (fun n : ℕ => (n:ℝ)*c n)) (x : ℝ) (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (gen c) (∑' n, c n*((n:ℝ)*x^(n-1))) x := by
  apply hasDerivAt_tsum_of_isPreconnected hns isOpen_Ioo (convex_Ioo (-1:ℝ) 1).isPreconnected
    (fun n y _ => (hasDerivAt_pow n y).const_mul (c n))
    (fun n y hy => deriv_bound c hc n y (abs_le.mpr ⟨hy.1.le,hy.2.le⟩))
    (show (0:ℝ) ∈ Ioo (-1:ℝ) 1 by norm_num)
    (gen_summable c hc hs 0 (by norm_num)) hx

lemma pot_coeff_bound (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (n : ℕ) :
    0 ≤ a n/((n:ℝ)+1) ∧ a n/((n:ℝ)+1) ≤ a n := by
  constructor
  · exact div_nonneg (ha n) (by positivity)
  · exact div_le_self (ha n) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)

lemma pot_bound (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (n : ℕ) (x : ℝ) (hx : |x| ≤ 1) :
    ‖(a n/((n:ℝ)+1))*x^(n+1)‖ ≤ a n := by
  rw [norm_mul, Real.norm_of_nonneg (pot_coeff_bound a ha n).1, norm_pow, Real.norm_eq_abs]
  calc
    _ ≤ (a n/((n:ℝ)+1))*1 := mul_le_mul_of_nonneg_left
      (pow_le_one₀ (abs_nonneg x) hx) (pot_coeff_bound a ha n).1
    _ ≤ _ := by simpa using (pot_coeff_bound a ha n).2

lemma pot_continuousOn (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hs : Summable a) :
    ContinuousOn (pot a) (Icc (0:ℝ) 1) := by
  apply continuousOn_tsum (fun n => (by fun_prop)) hs
  intro n x hx
  exact pot_bound a ha n x (abs_le.mpr ⟨by linarith [hx.1],hx.2⟩)

lemma pot_deriv (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (x : ℝ) (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (pot a) (gen a x) x := by
  apply hasDerivAt_tsum_of_isPreconnected hs isOpen_Ioo (convex_Ioo (-1:ℝ) 1).isPreconnected
    (g' := fun n y => a n*y^n)
    (fun n y _ => ?_)
    (fun n y hy => power_bound a ha n y (abs_le.mpr ⟨hy.1.le,hy.2.le⟩))
    (show (0:ℝ) ∈ Ioo (-1:ℝ) 1 by norm_num) (by simp) hx
  convert (hasDerivAt_pow (n+1) y).const_mul (a n/((n:ℝ)+1)) using 1
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  have hn : (n:ℝ)+1 ≠ 0 := by positivity
  field_simp

/-- The physical recurrence's derivative is the Cauchy product. -/
lemma gen_deriv_product (c a : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (ha : ∀ n, 0 ≤ a n)
    (hcs : Summable c) (has : Summable a) (hns : Summable (fun n : ℕ => (n:ℝ)*c n))
    (hrec : ∀ n : ℕ, ((n:ℝ)+1)*c (n+1) = ∑ j ∈ Finset.range (n+1), a j*c (n-j))
    (x : ℝ) (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (gen c) (gen a x*gen c x) x := by
  have hab : |x| ≤ 1 := abs_le.mpr ⟨hx.1.le,hx.2.le⟩
  have hd := gen_deriv c hc hcs hns x hx
  convert hd using 1
  symm
  calc
    _ = ∑' n, c (n+1)*((n+1:ℕ):ℝ)*x^n := by
      have hs : Summable (fun n => c n*((n:ℝ)*x^(n-1))) :=
        hns.of_norm_bounded (fun n => deriv_bound c hc n x hab)
      rw [hs.tsum_eq_zero_add]
      simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add, Nat.add_sub_cancel,
        Nat.cast_add, Nat.cast_one]
      apply tsum_congr
      intro n
      ring
    _ = gen a x*gen c x := by
      rw [gen, gen, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
        ((gen_summable a ha has x hab).norm) ((gen_summable c hc hcs x hab).norm)]
      apply tsum_congr
      intro n
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      calc
        _ = ((n:ℝ)+1)*c (n+1)*x^n := by push_cast; ring
        _ = (∑ j ∈ Finset.range (n+1), a j*c (n-j))*x^n := by rw [hrec]
        _ = _ := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j hj
          have hjn := Finset.mem_range.mp hj
          have hp : x^n = x^j*x^(n-j) := by
            rw [← pow_add]
            congr 1
            omega
          rw [hp]
          ring

/-- Exact total norm from a summable nonnegative trace recurrence. -/
theorem total_eq_exp (c a : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (ha : ∀ n, 0 ≤ a n)
    (hcs : Summable c) (has : Summable a) (hns : Summable (fun n : ℕ => (n:ℝ)*c n))
    (hc0 : c 0 = 1)
    (hrec : ∀ n : ℕ, ((n:ℝ)+1)*c (n+1) = ∑ j ∈ Finset.range (n+1), a j*c (n-j)) :
    (∑' n, c n) = Real.exp (∑' n, a n/((n:ℝ)+1)) := by
  let f : ℝ → ℝ := fun x => gen c x * Real.exp (-pot a x)
  have hcont : ContinuousOn f (Icc (0:ℝ) 1) :=
    (gen_continuousOn c hc hcs).mul
      (Real.continuous_exp.comp_continuousOn (pot_continuousOn a ha has).neg)
  have hder : ∀ x ∈ Ico (0:ℝ) 1, HasDerivWithinAt f 0 (Ici x) x := by
    intro x hx
    have hx' : x ∈ Ioo (-1:ℝ) 1 := ⟨by linarith [hx.1],hx.2⟩
    have hd := (gen_deriv_product c a hc ha hcs has hns hrec x hx').mul
      ((pot_deriv a ha has x hx').neg.exp)
    have he : gen a x*gen c x*Real.exp (-pot a x) +
        gen c x*(Real.exp (-pot a x)*(-gen a x)) = 0 := by ring
    change HasDerivAt f (gen a x*gen c x*Real.exp (-pot a x) +
      gen c x*(Real.exp (-pot a x)*(-gen a x))) x at hd
    rw [he] at hd
    exact hd.hasDerivWithinAt
  have he := constant_of_has_deriv_right_zero hcont hder 1 (by norm_num)
  have hz : gen c 0 = 1 := by
    rw [gen, tsum_eq_single 0]
    · simpa using hc0
    · intro n hn; simp [zero_pow hn]
  have hp0 : pot a 0 = 0 := by simp [pot]
  change gen c 1*Real.exp (-pot a 1) = gen c 0*Real.exp (-pot a 0) at he
  rw [hz,hp0,neg_zero,Real.exp_zero,mul_one] at he
  have hc1 : gen c 1 = ∑' n, c n := by simp [gen]
  have hp1 : pot a 1 = ∑' n, a n/((n:ℝ)+1) := by simp [pot]
  rw [hc1,hp1] at he
  apply mul_right_cancel₀ (Real.exp_ne_zero (-(∑' n, a n/((n:ℝ)+1))))
  rw [he, ← Real.exp_add]
  simp

end QuantumNLS.Ext006ScalarNormR40a
#print axioms QuantumNLS.Ext006ScalarNormR40a.total_eq_exp

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006ScalarNormR40a." then
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
  Lean.logInfo m!"Round40a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
