import QuantumNLS.SobolevSpaces
import QuantumNLS.TerraMultiRound71Sequence

/-! Weighted Hilbert convergence from coordinates and squared moduli. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
open QuantumNLS.Sobolev
namespace QuantumNLS.Reg011SequencesR48a

theorem sum_zero_of_varying_bound {ι : Type*} (f e : ℕ → ι → ℝ) (a : ι → ℝ)
    (hf : ∀ j n, 0 ≤ f j n) (he : ∀ j n, 0 ≤ e j n) (ha : ∀ n, 0 ≤ a n)
    (hfs : ∀ j, Summable (f j)) (hes : ∀ j, Summable (e j)) (has : Summable a)
    (hpt : ∀ n, Tendsto (fun j => f j n) atTop (𝓝 0))
    (het : Tendsto (fun j => ∑' n, e j n) atTop (𝓝 0))
    (hbound : ∀ j n, f j n ≤ e j n + a n) :
    Tendsto (fun j => ∑' n, f j n) atTop (𝓝 0) := by
  have hm : ∀ j, Summable (fun n => min (f j n) (a n)) := by
    intro j
    exact has.of_nonneg_of_le (fun n => le_min (hf j n) (ha n)) (fun n => min_le_right _ _)
  have ht : Tendsto (fun j => ∑' n, min (f j n) (a n)) atTop (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence has
      (fun n => (hpt n).min tendsto_const_nhds)
      (Filter.Eventually.of_forall fun j n => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hf j n) (ha n))]
        exact min_le_right _ _)
    simpa only [min_eq_left (ha _), tsum_zero] using h
  have hb : ∀ j, (∑' n, f j n) ≤ (∑' n, e j n) + ∑' n, min (f j n) (a n) := by
    intro j
    rw [← (hes j).tsum_add (hm j)]
    apply (hfs j).tsum_le_tsum _ ((hes j).add (hm j))
    intro n
    rcases le_total (f j n) (a n) with h | h
    · rw [min_eq_left h]; linarith [he j n]
    · rw [min_eq_right h]; exact hbound j n
  exact squeeze_zero (fun j => tsum_nonneg (hf j)) hb (by simpa using het.add ht)

variable (W : PosWeight)

theorem coordinate_continuous (n : ℤ) : Continuous (fun x : PosWeight.WSeq W => x.val n) := by
  have h : Continuous (fun x : PosWeight.WSeq W => (PosWeight.toL2 W x) n) :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).continuous.comp (PosWeight.toL2ᵢ W).continuous
  have heq : (fun x : PosWeight.WSeq W => x.val n) =
      fun x => (PosWeight.toL2 W x) n / (Real.sqrt (W.w n) : ℂ) := by
    funext x
    rw [PosWeight.toL2_apply, mul_div_cancel_left₀ _ (PosWeight.sqrt_ne_zero' W n)]
  rw [heq]
  exact h.div_const _

theorem squared_moduli_tendsto (x : ℕ → PosWeight.WSeq W) (y : PosWeight.WSeq W)
    (hx : Tendsto x atTop (𝓝 y)) :
    Tendsto (fun j => ∑' n, W.w n * |‖(x j).val n‖^2 - ‖y.val n‖^2|) atTop (𝓝 0) := by
  have h := QuantumNLS.TerraMultiRound71Sequence.nonnegative_tsum_abs_sub_tendsto
    (fun j n => W.w n * ‖(x j).val n‖^2) (fun n => W.w n * ‖y.val n‖^2)
    (fun j n => mul_nonneg (W.pos n).le (sq_nonneg _))
    (fun n => mul_nonneg (W.pos n).le (sq_nonneg _))
    (fun j => (x j).summable) y.summable
    (fun n => (((coordinate_continuous W n).tendsto y |>.comp hx).norm.pow 2).const_mul _)
    (by simpa only [← PosWeight.norm_sq_eq_tsum] using hx.norm.pow 2)
  convert h using 1
  funext j
  apply tsum_congr
  intro n
  rw [← mul_sub, abs_mul, abs_of_pos (W.pos n)]

theorem tendsto_of_coordinates_moduli (x : ℕ → PosWeight.WSeq W) (y : PosWeight.WSeq W)
    (hpt : ∀ n, Tendsto (fun j => (x j).val n) atTop (𝓝 (y.val n)))
    (hm : Tendsto (fun j => ∑' n, W.w n * |‖(x j).val n‖^2 - ‖y.val n‖^2|) atTop (𝓝 0)) :
    Tendsto x atTop (𝓝 y) := by
  let f := fun j n => W.w n * ‖(x j).val n - y.val n‖^2
  let e := fun j n => 2 * (W.w n * |‖(x j).val n‖^2 - ‖y.val n‖^2|)
  let a := fun n => 4 * (W.w n * ‖y.val n‖^2)
  have hes : ∀ j, Summable (e j) := by
    intro j
    have h := ((x j).summable.sub y.summable).abs.mul_left 2
    convert h using 1
    funext n
    simp only [e, ← mul_sub, abs_mul, abs_of_pos (W.pos n)]
  have hf : Tendsto (fun j => ∑' n, f j n) atTop (𝓝 0) := by
    apply sum_zero_of_varying_bound f e a
      (fun j n => mul_nonneg (W.pos n).le (sq_nonneg _)) (fun j n => mul_nonneg (by norm_num) (mul_nonneg (W.pos n).le (abs_nonneg _)))
      (fun n => mul_nonneg (by norm_num) (mul_nonneg (W.pos n).le (sq_nonneg _)))
      (fun j => (x j - y).summable) hes (y.summable.mul_left 4)
    · intro n
      simpa only [f, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
        using ((hpt n).sub (tendsto_const_nhds (x := y.val n))).norm.pow 2 |>.const_mul (W.w n)
    · simpa only [e, tsum_mul_left, mul_zero] using hm.const_mul 2
    · intro j n
      have hn := norm_sub_le ((x j).val n) (y.val n)
      have hs : ‖(x j).val n - y.val n‖^2 ≤ 2*‖(x j).val n‖^2 + 2*‖y.val n‖^2 := by
        nlinarith [sq_nonneg (‖(x j).val n‖-‖y.val n‖), norm_nonneg ((x j).val n-y.val n)]
      have hb : ‖(x j).val n‖^2 ≤ |‖(x j).val n‖^2 - ‖y.val n‖^2| + ‖y.val n‖^2 := by
        linarith [le_abs_self (‖(x j).val n‖^2 - ‖y.val n‖^2)]
      dsimp [f,e,a]
      nlinarith [mul_le_mul_of_nonneg_left hs (W.pos n).le,
        mul_le_mul_of_nonneg_left hb (W.pos n).le]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have heq : (fun j => ∑' n, f j n) = fun j => ‖x j - y‖^2 := by
    funext j
    exact (PosWeight.norm_sq_eq_tsum W (x j-y)).symm
  rw [heq] at hf
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hf.sqrt

theorem tendsto_of_coordinates_norm (x : ℕ → PosWeight.WSeq W) (y : PosWeight.WSeq W)
    (hpt : ∀ n, Tendsto (fun j => (x j).val n) atTop (𝓝 (y.val n)))
    (hn : Tendsto (fun j => ‖x j‖^2) atTop (𝓝 (‖y‖^2))) :
    Tendsto x atTop (𝓝 y) := by
  apply tendsto_of_coordinates_moduli W x y hpt
  have h := QuantumNLS.TerraMultiRound71Sequence.nonnegative_tsum_abs_sub_tendsto
    (fun j n => W.w n * ‖(x j).val n‖^2) (fun n => W.w n * ‖y.val n‖^2)
    (fun j n => mul_nonneg (W.pos n).le (sq_nonneg _))
    (fun n => mul_nonneg (W.pos n).le (sq_nonneg _))
    (fun j => (x j).summable) y.summable
    (fun n => ((hpt n).norm.pow 2).const_mul _)
    (by simpa only [← PosWeight.norm_sq_eq_tsum] using hn)
  convert h using 1
  funext j
  apply tsum_congr
  intro n
  rw [← mul_sub, abs_mul, abs_of_pos (W.pos n)]

#print axioms sum_zero_of_varying_bound
#print axioms coordinate_continuous
#print axioms squared_moduli_tendsto
#print axioms tendsto_of_coordinates_moduli
#print axioms tendsto_of_coordinates_norm
end QuantumNLS.Reg011SequencesR48a

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Reg011SequencesR48a." ||
        n.toString.startsWith "_private.QuantumNLS.Reg011SequencesR48a." then
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
  Lean.logInfo m!"Round48 aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
