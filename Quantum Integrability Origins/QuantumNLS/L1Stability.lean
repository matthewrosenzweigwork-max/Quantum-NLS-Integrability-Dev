import Mathlib
import QuantumNLS.L1SpatialTransfer

/-!
# Gronwall inequality with L¹ weight and L¹-stability of the Volterra transfer

New module (R-7E0532E7 `thm:root-spectral-density`, L¹/L² remainder and trace-symbol identification).
Consumes `L1SpatialTransfer` / `LinearFundamental` read-only.

* `gronwall_integral`: if `f` is continuous on `[0,L]` and `f x ≤ a + ∫₀ˣ m f` with a nonnegative interval-integrable weight `m`,
  then `f x ≤ a exp(∫₀ˣ m)`.  Proof: iterate the hypothesis `n` times with `L1SpatialTransfer.integral_control_pow`, then `n → ∞`.
* `norm_transfer_le`: `‖transfer A x‖ ≤ ‖1‖ exp(∫₀ᴸ ‖A‖)`.
* `norm_transfer_sub_le`: for interval-integrable `A, A'` on `[0,L]`,
  `‖transfer A x - transfer A' x‖ ≤ (∫₀ᴸ‖A - A'‖) · ‖1‖ exp(∫₀ᴸ‖A‖) · exp(∫₀ᴸ‖A'‖)` for `x ∈ [0,L]`.
No assumption beyond interval integrability; no continuity of the coefficients.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped Interval

namespace QuantumNLS.L1Stability

open QuantumNLS.L1SpatialTransfer

/-- **Gronwall with `L¹` weight** (integral form). -/
theorem gronwall_integral {m f : ℝ → ℝ} {L a : ℝ} (hL : 0 ≤ L)
    (hm : IntervalIntegrable m volume 0 L) (hm0 : ∀ s, 0 ≤ m s)
    (hf : ContinuousOn f (Icc 0 L))
    (h : ∀ x ∈ Icc 0 L, f x ≤ a + ∫ s in (0 : ℝ)..x, m s * f s) :
    ∀ x ∈ Icc 0 L, f x ≤ a * Real.exp (∫ s in (0 : ℝ)..x, m s) := by
  obtain ⟨F, hF⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hsubx : ∀ x ∈ Icc (0 : ℝ) L, uIcc (0 : ℝ) x ⊆ uIcc (0 : ℝ) L := by
    intro x hx
    rw [uIcc_of_le hx.1, uIcc_of_le hL]; exact Icc_subset_Icc_right hx.2
  have hFf : ∀ x ∈ Icc (0 : ℝ) L, f x ≤ ‖F‖ := fun x hx =>
    (le_abs_self _).trans ((by simpa using hF x hx : |f x| ≤ F).trans (le_abs_self _))
  set Fb : ℝ := |F| with hFb
  have hFf' : ∀ x ∈ Icc (0 : ℝ) L, f x ≤ Fb := fun x hx =>
    (le_abs_self _).trans ((by simpa using hF x hx : |f x| ≤ F).trans (le_abs_self F))
  have hFb0 : 0 ≤ Fb := abs_nonneg _
  -- cumulative weight
  set c : ℝ → ℝ := fun x => ∫ s in (0 : ℝ)..x, m s with hc
  have hcx : ∀ x ∈ Icc (0 : ℝ) L, 0 ≤ c x := fun x hx =>
    intervalIntegral.integral_nonneg hx.1 (fun s _ => hm0 s)
  have hcc : ContinuousOn c (Icc 0 L) := by
    have := intervalIntegral.continuousOn_primitive_interval
      ((intervalIntegrable_iff' (by finiteness)).mp hm)
    simpa [uIcc_of_le hL, hc] using this
  have key : ∀ n : ℕ, ∀ x ∈ Icc (0 : ℝ) L,
      f x ≤ a * (∑ k ∈ Finset.range n, c x ^ k / (k.factorial : ℝ)) + Fb * c x ^ n / (n.factorial : ℝ) := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hFf' x hx
    | succ n ih =>
      intro x hx
      have hmx : IntervalIntegrable m volume 0 x := hm.mono_set (hsubx x hx)
      have hcont : ∀ k : ℕ, ContinuousOn (fun s => c s ^ k) (uIcc 0 x) := fun k =>
        ((intervalIntegral.continuousOn_primitive_interval
          ((intervalIntegrable_iff' (by finiteness)).mp hmx)).pow k)
      have hint : ∀ k : ℕ, IntervalIntegrable (fun s => m s * c s ^ k) volume 0 x := fun k =>
        hmx.mul_continuousOn (hcont k)
      have hbound : ∀ s ∈ Icc (0 : ℝ) x, m s * f s ≤
          m s * (a * (∑ k ∈ Finset.range n, c s ^ k / (k.factorial : ℝ)) + Fb * c s ^ n / (n.factorial : ℝ)) := by
        intro s hs
        exact mul_le_mul_of_nonneg_left (ih s ⟨hs.1, hs.2.trans hx.2⟩) (hm0 s)
      have hsumI : IntervalIntegrable (fun s => ∑ k ∈ Finset.range n, (m s * c s ^ k) / (k.factorial : ℝ))
          volume 0 x := by
        have := IntervalIntegrable.sum (Finset.range n)
          (f := fun (k : ℕ) (s : ℝ) => (m s * c s ^ k) / (k.factorial : ℝ)) (μ := volume) (a := 0) (b := x)
          (fun k _ => (hint k).div_const _)
        convert this using 1
        ext s; simp [Finset.sum_apply]
      have hfint : IntervalIntegrable (fun s => m s * f s) volume 0 x :=
        (hm.mul_continuousOn (by simpa [uIcc_of_le hL] using hf)).mono_set (hsubx x hx)
      have hrint : IntervalIntegrable (fun s => m s *
          (a * (∑ k ∈ Finset.range n, c s ^ k / (k.factorial : ℝ)) + Fb * c s ^ n / (n.factorial : ℝ))) volume 0 x := by
        have : (fun s => m s * (a * (∑ k ∈ Finset.range n, c s ^ k / (k.factorial : ℝ)) +
              Fb * c s ^ n / (n.factorial : ℝ))) =
            fun s => a * (∑ k ∈ Finset.range n, (m s * c s ^ k) / (k.factorial : ℝ)) +
              Fb * (m s * c s ^ n) / (n.factorial : ℝ) := by
          funext s
          rw [Finset.mul_sum, Finset.mul_sum, mul_add, Finset.mul_sum]
          congr 1
          · apply Finset.sum_congr rfl; intro k _; ring
          · ring
        rw [this]
        exact (hsumI.const_mul a).add (((hint n).const_mul Fb).div_const _)
      have hmono := intervalIntegral.integral_mono_on hx.1 hfint hrint hbound
      have hcalc : ∫ s in (0 : ℝ)..x, m s *
          (a * (∑ k ∈ Finset.range n, c s ^ k / (k.factorial : ℝ)) + Fb * c s ^ n / (n.factorial : ℝ)) =
          a * (∑ k ∈ Finset.range n, c x ^ (k + 1) / ((k + 1).factorial : ℝ)) +
            Fb * c x ^ (n + 1) / ((n + 1).factorial : ℝ) := by
        have hrew : ∀ s, m s * (a * (∑ k ∈ Finset.range n, c s ^ k / (k.factorial : ℝ)) +
            Fb * c s ^ n / (n.factorial : ℝ)) =
            a * (∑ k ∈ Finset.range n, (m s * c s ^ k) / (k.factorial : ℝ)) +
              Fb * (m s * c s ^ n) / (n.factorial : ℝ) := by
          intro s
          rw [Finset.mul_sum, Finset.mul_sum, mul_add, Finset.mul_sum]
          congr 1
          · apply Finset.sum_congr rfl; intro k _; ring
          · ring
        simp_rw [hrew]
        rw [intervalIntegral.integral_add]
        · congr 1
          · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
            · congr 1
              apply Finset.sum_congr rfl
              intro k _
              rw [intervalIntegral.integral_div]
              have := integral_control_pow hmx k
              simp only [hc] at this ⊢
              rw [this, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
              field_simp
            · intro k _
              exact (hint k).div_const _
          · rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul]
            have := integral_control_pow hmx n
            simp only [hc] at this ⊢
            rw [this, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
            field_simp
        · exact hsumI.const_mul a
        · exact ((hint n).const_mul Fb).div_const _
      have hh := h x hx
      have hxc : (∫ s in (0 : ℝ)..x, m s * f s) ≤ a * (∑ k ∈ Finset.range n, c x ^ (k + 1) / ((k + 1).factorial : ℝ)) +
            Fb * c x ^ (n + 1) / ((n + 1).factorial : ℝ) := hcalc ▸ hmono
      calc f x ≤ a + ∫ s in (0 : ℝ)..x, m s * f s := hh
        _ ≤ a + (a * (∑ k ∈ Finset.range n, c x ^ (k + 1) / ((k + 1).factorial : ℝ)) +
            Fb * c x ^ (n + 1) / ((n + 1).factorial : ℝ)) := by linarith
        _ = a * (∑ k ∈ Finset.range (n + 1), c x ^ k / (k.factorial : ℝ)) +
            Fb * c x ^ (n + 1) / ((n + 1).factorial : ℝ) := by
          rw [Finset.sum_range_succ', mul_add]
          simp
          ring
  intro x hx
  have hsum : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, c x ^ k / (k.factorial : ℝ)) atTop
      (𝓝 (Real.exp (c x))) := by
    have := (Real.summable_pow_div_factorial (c x)).hasSum
    have he : ∑' k : ℕ, c x ^ k / (k.factorial : ℝ) = Real.exp (c x) := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    rw [← he]
    exact this.tendsto_sum_nat
  have htail : Tendsto (fun n : ℕ => Fb * c x ^ n / (n.factorial : ℝ)) atTop (𝓝 0) := by
    have := (Real.summable_pow_div_factorial (c x)).tendsto_atTop_zero.const_mul Fb
    simpa [mul_div_assoc] using this
  have hlim := (hsum.const_mul a).add htail
  simp only [add_zero] at hlim
  exact ge_of_tendsto' hlim (fun n => key n x hx)

section General
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- Bound on the transfer in terms of the `L¹` norm of the coefficient. -/
theorem norm_transfer_le {A : ℝ → 𝔸} {L : ℝ} (hL : 0 ≤ L) (hA : IntervalIntegrable A volume 0 L)
    {x : ℝ} (hx : x ∈ Icc 0 L) :
    ‖transfer A x‖ ≤ ‖(1 : 𝔸)‖ * Real.exp (∫ s in (0 : ℝ)..L, ‖A s‖) := by
  obtain ⟨hs, hb⟩ := uniform_dyson_bound hL hA
  have h1 : ‖transfer A x‖ ≤ ∑' n : ℕ, ‖(1 : 𝔸)‖ * (∫ t in (0 : ℝ)..L, ‖A t‖) ^ n / (n.factorial : ℝ) :=
    tsum_of_norm_bounded hs.hasSum (fun n => hb n x hx)
  refine h1.trans (le_of_eq ?_)
  simp_rw [mul_div_assoc]
  rw [tsum_mul_left, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

/-- **`L¹`-stability of the Volterra transfer.** -/
theorem norm_transfer_sub_le {A A' : ℝ → 𝔸} {L : ℝ} (hL : 0 ≤ L)
    (hA : IntervalIntegrable A volume 0 L) (hA' : IntervalIntegrable A' volume 0 L)
    {x : ℝ} (hx : x ∈ Icc 0 L) :
    ‖transfer A x - transfer A' x‖ ≤
      (∫ s in (0 : ℝ)..L, ‖A s - A' s‖) * (‖(1 : 𝔸)‖ * Real.exp (∫ s in (0 : ℝ)..L, ‖A s‖)) *
        Real.exp (∫ s in (0 : ℝ)..L, ‖A' s‖) := by
  set M := transfer A with hM
  set M' := transfer A' with hM'
  set δ : ℝ := ∫ s in (0 : ℝ)..L, ‖A s - A' s‖ with hδ
  set K : ℝ := ‖(1 : 𝔸)‖ * Real.exp (∫ s in (0 : ℝ)..L, ‖A s‖) with hK
  have hMc : ContinuousOn M (Icc 0 L) := continuousOn_transfer hL hA
  have hM'c : ContinuousOn M' (Icc 0 L) := continuousOn_transfer hL hA'
  have hsubx : ∀ x ∈ Icc (0 : ℝ) L, uIcc (0 : ℝ) x ⊆ uIcc (0 : ℝ) L := by
    intro x hx
    rw [uIcc_of_le hx.1, uIcc_of_le hL]; exact Icc_subset_Icc_right hx.2
  have hpM : IntervalIntegrable (fun s => A s * M s) volume 0 L :=
    hA.mul_continuousOn (by simpa [uIcc_of_le hL] using hMc)
  have hpM' : IntervalIntegrable (fun s => A' s * M' s) volume 0 L :=
    hA'.mul_continuousOn (by simpa [uIcc_of_le hL] using hM'c)
  have hd : IntervalIntegrable (fun s => A s - A' s) volume 0 L := hA.sub hA'
  have hdM : IntervalIntegrable (fun s => (A s - A' s) * M s) volume 0 L :=
    hd.mul_continuousOn (by simpa [uIcc_of_le hL] using hMc)
  have hEc : ContinuousOn (fun x => ‖M x - M' x‖) (Icc 0 L) := (hMc.sub hM'c).norm
  have hAEc : IntervalIntegrable (fun s => A' s * (M s - M' s)) volume 0 L :=
    hA'.mul_continuousOn (by rw [uIcc_of_le hL]; exact hMc.sub hM'c)
  have hid : ∀ x ∈ Icc (0 : ℝ) L, M x - M' x =
      (∫ s in (0 : ℝ)..x, (A s - A' s) * M s) + ∫ s in (0 : ℝ)..x, A' s * (M s - M' s) := by
    intro x hx
    have e1 := transfer_integral_eq hL hA hx
    have e2 := transfer_integral_eq hL hA' hx
    rw [← intervalIntegral.integral_add (hdM.mono_set (hsubx x hx)) (hAEc.mono_set (hsubx x hx))]
    have : ∀ s, (A s - A' s) * M s + A' s * (M s - M' s) = A s * M s - A' s * M' s := by
      intro s; noncomm_ring
    simp_rw [this]
    rw [intervalIntegral.integral_sub (hpM.mono_set (hsubx x hx)) (hpM'.mono_set (hsubx x hx))]
    change transfer A x - transfer A' x = _
    rw [e1, e2]; abel
  set m : ℝ → ℝ := fun s => ‖A' s‖ with hm
  have hmI : IntervalIntegrable m volume 0 L := hA'.norm
  have hineq : ∀ x ∈ Icc (0 : ℝ) L, ‖M x - M' x‖ ≤ δ * K + ∫ s in (0 : ℝ)..x, m s * ‖M s - M' s‖ := by
    intro x hx
    rw [hid x hx]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (intervalIntegral.norm_integral_le_integral_norm hx.1).trans ?_
      calc ∫ s in (0 : ℝ)..x, ‖(A s - A' s) * M s‖
          ≤ ∫ s in (0 : ℝ)..x, ‖A s - A' s‖ * K := by
            refine intervalIntegral.integral_mono_on hx.1 (hdM.mono_set (hsubx x hx)).norm
              (((hA.sub hA').norm.mono_set (hsubx x hx)).mul_const _) (fun s hs => ?_)
            exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
              (norm_transfer_le hL hA ⟨hs.1, hs.2.trans hx.2⟩) (norm_nonneg _))
        _ = (∫ s in (0 : ℝ)..x, ‖A s - A' s‖) * K := intervalIntegral.integral_mul_const _ _
        _ ≤ δ * K := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2
              (ae_of_all _ fun s => norm_nonneg _) hd.norm
    · refine (intervalIntegral.norm_integral_le_integral_norm hx.1).trans ?_
      refine intervalIntegral.integral_mono_on hx.1 (hAEc.mono_set (hsubx x hx)).norm ?_ (fun s hs => ?_)
      · exact (hmI.mono_set (hsubx x hx)).mul_continuousOn (by
          have : ContinuousOn (fun s => ‖M s - M' s‖) (uIcc 0 x) :=
            hEc.mono (by rw [uIcc_of_le hx.1]; exact Icc_subset_Icc_right hx.2)
          exact this)
      · exact norm_mul_le _ _
  have hδK : 0 ≤ δ * K := by
    refine mul_nonneg (intervalIntegral.integral_nonneg hL fun s _ => norm_nonneg _) (by positivity)
  have hg := gronwall_integral hL hmI (fun s => norm_nonneg _) hEc hineq x hx
  refine hg.trans ?_
  have : Real.exp (∫ s in (0 : ℝ)..x, m s) ≤ Real.exp (∫ s in (0 : ℝ)..L, ‖A' s‖) :=
    Real.exp_le_exp.2 (intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2
      (ae_of_all _ fun s => norm_nonneg _) hmI)
  exact mul_le_mul_of_nonneg_left this hδK

end General

end QuantumNLS.L1Stability

#print axioms QuantumNLS.L1Stability.gronwall_integral
#print axioms QuantumNLS.L1Stability.norm_transfer_le
#print axioms QuantumNLS.L1Stability.norm_transfer_sub_le
