import NlsGge.Hierarchy.RiccatiRealRemainderV3_38
import NlsGge.Hierarchy.RiccatiFrequencyScaling38
import Mathlib.Tactic

/-! Batch 38, A01.06–.07: integer frequency scaling `u_k(x) = P(kx)` in the
explicit real `V_3` (paper/v2.tex lines 2465-2469):
`V_3(u_k) = β₃ k⁴ F(P) + k² (10β₂∫P²P'² + 70β₃∫P⁴P'²) + (β₁∫P⁴ + 2β₂∫P⁶ + 5β₃∫P⁸)`,
hence `V_3(u_k) → -∞` when `β₃ > 0` and `F(P) < 0`. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open scoped ContDiff

theorem scaled_contDiff38 (P : ℝ → ℝ) (hP : ContDiff ℝ ∞ P) (k : ℝ) :
    ContDiff ℝ ∞ (fun y => P (k * y)) :=
  hP.comp (contDiff_const.mul contDiff_id)

theorem scaled_ofReal_contDiff38 (P : ℝ → ℝ) (hP : ContDiff ℝ ∞ P) (k : ℝ) :
    ContDiff ℝ ∞ (fun y => ((P (k * y) : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (scaled_contDiff38 P hP k)

theorem scaled_ofReal_periodic38 (P : ℝ → ℝ) (hper : Function.Periodic P 1) (k : ℕ) :
    Function.Periodic (fun y => ((P (k * y) : ℝ) : ℂ)) 1 := by
  intro y
  simp only [periodic_comp_nat_mul38 P hper k y]

private theorem iterDerivCont38 (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (k : ℕ) :
    Continuous (iteratedDeriv k g) :=
  hg.continuous_iteratedDeriv k (by exact_mod_cast le_top)

theorem periodic_deriv38 (f : ℝ → ℝ) (hf : Function.Periodic f 1) :
    Function.Periodic (deriv f) 1 := by
  intro y
  have h : (fun x => f (x + 1)) = f := funext hf
  rw [← deriv_comp_add_const, h]

/-- Exact scaling identity for `V_3`. -/
theorem remainderV3_scaled38 (β : ℕ → ℝ) (P : ℝ → ℝ) (hP : ContDiff ℝ ∞ P)
    (hper : Function.Periodic P 1) (k : ℕ) (hk : 1 ≤ k) :
    remainderV38 3 β (fun y => ((P (k * y) : ℝ) : ℂ)) (scaled_ofReal_contDiff38 P hP k)
        (scaled_ofReal_periodic38 P hper k) =
      β 3 * (k : ℝ) ^ 4 *
          (∫ x in (0:ℝ)..1, quarticDensity38 (P x) (deriv P x) (iteratedDeriv 2 P x)) +
        (k : ℝ) ^ 2 * (10 * β 2 * (∫ x in (0:ℝ)..1, (P x) ^ 2 * (deriv P x) ^ 2) +
          70 * β 3 * (∫ x in (0:ℝ)..1, (P x) ^ 4 * (deriv P x) ^ 2)) +
        (β 1 * (∫ x in (0:ℝ)..1, (P x) ^ 4) + 2 * β 2 * (∫ x in (0:ℝ)..1, (P x) ^ 6) +
          5 * β 3 * (∫ x in (0:ℝ)..1, (P x) ^ 8)) := by
  set u : ℝ → ℝ := fun y => P (k * y) with hudef
  have hu := scaled_contDiff38 P hP k
  have huper : Function.Periodic u 1 := periodic_comp_nat_mul38 P hper k
  rw [remainderV3_real38 β u hu huper]
  have hd1 : ∀ x, deriv u x = k * deriv P (k * x) := by
    intro x
    have h := iteratedDeriv_comp_mul38 P hP k 1 x
    simpa [iteratedDeriv_one] using h
  have hd2 : ∀ x, iteratedDeriv 2 u x = (k : ℝ) ^ 2 * iteratedDeriv 2 P (k * x) :=
    fun x => iteratedDeriv_comp_mul38 P hP k 2 x
  have c0 : Continuous P := hP.continuous
  have c1 : Continuous (deriv P) := hP.continuous_deriv (by exact_mod_cast le_top)
  have c2 : Continuous (iteratedDeriv 2 P) := iterDerivCont38 P hP 2
  have p1 : Function.Periodic (deriv P) 1 := periodic_deriv38 P hper
  have p2 : Function.Periodic (iteratedDeriv 2 P) 1 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]; exact periodic_deriv38 _ p1
  have hsc : ∀ h : ℝ → ℝ, Continuous h → Function.Periodic h 1 →
      (∫ x in (0:ℝ)..1, h (k * x)) = ∫ x in (0:ℝ)..1, h x :=
    fun h hc hp => intervalIntegral_comp_nat_mul_periodic38 h hc hp k hk
  simp_rw [hd1, hd2]
  simp only [hudef]
  have i1 := hsc (fun z => (P z) ^ 4) (by fun_prop) (fun z => by simp [hper z])
  have i2 := hsc (fun z => (P z) ^ 2 * (deriv P z) ^ 2) (by fun_prop)
    (fun z => by simp [hper z, p1 z])
  have i3 := hsc (fun z => (P z) ^ 6) (by fun_prop) (fun z => by simp [hper z])
  have i4 := hsc (fun z => quarticDensity38 (P z) (deriv P z) (iteratedDeriv 2 P z))
    (by unfold quarticDensity38; fun_prop) (fun z => by simp [hper z, p1 z, p2 z])
  have i5 := hsc (fun z => (P z) ^ 4 * (deriv P z) ^ 2) (by fun_prop)
    (fun z => by simp [hper z, p1 z])
  have i6 := hsc (fun z => (P z) ^ 8) (by fun_prop) (fun z => by simp [hper z])
  have q : ∀ x, quarticDensity38 (P (k * x)) (k * deriv P (k * x))
      ((k : ℝ) ^ 2 * iteratedDeriv 2 P (k * x)) =
      (k : ℝ) ^ 4 * quarticDensity38 (P (k * x)) (deriv P (k * x)) (iteratedDeriv 2 P (k * x)) := by
    intro x; unfold quarticDensity38; ring
  simp only [q]
  have r1 : ∀ x, 10 * P (k * x) ^ 2 * (k * deriv P (k * x)) ^ 2 + 2 * P (k * x) ^ 6 =
      (k : ℝ) ^ 2 * 10 * (P (k * x) ^ 2 * deriv P (k * x) ^ 2) + 2 * P (k * x) ^ 6 := by
    intro x; ring
  have r2 : ∀ x, 70 * P (k * x) ^ 4 * (k * deriv P (k * x)) ^ 2 + 5 * P (k * x) ^ 8 =
      (k : ℝ) ^ 2 * 70 * (P (k * x) ^ 4 * deriv P (k * x) ^ 2) + 5 * P (k * x) ^ 8 := by
    intro x; ring
  simp_rw [r1, r2]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  rw [i1, i2, i3, i4, i5, i6]
  ring

/-- Elementary: `a t² + b t + c → -∞` for `a < 0`. -/
theorem quartic_poly_eventually_lt38 (a b c C : ℝ) (ha : a < 0) :
    ∃ k : ℕ, 1 ≤ k ∧ a * (k : ℝ) ^ 4 + (k : ℝ) ^ 2 * b + c < C := by
  obtain ⟨k, hk⟩ := exists_nat_gt ((|b| + |c| + |C| + 1) / (-a) + 1)
  refine ⟨k, ?_, ?_⟩
  · have : (1 : ℝ) < k := by
      have : 0 ≤ (|b| + |c| + |C| + 1) / (-a) := by
        apply div_nonneg (by positivity) (by linarith)
      linarith
    exact_mod_cast this.le
  · set t : ℝ := (k : ℝ) ^ 2 with ht
    have hk1 : (1 : ℝ) ≤ k := by
      have : 0 ≤ (|b| + |c| + |C| + 1) / (-a) := by
        apply div_nonneg (by positivity) (by linarith)
      linarith
    have ht1 : 1 ≤ t := by rw [ht]; nlinarith
    have htk : (k : ℝ) ≤ t := by rw [ht]; nlinarith
    have hbound : (|b| + |c| + |C| + 1) / (-a) < t := by linarith
    have hat : a * t < -(|b| + |c| + |C| + 1) := by
      have := (div_lt_iff₀ (by linarith : (0:ℝ) < -a)).mp hbound
      linarith
    have e : a * (k : ℝ) ^ 4 = (a * t) * t := by rw [ht]; ring
    rw [e]
    have h1 : (a * t) * t ≤ -(|b| + |c| + |C| + 1) * t := by nlinarith
    have h2 : t * b ≤ t * |b| := by nlinarith [le_abs_self b]
    have h3 : c ≤ |c| * t := by nlinarith [le_abs_self c, abs_nonneg c]
    nlinarith [neg_abs_le C, abs_nonneg C, abs_nonneg b, abs_nonneg c]

/-- A01.07: if `β₃ > 0` and `F(P) < 0`, the scaled fields drive `V_3` below any
bound. -/
theorem remainderV3_scaled_lt38 (β : ℕ → ℝ) (hβ3 : 0 < β 3) (P : ℝ → ℝ)
    (hP : ContDiff ℝ ∞ P) (hper : Function.Periodic P 1)
    (hF : (∫ x in (0:ℝ)..1, quarticDensity38 (P x) (deriv P x) (iteratedDeriv 2 P x)) < 0)
    (C : ℝ) :
    ∃ k : ℕ, 1 ≤ k ∧
      remainderV38 3 β (fun y => ((P (k * y) : ℝ) : ℂ)) (scaled_ofReal_contDiff38 P hP k)
        (scaled_ofReal_periodic38 P hper k) < C := by
  obtain ⟨k, hk, hlt⟩ := quartic_poly_eventually_lt38
    (β 3 * ∫ x in (0:ℝ)..1, quarticDensity38 (P x) (deriv P x) (iteratedDeriv 2 P x))
    (10 * β 2 * (∫ x in (0:ℝ)..1, (P x) ^ 2 * (deriv P x) ^ 2) +
          70 * β 3 * (∫ x in (0:ℝ)..1, (P x) ^ 4 * (deriv P x) ^ 2))
    (β 1 * (∫ x in (0:ℝ)..1, (P x) ^ 4) + 2 * β 2 * (∫ x in (0:ℝ)..1, (P x) ^ 6) +
          5 * β 3 * (∫ x in (0:ℝ)..1, (P x) ^ 8)) C (mul_neg_of_pos_of_neg hβ3 hF)
  refine ⟨k, hk, ?_⟩
  rw [remainderV3_scaled38 β P hP hper k hk]
  linarith

end NlsGge.HierarchyRiccati.Core

end
