import Mathlib
import NlsGge.Hierarchy.RiccatiQ6Negative38
import NlsGge.Hierarchy.RiccatiQ6Scaling38
import NlsGge.Hierarchy.GaussianTailContractionsF06C2_38
import NlsGge.Birkhoff.F05Identity38
import NlsGge.ThirdConsultation.F.Bridge037A
import NlsGge.ThirdConsultation.F.Bridge037B

                                                                                                              
                                                                                                                      
                                                                                         
                                                                                                                  
                                                                                                        
                                                                   
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ContDiff
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core NlsGge.Birkhoff

namespace NlsGge.ThirdConsultation.F
namespace F037Aux

/-- Absolute bound for `k² X + Y`, `k ≥ 1`. -/
theorem abs_bound037 (k X Y : ℝ) (hk : 1 ≤ k) : |k ^ 2 * X + Y| ≤ (|X| + |Y|) * k ^ 2 := by
  have hk2 : (1 : ℝ) ≤ k ^ 2 := by nlinarith
  have h1 : |k ^ 2 * X| = k ^ 2 * |X| := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg k)]
  have h2 : |Y| ≤ |Y| * k ^ 2 := le_mul_of_one_le_right (abs_nonneg Y) hk2
  calc |k ^ 2 * X + Y| ≤ |k ^ 2 * X| + |Y| := abs_add_le _ _
    _ = k ^ 2 * |X| + |Y| := by rw [h1]
    _ ≤ k ^ 2 * |X| + |Y| * k ^ 2 := by linarith
    _ = (|X| + |Y|) * k ^ 2 := by ring

/-- Eventual negativity of `a k⁴ + X k² + Y` for `a < 0` along the natural numbers. -/
theorem quartic_eventually037 (a X Y C : ℝ) (ha : a < 0) :
    ∀ᶠ k : ℕ in atTop, a * (k : ℝ) ^ 4 + (k : ℝ) ^ 2 * X + Y < C := by
  have hna : 0 < -a := by linarith
  have hB0 : (0 : ℝ) ≤ (|X| + |Y| + |C| + 1) / (-a) :=
    div_nonneg (by positivity) hna.le
  obtain ⟨K, hK⟩ := exists_nat_gt ((|X| + |Y| + |C| + 1) / (-a))
  refine Filter.eventually_atTop.2 ⟨K, fun k hk => ?_⟩
  have hkK : (K : ℝ) ≤ (k : ℝ) := Nat.cast_le.2 hk
  have hkB : (|X| + |Y| + |C| + 1) / (-a) < (k : ℝ) := lt_of_lt_of_le hK hkK
  have hk0 : (0 : ℝ) < (k : ℝ) := lt_of_le_of_lt hB0 hkB
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
    have h0 : 0 < k := by exact_mod_cast hk0
    exact_mod_cast h0
  have hkk : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hbig : (|X| + |Y| + |C| + 1) / (-a) < (k : ℝ) ^ 2 := lt_of_lt_of_le hkB hkk
  have hat : a * (k : ℝ) ^ 2 < -(|X| + |Y| + |C| + 1) := by
    have h := (div_lt_iff₀ hna).mp hbig
    linarith
  have ht1 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have h1 : a * (k : ℝ) ^ 2 * (k : ℝ) ^ 2 ≤ -(|X| + |Y| + |C| + 1) * (k : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right hat.le (sq_nonneg _)
  have h2 : (k : ℝ) ^ 2 * X ≤ (k : ℝ) ^ 2 * |X| :=
    mul_le_mul_of_nonneg_left (le_abs_self X) (sq_nonneg _)
  have hD : (0 : ℝ) ≤ |Y| + |C| + 1 := by positivity
  have h3 : (|Y| + |C| + 1) * 1 ≤ (|Y| + |C| + 1) * (k : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left ht1 hD
  have hC : -|C| ≤ C := neg_abs_le C
  linarith [le_abs_self Y]

end F037Aux

/-- F-037 (`C:prop:negative` dilation step): integer dilates of a real trigonometric
polynomial have the exact expansion of `vLocal38 3`, the remainder is `β₃ k⁴ F(f) + O(k²)`,
and the realized remainder is unbounded below on the Fourier planes. -/
theorem f037 (β : ℕ → ℝ) (hβ : ∀ j ≤ 3, 0 < β j)
    (f : ℝ → ℝ) (hf : IsRealTrigPoly38 f) (hneg : q6QuarticF38 f < 0) :
    (∀ k : ℕ, IsRealTrigPoly38 (fun x => f ((k : ℝ) * x))) ∧
    (∀ k : ℕ, 1 ≤ k →
      vLocal38 3 β (fun x => (f ((k : ℝ) * x) : ℂ)) =
        β 3 * (k : ℝ) ^ 4 * q6QuarticF38 f +
        (k : ℝ) ^ 2 *
          (10 * β 2 * (∫ x in (0 : ℝ)..1, (f x) ^ 2 * (deriv f x) ^ 2) +
           70 * β 3 * (∫ x in (0 : ℝ)..1, (f x) ^ 4 * (deriv f x) ^ 2)) +
        β 1 * (∫ x in (0 : ℝ)..1, (f x) ^ 4) +
        2 * β 2 * (∫ x in (0 : ℝ)..1, (f x) ^ 6) +
        5 * β 3 * (∫ x in (0 : ℝ)..1, (f x) ^ 8)) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
      |vLocal38 3 β (fun x => (f ((k : ℝ) * x) : ℂ)) -
        β 3 * (k : ℝ) ^ 4 * q6QuarticF38 f| ≤ C * (k : ℝ) ^ 2) ∧
    Tendsto (fun k : ℕ => vLocal38 3 β (fun x => (f ((k : ℝ) * x) : ℂ)))
      atTop atBot ∧
    ∀ A : ℝ, ∃ N : ℕ, ∃ z : FourierPlane N,
      (∀ x : ℝ, (planeReal N z x).im = 0) ∧
      Vm38 3 β (planeElement38 (2 : ℝ) N z) < A := by
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = 10 * β 2 * (∫ x in (0 : ℝ)..1, (f x) ^ 2 * (deriv f x) ^ 2) +
      70 * β 3 * (∫ x in (0 : ℝ)..1, (f x) ^ 4 * (deriv f x) ^ 2) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = β 1 * (∫ x in (0 : ℝ)..1, (f x) ^ 4) +
      2 * β 2 * (∫ x in (0 : ℝ)..1, (f x) ^ 6) +
      5 * β 3 * (∫ x in (0 : ℝ)..1, (f x) ^ 8) := ⟨_, rfl⟩
  have hq : q6QuarticF38 f =
      ∫ x in (0 : ℝ)..1, quarticDensity38 (f x) (deriv f x) (iteratedDeriv 2 f x) := rfl
  -- exact expansion in grouped form
  have hexp : ∀ k : ℕ, 1 ≤ k →
      vLocal38 3 β (fun x => (f ((k : ℝ) * x) : ℂ)) =
        β 3 * (k : ℝ) ^ 4 * q6QuarticF38 f + (k : ℝ) ^ 2 * X + Y := by
    intro k hk
    have hb : vLocal38 3 β (fun x => (f ((k : ℝ) * x) : ℂ)) =
        remainderV38 3 β (fun y => ((f ((k : ℝ) * y) : ℝ) : ℂ))
          (scaled_ofReal_contDiff38 f hf.contDiff k) (scaled_ofReal_periodic38 f hf.periodic k) :=
      Bridge037B.vLocal_trig037 β (fun y => f ((k : ℝ) * y)) (hf.comp_nat_mul k)
    rw [hb, remainderV3_scaled38 β f hf.contDiff hf.periodic k hk, hq, hX, hY] <;> ring
  refine ⟨fun k => hf.comp_nat_mul k, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rw [hexp k hk, hX, hY] <;> ring
  · refine ⟨|X| + |Y|, by positivity, fun k hk => ?_⟩
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    rw [hexp k hk]
    have e : β 3 * (k : ℝ) ^ 4 * q6QuarticF38 f + (k : ℝ) ^ 2 * X + Y -
        β 3 * (k : ℝ) ^ 4 * q6QuarticF38 f = (k : ℝ) ^ 2 * X + Y := by ring
    rw [e]
    exact F037Aux.abs_bound037 (k : ℝ) X Y hk1
  · have hneg3 : β 3 * q6QuarticF38 f < 0 := mul_neg_of_pos_of_neg (hβ 3 le_rfl) hneg
    refine Filter.tendsto_atBot.2 (fun C => ?_)
    filter_upwards [F037Aux.quartic_eventually037 (β 3 * q6QuarticF38 f) X Y C hneg3,
      eventually_ge_atTop 1] with k hkC hk1
    show vLocal38 3 β (fun x => (f ((k : ℝ) * x) : ℂ)) ≤ C
    rw [hexp k hk1]
    linarith
  · intro A
    have hneg3 : β 3 * q6QuarticF38 f < 0 := mul_neg_of_pos_of_neg (hβ 3 le_rfl) hneg
    obtain ⟨k, hkA, hk1⟩ := Filter.Eventually.exists
      ((F037Aux.quartic_eventually037 (β 3 * q6QuarticF38 f) X Y A hneg3).and
        (eventually_ge_atTop 1))
    obtain ⟨N, z, hz⟩ := Bridge037A.trig_realize037 (fun y => f ((k : ℝ) * y))
      (hf.comp_nat_mul k)
    refine ⟨N, z, fun x => ?_, ?_⟩
    · simp [hz x]
    · have e2 : planeReal N z = (fun x => (f ((k : ℝ) * x) : ℂ)) := funext hz
      rw [Bridge037B.Vm38_planeElement037 β N z, e2, hexp k hk1]
      linarith

end NlsGge.ThirdConsultation.F
end
