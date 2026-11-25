import Mathlib
import NlsGge.Hierarchy.FiniteOrderGaussianTail38
import NlsGge.Ramer.General.RamerInstancesB

                                                                                                              
                                                                                                                            
                                                                                                                  
                                                                                                                     
                                 

set_option autoImplicit false
open NlsGge.Pilot NlsGge.HierarchyRiccati.Core

namespace NlsGge.Atomic.F011

theorem rate_upper_comparison (m : ℕ) (β : ℕ → ℝ) (hβ : ∀ i ≤ m, 0 ≤ β i) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℤ,
      finiteHierarchyRate38 m β n ≤ C * (1 + (n:ℝ)^2)^m := by
  refine ⟨1 + ∑ j ∈ Finset.range (m+1), β j * (2*Real.pi)^(2*j), by
    have : 0 ≤ ∑ j ∈ Finset.range (m+1), β j * (2*Real.pi)^(2*j) :=
      Finset.sum_nonneg (fun j hj => mul_nonneg (hβ j (by have := Finset.mem_range.1 hj; omega))
        (by rw [pow_mul]; positivity))
    linarith, fun n => ?_⟩
  unfold finiteHierarchyRate38 finiteHierarchyW38
  have hterm : ∀ j ∈ Finset.range (m+1),
      β j * (2*Real.pi*(n:ℝ))^(2*j) ≤ β j * (2*Real.pi)^(2*j) * (1 + (n:ℝ)^2)^m := by
    intro j hj
    have hjm : j ≤ m := by have := Finset.mem_range.1 hj; omega
    have hb : 0 ≤ β j := hβ j hjm
    have hA : (n:ℝ)^(2*j) ≤ (1 + (n:ℝ)^2)^m := by
      rw [pow_mul]
      calc ((n:ℝ)^2)^j ≤ (1 + (n:ℝ)^2)^j :=
            pow_le_pow_left₀ (sq_nonneg _) (by linarith [sq_nonneg (n:ℝ)]) j
        _ ≤ (1 + (n:ℝ)^2)^m := pow_le_pow_right₀ (by nlinarith [sq_nonneg (n:ℝ)]) hjm
    have hpow : (2*Real.pi*(n:ℝ))^(2*j) = (2*Real.pi)^(2*j) * (n:ℝ)^(2*j) := by
      rw [mul_pow]
    rw [hpow]
    have hc : 0 ≤ (2*Real.pi)^(2*j) := by positivity
    have := mul_le_mul_of_nonneg_left hA (mul_nonneg hb hc)
    nlinarith [this]
  calc ∑ j ∈ Finset.range (m+1), β j * (2*Real.pi*(n:ℝ))^(2*j)
      ≤ ∑ j ∈ Finset.range (m+1), β j * (2*Real.pi)^(2*j) * (1 + (n:ℝ)^2)^m :=
        Finset.sum_le_sum hterm
    _ = (∑ j ∈ Finset.range (m+1), β j * (2*Real.pi)^(2*j)) * (1 + (n:ℝ)^2)^m := by
        rw [Finset.sum_mul]
    _ ≤ (1 + ∑ j ∈ Finset.range (m+1), β j * (2*Real.pi)^(2*j)) * (1 + (n:ℝ)^2)^m := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith

theorem F011_CM_summable_iff (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ)
    (hβ : ∀ i ≤ m, 0 ≤ β i) (h0 : 0 < β 0) (hM : 0 < β m) (z : ℤ → ℂ) :
    Summable (fun n : ℤ => 2 * finiteHierarchyRate38 m β n * ‖z n‖^2) ↔
      SobolevSquareSummable (m:ℝ) z := by
  obtain ⟨c, hc, hlow⟩ := rate_lower_bracket38 m β (by omega) hβ h0 hM
  obtain ⟨C, hC, hup⟩ := rate_upper_comparison m β hβ
  have hSS : SobolevSquareSummable (m:ℝ) z ↔
      Summable (fun n : ℤ => (1 + (n:ℝ)^2)^m * ‖z n‖^2) := by
    unfold SobolevSquareSummable
    apply summable_congr
    intro n
    rw [← sobolevWeight_eq38 m n]
    rfl
  rw [hSS]
  constructor
  · intro h
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (h.mul_left (1 / (2 * c)))
    have hn := hlow n
    have hz : 0 ≤ ‖z n‖^2 := by positivity
    have hpos : 0 ≤ (1 + (n:ℝ)^2)^m := by positivity
    have key : c * (1 + (n:ℝ)^2)^m * ‖z n‖^2 ≤ finiteHierarchyRate38 m β n * ‖z n‖^2 :=
      mul_le_mul_of_nonneg_right hn hz
    rw [show 1 / (2 * c) * (2 * finiteHierarchyRate38 m β n * ‖z n‖^2) =
        finiteHierarchyRate38 m β n * ‖z n‖^2 / c by field_simp]
    rw [le_div_iff₀ hc]
    nlinarith [key]
  · intro h
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (h.mul_left (2 * C))
    · have hr0 : 0 ≤ finiteHierarchyRate38 m β n :=
        le_trans (by positivity) (hlow n)
      exact mul_nonneg (mul_nonneg (by norm_num) hr0) (by positivity)
    have hn := hup n
    have hz : 0 ≤ ‖z n‖^2 := by positivity
    have := mul_le_mul_of_nonneg_right hn hz
    nlinarith [this]


theorem finiteOrder_CameronMartin_normalization
    (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 < β j) :
    let S := NlsGge.Ramer.General.F05Setting m β hm (fun j hj => (hβ j hj).le)
      (hβ 0 (Nat.zero_le m)) (hβ m le_rfl)
    (∀ h : S.H,
      HasSum (fun n : ℤ => 2 * finiteHierarchyRate38 m β n * ‖S.hcoord h n‖^2)
        (‖h‖^2)) ∧
    (∀ z : ℤ → ℂ,
      Summable (fun n => 2 * finiteHierarchyRate38 m β n * ‖z n‖^2) ↔
        SobolevSquareSummable (m:ℝ) z) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℤ,
      c * sobolevModeWeight (m:ℝ) n ≤ 2 * finiteHierarchyRate38 m β n ∧
      2 * finiteHierarchyRate38 m β n ≤ C * sobolevModeWeight (m:ℝ) n) ∧
    (∀ (ι : Type) (b : HilbertBasis ι ℝ S.H),
      HasSum (fun i : ι => ‖S.incl (b i)‖^2)
        (∑' n : ℤ, sobolevModeWeight ((m-1:ℕ):ℝ) n /
          finiteHierarchyRate38 m β n)) := by
  intro S
  have h0 : 0 < β 0 := hβ 0 (Nat.zero_le m)
  have hM : 0 < β m := hβ m le_rfl
  have hβn : ∀ i ≤ m, 0 ≤ β i := fun j hj => (hβ j hj).le
  refine ⟨fun h => S.hasSum_H h, fun z => F011_CM_summable_iff m hm β hβn h0 hM z, ?_, ?_⟩
  · obtain ⟨c, hc, hlow⟩ := rate_lower_bracket38 m β (by omega) hβn h0 hM
    obtain ⟨C, hC, hup⟩ := rate_upper_comparison m β hβn
    refine ⟨2 * c, 2 * C, by positivity, by positivity, fun n => ?_⟩
    rw [sobolevWeight_eq38 m n]
    have hl := hlow n
    have hu := hup n
    constructor
    · nlinarith [hl]
    · nlinarith [hu]
  · intro ι b
    have hMt : ∀ n : ℤ, (S.M n).tr = 2 * sobolevModeWeight ((m-1:ℕ):ℝ) n :=
      fun n => NlsGge.Ramer.General.ModeForm.iso_tr _ _
    have hsum : (∑' n : ℤ, (S.M n).tr / (2 * S.q n)) =
        ∑' n : ℤ, sobolevModeWeight ((m-1:ℕ):ℝ) n / finiteHierarchyRate38 m β n := by
      apply tsum_congr
      intro n
      rw [hMt n]
      have hq : S.q n = finiteHierarchyRate38 m β n := rfl
      rw [hq]
      have hr : finiteHierarchyRate38 m β n ≠ 0 := by
        have := (rate_lower_bracket38 m β (by omega) hβn h0 hM)
        obtain ⟨c, hc, hlow⟩ := this
        have : 0 < c * (1 + (n:ℝ)^2)^m := by positivity
        linarith [hlow n]
      field_simp
    have h := S.incl_hs_hasSum b
    rw [hsum] at h
    exact h

end NlsGge.Atomic.F011
