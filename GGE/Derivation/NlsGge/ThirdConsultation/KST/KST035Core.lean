import Mathlib
import NlsGge.Atomic.KSTPath
import NlsGge.Atomic.KST.KST022
import NlsGge.Atomic.KST.KST018
import NlsGge.Atomic.KST.KST025
import NlsGge.Atomic.KST.KST026
import NlsGge.Atomic.KST.KST027

/- KST035Core PRODUCTION01 (proof development, AUTHOR; not self-reviewed).  Target NlsGge/ThirdConsultation/KST/KST035Core.lean.
   SUPPORT module for KST-035 (no packet increment; no design head).  ROUTE (see KST035_ROUTE.md): the source proof of
   Prop 5.1 invokes the Prop 4.1 estimate "as in (61)" with the weighted-tail smallness Cw^2 (R_N(phi_v)_w + ...) <= 1/60,
   which is not uniform on the omega-ball.  The landed kst027_core uses that smallness only through the hypothesis
   Cw^2 (T + y) <= 1/60.  The pattern estimates kst025/kst026 need no smallness.  Here the SAME proof is re-run
   (verbatim structure of K027Core.kst027_core) with the weaker, uniformly available hypotheses
   Cw^2 y <= 1/60 and a <= 1/60 (y = E/sqrt N, a = T/w(N)^2), the weighted tail T entering linearly:
   weightedMajorantTail w A N <= ofReal (900 Cw^2 (T+1) (a+y)^2). -/
set_option autoImplicit false
open scoped ENNReal BigOperators
open NlsGge.Atomic.KSTPath NlsGge.Atomic.KST

namespace NlsGge.ThirdConsultation.KST
noncomputable section

namespace KST035C

theorem bq_one_rel (C y T a U : ℝ) (j τ : ℕ) (hC : 1 ≤ C) (hy : 0 ≤ y) (hT : 0 ≤ T) (ha : 0 ≤ a)
    (hay : a ≤ 1 / 60) (hyy : y ≤ 1 / 60) (hU : a + y ≤ U)
    (hτ1 : 1 ≤ τ) (hτ2 : τ ≤ 2 * (j + 1) + 1) :
    5 ^ (2 * (j + 1)) * C ^ 2 * T * a ^ (τ - 1) * y ^ (2 * (j + 1) + 1 - τ) ≤
      25 * C ^ 2 * U ^ 2 * (T + 1) * (1 / 144) ^ j := by
  have hC2 : 1 ≤ C ^ 2 := by nlinarith
  set M := max a y with hM
  have hM0 : 0 ≤ M := le_max_of_le_left ha
  have hMU : M ≤ U := max_le (by linarith) (by linarith)
  have hMs : M ≤ 1 / 60 := max_le hay hyy
  have hpq : (τ - 1) + (2 * (j + 1) + 1 - τ) = 2 * j + 2 := by omega
  have hap : a ^ (τ - 1) ≤ M ^ (τ - 1) := pow_le_pow_left₀ ha (le_max_left _ _) _
  have hyq : y ^ (2 * (j + 1) + 1 - τ) ≤ M ^ (2 * (j + 1) + 1 - τ) :=
    pow_le_pow_left₀ hy (le_max_right _ _) _
  have hprod : a ^ (τ - 1) * y ^ (2 * (j + 1) + 1 - τ) ≤ M ^ (2 * j + 2) := by
    calc a ^ (τ - 1) * y ^ (2 * (j + 1) + 1 - τ) ≤ M ^ (τ - 1) * M ^ (2 * (j + 1) + 1 - τ) :=
          mul_le_mul hap hyq (by positivity) (by positivity)
      _ = M ^ (2 * j + 2) := by rw [← pow_add, hpq]
  have hM2 : M ^ (2 * j + 2) ≤ U ^ 2 * (1 / 3600) ^ j := by
    have : M ^ (2 * j + 2) = M ^ 2 * (M ^ 2) ^ j := by rw [← pow_mul]; ring
    rw [this]
    refine mul_le_mul (pow_le_pow_left₀ hM0 hMU 2) ?_ (by positivity) (by positivity)
    calc (M ^ 2) ^ j ≤ ((1 / 60) ^ 2) ^ j := pow_le_pow_left₀ (by positivity)
          (pow_le_pow_left₀ hM0 hMs 2) j
      _ = (1 / 3600) ^ j := by norm_num
  have h25 : (5 : ℝ) ^ (2 * (j + 1)) = 25 ^ (j + 1) := by rw [pow_mul]; norm_num
  rw [h25]
  have hU0 : 0 ≤ U := le_trans hM0 hMU
  have h25b : (25 : ℝ) ^ (j + 1) * (1 / 3600) ^ j = 25 * (1 / 144) ^ j := by
    have h : (25 : ℝ) ^ j * (1 / 3600) ^ j = (1 / 144) ^ j := by
      rw [← mul_pow]; norm_num
    calc (25 : ℝ) ^ (j + 1) * (1 / 3600) ^ j = 25 * ((25 : ℝ) ^ j * (1 / 3600) ^ j) := by ring
      _ = _ := by rw [h]
  have h1 : 25 ^ (j + 1) * C ^ 2 * T * (a ^ (τ - 1) * y ^ (2 * (j + 1) + 1 - τ)) ≤
      25 ^ (j + 1) * C ^ 2 * T * (U ^ 2 * (1 / 3600) ^ j) :=
    mul_le_mul_of_nonneg_left (hprod.trans hM2) (by positivity)
  have h2 : 25 ^ (j + 1) * C ^ 2 * T * (U ^ 2 * (1 / 3600) ^ j) =
      25 * C ^ 2 * T * U ^ 2 * (1 / 144) ^ j := by
    calc 25 ^ (j + 1) * C ^ 2 * T * (U ^ 2 * (1 / 3600) ^ j)
        = (25 ^ (j + 1) * (1 / 3600) ^ j) * (C ^ 2 * T * U ^ 2) := by ring
      _ = _ := by rw [h25b]; ring
  have h3 : 25 * C ^ 2 * T * U ^ 2 * (1 / 144) ^ j ≤ 25 * C ^ 2 * U ^ 2 * (T + 1) * (1 / 144) ^ j := by
    have : 0 ≤ 25 * C ^ 2 * U ^ 2 * (1 / 144 : ℝ) ^ j := by positivity
    nlinarith [this]
  calc 25 ^ (j + 1) * C ^ 2 * T * a ^ (τ - 1) * y ^ (2 * (j + 1) + 1 - τ) =
      25 ^ (j + 1) * C ^ 2 * T * (a ^ (τ - 1) * y ^ (2 * (j + 1) + 1 - τ)) := by ring
    _ ≤ _ := h1
    _ = _ := h2
    _ ≤ _ := h3

theorem core_rel (w A : ℤ → ℝ) (Cw : ℝ) (hw : SlowWeight w Cw) (hA : ∀ j, 0 ≤ A j)
    (hE : scalarEnergy w A < ⊤) (N : ℕ) (hN : 1 ≤ N)
    (hy1 : Cw ^ 2 * ((scalarEnergy w A).toReal / Real.sqrt (N : ℝ)) ≤ 1 / 60)
    (ha1 : (scalarTailEnergy w A N).toReal / w (N : ℤ) ^ 2 ≤ 1 / 60) :
    weightedMajorantTail w A N ≤ ENNReal.ofReal (900 * Cw ^ 2 *
      ((scalarTailEnergy w A N).toReal + 1) *
      ((scalarTailEnergy w A N).toReal / w (N : ℤ) ^ 2 +
        (scalarEnergy w A).toReal / Real.sqrt (N : ℝ)) ^ 2) := by
  classical
  have hC : 1 ≤ Cw := slowWeight_Cw_one_le hw
  set T : ℝ := (scalarTailEnergy w A N).toReal with hT
  set E : ℝ := (scalarEnergy w A).toReal with hEdef
  set y : ℝ := E / Real.sqrt (N : ℝ) with hy
  set a : ℝ := T / w (N : ℤ) ^ 2 with ha
  have hT0 : 0 ≤ T := ENNReal.toReal_nonneg
  have hE0 : 0 ≤ E := ENNReal.toReal_nonneg
  have hsqN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hy0 : 0 ≤ y := div_nonneg hE0 hsqN.le
  have hwN : 1 ≤ w (N : ℤ) := hw.one_le _
  have ha0 : 0 ≤ a := div_nonneg hT0 (sq_nonneg _)
  have haT : a ≤ T := by
    rw [ha]
    exact div_le_self hT0 (by nlinarith)
  have hC2 : 1 ≤ Cw ^ 2 := by nlinarith
  have hyy : y ≤ 1 / 60 := by nlinarith [mul_nonneg hy0 (sub_nonneg.2 hC2)]
  have hbound : ∀ ε : ℝ, 0 < ε → weightedMajorantTail w A N ≤
      ENNReal.ofReal (900 * Cw ^ 2 * (T + 1) * (a + y + ε) ^ 2) := by
    intro ε hε
    set U : ℝ := a + y + ε with hU
    have hU0 : 0 < U := by positivity
    set c0 : ℝ := 5 * Cw * U * Real.sqrt (T + 1) with hc0
    have hc0pos : 0 < c0 := by positivity
    set b : ℕ → ℝ := fun j => c0 * (1 / 12) ^ j with hb
    have hbpos : ∀ j, 0 < b j := fun j => by positivity
    have hs1 : Real.sqrt (T + 1) ^ 2 = T + 1 := Real.sq_sqrt (by linarith)
    have hb2 : ∀ j, b j ^ 2 = 25 * Cw ^ 2 * U ^ 2 * (T + 1) * (1 / 144) ^ j := by
      intro j
      have h12 : ((1 / 12 : ℝ) ^ j) ^ 2 = (1 / 144) ^ j := by
        rw [← pow_mul, mul_comm j 2, pow_mul]; norm_num
      have h : b j ^ 2 = (5 * Cw * U) ^ 2 * Real.sqrt (T + 1) ^ 2 * ((1 / 12 : ℝ) ^ j) ^ 2 := by
        simp only [hb, hc0]; ring
      rw [h, hs1, h12]; ring
    have hW : ∀ j (σ : Pattern (j+1)),
        (∑' n : ℤ, if N ≤ n.natAbs then ENNReal.ofReal (w (2*n)^2) *
          patternBlock (Nat.succ_pos j) A n σ ^ 2 else 0) ≤ ENNReal.ofReal (b j ^ 2) := by
      intro j σ
      refine (K027L2.weightedPattern_le_cauchy (Nat.succ_pos j) w A hA N σ).trans ?_
      rw [hb2]
      by_cases hτ : forcedTailCount (Nat.succ_pos j) σ = 0
      · refine (kst025 w A Cw hw hA hE N (j+1) hN (Nat.succ_pos j) σ hτ).2.2.trans ?_
        refine ENNReal.ofReal_le_ofReal ?_
        have h0 := K027D.bq_zero Cw y 0 a U j hC hy0 le_rfl ha0 (by linarith) (by linarith)
        refine h0.trans ?_
        have hpos : 0 ≤ 25 * Cw ^ 2 * U ^ 2 * (1 / 144 : ℝ) ^ j := by positivity
        nlinarith [hpos, mul_nonneg hpos hT0]
      · have hτ1 : 1 ≤ forcedTailCount (Nat.succ_pos j) σ := Nat.one_le_iff_ne_zero.2 hτ
        refine (kst026 w A Cw hw hA hE N (j+1) hN (Nat.succ_pos j) σ hτ1).2.trans ?_
        exact ENNReal.ofReal_le_ofReal (bq_one_rel Cw y T a U j _ hC hy0 hT0 ha0 ha1 hyy
          (by linarith) hτ1 (K027Core.forcedTailCount_le (Nat.succ_pos j) σ))
    refine (K027L2.S_le w A hA N b hbpos hW).trans ?_
    have htot : ∑' j : ℕ, (4 : ℝ≥0∞) ^ (j + 1) * ENNReal.ofReal (b j) = ENNReal.ofReal (6 * c0) :=
      K027Core.total_eq c0 hc0pos
    rw [htot, ← ENNReal.ofReal_pow (by positivity)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    have hsq : c0 ^ 2 = 25 * Cw ^ 2 * U ^ 2 * (T + 1) := by
      have h : c0 ^ 2 = (5 * Cw * U) ^ 2 * Real.sqrt (T + 1) ^ 2 := by
        simp only [hc0]; ring
      rw [h, hs1]; ring
    calc (6 * c0) ^ 2 = 36 * c0 ^ 2 := by ring
      _ = 900 * Cw ^ 2 * (T + 1) * U ^ 2 := by rw [hsq]; ring
  have hcont : Filter.Tendsto
      (fun ε : ℝ => ENNReal.ofReal (900 * Cw ^ 2 * (T + 1) * (a + y + ε) ^ 2))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (ENNReal.ofReal (900 * Cw ^ 2 * (T + 1) * (a + y + 0) ^ 2))) := by
    have : Continuous (fun ε : ℝ => ENNReal.ofReal (900 * Cw ^ 2 * (T + 1) * (a + y + ε) ^ 2)) :=
      ENNReal.continuous_ofReal.comp (by fun_prop)
    exact (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), weightedMajorantTail w A N ≤
      ENNReal.ofReal (900 * Cw ^ 2 * (T + 1) * (a + y + ε) ^ 2) :=
    eventually_nhdsWithin_of_forall (fun ε hε => hbound ε hε)
  simpa using ge_of_tendsto hcont hev

end KST035C

end
end NlsGge.ThirdConsultation.KST
