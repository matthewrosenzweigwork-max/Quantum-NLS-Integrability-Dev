import Mathlib
import NlsGge.Atomic.M.M014
import NlsGge.Atomic.M.M010Support1
import NlsGge.Atomic.M.M009Support8
import NlsGge.Spectral.ActualQuasimomentumDecayE02_38
import NlsGge.Spectral.ActualGapHeightHolderE02_38
import NlsGge.Atomic.I.I038FiniteGap
import NlsGge.ThirdConsultation.M.M016Host
import NlsGge.Atomic.M.M017Scalar

/- M-017 REAL TRACE CORE, PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). SUPPORT (no packet
   increment). Target NlsGge/Atomic/M/M017RealCore.lean, namespace NlsGge.ThirdConsultation.M017R.
   Molnar Thm 4(3), finite-gap real case, by Lemma 4 (coefficients) + the Herglotz/Cauchy form of the quasimomentum
   (instead of the contour formula (6); same coefficients, landed real inputs).  Hypotheses = exactly the M-016 body
   used (real or complex head): the exterior representative's agreement with the actual primitive (`hrep`, unfolded
   ExteriorPrimitiveRepresentative) and `PrimitiveLaurentCoefficients N φ F`; plus u ∈ H¹ and finitely many open gaps.
   For 2 ≤ k ≤ N+1: Σ_n higherAction u n k is summable and equals (−((2i)^{k−1})⁻¹ H_k(φ)).re.
   Route: J_{n,k} = (2/π)∫_{gap n} x^{k−1}v (landed M-014) → finite support, Σ J = (2/π)M_{k−1}, M_m = ∫ t^m v
   (I038F.sum_gapInt_eq with W(y) = (y/2)^{k−1}); on z = iy: F = −i k (landed primitive_formulas),
   k(z) = z + (1/π)∫v/(t−z) (landed actualQuasimomentum_herglotz_E02_38), Cauchy moment expansion (M017S) vs. the
   PrimitiveLaurentCoefficients expansion at order K = k → coefficient uniqueness (M017S.coeffs_zero) gives
   (i/π)M_{k−1} = H_k/(2i)^k; hence Σ J = −((2i)^{k−1})⁻¹ H_k (k=1 mass trace is separate and not used). -/
set_option autoImplicit false
open Filter MeasureTheory
open scoped BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Birkhoff
open NlsGge.ThirdConsultation

namespace NlsGge.ThirdConsultation.M017R

theorem sum_range_shift (f : ℕ → ℂ) (k : ℕ) :
    ∑ m ∈ Finset.range k, f (m + 1) = ∑ j ∈ Finset.Icc 1 k, f j := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]

theorem sum_Icc_one (f : ℕ → ℂ) (k : ℕ) (hk : 1 ≤ k) :
    ∑ j ∈ Finset.Icc 1 k, f j = f 1 + ∑ j ∈ Finset.Icc 2 k, f j := by
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_Icc_succ_top (by omega)]
    ring

theorem trace_real_core (u : PhysicalL2) (hu1 : SobolevSquareSummable 1 (physicalFourier u))
    (hfin : {n : ℤ | actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n}.Finite)
    (R : ℝ) (F : ℂ → ℂ)
    (hrep : ∀ z : ℂ, R < ‖z‖ →
      ∃ hz : realSlice u ∈ gkW ∧ z ∈ MPrimitive.endpointClosureFiber (realSlice u),
        F z = NlsGge.ThirdConsultation.M.primitive ⟨(realSlice u, z), hz⟩)
    (N : ℕ) (φ : KSPS.SobolevC N) (hPLC : NlsGge.ThirdConsultation.M.PrimitiveLaurentCoefficients N φ F)
    (k : ℕ) (hk : 2 ≤ k) (hkN : k ≤ N + 1) :
    Summable (fun n : ℤ => NlsGge.ThirdConsultation.M.higherAction u n k) ∧
    (∑' n : ℤ, NlsGge.ThirdConsultation.M.higherAction u n k) =
      (-((2 * Complex.I) ^ (k - 1))⁻¹ *
        NlsGge.ThirdConsultation.M.hierarchyCharge φ ⟨k, (by omega), hkN⟩).re := by
  set v : ℝ → ℝ := actualGapHeightE02_38 u with hv_def
  have hv : Continuous v := continuous_actualGapHeightE02_38 u
  obtain ⟨-, A, hA⟩ := actualGapHeight_support_finiteGap_E02_38 u hfin
  have hsupp : ∀ t : ℝ, max A 0 < |t| → v t = 0 := fun t ht => hA t (lt_of_le_of_lt (le_max_left _ _) ht)
  set W : ℝ → ℝ := fun y => (y / 2) ^ (k - 1) with hW_def
  have hW : Continuous W := (continuous_id.div_const 2).pow _
  have hW2 : ∀ x : ℝ, W (2 * x) = x ^ (k - 1) := fun x => by
    simp only [hW_def]; rw [mul_div_cancel_left₀ x two_ne_zero]
  have hJ : ∀ n : ℤ, NlsGge.ThirdConsultation.M.higherAction u n k = gapIntW38 W u n := by
    intro n
    rw [(NlsGge.ThirdConsultation.M.higher_action_gap_integral u n k (by omega)).2.2.2.2]
    unfold gapIntW38
    congr 1
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    simp only [hW2]
    rfl
  have hG0 : ∀ n ∉ hfin.toFinset, gapIntW38 W u n = 0 := by
    intro n hn
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_lt] at hn
    have : actualGapLowerAllE02_38 u n = actualGapUpperAllE02_38 u n :=
      le_antisymm (actualGapLower_le_upper38' u n) hn
    unfold gapIntW38
    rw [this, intervalIntegral.integral_same, mul_zero]
  have hsum : Summable (fun n : ℤ => NlsGge.ThirdConsultation.M.higherAction u n k) :=
    (summable_of_ne_finset_zero hG0).congr (fun n => (hJ n).symm)
  set M : ℝ := ∫ t : ℝ, t ^ (k - 1) * v t with hM_def
  have hsumJ : (∑' n : ℤ, NlsGge.ThirdConsultation.M.higherAction u n k) = (2 / Real.pi) * M := by
    rw [tsum_congr hJ, tsum_eq_sum hG0, NlsGge.ThirdConsultation.I038F.sum_gapInt_eq W hW u hfin]
    simp only [hW2]
    rfl
  refine ⟨hsum, ?_⟩
  -- complex side
  obtain ⟨C1, R1, hC1, hR1, hP⟩ := hPLC k (by omega) hkN
  obtain ⟨C2, hC2, hcm⟩ := NlsGge.ThirdConsultation.M017S.cauchy_moments v hv (max A 0) (le_max_right _ _) hsupp k
  set Mc : ℕ → ℂ := fun m => ∫ t : ℝ, (v t : ℂ) * (t : ℂ) ^ m with hMc
  set H1 : ℂ := NlsGge.ThirdConsultation.M.hierarchyCharge φ ⟨1, le_rfl, Nat.succ_le_succ (Nat.zero_le N)⟩
    with hH1
  set q : ℕ → ℂ := fun j => if j = 1 then -H1 * (2 * Complex.I)⁻¹ else
    (if hj : 1 ≤ j ∧ j ≤ N + 1 then
      NlsGge.ThirdConsultation.M.hierarchyCharge φ ⟨j, hj.1, hj.2⟩ * ((2 * Complex.I) ^ j)⁻¹ else 0) with hq
  set d : ℕ → ℂ := fun j => Complex.I / Real.pi * Mc (j - 1) - q j with hd
  set Y0 : ℝ := max (max R R1) 1 + 1 with hY0
  have hbound : ∀ y : ℝ, Y0 ≤ y → 0 < y →
      ‖∑ j ∈ Finset.Icc 1 k, d j * (Complex.I * y)⁻¹ ^ j‖ ≤ (C1 + C2 / Real.pi) * y⁻¹ ^ (k + 1) := by
    intro y hy hypos
    set z : ℂ := Complex.I * y with hz_def
    have hzn : ‖z‖ = y := by
      rw [hz_def, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hypos]
    have hz0 : z ≠ 0 := by rw [← norm_ne_zero_iff, hzn]; exact hypos.ne'
    have him : 0 < z.im := by simp [hz_def, hypos]
    have hyR : R < ‖z‖ := by
      rw [hzn]; have := le_max_left R R1; have := le_max_left (max R R1) 1; linarith
    have hyR1 : R1 ≤ ‖z‖ := by
      rw [hzn]; have := le_max_right R R1; have := le_max_left (max R R1) 1; linarith
    obtain ⟨hz, hFz⟩ := hrep z hyR
    have hFk : F z = -Complex.I * actualQuasimomentumE02_38 u z := by
      rw [hFz]; exact (MPrimitive.primitive_formulas u).1 z him
    obtain ⟨-, hherg⟩ := actualQuasimomentum_herglotz_E02_38 u hu1 z him
    obtain ⟨-, hE1⟩ := hcm y hypos
    have hE2 := hP z hyR1
    set Int : ℂ := ∫ t : ℝ, (v t : ℂ) / ((t : ℂ) - z) with hInt
    have hFI : F z + Complex.I * z = -Complex.I * ((1 / Real.pi : ℂ) * Int) := by
      rw [hFk, hherg]; ring
    have hS1 : ∑ j ∈ Finset.Icc 1 k, Mc (j - 1) * z⁻¹ ^ j = ∑ m ∈ Finset.range k, Mc m * z⁻¹ ^ (m + 1) := by
      rw [← sum_range_shift (fun j => Mc (j - 1) * z⁻¹ ^ j) k]
      simp only [Nat.add_sub_cancel]
    have hS2 : ∑ j ∈ Finset.Icc 1 k, q j * z⁻¹ ^ j =
        -H1 / (2 * Complex.I * z) + ∑ j ∈ Finset.Icc 2 k,
          (if hj : 1 ≤ j ∧ j ≤ N + 1 then
            NlsGge.ThirdConsultation.M.hierarchyCharge φ ⟨j, hj.1, hj.2⟩ / (2 * Complex.I * z) ^ j
           else 0) := by
      rw [sum_Icc_one _ k (by omega)]
      congr 1
      · simp only [hq, ↓reduceIte, pow_one]
        field_simp
      · refine Finset.sum_congr rfl (fun j hj => ?_)
        have hj1 : j ≠ 1 := by have := (Finset.mem_Icc.1 hj).1; omega
        simp only [hq, hj1, ↓reduceIte]
        split_ifs with hc
        · rw [mul_pow, inv_pow]; field_simp; ring
        · simp
    have hid : ∑ j ∈ Finset.Icc 1 k, d j * z⁻¹ ^ j =
        Complex.I / Real.pi * ((∫ t : ℝ, (v t : ℂ) / ((t : ℂ) - Complex.I * y)) +
          ∑ m ∈ Finset.range k, (∫ t : ℝ, (v t : ℂ) * (t : ℂ) ^ m) * (Complex.I * y)⁻¹ ^ (m + 1)) +
        (F z + Complex.I * z +
          NlsGge.ThirdConsultation.M.hierarchyCharge φ ⟨1, le_rfl, Nat.succ_le_succ (Nat.zero_le N)⟩ /
            (2 * Complex.I * z) -
          ∑ j ∈ Finset.Icc 2 k,
            (if hj : 1 ≤ j ∧ j ≤ N + 1 then
              NlsGge.ThirdConsultation.M.hierarchyCharge φ ⟨j, hj.1, hj.2⟩ / (2 * Complex.I * z) ^ j
             else 0)) := by
      have e1 : ∑ j ∈ Finset.Icc 1 k, d j * z⁻¹ ^ j =
          Complex.I / Real.pi * ∑ j ∈ Finset.Icc 1 k, Mc (j - 1) * z⁻¹ ^ j -
            ∑ j ∈ Finset.Icc 1 k, q j * z⁻¹ ^ j := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun j _ => by simp only [hd]; ring)
      rw [e1, hS1, hS2]
      rw [← hz_def, ← hInt]
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      rw [hFI]
      simp only [hMc, hH1]
      generalize (∑ j ∈ Finset.Icc 2 k,
            (if hj : 1 ≤ j ∧ j ≤ N + 1 then
              NlsGge.ThirdConsultation.M.hierarchyCharge φ ⟨j, hj.1, hj.2⟩ / (2 * Complex.I * z) ^ j
             else 0)) = S
      generalize (∑ m ∈ Finset.range k, (∫ t : ℝ, (v t : ℂ) * (t : ℂ) ^ m) * z⁻¹ ^ (m + 1)) = T
      field_simp
      ring_nf
    rw [hid]
    have hE2' : ‖F z + Complex.I * z +
          NlsGge.ThirdConsultation.M.hierarchyCharge φ ⟨1, le_rfl, Nat.succ_le_succ (Nat.zero_le N)⟩ /
            (2 * Complex.I * z) -
          ∑ j ∈ Finset.Icc 2 k,
            (if hj : 1 ≤ j ∧ j ≤ N + 1 then
              NlsGge.ThirdConsultation.M.hierarchyCharge φ ⟨j, hj.1, hj.2⟩ / (2 * Complex.I * z) ^ j
             else 0)‖ ≤ C1 * y⁻¹ ^ (k + 1) := by
      refine hE2.trans (le_of_eq ?_)
      rw [hzn, div_eq_mul_inv, inv_pow]
    have hn : ‖Complex.I / (Real.pi : ℂ)‖ = 1 / Real.pi := by
      rw [norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    calc _ ≤ ‖Complex.I / (Real.pi : ℂ) * ((∫ t : ℝ, (v t : ℂ) / ((t : ℂ) - Complex.I * y)) +
          ∑ m ∈ Finset.range k, (∫ t : ℝ, (v t : ℂ) * (t : ℂ) ^ m) * (Complex.I * y)⁻¹ ^ (m + 1))‖ +
          ‖F z + Complex.I * z +
            NlsGge.ThirdConsultation.M.hierarchyCharge φ ⟨1, le_rfl, Nat.succ_le_succ (Nat.zero_le N)⟩ /
              (2 * Complex.I * z) -
            ∑ j ∈ Finset.Icc 2 k,
              (if hj : 1 ≤ j ∧ j ≤ N + 1 then
                NlsGge.ThirdConsultation.M.hierarchyCharge φ ⟨j, hj.1, hj.2⟩ / (2 * Complex.I * z) ^ j
               else 0)‖ := norm_add_le _ _
      _ ≤ 1 / Real.pi * (C2 * y⁻¹ ^ (k + 1)) + C1 * y⁻¹ ^ (k + 1) := by
          rw [norm_mul, hn]
          exact add_le_add (mul_le_mul_of_nonneg_left hE1 (by positivity)) hE2'
      _ = (C1 + C2 / Real.pi) * y⁻¹ ^ (k + 1) := by ring
  have hdk := NlsGge.ThirdConsultation.M017S.coeffs_zero k d _ Y0 hbound k (Finset.mem_Icc.2 ⟨by omega, le_rfl⟩)
  have hk1 : k ≠ 1 := by omega
  have hc : 1 ≤ k ∧ k ≤ N + 1 := ⟨by omega, hkN⟩
  simp only [hd, hq, hk1, ↓reduceIte, dif_pos hc] at hdk
  have hMc : Mc (k - 1) = (M : ℂ) := by
    simp only [hMc, hM_def]
    rw [← integral_complex_ofReal]
    congr 1; funext t; push_cast; ring
  rw [hMc] at hdk
  rw [hsumJ]
  have hfinal : (((2 / Real.pi) * M : ℝ) : ℂ) = -((2 * Complex.I) ^ (k - 1))⁻¹ *
      NlsGge.ThirdConsultation.M.hierarchyCharge φ ⟨k, (by omega), hkN⟩ := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hdk ⊢
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h2I : (2 * Complex.I) ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
    have hM' : (M : ℂ) = Real.pi / Complex.I *
        (NlsGge.ThirdConsultation.M.hierarchyCharge φ ⟨j + 1, hc.1, hc.2⟩ * ((2 * Complex.I) ^ (j + 1))⁻¹) := by
      rw [← sub_eq_zero.1 hdk]; field_simp
    push_cast
    rw [hM', pow_succ]
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [← hfinal, Complex.ofReal_re]

end NlsGge.ThirdConsultation.M017R
