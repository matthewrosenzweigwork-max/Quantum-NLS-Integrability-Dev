import Mathlib
import NlsGge.Atomic.M.M016Core2
import NlsGge.Atomic.M.M016Lift
import NlsGge.Atomic.M.M016HalfNodeReal
import NlsGge.ThirdConsultation.M.M016Host

                                                                                                                
                                                                                                      
                                                                                                                      
                                                                                                                       
                                                                                      
                                                                                                                          
                                                                            
                                                                                                                    
                                                                                                               
                                                                                                                         
                                                                        
set_option autoImplicit false
open Filter Topology
open scoped BigOperators
open NlsGge.Pilot NlsGge.GK38
open NlsGge.ThirdConsultation

namespace NlsGge.ThirdConsultation.M016Q

theorem sum_range_succ_eq (f : ℕ → ℂ) (M : ℕ) :
    ∑ k ∈ Finset.range (M + 1), f k = f 0 + ∑ k ∈ Finset.Icc 1 M, f k := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]
    ring

theorem sum_range_succ_eq_two (f : ℕ → ℂ) (K : ℕ) (hK : 1 ≤ K) :
    ∑ k ∈ Finset.range (K + 1), f k = f 0 + f 1 + ∑ k ∈ Finset.Icc 2 K, f k := by
  induction K, hK using Nat.le_induction with
  | base => simp [Finset.sum_range_succ]
  | succ K hK ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]
    ring

theorem zpow_term (x c : ℂ) (k : ℕ) :
    (2 * Complex.I * x) ^ (-(k : ℤ)) * c = ((2 * Complex.I) ^ k)⁻¹ * c * x⁻¹ ^ k := by
  rw [zpow_neg, zpow_natCast, mul_pow, mul_inv, inv_pow]
  ring

theorem laurent_core (u : PhysicalL2) (R : ℝ) (F : ℂ → ℂ)
    (hrep : ∀ z : ℂ, R < ‖z‖ →
      ∃ hz : realSlice u ∈ gkW ∧ z ∈ MPrimitive.endpointClosureFiber (realSlice u),
        F z = NlsGge.ThirdConsultation.M.primitive ⟨(realSlice u, z), hz⟩)
    (hval : MPrimitive.HasValueAtInfinity (fun z : ℂ => F z + Complex.I * z) 0)
    (hG : NlsGge.ThirdConsultation.M.AnalyticAtInfinity (fun z : ℂ => F z + Complex.I * z))
    (N : ℕ) (φ : KSPS.SobolevC N) (hφ : KSPS.toPotPair φ = realSlice u)
    (ψ : KSPS.SobolevC (N + 2)) (hψ : KSPS.toPotPair ψ = realSlice u)
    (h031 : ∃ (C : ℝ) (J : ℕ), 0 ≤ C ∧ ∀ j : ℤ, J ≤ j.natAbs →
      ∃ hchart : KSPSWKB.NonresonantBranchDomain ψ j (KSPSWKB.halfNode j),
        ‖KSPSWKB.primitive (N + 2) ψ ⟨(j, KSPSWKB.halfNode j), hchart⟩ +
            Complex.I * KSPS.wkbPhase ψ (KSPSWKB.halfNode j)‖ ≤
          C / ‖KSPSWKB.halfNode j‖ ^ (N + 2))
    (hcoef : ∀ (k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N + 2 + 1),
      KSPS.integralRiccatiLeft ψ k =
        if k = 1 then -NlsGge.ThirdConsultation.M.hierarchyCharge ψ ⟨k, hk, hkN⟩
        else NlsGge.ThirdConsultation.M.hierarchyCharge ψ ⟨k, hk, hkN⟩) :
    NlsGge.ThirdConsultation.M.PrimitiveLaurentCoefficients N φ F := by
  set a : ℕ → ℂ := fun k => if k = 0 then 0 else ((2 * Complex.I) ^ k)⁻¹ * KSPS.integralRiccatiLeft ψ k
    with ha
  obtain ⟨C, J1, hC, hJ1⟩ := h031
  obtain ⟨J2, hJ2⟩ := NlsGge.ThirdConsultation.M016H.halfNode_real u R F hrep hval (N + 2) ψ hψ
  set J : ℕ := max J1 J2 with hJ
  set x : ℕ → ℂ := fun n => KSPSWKB.halfNode ((J : ℤ) + (n : ℤ)) with hx
  have hxabs : ∀ n : ℕ, ((J : ℤ) + (n : ℤ)).natAbs = J + n := fun n => by omega
  have hxnorm : ∀ n : ℕ, ((J + n : ℕ) : ℝ) ≤ ‖x n‖ := fun n => by
    have := NlsGge.ThirdConsultation.KSPS031Analytic.natAbs_le_norm_halfNode_expr ((J : ℤ) + (n : ℤ))
    rw [hxabs] at this
    exact this
  have hx0 : ∀ n, x n ≠ 0 := fun n => by
    have := NlsGge.ThirdConsultation.KSPS031Analytic.one_le_norm_halfNode_expr ((J : ℤ) + (n : ℤ))
    intro h; change KSPSWKB.halfNode _ = 0 at h
    unfold KSPSWKB.halfNode at h; rw [h, norm_zero] at this; linarith
  have hxt : Tendsto (fun n => ‖x n‖) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
    exact le_trans (by exact_mod_cast Nat.le_add_left n J) (hxnorm n)
  -- the WKB phase as the Laurent polynomial of the a_k
  have hwkb : ∀ y : ℂ, Complex.I * KSPS.wkbPhase ψ y =
      Complex.I * y - ∑ k ∈ Finset.range (N + 2 + 1), a k * y⁻¹ ^ k := by
    intro y
    unfold KSPS.wkbPhase
    rw [sum_range_succ_eq]
    have e : ∑ k ∈ Finset.Icc 1 (N + 2), a k * y⁻¹ ^ k =
        ∑ k ∈ Finset.Icc 1 (N + 2), (2 * Complex.I * y) ^ (-(k : ℤ)) * KSPS.integralRiccatiLeft ψ k := by
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hk0 : k ≠ 0 := by have := (Finset.mem_Icc.1 hk).1; omega
      simp only [ha, hk0, ↓reduceIte]
      rw [zpow_term]
    rw [e]
    simp only [ha, ↓reduceIte, zero_mul, zero_add]
    rw [mul_add, ← mul_assoc, Complex.I_mul_I]
    ring
  have hb : ∀ n, ‖F (x n) + Complex.I * x n - ∑ k ∈ Finset.range (N + 2), a k * (x n)⁻¹ ^ k‖ ≤
      (C + ‖a (N + 2)‖) * ‖(x n)⁻¹‖ ^ (N + 2) := by
    intro n
    have hj1 : J1 ≤ ((J : ℤ) + (n : ℤ)).natAbs := by rw [hxabs]; omega
    have hj2 : J2 ≤ ((J : ℤ) + (n : ℤ)).natAbs := by rw [hxabs]; omega
    obtain ⟨hch, hbound⟩ := hJ1 _ hj1
    obtain ⟨hch', hF⟩ := hJ2 _ hj2
    have hFx : F (x n) = KSPSWKB.primitive (N + 2) ψ ⟨((J : ℤ) + (n : ℤ), x n), hch⟩ := hF
    have e : F (x n) + Complex.I * x n - ∑ k ∈ Finset.range (N + 2), a k * (x n)⁻¹ ^ k =
        (KSPSWKB.primitive (N + 2) ψ ⟨((J : ℤ) + (n : ℤ), x n), hch⟩ +
          Complex.I * KSPS.wkbPhase ψ (x n)) + a (N + 2) * (x n)⁻¹ ^ (N + 2) := by
      rw [hFx, hwkb, Finset.sum_range_succ (fun k => a k * (x n)⁻¹ ^ k) (N + 2)]
      ring
    rw [e]
    have hxpos : 0 < ‖x n‖ := norm_pos_iff.2 (hx0 n)
    have h1 : C / ‖x n‖ ^ (N + 2) = C * ‖(x n)⁻¹‖ ^ (N + 2) := by
      rw [norm_inv, inv_pow, div_eq_mul_inv]
    calc _ ≤ ‖KSPSWKB.primitive (N + 2) ψ ⟨((J : ℤ) + (n : ℤ), x n), hch⟩ +
            Complex.I * KSPS.wkbPhase ψ (x n)‖ + ‖a (N + 2) * (x n)⁻¹ ^ (N + 2)‖ := norm_add_le _ _
      _ ≤ C * ‖(x n)⁻¹‖ ^ (N + 2) + ‖a (N + 2)‖ * ‖(x n)⁻¹‖ ^ (N + 2) := by
          rw [← h1, norm_mul, norm_pow]
          exact add_le_add hbound le_rfl
      _ = (C + ‖a (N + 2)‖) * ‖(x n)⁻¹‖ ^ (N + 2) := by ring
  obtain ⟨C', R', hC', hR', hext⟩ :=
    NlsGge.ThirdConsultation.M016C.exterior_bound F hG a (N + 2) x hx0 hxt _ hb
  intro K hK1 hKN
  obtain ⟨C'', R'', hC'', hR'', htr⟩ := NlsGge.ThirdConsultation.M016C.truncate
    (fun z => F z + Complex.I * z) a (N + 2) K (by omega) C' R' hC' hR' hext
  refine ⟨C'', R'', hC'', hR'', fun z hz => ?_⟩
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hR'' hz
  have hz0 : z ≠ 0 := norm_pos_iff.1 hzpos
  have hlift : KSPS.toPotPair ψ = KSPS.toPotPair φ := hψ.trans hφ.symm
  have hexpr : F z + Complex.I * z +
      NlsGge.ThirdConsultation.M.hierarchyCharge φ ⟨1, le_rfl, Nat.succ_le_succ (Nat.zero_le N)⟩ /
        (2 * Complex.I * z) -
      ∑ k ∈ Finset.Icc 2 K,
        (if hk : 1 ≤ k ∧ k ≤ N + 1 then
          NlsGge.ThirdConsultation.M.hierarchyCharge φ ⟨k, hk.1, hk.2⟩ / (2 * Complex.I * z) ^ k
         else 0) =
      F z + Complex.I * z - ∑ k ∈ Finset.range (K + 1), a k * z⁻¹ ^ k := by
    rw [sum_range_succ_eq_two _ K hK1]
    have ha1 : a 1 * z⁻¹ ^ 1 = -NlsGge.ThirdConsultation.M.hierarchyCharge φ
        ⟨1, le_rfl, Nat.succ_le_succ (Nat.zero_le N)⟩ / (2 * Complex.I * z) := by
      simp only [ha, one_ne_zero, ↓reduceIte]
      rw [hcoef 1 le_rfl (by omega), if_pos rfl,
        NlsGge.ThirdConsultation.M.hierarchyCharge_lift ψ φ hlift 1 le_rfl (by omega) (by omega)]
      field_simp
    have hak : ∀ k ∈ Finset.Icc 2 K, a k * z⁻¹ ^ k =
        (if hk : 1 ≤ k ∧ k ≤ N + 1 then
          NlsGge.ThirdConsultation.M.hierarchyCharge φ ⟨k, hk.1, hk.2⟩ / (2 * Complex.I * z) ^ k
         else 0) := by
      intro k hk
      obtain ⟨hk2, hkK⟩ := Finset.mem_Icc.1 hk
      have hc : 1 ≤ k ∧ k ≤ N + 1 := ⟨by omega, by omega⟩
      have hk0 : k ≠ 0 := by omega
      have hk1 : k ≠ 1 := by omega
      rw [dif_pos hc]
      simp only [ha, hk0, ↓reduceIte]
      rw [hcoef k hc.1 (by omega), if_neg hk1,
        NlsGge.ThirdConsultation.M.hierarchyCharge_lift ψ φ hlift k hc.1 (by omega) hc.2]
      rw [mul_pow, inv_pow]
      field_simp
      ring
    rw [Finset.sum_congr rfl hak, ha1]
    simp only [ha, ↓reduceIte, zero_mul, zero_add]
    ring
  rw [hexpr]
  have h := htr z hz
  rw [norm_inv, inv_pow, ← div_eq_mul_inv] at h
  exact h

end NlsGge.ThirdConsultation.M016Q
