import Mathlib
import NlsGge.ThirdConsultation.G1.Round5
import NlsGge.ThirdConsultation.KSPS.Round5
import NlsGge.ThirdConsultation.G1.Wkb035A

                                                                                
                                                                            
                                                                             
                                                                                                   

                                                                        
                                                                                                 
                                                                          
                                                                                                                                                                 

                                                                                                        
                                                                                                          
                                                                                                          
                                                                                                                           
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GKDefinitionDesign
open scoped ENNReal
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.GK38
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38

namespace NlsGge.ThirdConsultation.KSPSSupport
noncomputable section

/-- S1: every physical L2 field lies in the order-zero Sobolev class. -/
theorem physicalSobolev_zero_all (u : PhysicalL2) : physicalSobolev (0 : ℝ) u := by
  unfold physicalSobolev SobolevSquareSummable
  have h : Summable (fun n : ℤ => ‖(reflectedFourierL2 u) n‖ ^ 2) := by
    have h2 := Memℓp.summable (p := (2 : ℝ≥0∞)) (by norm_num) (reflectedFourierL2 u).2
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h2
  refine Summable.congr h (fun n => ?_)
  simp

/-- Scalar multiplication commutes with the L2 product in the first slot. -/
theorem productInL2_smul_left_of (c : ℂ) (u v : PhysicalL2) (huv : productInL2 u v) :
    productInL2 (c • u) v := by
  have hm : MemLp (fun x : PhysicalCircle => c * (u x * v x)) 2 spatialMeasure :=
    MemLp.const_mul huv c
  refine hm.ae_eq ?_
  filter_upwards [Lp.coeFn_smul c u] with x hx
  simp [hx, mul_assoc]

/-- The product with the zero field. -/
theorem physicalProduct_zero_left (v : PhysicalL2) : physicalProduct 0 v = 0 := by
  unfold physicalProduct
  split_ifs with h
  · apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp h, Lp.coeFn_zero ℂ 2 spatialMeasure] with x h1 h2
    rw [h1, h2]
    simp
  · rfl

/-- S4 (first slot): physicalProduct is homogeneous in its first argument. -/
theorem physicalProduct_smul_left (c : ℂ) (u v : PhysicalL2) :
    physicalProduct (c • u) v = c • physicalProduct u v := by
  by_cases huv : productInL2 u v
  · have hc : productInL2 (c • u) v := productInL2_smul_left_of c u v huv
    apply Lp.ext
    filter_upwards [physicalProduct_ae (c • u) v hc, Lp.coeFn_smul c (physicalProduct u v),
      physicalProduct_ae u v huv, Lp.coeFn_smul c u] with x h1 h2 h3 h4
    simp only [Pi.smul_apply, smul_eq_mul] at h2 h4 ⊢
    rw [h1, h2, h3, h4]
    ring
  · by_cases hc : c = 0
    · subst hc
      rw [zero_smul, physicalProduct_zero_left, zero_smul]
    · have hn : ¬ productInL2 (c • u) v := by
        intro h
        apply huv
        have hm : MemLp (fun x : PhysicalCircle => c⁻¹ * ((c • u) x * v x)) 2 spatialMeasure :=
          MemLp.const_mul h c⁻¹
        refine hm.ae_eq ?_
        filter_upwards [Lp.coeFn_smul c u] with x hx
        simp [hx, ← mul_assoc, inv_mul_cancel₀ hc]
      unfold physicalProduct
      rw [dif_neg huv, dif_neg hn, smul_zero]

/-- The L2 product is commutative as a physical class. -/
theorem physicalProduct_comm (u v : PhysicalL2) : physicalProduct u v = physicalProduct v u := by
  have e : (fun x : PhysicalCircle => u x * v x) = fun x => v x * u x :=
    funext fun x => mul_comm _ _
  by_cases huv : productInL2 u v
  · have hvu : productInL2 v u := by
      unfold productInL2 at huv ⊢
      rw [← e]
      exact huv
    apply Lp.ext
    filter_upwards [physicalProduct_ae u v huv, physicalProduct_ae v u hvu] with x h1 h2
    rw [h1, h2, mul_comm]
  · have hvu : ¬ productInL2 v u := by
      intro h
      apply huv
      unfold productInL2 at h ⊢
      rw [e]
      exact h
    unfold physicalProduct
    rw [dif_neg huv, dif_neg hvu]

/-- S4 (second slot): physicalProduct is homogeneous in its second argument. -/
theorem physicalProduct_smul_right (c : ℂ) (u v : PhysicalL2) :
    physicalProduct u (c • v) = c • physicalProduct u v := by
  rw [physicalProduct_comm u (c • v), physicalProduct_smul_left, physicalProduct_comm v u]

/-- The scalar factor of the reflected Fourier coefficients of `c • u`. -/
theorem reflectedFourierL2_smul_apply (c : ℂ) (u : PhysicalL2) (n : ℤ) :
    reflectedFourierL2 (c • u) n = c * reflectedFourierL2 u n := by
  rw [map_smul]
  simp

/-- S4 (weak derivative): the weak derivative is homogeneous. -/
theorem weakDerivative_smul (c : ℂ) (u : PhysicalL2) :
    weakDerivative (c • u) = c • weakDerivative u := by
  by_cases hc : c = 0
  · subst hc
    simp [weakDerivative]
    intro h
    exact Subtype.ext rfl
  · have e : (fun n : ℤ => (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) *
          reflectedFourierL2 (c • u) n) =
          c • (fun n : ℤ => (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) *
            reflectedFourierL2 u n) := by
        funext n
        rw [reflectedFourierL2_smul_apply, Pi.smul_apply, smul_eq_mul]
        ring
    unfold weakDerivative
    by_cases hd : Memℓp (fun n : ℤ => (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) *
        reflectedFourierL2 u n) 2
    · have hd' : Memℓp (fun n : ℤ => (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) *
          reflectedFourierL2 (c • u) n) 2 := by
        rw [e]
        exact hd.const_smul c
      have hlp : (⟨_, hd'⟩ : lp (fun _ : ℤ => ℂ) 2) =
          c • (⟨_, hd⟩ : lp (fun _ : ℤ => ℂ) 2) :=
        Subtype.ext e
      rw [dif_pos hd, dif_pos hd', hlp, map_smul]
    · have hd' : ¬ Memℓp (fun n : ℤ => (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) *
          reflectedFourierL2 (c • u) n) 2 := by
        intro h
        apply hd
        have hback : (fun n : ℤ => (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) *
            reflectedFourierL2 u n) =
            c⁻¹ • (fun n : ℤ => (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) *
              reflectedFourierL2 (c • u) n) := by
          rw [e, smul_smul, inv_mul_cancel₀ hc, one_smul]
        rw [hback]
        exact h.const_smul c⁻¹
      rw [dif_neg hd, dif_neg hd', smul_zero]

end
end NlsGge.ThirdConsultation.KSPSSupport
namespace NlsGge.ThirdConsultation.KSPSSupport
noncomputable section

/-- S2 (scalar form): the physical embedding of an order-m Sobolev class lies in physicalSobolev m. -/
theorem physicalSobolevEmbed_mem (m : ℕ) (u : PhysicalSobolev38 (m : ℝ)) :
    physicalSobolev (m : ℝ) (physicalSobolevEmbed m u) := by
  have hcoord : ∀ n : ℤ, (reflectedFourierL2 (physicalSobolevEmbed m u)) n =
      carrierCoe38 (m : ℝ) (physicalSobolevFourierEquiv38 (m : ℝ) u) n :=
    fun n => physicalSobolevEmbed_fourier m u n
  unfold physicalSobolev SobolevSquareSummable
  simp only [hcoord]
  exact (mem_seqSobolev38_iff (m : ℝ) _).1 (carrierCoe38_mem (m : ℝ) _)

/-- S2: the pair attached to an order-N Sobolev field is in pairSobolev N. -/
theorem pairSobolev_toPotPair {N : ℕ} (φ : SobolevC N) :
    pairSobolev (N : ℝ) (toPotPair φ) :=
  ⟨physicalSobolevEmbed_mem N φ.1, physicalSobolevEmbed_mem N φ.2⟩

/-- S2 (swap version): the swapped pair is also in pairSobolev N. -/
theorem pairSobolev_swap_toPotPair {N : ℕ} (φ : SobolevC N) :
    pairSobolev (N : ℝ) (Prod.swap (toPotPair φ)) :=
  ⟨physicalSobolevEmbed_mem N φ.2, physicalSobolevEmbed_mem N φ.1⟩

end
end NlsGge.ThirdConsultation.KSPSSupport
namespace NlsGge.ThirdConsultation.KSPSSupport
noncomputable section
open NlsGge.GKDefinitionDesign

theorem g35_identity_ne (M : ℕ) (φ : PotPair) (l : ℂ) (hl : l ≠ 0)
    (hr : ∀ k, 1 ≤ k → k ≤ M + 1 → physicalSobolev 1 (wkbR φ k))
    (hφ : physicalSobolev 1 φ.1) :
    wkbResidual (M + 1) l φ = wkbResidualTail (M + 1) l φ := by
  have hl0 : (2 * Complex.I * l) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hl
  have he0 : ((2 * Complex.I * l) ^ 0)⁻¹ = (1 : ℂ) := by simp
  have he_mul : ∀ n j : ℕ, ((2 * Complex.I * l) ^ n)⁻¹ * ((2 * Complex.I * l) ^ j)⁻¹ =
      ((2 * Complex.I * l) ^ (n + j))⁻¹ := by
    intro n j
    rw [← mul_inv, ← pow_add]
  have hh : ∀ n : ℕ, 1 ≤ n → (2 * Complex.I * l) * ((2 * Complex.I * l) ^ n)⁻¹ =
      ((2 * Complex.I * l) ^ (n - 1))⁻¹ := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ, mul_inv]
    field_simp
  have hr1 : wkbR φ 1 = -φ.2 := wkbR_one φ
  have hDr : ∀ n : ℕ, 1 ≤ n → n ≤ M →
      weakDerivative (wkbR φ n) = wkbR φ (n + 1) -
        ∑ k ∈ Finset.Icc 1 (n - 1), physicalProduct φ.1 (physicalProduct (wkbR φ k) (wkbR φ (n - k))) := by
    intro n hn _
    have h := wkbR_succ φ n hn
    rw [g35_P_sum_right φ.1 hφ] at h
    exact eq_sub_of_add_eq h.symm
  have hfs : ∀ i ∈ Finset.Icc 1 (M + 1), physicalSobolev 1 (wkbR φ i) := fun i hi =>
    hr i (Finset.mem_Icc.1 hi).1 (Finset.mem_Icc.1 hi).2
  have hW : weakDerivative (∑ n ∈ Finset.Icc 1 (M + 1), ((2 * Complex.I * l) ^ n)⁻¹ • wkbR φ n) =
      ∑ n ∈ Finset.Icc 1 (M + 1), ((2 * Complex.I * l) ^ n)⁻¹ • weakDerivative (wkbR φ n) :=
    g35_D_sum _ _ _ hfs
  have hP : physicalProduct φ.1
      (physicalProduct (∑ n ∈ Finset.Icc 1 (M + 1), ((2 * Complex.I * l) ^ n)⁻¹ • wkbR φ n)
        (∑ n ∈ Finset.Icc 1 (M + 1), ((2 * Complex.I * l) ^ n)⁻¹ • wkbR φ n)) =
      ∑ n ∈ Finset.Icc 1 (M + 1), ∑ j ∈ Finset.Icc 1 (M + 1),
        (((2 * Complex.I * l) ^ n)⁻¹ * ((2 * Complex.I * l) ^ j)⁻¹) •
          physicalProduct φ.1 (physicalProduct (wkbR φ n) (wkbR φ j)) := by
    rw [g35_P_sum_smul_self _ _ _ hfs, g35_P_sum_right φ.1 hφ]
    apply Finset.sum_congr rfl
    intro n _
    rw [g35_P_sum_right φ.1 hφ]
    apply Finset.sum_congr rfl
    intro j _
    rw [g35_P_smul_right _ _ _ hφ]
  unfold wkbResidual wkbResidualTail
  unfold wkbPartial
  rw [hW, hP]
  exact g35_algebra M (fun n => ((2 * Complex.I * l) ^ n)⁻¹) (2 * Complex.I * l)
    (fun n => wkbR φ n) (fun n => weakDerivative (wkbR φ n))
    (fun k j => physicalProduct φ.1 (physicalProduct (wkbR φ k) (wkbR φ j))) φ.2
    he0 he_mul hh hr1 hDr


end
end NlsGge.ThirdConsultation.KSPSSupport
