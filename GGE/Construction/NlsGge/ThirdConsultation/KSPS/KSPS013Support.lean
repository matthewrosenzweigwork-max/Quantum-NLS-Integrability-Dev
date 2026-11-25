import Mathlib
import NlsGge.Hierarchy.RiccatiWronskianIdentity38
import NlsGge.Hierarchy.FormalLogExactness38
import NlsGge.Atomic.M.M003
import NlsGge.ThirdConsultation.M.M053Sup4
import NlsGge.ThirdConsultation.KSPSSupport.ANA01
import NlsGge.ThirdConsultation.KSPSInversePhaseHost

                                                                                                                  
                                                                                               
                                                                                                                  
                                                                        
                                                                                         
                                                                                                                
                                                                                                                 
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace NlsGge.ThirdConsultation.KSPSWKB
noncomputable section
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign NlsGge.HierarchyRiccati.Core
open NlsGge.ThirdConsultation.KSPS

/-! ### Formal part -/

theorem rv_p_zero : p 0 = 0 := by simp [p]

theorem rv_swap_mem_jetAlg {r : ℕ} {P : Poly} (hP : P ∈ NlsGge.Atomic.M003.jetAlg r) :
    riccatiSwap38 P ∈ NlsGge.Atomic.M003.jetAlg r := by
  unfold NlsGge.Atomic.M003.jetAlg at hP ⊢
  induction hP using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    rw [riccatiSwap38_X]
    exact Algebra.subset_adjoin
      (show MvPolynomial.X ((!v.1, v.2) : Jet) ∈ NlsGge.Atomic.M003.jetGen r from ⟨(!v.1, v.2), hv, rfl⟩)
  | algebraMap c =>
    rw [MvPolynomial.algebraMap_eq, riccatiSwap38_C, ← MvPolynomial.algebraMap_eq]
    exact Subalgebra.algebraMap_mem _ c
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy =>
    rw [map_mul]
    exact Subalgebra.mul_mem _ hx hy

theorem rv_p_mem {r a : ℕ} (ha : a ≤ r + 1) : p a ∈ NlsGge.Atomic.M003.jetAlg r := by
  rcases a with _ | a
  · rw [rv_p_zero]
    exact Subalgebra.zero_mem _
  · exact NlsGge.Atomic.M003.jetAlg_mono (by omega)
      (NlsGge.Atomic.M003.mem_jetAlg_of_jetOrd (NlsGge.Atomic.M003.p_jetOrd a))

theorem rv_coeffP_mem {r m : ℕ} (hm : m ≤ r + 2) :
    PowerSeries.coeff m (riccatiGamma38 * riccatiDelta38) ∈ NlsGge.Atomic.M003.jetAlg r := by
  rw [PowerSeries.coeff_mul]
  refine Subalgebra.sum_mem _ (fun x hx => ?_)
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  simp only [riccatiGamma38, riccatiDelta38, PowerSeries.coeff_mk]
  by_cases h1 : x.1 = 0
  · rw [h1, rv_p_zero, zero_mul]
    exact Subalgebra.zero_mem _
  by_cases h2 : x.2 = 0
  · rw [h2, rv_p_zero, map_zero, mul_zero, mul_zero]
    exact Subalgebra.zero_mem _
  refine Subalgebra.mul_mem _ (rv_p_mem (by omega))
    (Subalgebra.mul_mem _ ?_ (rv_swap_mem_jetAlg (rv_p_mem (by omega))))
  exact Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _

theorem rv_coeff_pow_mem {r k : ℕ} (P : PowerSeries Poly)
    (hP : ∀ m, m ≤ k → PowerSeries.coeff m P ∈ NlsGge.Atomic.M003.jetAlg r) (n : ℕ) :
    ∀ m, m ≤ k → PowerSeries.coeff m (P ^ n) ∈ NlsGge.Atomic.M003.jetAlg r := by
  induction n with
  | zero =>
    intro m _
    rw [pow_zero, PowerSeries.coeff_one]
    split_ifs
    · exact Subalgebra.one_mem _
    · exact Subalgebra.zero_mem _
  | succ n ih =>
    intro m hm
    rw [pow_succ, PowerSeries.coeff_mul]
    refine Subalgebra.sum_mem _ (fun x hx => ?_)
    have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    exact Subalgebra.mul_mem _ (ih x.1 (by omega)) (hP x.2 (by omega))

/-- `formalLog_exact38` with its witness exposed (same proof, same generic ring/derivation). -/
theorem rv_formalLog {R : Type*} [CommRing R] (d : Derivation ℤ R R) (A P : PowerSeries R)
    (hP : PowerSeries.constantCoeff P = 0)
    (h : A * (1 - P) = PowerSeries.mk (fun k => d (PowerSeries.coeff k P))) (k : ℕ) :
    (k.factorial : R) * PowerSeries.coeff k A =
      d (∑ j ∈ Finset.range k,
        ((k.factorial / (j + 1) : ℕ) : R) * PowerSeries.coeff k (P ^ (j + 1))) := by
  have h' : A * (1 - P) = serD d P := h
  rw [coeff_eq_sum_formalLog38 d A P hP h' k, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j + 1 ≤ k := Finset.mem_range.mp hj
  have hdvd : (j + 1) ∣ k.factorial := Nat.dvd_factorial (Nat.succ_pos j) hjk
  have hc : PowerSeries.coeff k (serD d (P ^ (j + 1))) =
      ((j + 1 : ℕ) : R) * PowerSeries.coeff k (P ^ j * serD d P) := by
    rw [serD_pow_succ, map_nsmul, nsmul_eq_mul]
  rw [coeff_serD] at hc
  have hk : (k.factorial : R) = ((k.factorial / (j + 1) : ℕ) : R) * ((j + 1 : ℕ) : R) := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel hdvd]
  rw [hk, mul_assoc, ← hc]
  have : ((k.factorial / (j + 1) : ℕ) : R) * d (PowerSeries.coeff k (P ^ (j + 1))) =
      d (((k.factorial / (j + 1) : ℕ) : R) * PowerSeries.coeff k (P ^ (j + 1))) := by
    rw [← nsmul_eq_mul, ← nsmul_eq_mul, map_nsmul]
  rw [this]

/-- The k-th coefficient of `u Γ + ū Δ`, times k!, is the spatial derivative of a jet polynomial of order
    at most N-1, when k ≤ N+1. -/
theorem rv_formal (k N : ℕ) (hN : 1 ≤ N) (hkN : k ≤ N + 1) :
    ∃ ℓ : Poly, ℓ ∈ NlsGge.Atomic.M003.jetAlg (N - 1) ∧
      (k.factorial : Poly) * (MvPolynomial.X (false, 0) * p k +
        MvPolynomial.X (true, 0) * ((-1 : Poly) ^ k * riccatiSwap38 (p k))) = spatialD ℓ := by
  have hP0 : PowerSeries.constantCoeff (riccatiGamma38 * riccatiDelta38) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mul]
    simp [riccatiGamma38, riccatiDelta38, rv_p_zero]
  have hA := rv_formalLog spatialD
    (PowerSeries.C (MvPolynomial.X (false, 0)) * riccatiGamma38 +
      PowerSeries.C (MvPolynomial.X (true, 0)) * riccatiDelta38)
    (riccatiGamma38 * riccatiDelta38) hP0 riccatiWronskian38 k
  refine ⟨_, ?_, Eq.trans ?_ hA⟩
  swap
  · congr 1
    rw [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, riccatiGamma38,
      riccatiDelta38, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  refine Subalgebra.sum_mem _ (fun j _ => Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _) ?_)
  exact rv_coeff_pow_mem (k := k) _ (fun m hm => rv_coeffP_mem (by omega)) (j + 1) k le_rfl

/-! ### Analytic part -/

theorem rv_integral_cover_eq_fourier0 (u : PhysicalL2) :
    ∫ s in (0 : ℝ)..1, coverRep38 u s = physicalFourier u 0 := by
  unfold physicalFourier
  rw [fourierCoeff_eq_intervalIntegral (u : AddCircle (1 : ℝ) → ℂ) 0 0]
  simp only [zero_add, div_one, one_smul]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [coverRep38_ae_phys u] with s hs _
  rw [hs]
  simp

theorem rv_integral_weakDerivative (w : PhysicalL2) (hw : physicalSobolev 1 w) :
    ∫ s in (0 : ℝ)..1, coverRep38 (weakDerivative w) s = 0 := by
  rw [rv_integral_cover_eq_fourier0, physicalFourier_weakDerivative w hw 0]
  simp

theorem rv_integral_spatialD_eval {N : ℕ} (hN : 1 ≤ N) (φ : SobolevC N) (ℓ : Poly)
    (hℓ : ℓ ∈ NlsGge.Atomic.M003.jetAlg (N - 1)) :
    ∫ x in (0 : ℝ)..1,
      polynomialEvaluation (fun v => coverRep38 (NlsGge.ThirdConsultation.M.hierarchyJetL2 φ v) x)
        (spatialD ℓ) = 0 := by
  obtain ⟨w, hw, -, hd⟩ := NlsGge.ThirdConsultation.M.polyRealised_of_jetOrd
    (NlsGge.ThirdConsultation.M.hierarchyJetL2 φ) (N - 1)
    (fun v hv => NlsGge.ThirdConsultation.M.hierarchyJetL2_sobolev φ v (by omega))
    (fun v _ => NlsGge.ThirdConsultation.M.hierarchyJetL2_deriv φ v)
    ℓ (NlsGge.Atomic.M003.jetOrd_of_mem_jetAlg hℓ)
  rw [← rv_integral_weakDerivative w hw]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hd] with x hx _
  exact hx.symm

theorem rv_jet_swap {N : ℕ} (φ : SobolevC N) (v : Jet) :
    NlsGge.ThirdConsultation.M.hierarchyJetL2 ((φ.2, φ.1) : SobolevC N) v =
      NlsGge.ThirdConsultation.M.hierarchyJetL2 φ (!v.1, v.2) := by
  rcases v with ⟨b, j⟩
  cases b <;> simp [NlsGge.ThirdConsultation.M.hierarchyJetL2, toPotPair]

theorem rv_jet_false0 {N : ℕ} (φ : SobolevC N) :
    NlsGge.ThirdConsultation.M.hierarchyJetL2 φ (false, 0) = (toPotPair φ).1 := rfl

theorem rv_jet_true0 {N : ℕ} (φ : SobolevC N) :
    NlsGge.ThirdConsultation.M.hierarchyJetL2 φ (true, 0) = (toPotPair φ).2 := rfl

theorem rv_eval_swap (f : Jet → ℂ) (P : Poly) :
    polynomialEvaluation f (riccatiSwap38 P) =
      polynomialEvaluation (fun v => f (!v.1, v.2)) P := by
  simp only [polynomialEvaluation, riccatiSwap38, MvPolynomial.coe_eval₂Hom]
  exact MvPolynomial.eval₂_rename _ _ _ _

theorem rv_right_eq {N : ℕ} (φ : SobolevC N) (k : ℕ) :
    NlsGge.ThirdConsultation.KSPSRiccati.right φ k =
      ((-1 : ℂ) ^ (k + 1)) •
        NlsGge.ThirdConsultation.KSPSRiccati.left ((φ.2, φ.1) : SobolevC N) k := rfl

theorem rv_right_cover {N : ℕ} (hN : 1 ≤ N) (φ : SobolevC N) (k : ℕ)
    (hk1 : 1 ≤ k) (hkN : k ≤ N + 1) :
    ∀ᵐ x : ℝ, coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.right φ k) x =
      (-1 : ℂ) ^ (k + 1) *
        polynomialEvaluation (fun v => coverRep38 (NlsGge.ThirdConsultation.M.hierarchyJetL2 φ v) x)
          (riccatiSwap38 (p k)) := by
  filter_upwards [coverRep38_smul_ae ((-1 : ℂ) ^ (k + 1))
      (NlsGge.ThirdConsultation.KSPSRiccati.left ((φ.2, φ.1) : SobolevC N) k),
    NlsGge.ThirdConsultation.M.left_cover_eq_polyEval hN ((φ.2, φ.1) : SobolevC N) k hk1 hkN]
    with x h1 h2
  rw [rv_right_eq, h1, h2, rv_eval_swap]
  simp only [rv_jet_swap]

theorem rv_prod_intervalIntegrable (f g : PhysicalL2) :
    IntervalIntegrable (fun t : ℝ => coverRep38 f t * coverRep38 g t) volume 0 1 :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).2
    (NlsGge.ThirdConsultation.KSPSSupport.h150_prod_integrableOn f g)

/-- Left integral in cover form. -/
theorem rv_left_cover_integral {N : ℕ} (φ : SobolevC N) (k : ℕ) :
    integralRiccatiLeft φ k =
      ∫ x in (0 : ℝ)..1, coverRep38 (toPotPair φ).1 x * coverRep38 (riccatiLeft φ k) x := by
  unfold integralRiccatiLeft
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [coverRep38_ae_phys (toPotPair φ).1, coverRep38_ae_phys (riccatiLeft φ k)]
    with x h1 h2 _
  rw [h1, h2]

/-- Main case 2 ≤ k ≤ N+1 (so N ≥ 1), with the right integral written out literally. -/
theorem rv_vanishing_ge_two {N : ℕ} (φ : SobolevC N) (k : ℕ) (hk2 : 2 ≤ k) (hkN : k ≤ N + 1) :
    integralRiccatiLeft φ k =
      ∫ x in (0 : ℝ)..1,
        coverRep38 (toPotPair φ).2 x *
          coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.right φ k) x := by
  have hN : 1 ≤ N := by omega
  obtain ⟨ℓ, hℓ, hid⟩ := rv_formal k N hN hkN
  have hzero := rv_integral_spatialD_eval hN φ ℓ hℓ
  have hfac : ((k.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  rw [← sub_eq_zero, rv_left_cover_integral,
    ← intervalIntegral.integral_sub (rv_prod_intervalIntegrable _ _) (rv_prod_intervalIntegrable _ _)]
  calc _ = ∫ x in (0 : ℝ)..1, ((k.factorial : ℕ) : ℂ)⁻¹ *
        polynomialEvaluation
          (fun v => coverRep38 (NlsGge.ThirdConsultation.M.hierarchyJetL2 φ v) x) (spatialD ℓ) := by
        refine intervalIntegral.integral_congr_ae ?_
        filter_upwards [NlsGge.ThirdConsultation.M.left_cover_eq_polyEval hN φ k (by omega) hkN,
          rv_right_cover hN φ k (by omega) hkN] with x hL hR _
        have hL' : coverRep38 (riccatiLeft φ k) x =
            polynomialEvaluation
              (fun v => coverRep38 (NlsGge.ThirdConsultation.M.hierarchyJetL2 φ v) x) (p k) := hL
        rw [hL', hR, ← hid, map_mul, map_natCast]
        simp only [map_add, map_mul, map_pow, map_neg, map_one, polynomialEvaluation_X,
          rv_jet_false0, rv_jet_true0]
        field_simp
        ring
    _ = 0 := by rw [intervalIntegral.integral_const_mul, hzero, mul_zero]

/-- Boundary case k = 1 (every N, including N = 0): both sides are minus the bilinear mass. -/
theorem rv_vanishing_one {N : ℕ} (φ : SobolevC N) :
    integralRiccatiLeft φ 1 =
      ∫ x in (0 : ℝ)..1,
        coverRep38 (toPotPair φ).2 x *
          coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.right φ 1) x := by
  have eL : riccatiLeft φ 1 = -(toPotPair φ).2 := by
    show wkbR (toPotPair φ) 1 = _
    exact wkbR_one _
  have eL' : NlsGge.ThirdConsultation.KSPSRiccati.left ((φ.2, φ.1) : SobolevC N) 1 =
      -(toPotPair φ).1 := by
    show wkbR (toPotPair ((φ.2, φ.1) : SobolevC N)) 1 = _
    exact wkbR_one _
  have eR : NlsGge.ThirdConsultation.KSPSRiccati.right φ 1 =
      ((-1 : ℂ) ^ (1 + 1)) • (-(toPotPair φ).1) := by
    rw [rv_right_eq, eL']
  rw [rv_left_cover_integral]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [coverRep38_neg_ae (toPotPair φ).2,
    coverRep38_smul_ae ((-1 : ℂ) ^ (1 + 1)) (-(toPotPair φ).1),
    coverRep38_neg_ae (toPotPair φ).1] with x h3 h4 h5 _
  rw [eL, h3, eR, h4, h5]
  ring

end
end NlsGge.ThirdConsultation.KSPSWKB
