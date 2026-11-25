import Mathlib
import NlsGge.Atomic.G1.G1036
import NlsGge.Atomic.G1.G1037Host
import NlsGge.ThirdConsultation.G1.Round6
import NlsGge.Hierarchy.RiccatiUnitPeriodIntervalToPhysicalHaar

/- G1-037 SUP02 (proof development, AUTHOR; not reviewed). Target NlsGge/Atomic/G1/G1037Sup2.lean.
   Supporting module (statements M3 of G1037_STOP.md, proof development): the exact phase identity
   wkbPhase N z phi 1 = exp (wkbSigma N z phi), i.e. -i z + i int_0^1 phi_1 alpha_N = sigma_N.
   Steps: (a) alpha_N(1) = alpha_N(0) (1-periodicity of the Fourier representative);
   (b) <star f, g> = int_circle f g (L2 inner product); (c) interval integral of covers = circle integral
   (RiccatiUnitPeriodIntervalToPhysicalHaar); (d) int_0^1 phi_1 alpha_N is the finite sum of the pairings of phi_1
   with wkbR n, through the a.e. identification fourierRepresentative = coverRep38 for H1 classes (G1036 S1b)
   and linearity of the inner product on the finite sum wkbPartial;
   (e) wkbR 1 = -phi_2, hierarchyHamiltonian 1 = int phi_1 phi_2, hierarchyHamiltonian k = int phi_1 wkbR k for k >= 2. -/
set_option autoImplicit false
open Classical Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open scoped BigOperators Matrix

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g37_alpha_one (N : ℕ) (z : ℂ) (φ : PotPair) : wkbAlpha N z φ 1 = wkbAlpha N z φ 0 := by
  unfold wkbAlpha fourierRepresentative
  congr 2
  refine tsum_congr (fun n => ?_)
  have h : -2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (((1 : ℝ)) : ℂ) =
      ((-n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]
  simp

theorem g37_inner_star (f g : PhysicalL2) :
    inner ℂ (star f) g = ∫ x : PhysicalCircle, f x * g x ∂spatialMeasure := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MeasureTheory.Lp.coeFn_star f] with a h2
  rw [RCLike.inner_apply, h2]
  simp [mul_comm]

theorem g37_interval_circle (f g : PhysicalL2) :
    ∫ s in (0 : ℝ)..1, coverRep38 f s * coverRep38 g s =
      ∫ x : PhysicalCircle, f x * g x ∂spatialMeasure := by
  calc ∫ s in (0 : ℝ)..1, coverRep38 f s * coverRep38 g s
      = ∫ s in (0 : ℝ)..1, (fun x : PhysicalCircle => f x * g x) (s : PhysicalCircle) := by
        refine intervalIntegral.integral_congr_ae ?_
        filter_upwards [coverRep38_ae_phys f, coverRep38_ae_phys g] with s h1 h2 _
        simp only [h1, h2]
    _ = _ := NlsGge.HierarchyRiccati.unitIntervalIntegral_lift_eq_spatialHaar (E := ℂ)
          (fun x : PhysicalCircle => f x * g x)

theorem g37_phase_integral (N : ℕ) (hN : 1 ≤ N) (z : ℂ) (hz : 1 ≤ ‖z‖) (φ : PotPair)
    (hφ : pairSobolev (N : ℝ) φ) :
    Complex.I * ∫ s in (0 : ℝ)..1, potRepFst38 φ s * wkbAlpha N z φ s =
      ∑ n ∈ Finset.Icc 1 N, ((2 * Complex.I * z) ^ n)⁻¹ *
        ∫ x : PhysicalCircle, φ.1 x * wkbR φ n x ∂spatialMeasure := by
  obtain ⟨K, hK, p, h⟩ := g36_s6_partial_H1 N hN
  have hP : physicalSobolev 1 (wkbPartial N z φ) := (h φ hφ z hz).1
  have hae := g36_s1b_fourierRepresentative_ae (wkbPartial N z φ) hP
  have h1 : ∫ s in (0 : ℝ)..1, potRepFst38 φ s * wkbAlpha N z φ s =
      -Complex.I * ∫ x : PhysicalCircle, φ.1 x * (wkbPartial N z φ) x ∂spatialMeasure := by
    rw [← g37_interval_circle φ.1 (wkbPartial N z φ), ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with s hs _
    unfold wkbAlpha potRepFst38
    rw [hs]
    ring
  have e : wkbPartial N z φ =
      ∑ n ∈ Finset.Icc 1 N, ((2 * Complex.I * z) ^ n)⁻¹ • wkbR φ n := rfl
  rw [h1, ← g37_inner_star, e, inner_sum]
  simp only [inner_smul_right, g37_inner_star]
  rw [← mul_assoc, show Complex.I * -Complex.I = 1 by simp, one_mul]

theorem g37_phase_eq (N : ℕ) (hN : 1 ≤ N) (z : ℂ) (hz : 1 ≤ ‖z‖) (φ : PotPair)
    (hφ : pairSobolev (N : ℝ) φ) :
    wkbPhase N z φ 1 = Complex.exp (wkbSigma N z φ) := by
  unfold wkbPhase
  congr 1
  rw [g37_phase_integral N hN z hz φ hφ]
  have hs : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have h1 : ∫ x : PhysicalCircle, φ.1 x * wkbR φ 1 x ∂spatialMeasure = -hierarchyHamiltonian 1 φ := by
    rw [wkbR_one, ← g37_inner_star, inner_neg_right, g37_inner_star]
    simp [hierarchyHamiltonian]
  have hk : ∀ k ∈ Finset.Icc 2 N,
      ((2 * Complex.I * z) ^ k)⁻¹ * ∫ x : PhysicalCircle, φ.1 x * wkbR φ k x ∂spatialMeasure =
        hierarchyHamiltonian k φ / (2 * Complex.I * z) ^ k := by
    intro k hk
    have hk2 : k ≠ 1 := by
      have := (Finset.mem_Icc.1 hk).1
      omega
    rw [div_eq_inv_mul]
    unfold hierarchyHamiltonian
    rw [if_neg hk2]
  rw [hs, Finset.sum_insert (by simp), Finset.sum_congr rfl hk, h1]
  unfold wkbSigma
  simp only [Complex.ofReal_one, mul_one, pow_one]
  rw [div_eq_inv_mul]
  ring

end
end NlsGge.GKDefinitionDesign
