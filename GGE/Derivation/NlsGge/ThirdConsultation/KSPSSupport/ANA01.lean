import Mathlib
import NlsGge.ThirdConsultation.Sobolev.Round5
import NlsGge.ThirdConsultation.KSPS.Round5
import NlsGge.ThirdConsultation.G1.Round5
import NlsGge.ThirdConsultation.G1.NormCalculus
import NlsGge.ThirdConsultation.G1.ProductBounds
import NlsGge.ThirdConsultation.G1.WkbStructure
import NlsGge.ThirdConsultation.G1.Wkb035A
import NlsGge.Atomic.G1.G1034
import NlsGge.ThirdConsultation.KSPSRiccatiHost
import NlsGge.ThirdConsultation.KSPSSupport
import NlsGge.ThirdConsultation.KSPSSupport.CORE01

/- KSPS-010 ANA01 (proof development, AUTHOR; not reviewed).
   S8  coverRep38_memLp_Icc: the period-one representative of an L2 field is in L2 of the unit interval.
   Fixed-lam L2 facts for the packet clause C6 (non-uniform): forcing, a1, a2 are in L2([0,1]) for lam ≠ 0,
   via continuity of the prefix integrals on [0,1] (bounded, so the phase factor is bounded there).
   The a.e. identity forcing = coverRep(coef_{N+1}) + (2 i lam)^{-1} a1 + (2 i lam)^{-2} a2 is algebra.
   Uniform bounds (S11, S12) are NOT here. -/
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.GK38 NlsGge.Atomic.Common
open NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPSSupport
noncomputable section

/-- S8: the period-one representative of an L2 field is in L2 of the unit interval. -/
theorem coverRep38_memLp_Icc (f : PhysicalL2) :
    MemLp (coverRep38 f) 2 KSPSRiccati.intervalMeasure := by
  unfold KSPSRiccati.intervalMeasure
  rw [memLp_two_iff_integrable_sq_norm (stronglyMeasurable_coverRep38 f).aestronglyMeasurable]
  have h := intervalIntegrable_coverRep38_sq_one f
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)] at h
  exact h

/-- The product of two period-one representatives is integrable on [0,1]. -/
theorem h150_prod_integrableOn (f g : PhysicalL2) :
    IntegrableOn (fun t : ℝ => coverRep38 f t * coverRep38 g t) (Set.Icc (0 : ℝ) 1) := by
  have hf := coverRep38_memLp_Icc f
  have hg := coverRep38_memLp_Icc g
  unfold KSPSRiccati.intervalMeasure at hf hg
  exact hf.integrable_mul hg

/-- The primitive of a product of two representatives is continuous on [0,1]. -/
theorem h150_prim_continuousOn (f g : PhysicalL2) :
    ContinuousOn (fun x : ℝ => ∫ t in (0 : ℝ)..x, coverRep38 f t * coverRep38 g t)
      (Set.Icc (0 : ℝ) 1) := by
  have hint : IntegrableOn (fun t : ℝ => coverRep38 f t * coverRep38 g t) (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num)]
    exact h150_prod_integrableOn f g
  have h := intervalIntegral.continuousOn_primitive_interval hint
  rw [Set.uIcc_of_le (by norm_num)] at h
  exact h

/-- A bounded continuous multiplier on [0,1] preserves L2([0,1]). -/
theorem h150_memLp_mul_bdd (f g : ℝ → ℂ) (hf : MemLp f 2 KSPSRiccati.intervalMeasure)
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) 1)) :
    MemLp (fun x => g x * f x) 2 KSPSRiccati.intervalMeasure := by
  have hmeas : AEStronglyMeasurable g KSPSRiccati.intervalMeasure := by
    unfold KSPSRiccati.intervalMeasure
    exact hg.aestronglyMeasurable measurableSet_Icc
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  have hbd : ∀ᵐ x ∂KSPSRiccati.intervalMeasure, ‖g x‖ ≤ C := by
    unfold KSPSRiccati.intervalMeasure
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact hC x hx
  have hgt : MemLp g ⊤ KSPSRiccati.intervalMeasure := memLp_top_of_bound hmeas C hbd
  exact hgt.mul hf

/-- The phase factor is continuous on [0,1] (exponential of a continuous function). -/
theorem h150_phase_continuousOn {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : ℂ) :
    ContinuousOn (KSPSRiccati.phaseFactor φ b lam) (Set.Icc (0 : ℝ) 1) := by
  unfold KSPSRiccati.phaseFactor KSPSRiccati.prefix
  apply ContinuousOn.cexp
  apply ContinuousOn.mul continuousOn_const
  apply continuousOn_finset_sum
  intro k _
  apply ContinuousOn.mul continuousOn_const
  exact h150_prim_continuousOn (KSPSRiccati.sidePotential φ b) (KSPSRiccati.coefficient φ b k)

/-- The forcing is in L2([0,1]) for every lam (fixed lam; no uniformity). -/
theorem h150_forcing_memLp {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : ℂ) :
    MemLp (KSPSRiccati.forcing φ b lam) 2 KSPSRiccati.intervalMeasure := by
  have hg : ContinuousOn (fun x : ℝ => (2 * Complex.I * lam) ^ N * KSPSRiccati.phaseFactor φ b lam x)
      (Set.Icc (0 : ℝ) 1) :=
    continuousOn_const.mul (h150_phase_continuousOn φ b lam)
  unfold KSPSRiccati.forcing
  exact h150_memLp_mul_bdd (fun x => coverRep38 (KSPSRiccati.rho φ b lam) x) _
    (coverRep38_memLp_Icc _) hg

/-- The mass prefix is continuous on [0,1]. -/
theorem h150_massPrefix_continuousOn {N : ℕ} (φ : SobolevC N) (σ : ℂ) :
    ContinuousOn (fun x : ℝ => σ * KSPSRiccati.massPrefix φ x) (Set.Icc (0 : ℝ) 1) := by
  apply continuousOn_const.mul
  unfold KSPSRiccati.massPrefix
  exact h150_prim_continuousOn (toPotPair φ).1 (toPotPair φ).2

/-- a1 is in L2([0,1]) for each side (fixed data). -/
theorem h150_a1_memLp {N : ℕ} (φ : SobolevC N) (b : Bool) :
    MemLp (KSPSRiccati.a1 φ b) 2 KSPSRiccati.intervalMeasure := by
  have hq := coverRep38_memLp_Icc (KSPSRiccati.quadratic φ b (N + 1))
  have hc := coverRep38_memLp_Icc (KSPSRiccati.coefficient φ b (N + 1))
  have ht := h150_memLp_mul_bdd (fun x => coverRep38 (KSPSRiccati.coefficient φ b (N + 1)) x) _ hc
    (h150_massPrefix_continuousOn φ (if b then (1 : ℂ) else -1))
  have ht2 : MemLp (fun x => (if b then (1 : ℂ) else -1) *
      coverRep38 (KSPSRiccati.coefficient φ b (N + 1)) x * KSPSRiccati.massPrefix φ x) 2
      KSPSRiccati.intervalMeasure := by
    convert ht using 1
    funext x
    ring
  unfold KSPSRiccati.a1
  exact hq.add ht2

/-- a2 is in L2([0,1]) for each fixed lam ≠ 0 (finite combination of L2 functions). -/
theorem h150_a2_memLp {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : ℂ) :
    MemLp (KSPSRiccati.a2 φ b lam) 2 KSPSRiccati.intervalMeasure := by
  unfold KSPSRiccati.a2
  exact ((((h150_forcing_memLp φ b lam).sub
    (coverRep38_memLp_Icc (KSPSRiccati.coefficient φ b (N + 1)))).sub
    ((h150_a1_memLp φ b).const_mul _))).const_mul _

/-- The a.e. (in fact everywhere) expansion of the forcing through a1 and a2 for lam ≠ 0. -/
theorem h150_forcing_ae {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : ℂ) (hlam : lam ≠ 0) :
    KSPSRiccati.forcing φ b lam =ᵐ[KSPSRiccati.intervalMeasure] fun x =>
      coverRep38 (KSPSRiccati.coefficient φ b (N + 1)) x +
        (2 * Complex.I * lam)⁻¹ * KSPSRiccati.a1 φ b x +
        ((2 * Complex.I * lam) ^ 2)⁻¹ * KSPSRiccati.a2 φ b lam x := by
  have hne : (2 * Complex.I * lam) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hlam
  have hk : ((2 * Complex.I * lam) ^ 2)⁻¹ * (2 * Complex.I * lam) ^ 2 = 1 :=
    inv_mul_cancel₀ (pow_ne_zero 2 hne)
  refine Filter.Eventually.of_forall (fun x => ?_)
  unfold KSPSRiccati.a2
  beta_reduce
  linear_combination (-(KSPSRiccati.forcing φ b lam x - coverRep38 (KSPSRiccati.coefficient φ b (N + 1)) x -
    (2 * Complex.I * lam)⁻¹ * KSPSRiccati.a1 φ b x)) * hk

/-- C6 (products): the partial sum is in H^1, so its self-product is in L2 (lam arbitrary). -/
theorem h150_C6_partial_productInL2 {N : ℕ} (hN : 1 ≤ N) (φ : SobolevC N) (b : Bool) (lam : ℂ) :
    productInL2 (KSPSRiccati.«partial» φ b lam) (KSPSRiccati.«partial» φ b lam) :=
  productInL2_of_H1 _ _ (partial_H1 φ b lam hN)

/-- C6 (products): the side potential times the self-product of the partial sum is in L2. -/
theorem h150_C6_side_productInL2 {N : ℕ} (hN : 1 ≤ N) (φ : SobolevC N) (b : Bool) (lam : ℂ) :
    productInL2 (KSPSRiccati.sidePotential φ b)
      (physicalProduct (KSPSRiccati.«partial» φ b lam) (KSPSRiccati.«partial» φ b lam)) :=
  productInL2_of_H1 _ _ (h150_side_H1 N hN φ b)

end
end NlsGge.ThirdConsultation.KSPSSupport
