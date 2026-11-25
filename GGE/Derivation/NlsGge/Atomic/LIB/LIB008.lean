import NlsGge.Birkhoff.F01Determinant38d
import NlsGge.Birkhoff.W08Compact38
import NlsGge.Atomic.LIB.LIB021
import NlsGge.Atomic.LIB.LIB022
import NlsGge.Atomic.PhysicalSobolev
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
noncomputable section

open Filter Topology

namespace NlsGge.Atomic.LIB008

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff

/-- The identity on Fourier coefficients, regarded as the continuous inclusion
from the repository's actual weighted `h^s` Hilbert carrier into `h^t`. -/
def sobolevSequenceInclusion (s t : ℝ) (hst : t ≤ s) :
    SobolevCarrier38 s →L[ℝ] SobolevCarrier38 t := carrierIncl38 hst

theorem sobolevSequenceInclusion_apply (s t : ℝ) (hst : t ≤ s)
    (x : SobolevCarrier38 s) (n : ℤ) :
    carrierCoe38 t (sobolevSequenceInclusion s t hst x) n = carrierCoe38 s x n := by
  exact congrFun (carrierCoe38_incl38 hst x) n

theorem sobolevSequenceInclusion_norm_le (s t : ℝ) (hst : t ≤ s)
    (x : SobolevCarrier38 s) :
    ‖sobolevSequenceInclusion s t hst x‖ ≤ ‖x‖ := by
  have hsource := carrier_hasSum_norm_sq38 s x
  have htarget := carrier_hasSum_norm_sq38 t (sobolevSequenceInclusion s t hst x)
  have hsq : ‖sobolevSequenceInclusion s t hst x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    refine hasSum_le (fun n => ?_) htarget hsource
    rw [sobolevSequenceInclusion_apply]
    exact mul_le_mul_of_nonneg_right (sobolevModeWeight_mono hst n) (sq_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq

/-- The symmetric finite-frequency truncation on the target Sobolev carrier. -/
def sobolevSequenceProjection (t : ℝ) (N : ℕ) :
    SobolevCarrier38 t →L[ℝ] SobolevCarrier38 t := projC38 t N

private theorem finiteDimensional_range_sobolevProjection (t : ℝ) (N : ℕ) :
    FiniteDimensional ℝ (LinearMap.range (projLin38 t N)) := by
  let g : SobolevCarrier38 t →ₗ[ℝ] (↥(symmetricModes N) → ℂ) :=
    { toFun := fun x n => carrierCoe38 t x n
      map_add' := fun x y => rfl
      map_smul' := fun c x => by
        funext n
        simp [Complex.real_smul]
        rfl }
  refine Module.Finite.of_injective (g.domRestrict (LinearMap.range (projLin38 t N))) ?_
  intro x y hxy
  apply Subtype.ext
  apply carrierExt38
  funext n
  obtain ⟨x', hx'⟩ := x.2
  obtain ⟨y', hy'⟩ := y.2
  by_cases hn : n ∈ symmetricModes N
  · exact congrFun hxy ⟨n, hn⟩
  · have e1 : carrierCoe38 t x.1 n = 0 := by
      rw [← hx']
      show carrierCoe38 t (projC38 t N x') n = 0
      rw [carrierCoe38_projC38, if_neg hn]
    have e2 : carrierCoe38 t y.1 n = 0 := by
      rw [← hy']
      show carrierCoe38 t (projC38 t N y') n = 0
      rw [carrierCoe38_projC38, if_neg hn]
    rw [e1, e2]

/-- Uniform coefficient tail multiplier in the exact scale dictated by the
weight comparison. -/
def sobolevTailFactor (s t : ℝ) (N : ℕ) : ℝ :=
  ((N : ℝ) + 1) ^ (t - s)

theorem sobolevTailFactor_nonneg (s t : ℝ) (N : ℕ) :
    0 ≤ sobolevTailFactor s t N := by
  apply Real.rpow_nonneg
  positivity

theorem tendsto_sobolevTailFactor {s t : ℝ} (hst : t < s) :
    Tendsto (sobolevTailFactor s t) atTop (𝓝 0) := by
  have hshift : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hst)).comp hshift
  have heq : (fun N : ℕ => ((N : ℝ) + 1) ^ (t - s)) =
      (fun N : ℕ => ((N : ℝ) + 1) ^ (-(s - t))) := by
    funext N
    congr 1
    ring
  change Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ (t - s)) atTop (𝓝 0)
  rw [heq]
  exact h

private theorem sobolev_tail_weight_le {s t : ℝ} (hst : t < s) (N : ℕ)
    {n : ℤ} (hn : n ∉ symmetricModes N) :
    sobolevModeWeight t n ≤
      sobolevTailFactor s t N ^ 2 * sobolevModeWeight s n := by
  have hnZ : (N : ℤ) + 1 ≤ |n| := by
    have hnot : ¬ (-(N : ℤ) ≤ n ∧ n ≤ (N : ℤ)) := by
      simpa [symmetricModes, Finset.mem_Icc] using hn
    rcases not_and_or.mp hnot with hlow | hhigh
    · have : n < -(N : ℤ) := by omega
      rw [abs_of_neg (by omega)]
      omega
    · have : (N : ℤ) < n := by omega
      rw [abs_of_pos (by omega)]
      omega
  have hnR : (N : ℝ) + 1 ≤ |(n : ℝ)| := by exact_mod_cast hnZ
  have hbr : |(n : ℝ)| ≤ japaneseBracket n := by
    unfold japaneseBracket
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_abs (n : ℝ)]
  have hbase : 0 < (N : ℝ) + 1 := by positivity
  have hbase_le : (N : ℝ) + 1 ≤ japaneseBracket n := hnR.trans hbr
  have hpow : japaneseBracket n ^ (2 * (t - s)) ≤ ((N : ℝ) + 1) ^ (2 * (t - s)) :=
    Real.rpow_le_rpow_of_nonpos hbase hbase_le (by linarith)
  have hweight : sobolevModeWeight t n =
      japaneseBracket n ^ (2 * (t - s)) * sobolevModeWeight s n := by
    unfold sobolevModeWeight
    calc
      japaneseBracket n ^ (2 * t) =
          japaneseBracket n ^ (2 * (t - s) + 2 * s) := by congr 1 <;> ring
      _ = japaneseBracket n ^ (2 * (t - s)) * japaneseBracket n ^ (2 * s) :=
        Real.rpow_add (japaneseBracket_pos n) _ _
  have hfactor : sobolevTailFactor s t N ^ 2 = ((N : ℝ) + 1) ^ (2 * (t - s)) := by
    unfold sobolevTailFactor
    have hbase : 0 ≤ (N : ℝ) + 1 := by positivity
    calc
      (((N : ℝ) + 1) ^ (t - s)) ^ 2 =
          ((N : ℝ) + 1) ^ ((t - s) * 2) := by
        calc
          (((N : ℝ) + 1) ^ (t - s)) ^ 2 =
              (((N : ℝ) + 1) ^ (t - s)) ^ (2 : ℝ) :=
                (Real.rpow_natCast _ _).symm
          _ = ((N : ℝ) + 1) ^ ((t - s) * 2) := (Real.rpow_mul hbase _ _).symm
      _ = ((N : ℝ) + 1) ^ (2 * (t - s)) := by rw [mul_comm]
  rw [hweight, hfactor]
  exact mul_le_mul_of_nonneg_right hpow (sobolevModeWeight_pos s n).le

/-- The part of the inclusion discarded by a symmetric Fourier cutoff has the
explicit operator-norm estimate from the packet. -/
theorem sobolevSequenceInclusion_tail_norm_le {s t : ℝ} (hst : t < s)
    (N : ℕ) :
    ‖sobolevSequenceInclusion s t hst.le -
      (sobolevSequenceProjection t N).comp (sobolevSequenceInclusion s t hst.le)‖ ≤
        sobolevTailFactor s t N := by
  refine ContinuousLinearMap.opNorm_le_bound _ (sobolevTailFactor_nonneg s t N) (fun x => ?_)
  let R : SobolevCarrier38 t :=
    (sobolevSequenceInclusion s t hst.le -
      (sobolevSequenceProjection t N).comp (sobolevSequenceInclusion s t hst.le)) x
  have hcoef (n : ℤ) :
      carrierCoe38 t R n = carrierCoe38 s x n -
        (if n ∈ symmetricModes N then carrierCoe38 s x n else 0) := by
    change carrierCoe38 t (sobolevSequenceInclusion s t hst.le x) n -
      carrierCoe38 t (projC38 t N (sobolevSequenceInclusion s t hst.le x)) n = _
    rw [carrierCoe38_projC38, sobolevSequenceInclusion_apply]
  have htarget := (carrier_hasSum_norm_sq38 t R).tsum_eq.symm
  have hsource := carrier_hasSum_norm_sq38 s x
  have hsumEq : (∑' n : ℤ, sobolevModeWeight t n *
      ‖carrierCoe38 s x n -
        (if n ∈ symmetricModes N then carrierCoe38 s x n else 0)‖ ^ 2) =
      ∑' n : ℤ, sobolevModeWeight t n * ‖carrierCoe38 t R n‖ ^ 2 := by
    apply tsum_congr
    intro n
    rw [hcoef n]
  have hsum : (∑' n : ℤ, sobolevModeWeight t n *
      ‖carrierCoe38 s x n -
        (if n ∈ symmetricModes N then carrierCoe38 s x n else 0)‖ ^ 2) ≤
      sobolevTailFactor s t N ^ 2 * ‖x‖ ^ 2 := by
    calc
      _ = ∑' n : ℤ, sobolevModeWeight t n * ‖carrierCoe38 t R n‖ ^ 2 := hsumEq
      _ ≤ sobolevTailFactor s t N ^ 2 *
          ∑' n : ℤ, sobolevModeWeight s n * ‖carrierCoe38 s x n‖ ^ 2 := by
        rw [← hsource.summable.tsum_mul_left (sobolevTailFactor s t N ^ 2)]
        refine Summable.tsum_le_tsum (fun n => ?_)
          (carrier_hasSum_norm_sq38 t R).summable
          (hsource.summable.mul_left (sobolevTailFactor s t N ^ 2))
        by_cases hn : n ∈ symmetricModes N
        · rw [hcoef, if_pos hn]
          simp only [sub_self, norm_zero]
          norm_num
          exact mul_nonneg (sq_nonneg (sobolevTailFactor s t N))
            (mul_nonneg (sobolevModeWeight_pos s n).le (sq_nonneg _))
        · rw [hcoef, if_neg hn, sub_zero]
          calc
            sobolevModeWeight t n * ‖carrierCoe38 s x n‖ ^ 2 ≤
                (sobolevTailFactor s t N ^ 2 * sobolevModeWeight s n) *
                  ‖carrierCoe38 s x n‖ ^ 2 :=
              mul_le_mul_of_nonneg_right (sobolev_tail_weight_le hst N hn) (sq_nonneg _)
            _ = sobolevTailFactor s t N ^ 2 *
                (sobolevModeWeight s n * ‖carrierCoe38 s x n‖ ^ 2) := by ring
      _ = sobolevTailFactor s t N ^ 2 * ‖x‖ ^ 2 := by
        rw [← hsource.tsum_eq]
  have hfactorSq : sobolevTailFactor s t N ^ 2 = ((N : ℝ) + 1) ^ (2 * (t - s)) := by
    unfold sobolevTailFactor
    have hbase : 0 ≤ (N : ℝ) + 1 := by positivity
    calc
      (((N : ℝ) + 1) ^ (t - s)) ^ 2 =
          ((N : ℝ) + 1) ^ ((t - s) * 2) := by
        calc
          (((N : ℝ) + 1) ^ (t - s)) ^ 2 =
              (((N : ℝ) + 1) ^ (t - s)) ^ (2 : ℝ) :=
                (Real.rpow_natCast _ _).symm
          _ = ((N : ℝ) + 1) ^ ((t - s) * 2) := (Real.rpow_mul hbase _ _).symm
      _ = ((N : ℝ) + 1) ^ (2 * (t - s)) := by rw [mul_comm]
  have hsq0 : ‖R‖ ^ 2 ≤ sobolevTailFactor s t N ^ 2 * ‖x‖ ^ 2 := by
    calc
      ‖R‖ ^ 2 = ∑' n : ℤ, sobolevModeWeight t n * ‖carrierCoe38 t R n‖ ^ 2 :=
        htarget
      _ ≤ sobolevTailFactor s t N ^ 2 * ‖x‖ ^ 2 := by
        calc
          _ = ∑' n : ℤ, sobolevModeWeight t n *
              ‖carrierCoe38 s x n -
                (if n ∈ symmetricModes N then carrierCoe38 s x n else 0)‖ ^ 2 := hsumEq.symm
          _ ≤ _ := hsum
  have hsq : ‖R‖ ^ 2 ≤ (sobolevTailFactor s t N * ‖x‖) ^ 2 := by
    rw [mul_pow]
    exact hsq0
  have hnonneg : 0 ≤ sobolevTailFactor s t N * ‖x‖ :=
    mul_nonneg (sobolevTailFactor_nonneg s t N) (norm_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _) hnonneg).1 hsq

private theorem compact_sobolevSequenceApproximation {s t : ℝ}
    (hst : t ≤ s) (N : ℕ) :
    IsCompactOperator ((sobolevSequenceProjection t N).comp
      (sobolevSequenceInclusion s t hst)) := by
  let T := (sobolevSequenceProjection t N).comp (sobolevSequenceInclusion s t hst)
  letI : FiniteDimensional ℝ (LinearMap.range (projLin38 t N)) :=
    finiteDimensional_range_projC38_W08 t N
  let g : SobolevCarrier38 s →L[ℝ] LinearMap.range (projLin38 t N) :=
    T.codRestrict (LinearMap.range (projLin38 t N))
      (fun x => ⟨sobolevSequenceInclusion s t hst x, rfl⟩)
  have h1 : IsCompactOperator (LinearMap.range (projLin38 t N)).subtypeL :=
    isCompactOperator_of_locallyCompactSpace_rng _
  change IsCompactOperator ((LinearMap.range (projLin38 t N)).subtypeL.comp g)
  exact h1.comp_clm g

theorem sobolevSequenceInclusion_compact {s t : ℝ} (hst : t < s) :
    IsCompactOperator (sobolevSequenceInclusion s t hst.le) := by
  have hlim : Tendsto (fun N : ℕ => (sobolevSequenceProjection t N).comp
      (sobolevSequenceInclusion s t hst.le)) atTop
      (𝓝 (sobolevSequenceInclusion s t hst.le)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_)
      (tendsto_sobolevTailFactor hst)
    simpa only [norm_sub_rev] using sobolevSequenceInclusion_tail_norm_le hst N
  exact NlsGge.Atomic.compact_of_operatorNorm_limit
    (fun N => compact_sobolevSequenceApproximation hst.le N) hlim

/-! Physical transport through the proved completion Fourier equivalences. -/

open NlsGge.Atomic.Common

def physicalSobolevSequenceInclusion (s t : ℝ) (hst : t ≤ s) :
    PhysicalSobolev38 s →L[ℝ] PhysicalSobolev38 t :=
  (physicalSobolevFourierEquiv38 t).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((sobolevSequenceInclusion s t hst).comp
      (physicalSobolevFourierEquiv38 s).toContinuousLinearEquiv.toContinuousLinearMap)

def physicalSobolevSequenceProjection (t : ℝ) (N : ℕ) :
    PhysicalSobolev38 t →L[ℝ] PhysicalSobolev38 t :=
  (physicalSobolevFourierEquiv38 t).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((sobolevSequenceProjection t N).comp
      (physicalSobolevFourierEquiv38 t).toContinuousLinearEquiv.toContinuousLinearMap)

theorem physicalSobolevSequenceInclusion_fourier (s t : ℝ) (hst : t ≤ s)
    (x : PhysicalSobolev38 s) :
    physicalSobolevFourierEquiv38 t (physicalSobolevSequenceInclusion s t hst x) =
      sobolevSequenceInclusion s t hst (physicalSobolevFourierEquiv38 s x) := by
  simp [physicalSobolevSequenceInclusion]

theorem physicalSobolevSequenceProjection_fourier (t : ℝ) (N : ℕ)
    (x : PhysicalSobolev38 t) :
    physicalSobolevFourierEquiv38 t (physicalSobolevSequenceProjection t N x) =
      sobolevSequenceProjection t N (physicalSobolevFourierEquiv38 t x) := by
  simp [physicalSobolevSequenceProjection]

theorem physicalSobolevSequenceInclusion_norm_le (s t : ℝ) (hst : t ≤ s)
    (x : PhysicalSobolev38 s) :
    ‖physicalSobolevSequenceInclusion s t hst x‖ ≤ ‖x‖ := by
  calc
    ‖physicalSobolevSequenceInclusion s t hst x‖ =
        ‖physicalSobolevFourierEquiv38 t
          (physicalSobolevSequenceInclusion s t hst x)‖ :=
      ((physicalSobolevFourierEquiv38 t).norm_map _).symm
    _ = ‖sobolevSequenceInclusion s t hst (physicalSobolevFourierEquiv38 s x)‖ := by
      rw [physicalSobolevSequenceInclusion_fourier]
    _ ≤ ‖physicalSobolevFourierEquiv38 s x‖ :=
      sobolevSequenceInclusion_norm_le s t hst _
    _ = ‖x‖ := (physicalSobolevFourierEquiv38 s).norm_map x

theorem physicalSobolevSequenceInclusion_polynomial {s t : ℝ} (hst : t ≤ s)
    (p : PhysicalFourierPolynomial38 s) :
    physicalSobolevSequenceInclusion s t hst (p : PhysicalSobolev38 s) =
      (show PhysicalSobolev38 t from
        ((⟨p.toPhysicalSubmodule⟩ : PhysicalFourierPolynomial38 t) :
          PhysicalSobolev38 t)) := by
  let q : PhysicalFourierPolynomial38 t := ⟨p.toPhysicalSubmodule⟩
  apply (physicalSobolevFourierEquiv38 t).injective
  rw [physicalSobolevSequenceInclusion_fourier,
    physicalSobolevFourierEquiv38_coe, physicalSobolevFourierEquiv38_coe]
  apply carrierExt38
  funext n
  rw [sobolevSequenceInclusion_apply]
  simp [physicalFourierPolynomialToCarrier38, q]

theorem physicalSobolevSequenceInclusion_tail_norm_le {s t : ℝ} (hst : t < s)
    (N : ℕ) :
    ‖physicalSobolevSequenceInclusion s t hst.le -
      (physicalSobolevSequenceProjection t N).comp
        (physicalSobolevSequenceInclusion s t hst.le)‖ ≤ sobolevTailFactor s t N := by
  refine ContinuousLinearMap.opNorm_le_bound _ (sobolevTailFactor_nonneg s t N) (fun x => ?_)
  let R : PhysicalSobolev38 t :=
    (physicalSobolevSequenceInclusion s t hst.le -
      (physicalSobolevSequenceProjection t N).comp
        (physicalSobolevSequenceInclusion s t hst.le)) x
  have hfourier : physicalSobolevFourierEquiv38 t R =
      (sobolevSequenceInclusion s t hst.le -
        (sobolevSequenceProjection t N).comp (sobolevSequenceInclusion s t hst.le))
          (physicalSobolevFourierEquiv38 s x) := by
    simp [R, map_sub, physicalSobolevSequenceInclusion_fourier,
      physicalSobolevSequenceProjection_fourier]
  rw [← (physicalSobolevFourierEquiv38 t).norm_map, hfourier]
  calc
    ‖(sobolevSequenceInclusion s t hst.le -
        (sobolevSequenceProjection t N).comp (sobolevSequenceInclusion s t hst.le))
        (physicalSobolevFourierEquiv38 s x)‖ ≤
      ‖sobolevSequenceInclusion s t hst.le -
        (sobolevSequenceProjection t N).comp (sobolevSequenceInclusion s t hst.le)‖ *
          ‖physicalSobolevFourierEquiv38 s x‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ sobolevTailFactor s t N * ‖x‖ := by
      rw [(physicalSobolevFourierEquiv38 s).norm_map x]
      exact mul_le_mul_of_nonneg_right
        (sobolevSequenceInclusion_tail_norm_le hst N) (norm_nonneg _)

theorem physicalSobolevSequenceInclusion_compact {s t : ℝ} (hst : t < s) :
    IsCompactOperator (physicalSobolevSequenceInclusion s t hst.le) := by
  have hseq := sobolevSequenceInclusion_compact hst
  change IsCompactOperator
    ((physicalSobolevFourierEquiv38 t).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘
      ((sobolevSequenceInclusion s t hst.le).comp
        (physicalSobolevFourierEquiv38 s).toContinuousLinearEquiv.toContinuousLinearMap))
  exact (hseq.comp_clm (physicalSobolevFourierEquiv38 s).toContinuousLinearEquiv.toContinuousLinearMap).clm_comp
    (physicalSobolevFourierEquiv38 t).symm.toContinuousLinearEquiv.toContinuousLinearMap

end NlsGge.Atomic.LIB008
