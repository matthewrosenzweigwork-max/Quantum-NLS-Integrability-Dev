import Mathlib
import NlsGge.Atomic.LIB.LIB001
import NlsGge.Atomic.LIB.LIB002
import NlsGge.Analysis.H1Fourier
import NlsGge.Hierarchy.RiccatiPhysicalH1CanonicalAndDerivativeCLMAfterDerivativeClassLinearityPrerequisite

set_option autoImplicit false

/-! LIB-004 (proof development, AUTHOR; not self-reviewed; no acceptance claimed).
Implements the continuous period-one H1 representative packet of the GPT-6 Pro supplemental design
(`root/gpt6pro_supp/NLS_GGE_SUPPLEMENTAL_DESIGN_20261027.md`, section LIB-004) with the design's definitions and
statements; the representative is the accepted `physicalH1Continuous`, the physical graph norm (weight
`1 + (2 pi n)^2`) is kept distinct from the house Sobolev norm (weight `1 + n^2`). -/

open MeasureTheory Filter
open scoped ENNReal Topology
open NlsGge.Pilot NlsGge.Analysis

namespace NlsGge.Atomic.LIB004

noncomputable section

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

def graphWeight (n : ℤ) : ℝ :=
  1 + (2 * Real.pi * (n : ℝ)) ^ 2

noncomputable def h1GraphEnergy (u : PhysicalL2) : ℝ≥0∞ :=
  ∑' n : ℤ, ENNReal.ofReal (graphWeight n * ‖physicalFourier u n‖ ^ 2)

noncomputable def h1GraphNorm (u : PhysicalL2) : ℝ :=
  Real.sqrt (h1GraphEnergy u).toReal

noncomputable def embeddingEnergy : ℝ≥0∞ :=
  ∑' n : ℤ, (ENNReal.ofReal (graphWeight n))⁻¹

noncomputable def sobolevEmbeddingConstant : ℝ :=
  Real.sqrt embeddingEnergy.toReal

noncomputable def fourierTerm (u : PhysicalL2) (n : ℤ) :
    C(PhysicalCircle, ℂ) :=
  physicalFourier u n • fourier (T := (1 : ℝ)) n

noncomputable abbrev continuousRepresentative (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    C(PhysicalCircle, ℂ) := physicalH1Continuous u hu

/-! ### weights -/

theorem graphWeight_pos (n : ℤ) : 0 < graphWeight n := by
  unfold graphWeight
  positivity

theorem two_pi_sq_ge_one : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := by
  nlinarith [Real.pi_gt_three]

theorem graphWeight_ge (n : ℤ) : 1 + (n : ℝ) ^ 2 ≤ graphWeight n := by
  unfold graphWeight
  have e : (2 * Real.pi * (n : ℝ)) ^ 2 = (2 * Real.pi) ^ 2 * (n : ℝ) ^ 2 := by ring
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_right two_pi_sq_ge_one (sq_nonneg (n : ℝ))]

theorem graphWeight_le (n : ℤ) : graphWeight n ≤ (2 * Real.pi) ^ 2 * (1 + (n : ℝ) ^ 2) := by
  unfold graphWeight
  have e : (2 * Real.pi * (n : ℝ)) ^ 2 = (2 * Real.pi) ^ 2 * (n : ℝ) ^ 2 := by ring
  rw [e]
  nlinarith [two_pi_sq_ge_one]

theorem reciprocal_graphWeight_summable :
    Summable (fun n : ℤ => (graphWeight n)⁻¹) := by
  refine Summable.of_nonneg_of_le (fun n => inv_nonneg.mpr (graphWeight_pos n).le)
    (fun n => ?_) summable_reciprocal_bracket_square
  rw [one_div]
  exact inv_anti₀ (by positivity) (graphWeight_ge n)

/-! ### nonnegative extended-real sums -/

theorem tsum_ofReal_ne_top_iff {a : ℤ → ℝ} (ha : ∀ n, 0 ≤ a n) :
    ∑' n, ENNReal.ofReal (a n) ≠ ∞ ↔ Summable a := by
  constructor
  · intro h
    exact (ENNReal.summable_toReal h).congr (fun n => ENNReal.toReal_ofReal (ha n))
  · intro h
    rw [← ENNReal.ofReal_tsum_of_nonneg ha h]
    exact ENNReal.ofReal_ne_top

theorem tsum_ofReal_toReal {a : ℤ → ℝ} (ha : ∀ n, 0 ≤ a n) (h : Summable a) :
    (∑' n, ENNReal.ofReal (a n)).toReal = ∑' n, a n := by
  rw [← ENNReal.ofReal_tsum_of_nonneg ha h, ENNReal.toReal_ofReal (tsum_nonneg ha)]

theorem embeddingEnergy_eq :
    embeddingEnergy = ∑' n : ℤ, ENNReal.ofReal ((graphWeight n)⁻¹) :=
  tsum_congr fun n => (ENNReal.ofReal_inv_of_pos (graphWeight_pos n)).symm

theorem embeddingEnergy_finite_and_constant :
    embeddingEnergy ≠ ∞ ∧
    1 ≤ sobolevEmbeddingConstant ∧
    sobolevEmbeddingConstant ^ 2 =
      ∑' n : ℤ, (1 + (2 * Real.pi * (n : ℝ)) ^ 2)⁻¹ := by
  have hs := reciprocal_graphWeight_summable
  have hnn : ∀ n : ℤ, 0 ≤ (graphWeight n)⁻¹ := fun n => inv_nonneg.mpr (graphWeight_pos n).le
  have htoReal : embeddingEnergy.toReal = ∑' n : ℤ, (graphWeight n)⁻¹ := by
    rw [embeddingEnergy_eq]
    exact tsum_ofReal_toReal hnn hs
  refine ⟨?_, ?_, ?_⟩
  · rw [embeddingEnergy_eq]
    exact (tsum_ofReal_ne_top_iff hnn).mpr hs
  · have h0 : (graphWeight 0)⁻¹ ≤ ∑' n : ℤ, (graphWeight n)⁻¹ := hs.le_tsum 0 (fun j _ => hnn j)
    have hg0 : graphWeight 0 = 1 := by simp [graphWeight]
    rw [hg0, inv_one] at h0
    unfold sobolevEmbeddingConstant
    rw [htoReal]
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ _ := Real.sqrt_le_sqrt h0
  · unfold sobolevEmbeddingConstant
    rw [Real.sq_sqrt (ENNReal.toReal_nonneg), htoReal]
    rfl

/-! ### compatibility with the house H1 predicate -/

theorem graphTerm_nonneg (u : PhysicalL2) (n : ℤ) :
    0 ≤ graphWeight n * ‖physicalFourier u n‖ ^ 2 :=
  mul_nonneg (graphWeight_pos n).le (sq_nonneg _)

theorem h1GraphEnergy_finite_iff (u : PhysicalL2) :
    h1GraphEnergy u ≠ ∞ ↔ SobolevSquareSummable 1 (physicalFourier u) := by
  unfold h1GraphEnergy
  rw [tsum_ofReal_ne_top_iff (graphTerm_nonneg u)]
  unfold SobolevSquareSummable
  simp only [japaneseBracket_h1_weight]
  constructor
  · intro h
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) h
    exact mul_le_mul_of_nonneg_right (graphWeight_ge n) (sq_nonneg _)
  · intro h
    refine Summable.of_nonneg_of_le (graphTerm_nonneg u) (fun n => ?_)
      (h.mul_left ((2 * Real.pi) ^ 2))
    calc graphWeight n * ‖physicalFourier u n‖ ^ 2
        ≤ ((2 * Real.pi) ^ 2 * (1 + (n : ℝ) ^ 2)) * ‖physicalFourier u n‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (graphWeight_le n) (sq_nonneg _)
      _ = (2 * Real.pi) ^ 2 * ((1 + (n : ℝ) ^ 2) * ‖physicalFourier u n‖ ^ 2) := by ring

theorem graph_summable (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    Summable (fun n : ℤ => graphWeight n * ‖physicalFourier u n‖ ^ 2) := by
  have h := (h1GraphEnergy_finite_iff u).mpr hu
  unfold h1GraphEnergy at h
  exact (tsum_ofReal_ne_top_iff (graphTerm_nonneg u)).mp h

theorem h1GraphEnergy_toReal (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    (h1GraphEnergy u).toReal = ∑' n : ℤ, graphWeight n * ‖physicalFourier u n‖ ^ 2 :=
  tsum_ofReal_toReal (graphTerm_nonneg u) (graph_summable u hu)

theorem h1GraphNorm_eq (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    h1GraphNorm u = Real.sqrt (∑' n : ℤ, graphWeight n * ‖physicalFourier u n‖ ^ 2) := by
  unfold h1GraphNorm
  rw [h1GraphEnergy_toReal u hu]

theorem house_norm_sq (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    ‖physicalSobolevL2 1 u hu‖ ^ 2 = ∑' n : ℤ, (1 + (n : ℝ) ^ 2) * ‖physicalFourier u n‖ ^ 2 := by
  rw [physicalSobolevL2_norm_sq]
  simp only [japaneseBracket_h1_weight]

theorem h1GraphNorm_house_bounds (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    ‖physicalSobolevL2 1 u hu‖ ≤ h1GraphNorm u ∧
    h1GraphNorm u ≤ 2 * Real.pi * ‖physicalSobolevL2 1 u hu‖ := by
  have hS1 : Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2) * ‖physicalFourier u n‖ ^ 2) := by
    have := hu
    unfold SobolevSquareSummable at this
    simpa only [japaneseBracket_h1_weight] using this
  have hS2 := graph_summable u hu
  have hlow : ∑' n : ℤ, (1 + (n : ℝ) ^ 2) * ‖physicalFourier u n‖ ^ 2 ≤
      ∑' n : ℤ, graphWeight n * ‖physicalFourier u n‖ ^ 2 :=
    hS1.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_right (graphWeight_ge n) (sq_nonneg _)) hS2
  have hup : ∑' n : ℤ, graphWeight n * ‖physicalFourier u n‖ ^ 2 ≤
      (2 * Real.pi) ^ 2 * ∑' n : ℤ, (1 + (n : ℝ) ^ 2) * ‖physicalFourier u n‖ ^ 2 := by
    rw [← tsum_mul_left]
    refine hS2.tsum_le_tsum (fun n => ?_) (hS1.mul_left _)
    calc graphWeight n * ‖physicalFourier u n‖ ^ 2
        ≤ ((2 * Real.pi) ^ 2 * (1 + (n : ℝ) ^ 2)) * ‖physicalFourier u n‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (graphWeight_le n) (sq_nonneg _)
      _ = (2 * Real.pi) ^ 2 * ((1 + (n : ℝ) ^ 2) * ‖physicalFourier u n‖ ^ 2) := by ring
  rw [h1GraphNorm_eq u hu]
  have hn := house_norm_sq u hu
  constructor
  · apply le_trans (le_abs_self _)
    apply Real.abs_le_sqrt
    rw [hn]
    exact hlow
  · rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, hn]
    exact hup

/-! ### weak derivative -/

theorem norm_fourierMultiplier_one (n : ℤ) :
    ‖NlsGge.Atomic.LIB002.fourierMultiplier 1 n‖ = 2 * Real.pi * |(n : ℝ)| := by
  unfold NlsGge.Atomic.LIB002.fourierMultiplier
  have e : (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) / ((1 : ℝ) : ℂ)) =
      ((2 * Real.pi * (n : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_mul, abs_of_pos Real.pi_pos]
  norm_num

theorem norm_fourierMultiplier_sq (n : ℤ) :
    ‖NlsGge.Atomic.LIB002.fourierMultiplier 1 n‖ ^ 2 = (2 * Real.pi * (n : ℝ)) ^ 2 := by
  rw [norm_fourierMultiplier_one, mul_pow, sq_abs]
  ring

theorem derivative_term (u v : PhysicalL2)
    (hv : NlsGge.Atomic.LIB002.HasWeakDerivativeL2 1 1 u v) (n : ℤ) :
    ‖physicalFourier v n‖ ^ 2 = (2 * Real.pi * (n : ℝ)) ^ 2 * ‖physicalFourier u n‖ ^ 2 := by
  have hc : fourierCoeff (v : PhysicalCircle → ℂ) n =
      NlsGge.Atomic.LIB002.fourierMultiplier 1 n ^ 1 * fourierCoeff (u : PhysicalCircle → ℂ) n :=
    NlsGge.Atomic.LIB002.weakDerivative_fourierCoeff hv n
  show ‖fourierCoeff (v : PhysicalCircle → ℂ) n‖ ^ 2 =
    (2 * Real.pi * (n : ℝ)) ^ 2 * ‖fourierCoeff (u : PhysicalCircle → ℂ) n‖ ^ 2
  rw [hc, pow_one, norm_mul, mul_pow, norm_fourierMultiplier_sq]

theorem h1GraphEnergy_eq_derivative_energy
    (u v : PhysicalL2)
    (hv : NlsGge.Atomic.LIB002.HasWeakDerivativeL2 1 1 u v) :
    h1GraphEnergy u = ENNReal.ofReal (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  have hsum : HasSum (fun n : ℤ => ‖physicalFourier u n‖ ^ 2 + ‖physicalFourier v n‖ ^ 2)
      (‖u‖ ^ 2 + ‖v‖ ^ 2) := (hasSum_physicalFourier_sq u).add (hasSum_physicalFourier_sq v)
  have hterm : ∀ n : ℤ, graphWeight n * ‖physicalFourier u n‖ ^ 2 =
      ‖physicalFourier u n‖ ^ 2 + ‖physicalFourier v n‖ ^ 2 := by
    intro n
    rw [derivative_term u v hv n]
    unfold graphWeight
    ring
  unfold h1GraphEnergy
  have hnn : ∀ n : ℤ, 0 ≤ graphWeight n * ‖physicalFourier u n‖ ^ 2 := graphTerm_nonneg u
  have hsm : Summable (fun n : ℤ => graphWeight n * ‖physicalFourier u n‖ ^ 2) := by
    simp only [hterm]
    exact hsum.summable
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsm]
  congr 1
  simp only [hterm]
  exact hsum.tsum_eq

theorem h1_iff_weak_derivative (u : PhysicalL2) :
    SobolevSquareSummable 1 (physicalFourier u) ↔
      ∃ v : PhysicalL2,
        NlsGge.Atomic.LIB002.HasWeakDerivativeL2 1 1 u v := by
  refine Iff.trans ?_ (NlsGge.Atomic.LIB002.weakDerivative_fourier_iff (T := 1) 1 u).symm
  have hs := summable_physicalFourier_sq u
  have e : ∀ n : ℤ,
      ‖NlsGge.Atomic.LIB002.fourierMultiplier 1 n ^ 1 * fourierCoeff (u : PhysicalCircle → ℂ) n‖ ^ 2 =
        (2 * Real.pi * (n : ℝ)) ^ 2 * ‖physicalFourier u n‖ ^ 2 := by
    intro n
    rw [pow_one, norm_mul, mul_pow, norm_fourierMultiplier_sq]
    rfl
  have hmain : SobolevSquareSummable 1 (physicalFourier u) ↔
      Summable (fun n : ℤ => (2 * Real.pi * (n : ℝ)) ^ 2 * ‖physicalFourier u n‖ ^ 2) := by
    unfold SobolevSquareSummable
    simp only [japaneseBracket_h1_weight]
    constructor
    · intro h
      refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
        (h.mul_left ((2 * Real.pi) ^ 2))
      calc (2 * Real.pi * (n : ℝ)) ^ 2 * ‖physicalFourier u n‖ ^ 2
          ≤ ((2 * Real.pi) ^ 2 * (1 + (n : ℝ) ^ 2)) * ‖physicalFourier u n‖ ^ 2 := by
            apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
            have e2 : (2 * Real.pi * (n : ℝ)) ^ 2 = (2 * Real.pi) ^ 2 * (n : ℝ) ^ 2 := by ring
            rw [e2]
            nlinarith [sq_nonneg (n : ℝ), sq_nonneg (2 * Real.pi)]
        _ = (2 * Real.pi) ^ 2 * ((1 + (n : ℝ) ^ 2) * ‖physicalFourier u n‖ ^ 2) := by ring
    · intro h
      have h2 := hs.add (h.mul_left (((2 * Real.pi) ^ 2)⁻¹))
      refine h2.congr (fun n => ?_)
      have hp : (2 * Real.pi) ^ 2 ≠ 0 := by positivity
      have e2 : (2 * Real.pi * (n : ℝ)) ^ 2 = (2 * Real.pi) ^ 2 * (n : ℝ) ^ 2 := by ring
      rw [e2]
      field_simp
  exact hmain.trans (summable_congr (fun n => (e n).symm))

/-! ### weighted l1 estimate -/

theorem weighted_l1_bound {ι : Type*}
    (w : ι → ℝ) (a : ι → ℂ)
    (hw : ∀ i, 0 < w i)
    (hInv : Summable (fun i => (w i)⁻¹))
    (hE : Summable (fun i => w i * ‖a i‖ ^ 2)) :
    Summable (fun i => ‖a i‖) ∧
    (∑' i, ‖a i‖) ≤
      Real.sqrt (∑' i, (w i)⁻¹) *
        Real.sqrt (∑' i, w i * ‖a i‖ ^ 2) := by
  set A := ∑' i, (w i)⁻¹ with hAdef
  set B := ∑' i, w i * ‖a i‖ ^ 2 with hBdef
  have hAn : 0 ≤ A := tsum_nonneg (fun i => inv_nonneg.mpr (hw i).le)
  have hfin : ∀ s : Finset ι, ∑ i ∈ s, ‖a i‖ ≤ Real.sqrt A * Real.sqrt B := by
    intro s
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => (Real.sqrt (w i))⁻¹)
      (fun i => Real.sqrt (w i) * ‖a i‖)
    have e1 : ∀ i, (Real.sqrt (w i))⁻¹ * (Real.sqrt (w i) * ‖a i‖) = ‖a i‖ := fun i => by
      have : Real.sqrt (w i) ≠ 0 := (Real.sqrt_pos.mpr (hw i)).ne'
      field_simp
    have e2 : ∀ i, ((Real.sqrt (w i))⁻¹) ^ 2 = (w i)⁻¹ := fun i => by
      rw [inv_pow, Real.sq_sqrt (hw i).le]
    have e3 : ∀ i, (Real.sqrt (w i) * ‖a i‖) ^ 2 = w i * ‖a i‖ ^ 2 := fun i => by
      rw [mul_pow, Real.sq_sqrt (hw i).le]
    simp only [e1, e2, e3] at hcs
    have hA : ∑ i ∈ s, (w i)⁻¹ ≤ A :=
      hInv.sum_le_tsum s (fun i _ => inv_nonneg.mpr (hw i).le)
    have hB : ∑ i ∈ s, w i * ‖a i‖ ^ 2 ≤ B :=
      hE.sum_le_tsum s (fun i _ => mul_nonneg (hw i).le (sq_nonneg _))
    have hsB : 0 ≤ ∑ i ∈ s, w i * ‖a i‖ ^ 2 :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (hw i).le (sq_nonneg _))
    calc ∑ i ∈ s, ‖a i‖
        ≤ Real.sqrt ((∑ i ∈ s, (w i)⁻¹) * ∑ i ∈ s, w i * ‖a i‖ ^ 2) :=
          le_trans (le_abs_self _) (Real.abs_le_sqrt hcs)
      _ ≤ Real.sqrt (A * B) := Real.sqrt_le_sqrt (mul_le_mul hA hB hsB hAn)
      _ = Real.sqrt A * Real.sqrt B := Real.sqrt_mul hAn B
  have hsum : Summable (fun i => ‖a i‖) := summable_of_sum_le (fun i => norm_nonneg _) hfin
  exact ⟨hsum, hsum.tsum_le_of_sum_le hfin⟩

theorem fourier_l1_le (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    Summable (fun n : ℤ => ‖physicalFourier u n‖) ∧
    (∑' n : ℤ, ‖physicalFourier u n‖) ≤
      sobolevEmbeddingConstant * h1GraphNorm u := by
  obtain ⟨hs, hb⟩ := weighted_l1_bound graphWeight (physicalFourier u) graphWeight_pos
    reciprocal_graphWeight_summable (graph_summable u hu)
  refine ⟨hs, ?_⟩
  have hc : sobolevEmbeddingConstant = Real.sqrt (∑' n : ℤ, (graphWeight n)⁻¹) := by
    unfold sobolevEmbeddingConstant
    rw [embeddingEnergy_eq]
    rw [tsum_ofReal_toReal (fun n => inv_nonneg.mpr (graphWeight_pos n).le)
      reciprocal_graphWeight_summable]
  rw [hc, h1GraphNorm_eq u hu]
  exact hb

/-! ### Fourier synthesis -/

theorem continuous_fourier_hasSum (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    Summable (fun n : ℤ => ‖fourierTerm u n‖) ∧
    HasSum (fourierTerm u) (continuousRepresentative u hu) := by
  refine ⟨?_, physicalH1Continuous_hasSum u hu⟩
  have h := physicalH1_absolute_fourier_summable u hu
  simpa only [fourierTerm, norm_smul, fourier_norm, mul_one] using h

theorem continuous_fourier_tendstoUniformly (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    TendstoUniformly
      (fun s : Finset ℤ => fun x : PhysicalCircle =>
        ∑ n ∈ s, physicalFourier u n * fourier n x)
      (continuousRepresentative u hu) atTop := by
  have h : Tendsto (fun s : Finset ℤ => ∑ n ∈ s, fourierTerm u n) atTop
      (𝓝 (continuousRepresentative u hu)) := (continuous_fourier_hasSum u hu).2
  have h2 := ContinuousMap.tendsto_iff_tendstoUniformly.mp h
  have e : (fun s : Finset ℤ => fun x : PhysicalCircle =>
      ∑ n ∈ s, physicalFourier u n * fourier n x) =
      fun s : Finset ℤ => fun x : PhysicalCircle => (∑ n ∈ s, fourierTerm u n) x := by
    funext s x
    simp [fourierTerm, ContinuousMap.sum_apply]
  rw [e]
  exact h2

theorem continuousRepresentative_toLp (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    ContinuousMap.toLp 2 spatialMeasure ℂ
      (continuousRepresentative u hu) = u :=
  physicalH1Continuous_toLp u hu

theorem continuousRepresentative_norm_le_l1 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    ‖continuousRepresentative u hu‖ ≤ ∑' n : ℤ, ‖physicalFourier u n‖ := by
  have hs := (continuous_fourier_hasSum u hu).1
  calc ‖continuousRepresentative u hu‖
      = ‖∑' n : ℤ, fourierTerm u n‖ := by rw [(continuous_fourier_hasSum u hu).2.tsum_eq]
    _ ≤ ∑' n : ℤ, ‖fourierTerm u n‖ := norm_tsum_le_tsum_norm hs
    _ = ∑' n : ℤ, ‖physicalFourier u n‖ := by
        simp only [fourierTerm, norm_smul, fourier_norm, mul_one]

theorem h1_norm_sup_le
    (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    ‖continuousRepresentative u hu‖ ≤
      sobolevEmbeddingConstant * h1GraphNorm u :=
  (continuousRepresentative_norm_le_l1 u hu).trans (fourier_l1_le u hu).2

theorem h1_fourier_continuous_representative
    (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    h1GraphEnergy u ≠ ∞ ∧ embeddingEnergy ≠ ∞ ∧
    Summable (fun n : ℤ => ‖physicalFourier u n‖) ∧
    HasSum (fourierTerm u) (continuousRepresentative u hu) ∧
    TendstoUniformly
      (fun s : Finset ℤ => fun x : PhysicalCircle =>
        ∑ n ∈ s, physicalFourier u n * fourier n x)
      (continuousRepresentative u hu) atTop ∧
    ContinuousMap.toLp 2 spatialMeasure ℂ
      (continuousRepresentative u hu) = u ∧
    ‖continuousRepresentative u hu‖ ≤
      sobolevEmbeddingConstant * h1GraphNorm u :=
  ⟨(h1GraphEnergy_finite_iff u).mpr hu, embeddingEnergy_finite_and_constant.1,
    (fourier_l1_le u hu).1, (continuous_fourier_hasSum u hu).2,
    continuous_fourier_tendstoUniformly u hu, continuousRepresentative_toLp u hu,
    h1_norm_sup_le u hu⟩

theorem h1_pair_component_sup_le
    (u : Bool → PhysicalL2)
    (hu : ∀ b, SobolevSquareSummable 1 (physicalFourier (u b))) :
    ∀ b, ‖continuousRepresentative (u b) (hu b)‖ ≤
      sobolevEmbeddingConstant * h1GraphNorm (u b) :=
  fun b => h1_norm_sup_le (u b) (hu b)

theorem continuousRepresentative_eq_canonical (x : SobolevHilbert 1) :
    continuousRepresentative
      (physicalH1CarrierToL2AfterAcceptedCoordinate x)
      (physicalH1CarrierToL2AfterAcceptedCoordinate_sobolevSquareSummable x) =
      physicalH1CanonicalContinuousRepresentativeCLM x := rfl

theorem canonical_h1_norm_sup_le (x : SobolevHilbert 1) :
    ‖physicalH1CanonicalContinuousRepresentativeCLM x‖ ≤
      sobolevEmbeddingConstant *
        h1GraphNorm (physicalH1CarrierToL2AfterAcceptedCoordinate x) := by
  rw [← continuousRepresentative_eq_canonical]
  exact h1_norm_sup_le _ _

end


end NlsGge.Atomic.LIB004
