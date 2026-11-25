import NlsGge.Hierarchy.ALQ4Limit38
import NlsGge.Hierarchy.ALFreeFields38
import NlsGge.Hierarchy.ALCorrector38
import NlsGge.Hierarchy.ALFreeDeterminant38
import NlsGge.Hierarchy.ALRatesBridge38
import NlsGge.Hierarchy.ALCompactConsistency38
import NlsGge.Hierarchy.ALPlaneConsistency38
import NlsGge.Hierarchy.ALNegativeQuartic38
import NlsGge.Hierarchy.ALTiltMeasure38
import NlsGge.Birkhoff.W04WeightedSmoothing38
import NlsGge.Birkhoff.S05FreeEnergy38b
import NlsGge.Hierarchy.ALEnergyAnalytic38
import NlsGge.Hierarchy.ALPositiveDecompositions38
import NlsGge.Hierarchy.ALFiniteMeasure38
import NlsGge.Hierarchy.ALMoments38
import NlsGge.Hierarchy.ALFullEnergy38
import NlsGge.Hierarchy.ALTransferDefs38
import NlsGge.Hierarchy.ALSampling38
import NlsGge.Hierarchy.ALSamplingV2Formula38
import NlsGge.Hierarchy.ALQ4Ensemble38
import NlsGge.Hierarchy.ALQ4Gaussian38
import NlsGge.Hierarchy.ALGaussianNormalizer38
import NlsGge.Hierarchy.ALTilt38
import NlsGge.Hierarchy.ALLaurent38
import NlsGge.Hierarchy.ALExteriorBranch38
import NlsGge.Hierarchy.ALQuadraticPart38
import NlsGge.Hierarchy.ALIsospectral38
import NlsGge.Hierarchy.ALGlobalFlow38
import NlsGge.Hierarchy.ALLiouvilleInvariance38
import NlsGge.Hierarchy.ALBoundaryKappa38
import NlsGge.Hierarchy.ALPoissonLiouville38
import NlsGge.Hierarchy.ALComplexMonodromy38
import NlsGge.Hierarchy.ALComplexExteriorLog38
import NlsGge.Hierarchy.ALPlaneWaveGap38
import NlsGge.Hierarchy.FullEnergyPlaneConvergence38
import NlsGge.Spectral.ActualComplexZsDysonProductHasSumV2
import NlsGge.Analysis.NaturalCover
import NlsGge.Definitions.PilotInterfaces
import NlsGge.Schur.FourierMultiplier
import NlsGge.Sobolev.SourceWeighted
import NlsGge.Sobolev.SourceEmbeddings
import NlsGge.Sobolev.FiniteFourier
import NlsGge.Birkhoff.F08Bare38g
import NlsGge.Birkhoff.F08Bare38d
import NlsGge.Birkhoff.F05Identity38
import NlsGge.Bootstrap

open scoped Nat
open NlsGge.AblowitzLadik NlsGge.HierarchyRiccati.Core
open NlsGge.Pilot NlsGge.Weights
open Set Filter Topology MeasureTheory

namespace NlsGge.ThirdConsultation.AL

theorem al110 (lower upper : ℝ) (hlower : 0 < lower) (hlu : lower ≤ upper) :
    (Tendsto (fun N : ℕ => (alMeshStep38 N ^ 2 / 2) /
      alMeshStep38 N ^ (3 / 2 : ℝ)) atTop (𝓝 0)) ∧
    ∃ C h0 : ℝ, 0 < C ∧ 0 < h0 ∧
      ∀ c : BoundedCoefficients lower upper, ∀ N : ℕ, alMeshStep38 N ≤ h0 →
      let h : ℝ := alMeshStep38 N
      let omega : ℝ := alOmega38 h (N : ℤ)
      let c0 : ℝ := Real.cos (Real.pi * (N : ℝ) * h)
      c0 = Real.sin (Real.pi * h / 2) ∧
      |c0| ≤ C * h ∧ |omega - 2 / h| ≤ C * h ∧
      |alBQuartic38 (weight c.val) h (N : ℤ) / weight c.val omega +
        Real.sqrt 2 / 4 * h ^ (3 / 2 : ℝ)| ≤ C * h ^ (7 / 4 : ℝ) ∧
      |c0 ^ 2 * deriv (deriv (weight c.val)) omega / (2 * weight c.val omega)| ≤
        C * h ^ 3 := by
  have hpos_all : ∀ N : ℕ, 0 < alMeshStep38 N := fun N => by unfold alMeshStep38; positivity
  have hT : Tendsto (fun N : ℕ => alMeshStep38 N) atTop (𝓝 0) := by
    have hg : Tendsto (fun N : ℕ => 2 * (N : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos)
    exact (tendsto_const_nhds (x := (1 : ℝ))).div_atTop hg
  have hid : ∀ h : ℝ, 0 < h → h ^ 2 / 2 / h ^ (3 / 2 : ℝ) = 1 / 2 * h ^ (1 / 2 : ℝ) := by
    intro h hp
    have e : h ^ (3 / 2 : ℝ) * h ^ (1 / 2 : ℝ) = h ^ 2 := by
      rw [← Real.rpow_add hp]; norm_num
    have hne : h ^ (3 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hp _).ne'
    rw [div_div, div_eq_iff (mul_ne_zero two_ne_zero hne), ← e]
    ring
  have hpart1 : Tendsto (fun N : ℕ => (alMeshStep38 N ^ 2 / 2) / alMeshStep38 N ^ (3 / 2 : ℝ))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => alMeshStep38 N ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
      have := ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 2)).tendsto 0).comp hT
      rw [Real.zero_rpow (by norm_num)] at this
      exact this
    have h2 := h1.const_mul (1 / 2 : ℝ)
    rw [mul_zero] at h2
    exact h2.congr' (Eventually.of_forall fun N => (hid _ (hpos_all N)).symm)
  obtain ⟨K, h₀, hK, hh₀, hanch⟩ := alPlane_edge_asymptotics38 lower upper hlower hlu
  obtain ⟨C₀, hC₀, hW⟩ := NlsGge.Weights.weight_uniform_derivative_asymptotics lower upper hlower hlu
  refine ⟨hpart1, 11 + 2 * C₀ + K, min h₀ (1 / 16), by positivity, lt_min hh₀ (by norm_num), ?_⟩
  intro c N hN
  intro h omega c0
  have hpos : 0 < alMeshStep38 N := hpos_all N
  have hh : h = 1 / ((2 * N + 1 : ℕ) : ℝ) := by
    show alMeshStep38 N = _
    unfold alMeshStep38
    push_cast
    ring_nf
  have hhpos : 0 < h := by rw [hh]; positivity
  have hh16 : h ≤ 1 / 16 := (show h ≤ min h₀ (1 / 16) from hN).trans (min_le_right _ _)
  have hhh₀ : h ≤ h₀ := (show h ≤ min h₀ (1 / 16) from hN).trans (min_le_left _ _)
  have hLh : h * (2 * (N : ℝ) + 1) = 1 := by rw [hh]; push_cast; field_simp
  have hlo' : ∀ j : ℕ, lower ≤ c.val j := fun j => (c.property.2.2 j).1
  have hhi' : ∀ j : ℕ, c.val j ≤ upper := fun j => (c.property.2.2 j).2
  set x := Real.pi * h / 2 with hx
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hxh : x ≤ 2 * h := by
    rw [hx]
    have := mul_le_mul_of_nonneg_right hpi4 hhpos.le
    linarith
  have hx2 : x ^ 2 ≤ 4 * h ^ 2 := by
    calc x ^ 2 ≤ (2 * h) ^ 2 := pow_le_pow_left₀ hx0 hxh 2
      _ = 4 * h ^ 2 := by ring
  have hθ : Real.pi * (N : ℝ) * h = Real.pi / 2 - x := by
    have hNh : (N : ℝ) * h = (1 - h) / 2 := by linear_combination hLh / 2
    rw [hx]
    linear_combination Real.pi * hNh
  have hc0 : c0 = Real.sin x := by
    show Real.cos (Real.pi * (N : ℝ) * h) = _
    rw [hθ, Real.cos_pi_div_two_sub]
  have hom : omega = 2 * Real.cos x / h := by
    show alOmega38 h (N : ℤ) = _
    unfold alOmega38
    push_cast
    rw [hθ, Real.sin_pi_div_two_sub]
  have hh2 : h ^ 2 ≤ (1 / 16) ^ 2 := pow_le_pow_left₀ hhpos.le hh16 2
  have hcos : 1 / 2 ≤ Real.cos x := by
    have := Real.one_sub_sq_div_two_le_cos (x := x)
    linarith
  have hom_ge : 1 / h ≤ omega := by
    rw [hom]
    apply div_le_div_of_nonneg_right _ hhpos.le
    linarith
  have hom16 : 16 ≤ omega := by
    have : 16 ≤ 1 / h := by rw [le_div_iff₀ hhpos]; linarith
    linarith
  have hom_pos : 0 < omega := by linarith
  have hωh : 1 ≤ omega * h := by
    have := hom_ge
    rw [div_le_iff₀ hhpos] at this
    linarith
  have hWpos : 0 < weight c.val omega :=
    NlsGge.Weights.weight_pos lower upper c.val hlower hlo' hhi' omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hc0]
  · rw [hc0]
    calc |Real.sin x| ≤ |x| := Real.abs_sin_le_abs
      _ = x := abs_of_nonneg hx0
      _ ≤ 2 * h := hxh
      _ ≤ (11 + 2 * C₀ + K) * h := by
          apply mul_le_mul_of_nonneg_right _ hhpos.le
          linarith
  · have hA : 2 * Real.cos x / h - 2 / h ≤ 0 := by
      have : 2 * Real.cos x / h ≤ 2 / h :=
        div_le_div_of_nonneg_right (by linarith [Real.cos_le_one x]) hhpos.le
      linarith
    have hB : -(4 * h) ≤ 2 * Real.cos x / h - 2 / h := by
      rw [← sub_div, le_div_iff₀ hhpos]
      have e4 : -(4 * h) * h = -(4 * h ^ 2) := by ring
      rw [e4]
      linarith [Real.one_sub_sq_div_two_le_cos (x := x)]
    have hCh : 4 * h ≤ (11 + 2 * C₀ + K) * h :=
      mul_le_mul_of_nonneg_right (by linarith) hhpos.le
    rw [hom, abs_le]
    constructor
    · linarith
    · linarith
  · have := hanch c.val hlo' hhi' N h hh hhh₀
    refine le_trans this ?_
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith
  · have h2 := (hW c.val hlo' hhi' omega hom16).2
    have hQ : |deriv (deriv (weight c.val)) omega / weight c.val omega| ≤ (4 + C₀) * h := by
      have h4 : 4 / omega ≤ 4 * h := by
        rw [div_le_iff₀ hom_pos]
        have e4 : 4 * h * omega = 4 * (omega * h) := by ring
        rw [e4]
        linarith
      have h4' : |4 / omega| ≤ 4 * h := by
        rw [abs_of_pos (by positivity)]
        exact h4
      have h5 : omega ^ (-5 / 4 : ℝ) ≤ h := by
        have hm : omega ^ (-5 / 4 : ℝ) ≤ (1 / h) ^ (-5 / 4 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hom_ge (by norm_num)
        have e : (1 / h) ^ (-5 / 4 : ℝ) = h ^ (5 / 4 : ℝ) := by
          rw [Real.div_rpow zero_le_one hhpos.le, Real.one_rpow,
            show (-5 / 4 : ℝ) = -(5 / 4) by norm_num, Real.rpow_neg hhpos.le, one_div, inv_inv]
        have h6 : h ^ (5 / 4 : ℝ) ≤ h ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hhpos (by linarith) (by norm_num)
        rw [Real.rpow_one] at h6
        linarith
      have h7 : |deriv (deriv (weight c.val)) omega / weight c.val omega - 4 / omega| ≤
          C₀ * |omega ^ (-5 / 4 : ℝ)| :=
        le_trans h2 (mul_le_mul_of_nonneg_left (le_abs_self _) hC₀.le)
      have h8 : |omega ^ (-5 / 4 : ℝ)| ≤ h := by
        rw [abs_of_nonneg (by positivity)]
        exact h5
      calc |deriv (deriv (weight c.val)) omega / weight c.val omega|
          = |(deriv (deriv (weight c.val)) omega / weight c.val omega - 4 / omega) + 4 / omega| := by
            ring_nf
        _ ≤ |deriv (deriv (weight c.val)) omega / weight c.val omega - 4 / omega| + |4 / omega| :=
            abs_add_le _ _
        _ ≤ C₀ * h + 4 * h := by
            have := mul_le_mul_of_nonneg_left h8 hC₀.le
            linarith
        _ = (4 + C₀) * h := by ring
    have hsin2 : Real.sin x ^ 2 ≤ 4 * h ^ 2 := by
      have hs := Real.abs_sin_le_abs (x := x)
      have h2' := pow_le_pow_left₀ (abs_nonneg (Real.sin x)) hs 2
      rw [sq_abs, sq_abs] at h2'
      linarith
    have e5 : c0 ^ 2 * deriv (deriv (weight c.val)) omega / (2 * weight c.val omega) =
        (c0 ^ 2 / 2) * (deriv (deriv (weight c.val)) omega / weight c.val omega) := by
      field_simp
    rw [e5, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ c0 ^ 2 / 2)]
    rw [hc0]
    calc Real.sin x ^ 2 / 2 * |deriv (deriv (weight c.val)) omega / weight c.val omega|
        ≤ 4 * h ^ 2 / 2 * ((4 + C₀) * h) := by
          apply mul_le_mul (by linarith) hQ (abs_nonneg _) (by positivity)
      _ = (2 * (4 + C₀)) * h ^ 3 := by ring
      _ ≤ (11 + 2 * C₀ + K) * h ^ 3 :=
          mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hhpos.le 3)

end NlsGge.ThirdConsultation.AL
