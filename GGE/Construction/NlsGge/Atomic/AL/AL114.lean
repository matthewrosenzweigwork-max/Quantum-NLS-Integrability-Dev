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

theorem al114 (lower upper : ℝ) (c : BoundedCoefficients lower upper)
    (delta : ℝ) (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ lower / 64) :
    Summable (fun k : ℤ => (1 + |(k : ℝ)| ^ 4) / alRateComp38 c.val k) ∧
    (∀ N : ℕ, alMeshStep38 N ≤ c.val 0 / 2 →
      ∀ k : ℤ, |k| ≤ (N : ℤ) →
      let d : ℝ := delta * (1 + alOmegaFree38 N k ^ 4) / alRateFree38 c.val N k
      d ≤ (2 * (1 + (2 * Real.pi) ^ 4)) * delta *
        (1 + |(k : ℝ)| ^ 4) / alRateComp38 c.val k ∧
      |Real.log (alTiltFactor38 c.val delta (alOmegaFree38 N k) (alMeshStep38 N))| ≤
        2 * d) ∧
    (∀ k : ℤ, Tendsto
      (fun N : ℕ => Real.log
        (alTiltFactor38 c.val delta (alOmegaFree38 N k) (alMeshStep38 N)))
      atTop (𝓝 (Real.log (alTiltFactor38 c.val delta (2 * Real.pi * (k : ℝ)) 0)))) := by
  have hlo : 0 < lower := c.property.1
  have hc := c.property
  have hKpos : 0 < lower / 1296 := by positivity
  have hnn : ∀ (r : ℝ) (i : ℕ), 0 ≤ NlsGge.weightTerm c.val r i := fun r i => by
    unfold NlsGge.weightTerm NlsGge.coefficient
    have hci : 0 ≤ c.val i / (Nat.factorial i : ℝ) ^ 4 :=
      div_nonneg (by linarith [(c.property.2.2 i).1]) (by positivity)
    exact mul_nonneg hci (by rw [pow_mul]; positivity)
  have hsum : ∀ r : ℝ, Summable (NlsGge.weightTerm c.val r) := fun r =>
    NlsGge.Weights.weightTerm_summable lower upper c.val hlo
      (fun j => (c.property.2.2 j).1) (fun j => (c.property.2.2 j).2) r
  have hc0 : ∀ r : ℝ, c.val 0 ≤ NlsGge.Weights.weight c.val r := fun r => by
    have h0 := (hsum r).le_tsum 0 (fun i _ => hnn r i)
    have e : NlsGge.weightTerm c.val r 0 = c.val 0 := by
      unfold NlsGge.weightTerm NlsGge.coefficient
      simp
    have hw : NlsGge.Weights.weight c.val r = ∑' j, NlsGge.weightTerm c.val r j := rfl
    rw [hw]
    linarith
  have hWmono : ∀ r s : ℝ, s ^ 2 ≤ r ^ 2 →
      NlsGge.Weights.weight c.val s ≤ NlsGge.Weights.weight c.val r := by
    intro r s hrs
    have hsr : ∀ j : ℕ, NlsGge.weightTerm c.val s j ≤ NlsGge.weightTerm c.val r j := fun j => by
      unfold NlsGge.weightTerm NlsGge.coefficient
      rw [pow_mul, pow_mul]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sq_nonneg s) hrs j)
        (div_nonneg (by linarith [(c.property.2.2 j).1]) (by positivity))
    exact Summable.tsum_le_tsum hsr (hsum s) (hsum r)
  have hW3 : ∀ r : ℝ, lower / 1296 * r ^ 6 ≤ NlsGge.Weights.weight c.val r := fun r => by
    have h3 := (hsum r).le_tsum 3 (fun i _ => hnn r i)
    have e : NlsGge.weightTerm c.val r 3 = c.val 3 / 1296 * r ^ 6 := by
      unfold NlsGge.weightTerm NlsGge.coefficient
      norm_num [Nat.factorial]
    have hw : NlsGge.Weights.weight c.val r = ∑' j, NlsGge.weightTerm c.val r j := rfl
    have hb : lower / 1296 * r ^ 6 ≤ c.val 3 / 1296 * r ^ 6 :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by linarith [(c.property.2.2 3).1])
        (by norm_num)) (by positivity)
    rw [hw]
    linarith
  -- Part A
  have hpartA : Summable (fun k : ℤ => (1 + |(k : ℝ)| ^ 4) / alRateComp38 c.val k) := by
    have hmaj : Summable (fun k : ℤ =>
        (2 / (lower / 1296 * 4096)) * (1 / (k : ℝ) ^ 2) +
          (if k = 0 then 1 / c.val 0 else 0)) := by
      refine Summable.add ?_ (hasSum_ite_eq (0 : ℤ) (1 / c.val 0)).summable
      exact (Real.summable_one_div_int_pow.2 one_lt_two).mul_left _
    have hnonneg : ∀ k : ℤ, 0 ≤ (1 + |(k : ℝ)| ^ 4) / alRateComp38 c.val k := fun k => by
      unfold alRateComp38
      have hnum : (0 : ℝ) ≤ 1 + |(k : ℝ)| ^ 4 := by positivity
      have hc0pos : (0 : ℝ) ≤ c.val 0 := le_of_lt (lt_of_lt_of_le hlo (c.property.2.2 0).1)
      exact div_nonneg hnum (le_trans hc0pos (hc0 _))
    refine Summable.of_nonneg_of_le hnonneg (fun k => ?_) hmaj
    · unfold alRateComp38
      by_cases hk0 : k = 0
      · subst hk0
        have hcpos : 0 < c.val 0 := lt_of_lt_of_le hlo (c.property.2.2 0).1
        have hW0 : c.val 0 ≤ NlsGge.Weights.weight c.val (4 * |((0 : ℤ) : ℝ)|) := hc0 _
        simp only [Int.cast_zero, abs_zero, mul_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true, div_zero, zero_add, if_true, add_zero, pow_zero, one_div]
        simp only [Int.cast_zero, abs_zero, mul_zero] at hW0
        exact inv_anti₀ hcpos hW0
      · have ha1 : (1 : ℝ) ≤ |(k : ℝ)| := by
          have := Int.one_le_abs hk0
          rw [← Int.cast_abs]
          exact_mod_cast this
        have hW := hW3 (4 * |(k : ℝ)|)
        have hden : 0 < lower / 1296 * (4 * |(k : ℝ)|) ^ 6 := by positivity
        have h1 : (1 + |(k : ℝ)| ^ 4) / NlsGge.Weights.weight c.val (4 * |(k : ℝ)|) ≤
            (1 + |(k : ℝ)| ^ 4) / (lower / 1296 * (4 * |(k : ℝ)|) ^ 6) :=
          div_le_div_of_nonneg_left (by positivity) hden hW
        have hk2 : (k : ℝ) ^ 2 = |(k : ℝ)| ^ 2 := (sq_abs _).symm
        have h2 : (1 + |(k : ℝ)| ^ 4) / (lower / 1296 * (4 * |(k : ℝ)|) ^ 6) ≤
            (2 / (lower / 1296 * 4096)) * (1 / |(k : ℝ)| ^ 2) := by
          have e : (2 / (lower / 1296 * 4096)) * (1 / |(k : ℝ)| ^ 2) =
              2 / (lower / 1296 * 4096 * |(k : ℝ)| ^ 2) := by
            field_simp
          rw [e, div_le_div_iff₀ hden (by positivity)]
          have ha4 : (1 : ℝ) ≤ |(k : ℝ)| ^ 4 := one_le_pow₀ ha1
          nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ lower / 1296 * 4096 * |(k : ℝ)| ^ 2)
            (sub_nonneg.2 ha4)]
        rw [hk2]
        simp only [hk0, if_false, add_zero]
        exact h1.trans h2
  refine ⟨hpartA, ?_, ?_⟩
  · intro N hN k hk
    intro d
    have hh : 0 < alMeshStep38 N := by unfold alMeshStep38; positivity
    have hNh : alMeshStep38 N ≤ c.val 0 / 2 := hN
    have hWc := hc0 (alOmegaFree38 N k)
    have hW2 := weight_ge_two38 (lo := lower) (up := upper) (c := c.val) hc (alOmegaFree38 N k)
    have hWpos : 0 < NlsGge.Weights.weight c.val (alOmegaFree38 N k) := by
      have : 0 < lower + lower / 16 * alOmegaFree38 N k ^ 4 := by positivity
      linarith
    have hDpos : 0 < NlsGge.Weights.weight c.val (alOmegaFree38 N k) - alMeshStep38 N := by
      linarith
    have hdnn : 0 ≤ d := by
      show 0 ≤ delta * (1 + alOmegaFree38 N k ^ 4) / alRateFree38 c.val N k
      exact div_nonneg (mul_nonneg hdelta0 (by positivity)) (by unfold alRateFree38; exact hDpos.le)
    have hkey : delta * (1 + alOmegaFree38 N k ^ 4) ≤ lower * (1 + alOmegaFree38 N k ^ 4 / 16) / 4 := by
      have h1 : delta * (1 + alOmegaFree38 N k ^ 4) ≤ lower / 64 * (1 + alOmegaFree38 N k ^ 4) :=
        mul_le_mul_of_nonneg_right hdelta (by positivity)
      have h2 : lower / 64 * (1 + alOmegaFree38 N k ^ 4) =
          lower * (1 + alOmegaFree38 N k ^ 4 / 16) / 4 - lower * 15 / 64 := by ring
      linarith
    have hd_le : d ≤ 1 / 2 := by
      show delta * (1 + alOmegaFree38 N k ^ 4) / alRateFree38 c.val N k ≤ 1 / 2
      unfold alRateFree38
      rw [div_le_iff₀ hDpos]
      linarith
    -- the tilt factor is 1 - d
    have hf : alTiltFactor38 c.val delta (alOmegaFree38 N k) (alMeshStep38 N) = 1 - d := rfl
    refine ⟨?_, ?_⟩
    · -- d ≤ 2(1+(2π)^4) δ(1+|k|^4)/W(4|k|)
      have hWh2 : 2 * alMeshStep38 N ≤ NlsGge.Weights.weight c.val (alOmegaFree38 N k) := by
        linarith
      have hA : delta * (1 + alOmegaFree38 N k ^ 4) /
          (NlsGge.Weights.weight c.val (alOmegaFree38 N k) - alMeshStep38 N) ≤
          2 * (delta * (1 + alOmegaFree38 N k ^ 4)) / NlsGge.Weights.weight c.val (alOmegaFree38 N k) := by
        rw [div_le_div_iff₀ hDpos hWpos]
        have hnum : 0 ≤ delta * (1 + alOmegaFree38 N k ^ 4) := by positivity
        nlinarith [mul_nonneg hnum (sub_nonneg.2 hWh2)]
      have hk_nonneg : |(k : ℝ)| * alMeshStep38 N ≤ 1 / 2 := by
        have hkN : |(k : ℝ)| ≤ (N : ℝ) := by
          have : |(k : ℝ)| = ((|k| : ℤ) : ℝ) := (Int.cast_abs).symm
          rw [this]
          exact_mod_cast hk
        have hmeshval : alMeshStep38 N = 1 / (2 * (N : ℝ) + 1) := rfl
        rw [hmeshval, mul_one_div, div_le_iff₀ (by positivity)]
        linarith
      have hωabs : 4 * |(k : ℝ)| ≤ |alOmegaFree38 N k| :=
        alOmega_abs_ge38 hh hk_nonneg
      have hωle : |alOmegaFree38 N k| ≤ 2 * Real.pi * |(k : ℝ)| := by
        have hs := Real.abs_sin_le_abs (x := Real.pi * (k : ℝ) * alMeshStep38 N)
        have habs : |Real.pi * (k : ℝ) * alMeshStep38 N| = Real.pi * |(k : ℝ)| * alMeshStep38 N := by
          rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hh]
        rw [habs] at hs
        have e : alOmegaFree38 N k = 2 * Real.sin (Real.pi * (k : ℝ) * alMeshStep38 N) / alMeshStep38 N := rfl
        rw [e, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hh,
          div_le_iff₀ hh]
        nlinarith
      have hω4 : alOmegaFree38 N k ^ 4 ≤ (2 * Real.pi * |(k : ℝ)|) ^ 4 := by
        have e4 : alOmegaFree38 N k ^ 4 = |alOmegaFree38 N k| ^ 4 := by
          rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
        rw [e4]
        exact pow_le_pow_left₀ (abs_nonneg _) hωle 4
      have hnumle : 1 + alOmegaFree38 N k ^ 4 ≤ (1 + (2 * Real.pi) ^ 4) * (1 + |(k : ℝ)| ^ 4) := by
        have e : (2 * Real.pi * |(k : ℝ)|) ^ 4 = (2 * Real.pi) ^ 4 * |(k : ℝ)| ^ 4 := by ring
        rw [e] at hω4
        have : 0 ≤ (2 * Real.pi) ^ 4 * |(k : ℝ)| ^ 4 := by positivity
        have h5 : 0 ≤ (2 * Real.pi) ^ 4 := by positivity
        have ha4 : 0 ≤ |(k : ℝ)| ^ 4 := by positivity
        nlinarith [hω4, ha4, h5, this]
      have hW4pos : 0 < NlsGge.Weights.weight c.val (4 * |(k : ℝ)|) := by
        have := hc0 (4 * |(k : ℝ)|)
        linarith [hlo]
      have hWmon : NlsGge.Weights.weight c.val (4 * |(k : ℝ)|) ≤
          NlsGge.Weights.weight c.val (alOmegaFree38 N k) := by
        apply hWmono
        have h4sq : (4 * |(k : ℝ)|) ^ 2 ≤ alOmegaFree38 N k ^ 2 := by
          rw [← sq_abs (alOmegaFree38 N k)]
          exact pow_le_pow_left₀ (by positivity) hωabs 2
        exact h4sq
      have hB : 2 * (delta * (1 + alOmegaFree38 N k ^ 4)) / NlsGge.Weights.weight c.val (alOmegaFree38 N k) ≤
          2 * (delta * ((1 + (2 * Real.pi) ^ 4) * (1 + |(k : ℝ)| ^ 4))) /
            NlsGge.Weights.weight c.val (4 * |(k : ℝ)|) := by
        apply div_le_div₀ (by positivity)
        · have := mul_le_mul_of_nonneg_left hnumle hdelta0
          nlinarith
        · exact hW4pos
        · exact hWmon
      have hfinal : d ≤ 2 * (1 + (2 * Real.pi) ^ 4) * delta * (1 + |(k : ℝ)| ^ 4) /
          alRateComp38 c.val k := by
        have e : 2 * (1 + (2 * Real.pi) ^ 4) * delta * (1 + |(k : ℝ)| ^ 4) / alRateComp38 c.val k =
            2 * (delta * ((1 + (2 * Real.pi) ^ 4) * (1 + |(k : ℝ)| ^ 4))) /
              NlsGge.Weights.weight c.val (4 * |(k : ℝ)|) := by
          unfold alRateComp38
          ring
        rw [e]
        refine le_trans ?_ hB
        exact hA
      exact hfinal
    · -- |log(1-d)| ≤ 2d
      rw [hf]
      have hl1 : Real.log (1 - d) ≤ 0 :=
        Real.log_nonpos (by linarith : (0 : ℝ) ≤ 1 - d) (by linarith : 1 - d ≤ 1)
      have hpos1 : (0 : ℝ) < 1 - d := by linarith
      have hl2 : 1 - (1 - d)⁻¹ ≤ Real.log (1 - d) := Real.one_sub_inv_le_log_of_pos hpos1
      have hinv : (1 - d)⁻¹ ≤ 1 + 2 * d := by
        rw [← one_div, div_le_iff₀ hpos1]
        nlinarith
      rw [abs_le]
      constructor <;> linarith
  · intro k
    have hh0 : (0 : ℝ) ≤ lower / 2 := by linarith
    have hT := tendsto_alFactor38 (lo := lower) (up := upper) (c := c.val) hc delta k
    have hpos0 : 0 < alTiltFactor38 c.val delta (2 * Real.pi * (k : ℝ)) 0 := by
      have hb := alTiltFactor_bounds38 (c := c.val) hc hdelta0 hdelta hh0 (2 * Real.pi * (k : ℝ))
      linarith [hb.1]
    have hmesh : ∀ N : ℕ, alMeshStep38 N = alMesh38 N := fun N => by
      unfold alMeshStep38 alMesh38
      rw [one_div]
      push_cast
      ring_nf
    have hfun : (fun N : ℕ => Real.log (alTiltFactor38 c.val delta (alOmegaFree38 N k) (alMeshStep38 N))) =
        fun N : ℕ => Real.log (alTiltFactor38 c.val delta (alOmega38 (alMesh38 N) k) (alMesh38 N)) := by
      funext N
      show Real.log (alTiltFactor38 c.val delta (alOmega38 (alMeshStep38 N) k) (alMeshStep38 N)) = _
      rw [hmesh N]
    rw [hfun]
    exact hT.log hpos0.ne'

end NlsGge.ThirdConsultation.AL
