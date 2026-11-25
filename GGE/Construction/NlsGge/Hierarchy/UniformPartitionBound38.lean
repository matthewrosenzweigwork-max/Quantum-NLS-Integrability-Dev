import NlsGge.Hierarchy.UniformPartitionBoundAux38
import NlsGge.Schur.ActualSchurBallFullEnergy38V1

/-!
# NEW-F07 (v2 `F:thm:partition`): uniform full-energy relative partition bound

For every `0 < c₋ ≤ c₊` there is `C` (depending only on `c₋, c₊`) such that for every
admitted coefficient sequence `c` (`BoundedCoefficients c₋ c₊`) and every `N`,
`Z_N(W) ≤ C`, where `Z_N(W) = 𝒵_{W,N} / ∏_{|n|≤N}(π/a_n)` is `relativePartition38`.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open NlsGge.Pilot NlsGge.Measure NlsGge.Schur MeasureTheory
open scoped ENNReal

theorem continuous_planeH1Norm38 (N : ℕ) : Continuous (planeH1Norm38 N) :=
  (planeH1Embedding38 N).continuous.norm

/-- Shell decomposition: the full-energy integral over the whole plane is bounded by the sum
over the shells `k ≤ ‖z‖_{H¹} < k+1` (NEW-F07.05, .06). -/
theorem shell_lintegral_bound38 {lo up : ℝ} (c : BoundedCoefficients lo up) (N : ℕ)
    (P : ℝ≥0∞) (Cs' g' R₀' : ℝ)
    (hschur : ∀ R : ℝ, 1 ≤ R →
      ∫⁻ z in {z | planeH1Norm38 N z < R},
          ENNReal.ofReal (Real.exp (-fullEnergy38 (shiftedCoefficients38 c) N z)) ∂planeVolume N ≤
        P * ENNReal.ofReal (Real.exp (Cs' * (1 + R) ^ 9)))
    (hcoer : ∀ (z : FourierPlane N) (R : ℝ), R₀' ≤ R → R ≤ planeH1Norm38 N z →
      g' * Real.exp (g' * R ^ (1 / 4 : ℝ)) ≤ reservedEnergy38 c N z) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (-fullEnergy38 c N z)) ∂planeVolume N ≤
      P * ∑' k : ℕ, ENNReal.ofReal (Real.exp (Cs' * ((k : ℝ) + 2) ^ 9 -
        shiftEps38 lo up * shellLevel38 g' R₀' k)) := by
  have hmeas := continuous_planeH1Norm38 N
  have hcover : (Set.univ : Set (FourierPlane N)) ⊆
      ⋃ k : ℕ, {z | (k : ℝ) ≤ planeH1Norm38 N z ∧ planeH1Norm38 N z < (k : ℝ) + 1} := by
    intro z _
    have h0 : 0 ≤ planeH1Norm38 N z := norm_nonneg _
    refine Set.mem_iUnion.mpr ⟨⌊planeH1Norm38 N z⌋₊, Nat.floor_le h0, Nat.lt_floor_add_one _⟩
  have hε := shiftEps38_pos c.property.1 c.property.2.1
  calc ∫⁻ z, ENNReal.ofReal (Real.exp (-fullEnergy38 c N z)) ∂planeVolume N
      = ∫⁻ z in Set.univ, ENNReal.ofReal (Real.exp (-fullEnergy38 c N z)) ∂planeVolume N := by
        rw [Measure.restrict_univ]
    _ ≤ ∫⁻ z in ⋃ k : ℕ, {z | (k : ℝ) ≤ planeH1Norm38 N z ∧ planeH1Norm38 N z < (k : ℝ) + 1},
          ENNReal.ofReal (Real.exp (-fullEnergy38 c N z)) ∂planeVolume N :=
        lintegral_mono_set hcover
    _ ≤ ∑' k : ℕ, ∫⁻ z in {z | (k : ℝ) ≤ planeH1Norm38 N z ∧ planeH1Norm38 N z < (k : ℝ) + 1},
          ENNReal.ofReal (Real.exp (-fullEnergy38 c N z)) ∂planeVolume N :=
        lintegral_iUnion_le _ _
    _ ≤ ∑' k : ℕ, P * ENNReal.ofReal (Real.exp (Cs' * ((k : ℝ) + 2) ^ 9 -
          shiftEps38 lo up * shellLevel38 g' R₀' k)) := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        set Sk : Set (FourierPlane N) :=
          {z | (k : ℝ) ≤ planeH1Norm38 N z ∧ planeH1Norm38 N z < (k : ℝ) + 1} with hSk
        have hSkm : MeasurableSet Sk :=
          (measurableSet_le measurable_const hmeas.measurable).inter
            (measurableSet_lt hmeas.measurable measurable_const)
        have hEm : Measurable fun z => ENNReal.ofReal
            (Real.exp (-fullEnergy38 (shiftedCoefficients38 c) N z)) :=
          (Real.continuous_exp.comp
            (continuous_fullEnergy38 (shiftedCoefficients38 c) N).neg).measurable.ennreal_ofReal
        have hlev : ∀ z ∈ Sk, shellLevel38 g' R₀' k ≤ reservedEnergy38 c N z := by
          intro z hz
          unfold shellLevel38
          split_ifs with h
          · exact hcoer z k h hz.1
          · exact reservedEnergy38_nonneg c N z
        calc ∫⁻ z in Sk, ENNReal.ofReal (Real.exp (-fullEnergy38 c N z)) ∂planeVolume N
            ≤ ∫⁻ z in Sk, ENNReal.ofReal (Real.exp (-(shiftEps38 lo up * shellLevel38 g' R₀' k))) *
                ENNReal.ofReal (Real.exp (-fullEnergy38 (shiftedCoefficients38 c) N z))
                ∂planeVolume N := by
              refine setLIntegral_mono' hSkm fun z hz => ?_
              rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
              apply ENNReal.ofReal_le_ofReal
              apply Real.exp_le_exp.mpr
              have := fullEnergy38_split c N z
              have := mul_le_mul_of_nonneg_left (hlev z hz) hε.le
              linarith
          _ = ENNReal.ofReal (Real.exp (-(shiftEps38 lo up * shellLevel38 g' R₀' k))) *
                ∫⁻ z in Sk, ENNReal.ofReal (Real.exp (-fullEnergy38 (shiftedCoefficients38 c) N z))
                  ∂planeVolume N := lintegral_const_mul _ hEm
          _ ≤ ENNReal.ofReal (Real.exp (-(shiftEps38 lo up * shellLevel38 g' R₀' k))) *
                ∫⁻ z in {z | planeH1Norm38 N z < (k : ℝ) + 1},
                  ENNReal.ofReal (Real.exp (-fullEnergy38 (shiftedCoefficients38 c) N z))
                    ∂planeVolume N := by
              gcongr
              exact fun z hz => hz.2
          _ ≤ ENNReal.ofReal (Real.exp (-(shiftEps38 lo up * shellLevel38 g' R₀' k))) *
                (P * ENNReal.ofReal (Real.exp (Cs' * (1 + ((k : ℝ) + 1)) ^ 9))) := by
              gcongr
              exact hschur _ (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
          _ = P * ENNReal.ofReal (Real.exp (Cs' * ((k : ℝ) + 2) ^ 9 -
                shiftEps38 lo up * shellLevel38 g' R₀' k)) := by
              rw [mul_left_comm, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
              congr 3
              ring
    _ = P * ∑' k : ℕ, ENNReal.ofReal (Real.exp (Cs' * ((k : ℝ) + 2) ^ 9 -
          shiftEps38 lo up * shellLevel38 g' R₀' k)) := by
        rw [ENNReal.tsum_mul_left]


/-- **NEW-F07 / `F:thm:partition`.** For every `0 < c₋ ≤ c₊` there is a constant `C`, depending
only on `c₋, c₊`, such that for every admitted coefficient sequence `c` and every cutoff `N`
the relative partition function `Z_N(W) = 𝒵_{W,N}/∏_{|n|≤N}(π/a_n)` is at most `C`. -/
theorem uniformRelativePartition_bound38 (lo up : ℝ) (hl : 0 < lo) (hlu : lo ≤ up) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : BoundedCoefficients lo up) (N : ℕ), relativePartition38 c N ≤ C := by
  obtain ⟨Cs, hCs, hschur⟩ :=
    actualSchurBallIntegral_fullEnergy38 (3 * lo / 4) up (by linarith) (by linarith)
  obtain ⟨g, R₀, hg, hR₀, hcoer⟩ := reservedEnergy_coercive38 lo up hl hlu
  obtain ⟨C₀, hC₀, hfree⟩ := freeNormalizer_shifted_le38
  have hε := shiftEps38_pos hl hlu
  have hsum := shellSeries_summable38 (C := Cs) (g := g) (ε := shiftEps38 lo up) R₀ hCs.le hg hε
  set S : ℝ := ∑' k : ℕ, Real.exp (Cs * ((k : ℝ) + 2) ^ 9 -
    shiftEps38 lo up * shellLevel38 g R₀ k) with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun k => (Real.exp_pos _).le
  refine ⟨C₀ * S + 1, by positivity, fun c N => ?_⟩
  have hD := freeNormalizer38_pos c N
  have hI := integrable_exp_neg_fullEnergy38 c N
  have hdom := shell_lintegral_bound38 c N
    (∏ i : Fin (2 * N + 1), ENNReal.ofReal (Real.pi /
      fullWeightRate (shiftedCoefficients38 c).val (modeIndex N i))) Cs g R₀
    (fun R hR => hschur (shiftedCoefficients38 c) R hR N)
    (fun z R h1 h2 => hcoer c N z R h1 h2)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => (Real.exp_pos _).le) hsum,
    ← ENNReal.ofReal_prod_of_nonneg (fun i _ => div_nonneg Real.pi_pos.le
      (fullWeightRate_pos38 (shiftedCoefficients38 c) _).le)] at hdom
  rw [← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => div_nonneg Real.pi_pos.le
      (fullWeightRate_pos38 (shiftedCoefficients38 c) _).le),
    ← ofReal_integral_eq_lintegral_ofReal hI
      (Filter.Eventually.of_forall fun z => (Real.exp_pos _).le)] at hdom
  have hdom' : fullPartition38 c N ≤ freeNormalizer38 (shiftedCoefficients38 c) N * S := by
    have := (ENNReal.ofReal_le_ofReal_iff (by
      have := freeNormalizer38_pos (shiftedCoefficients38 c) N
      positivity)).mp hdom
    exact this
  have h2 := hfree lo up c N
  have h3 : fullPartition38 c N ≤ C₀ * S * freeNormalizer38 c N := by
    calc fullPartition38 c N ≤ freeNormalizer38 (shiftedCoefficients38 c) N * S := hdom'
      _ ≤ (C₀ * freeNormalizer38 c N) * S := mul_le_mul_of_nonneg_right h2 hS0
      _ = _ := by ring
  unfold relativePartition38
  rw [div_le_iff₀ hD]
  nlinarith

end NlsGge.HierarchyRiccati.Core

end
