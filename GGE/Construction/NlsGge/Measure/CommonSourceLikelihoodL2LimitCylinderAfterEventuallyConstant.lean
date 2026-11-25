import NlsGge.Measure.CommonSourceLikelihoodFiniteCylinderAfterPrerequisite
import NlsGge.Measure.CommonSourceLikelihoodL2LimitProbability
import NlsGge.Measure.TendstoEventuallyConstant
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace NlsGge.Measure

private theorem finiteRestriction_projection_eq_rawEval
    (N : ℕ) (U : Finset ℤ)
    (hU : ∀ n ∈ U, n ∈ NlsGge.Pilot.symmetricModes N) :
    (fun z : ℤ → ℂ => fun u : U =>
      finiteModeRestrictionAfterRaw N U hU
        (fun i : Fin (2 * N + 1) => z (NlsGge.Pilot.modeIndex N i)) u) =
      fun z u => z u.1 := by
  funext z u
  have hlo : (-(N : ℤ)) ≤ u.1 := by
    simpa [NlsGge.Pilot.symmetricModes] using
      (Finset.mem_Icc.mp (hU u.1 u.2)).1
  have hhi : u.1 ≤ (N : ℤ) := by
    simpa [NlsGge.Pilot.symmetricModes] using
      (Finset.mem_Icc.mp (hU u.1 u.2)).2
  have hmode := Classical.choose_spec
    (NlsGge.Pilot.modeIndex_covers N u.1 hlo hhi)
  change z (NlsGge.Pilot.modeIndex N
      (Classical.choose (NlsGge.Pilot.modeIndex_covers N u.1 hlo hhi))) = z u.1
  rw [hmode]

private theorem symmetricModes_subset_of_le {M N : ℕ} (hMN : M ≤ N) :
    NlsGge.Pilot.symmetricModes M ⊆ NlsGge.Pilot.symmetricModes N := by
  intro n hn
  have hn' := Finset.mem_Icc.mp (by simpa [NlsGge.Pilot.symmetricModes] using hn)
  have hMN' : (M : ℤ) ≤ (N : ℤ) := by exact_mod_cast hMN
  apply Finset.mem_Icc.mpr
  constructor <;> dsimp [NlsGge.Pilot.symmetricModes] at * <;> omega

/-- The actual CM likelihood limit integrates on every finite raw-coordinate
cylinder to the corresponding translated finite Gaussian marginal. The theorem
uses L² convergence against a cylinder indicator; it makes no full-space RN
claim by itself. -/
theorem exists_actualSourceCMCommonLikelihoodL2Limit_finiteCylinder_afterEventuallyConstant
    {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (x : NlsGge.Pilot.WeightedRealHilbert
      (NlsGge.Pilot.cmModeWeight c))
    (M : ℕ) (U : Finset ℤ)
    (hU : ∀ n ∈ U, n ∈ NlsGge.Pilot.symmetricModes M)
    (B : Set ((u : U) → ℂ)) (hB : MeasurableSet B) :
    ∃ L : MeasureTheory.Lp ℝ 2
        (NlsGge.Measure.fullWeightSequenceGaussian c.val),
      Tendsto
        (NlsGge.Measure.commonSourceLikelihoodLpSequenceOfMemLp
          lower upper c (NlsGge.Measure.actualSourceCMSequence c x)
          (fun N => NlsGge.Measure.memLp_commonSourceLikelihoodReal c N
            (NlsGge.Measure.actualSourceCMSequence c x)))
        atTop (nhds L) ∧
      (∀ᵐ z ∂NlsGge.Measure.fullWeightSequenceGaussian c.val, 0 ≤ L z) ∧
      (∫ z : ℤ → ℂ, L z ∂NlsGge.Measure.fullWeightSequenceGaussian c.val) = 1 ∧
      ENNReal.ofReal
          (∫ z in
            (fun z : ℤ → ℂ => fun u : U => z u.1) ⁻¹' B,
            L z ∂NlsGge.Measure.fullWeightSequenceGaussian c.val) =
        (Measure.pi (fun u : U =>
          (complexGaussian (fullWeightRate c.val u.1)).map
            (fun z : ℂ => z + NlsGge.Measure.actualSourceCMSequence c x u.1))) B := by
  classical
  obtain ⟨L, hconv, hnonneg, hmass⟩ :=
    exists_actualSourceCMCommonLikelihoodL2Limit_probability c x
  let μ : Measure (ℤ → ℂ) := fullWeightSequenceGaussian c.val
  let h : ℤ → ℂ := actualSourceCMSequence c x
  let hmem : ∀ N : ℕ, MemLp
      (fun z : ℤ → ℂ => commonSourceLikelihoodReal lower upper c N h z)
      2 μ := fun N => memLp_commonSourceLikelihoodReal c N h
  let u : ℕ → Lp ℝ 2 μ :=
    commonSourceLikelihoodLpSequenceOfMemLp lower upper c h hmem
  have hconv' : Tendsto u atTop (nhds L) := by
    simpa [u, hmem, h, μ] using hconv
  let A : Set (ℤ → ℂ) := (fun z : ℤ → ℂ => fun v : U => z v.1) ⁻¹' B
  have hA : MeasurableSet A := by
    apply hB.preimage
    fun_prop
  have hμA : μ A ≠ ∞ := measure_ne_top μ A
  let g : Lp ℝ 2 μ := MeasureTheory.indicatorConstLp 2 hA hμA (1 : ℝ)
  have hg : (fun z : ℤ → ℂ => g z) =ᵐ[μ]
      A.indicator (fun _ : ℤ → ℂ => (1 : ℝ)) := by
    simpa [g] using
      (MeasureTheory.indicatorConstLp_coeFn
        (p := (2 : ℝ≥0∞)) (hs := hA) (hμs := hμA) (c := (1 : ℝ)))
  have hrepr (N : ℕ) : ∀ᵐ z ∂μ,
      u N z = commonSourceLikelihoodReal lower upper c N h z := by
    filter_upwards [(hmem N).coeFn_toLp] with z hz
    simpa [u, commonSourceLikelihoodLpSequenceOfMemLp,
      commonSourceLikelihoodLpOfMemLp] using hz
  have hpair (N : ℕ) :
      inner ℝ (u N) g =
        ∫ z in A, commonSourceLikelihoodReal lower upper c N h z ∂μ := by
    rw [MeasureTheory.L2.inner_def]
    calc
      (∫ z : ℤ → ℂ, inner ℝ (u N z) (g z) ∂μ) =
          ∫ z : ℤ → ℂ,
            A.indicator (fun z => commonSourceLikelihoodReal lower upper c N h z) z ∂μ := by
              apply integral_congr_ae
              filter_upwards [hrepr N, hg] with z hz hgz
              by_cases hzA : z ∈ A <;> simp [hz, hgz, hzA]
      _ = ∫ z in A, commonSourceLikelihoodReal lower upper c N h z ∂μ :=
            integral_indicator hA
  have hpairLimit : Tendsto (fun N : ℕ => inner ℝ (u N) g) atTop
      (nhds (inner ℝ L g)) := by
    exact hconv'.inner (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => g) atTop (nhds g))
  let target : ℝ≥0∞ :=
    (Measure.pi (fun v : U =>
      (complexGaussian (fullWeightRate c.val v.1)).map
        (fun z : ℂ => z + h v.1))) B
  have htarget_lt : target < ∞ := measure_lt_top _ B
  have htarget_ne : target ≠ ∞ := ne_of_lt htarget_lt
  have hpair_eventually : ∀ᶠ N in atTop, inner ℝ (u N) g = target.toReal := by
    filter_upwards [eventually_ge_atTop M] with N hMN
    have hUN : ∀ n ∈ U, n ∈ NlsGge.Pilot.symmetricModes N := by
      intro n hn
      exact symmetricModes_subset_of_le hMN (hU n hn)
    have hraw := finiteRestriction_projection_eq_rawEval N U hUN
    have hEvent :
        ((finiteModeRestrictionAfterRaw N U hUN) ∘
          (fun z : ℤ → ℂ => fun i : Fin (2 * N + 1) =>
            z (NlsGge.Pilot.modeIndex N i))) ⁻¹' B = A := by
      change ((finiteModeRestrictionAfterRaw N U hUN) ∘
        (fun z : ℤ → ℂ => fun i : Fin (2 * N + 1) =>
          z (NlsGge.Pilot.modeIndex N i))) ⁻¹' B = A
      have heq : ((finiteModeRestrictionAfterRaw N U hUN) ∘
        (fun z : ℤ → ℂ => fun i : Fin (2 * N + 1) =>
          z (NlsGge.Pilot.modeIndex N i))) =
          (fun z : ℤ → ℂ => fun v : U => z v.1) := hraw
      rw [heq]
    have hcut :
        (∫⁻ z in A, ENNReal.ofReal
          (commonSourceLikelihoodReal lower upper c N h z) ∂μ) = target := by
      have hc := commonSourceLikelihood_cutoff_finiteCylinder
          lower upper c c.property.1
          (fun j => (c.property.2.2 j).1)
          (fun j => (c.property.2.2 j).2)
          N h U hUN B hB
      change (∫⁻ z in
        ((finiteModeRestrictionAfterRaw N U hUN) ∘
          (fun z : ℤ → ℂ => fun i : Fin (2 * N + 1) =>
            z (NlsGge.Pilot.modeIndex N i))) ⁻¹' B,
        ENNReal.ofReal (commonSourceLikelihoodReal lower upper c N h z) ∂μ) = target at hc
      rw [hEvent] at hc
      exact hc
    have hconvert :
        ENNReal.ofReal
          (∫ z in A, commonSourceLikelihoodReal lower upper c N h z ∂μ) =
        ∫⁻ z in A, ENNReal.ofReal
          (commonSourceLikelihoodReal lower upper c N h z) ∂μ := by
      exact ofReal_integral_eq_lintegral_ofReal
        (((hmem N).integrable (by norm_num)).restrict)
        (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _)
    have hreal :
        (∫ z in A, commonSourceLikelihoodReal lower upper c N h z ∂μ) = target.toReal := by
      have ht := congrArg ENNReal.toReal (hconvert.trans hcut)
      have hnonnegIntegral :
          0 ≤ ∫ z in A, commonSourceLikelihoodReal lower upper c N h z ∂μ :=
        integral_nonneg_of_ae (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _)
      rw [ENNReal.toReal_ofReal hnonnegIntegral] at ht
      exact ht
    rw [hpair N, hreal]
  have hinner : inner ℝ L g = target.toReal :=
    tendsto_limit_eq_of_eventually_constant
      (fun N : ℕ => inner ℝ (u N) g) (inner ℝ L g) target.toReal
      hpairLimit hpair_eventually
  have hlimitPair : inner ℝ L g = ∫ z in A, L z ∂μ := by
    rw [MeasureTheory.L2.inner_def]
    calc
      (∫ z : ℤ → ℂ, inner ℝ (L z) (g z) ∂μ) =
          ∫ z : ℤ → ℂ, A.indicator (fun z => L z) z ∂μ := by
        apply integral_congr_ae
        filter_upwards [hg] with z hgz
        by_cases hzA : z ∈ A <;> simp [hgz, hzA]
      _ = ∫ z in A, L z ∂μ := integral_indicator hA
  have hlimitInt : (∫ z in A, L z ∂μ) = target.toReal := by
    rw [← hlimitPair]
    exact hinner
  refine ⟨L, ?_, ?_, ?_, ?_⟩
  · simpa [u, hmem, h, μ] using hconv'
  · simpa [μ] using hnonneg
  · simpa [μ] using hmass
  · rw [hlimitInt]
    exact ENNReal.ofReal_toReal htarget_ne

end NlsGge.Measure
