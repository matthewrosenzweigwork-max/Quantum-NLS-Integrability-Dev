import NlsGge.GK38.XiSqCandidates
import NlsGge.GK38.ActionRealBridge
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.Connected.LocallyConnected

set_option autoImplicit false
open Set Filter Topology Metric
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

def a5RealGapPerturbation38 (u : PhysicalL2) (n : ℤ) (s : ℝ) : PhysicalL2 :=
  u + s • (a5OpenWitness38 n - u)

def a5GapOpeningLine38 (u : PhysicalL2) (n : ℤ) (z : ℂ) : PotPair :=
  realSlice u + z • (realSlice (a5OpenWitness38 n) - realSlice u)

theorem a5GapOpeningLine_ofReal38 (u : PhysicalL2) (n : ℤ) (s : ℝ) :
    a5GapOpeningLine38 u n (s : ℂ) = realSlice (a5RealGapPerturbation38 u n s) := by
  rw [a5RealGapPerturbation38, realSlice_add, realSlice_smul_real, realSlice_sub]
  unfold a5GapOpeningLine38
  congr 1

theorem a5GapOpeningLine_analyticAt38 (u : PhysicalL2) (n : ℤ) (z : ℂ) :
    AnalyticAt ℂ (a5GapOpeningLine38 u n) z := by
  change AnalyticAt ℂ (fun w : ℂ => realSlice u +
    w • (realSlice (a5OpenWitness38 n) - realSlice u)) z
  exact analyticAt_const.add (analyticAt_id.smul analyticAt_const)

theorem a5OfReal_punctured_tendsto38 :
    Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
  apply tendsto_inf.2
  refine ⟨Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
  apply tendsto_principal.2
  filter_upwards [self_mem_nhdsWithin] with s hs
  simpa only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_eq_zero] using hs

/-- Actual REAL open-gap approximants, earned through one complex scalar line. -/
theorem a5RealGap_perturb_ne_eventually38 (u : PhysicalL2) (n : ℤ) :
    ∀ᶠ s in 𝓝[≠] (0 : ℝ),
      gamma2 (realSlice (a5RealGapPerturbation38 u n s)) n ≠ 0 := by
  let L := a5GapOpeningLine38 u n
  let U : Set ℂ := L ⁻¹' gkW
  let B := connectedComponentIn U 0
  have hreal (s : ℝ) : (s : ℂ) ∈ U := by
    change a5GapOpeningLine38 u n (s : ℂ) ∈ gkW
    rw [a5GapOpeningLine_ofReal38]
    exact realSlice_mem_gkW _
  have haxis : IsPreconnected (Set.range (fun s : ℝ => (s : ℂ))) :=
    isPreconnected_range Complex.continuous_ofReal
  have haxisB : Set.range (fun s : ℝ => (s : ℂ)) ⊆ B :=
    haxis.subset_connectedComponentIn ⟨0, by simp⟩ (by rintro _ ⟨s, rfl⟩; exact hreal s)
  have h0B : (0 : ℂ) ∈ B := haxisB ⟨0, by simp⟩
  have h1B : (1 : ℂ) ∈ B := haxisB ⟨1, by simp⟩
  have hF : AnalyticOnNhd ℂ (fun z => gamma2 (L z) n) B := by
    intro z hz
    exact AnalyticAt.comp (g := fun φ : PotPair => gamma2 φ n) (f := L)
      (gamma2_analytic n (L z) (connectedComponentIn_subset U 0 hz))
      (a5GapOpeningLine_analyticAt38 u n z)
  have hnotzero : ¬ (∀ᶠ z in 𝓝 (0 : ℂ), gamma2 (L z) n = 0) := by
    intro hzero
    have heq : Set.EqOn (fun z => gamma2 (L z) n) (fun _ => 0) B :=
      hF.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
        isPreconnected_connectedComponentIn h0B hzero
    have hL1 : L 1 = realSlice (a5OpenWitness38 n) := by simp [L, a5GapOpeningLine38]
    have h1 := heq h1B
    change gamma2 (L 1) n = 0 at h1
    rw [hL1, a5OpenWitness_gamma2_38] at h1
    norm_num at h1
  have hne := (hF 0 h0B).eventually_eq_zero_or_eventually_ne_zero.resolve_left hnotzero
  have hre := a5OfReal_punctured_tendsto38.eventually hne
  filter_upwards [hre] with s hs
  change gamma2 (a5GapOpeningLine38 u n (s : ℂ)) n ≠ 0 at hs
  rwa [a5GapOpeningLine_ofReal38] at hs

/-- The actual real bridge and scalar semicircle lower bound earn the open-gap value. -/
theorem xiSqCandidate_real_ge_one_of_ne38 (n : ℤ) (g : PotPair → ℂ)
    (hg : XiSqSpec38 n g) (u : PhysicalL2) (hne : gamma2 (realSlice u) n ≠ 0) :
    (g (realSlice u)).im = 0 ∧ 1 ≤ (g (realSlice u)).re := by
  let d : ℝ := (actualGapUpperAllE02_38 u n - actualGapLowerAllE02_38 u n)^2
  have hgamma : gamma2 (realSlice u) n = (d : ℂ) := (tauGamma_real38 u n).2
  have hdne : d ≠ 0 := by
    intro hd
    exact hne (by simpa only [hd, Complex.ofReal_zero] using hgamma)
  have hd : 0 < d := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hdne)
  have hprod := xiSqCandidate_multiplied38 n g hg (realSlice u) (realSlice_mem_gkW u)
  rw [hgamma, ActionRealBridge.action_real_bridge] at hprod
  have him : d * (g (realSlice u)).im = 0 := by
    simpa [Complex.mul_im] using congrArg Complex.im hprod
  have hre : d * (g (realSlice u)).re = 4 * actualGapActionAllE02_38 u n := by
    simpa [Complex.mul_re] using congrArg Complex.re hprod
  refine ⟨(mul_eq_zero.mp him).resolve_left hdne, ?_⟩
  apply (mul_le_mul_iff_right₀ hd).mp
  rw [mul_one, hre]
  have hbound := actualGapAction_ge_sq_div_four_all_E02_38 u n
  change d / 4 ≤ actualGapActionAllE02_38 u n at hbound
  linarith

/-- All actual real potentials and all integer labels, INCLUDING collapsed gaps. -/
theorem xiSqCandidate_real_ge_one38 (n : ℤ) (g : PotPair → ℂ)
    (hg : XiSqSpec38 n g) (u : PhysicalL2) :
    (g (realSlice u)).im = 0 ∧ 1 ≤ (g (realSlice u)).re := by
  let F : ℝ → ℂ := fun s => g (realSlice (a5RealGapPerturbation38 u n s))
  have hpath : Continuous (fun s : ℝ => realSlice (a5RealGapPerturbation38 u n s)) := by
    exact realSlice.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))
  have hg0 : ContinuousAt g (realSlice (a5RealGapPerturbation38 u n 0)) := by
    simpa only [a5RealGapPerturbation38, zero_smul, add_zero] using
      (hg.1 (realSlice u) (realSlice_mem_gkW u)).continuousAt
  have hF : ContinuousAt F 0 := ContinuousAt.comp'
    (f := fun s : ℝ => realSlice (a5RealGapPerturbation38 u n s))
    (g := g) (x := 0) hg0 hpath.continuousAt
  have hclosed : IsClosed {z : ℂ | z.im = 0 ∧ 1 ≤ z.re} :=
    (isClosed_eq Complex.continuous_im continuous_const).inter
      (isClosed_le continuous_const Complex.continuous_re)
  have hevent : ∀ᶠ s in 𝓝[≠] (0 : ℝ), F s ∈ {z : ℂ | z.im = 0 ∧ 1 ≤ z.re} := by
    filter_upwards [a5RealGap_perturb_ne_eventually38 u n] with s hs
    exact xiSqCandidate_real_ge_one_of_ne38 n g hg (a5RealGapPerturbation38 u n s) hs
  have hmem := hclosed.mem_of_tendsto (hF.tendsto.mono_left nhdsWithin_le_nhds) hevent
  change (F 0).im = 0 ∧ 1 ≤ (F 0).re at hmem
  simpa only [F, a5RealGapPerturbation38, zero_smul, add_zero] using hmem

/-- The exact selected FULL positivity contract; no existence or noncollapse premise. -/
theorem a5XiSqRealPositive38 : XiSqRealPositive38 := by
  intro g hg u n
  have h := xiSqCandidate_real_ge_one38 n (g n) (hg n) u
  exact ⟨h.1, lt_of_lt_of_le (by norm_num) h.2⟩

end
end NlsGge.GK38
