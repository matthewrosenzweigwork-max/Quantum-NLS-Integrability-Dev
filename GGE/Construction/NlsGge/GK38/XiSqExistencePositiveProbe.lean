import NlsGge.GK38.XiSqExistence
import NlsGge.GK38.XiSqRealPositive

set_option autoImplicit false
open Set Filter Topology
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.AblowitzLadik
namespace A5ExistencePositiveFixture
noncomputable section

theorem existence : XiSqExistence38 := a5XiSqExistence38
theorem realPositive : XiSqRealPositive38 := a5XiSqRealPositive38

theorem allReal_ge_one (n : ℤ) (g : PotPair → ℂ) (hg : XiSqSpec38 n g)
    (u : PhysicalL2) : (g (realSlice u)).im = 0 ∧ 1 ≤ (g (realSlice u)).re :=
  xiSqCandidate_real_ge_one38 n g hg u

/-- Actual all-label amplitude curve, retaining negative and zero amplitudes. -/
theorem actual_plane_gap_square (n : ℤ) (t : ℝ) :
    gamma2 (realSlice (t • a5OpenWitness38 n)) n = 4 * (t : ℂ)^2 := by
  have hscale : t • a5OpenWitness38 n =
      planeL2 n.natAbs (planeWaveCoeff38 n.natAbs (-n) t) := by
    symm
    simpa only [mul_one, a5OpenWitness38] using planeWave_L2_smul38 n.natAbs (-n) t 1
  have hguard : (-n).natAbs ≤ n.natAbs := by simp
  have hends := planeWaveOpenEndpoints38 n.natAbs (-n) hguard t
  simp only [neg_neg] at hends
  rw [hscale, (tauGamma_real38 _ n).2, hends.1, hends.2]
  have hreal : ((-Real.pi * (-n) + |t|) - (-Real.pi * (-n) - |t|))^2 = 4 * t^2 := by
    nlinarith [sq_abs t]
  exact_mod_cast hreal

theorem actual_plane_action (n : ℤ) (t : ℝ) :
    actualGapActionAllE02_38 (t • a5OpenWitness38 n) n = t^2 := by
  have hscale : t • a5OpenWitness38 n =
      planeL2 n.natAbs (planeWaveCoeff38 n.natAbs (-n) t) := by
    symm
    simpa only [mul_one, a5OpenWitness38] using planeWave_L2_smul38 n.natAbs (-n) t 1
  rw [hscale]
  have hguard : (-n).natAbs ≤ n.natAbs := by simp
  simpa using planeWaveActionProbe38 n.natAbs (-n) hguard t n

/-- Division occurs only at an earned nonzero real amplitude, never at collapse. -/
theorem candidate_actual_plane_one (n : ℤ) (g : PotPair → ℂ)
    (hg : XiSqSpec38 n g) (t : ℝ) (ht : t ≠ 0) :
    g (realSlice (t • a5OpenWitness38 n)) = 1 := by
  have hprod := xiSqCandidate_multiplied38 n g hg
    (realSlice (t • a5OpenWitness38 n)) (realSlice_mem_gkW _)
  rw [actual_plane_gap_square, NlsGge.GK38.ActionRealBridge.action_real_bridge,
    actual_plane_action] at hprod
  have hc : (4 : ℂ) * (t : ℂ)^2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr ht))
  apply mul_left_cancel₀ hc
  simpa only [Complex.ofReal_pow, mul_one] using hprod

/-- The FULL collapsed free value follows by real amplitude continuity, with no division by zero. -/
theorem candidate_free_one (n : ℤ) (g : PotPair → ℂ) (hg : XiSqSpec38 n g) :
    g (0 : PotPair) = 1 := by
  let F : ℝ → ℂ := fun t => g (realSlice (t • a5OpenWitness38 n))
  have hpath : Continuous (fun t : ℝ => realSlice (t • a5OpenWitness38 n)) :=
    realSlice.continuous.comp (continuous_id.smul continuous_const)
  have hzero : realSlice ((0 : ℝ) • a5OpenWitness38 n) = (0 : PotPair) := by
    rw [zero_smul, realSlice_zero]
  have hg0 : ContinuousAt g (realSlice ((0 : ℝ) • a5OpenWitness38 n)) := by
    rw [hzero]
    exact (hg.1 0 free_mem_gkW).continuousAt
  have hF : ContinuousAt F 0 := ContinuousAt.comp'
    (f := fun t : ℝ => realSlice (t • a5OpenWitness38 n)) (g := g) hg0 hpath.continuousAt
  have hevt : ∀ᶠ t in 𝓝[≠] (0 : ℝ), F t = 1 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact candidate_actual_plane_one n g hg t ht
  have hconst : Tendsto F (𝓝[≠] (0 : ℝ)) (𝓝 (1 : ℂ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hevt] with t ht
    exact ht.symm
  have heq : F 0 = 1 := tendsto_nhds_unique
    (hF.tendsto.mono_left nhdsWithin_le_nhds) hconst
  simpa only [F, zero_smul, realSlice_zero] using heq

/-- A concrete witness exists for every signed index, including its actual collapsed free value. -/
theorem actual_global_extension (n : ℤ) :
    ∃ g : PotPair → ℂ, XiSqSpec38 n g ∧ g 0 = 1 ∧
      ∀ u : PhysicalL2, (g (realSlice u)).im = 0 ∧ 1 ≤ (g (realSlice u)).re := by
  obtain ⟨g, hg, _⟩ := a5XiSqExists38 n
  exact ⟨g, hg, candidate_free_one n g hg, fun u => allReal_ge_one n g hg u⟩

end
end A5ExistencePositiveFixture
