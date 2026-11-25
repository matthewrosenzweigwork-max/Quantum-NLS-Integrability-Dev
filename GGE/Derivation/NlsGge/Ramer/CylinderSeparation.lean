import NlsGge.Measure.CountableGaussian
import NlsGge.Sobolev.SourceWeighted
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# Smooth compactly supported cylinder functions separate `L¹(γ_c)`

If `η ∈ L¹` of the full-weight countable Gaussian law on `ℤ → ℂ` annihilates every
`φ(z_{-N}, …, z_N)` with `φ` smooth and compactly supported on the Fourier plane, then `η = 0`
almost everywhere.  Proof: the finite-window conditional expectations vanish (the head law has a
strictly positive continuous density against the plane volume, and mathlib's smooth-test-function
lemma applies), then Lévy's upward theorem.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff ENNReal NNReal

namespace NlsGge.Ramer

open NlsGge.Pilot NlsGge.Measure

/-- The window projection `z ↦ (z_{-N}, …, z_N)`. -/
def windowProj (N : ℕ) (z : ℤ → ℂ) : FourierPlane N := fun i => z (modeIndex N i)

lemma measurable_windowProj (N : ℕ) : Measurable (windowProj N) :=
  Measurable.of_eval (fun i => measurable_pi_apply (modeIndex N i))

set_option warn.classDefReducibility false in
/-- The window σ-algebra. -/
def windowSigma (N : ℕ) : MeasurableSpace (ℤ → ℂ) :=
  MeasurableSpace.comap (windowProj N) inferInstance

lemma windowSigma_le_pi (N : ℕ) : windowSigma N ≤ (inferInstance : MeasurableSpace (ℤ → ℂ)) :=
  (measurable_windowProj N).comap_le

/-- Evaluation at an integer is measurable for the `M`-window σ-algebra once `|n| ≤ M`. -/
lemma measurable_eval_windowSigma (M : ℕ) (n : ℤ) (hlo : -(M : ℤ) ≤ n) (hhi : n ≤ (M : ℤ)) :
    @Measurable (ℤ → ℂ) ℂ (windowSigma M) _ (fun z => z n) := by
  obtain ⟨j, hj⟩ := modeIndex_covers M n hlo hhi
  have : (fun z : ℤ → ℂ => z n) = (fun x : FourierPlane M => x j) ∘ windowProj M := by
    ext z; simp [windowProj, hj]
  rw [this]
  exact (measurable_pi_apply j).comp (comap_measurable (windowProj M))

lemma windowSigma_mono : Monotone windowSigma := by
  intro N M hNM
  refine (measurable_iff_comap_le (m₁ := windowSigma M)).1 ?_
  refine @Measurable.of_eval _ _ _ (windowSigma M) _ _ (fun i => ?_)
  have hb := modeIndex_bounds N i
  exact measurable_eval_windowSigma M _ (by have : (N : ℤ) ≤ M := by exact_mod_cast hNM
                                            omega)
    (by have : (N : ℤ) ≤ M := by exact_mod_cast hNM
        omega)

/-- The window filtration on `ℤ → ℂ`. -/
def windowFiltration : Filtration ℕ (inferInstance : MeasurableSpace (ℤ → ℂ)) where
  seq := windowSigma
  mono' := windowSigma_mono
  le' := windowSigma_le_pi

lemma iSup_windowSigma : (⨆ N, windowSigma N) = (inferInstance : MeasurableSpace (ℤ → ℂ)) := by
  refine le_antisymm (iSup_le windowSigma_le_pi) ?_
  show (⨆ a : ℤ, MeasurableSpace.comap (fun z : ℤ → ℂ => z a) inferInstance) ≤ _
  refine iSup_le (fun n => ?_)
  have hN : -((n.natAbs : ℕ) : ℤ) ≤ n ∧ n ≤ ((n.natAbs : ℕ) : ℤ) := by omega
  refine le_trans ?_ (le_iSup windowSigma n.natAbs)
  exact (measurable_iff_comap_le (m₁ := windowSigma n.natAbs)).1
    (measurable_eval_windowSigma _ n hN.1 hN.2)

/-- Positive Gaussian density on the plane, as a real function. -/
def headDensity (c : ℕ → ℝ) (N : ℕ) (x : FourierPlane N) : ℝ :=
  ∏ i, (fullWeightRate c (modeIndex N i) / Real.pi) *
    Real.exp (-fullWeightRate c (modeIndex N i) * ‖x i‖ ^ 2)

lemma headDensity_pos {lower upper : ℝ} (c : BoundedCoefficients lower upper) (N : ℕ)
    (x : FourierPlane N) : 0 < headDensity c.val N x := by
  unfold headDensity
  refine Finset.prod_pos (fun i _ => ?_)
  have hp : 0 < fullWeightRate c.val (modeIndex N i) :=
    fullWeightRate_pos lower upper c.val c.property.1 (fun j => (c.property.2.2 j).1)
      (fun j => (c.property.2.2 j).2) _
  positivity

lemma measurable_headDensity (c : ℕ → ℝ) (N : ℕ) : Measurable (headDensity c N) :=
  measurable_fullWeightFourierGaussianPDF N c

/-- Step: if `η ∈ L¹` annihilates all smooth compactly supported window cylinders of size `N`,
then its `N`-window conditional expectation vanishes a.e. -/
lemma condExp_window_eq_zero {lower upper : ℝ} (c : BoundedCoefficients lower upper)
    (η : (ℤ → ℂ) → ℝ) (hη : Integrable η (fullWeightSequenceGaussian c.val)) (N : ℕ)
    (h : ∀ φ : FourierPlane N → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ z, φ (windowProj N z) * η z ∂(fullWeightSequenceGaussian c.val) = 0) :
    (fullWeightSequenceGaussian c.val)[η | windowSigma N]
      =ᵐ[fullWeightSequenceGaussian c.val] 0 := by
  set μ := fullWeightSequenceGaussian c.val with hμ
  have hm : windowSigma N ≤ (inferInstance : MeasurableSpace (ℤ → ℂ)) := windowSigma_le_pi N
  set m := μ[η | windowSigma N] with hmdef
  have hmsm : StronglyMeasurable[windowSigma N] m := stronglyMeasurable_condExp
  obtain ⟨g, hg, hgm⟩ := StronglyMeasurable.exists_eq_measurable_comp (f := windowProj N) hmsm
  have hmint : Integrable m μ := integrable_condExp
  have hν : μ.map (windowProj N) = fullWeightFourierGaussian N c.val :=
    fullWeightSequenceGaussian_map_modes N c.val
  have hdens : fullWeightFourierGaussian N c.val
      = (planeVolume N).withDensity (fun x => ((headDensity c.val N x).toNNReal : ℝ≥0∞)) :=
    fullWeightFourierGaussian_density lower upper c.val c.property.1
      (fun j => (c.property.2.2 j).1) (fun j => (c.property.2.2 j).2) N
  have hgint : Integrable g (μ.map (windowProj N)) := by
    rw [integrable_map_measure hg.aestronglyMeasurable (measurable_windowProj N).aemeasurable]
    rw [hgm] at hmint
    exact hmint
  have hρmeas : Measurable (fun x => (headDensity c.val N x).toNNReal) :=
    (measurable_headDensity c.val N).real_toNNReal
  rw [hν, hdens] at hgint
  have hfint : Integrable (fun x => (headDensity c.val N x).toNNReal • g x) (planeVolume N) :=
    (integrable_withDensity_iff_integrable_smul hρmeas).1 hgint
  -- annihilation of the pushed-forward function
  have hzero : ∀ φ : FourierPlane N → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ x, φ x • ((headDensity c.val N x).toNNReal • g x) ∂(planeVolume N) = 0 := by
    intro φ hφ hφc
    have hbd : ∃ C, ∀ x, ‖φ x‖ ≤ C := by
      obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hφc
      exact ⟨C, hC⟩
    obtain ⟨C, hC⟩ := hbd
    have hφm : Measurable φ := hφ.continuous.measurable
    have hφπ : StronglyMeasurable[windowSigma N] (fun z => φ (windowProj N z)) := by
      refine Measurable.stronglyMeasurable (mα := windowSigma N) ?_
      exact hφm.comp (comap_measurable (windowProj N))
    have hpull : μ[(fun z => φ (windowProj N z)) * η | windowSigma N]
        =ᵐ[μ] (fun z => φ (windowProj N z)) * m :=
      condExp_stronglyMeasurable_mul_of_bound hm hφπ hη C
        (Filter.Eventually.of_forall (fun z => hC _))
    have hint1 : ∫ z, φ (windowProj N z) * m z ∂μ = 0 := by
      have e1 : ∫ z, (φ (windowProj N z) * m z) ∂μ
          = ∫ z, μ[(fun z => φ (windowProj N z)) * η | windowSigma N] z ∂μ :=
        (integral_congr_ae hpull).symm
      rw [e1, integral_condExp hm]
      exact h φ hφ hφc
    have hint2 : ∫ z, φ (windowProj N z) * m z ∂μ
        = ∫ x, φ x * g x ∂(μ.map (windowProj N)) := by
      rw [integral_map (f := fun x => φ x * g x) (measurable_windowProj N).aemeasurable
        ((hφm.mul hg.measurable).aestronglyMeasurable)]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      simp [hgm]
    have hint3 : ∫ x, φ x * g x ∂(μ.map (windowProj N))
        = ∫ x, (headDensity c.val N x).toNNReal • (φ x * g x) ∂(planeVolume N) := by
      rw [hν, hdens, integral_withDensity_eq_integral_smul hρmeas]
    have : ∫ x, φ x • ((headDensity c.val N x).toNNReal • g x) ∂(planeVolume N) = 0 := by
      rw [← hint1, hint2, hint3]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      simp only [NNReal.smul_def, smul_eq_mul]
      ring
    exact this
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := planeVolume N)
    hfint.locallyIntegrable hzero
  have hgae : ∀ᵐ x ∂(planeVolume N), g x = 0 := by
    filter_upwards [hae] with x hx
    have hp := headDensity_pos c N x
    have hp' : ((headDensity c.val N x).toNNReal : ℝ) ≠ 0 := by
      rw [Real.coe_toNNReal _ hp.le]; exact hp.ne'
    rw [NNReal.smul_def, smul_eq_mul] at hx
    rcases mul_eq_zero.1 hx with h0 | h0
    · exact absurd h0 hp'
    · exact h0
  have hgν : ∀ᵐ x ∂(μ.map (windowProj N)), g x = 0 := by
    rw [hν, hdens]
    exact (withDensity_absolutelyContinuous _ _) hgae
  have hgμ : ∀ᵐ z ∂μ, g (windowProj N z) = 0 :=
    ae_of_ae_map (measurable_windowProj N).aemeasurable hgν
  filter_upwards [hgμ] with z hz
  simp [hgm, hz]

/-- **Cylinder separation.** -/
theorem ae_eq_zero_of_integral_cylinder_mul_eq_zero {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (η : (ℤ → ℂ) → ℝ)
    (hη : Integrable η (NlsGge.Measure.fullWeightSequenceGaussian c.val))
    (h : ∀ (N : ℕ) (φ : NlsGge.Pilot.FourierPlane N → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ z, φ (fun i => z (NlsGge.Pilot.modeIndex N i)) * η z
        ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val) = 0) :
    η =ᵐ[NlsGge.Measure.fullWeightSequenceGaussian c.val] 0 := by
  set μ := fullWeightSequenceGaussian c.val with hμ
  -- strongly measurable representative
  set η' := hη.1.mk η with hη'
  have hηη' : η =ᵐ[μ] η' := hη.1.ae_eq_mk
  have hη'sm : StronglyMeasurable η' := hη.1.stronglyMeasurable_mk
  have hη'int : Integrable η' μ := hη.congr hηη'
  have h' : ∀ (N : ℕ) (φ : FourierPlane N → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ z, φ (windowProj N z) * η' z ∂μ = 0 := by
    intro N φ hφ hφc
    rw [← h N φ hφ hφc]
    refine integral_congr_ae ?_
    filter_upwards [hηη'] with z hz
    rw [hz]; rfl
  have hcond : ∀ N : ℕ, μ[η' | windowFiltration N] =ᵐ[μ] 0 :=
    fun N => condExp_window_eq_zero c η' hη'int N (h' N)
  have hlim := Integrable.tendsto_ae_condExp (μ := μ) (ℱ := windowFiltration) hη'int
    (by
      have : StronglyMeasurable[(inferInstance : MeasurableSpace (ℤ → ℂ))] η' := hη'sm
      rw [show (⨆ n, windowFiltration n) = (inferInstance : MeasurableSpace (ℤ → ℂ)) from
        iSup_windowSigma]
      exact this)
  have hall : ∀ᵐ z ∂μ, ∀ N : ℕ, (μ[η' | windowFiltration N]) z = 0 := by
    rw [ae_all_iff]
    intro N
    filter_upwards [hcond N] with z hz using hz
  have hη'0 : η' =ᵐ[μ] 0 := by
    filter_upwards [hlim, hall] with z hz1 hz2
    have : Tendsto (fun n : ℕ => (μ[η' | windowFiltration n]) z) atTop (𝓝 0) := by
      simp only [hz2]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hz1 this
  exact hηη'.trans hη'0

end NlsGge.Ramer
