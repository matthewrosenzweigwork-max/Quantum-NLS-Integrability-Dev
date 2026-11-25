import QuantumNLS.BetheCoefficientTransform

/-!
# DEF-010: empirical rapidity measure and Cauchy transform
(`definitions.tex`, `def:report-10`; `DEFINITIONS_LEDGER.md:203`)

> Under the Born law, the empirical rapidity measure is `ν_N = N⁻¹ Σ_{j=1}^N δ_{q_j}`. For a finite positive
> measure `M` on `ℝ`, its Cauchy transform is `G_M(z) = ∫ (z−t)⁻¹ dM(t)` for nonreal `z`. This sign gives a
> negative imaginary part in the upper half-plane. The limiting unit-mass measure is denoted `μ_{κ,u}`; the
> full-mass measure is `M_{κ,u}`.

Realized here:
* `empiricalMeasure L c m = N⁻¹ Σ_j δ_{q_j(m)}`, with `q(m) = BetheLabels.arrRoots L c m` the realized DEF-006
  ordered Bethe roots of the label `m ∈ 𝓜_N` (the unique solution of the rapidity equations at coupling `c`,
  R-4C8D7C9E); `empiricalMeasureκ` is the value at the microscopic coupling `c = κ/N` of the unit-mass
  preparation (DEF-003: `κ m/N` with `m = 1`);
* it is a probability measure for `N ≥ 1` (`isProbabilityMeasure_empiricalMeasure`);
* as a *random measure*: the Markov kernel `empiricalKernel : 𝓜_N ⇝ ℝ` on the countable label set with its
  discrete σ-algebra, defined on the Born space `(𝓜_N, bornPMF Ψ u)` of the parametric DEF-007
  (`BetheCoefficientTransform`, any basis `Ψ`); the Born law as a measure is `bornMeasure`, and the annealed
  (mean) empirical measure `meanEmpirical = ∫ ν_N(m) dP_N(m)` is a probability measure
  (`meanEmpirical_univ`);
* the Cauchy transform `cauchyTransform M z = ∫ (z−t)⁻¹ dM(t)` of any finite measure, its bound
  `‖G_M(z)‖ ≤ M(ℝ)/|Im z|` and **the sign fact** `Im G_M(z) < 0` for `Im z > 0` and `M ≠ 0`
  (`im_cauchyTransform_neg`);
* `cauchyTransform_empiricalMeasure : G_{ν_N}(z) = N⁻¹ Σ_j (z − q_j)⁻¹`, and the random Cauchy transform
  `randomCauchy` has negative imaginary part in the upper half-plane for every label.

The limiting measures `μ_{κ,u}` (unit mass) and `M_{κ,u}` (full mass) are only *named* by DEF-010; they are not
defined here (DEF-003's `fullMassMeasure` rescales a supplied unit-mass limit).
-/

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace QuantumNLS.EmpiricalRapidity

open QuantumNLS.BetheLabels (MArr arrRoots)

/-! ### Cauchy transform and its sign -/

/-- `G_M(z) = ∫ (z − t)⁻¹ dM(t)`. -/
def cauchyTransform (M : Measure ℝ) (z : ℂ) : ℂ := ∫ t : ℝ, ((z - (t : ℂ))⁻¹ : ℂ) ∂M

theorem sub_ne_zero_of_im (z : ℂ) (hz : z.im ≠ 0) (t : ℝ) : z - (t : ℂ) ≠ 0 := by
  intro h
  apply hz
  have := congrArg Complex.im h
  simpa using this

theorem continuous_cauchyIntegrand (z : ℂ) (hz : z.im ≠ 0) :
    Continuous fun t : ℝ => ((z - (t : ℂ))⁻¹ : ℂ) :=
  (continuous_const.sub Complex.continuous_ofReal).inv₀ (sub_ne_zero_of_im z hz)

theorem norm_cauchyIntegrand_le (z : ℂ) (hz : z.im ≠ 0) (t : ℝ) :
    ‖((z - (t : ℂ))⁻¹ : ℂ)‖ ≤ |z.im|⁻¹ := by
  rw [norm_inv]
  have h1 : |z.im| ≤ ‖z - (t : ℂ)‖ := by
    have := Complex.abs_im_le_norm (z - (t : ℂ))
    simpa using this
  exact inv_anti₀ (abs_pos.mpr hz) h1

theorem integrable_cauchyIntegrand (M : Measure ℝ) [IsFiniteMeasure M] (z : ℂ) (hz : z.im ≠ 0) :
    Integrable (fun t : ℝ => ((z - (t : ℂ))⁻¹ : ℂ)) M :=
  Integrable.mono' (integrable_const (|z.im|⁻¹))
    (continuous_cauchyIntegrand z hz).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_cauchyIntegrand_le z hz))

/-- `|G_M(z)| ≤ M(ℝ)/|Im z|`. -/
theorem norm_cauchyTransform_le (M : Measure ℝ) [IsFiniteMeasure M] (z : ℂ) (hz : z.im ≠ 0) :
    ‖cauchyTransform M z‖ ≤ M.real Set.univ * |z.im|⁻¹ := by
  unfold cauchyTransform
  refine (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall
    (norm_cauchyIntegrand_le z hz))).trans (le_of_eq ?_)
  rw [mul_comm]

theorem im_cauchyIntegrand (z : ℂ) (t : ℝ) :
    ((z - (t : ℂ))⁻¹).im = -z.im / Complex.normSq (z - (t : ℂ)) := by
  rw [Complex.inv_im]
  simp

/-- **The sign fact**: `Im G_M(z) < 0` for `Im z > 0` and a nonzero finite positive measure `M`. -/
theorem im_cauchyTransform_neg (M : Measure ℝ) [IsFiniteMeasure M] (hM : M ≠ 0) (z : ℂ)
    (hz : 0 < z.im) : (cauchyTransform M z).im < 0 := by
  have hz' : z.im ≠ 0 := hz.ne'
  have hint := integrable_cauchyIntegrand M z hz'
  have him : (cauchyTransform M z).im = ∫ t : ℝ, (((z - (t : ℂ))⁻¹ : ℂ)).im ∂M := by
    unfold cauchyTransform
    have := Complex.imCLM.integral_comp_comm hint
    simpa using this.symm
  rw [him]
  have hpos : ∀ t : ℝ, 0 < z.im / Complex.normSq (z - (t : ℂ)) := fun t => by
    apply div_pos hz
    apply Complex.normSq_pos.mpr
    exact sub_ne_zero_of_im z hz' t
  have hne : ∫ t : ℝ, (((z - (t : ℂ))⁻¹ : ℂ)).im ∂M =
      -∫ t : ℝ, z.im / Complex.normSq (z - (t : ℂ)) ∂M := by
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
    simp only [im_cauchyIntegrand]
    ring
  rw [hne, neg_lt_zero]
  have hint2 : Integrable (fun t : ℝ => z.im / Complex.normSq (z - (t : ℂ))) M := by
    have := (Complex.imCLM.integrable_comp hint).neg
    refine this.congr (Filter.Eventually.of_forall (fun t => ?_))
    simp only [Pi.neg_apply, Complex.imCLM_apply, im_cauchyIntegrand]
    ring
  rw [integral_pos_iff_support_of_nonneg (fun t => (hpos t).le) hint2]
  have : Function.support (fun t : ℝ => z.im / Complex.normSq (z - (t : ℂ))) = Set.univ :=
    Set.eq_univ_of_forall (fun t => (hpos t).ne')
  rw [this]
  exact Measure.measure_univ_pos.mpr hM

/-! ### The empirical rapidity measure -/

/-- **`ν_N = N⁻¹ Σ_j δ_{q_j}`** for the ordered Bethe roots `q(m) = arrRoots L c m` of the label
`m ∈ 𝓜_N` at coupling `c`. -/
def empiricalMeasure (L c : ℝ) {N : ℕ} (m : MArr N) : Measure ℝ :=
  ((N : ℝ≥0∞)⁻¹) • ∑ j : Fin N, Measure.dirac (arrRoots L c m j)

/-- At the microscopic coupling `c = κ/N` (unit-mass preparation). -/
def empiricalMeasureκ (L κ : ℝ) {N : ℕ} (m : MArr N) : Measure ℝ :=
  empiricalMeasure L (κ / N) m

theorem empiricalMeasure_univ (L c : ℝ) {N : ℕ} (hN : 0 < N) (m : MArr N) :
    empiricalMeasure L c m Set.univ = 1 := by
  unfold empiricalMeasure
  simp only [Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply, Measure.dirac_apply_of_mem
    (Set.mem_univ _), smul_eq_mul]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hN.ne') (ENNReal.natCast_ne_top N)

theorem isProbabilityMeasure_empiricalMeasure (L c : ℝ) {N : ℕ} (hN : 0 < N) (m : MArr N) :
    IsProbabilityMeasure (empiricalMeasure L c m) :=
  ⟨empiricalMeasure_univ L c hN m⟩

theorem empiricalMeasure_ne_zero (L c : ℝ) {N : ℕ} (hN : 0 < N) (m : MArr N) :
    empiricalMeasure L c m ≠ 0 := by
  intro h
  have := empiricalMeasure_univ L c hN m
  rw [h] at this
  simp at this

theorem cauchyTransform_empiricalMeasure (L c : ℝ) {N : ℕ} (hN : 0 < N) (m : MArr N) (z : ℂ)
    (hz : z.im ≠ 0) :
    cauchyTransform (empiricalMeasure L c m) z =
      ((N : ℂ)⁻¹) * ∑ j : Fin N, (z - (arrRoots L c m j : ℂ))⁻¹ := by
  haveI := isProbabilityMeasure_empiricalMeasure L c hN m
  unfold cauchyTransform empiricalMeasure
  rw [integral_smul_measure, integral_finset_sum_measure]
  · simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, Complex.real_smul]
    simp
  · intro j _
    exact integrable_cauchyIntegrand _ z hz

theorem im_cauchy_empiricalMeasure_neg (L c : ℝ) {N : ℕ} (hN : 0 < N) (m : MArr N) (z : ℂ)
    (hz : 0 < z.im) : (cauchyTransform (empiricalMeasure L c m) z).im < 0 := by
  haveI := isProbabilityMeasure_empiricalMeasure L c hN m
  exact im_cauchyTransform_neg _ (empiricalMeasure_ne_zero L c hN m) z hz

/-! ### The empirical measure as a random measure on the Born space -/

section Random

variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-- The label set `𝓜_N` carries the discrete σ-algebra (it is countable). -/
instance instMeasurableMArr : MeasurableSpace (MArr N) := ⊤

instance instDiscreteMArr : DiscreteMeasurableSpace (MArr N) := ⟨fun _ => trivial⟩

/-- The random measure `m ↦ ν_N(m)` as a Markov kernel on `𝓜_N`. -/
def empiricalKernel (L c : ℝ) (N : ℕ) : Kernel (MArr N) ℝ :=
  ⟨fun m => empiricalMeasure L c m, Measurable.of_discrete⟩

theorem empiricalKernel_apply (L c : ℝ) (N : ℕ) (m : MArr N) :
    empiricalKernel L c N m = empiricalMeasure L c m := rfl

theorem isMarkovKernel_empiricalKernel (L c : ℝ) (hN : 0 < N) :
    IsMarkovKernel (empiricalKernel L c N) :=
  ⟨fun m => isProbabilityMeasure_empiricalMeasure L c hN m⟩

/-- The Born law of the parametric DEF-007 as a probability measure on `𝓜_N`. -/
def bornMeasure (Ψ : QuantumNLS.BetheCoefficientTransform.BetheBasis L N) (u : QuantumNLS.PhysicalTensor.L2T L)
    (hu : ‖u‖ = 1) : Measure (MArr N) :=
  (QuantumNLS.BetheCoefficientTransform.bornPMF Ψ u hu).toMeasure

instance (Ψ : QuantumNLS.BetheCoefficientTransform.BetheBasis L N) (u : QuantumNLS.PhysicalTensor.L2T L)
    (hu : ‖u‖ = 1) : IsProbabilityMeasure (bornMeasure Ψ u hu) := by
  unfold bornMeasure; infer_instance

theorem bornMeasure_singleton (Ψ : QuantumNLS.BetheCoefficientTransform.BetheBasis L N)
    (u : QuantumNLS.PhysicalTensor.L2T L) (hu : ‖u‖ = 1) (m : MArr N) :
    bornMeasure Ψ u hu {m} = ENNReal.ofReal (QuantumNLS.BetheCoefficientTransform.bornLaw Ψ u m) := by
  unfold bornMeasure
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton m)]
  rfl

/-- The annealed (mean) empirical rapidity measure `∫ ν_N(m) dP_N(m)`. -/
def meanEmpirical (Ψ : QuantumNLS.BetheCoefficientTransform.BetheBasis L N)
    (u : QuantumNLS.PhysicalTensor.L2T L) (hu : ‖u‖ = 1) (c : ℝ) : Measure ℝ :=
  (bornMeasure Ψ u hu).bind (fun m => empiricalMeasure L c m)

theorem meanEmpirical_univ (Ψ : QuantumNLS.BetheCoefficientTransform.BetheBasis L N)
    (u : QuantumNLS.PhysicalTensor.L2T L) (hu : ‖u‖ = 1) (c : ℝ) (hN : 0 < N) :
    meanEmpirical Ψ u hu c Set.univ = 1 := by
  unfold meanEmpirical
  rw [Measure.bind_apply MeasurableSet.univ Measurable.of_discrete.aemeasurable]
  simp only [empiricalMeasure_univ L c hN, lintegral_const, measure_univ, mul_one]

/-- The random Cauchy transform `m ↦ G_{ν_N(m)}(z)`; for `Im z > 0` its imaginary part is negative for
every label `m`. -/
def randomCauchy (L c : ℝ) {N : ℕ} (z : ℂ) (m : MArr N) : ℂ :=
  cauchyTransform (empiricalMeasure L c m) z

theorem im_randomCauchy_neg (L c : ℝ) (hN : 0 < N) (z : ℂ) (hz : 0 < z.im) (m : MArr N) :
    (randomCauchy L c z m).im < 0 :=
  im_cauchy_empiricalMeasure_neg L c hN m z hz

end Random

#print axioms im_cauchyTransform_neg
#print axioms cauchyTransform_empiricalMeasure
#print axioms isProbabilityMeasure_empiricalMeasure
#print axioms meanEmpirical_univ
#print axioms bornMeasure_singleton

end QuantumNLS.EmpiricalRapidity
