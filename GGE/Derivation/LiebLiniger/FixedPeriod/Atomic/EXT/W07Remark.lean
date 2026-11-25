import NlsGge.Birkhoff.W07Probability38e
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing

/-!
# The relative nonlinear energy of the full Fourier Gaussian

This supplies the W07 remark in `paper/v2.tex:1576-1578`, SHA-256
`0e7c2e61a06ab6886124c3891c73e0b8997ab71473eaf75b05c524098a58e3ec`.
The finite differences use the complete hierarchy energy at each Fourier cutoff,
including the zero mode. Their spectral energy is finite by the existing
`spectralEnergy_projE38_ne_top_W07`; hence its `toReal` denotes the finite source
energy, not the real totalization of an infinite Gaussian energy.

The raw W06 density is a.e. measurable. We retain that formula and its SAME
Ramer divergence witness and produce a globally measurable representative of
its negative logarithm, explicitly identified a.e. The source's measurable
random variable is understood in precisely this sense; no global Borel property
of an arbitrary raw divergence representative follows from integrability.
The final theorem uses the actual Birkhoff and one-smoothing producers internally.
These are author proofs submitted for independent semantic review, not acceptance.

Pinned Mathlib: commit `d13f23b723b8a846827a245b89c10fc7d3f11612`, Apache-2.0.
The subsequence criterion and congruence are in
`Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean`; logarithm continuity
and measurability are in `Analysis/SpecialFunctions/Log/Basic.lean` and
`MeasureTheory/Function/SpecialFunctions/Basic.lean`; the measurable representative
API is in `MeasureTheory/Measure/MeasureSpaceDef.lean`.
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.EXT

open MeasureTheory Filter Topology NlsGge.Pilot NlsGge.Measure NlsGge.Birkhoff
  NlsGge.SpectralFoundations NlsGge.Ramer NlsGge.ThirdConsultation.PDE

/-- On any measurable type `α` with finite measure `μ`, let `f n` be real
approximants indexed by all naturals and `g` a real limit. If each approximant
is a.e. strongly measurable (`hf`), the approximants converge in measure
(`hfg`), and `g` is positive a.e. (`hg`), their negative logarithms converge in
measure to the negative logarithm of `g`. No logarithmic integrability or
uniform positive lower bound is assumed. -/
theorem tendstoInMeasure_neg_log_of_ae_pos38
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : ℕ → α → ℝ} {g : α → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hfg : TendstoInMeasure μ f atTop g)
    (hg : ∀ᵐ x ∂μ, 0 < g x) :
    TendstoInMeasure μ (fun n x => -Real.log (f n x)) atTop
      (fun x => -Real.log (g x)) := by
  have hlog : ∀ n, AEStronglyMeasurable (fun x => -Real.log (f n x)) μ :=
    fun n => (Real.measurable_log.comp_aemeasurable (hf n).aemeasurable).neg.aestronglyMeasurable
  rw [exists_seq_tendstoInMeasure_atTop_iff hlog]
  intro ns hns
  obtain ⟨ns', hns', hae⟩ := (hfg.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ns', hns', ?_⟩
  filter_upwards [hae, hg] with x hx hxpos
  exact ((Real.continuousAt_log hxpos.ne').tendsto.comp hx).neg

/-- For arbitrary real coefficient bounds `lower`, `upper`, admitted coefficient
sequence `c`, real Sobolev index `s`, natural Fourier cutoff `N`, and weighted
Hilbert point `x`, the negative logarithm of the finite weight equals its finite
full spectral energy minus the finite Gaussian quadratic energy. Finiteness of
the first term is already `spectralEnergy_projE38_ne_top_W07`; the second is a
finite sum over `symmetricModes N`. No infinite-energy subtraction occurs. -/
theorem negLog_fN_eq_finiteEnergyDifference38 {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) (s : ℝ) (N : ℕ)
    (x : FullWeightedHilbert c s) :
    -Real.log (fN38 c s N x) =
      (spectralEnergyW38 c.val (physOfE38 c s (projE38 c s N x))).toReal -
        Afin38 c N (coordE c s x) := by
  rw [fN38, Real.log_exp]
  ring

/-- For arbitrary real bounds `lower`, `upper`, admitted coefficient sequence
`c`, real index `s`, and natural Fourier cutoff `N`, the finite full-energy
minus Gaussian-energy difference is a globally measurable real function on the
actual weighted Hilbert carrier. This follows from its exact negative-log
formula for the globally measurable finite weight. -/
theorem measurable_finiteEnergyDifferenceW07_38 {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) (s : ℝ) (N : ℕ) :
    Measurable (fun x : FullWeightedHilbert c s =>
      (spectralEnergyW38 c.val (physOfE38 c s (projE38 c s N x))).toReal -
        Afin38 c N (coordE c s x)) := by
  have hm : Measurable (fun x : FullWeightedHilbert c s => -Real.log (fN38 c s N x)) :=
    (Real.measurable_log.comp (measurable_fN38 c s N)).neg
  simpa only [negLog_fN_eq_finiteEnergyDifference38] using hm

/-- For a Birkhoff producer `B`, its one-smoothing producer `O`, arbitrary real
coefficient bounds `lower`, `upper`, admitted sequence `c`, and real index `s`
with `hs : 1/2 < s` and `hs' : s < 3/4`, there is ONE Ramer divergence `δK` for
the corresponding `K`. Its unnormalized full weight `f` is positive everywhere,
integrable under the genuine full Gaussian, and is the probability limit of
all finite full weights. The producers are helper parameters; the actual final
theorem supplies them internally. -/
theorem positive_weight_and_probability_W07_38
    (B : BirkhoffInput38) (O : OneSmoothingInput38 B)
    {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
    ∃ δK : (ℤ → ℂ) → ℝ,
      RamerDivergence38 c s
        (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δK ∧
      (let f := fW06_38 c s hs
         (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δK;
       (∀ x, 0 < f x) ∧ Integrable f (fullWeightedSequenceGaussian c s) ∧
       TendstoInMeasure (fullWeightedSequenceGaussian c s)
         (fun N x => fN38 c s N x) atTop f) := by
  have hs1 := le_one_of_lt_three_quarters_W06_38 hs'
  obtain ⟨δK, hdiv, hmap, hpos, hint, _hone, hconv⟩ := B.ramer_W06_cyl_38 O c hs hs1
  obtain ⟨hfpos, hfi, _⟩ := density_W06_38 B c s O hs hs' _ hmap hint hpos
  exact ⟨δK, hdiv, hfpos, hfi, B.tendstoInMeasure_fN_W07 O c hs hs' hs1 δK hconv⟩

/-- On an arbitrary measurable type `α` with measure `μ`, a real function `f`
that is a.e. measurable (`hf`) and positive a.e. (`hpos`) has an a.e. measurable
negative logarithm. There exists a globally measurable real representative `V`,
a.e. equal to that raw negative logarithm, with `exp (-V) = f` a.e. Both `V` and
its a.e. identification are conclusions; the raw function is retained. -/
theorem negLog_measurableRepresentative38
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : AEMeasurable f μ) (hpos : ∀ᵐ x ∂μ, 0 < f x) :
    AEMeasurable (fun x => -Real.log (f x)) μ ∧
    ∃ V : α → ℝ, Measurable V ∧
      V =ᵐ[μ] (fun x => -Real.log (f x)) ∧
      (∀ᵐ x ∂μ, Real.exp (-V x) = f x) := by
  have hraw := (Real.measurable_log.comp_aemeasurable hf).neg
  let V := hraw.mk (fun x => -Real.log (f x))
  have hV : V =ᵐ[μ] (fun x => -Real.log (f x)) := hraw.ae_eq_mk.symm
  refine ⟨hraw, V, hraw.measurable_mk, hV, ?_⟩
  filter_upwards [hV, hpos] with x hx hxpos
  rw [hx, neg_neg, Real.exp_log hxpos]

/-- The W07 source remark for the actual full Fourier Gaussian. The real bounds
`lower`, `upper` and coefficient sequence `c` are arbitrary subject to the source
`BoundedCoefficients` condition (positive lower bound and uniform upper bound).
The real index `s` satisfies exactly `hs : 1/2 < s` and `hs' : s < 3/4`.
There exists a divergence `δK` for the actual Birkhoff difference, retained in
ONE unnormalized density `f`. This density is positive a.e.; its raw negative
logarithm is a.e. measurable and is the limit in probability of the finite
complete hierarchy-energy differences for all natural cutoffs `N`. There also
exists a globally measurable real `V`, explicitly a.e. equal to that raw energy,
with `exp (-V) = f` a.e. and the SAME probability limit. All a.e. and convergence
statements use `fullWeightedSequenceGaussian c s`, not a finite-plane law.
No Birkhoff/Ramer/spectral proof premise, energy integrability, continuity,
normalized-density shift, or extra restriction is added to the source. -/
theorem actual_w07_relative_energy38 {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
    ∃ δK : (ℤ → ℂ) → ℝ,
      RamerDivergence38 c s (actualBirkhoffInput38.KW06_38 actualOneSmoothingInput38 c
        (le_one_of_lt_three_quarters_W06_38 hs')) δK ∧
      (let f : FullWeightedHilbert c s → ℝ := fW06_38 c s hs
         (actualBirkhoffInput38.KW06_38 actualOneSmoothingInput38 c
           (le_one_of_lt_three_quarters_W06_38 hs')) δK;
       (∀ᵐ x ∂(fullWeightedSequenceGaussian c s), 0 < f x) ∧
       AEMeasurable (fun x => -Real.log (f x)) (fullWeightedSequenceGaussian c s) ∧
       TendstoInMeasure (fullWeightedSequenceGaussian c s)
         (fun N x => (spectralEnergyW38 c.val (physOfE38 c s (projE38 c s N x))).toReal -
           Afin38 c N (coordE c s x)) atTop (fun x => -Real.log (f x)) ∧
       ∃ V : FullWeightedHilbert c s → ℝ, Measurable V ∧
         V =ᵐ[fullWeightedSequenceGaussian c s] (fun x => -Real.log (f x)) ∧
         (∀ᵐ x ∂(fullWeightedSequenceGaussian c s), Real.exp (-V x) = f x) ∧
         TendstoInMeasure (fullWeightedSequenceGaussian c s)
           (fun N x => (spectralEnergyW38 c.val (physOfE38 c s (projE38 c s N x))).toReal -
             Afin38 c N (coordE c s x)) atTop V) := by
  obtain ⟨δK, hdiv, hpos, hint, hconv⟩ := positive_weight_and_probability_W07_38
    actualBirkhoffInput38 actualOneSmoothingInput38 c s hs hs'
  have hposae : ∀ᵐ x ∂(fullWeightedSequenceGaussian c s),
      0 < fW06_38 c s hs (actualBirkhoffInput38.KW06_38 actualOneSmoothingInput38 c
        (le_one_of_lt_three_quarters_W06_38 hs')) δK x := Filter.Eventually.of_forall hpos
  obtain ⟨hraw, V, hVm, hVeq, hVexp⟩ :=
    negLog_measurableRepresentative38 hint.aemeasurable hposae
  have hlog := tendstoInMeasure_neg_log_of_ae_pos38
    (fun N => (measurable_fN38 c s N).aestronglyMeasurable) hconv hposae
  have henergy : TendstoInMeasure (fullWeightedSequenceGaussian c s)
      (fun N x => (spectralEnergyW38 c.val (physOfE38 c s (projE38 c s N x))).toReal -
        Afin38 c N (coordE c s x)) atTop
      (fun x => -Real.log (fW06_38 c s hs
        (actualBirkhoffInput38.KW06_38 actualOneSmoothingInput38 c
          (le_one_of_lt_three_quarters_W06_38 hs')) δK x)) := by
    simpa only [negLog_fN_eq_finiteEnergyDifference38] using hlog
  exact ⟨δK, hdiv, hposae, hraw, henergy, V, hVm, hVeq, hVexp,
    henergy.congr_right hVeq.symm⟩

end LiebLiniger.FixedPeriod.EXT
