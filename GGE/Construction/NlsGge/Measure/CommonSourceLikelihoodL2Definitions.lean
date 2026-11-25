import NlsGge.Measure.CountableGaussian
import NlsGge.Sobolev.SourceWeighted
import NlsGge.Sobolev.CMCoordinateSeries
import NlsGge.Sobolev.CMWeightComparison
import NlsGge.Measure.CommonSourceLikelihoodFiniteAfterScalarPrerequisite
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
Type-only Prop contracts for the next common-source likelihood L² stage.

These definitions are propositions to be proved, not axioms or theorem
declarations. The source CM sequence is extracted from the actual weighted
Hilbert vector below; its energy summability is a separate target, not an
assumption used to assert that an arbitrary shift is a CM vector. The final
contract is only Cauchy convergence in the actual common L² space.
-/

set_option autoImplicit false
noncomputable section

open Filter

namespace NlsGge.Measure

variable {lower upper : ℝ}

/-- The sequence represented by an actual vector in the source CM Hilbert
space, viewed in its underlying complex weighted-sequence carrier. -/
def actualSourceCMSequence
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (x : NlsGge.Pilot.WeightedRealHilbert
      (NlsGge.Pilot.cmModeWeight c)) : ℤ → ℂ :=
  fun n => (show NlsGge.Pilot.WeightedHilbert
    (NlsGge.Pilot.cmModeWeight c) from x) n

/-- This is an explicit proof obligation for the actual CM realization.
It follows from the source weighted-Hilbert norm-series theorem; it is not a
free summability premise on a shift sequence. -/
def actualSourceCMSequenceEnergySummableContract : Prop :=
  ∀ (lower upper : ℝ)
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (x : NlsGge.Pilot.WeightedRealHilbert
      (NlsGge.Pilot.cmModeWeight c)),
    Summable (fun n : ℤ =>
      NlsGge.Pilot.cmModeWeight c n *
        ‖NlsGge.Measure.actualSourceCMSequence c x n‖ ^ 2)

/-- Finite-cutoff likelihood belongs to the actual real L² space over the
unchanged full signed-coordinate source Gaussian. -/
def memLpCommonSourceLikelihoodRealContract : Prop :=
  ∀ (lower upper : ℝ)
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (N : ℕ) (h : ℤ → ℂ),
    MeasureTheory.MemLp
      (fun z : ℤ → ℂ =>
        NlsGge.Measure.commonSourceLikelihoodReal lower upper c N h z)
      2 (NlsGge.Measure.fullWeightSequenceGaussian c.val)

/-- Lp representative of the finite real likelihood, parameterized by its
actual MemLp proof so the contract file needs no choice or unproved lemma. -/
noncomputable def commonSourceLikelihoodLpOfMemLp
    (lower upper : ℝ)
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (N : ℕ) (h : ℤ → ℂ)
    (hmem : MeasureTheory.MemLp
      (fun z : ℤ → ℂ =>
        NlsGge.Measure.commonSourceLikelihoodReal lower upper c N h z)
      2 (NlsGge.Measure.fullWeightSequenceGaussian c.val)) :
    MeasureTheory.Lp ℝ 2
      (NlsGge.Measure.fullWeightSequenceGaussian c.val) :=
  hmem.toLp (fun z : ℤ → ℂ =>
    NlsGge.Measure.commonSourceLikelihoodReal lower upper c N h z)

/-- The finite L² norm-distance identity to be proved from the already
compiled finite square-integral identity and the Lp norm formula. -/
def normSqCommonSourceLikelihoodLpDistanceContract : Prop :=
  ∀ (lower upper : ℝ)
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (N M : ℕ) (hNM : N ≤ M) (h : ℤ → ℂ)
    (hmemM : MeasureTheory.MemLp
      (fun z : ℤ → ℂ =>
        NlsGge.Measure.commonSourceLikelihoodReal lower upper c M h z)
      2 (NlsGge.Measure.fullWeightSequenceGaussian c.val))
    (hmemN : MeasureTheory.MemLp
      (fun z : ℤ → ℂ =>
        NlsGge.Measure.commonSourceLikelihoodReal lower upper c N h z)
      2 (NlsGge.Measure.fullWeightSequenceGaussian c.val)),
    ‖NlsGge.Measure.commonSourceLikelihoodLpOfMemLp
        lower upper c M h hmemM -
      NlsGge.Measure.commonSourceLikelihoodLpOfMemLp
        lower upper c N h hmemN‖ ^ 2 =
      Real.exp (NlsGge.Measure.commonSourceLikelihoodEnergy lower upper c M h) -
        Real.exp (NlsGge.Measure.commonSourceLikelihoodEnergy lower upper c N h)

/-- Partial energies of the sequence extracted from an actual CM vector
converge along the existing symmetric-mode exhaustion to its source CM norm
square. -/
def actualSourceCMPartialEnergyTendstoContract : Prop :=
  ∀ (lower upper : ℝ)
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (x : NlsGge.Pilot.WeightedRealHilbert
      (NlsGge.Pilot.cmModeWeight c)),
    Filter.Tendsto
      (fun N : ℕ =>
        NlsGge.Measure.commonSourceLikelihoodEnergy lower upper c N
          (NlsGge.Measure.actualSourceCMSequence c x))
      Filter.atTop
      (nhds (∑' n : ℤ,
        NlsGge.Pilot.cmModeWeight c n *
          ‖NlsGge.Measure.actualSourceCMSequence c x n‖ ^ 2))

/-- Lp sequence built from a family of finite MemLp proofs. -/
noncomputable def commonSourceLikelihoodLpSequenceOfMemLp
    (lower upper : ℝ)
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (h : ℤ → ℂ)
    (hmem : ∀ N : ℕ, MeasureTheory.MemLp
      (fun z : ℤ → ℂ =>
        NlsGge.Measure.commonSourceLikelihoodReal lower upper c N h z)
      2 (NlsGge.Measure.fullWeightSequenceGaussian c.val)) :
    ℕ → MeasureTheory.Lp ℝ 2
      (NlsGge.Measure.fullWeightSequenceGaussian c.val) :=
  fun N => NlsGge.Measure.commonSourceLikelihoodLpOfMemLp
    lower upper c N h (hmem N)

/-- The Cauchy conclusion is parameterized by the two preceding obligations:
finite MemLp for each cutoff, and source-energy summability for the sequence
coming from an actual CM vector. These are proof dependencies, not extra
assumptions in the eventual CM theorem. -/
def actualSourceCMCommonLikelihoodCauchyContract : Prop :=
  ∀ (lower upper : ℝ)
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (x : NlsGge.Pilot.WeightedRealHilbert
      (NlsGge.Pilot.cmModeWeight c)),
    (hmem : ∀ N : ℕ, MeasureTheory.MemLp
      (fun z : ℤ → ℂ =>
        NlsGge.Measure.commonSourceLikelihoodReal lower upper c N
          (NlsGge.Measure.actualSourceCMSequence c x) z)
      2 (NlsGge.Measure.fullWeightSequenceGaussian c.val)) →
    (hsummable : Summable (fun n : ℤ =>
      NlsGge.Pilot.cmModeWeight c n *
        ‖NlsGge.Measure.actualSourceCMSequence c x n‖ ^ 2)) →
    CauchySeq (NlsGge.Measure.commonSourceLikelihoodLpSequenceOfMemLp
      lower upper c (NlsGge.Measure.actualSourceCMSequence c x)
      hmem)

end NlsGge.Measure

set_option pp.all true
set_option pp.universes true
set_option pp.fullNames true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check NlsGge.Measure.actualSourceCMSequence
#check NlsGge.Measure.actualSourceCMSequenceEnergySummableContract
#check NlsGge.Measure.memLpCommonSourceLikelihoodRealContract
#check NlsGge.Measure.normSqCommonSourceLikelihoodLpDistanceContract
#check NlsGge.Measure.actualSourceCMPartialEnergyTendstoContract
#check NlsGge.Measure.actualSourceCMCommonLikelihoodCauchyContract
