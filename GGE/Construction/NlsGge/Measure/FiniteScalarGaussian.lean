import NlsGge.Measure.WeightedModes
import NlsGge.Measure.ScalarGaussian
import NlsGge.Measure.CountableGaussian
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Independence.InfinitePi

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace NlsGge.Measure

/-!
This file proves the raw finite scalar Gaussian-law step only.  Its source law
is the actual infinite product of the source-rate complex Gaussian marginals;
the arbitrary real Sobolev index enters only through the finite mode maps.
-/

lemma hasGaussianLaw_fullWeightSequenceGaussian_modeScalar {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (L : NlsGge.Pilot.FullWeightedHilbert c s →L[ℝ] ℝ) (n : ℤ) :
    ProbabilityTheory.HasGaussianLaw
      (fun z : ℤ → ℂ => L (fullWeightedModeMap c s n (z n)))
      (fullWeightSequenceGaussian c.val) := by
  let M : ℂ →L[ℝ] NlsGge.Pilot.FullWeightedHilbert c s := fullWeightedModeMap c s n
  let X : (ℤ → ℂ) → ℝ := fun z => L (M (z n))
  have hmap : (fullWeightSequenceGaussian c.val).map X =
      (complexGaussian (fullWeightRate c.val n)).map (L.comp M) := by
    calc
      (fullWeightSequenceGaussian c.val).map X =
          ((fullWeightSequenceGaussian c.val).map (fun z : ℤ → ℂ => z n)).map (L.comp M) := by
            rw [Measure.map_map (by fun_prop) (by fun_prop)]
            rfl
      _ = (complexGaussian (fullWeightRate c.val n)).map (L.comp M) := by
            rw [fullWeightSequenceGaussian_map_eval]
  have hgauss : ProbabilityTheory.IsGaussian
      ((complexGaussian (fullWeightRate c.val n)).map (L.comp M)) :=
    isGaussian_complexGaussian_realLinear _ _
  have hXmeas : Measurable X := by
    exact L.continuous.measurable.comp
      (M.continuous.measurable.comp (measurable_pi_apply n))
  have hX : AEMeasurable X (fullWeightSequenceGaussian c.val) := hXmeas.aemeasurable
  exact ⟨hX, hmap ▸ hgauss⟩

lemma hasGaussianLaw_fullWeightSequenceGaussian_partialScalar {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) (N : ℕ)
    (L : NlsGge.Pilot.FullWeightedHilbert c s →L[ℝ] ℝ) :
    ProbabilityTheory.HasGaussianLaw
      (fun z : ℤ → ℂ =>
        L (fullWeightedSequencePartial c s N z))
      (fullWeightSequenceGaussian c.val) := by
  let μ := fullWeightSequenceGaussian c.val
  let S := NlsGge.Pilot.symmetricModes N
  let I := {n : ℤ // n ∈ S}
  let X : I → (ℤ → ℂ) → ℝ :=
    fun i z => L (fullWeightedModeMap c s i.1 (z i.1))
  have hcoord : iIndepFun (fun n : ℤ => fun z : ℤ → ℂ => z n) μ := by
    unfold μ
    simpa [fullWeightSequenceGaussian, countableComplexGaussian] using
      (ProbabilityTheory.iIndepFun_infinitePi
        (P := fun n : ℤ => complexGaussian (fullWeightRate c.val n))
        (X := fun n (z : ℂ) => z) (by fun_prop))
  have hsub : iIndepFun (fun i : I => fun z : ℤ → ℂ => z i.1) μ :=
    hcoord.precomp (fun i j hij => Subtype.ext hij)
  have hX : iIndepFun X μ := by
    exact hsub.comp
      (fun i w => L (fullWeightedModeMap c s i.1 w)) (by intro i; fun_prop)
  have hsum : HasGaussianLaw (fun z => ∑ i : I, X i z) μ :=
    ProbabilityTheory.iIndepFun.hasGaussianLaw_fun_sum
      (fun i => hasGaussianLaw_fullWeightSequenceGaussian_modeScalar c s L i.1)
      hX
  have hEq : (fun z : ℤ → ℂ => ∑ i : I, X i z) =
      (fun z => L (fullWeightedSequencePartial c s N z)) := by
    funext z
    rw [fullWeightedSequencePartial_eq_sumModeMaps]
    simp only [X, map_sum]
    dsimp [I, S]
    exact Finset.sum_attach (NlsGge.Pilot.symmetricModes N)
      (fun n => L (fullWeightedModeMap c s n (z n)))
  exact hsum.congr (Filter.Eventually.of_forall fun z => congrFun hEq z)

end NlsGge.Measure
