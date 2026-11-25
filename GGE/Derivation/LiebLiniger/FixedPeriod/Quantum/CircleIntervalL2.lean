import LiebLiniger.FixedPeriod.Quantum.TransferCoefficientKernel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
Explicit bridge between the physical mass-L AddCircle L carrier and the centered
interval kernel carrier. Endpoint replacement is justified by an AE measure
equality. The pullback is an actual surjective L² isometry, with no rescaling.
-/
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LiebLiniger.FixedPeriod.Quantum

/-- Replacing the lower endpoint changes no Lebesgue integral or L² class. -/
theorem transferIntervalMeasure_eq_Ioc (L : ℝ) :
    transferIntervalMeasure L = volume.restrict (Ioc (-L / 2) (-L / 2 + L)) := by
  unfold transferIntervalMeasure
  rw [show -L / 2 + L = L / 2 by ring]
  exact (Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := volume))).symm

/-- The interval carrier has the physical mass L, not normalized mass one. -/
theorem transferIntervalMeasure_univ (L : ℝ) :
    transferIntervalMeasure L univ = ENNReal.ofReal L := by
  simp only [transferIntervalMeasure, Measure.restrict_apply_univ, Real.volume_Icc]
  congr 1
  ring

variable (L : ℝ) [Fact (0 < L)]

/-- The actual periodic projection preserves unnormalized physical volume. -/
theorem intervalToCircle_measurePreserving :
    MeasurePreserving (fun x : ℝ => (x : AddCircle L))
      (transferIntervalMeasure L) (volume : Measure (AddCircle L)) := by
  rw [transferIntervalMeasure_eq_Ioc]
  exact AddCircle.measurePreserving_mk L (-L / 2)

/-- Pullback of a physical torus wavefunction to the centered interval. -/
def circleToIntervalL2 :
    Lp ℂ 2 (volume : Measure (AddCircle L)) →ₗᵢ[ℂ]
      Lp ℂ 2 (transferIntervalMeasure L) :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => (x : AddCircle L))
    (intervalToCircle_measurePreserving L)

/-- The pullback agrees AE with literal composition by the periodic projection. -/
theorem circleToIntervalL2_coeFn (f : Lp ℂ 2 (volume : Measure (AddCircle L))) :
    circleToIntervalL2 L f =ᵐ[transferIntervalMeasure L] fun x : ℝ => f (x : AddCircle L) :=
  Lp.coeFn_compMeasurePreserving f (intervalToCircle_measurePreserving L)

/-- Each interval L² wavefunction has a periodic lift, proving surjectivity
rather than assuming a spatial identification. -/
theorem circleToIntervalL2_surjective : Function.Surjective (circleToIntervalL2 L) := by
  intro f
  have hf : MemLp (fun x : ℝ => f x) 2
      (volume.restrict (Ioc (-L / 2) (-L / 2 + L))) := by
    rw [← transferIntervalMeasure_eq_Ioc]
    exact Lp.memLp f
  have hg : MemLp (AddCircle.liftIoc L (-L / 2) (fun x : ℝ => f x)) 2
      (volume : Measure (AddCircle L)) := hf.memLp_liftIoc
  let g : Lp ℂ 2 (volume : Measure (AddCircle L)) :=
    hg.toLp (AddCircle.liftIoc L (-L / 2) (fun x : ℝ => f x))
  refine ⟨g, ?_⟩
  apply Lp.ext
  have hglift : (fun x : ℝ => g (x : AddCircle L)) =ᵐ[transferIntervalMeasure L]
      fun x : ℝ => AddCircle.liftIoc L (-L / 2) (fun y : ℝ => f y) (x : AddCircle L) :=
    (intervalToCircle_measurePreserving L).quasiMeasurePreserving.ae_eq_comp hg.coeFn_toLp
  have hmem : ∀ᵐ x ∂transferIntervalMeasure L, x ∈ Ioc (-L / 2) (-L / 2 + L) := by
    rw [transferIntervalMeasure_eq_Ioc]
    exact ae_restrict_mem measurableSet_Ioc
  filter_upwards [circleToIntervalL2_coeFn L g, hglift, hmem] with x hx hgx hmx
  rw [hx, hgx]
  exact AddCircle.liftIoc_coe_apply hmx

/-- The genuine physical circle/interval L² unitary; both measures have mass L. -/
def circleIntervalL2Equiv :
    Lp ℂ 2 (volume : Measure (AddCircle L)) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (transferIntervalMeasure L) :=
  LinearIsometryEquiv.ofSurjective (circleToIntervalL2 L) (circleToIntervalL2_surjective L)

@[simp] theorem circleIntervalL2Equiv_apply (f : Lp ℂ 2 (volume : Measure (AddCircle L))) :
    circleIntervalL2Equiv L f = circleToIntervalL2 L f := rfl

/-- Both physical carriers retain the same finite-volume normalization. -/
theorem circle_interval_mass :
    (volume : Measure (AddCircle L)) univ = transferIntervalMeasure L univ := by
  rw [AddCircle.measure_univ L, transferIntervalMeasure_univ]

end LiebLiniger.FixedPeriod.Quantum
