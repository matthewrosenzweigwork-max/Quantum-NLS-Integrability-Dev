import QuantumNLS.Local001PotentialB
import QuantumNLS.Ext025A2Fourier
import QuantumNLS.HilbertDiagOp
import QuantumNLS.HaarResolvent
import QuantumNLS.HaarTwistedModes
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory AddCircle
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
open QuantumNLS.LocalSpectral

abbrev ScalarInterval (L : ℝ) :=
  Lp ℂ 2 (volume.restrict (Set.Ioc (0 : ℝ) L))

#print axioms ScalarInterval

abbrev CircleScalar (L : ℝ) [Fact (0 < L)] :=
  Lp ℂ 2 (volume : Measure (AddCircle L))


#print axioms CircleScalar

def IntervalH1Rep {L : ℝ} (f : ScalarInterval L) (g h : ℝ → ℂ) : Prop :=
  (f : ℝ → ℂ) =ᵐ[LocalSpectral.μI L] g ∧
    MemLp h 2 (LocalSpectral.μI L) ∧
    ∀ x ∈ Set.Icc 0 L, g x = g 0 + ∫ s in (0 : ℝ)..x, h s

variable (L : ℝ) [Fact (0 < L)]


#print axioms IntervalH1Rep

def intervalRepresentative (x : AddCircle L) : ℝ :=
  (AddCircle.equivIoc L 0 x : ℝ)


#print axioms intervalRepresentative

theorem interval_representative_measure_preserving :
    MeasurePreserving (intervalRepresentative L) (volume : Measure (AddCircle L))
      (volume.restrict (Set.Ioc (0 : ℝ) L)) := by
  change MeasurePreserving (Subtype.val ∘ AddCircle.equivIoc L 0)
    (volume : Measure (AddCircle L)) (volume.restrict (Set.Ioc (0 : ℝ) L))
  let J : Set ℝ := Set.Ioc (0 : ℝ) (0 + L)
  have h1 : MeasurePreserving (AddCircle.equivIoc L 0) (volume : Measure (AddCircle L))
      (Measure.comap (Subtype.val : J → ℝ) volume) := by
    simpa only [J] using
      (AddCircle.measurePreserving_equivIoc (T := L) (a := (0 : ℝ)))
  have h2 : MeasurePreserving (Subtype.val : J → ℝ)
      (Measure.comap (Subtype.val : J → ℝ) volume) (volume.restrict J) := by
    simpa only [J] using
      (measurePreserving_subtype_coe (s := J) (μa := (volume : Measure ℝ)) measurableSet_Ioc)
  have hcomp := h2.comp h1
  simpa only [J, zero_add] using hcomp


#print axioms interval_representative_measure_preserving

def intervalToCircle (f : ScalarInterval L) :
    Lp ℂ 2 (volume : Measure (AddCircle L)) :=
  Lp.compMeasurePreserving (intervalRepresentative L)
    (interval_representative_measure_preserving L) f


#print axioms intervalToCircle

def circleToInterval (f : Lp ℂ 2 (volume : Measure (AddCircle L))) : ScalarInterval L :=
  Lp.compMeasurePreserving (fun x : ℝ => (x : AddCircle L))
    (by simpa only [zero_add] using (AddCircle.measurePreserving_mk L (0 : ℝ))) f

#print axioms circleToInterval

theorem intervalToCircle_circleToInterval
    (f : Lp ℂ 2 (volume : Measure (AddCircle L))) :
    intervalToCircle L (circleToInterval L f) = f := by
  change Lp.compMeasurePreserving (intervalRepresentative L)
      (interval_representative_measure_preserving L)
      (Lp.compMeasurePreserving (fun x : ℝ => (x : AddCircle L))
        (by simpa only [zero_add] using (AddCircle.measurePreserving_mk L (0 : ℝ))) f) = f
  rw [← Lp.compMeasurePreserving_comp_apply]
  have hcomp : (fun x : ℝ => (x : AddCircle L)) ∘ intervalRepresentative L = id := by
    funext x
    exact AddCircle.coe_equivIoc
  simp only [hcomp, Lp.compMeasurePreserving_id_apply]


#print axioms intervalToCircle_circleToInterval

def intervalToCircleIso : ScalarInterval L ≃ₗᵢ[ℂ]
    Lp ℂ 2 (volume : Measure (AddCircle L)) :=
  LinearIsometryEquiv.ofSurjective
    (Lp.compMeasurePreservingₗᵢ ℂ (intervalRepresentative L)
      (interval_representative_measure_preserving L))
    (fun f => ⟨circleToInterval L f, intervalToCircle_circleToInterval L f⟩)

#print axioms intervalToCircleIso

theorem circleToInterval_intervalToCircle (f : ScalarInterval L) :
    circleToInterval L (intervalToCircle L f) = f := by
  apply (intervalToCircleIso L).injective
  change intervalToCircle L (circleToInterval L (intervalToCircle L f)) =
    intervalToCircle L f
  rw [intervalToCircle_circleToInterval]


#print axioms circleToInterval_intervalToCircle

theorem intervalRepresentative_eq_rep1 {L : ℝ} [Fact (0 < L)]
    {x : AddCircle L} (hx : x ≠ 0) :
    intervalRepresentative L x = QuantumNLS.HaarResolvent.rep1 L x := by
  have hbounds := QuantumNLS.HaarResolvent.rep1_bounds L x
  have hpos : 0 < QuantumNLS.HaarResolvent.rep1 L x := by
    by_contra hnot
    have hz : QuantumNLS.HaarResolvent.rep1 L x = 0 := by
      exact le_antisymm (not_lt.mp hnot) hbounds.1
    apply hx
    rw [← QuantumNLS.HaarResolvent.coe_rep1 L x, hz]
    simp
  have hrepIoc : QuantumNLS.HaarResolvent.rep1 L x ∈ Set.Ioc 0 L :=
    ⟨hpos, hbounds.2.le⟩
  have hinterval : intervalRepresentative L x ∈ Set.Ioc 0 L := by
    unfold intervalRepresentative
    have hp := (AddCircle.equivIoc L 0 x).property
    simpa [Set.mem_Ioc, zero_add] using hp
  have hcoe : (QuantumNLS.HaarResolvent.rep1 L x : AddCircle L) =
      (intervalRepresentative L x : AddCircle L) := by
    exact (QuantumNLS.HaarResolvent.coe_rep1 L x).trans AddCircle.coe_equivIoc.symm
  have hinterval' : intervalRepresentative L x ∈ Set.Ioc (0 : ℝ) (0 + L) := by
    exact ⟨hinterval.1, by simpa [zero_add] using hinterval.2⟩
  have hrepIoc' : QuantumNLS.HaarResolvent.rep1 L x ∈ Set.Ioc (0 : ℝ) (0 + L) := by
    exact ⟨hrepIoc.1, by simpa [zero_add] using hrepIoc.2⟩
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ioc hinterval' hrepIoc').mp hcoe.symm


#print axioms intervalRepresentative_eq_rep1

theorem circle_ae_to_interval {L : ℝ} [Fact (0 < L)] {P : AddCircle L → Prop}
    (hP : ∀ᵐ x : AddCircle L ∂(volume : Measure (AddCircle L)), P x) :
    ∀ᵐ x : ℝ ∂(LocalSpectral.μI L), P (x : AddCircle L) := by
  have mp := (AddCircle.measurePreserving_mk L (0 : ℝ))
  have hreal := mp.quasiMeasurePreserving.ae hP
  simpa [LocalSpectral.μI, zero_add] using hreal

#print axioms circle_ae_to_interval

theorem intervalToCircle_coe_ae {L : ℝ} [Fact (0 < L)] (f : ScalarInterval L) :
    ∀ᵐ x : ℝ ∂(LocalSpectral.μI L), intervalToCircle L f (x : AddCircle L) = f x := by
  have hcomp : ∀ᵐ y ∂(volume : Measure (AddCircle L)),
      intervalToCircle L f y = f (intervalRepresentative L y) := by
    have h := Lp.coeFn_compMeasurePreserving f
      (interval_representative_measure_preserving L)
    filter_upwards [h] with y hy
    simpa [intervalToCircle, Function.comp_apply] using hy
  have hcompI := circle_ae_to_interval (L := L) hcomp
  have hIoc : ∀ᵐ (x : ℝ) ∂LocalSpectral.μI L, x ∈ Set.Ioc 0 L :=
    ae_restrict_mem measurableSet_Ioc
  filter_upwards [hcompI, hIoc] with x hx hxI
  rw [hx]
  congr 1
  exact AddCircle.equivIoc_coe_of_mem (by simpa [Set.mem_Ioc, zero_add] using hxI)

#print axioms intervalToCircle_coe_ae

theorem circleToInterval_coe_ae {L : ℝ} [Fact (0 < L)]
    (f : Lp ℂ 2 (volume : Measure (AddCircle L))) :
    ∀ᵐ (x : ℝ) ∂LocalSpectral.μI L, circleToInterval L f x = f (x : AddCircle L) := by
  change ∀ᵐ x ∂(volume.restrict (Set.Ioc (0 : ℝ) L)), _
  have h := Lp.coeFn_compMeasurePreserving f
    (by simpa only [zero_add] using (AddCircle.measurePreserving_mk L (0 : ℝ)))
  filter_upwards [h] with x hx
  simpa [circleToInterval, Function.comp_apply] using hx


#print axioms circleToInterval_coe_ae

set_option maxHeartbeats 12000000 in
theorem intervalH1_to_circle {L : ℝ} [Fact (0 < L)]
    (f : ScalarInterval L) (g h : ℝ → ℂ)
    (hf : IntervalH1Rep f g h) :
    QuantumNLS.HaarResolvent.IsH1Rep L (intervalToCircle L f) g h := by
  refine ⟨?_, hf.2.1, hf.2.2⟩
  have hcomp : ∀ᵐ x ∂(volume : Measure (AddCircle L)),
      intervalToCircle L f x = f (intervalRepresentative L x) := by
    have h := Lp.coeFn_compMeasurePreserving f
      (interval_representative_measure_preserving L)
    filter_upwards [h] with x hx
    simpa [intervalToCircle, Function.comp_apply] using hx
  have hsrc :=
    (interval_representative_measure_preserving L).quasiMeasurePreserving.ae hf.1
  letI := QuantumNLS.HaarKernelFactorizationOp.nullSingleton L
  have hne : ∀ᵐ x ∂(volume : Measure (AddCircle L)), x ≠ 0 :=
    Measure.ae_ne _ _
  filter_upwards [hcomp, hsrc, hne] with x hxcomp hxsrc hx0
  exact hxcomp.trans (hxsrc.trans
    (congrArg g (intervalRepresentative_eq_rep1 (L := L) hx0)))


#print axioms intervalH1_to_circle

set_option maxHeartbeats 12000000 in
theorem circleH1_to_interval {L : ℝ} [Fact (0 < L)]
    (f : Lp ℂ 2 (volume : Measure (AddCircle L))) (g h : ℝ → ℂ)
    (hf : QuantumNLS.HaarResolvent.IsH1Rep L f g h) :
    IntervalH1Rep (circleToInterval L f) g h := by
  refine ⟨?_, hf.2.1, hf.2.2⟩
  have mp := (AddCircle.measurePreserving_mk L (0 : ℝ))
  have hcomp : ∀ᵐ (x : ℝ) ∂(LocalSpectral.μI L),
      circleToInterval L f x = f (x : AddCircle L) := by
    have h := Lp.coeFn_compMeasurePreserving f
      (by simpa only [zero_add] using mp)
    filter_upwards [h] with x hx
    simpa [LocalSpectral.μI, circleToInterval, Function.comp_apply] using hx
  have hrep := mp.quasiMeasurePreserving.ae hf.1
  have hrepI : ∀ᵐ (x : ℝ) ∂(LocalSpectral.μI L),
      f (x : AddCircle L) = g (QuantumNLS.HaarResolvent.rep1 L (x : AddCircle L)) := by
    simpa [LocalSpectral.μI] using hrep
  have hneqL : ∀ᵐ (x : ℝ) ∂(LocalSpectral.μI L), x ≠ L := by
    change ∀ᵐ x ∂(volume.restrict (Set.Ioc (0 : ℝ) L)), _
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [QuantumNLS.HaarResolvent.ae_ne_real L] with x hx hxI
    exact hx
  have hIoc : ∀ᵐ (x : ℝ) ∂(LocalSpectral.μI L), x ∈ Set.Ioc 0 L :=
    ae_restrict_mem measurableSet_Ioc
  filter_upwards [hcomp, hrepI, hneqL, hIoc] with x hxcomp hxrep hxL hxI
  calc
    circleToInterval L f x = f (x : AddCircle L) := hxcomp
    _ = g (QuantumNLS.HaarResolvent.rep1 L (x : AddCircle L)) := hxrep
    _ = g x := by
      congr 1
      exact QuantumNLS.HaarResolvent.rep1_coe L
        ⟨hxI.1.le, lt_of_le_of_ne hxI.2 hxL⟩


#print axioms circleH1_to_interval

theorem interval_fourier_parseval (f : ScalarInterval L) :
    ∑' k : ℤ, ‖QuantumNLS.Fourier.fourierL2 L (intervalToCircle L f) k‖ ^ 2 = ‖f‖ ^ 2 := by
  rw [← QuantumNLS.Fourier.hsNormSq_zero L
    (fun k => QuantumNLS.Fourier.fourierL2 L (intervalToCircle L f) k)]
  rw [QuantumNLS.Ext025A2.root01_parseval]
  change ‖Lp.compMeasurePreserving (intervalRepresentative L)
    (interval_representative_measure_preserving L) f‖ ^ 2 = ‖f‖ ^ 2
  exact congrArg (fun x : ℝ => x ^ 2)
    ((Lp.compMeasurePreservingₗᵢ ℂ (intervalRepresentative L)
      (interval_representative_measure_preserving L)).norm_map f)


#print axioms interval_fourier_parseval

end QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
