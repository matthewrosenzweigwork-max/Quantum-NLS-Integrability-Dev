import QuantumNLS.Local001CandidateB

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory AddCircle
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
open QuantumNLS.LocalSpectral
variable (L : ℝ) [Fact (0 < L)]

theorem scalarIntervalResolvent_range {L r : ℝ} [Fact (0 < L)]
    (hL : 0 < L) (hr : 0 < r) (hsmall : r < spacing L / 2)
    {n : ℤ} {z : ℂ} (hz : OnGamma L r n z) (j : Fin 2) (f : ScalarInterval L) :
    ∃ g h, IntervalH1Rep (scalarIntervalResolvent L n z j f) g h ∧
      g L = parityComplex n * g 0 ∧
      ∀ᵐ (x : ℝ) ∂LocalSpectral.μI L,
        z * scalarIntervalResolvent L n z j f x - f x =
          (if j = 0 then 2 * Complex.I * h x else -(2 * Complex.I) * h x) := by
  let ρ := parityComplex n
  let ζ := if j = 0 then -z / 2 else z / 2
  let c := if j = 0 then Complex.I / 2 else -Complex.I / 2
  let ψ : CircleScalar L := c • intervalToCircle L f
  have hq : QuantumNLS.HaarResolvent.qOf L ρ ζ ≠ 1 := by
    simpa [ρ, ζ] using scalarCircleResolvent_q_ne hL hr hsmall hz j
  have hgraph := QuantumNLS.HaarResolvent.resolvent_range
    (L := L) (ρ := ρ) (z := ζ) (parityComplex_sq n) hq ψ
  rcases hgraph with ⟨g, h, hrep, hboundary, haction⟩
  have hcircleAction :
      scalarCircleResolvent L n z j (intervalToCircle L f) =
        QuantumNLS.HaarResolvent.R1 L
          (QuantumNLS.HaarResolvent.qOf L ρ ζ) ζ ψ := by
    by_cases hj : j = 0
    · simp [scalarCircleResolvent, ρ, ζ, c, ψ, hj, ContinuousLinearMap.comp_apply]
    · simp [scalarCircleResolvent, ρ, ζ, c, ψ, hj, ContinuousLinearMap.comp_apply]
  have hout : scalarIntervalResolvent L n z j f =
      circleToInterval L (QuantumNLS.HaarResolvent.R1 L
        (QuantumNLS.HaarResolvent.qOf L ρ ζ) ζ ψ) := by
    apply (intervalToCircleIso L).injective
    calc
      intervalToCircle L (scalarIntervalResolvent L n z j f) =
          scalarCircleResolvent L n z j (intervalToCircle L f) :=
        scalarIntervalResolvent_toCircle L n z j f
      _ = QuantumNLS.HaarResolvent.R1 L
          (QuantumNLS.HaarResolvent.qOf L ρ ζ) ζ ψ := hcircleAction
      _ = intervalToCircle L (circleToInterval L
          (QuantumNLS.HaarResolvent.R1 L
            (QuantumNLS.HaarResolvent.qOf L ρ ζ) ζ ψ)) :=
        (intervalToCircle_circleToInterval L _).symm
  have houtH1 := circleH1_to_interval (L := L)
    (QuantumNLS.HaarResolvent.R1 L (QuantumNLS.HaarResolvent.qOf L ρ ζ) ζ ψ)
    g h hrep
  have hrepOut : IntervalH1Rep (scalarIntervalResolvent L n z j f) g h := by
    rw [hout]
    exact houtH1
  have hneqL : ∀ᵐ (x : ℝ) ∂LocalSpectral.μI L, x ≠ L := by
    change ∀ᵐ x ∂(volume.restrict (Set.Ioc (0 : ℝ) L)), x ≠ L
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [QuantumNLS.HaarResolvent.ae_ne_real L] with x hx hxI
    exact hx
  have hIoc : ∀ᵐ (x : ℝ) ∂LocalSpectral.μI L, x ∈ Set.Ioc 0 L :=
    ae_restrict_mem measurableSet_Ioc
  have hactionI : ∀ᵐ (x : ℝ) ∂LocalSpectral.μI L,
      ψ (x : AddCircle L) = h x - Complex.I * ζ * g x := by
    have hcircle := circle_ae_to_interval (L := L) haction
    filter_upwards [hcircle, hneqL, hIoc] with x hx hxL hxI
    have hrep1 := QuantumNLS.HaarResolvent.rep1_coe L
      ⟨hxI.1.le, lt_of_le_of_ne hxI.2 hxL⟩
    simpa [hrep1] using hx
  have hscale : ∀ᵐ (x : ℝ) ∂LocalSpectral.μI L, ψ (x : AddCircle L) = c * f x := by
    have hsmul := Lp.coeFn_smul c (intervalToCircle L f)
    have hsmulI := circle_ae_to_interval (L := L) hsmul
    have hif := intervalToCircle_coe_ae (L := L) f
    filter_upwards [hsmulI, hif] with x hs hf
    simpa [ψ, hf] using hs
  have hscalar : ∀ᵐ (x : ℝ) ∂LocalSpectral.μI L,
      c * f x = h x - Complex.I * ζ * g x := by
    filter_upwards [hscale, hactionI] with x hs ha
    exact hs.symm.trans ha
  refine ⟨g, h, hrepOut, hboundary, ?_⟩
  filter_upwards [hscalar, hrepOut.1] with x heq houtx
  rw [houtx]
  by_cases hj : j = 0
  · simp [c, ζ, hj, Complex.I_sq] at heq
    simp [hj, Complex.I_sq]
    linear_combination (2 * Complex.I) * heq - (f x - z * g x) * Complex.I_sq
  · simp [c, ζ, hj, Complex.I_sq] at heq
    simp [hj, Complex.I_sq]
    linear_combination (-2 * Complex.I) * heq - (f x - z * g x) * Complex.I_sq


#print axioms scalarIntervalResolvent_range

set_option maxHeartbeats 12000000 in
theorem scalarIntervalResolvent_left_inverse {L r : ℝ} [Fact (0 < L)]
    (hL : 0 < L) (hr : 0 < r) (hsmall : r < spacing L / 2)
    {n : ℤ} {z : ℂ} (hz : OnGamma L r n z) (j : Fin 2)
    (f p : ScalarInterval L) (g h : ℝ → ℂ)
    (hf : IntervalH1Rep f g h)
    (hboundary : g L = parityComplex n * g 0)
    (haction : ∀ᵐ (x : ℝ) ∂LocalSpectral.μI L,
      (if j = 0 then Complex.I / 2 else -Complex.I / 2) * p x =
        h x - Complex.I * (if j = 0 then -z / 2 else z / 2) * g x) :
    scalarIntervalResolvent L n z j p = f := by
  let ρ := parityComplex n
  let ζ := if j = 0 then -z / 2 else z / 2
  let c := if j = 0 then Complex.I / 2 else -Complex.I / 2
  let ψ : CircleScalar L := c • intervalToCircle L p
  have hq : QuantumNLS.HaarResolvent.qOf L ρ ζ ≠ 1 := by
    simpa [ρ, ζ] using scalarCircleResolvent_q_ne hL hr hsmall hz j
  have hfCircle : QuantumNLS.HaarResolvent.IsH1Rep L (intervalToCircle L f) g h :=
    intervalH1_to_circle (L := L) f g h hf
  letI := QuantumNLS.HaarKernelFactorizationOp.nullSingleton L
  have hne : ∀ᵐ y ∂(volume : Measure (AddCircle L)), y ≠ 0 :=
    Measure.ae_ne _ _
  have hactionCircle : ∀ᵐ y ∂(volume : Measure (AddCircle L)),
      ψ y = h (QuantumNLS.HaarResolvent.rep1 L y) -
        Complex.I * ζ * g (QuantumNLS.HaarResolvent.rep1 L y) := by
    have hψ := Lp.coeFn_smul c (intervalToCircle L p)
    have hp := Lp.coeFn_compMeasurePreserving p
      (interval_representative_measure_preserving L)
    have ha := (interval_representative_measure_preserving L).quasiMeasurePreserving.ae haction
    filter_upwards [hψ, hp, ha, hne] with y hψy hpy hay hy0
    have hrep := intervalRepresentative_eq_rep1 (L := L) hy0
    calc
      ψ y = c * intervalToCircle L p y := by simpa [ψ] using hψy
      _ = c * p (intervalRepresentative L y) := by
        exact congrArg (fun a : ℂ => c * a) hpy
      _ = h (QuantumNLS.HaarResolvent.rep1 L y) -
          Complex.I * ζ * g (QuantumNLS.HaarResolvent.rep1 L y) := by
        simpa only [hrep] using hay
  have hgraph :
      (intervalToCircle L f, ψ) ∈ QuantumNLS.HaarResolvent.graphD L ρ ζ := by
    exact ⟨g, h, hfCircle, hboundary, hactionCircle⟩
  have hleft := QuantumNLS.HaarResolvent.resolvent_left_inverse
    (L := L) (ρ := ρ) (z := ζ) (parityComplex_sq n) hq hgraph
  have hcircle : scalarCircleResolvent L n z j (intervalToCircle L p) =
      QuantumNLS.HaarResolvent.R1 L
        (QuantumNLS.HaarResolvent.qOf L ρ ζ) ζ ψ := by
    by_cases hj : j = 0
    · simp [scalarCircleResolvent, ρ, ζ, c, ψ, hj, ContinuousLinearMap.comp_apply]
    · simp [scalarCircleResolvent, ρ, ζ, c, ψ, hj, ContinuousLinearMap.comp_apply]
  apply (intervalToCircleIso L).injective
  change intervalToCircle L (scalarIntervalResolvent L n z j p) = intervalToCircle L f
  rw [scalarIntervalResolvent_toCircle, hcircle, hleft]


#print axioms scalarIntervalResolvent_left_inverse

end QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
