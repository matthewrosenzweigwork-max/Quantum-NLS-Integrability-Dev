import QuantumNLS.Local001SeriesB

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory AddCircle
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
open QuantumNLS.LocalSpectral
variable (L : ℝ) [Fact (0 < L)]

def intervalSeriesRep (a : ℤ → ℂ) (ha : Summable fun k => ‖a k‖) : ScalarInterval L :=
  circleToInterval L ((QuantumNLS.Fourier.memLp_seriesRep ha).toLp
    (QuantumNLS.Fourier.seriesRep L a))


#print axioms intervalSeriesRep

theorem intervalFourierIso_intervalSeriesRep_apply (a : ℤ → ℂ)
    (ha : Summable fun k => ‖a k‖) (k : ℤ) :
    intervalFourierIso L (intervalSeriesRep L a ha) k = a k := by
  change QuantumNLS.Fourier.fourierL2 L
      (intervalToCircle L (circleToInterval L
        ((QuantumNLS.Fourier.memLp_seriesRep ha).toLp
          (QuantumNLS.Fourier.seriesRep L a)))) k = a k
  rw [intervalToCircle_circleToInterval]
  rw [QuantumNLS.Fourier.fourierL2_apply,
    QuantumNLS.Fourier.coeff_congr_ae L
      (QuantumNLS.Fourier.memLp_seriesRep ha).coeFn_toLp,
    QuantumNLS.Fourier.coeff_seriesRep ha]


#print axioms intervalFourierIso_intervalSeriesRep_apply

theorem intervalShiftedBasis_seriesRep_coeff (s : ℤ) (a : ℤ → ℂ)
    (ha : Summable fun k => ‖a k‖) (k : ℤ) :
    ⟪intervalShiftedBasis L s k,
      halfFrequencyMultiply L s (intervalSeriesRep L a ha)⟫_ℂ = a k := by
  have hrepr : (intervalShiftedBasis L s).repr
      (halfFrequencyMultiply L s (intervalSeriesRep L a ha)) k = a k := by
    have hcancel : (halfFrequencyMultiplyIso L s).symm
        (halfFrequencyMultiply L s (intervalSeriesRep L a ha)) =
          intervalSeriesRep L a ha := by
      change (halfFrequencyMultiplyIso L s).symm
        ((halfFrequencyMultiplyIso L s) (intervalSeriesRep L a ha)) = _
      exact (halfFrequencyMultiplyIso L s).symm_apply_apply _
    change (intervalFourierIso L
      ((halfFrequencyMultiplyIso L s).symm
        (halfFrequencyMultiply L s (intervalSeriesRep L a ha)))) k = a k
    rw [hcancel]
    exact intervalFourierIso_intervalSeriesRep_apply L a ha k
  rw [← HilbertBasis.repr_apply_apply]
  exact hrepr


#print axioms intervalShiftedBasis_seriesRep_coeff

theorem freeDiagonal_component_eq_seriesRep (hL : 0 < L) (n : ℤ)
    {r : ℝ} {z : ℂ} (hr : 0 < r) (hsmall : r < spacing L / 2)
    (hz : OnGamma L r n z) (f : VectorInterval L) (j : Fin 2) :
    vectorToComponentsLinear L (freeDiagonalResolvent L hL n hr hsmall hz f) j =
      halfFrequencyMultiply L (componentShift n j)
        (intervalSeriesRep L
          (fun k => freeResolventMultiplier L n z (j, k) *
            ⟪vectorModeBasis L n (j, k), f⟫_ℂ)
          (freeResolventCoefficient_l1 L hL n hr hsmall hz f j).1) := by
  apply (intervalShiftedBasis L (componentShift n j)).repr.injective
  apply lp.ext
  funext k
  calc
    ((intervalShiftedBasis L (componentShift n j)).repr
        (vectorToComponentsLinear L (freeDiagonalResolvent L hL n hr hsmall hz f) j)) k =
        ⟪intervalShiftedBasis L (componentShift n j) k,
          vectorToComponentsLinear L (freeDiagonalResolvent L hL n hr hsmall hz f) j⟫_ℂ :=
          HilbertBasis.repr_apply_apply _ _ _
    _ = ⟪vectorModeBasis L n (j, k), freeDiagonalResolvent L hL n hr hsmall hz f⟫_ℂ := by
          rw [vectorModeBasis_inner_component L n j k]
    _ = freeResolventMultiplier L n z (j, k) *
          ⟪vectorModeBasis L n (j, k), f⟫_ℂ :=
          freeDiagonalResolvent_inner L hL n hr hsmall hz (j, k) f
    _ = freeResolventMultiplier L n z (j, k) *
          ⟪intervalShiftedBasis L (componentShift n j) k,
            vectorToComponentsLinear L f j⟫_ℂ := by
          rw [vectorModeBasis_inner_component L n j k f]
    _ = (intervalShiftedBasis L (componentShift n j)).repr
          (halfFrequencyMultiply L (componentShift n j)
            (intervalSeriesRep L
              (fun k => freeResolventMultiplier L n z (j, k) *
                ⟪vectorModeBasis L n (j, k), f⟫_ℂ)
              (freeResolventCoefficient_l1 L hL n hr hsmall hz f j).1)) k := by
          let a : ℤ → ℂ := fun k => freeResolventMultiplier L n z (j, k) *
            ⟪vectorModeBasis L n (j, k), f⟫_ℂ
          have hcoeff := intervalShiftedBasis_seriesRep_coeff L
            (componentShift n j) a (freeResolventCoefficient_l1 L hL n hr hsmall hz f j).1 k
          calc
            freeResolventMultiplier L n z (j, k) *
                ⟪intervalShiftedBasis L (componentShift n j) k,
                  vectorToComponentsLinear L f j⟫_ℂ = a k := by
                    dsimp [a]
                    rw [← vectorModeBasis_inner_component L n j k f]
            _ = (intervalShiftedBasis L (componentShift n j)).repr
                (halfFrequencyMultiply L (componentShift n j)
                  (intervalSeriesRep L a
                    (freeResolventCoefficient_l1 L hL n hr hsmall hz f j).1)) k := by
                    rw [HilbertBasis.repr_apply_apply]
                    exact hcoeff.symm


#print axioms freeDiagonal_component_eq_seriesRep

theorem freeDiagonal_component_ae_bound (hL : 0 < L) (n : ℤ) {r : ℝ} {z : ℂ}
    (hr : 0 < r) (hsmall : r < spacing L / 2) (hz : OnGamma L r n z)
    (f : VectorInterval L) (j : Fin 2) :
    ∀ᵐ x ∂(volume.restrict (Set.Ioc (0 : ℝ) L)),
      ‖vectorToComponentsLinear L (freeDiagonalResolvent L hL n hr hsmall hz f) j x‖ ≤
        (Real.sqrt L)⁻¹ * Real.sqrt (r⁻¹ ^ 2 + 2 *
          ∑' k : ℕ+, (spacing L * (k : ℝ) - r)⁻¹ ^ 2) *
          ‖vectorToComponentsLinear L f j‖ := by
  let a : ℤ → ℂ := fun k => freeResolventMultiplier L n z (j, k) *
    ⟪vectorModeBasis L n (j, k), f⟫_ℂ
  have ha := (freeResolventCoefficient_l1 L hL n hr hsmall hz f j)
  have hrep := freeDiagonal_component_eq_seriesRep L hL n hr hsmall hz f j
  rw [hrep]
  have hpoint : ∀ x : ℝ, ‖halfFrequencyPhase L (componentShift n j) x *
      (QuantumNLS.Fourier.seriesRep L a (x : AddCircle L))‖ =
      ‖QuantumNLS.Fourier.seriesRep L a (x : AddCircle L)‖ := by
    intro x
    rw [norm_mul, norm_halfFrequencyPhase, one_mul]
  have hcoe := (halfFrequencyMultiply_coe L (componentShift n j)
    (intervalSeriesRep L a ha.1))
  have hseries : ∀ᵐ (x : ℝ) ∂μI L,
      intervalSeriesRep L a ha.1 x = QuantumNLS.Fourier.seriesRep L a (x : AddCircle L) := by
    change (Lp.compMeasurePreserving (fun x : ℝ => (x : AddCircle L))
      (interval_quotient_measure_preserving L)
      ((QuantumNLS.Fourier.memLp_seriesRep ha.1).toLp
        (QuantumNLS.Fourier.seriesRep L a)) : ℝ → ℂ) =ᵐ[μI L] _
    have hcomp := Lp.coeFn_compMeasurePreserving
      ((QuantumNLS.Fourier.memLp_seriesRep ha.1).toLp
        (QuantumNLS.Fourier.seriesRep L a)) (interval_quotient_measure_preserving L)
    have hcircle : ∀ᵐ x ∂(volume : Measure (AddCircle L)),
        ((QuantumNLS.Fourier.memLp_seriesRep ha.1).toLp
          (QuantumNLS.Fourier.seriesRep L a) :
            Lp ℂ 2 (volume : Measure (AddCircle L))) x =
          QuantumNLS.Fourier.seriesRep L a x :=
      (QuantumNLS.Fourier.memLp_seriesRep ha.1).coeFn_toLp
    have hcircleInt := (interval_quotient_measure_preserving L).quasiMeasurePreserving.ae hcircle
    filter_upwards [hcomp, hcircleInt] with x hx hc
    exact hx.trans hc
  have hbound : ∀ x : AddCircle L,
      ‖QuantumNLS.Fourier.seriesRep L a x‖ ≤
        (Real.sqrt L)⁻¹ * ∑' k, ‖a k‖ :=
    QuantumNLS.Fourier.norm_seriesRep_le ha.1
  filter_upwards [hcoe, hseries] with x hg hs
  calc
    ‖halfFrequencyMultiply L (componentShift n j)
        (intervalSeriesRep L a ha.1) x‖ =
        ‖halfFrequencyPhase L (componentShift n j) x *
          QuantumNLS.Fourier.seriesRep L a (x : AddCircle L)‖ := by
        rw [hg, hs]
    _ = ‖QuantumNLS.Fourier.seriesRep L a (x : AddCircle L)‖ := hpoint x
    _ ≤ (Real.sqrt L)⁻¹ * ∑' k, ‖a k‖ := hbound (x : AddCircle L)
    _ ≤ (Real.sqrt L)⁻¹ * Real.sqrt (r⁻¹ ^ 2 + 2 *
          ∑' k : ℕ+, (spacing L * (k : ℝ) - r)⁻¹ ^ 2) *
          ‖vectorToComponentsLinear L f j‖ := by
      dsimp [a] at ha
      have hsqrt : 0 ≤ (Real.sqrt L)⁻¹ := by positivity
      have hle := mul_le_mul_of_nonneg_left ha.2 hsqrt
      have hnorm : ‖vectorToComponentsLinear L f j‖ ≥ 0 := norm_nonneg _
      convert hle using 1 <;> ring


#print axioms freeDiagonal_component_ae_bound

end QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
