import QuantumNLS.Local001PolesB

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory AddCircle
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
open QuantumNLS.LocalSpectral

noncomputable def scalarCircleResolvent (L : ℝ) [Fact (0 < L)]
    (n : ℤ) (z : ℂ) (j : Fin 2) :
    CircleScalar L →L[ℂ] CircleScalar L := by
  let ρ := parityComplex n
  exact if j = 0 then
    (QuantumNLS.HaarResolvent.R1 L
      (QuantumNLS.HaarResolvent.qOf L ρ (-z / 2)) (-z / 2)).comp
        ((Complex.I / 2) • ContinuousLinearMap.id ℂ _)
  else
    (QuantumNLS.HaarResolvent.R1 L
      (QuantumNLS.HaarResolvent.qOf L ρ (z / 2)) (z / 2)).comp
        ((-Complex.I / 2) • ContinuousLinearMap.id ℂ _)


#print axioms scalarCircleResolvent

noncomputable def scalarIntervalResolvent (L : ℝ) [Fact (0 < L)]
    (n : ℤ) (z : ℂ) (j : Fin 2) : ScalarInterval L →L[ℂ] ScalarInterval L :=
  (intervalToCircleIso L).symm.toLinearIsometry.toContinuousLinearMap.comp
    ((scalarCircleResolvent L n z j).comp
      (intervalToCircleIso L).toLinearIsometry.toContinuousLinearMap)


#print axioms scalarIntervalResolvent

noncomputable def scalarPairResolvent (L : ℝ) [Fact (0 < L)]
    (n : ℤ) (z : ℂ) : ScalarPair L →L[ℂ] ScalarPair L := by
  let e := PiLp.continuousLinearEquiv (2 : ℝ≥0∞) ℂ
    (fun _ : Fin 2 => ScalarInterval L)
  exact e.symm.toContinuousLinearMap.comp (ContinuousLinearMap.pi fun j =>
    (scalarIntervalResolvent L n z j).comp
      ((ContinuousLinearMap.proj j).comp e.toContinuousLinearMap))


#print axioms scalarPairResolvent

noncomputable def freeResolventCandidate (L : ℝ) [Fact (0 < L)]
    (n : ℤ) (z : ℂ) : VectorInterval L →L[ℂ] VectorInterval L :=
  (vectorComponentsIsometry L).symm.toLinearIsometry.toContinuousLinearMap.comp
    ((scalarPairResolvent L n z).comp
      (vectorComponentsIsometry L).toLinearIsometry.toContinuousLinearMap)

#print axioms freeResolventCandidate

theorem scalarPairResolvent_apply (L : ℝ) [Fact (0 < L)] (n : ℤ) (z : ℂ)
    (v : ScalarPair L) (j : Fin 2) :
    scalarPairResolvent L n z v j = scalarIntervalResolvent L n z j (v j) := by
  classical
  simp [scalarPairResolvent, ContinuousLinearMap.comp_apply]

#print axioms scalarPairResolvent_apply

theorem scalarIntervalResolvent_toCircle (L : ℝ) [Fact (0 < L)]
    (n : ℤ) (z : ℂ) (j : Fin 2) (f : ScalarInterval L) :
    intervalToCircle L (scalarIntervalResolvent L n z j f) =
      scalarCircleResolvent L n z j (intervalToCircle L f) := by
  change (intervalToCircleIso L)
      ((intervalToCircleIso L).symm
        (scalarCircleResolvent L n z j ((intervalToCircleIso L) f))) = _
  simp only [LinearIsometryEquiv.apply_symm_apply]
  congr 1

#print axioms scalarIntervalResolvent_toCircle

theorem freeResolventCandidate_component (L : ℝ) [Fact (0 < L)]
    (n : ℤ) (z : ℂ) (f : VectorInterval L) (j : Fin 2) :
    vectorToComponentsLinear L (freeResolventCandidate L n z f) j =
      scalarIntervalResolvent L n z j (vectorToComponentsLinear L f j) := by
  change (vectorComponentsIsometry L (freeResolventCandidate L n z f)) j = _
  simp [freeResolventCandidate, scalarPairResolvent_apply]
  congr 1

#print axioms freeResolventCandidate_component

theorem scalarCircleResolvent_q_ne {L r : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hsmall : r < spacing L / 2) {n : ℤ} {z : ℂ} (hz : OnGamma L r n z)
    (j : Fin 2) :
    QuantumNLS.HaarResolvent.qOf L (parityComplex n)
      (if j = 0 then -z / 2 else z / 2) ≠ 1 := by
  by_cases hj : j = 0
  · apply scalarContour_q_ne hL hr hsmall hz (-1) (Or.inr rfl) <;> simp [hj]
  · apply scalarContour_q_ne hL hr hsmall hz 1 (Or.inl rfl) <;> simp [hj]


#print axioms scalarCircleResolvent_q_ne

end QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
