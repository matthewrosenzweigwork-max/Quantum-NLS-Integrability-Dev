import NlsGge.Weights.SpatialJensen
import NlsGge.Hierarchy.RiccatiUnitPeriodIntervalToPhysicalHaar
import NlsGge.Hierarchy.FullEnergyPlaneConvergence38
import NlsGge.Hierarchy.ALPositiveDecompositions38
import NlsGge.Hierarchy.A01Spectral38
import NlsGge.Spectral.ActualTraceFormulaQ024E02_38
import NlsGge.Sobolev.SmoothRepresentative
import NlsGge.NLS38.SeqConv38
import NlsGge.NLS38.ClassicalSolution38

                                                                                                            
                                                                              
                                                                           
  

set_option autoImplicit false
noncomputable section

namespace NlsGge.ThirdConsultation.Narrative

open NlsGge.Pilot NlsGge.HierarchyRiccati NlsGge.HierarchyRiccati.Core
open NlsGge.SpectralFoundations MeasureTheory
open scoped ContDiff ComplexConjugate

/-- The ordinary derivative of the squared complex norm, without a nonzero-field premise. -/
theorem grouped_norm_sq_deriv (u : ℝ → ℂ) (x : ℝ)
    (hu : DifferentiableAt ℝ u x) :
    deriv (fun y => ‖u y‖ ^ 2) x =
      2 * ((starRingEnd ℂ) (u x) * deriv u x).re := by
  have h := hu.hasDerivAt.norm_sq
  rw [h.deriv]
  change 2 * (deriv u x * (starRingEnd ℂ) (u x)).re =
    2 * ((starRingEnd ℂ) (u x) * deriv u x).re
  rw [mul_comm (deriv u x) ((starRingEnd ℂ) (u x))]

/-- Integrability of the literal second Q4 density on the source smooth domain. -/
theorem grouped_q4_second_integrand_intervalIntegrable (u : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) :
    IntervalIntegrable (fun x =>
      ‖iteratedDeriv 2 u x‖ ^ 2 + 2 * ‖u x‖ ^ 6 +
        6 * ‖u x‖ ^ 2 * ‖deriv u x‖ ^ 2 +
          (deriv (fun y => ‖u y‖ ^ 2) x) ^ 2) volume 0 1 := by
  have hk (k : ℕ) : Continuous (iteratedDeriv k u) := by
    rw [iteratedDeriv_eq_iterate]
    exact (hu.iterate_deriv k).continuous
  have h0 := hu.continuous
  have h1 := hk 1
  simp only [iteratedDeriv_one] at h1
  have h2 := hk 2
  have hn : deriv (fun y => ‖u y‖ ^ 2) =
      fun x => 2 * ((starRingEnd ℂ) (u x) * deriv u x).re := by
    funext x
    exact grouped_norm_sq_deriv u x
      ((hu.differentiable (by simp)).differentiableAt)
  rw [hn]
  exact (by fun_prop : Continuous (fun x =>
    ‖iteratedDeriv 2 u x‖ ^ 2 + 2 * ‖u x‖ ^ 6 +
      6 * ‖u x‖ ^ 2 * ‖deriv u x‖ ^ 2 +
        (2 * ((starRingEnd ℂ) (u x) * deriv u x).re) ^ 2)).intervalIntegrable 0 1

/-- v2 lines 64--74, the literal second complex Q4 integral, with the existing local charge. -/
theorem grouped_q4_second_integral (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) :
    localCharge38 u 2 = ∫ x in (0 : ℝ)..1,
      ‖iteratedDeriv 2 u x‖ ^ 2 + 2 * ‖u x‖ ^ 6 +
        6 * ‖u x‖ ^ 2 * ‖deriv u x‖ ^ 2 +
          (deriv (fun y => ‖u y‖ ^ 2) x) ^ 2 := by
  change (∫ x in (0 : ℝ)..1,
    riccatiJetEvaluation u x (formalChargeIntegrand 2)).re = _
  rw [complexQ4_local_formula_Q024 u hu hper]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [grouped_norm_sq_deriv u x
    ((hu.differentiable (by simp)).differentiableAt)]
  exact q4_integrand_eq (u x) (deriv u x) (iteratedDeriv 2 u x)

/-- The same literal integral is the existing spectrally normalized Q4. -/
theorem grouped_q4_second_integral_spectral (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) :
    spectralCharge38 u hu hper 2 = ∫ x in (0 : ℝ)..1,
      ‖iteratedDeriv 2 u x‖ ^ 2 + 2 * ‖u x‖ ^ 6 +
        6 * ‖u x‖ ^ 2 * ‖deriv u x‖ ^ 2 +
          (deriv (fun y => ‖u y‖ ^ 2) x) ^ 2 := by
  calc
    spectralCharge38 u hu hper 2 = localCharge38 u 2 :=
      (localCharge_eq_spectralCharge38 u hu hper 2).symm
    _ = _ := grouped_q4_second_integral u hu hper

/-- Specialization to the project's actual smooth weighted physical representative. -/
theorem grouped_q4_second_integral_physicalWeighted {lo up : ℝ}
    (c : BoundedCoefficients lo up) (s : ℝ) (u : PhysicalWeighted c s) :
    localCharge38 (physicalWeightedReal c s u) 2 = ∫ x in (0 : ℝ)..1,
      ‖iteratedDeriv 2 (physicalWeightedReal c s u) x‖ ^ 2 +
        2 * ‖physicalWeightedReal c s u x‖ ^ 6 +
          6 * ‖physicalWeightedReal c s u x‖ ^ 2 *
            ‖deriv (physicalWeightedReal c s u) x‖ ^ 2 +
              (deriv (fun y => ‖physicalWeightedReal c s u y‖ ^ 2) x) ^ 2 :=
  grouped_q4_second_integral _ (contDiff_physicalWeightedReal c s u)
    (physicalWeightedReal_periodic c s u)

/-- The witness uses the existing Fourier plane, including its zero mode. -/
theorem grouped_three_mode_physicalFourier :
    physicalFourier (planeL2 1 ![(1 : ℂ), 1, Complex.I]) =
      (Pi.single (-1 : ℤ) (1 : ℂ) + Pi.single (0 : ℤ) 1 + Pi.single (1 : ℤ) Complex.I : ℤ → ℂ) := by
  funext n
  rw [physicalFourier_planeL2, physicalFourier_planeField_sum]
  simp [Fin.sum_univ_succ, modeIndex, Pi.single_apply, eq_comm] <;> ring

/-- Finite support establishes summability before evaluating this convolution. -/
private theorem conv_three_mode49 (a b c : ℂ) (f : ℤ → ℂ) (n : ℤ) :
    Summable (fun k : ℤ =>
      ((Pi.single (-1 : ℤ) a + Pi.single (0 : ℤ) b + Pi.single (1 : ℤ) c : ℤ → ℂ)) k * f (n - k)) ∧
    NlsGge.NLS38.conv
        ((Pi.single (-1 : ℤ) a + Pi.single (0 : ℤ) b + Pi.single (1 : ℤ) c : ℤ → ℂ)) f n =
      a * f (n + 1) + b * f n + c * f (n - 1) := by
  classical
  have hzero : ∀ k : ℤ, k ∉ ({-1, 0, 1} : Finset ℤ) →
      ((Pi.single (-1 : ℤ) a + Pi.single (0 : ℤ) b + Pi.single (1 : ℤ) c : ℤ → ℂ)) k * f (n - k) = 0 := by
    intro k hk
    have hk' : k ≠ -1 ∧ k ≠ 0 ∧ k ≠ 1 := by simpa using hk
    simp [Pi.single_apply, hk'.1, hk'.2.1, hk'.2.2, eq_comm]
  refine ⟨summable_of_ne_finset_zero hzero, ?_⟩
  unfold NlsGge.NLS38.conv
  rw [tsum_eq_sum hzero]
  norm_num [Pi.single_apply] <;> ring

/-- The ordinary symmetric Fourier projection of the project's actual NLS RHS,
at the proposed nonconservation witness. This is a vector-field calculation;
it does not assert the still-unproved Q4 first-variation bridge. -/
theorem grouped_three_mode_projected_rhs :
    (fun i : Fin 3 => NlsGge.NLS38.rhsSeq
      (physicalFourier (planeL2 1 ![(1 : ℂ), 1, Complex.I])) (modeIndex 1 i)) =
      ![-2 - Complex.I * ((((2 * Real.pi) ^ 2 + 10 : ℝ) : ℂ)),
        4 - 10 * Complex.I,
        ((((2 * Real.pi) ^ 2 + 10 : ℝ) : ℂ)) - 2 * Complex.I] := by
  rw [grouped_three_mode_physicalFourier]
  let v : ℤ → ℂ :=
    (Pi.single (-1 : ℤ) (1 : ℂ) + Pi.single (0 : ℤ) 1 + Pi.single (1 : ℤ) Complex.I : ℤ → ℂ)
  have hc : NlsGge.NLS38.cstar v =
      (Pi.single (-1 : ℤ) (-Complex.I) + Pi.single (0 : ℤ) 1 + Pi.single (1 : ℤ) 1 : ℤ → ℂ) := by
    dsimp [v]
    simp only [NlsGge.NLS38.cstar_add, NlsGge.NLS38.cstar_single]
    norm_num <;> abel
  have hconv (n : ℤ) : NlsGge.NLS38.conv v v n =
      v (n + 1) + v n + Complex.I * v (n - 1) := by
    simpa only [one_mul] using (conv_three_mode49 1 1 Complex.I v n).2
  have hnonlin (n : ℤ) : NlsGge.NLS38.nonlin v n =
      2 * (-Complex.I * NlsGge.NLS38.conv v v (n + 1) +
        NlsGge.NLS38.conv v v n + NlsGge.NLS38.conv v v (n - 1)) := by
    unfold NlsGge.NLS38.nonlin
    rw [NlsGge.NLS38.conv_comm (NlsGge.NLS38.conv v v) (NlsGge.NLS38.cstar v), hc]
    simpa only [one_mul] using
      congrArg (fun w : ℂ => 2 * w)
        (conv_three_mode49 (-Complex.I) 1 1 (NlsGge.NLS38.conv v v) n).2
  change (fun i : Fin 3 => NlsGge.NLS38.rhsSeq v (modeIndex 1 i)) = _
  funext i
  fin_cases i <;>
    simp only [NlsGge.NLS38.rhsSeq, hnonlin, hconv] <;>
    apply Complex.ext <;>
    norm_num [v, modeIndex, NlsGge.NLS38.disp, Pi.single_apply,
      Complex.mul_re, Complex.mul_im] <;>
    ring

end NlsGge.ThirdConsultation.Narrative

/-! G13 addition. The preceding version-03 declarations are preserved verbatim.
These coefficient lists are Fourier products, not replacements for the charge.
All source-facing conclusions below use localCharge38 and the actual rhsSeq.
-/

namespace NlsGge.ThirdConsultation.Narrative

open NlsGge.Pilot NlsGge.HierarchyRiccati NlsGge.HierarchyRiccati.Core
open NlsGge.SpectralFoundations MeasureTheory
open scoped ContDiff ComplexConjugate

private def q4CubeCoeffs49 (z : FourierPlane 1) : FourierPlane 3 :=
  ![z 0 ^ 3, 3 * z 0 ^ 2 * z 1,
    3 * z 0 * (z 0 * z 2 + z 1 ^ 2),
    z 1 ^ 3 + 6 * z 0 * z 1 * z 2,
    3 * z 2 * (z 0 * z 2 + z 1 ^ 2),
    3 * z 1 * z 2 ^ 2, z 2 ^ 3]

private def q4WeightedCoeffs49 (z : FourierPlane 1) : FourierPlane 2 :=
  let d : ℂ := 2 * Real.pi * Complex.I
  ![-d * z 0 ^ 2, -d * z 0 * z 1, 0,
    d * z 1 * z 2, d * z 2 ^ 2]

private def q4NormDerivativeCoeffs49 (z : FourierPlane 1) : FourierPlane 2 :=
  let d : ℂ := 2 * Real.pi * Complex.I
  ![-2 * d * z 0 * (starRingEnd ℂ) (z 2),
    -d * (z 0 * (starRingEnd ℂ) (z 1) + z 1 * (starRingEnd ℂ) (z 2)), 0,
    d * (z 1 * (starRingEnd ℂ) (z 0) + z 2 * (starRingEnd ℂ) (z 1)),
    2 * d * z 2 * (starRingEnd ℂ) (z 0)]

private def q4InvariantPolynomial49 (q A B C R : ℝ) : ℝ :=
  q ^ 4 * (A + C) +
    q ^ 2 * (6 * A ^ 2 + 6 * C ^ 2 + 8 * A * C + 8 * B * (A + C) + 4 * R) +
    2 * (A ^ 3 + B ^ 3 + C ^ 3 +
      9 * (A ^ 2 * B + A * B ^ 2 + A ^ 2 * C +
        A * C ^ 2 + B ^ 2 * C + B * C ^ 2) +
      36 * A * B * C + (18 * A + 12 * B + 18 * C) * R)

private theorem q4_fourier_pow49 (x : PhysicalCircle) (n : ℤ) (m : ℕ) :
    fourier ((m : ℤ) * n) x = fourier n x ^ m := by
  induction m with
  | zero =>
      simp only [Nat.cast_zero, zero_mul, pow_zero, fourier_zero]
  | succ m ih =>
      change fourier (((m : ℤ) + 1) * n) x = fourier n x ^ (m + 1)
      rw [add_mul, one_mul, fourier_add, ih, pow_succ]

private theorem q4_field_one49 (z : FourierPlane 1) (x : PhysicalCircle) :
    planeField 1 z x = z 0 * fourier (-1 : ℤ) x + z 1 + z 2 * fourier (1 : ℤ) x := by
  simp only [planeField, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change z 0 * fourier (-1 : ℤ) x +
    (z 1 * fourier (0 : ℤ) x + z 2 * fourier (1 : ℤ) x) = _
  simp only [fourier_zero, mul_one]
  ring

private theorem q4_field_two49 (w : FourierPlane 2) (x : PhysicalCircle) :
    planeField 2 w x =
      w 0 * fourier (-2 : ℤ) x + (w 1 * fourier (-1 : ℤ) x +
        (w 2 * fourier (0 : ℤ) x + (w 3 * fourier (1 : ℤ) x + w 4 * fourier (2 : ℤ) x))) := by
  simp only [planeField, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  rfl

private theorem q4_field_three49 (w : FourierPlane 3) (x : PhysicalCircle) :
    planeField 3 w x =
      w 0 * fourier (-3 : ℤ) x + (w 1 * fourier (-2 : ℤ) x +
        (w 2 * fourier (-1 : ℤ) x + (w 3 * fourier (0 : ℤ) x +
          (w 4 * fourier (1 : ℤ) x + (w 5 * fourier (2 : ℤ) x + w 6 * fourier (3 : ℤ) x))))) := by
  simp only [planeField, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  rfl

private theorem q4_derivative_field_one49 (z : FourierPlane 1) (x : PhysicalCircle) :
    planeField 1 (derivativePlane 1 z) x =
      (2 * Real.pi * Complex.I) *
        (-z 0 * fourier (-1 : ℤ) x + z 2 * fourier (1 : ℤ) x) := by
  have hm0 : (modeIndex 1 (0 : Fin 3) : ℂ) = -1 := by norm_num [modeIndex]
  have hm1 : (modeIndex 1 (1 : Fin 3) : ℂ) = 0 := by norm_num [modeIndex]
  have hm2 : (modeIndex 1 (2 : Fin 3) : ℂ) = 1 := by norm_num [modeIndex]
  rw [q4_field_one49]
  simp only [derivativePlane, hm0, hm1, hm2, mul_zero, mul_one, add_zero]
  ring

private theorem q4_cube_field49 (z : FourierPlane 1) (x : PhysicalCircle) :
    planeField 1 z x ^ 3 = planeField 3 (q4CubeCoeffs49 z) x := by
  let p : ℂ := fourier (-1 : ℤ) x
  let r : ℂ := fourier (1 : ℤ) x
  have hpq : p * r = 1 := by
    change fourier (-1 : ℤ) x * fourier (1 : ℤ) x = 1
    calc
      fourier (-1 : ℤ) x * fourier (1 : ℤ) x = fourier ((-1 : ℤ) + 1) x :=
        fourier_add.symm
      _ = 1 := fourier_zero
  have hm2 : fourier (-2 : ℤ) x = p ^ 2 := by
    exact q4_fourier_pow49 x (-1) 2
  have hm3 : fourier (-3 : ℤ) x = p ^ 3 := by
    exact q4_fourier_pow49 x (-1) 3
  have hp2 : fourier (2 : ℤ) x = r ^ 2 := by
    exact q4_fourier_pow49 x 1 2
  have hp3 : fourier (3 : ℤ) x = r ^ 3 := by
    exact q4_fourier_pow49 x 1 3
  rw [q4_field_one49]
  rw [q4_field_three49]
  simp only [q4CubeCoeffs49, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_succ,
    fourier_zero, mul_one]
  rw [hm2, hm3, hp2, hp3]
  change (z 0 * p + z 1 + z 2 * r) ^ 3 = _
  linear_combination
    (3 * z 0 ^ 2 * z 2 * p + 6 * z 0 * z 1 * z 2 + 3 * z 0 * z 2 ^ 2 * r) * hpq

private theorem q4_weighted_field49 (z : FourierPlane 1) (x : PhysicalCircle) :
    planeField 1 z x * planeField 1 (derivativePlane 1 z) x =
      planeField 2 (q4WeightedCoeffs49 z) x := by
  have hm2 : fourier (-2 : ℤ) x = fourier (-1 : ℤ) x ^ 2 := by
    exact q4_fourier_pow49 x (-1) 2
  have hp2 : fourier (2 : ℤ) x = fourier (1 : ℤ) x ^ 2 := by
    exact q4_fourier_pow49 x 1 2
  simp only [q4_derivative_field_one49]
  simp only [q4_field_one49]
  rw [q4_field_two49]
  simp only [q4WeightedCoeffs49, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_succ,
    zero_mul, add_zero]
  rw [hm2, hp2]
  ring

private theorem q4_norm_derivative_field49 (z : FourierPlane 1) (x : PhysicalCircle) :
    (starRingEnd ℂ) (planeField 1 z x) * planeField 1 (derivativePlane 1 z) x +
      planeField 1 z x * (starRingEnd ℂ) (planeField 1 (derivativePlane 1 z) x) =
        planeField 2 (q4NormDerivativeCoeffs49 z) x := by
  have hm2 : fourier (-2 : ℤ) x = fourier (-1 : ℤ) x ^ 2 := by
    exact q4_fourier_pow49 x (-1) 2
  have hp2 : fourier (2 : ℤ) x = fourier (1 : ℤ) x ^ 2 := by
    exact q4_fourier_pow49 x 1 2
  have hcm : (starRingEnd ℂ) (fourier (-1 : ℤ) x) = fourier (1 : ℤ) x := by
    exact (fourier_neg (n := (-1 : ℤ)) (x := x)).symm
  have hcp : (starRingEnd ℂ) (fourier (1 : ℤ) x) = fourier (-1 : ℤ) x :=
    fourier_neg.symm
  simp only [q4_derivative_field_one49]
  simp only [q4_field_one49]
  rw [q4_field_two49]
  simp only [q4NormDerivativeCoeffs49, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_succ,
    zero_mul, add_zero]
  rw [hm2, hp2]
  simp only [map_add, map_mul, map_neg, map_ofNat, Complex.conj_ofReal,
    Complex.conj_I, hcm, hcp]
  ring

private theorem q4_plane_norm_integral49 (N : ℕ) (z : FourierPlane N) :
    (∫ x in (0 : ℝ)..1, ‖planeReal N z x‖ ^ 2) =
      ∑ i : Fin (2 * N + 1), ‖z i‖ ^ 2 := by
  exact (unitIntervalIntegral_lift_eq_spatialHaar
    (fun x : PhysicalCircle => ‖planeField N z x‖ ^ 2)).trans
      (NlsGge.Weights.plane_mass_integral_eq_sum N z)

private theorem q4_plane_normsum49 (z : FourierPlane 1) :
    localCharge38 (planeReal 1 z) 2 =
      (∑ i : Fin 3, ‖derivativePlane 1 (derivativePlane 1 z) i‖ ^ 2) +
      2 * (∑ i : Fin 7, ‖q4CubeCoeffs49 z i‖ ^ 2) +
      6 * (∑ i : Fin 5, ‖q4WeightedCoeffs49 z i‖ ^ 2) +
      (∑ i : Fin 5, ‖q4NormDerivativeCoeffs49 z i‖ ^ 2) := by
  have hI (N : ℕ) (w : FourierPlane N) :
      IntervalIntegrable (fun x => ‖planeReal N w x‖ ^ 2) volume 0 1 :=
    ((contDiff_planeReal N w).continuous.norm.pow 2).intervalIntegrable 0 1
  have hdensity :
      (fun x : ℝ => ‖iteratedDeriv 2 (planeReal 1 z) x‖ ^ 2 +
        2 * ‖planeReal 1 z x‖ ^ 6 +
        6 * ‖planeReal 1 z x‖ ^ 2 * ‖deriv (planeReal 1 z) x‖ ^ 2 +
        (deriv (fun y => ‖planeReal 1 z y‖ ^ 2) x) ^ 2) =
      (fun x : ℝ => ‖planeReal 1 (derivativePlane 1 (derivativePlane 1 z)) x‖ ^ 2 +
        2 * ‖planeReal 3 (q4CubeCoeffs49 z) x‖ ^ 2 +
        6 * ‖planeReal 2 (q4WeightedCoeffs49 z) x‖ ^ 2 +
        ‖planeReal 2 (q4NormDerivativeCoeffs49 z) x‖ ^ 2) := by
    funext x
    have hlead : ‖iteratedDeriv 2 (planeReal 1 z) x‖ ^ 2 =
        ‖planeReal 1 (derivativePlane 1 (derivativePlane 1 z)) x‖ ^ 2 := by
      rw [iteratedDeriv_planeReal, Function.iterate_succ_apply', Function.iterate_one]
    have hsix : ‖planeReal 1 z x‖ ^ 6 = ‖planeReal 3 (q4CubeCoeffs49 z) x‖ ^ 2 := by
      change ‖planeField 1 z (x : PhysicalCircle)‖ ^ 6 =
        ‖planeField 3 (q4CubeCoeffs49 z) (x : PhysicalCircle)‖ ^ 2
      rw [← q4_cube_field49, norm_pow]
      ring
    have hweighted : ‖planeReal 1 z x‖ ^ 2 * ‖deriv (planeReal 1 z) x‖ ^ 2 =
        ‖planeReal 2 (q4WeightedCoeffs49 z) x‖ ^ 2 := by
      rw [deriv_planeReal]
      change ‖planeField 1 z (x : PhysicalCircle)‖ ^ 2 *
          ‖planeField 1 (derivativePlane 1 z) (x : PhysicalCircle)‖ ^ 2 =
        ‖planeField 2 (q4WeightedCoeffs49 z) (x : PhysicalCircle)‖ ^ 2
      rw [← q4_weighted_field49, norm_mul, mul_pow]
    have hnormderiv : (deriv (fun y => ‖planeReal 1 z y‖ ^ 2) x) ^ 2 =
        ‖planeReal 2 (q4NormDerivativeCoeffs49 z) x‖ ^ 2 := by
      rw [grouped_norm_sq_deriv _ x (hasDerivAt_planeReal 1 z x).differentiableAt,
        deriv_planeReal]
      have hcast :
          (starRingEnd ℂ) (planeReal 1 z x) * planeReal 1 (derivativePlane 1 z) x +
            planeReal 1 z x * (starRingEnd ℂ) (planeReal 1 (derivativePlane 1 z) x) =
          (((2 * ((starRingEnd ℂ) (planeReal 1 z x) *
            planeReal 1 (derivativePlane 1 z) x).re : ℝ)) : ℂ) := by
        change (starRingEnd ℂ) (planeReal 1 z x) * planeReal 1 (derivativePlane 1 z) x +
            planeReal 1 z x * (starRingEnd ℂ) (planeReal 1 (derivativePlane 1 z) x) =
          (((2 * ((starRingEnd ℂ) (planeReal 1 z x) *
            planeReal 1 (derivativePlane 1 z) x).re : ℝ)) : ℂ)
        apply Complex.ext <;>
          simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
            Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im] <;>
          ring
      have hc : planeReal 2 (q4NormDerivativeCoeffs49 z) x =
          (((2 * ((starRingEnd ℂ) (planeReal 1 z x) *
            planeReal 1 (derivativePlane 1 z) x).re : ℝ)) : ℂ) :=
        (q4_norm_derivative_field49 z (x : PhysicalCircle)).symm.trans hcast
      rw [hc]
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [hlead, hsix, hnormderiv]
    linear_combination 6 * hweighted
  have h0 := hI 1 (derivativePlane 1 (derivativePlane 1 z))
  have h1 := (hI 3 (q4CubeCoeffs49 z)).const_mul 2
  have h2 := (hI 2 (q4WeightedCoeffs49 z)).const_mul 6
  have h3 := hI 2 (q4NormDerivativeCoeffs49 z)
  rw [grouped_q4_second_integral _ (planeReal_smooth38 1 z) (planeReal_periodic 1 z),
    hdensity]
  rw [intervalIntegral.integral_add ((h0.add h1).add h2) h3,
    intervalIntegral.integral_add (h0.add h1) h2,
    intervalIntegral.integral_add h0 h1,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  simp only [q4_plane_norm_integral49]

/-- Exact Q4 polynomial on the actual three-mode Fourier plane. -/
theorem grouped_q4_three_mode_polynomial (z : FourierPlane 1) :
    localCharge38 (planeReal 1 z) 2 =
      let a := z 0
      let b := z 1
      let c := z 2
      let A := ‖a‖ ^ 2
      let B := ‖b‖ ^ 2
      let C := ‖c‖ ^ 2
      let R := (a * c * (starRingEnd ℂ) b ^ 2).re
      let q := 2 * Real.pi
      q ^ 4 * (A + C) +
        q ^ 2 * (6 * A ^ 2 + 6 * C ^ 2 + 8 * A * C + 8 * B * (A + C) + 4 * R) +
        2 * (A ^ 3 + B ^ 3 + C ^ 3 +
          9 * (A ^ 2 * B + A * B ^ 2 + A ^ 2 * C +
            A * C ^ 2 + B ^ 2 * C + B * C ^ 2) +
          36 * A * B * C + (18 * A + 12 * B + 18 * C) * R) := by
  rw [q4_plane_normsum49]
  norm_num only [q4CubeCoeffs49, q4WeightedCoeffs49, q4NormDerivativeCoeffs49,
    derivativePlane, modeIndex, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_succ]
  simp only [Complex.sq_norm, Complex.normSq_apply]
  simp only [pow_succ, pow_zero, mul_one]
  norm_num [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.neg_re, Complex.neg_im, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im] <;> ring

/-- The source Q4 restriction is genuinely differentiable; its fderiv is not a junk value. -/
theorem grouped_three_mode_q4_differentiable :
    Differentiable ℝ (fun w : FourierPlane 1 => localCharge38 (planeReal 1 w) 2) := by
  have hcoord (i : Fin 3) : Differentiable ℝ (fun w : FourierPlane 1 => w i) := by
    fun_prop
  have hA := (hcoord 0).norm_sq ℝ
  have hB := (hcoord 1).norm_sq ℝ
  have hC := (hcoord 2).norm_sq ℝ
  have hconj : Differentiable ℝ (fun w : FourierPlane 1 => (starRingEnd ℂ) (w 1)) :=
    (hcoord 1).star
  have hR : Differentiable ℝ
      (fun w : FourierPlane 1 => (w 0 * w 2 * (starRingEnd ℂ) (w 1) ^ 2).re) :=
    Complex.reCLM.differentiable.comp (((hcoord 0).mul (hcoord 2)).mul (hconj.pow 2))
  have heq : (fun w : FourierPlane 1 => localCharge38 (planeReal 1 w) 2) =
      fun w => q4InvariantPolynomial49 (2 * Real.pi)
        (‖w 0‖ ^ 2) (‖w 1‖ ^ 2) (‖w 2‖ ^ 2)
        (w 0 * w 2 * (starRingEnd ℂ) (w 1) ^ 2).re := by
    funext w
    exact grouped_q4_three_mode_polynomial w
  rw [heq]
  unfold q4InvariantPolynomial49
  fun_prop

/-- Exact directional derivative of the existing Q4 along the actual projected cubic-NLS RHS. -/
theorem grouped_three_mode_q4_directional_derivative :
    fderiv ℝ
      (fun w : FourierPlane 1 => localCharge38 (planeReal 1 w) 2)
      ![(1 : ℂ), 1, Complex.I]
      (fun i : Fin 3 => NlsGge.NLS38.rhsSeq
        (physicalFourier (planeL2 1 ![(1 : ℂ), 1, Complex.I]))
        (modeIndex 1 i)) = 384 * Real.pi ^ 2 := by
  let q : ℝ := 2 * Real.pi
  let z : FourierPlane 1 := ![(1 : ℂ), 1, Complex.I]
  let v : FourierPlane 1 :=
    ![-2 - Complex.I * ((q ^ 2 + 10 : ℝ) : ℂ), 4 - 10 * Complex.I,
      ((q ^ 2 + 10 : ℝ) : ℂ) - 2 * Complex.I]
  let γ : ℝ → (Fin 3 → ℂ) := fun t => z + t • v
  have hγ : HasDerivAt γ v (0 : ℝ) := by
    refine hasDerivAt_pi.2 fun i => ?_
    change HasDerivAt (fun t : ℝ => z i + t • v i) (v i) (0 : ℝ)
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const (v i)).const_add (z i) using 1 <;>
      simp only [one_smul, id_eq]
  have hzero : γ 0 = z := by simp [γ]
  let A : ℝ → ℝ := fun t => ‖γ t 0‖ ^ 2
  let B : ℝ → ℝ := fun t => ‖γ t 1‖ ^ 2
  let C : ℝ → ℝ := fun t => ‖γ t 2‖ ^ 2
  let R : ℝ → ℝ := fun t => (γ t 0 * γ t 2 * (starRingEnd ℂ) (γ t 1) ^ 2).re
  have ha := hasDerivAt_pi.1 hγ (0 : Fin 3)
  have hb := hasDerivAt_pi.1 hγ (1 : Fin 3)
  have hc := hasDerivAt_pi.1 hγ (2 : Fin 3)
  have hqre : ((q : ℂ) ^ 2).re = q ^ 2 := by
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have hqim : ((q : ℂ) ^ 2).im = 0 := by
    rw [← Complex.ofReal_pow, Complex.ofReal_im]
  have hA : HasDerivAt A (-4) 0 := by
    convert ha.norm_sq using 1 <;>
      norm_num [A, hzero, z, v, Complex.inner, Complex.mul_re, Complex.mul_im, hqre, hqim] <;> ring
  have hB : HasDerivAt B 8 0 := by
    convert hb.norm_sq using 1 <;>
      norm_num [B, hzero, z, v, Complex.inner, Complex.mul_re, Complex.mul_im, hqre, hqim] <;> ring
  have hC : HasDerivAt C (-4) 0 := by
    convert hc.norm_sq using 1 <;>
      norm_num [C, hzero, z, v, Complex.inner, Complex.mul_re, Complex.mul_im, hqre, hqim] <;> ring
  have hcb : HasDerivAt (fun t => (starRingEnd ℂ) (γ t 1)) ((starRingEnd ℂ) (v 1)) 0 :=
    hb.star
  have hRc := (ha.mul hc).mul (hcb.pow (𝕜 := ℝ) (n := 2))
  have hR : HasDerivAt R (2 * q ^ 2) 0 := by
    have hRe0 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hRc
    have hRe : HasDerivAt R
        (((v 0 * γ 0 2 + γ 0 0 * v 2) * ((starRingEnd ℂ) (γ 0 1)) ^ 2 +
          (γ 0 0 * γ 0 2) *
            ((2 : ℂ) * ((starRingEnd ℂ) (γ 0 1)) ^ (2 - 1) *
              (starRingEnd ℂ) (v 1))).re) (0 : ℝ) := by
      convert! hRe0 using 1 <;>
        simp only [R, Function.comp_def, Pi.mul_apply, Pi.pow_apply,
          Complex.reCLM_apply]
    refine hRe.congr_deriv ?_
    norm_num [hzero, z, v, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, hqre, hqim] <;> ring
  have hA0 : A 0 = 1 := by simp [A, hzero, z]
  have hB0 : B 0 = 1 := by simp [B, hzero, z]
  have hC0 : C 0 = 1 := by simp [C, hzero, z]
  have hR0 : R 0 = 0 := by simp [R, hzero, z]
  have hlead := (hA.add hC).const_mul (q ^ 4)
  have hquart := (((((hA.pow 2).const_mul 6).add ((hC.pow 2).const_mul 6)).add
    ((hA.mul hC).const_mul 8)).add ((hB.mul (hA.add hC)).const_mul 8)).add
      (hR.const_mul 4)
  have hpairs := ((((((hA.pow 2).mul hB).add (hA.mul (hB.pow 2))).add
    ((hA.pow 2).mul hC)).add (hA.mul (hC.pow 2))).add
      ((hB.pow 2).mul hC)).add (hB.mul (hC.pow 2))
  have hsix := ((((hA.pow 3).add (hB.pow 3)).add (hC.pow 3)).add
    (hpairs.const_mul 9)).add (((hA.mul hB).mul hC).const_mul 36)
  have hlast := (((hA.const_mul 18).add (hB.const_mul 12)).add
    (hC.const_mul 18)).mul hR
  have hpoly := (hlead.add (hquart.const_mul (q ^ 2))).add ((hsix.add hlast).const_mul 2)
  have hpath : HasDerivAt
      (fun t => localCharge38 (planeReal 1 (γ t)) 2) (384 * Real.pi ^ 2) 0 := by
    convert hpoly using 1
    · funext t
      calc
        localCharge38 (planeReal 1 (γ t)) 2 =
            q4InvariantPolynomial49 (2 * Real.pi)
              (‖γ t 0‖ ^ 2) (‖γ t 1‖ ^ 2) (‖γ t 2‖ ^ 2)
              (γ t 0 * γ t 2 * (starRingEnd ℂ) (γ t 1) ^ 2).re :=
          grouped_q4_three_mode_polynomial (γ t)
        _ = _ := by
          dsimp only [q4InvariantPolynomial49, A, B, C, R, q,
            Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
          ring
    · norm_num [hA0, hB0, hC0, hR0, q] <;> ring
  let L : ℝ →L[ℝ] (Fin 3 → ℂ) := (1 : ℝ →L[ℝ] ℝ).smulRight v
  have hL : HasFDerivAt (fun t : ℝ => z + L t) L (0 : ℝ) :=
    L.hasFDerivAt.const_add z
  have hcomp := (grouped_three_mode_q4_differentiable (z + L 0)).hasFDerivAt.comp
    (0 : ℝ) hL
  have hchain : HasDerivAt (fun t => localCharge38 (planeReal 1 (γ t)) 2)
      (fderiv ℝ (fun w : FourierPlane 1 => localCharge38 (planeReal 1 w) 2) z v) 0 := by
    convert! hcomp.hasDerivAt using 1 <;>
      simp [γ, L, Function.comp_def]
  have hvalue := hchain.unique hpath
  rw [grouped_three_mode_projected_rhs]
  change fderiv ℝ (fun w : FourierPlane 1 => localCharge38 (planeReal 1 w) 2) z v = _
  simpa only [hzero] using hvalue

/-- The source's three-mode truncation fails to conserve the restricted higher charge Q4. -/
theorem grouped_three_mode_q4_nonconservation :
    fderiv ℝ
      (fun w : FourierPlane 1 => localCharge38 (planeReal 1 w) 2)
      ![(1 : ℂ), 1, Complex.I]
      (fun i : Fin 3 => NlsGge.NLS38.rhsSeq
        (physicalFourier (planeL2 1 ![(1 : ℂ), 1, Complex.I]))
        (modeIndex 1 i)) ≠ 0 := by
  rw [grouped_three_mode_q4_directional_derivative]
  exact ne_of_gt (mul_pos (by norm_num : (0 : ℝ) < 384) (pow_pos Real.pi_pos 2))

/-- Existential form of the source's qualified nonconservation assertion. -/
theorem grouped_fourier_truncation_nonconservation :
    ∃ (N j : ℕ) (z : FourierPlane N),
      fderiv ℝ (fun w : FourierPlane N => localCharge38 (planeReal N w) j) z
        (fun i : Fin (2 * N + 1) => NlsGge.NLS38.rhsSeq
          (physicalFourier (planeL2 N z)) (modeIndex N i)) ≠ 0 := by
  exact ⟨1, 2, ![(1 : ℂ), 1, Complex.I], grouped_three_mode_q4_nonconservation⟩

end NlsGge.ThirdConsultation.Narrative
