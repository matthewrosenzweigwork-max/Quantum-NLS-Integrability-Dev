import QuantumNLS.Local001TransportB

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory AddCircle
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
open QuantumNLS.LocalSpectral
variable (L : ℝ) [Fact (0 < L)]

def halfFrequencyPhase (n : ℤ) (x : ℝ) : ℂ :=
  Complex.exp ((((Real.pi * (n : ℝ) * x / L : ℝ) : ℂ) * Complex.I))

#print axioms halfFrequencyPhase

omit [Fact (0 < L)] in
theorem norm_halfFrequencyPhase (n : ℤ) (x : ℝ) :
    ‖halfFrequencyPhase L n x‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

#print axioms norm_halfFrequencyPhase

omit [Fact (0 < L)] in
theorem continuous_halfFrequencyPhase (n : ℤ) :
    Continuous (halfFrequencyPhase L n) := by
  unfold halfFrequencyPhase
  fun_prop

#print axioms continuous_halfFrequencyPhase

omit [Fact (0 < L)] in
theorem memLp_halfFrequencyPhase (n : ℤ) :
    MemLp (halfFrequencyPhase L n) ∞ (volume.restrict (Set.Ioc (0 : ℝ) L)) := by
  refine MemLp.of_bound (continuous_halfFrequencyPhase L n).aestronglyMeasurable 1 ?_
  filter_upwards [] with x
  rw [norm_halfFrequencyPhase]


#print axioms memLp_halfFrequencyPhase

def halfFrequencyMultiply (n : ℤ) (f : ScalarInterval L) : ScalarInterval L :=
  ((memLp_halfFrequencyPhase L n).smul (Lp.memLp f)).toLp
    (fun x => halfFrequencyPhase L n x * f x)

#print axioms halfFrequencyMultiply

omit [Fact (0 < L)] in
theorem halfFrequencyMultiply_coe (n : ℤ) (f : ScalarInterval L) :
    (halfFrequencyMultiply L n f : ℝ → ℂ) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) L)]
      (fun x => halfFrequencyPhase L n x * f x) :=
  ((memLp_halfFrequencyPhase L n).smul (Lp.memLp f)).coeFn_toLp

#print axioms halfFrequencyMultiply_coe

omit [Fact (0 < L)] in
theorem halfFrequencyMultiply_add (n : ℤ) (f g : ScalarInterval L) :
    halfFrequencyMultiply L n (f + g) =
      halfFrequencyMultiply L n f + halfFrequencyMultiply L n g := by
  apply Lp.ext
  filter_upwards [halfFrequencyMultiply_coe L n (f + g),
    halfFrequencyMultiply_coe L n f, halfFrequencyMultiply_coe L n g,
    Lp.coeFn_add f g, Lp.coeFn_add (halfFrequencyMultiply L n f) (halfFrequencyMultiply L n g)]
    with x hsum hf hg hfg hout
  rw [hsum, hfg, hout]
  simp only [Pi.add_apply]
  rw [hf, hg]
  ring

#print axioms halfFrequencyMultiply_add

omit [Fact (0 < L)] in
theorem halfFrequencyMultiply_smul (n : ℤ) (c : ℂ) (f : ScalarInterval L) :
    halfFrequencyMultiply L n (c • f) = c • halfFrequencyMultiply L n f := by
  apply Lp.ext
  filter_upwards [halfFrequencyMultiply_coe L n (c • f),
    halfFrequencyMultiply_coe L n f, Lp.coeFn_smul c f,
    Lp.coeFn_smul c (halfFrequencyMultiply L n f)] with x hmul hf hsmul hout
  rw [hmul, hsmul, hout]
  simp only [Pi.smul_apply]
  rw [hf]
  ring

#print axioms halfFrequencyMultiply_smul

omit [Fact (0 < L)] in
theorem halfFrequencyPhase_neg_mul (n : ℤ) (x : ℝ) :
    halfFrequencyPhase L n x * halfFrequencyPhase L (-n) x = 1 := by
  unfold halfFrequencyPhase
  rw [← Complex.exp_add]
  have he : ((((Real.pi * (n : ℝ) * x / L : ℝ) : ℂ) * Complex.I) +
      (((Real.pi * ((-n : ℤ) : ℝ) * x / L : ℝ) : ℂ) * Complex.I)) = 0 := by
    push_cast
    ring
  rw [he, Complex.exp_zero]

#print axioms halfFrequencyPhase_neg_mul

omit [Fact (0 < L)] in
theorem halfFrequencyMultiply_neg (n : ℤ) (f : ScalarInterval L) :
    halfFrequencyMultiply L n (halfFrequencyMultiply L (-n) f) = f := by
  apply Lp.ext
  filter_upwards [halfFrequencyMultiply_coe L n (halfFrequencyMultiply L (-n) f),
    halfFrequencyMultiply_coe L (-n) f] with x houter hinner
  rw [houter, hinner, ← mul_assoc, halfFrequencyPhase_neg_mul]
  simp

#print axioms halfFrequencyMultiply_neg

omit [Fact (0 < L)] in
theorem norm_halfFrequencyMultiply (n : ℤ) (f : ScalarInterval L) :
    ‖halfFrequencyMultiply L n f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  exact eLpNorm_congr_enorm_ae
    (Lp.aestronglyMeasurable (halfFrequencyMultiply L n f)) (Lp.aestronglyMeasurable f) <| by
      filter_upwards [halfFrequencyMultiply_coe L n f] with x hx
      rw [hx]
      have hp : ‖halfFrequencyPhase L n x‖ₑ = 1 := by
        rw [enorm_eq_nnnorm]
        have hnn : ‖halfFrequencyPhase L n x‖₊ = 1 := by
          apply Subtype.ext
          exact norm_halfFrequencyPhase L n x
        rw [hnn]
        rfl
      simp only [enorm_mul, hp, one_mul]


#print axioms norm_halfFrequencyMultiply

def halfFrequencyMultiplyIso (n : ℤ) :
    ScalarInterval L ≃ₗᵢ[ℂ] ScalarInterval L where
  toFun := halfFrequencyMultiply L n
  invFun := halfFrequencyMultiply L (-n)
  left_inv := by intro f; simpa only [neg_neg] using halfFrequencyMultiply_neg L (-n) f
  right_inv := halfFrequencyMultiply_neg L n
  map_add' := halfFrequencyMultiply_add L n
  map_smul' := halfFrequencyMultiply_smul L n
  norm_map' := norm_halfFrequencyMultiply L n

#print axioms halfFrequencyMultiplyIso

theorem interval_quotient_measure_preserving :
    MeasurePreserving (fun x : ℝ => (x : AddCircle L))
      (volume.restrict (Set.Ioc (0 : ℝ) L)) (volume : Measure (AddCircle L)) := by
  simpa only [zero_add] using (AddCircle.measurePreserving_mk L (0 : ℝ))


#print axioms interval_quotient_measure_preserving

def intervalFourierIso : ScalarInterval L ≃ₗᵢ[ℂ] lp (fun _ : ℤ => ℂ) 2 :=
  (intervalToCircleIso L).trans (QuantumNLS.Fourier.fourierL2 L)


#print axioms intervalFourierIso

def intervalMode (k : ℤ) : ScalarInterval L :=
  circleToInterval L (QuantumNLS.Fourier.modeLp L k)

#print axioms intervalMode

theorem intervalFourierIso_intervalMode (k : ℤ) :
    intervalFourierIso L (intervalMode L k) = lp.single 2 k (1 : ℂ) := by
  change QuantumNLS.Fourier.fourierL2 L
    (intervalToCircle L (circleToInterval L (QuantumNLS.Fourier.modeLp L k))) = _
  rw [intervalToCircle_circleToInterval]
  exact QuantumNLS.Fourier.fourierL2_modeLp L k

#print axioms intervalFourierIso_intervalMode

theorem intervalToCircle_intervalMode (k : ℤ) :
    intervalToCircle L (intervalMode L k) = QuantumNLS.Fourier.modeLp L k := by
  exact intervalToCircle_circleToInterval L (QuantumNLS.Fourier.modeLp L k)

#print axioms intervalToCircle_intervalMode

theorem intervalMode_eq_circleToInterval (k : ℤ) :
    intervalMode L k = circleToInterval L (QuantumNLS.Fourier.modeLp L k) := by
  rfl

#print axioms intervalMode_eq_circleToInterval

theorem intervalMode_coe (k : ℤ) :
    (intervalMode L k : ℝ → ℂ) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) L)]
      fun x => QuantumNLS.Fourier.mode L k (x : AddCircle L) := by
  rw [intervalMode_eq_circleToInterval]
  change (Lp.compMeasurePreserving (fun x : ℝ => (x : AddCircle L))
    (interval_quotient_measure_preserving L) (QuantumNLS.Fourier.modeLp L k) : ℝ → ℂ) =ᵐ[_] _
  have hcoe := Lp.coeFn_compMeasurePreserving (QuantumNLS.Fourier.modeLp L k)
    (interval_quotient_measure_preserving L)
  have hmode := (interval_quotient_measure_preserving L).quasiMeasurePreserving.ae
    (QuantumNLS.Fourier.coeFn_modeLp L k)
  filter_upwards [hcoe, hmode] with x h1 h2
  rw [h1]
  simpa only [Function.comp_apply] using h2


#print axioms intervalMode_coe

def intervalBasis : HilbertBasis ℤ ℂ (ScalarInterval L) :=
  HilbertBasis.ofRepr (intervalFourierIso L)

#print axioms intervalBasis

theorem intervalBasis_apply (k : ℤ) : intervalBasis L k = intervalMode L k := by
  classical
  rw [← HilbertBasis.repr_symm_single]
  change (intervalFourierIso L).symm (lp.single 2 k (1 : ℂ)) = _
  rw [← intervalFourierIso_intervalMode L k, LinearIsometryEquiv.symm_apply_apply]


#print axioms intervalBasis_apply

def intervalShiftedBasis (n : ℤ) : HilbertBasis ℤ ℂ (ScalarInterval L) :=
  HilbertBasis.ofRepr ((halfFrequencyMultiplyIso L n).symm.trans (intervalFourierIso L))

#print axioms intervalShiftedBasis

theorem intervalShiftedBasis_apply (n k : ℤ) :
    intervalShiftedBasis L n k = halfFrequencyMultiply L n (intervalMode L k) := by
  classical
  rw [← HilbertBasis.repr_symm_single]
  show (((halfFrequencyMultiplyIso L n).symm.trans (intervalFourierIso L)).symm
      (lp.single 2 k (1 : ℂ))) = _
  rw [LinearIsometryEquiv.symm_trans, LinearIsometryEquiv.trans_apply,
    ← intervalFourierIso_intervalMode L k, LinearIsometryEquiv.symm_apply_apply]
  rfl




#print axioms intervalShiftedBasis_apply

end QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
