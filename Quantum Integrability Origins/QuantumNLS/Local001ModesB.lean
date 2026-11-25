import QuantumNLS.Local001VectorInverseB

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory AddCircle
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
open QuantumNLS.LocalSpectral
variable (L : ℝ) [Fact (0 < L)]

def componentShift (n : ℤ) (j : Fin 2) : ℤ := if j = 0 then -n else n


#print axioms componentShift

def sourceModeIndex (j : Fin 2) (k : ℤ) : ℤ := if j = 0 then -k else k


#print axioms sourceModeIndex

def sourceMode (n : ℤ) (i : Fin 2 × ℤ) : ℤ := n + 2 * sourceModeIndex i.1 i.2


#print axioms sourceMode

def scalarPairMode (n : ℤ) (i : Fin 2 × ℤ) : ScalarPair L :=
  PiLp.single (p := (2 : ℝ≥0∞)) i.1
    (intervalShiftedBasis L (componentShift n i.1) i.2)


#print axioms scalarPairMode

theorem scalarPairMode_orthonormal (n : ℤ) : Orthonormal ℂ (scalarPairMode L n) := by
  classical
  rw [orthonormal_iff_ite]
  intro i i'
  rcases i with ⟨j, k⟩
  rcases i' with ⟨j', k'⟩
  by_cases hcoord : j = j'
  · subst j'
    fin_cases j
    · have hscalar :=
        (intervalShiftedBasis L (componentShift n (0 : Fin 2))).orthonormal
      have hfreq := orthonormal_iff_ite.mp hscalar k k'
      simpa [scalarPairMode, PiLp.inner_apply, componentShift] using hfreq
    · have hscalar :=
        (intervalShiftedBasis L (componentShift n (1 : Fin 2))).orthonormal
      have hfreq := orthonormal_iff_ite.mp hscalar k k'
      simpa [scalarPairMode, PiLp.inner_apply, componentShift] using hfreq
  · fin_cases j <;> fin_cases j' <;> simp_all [scalarPairMode, PiLp.inner_apply]


#print axioms scalarPairMode_orthonormal

theorem scalarPairMode_orthogonal_eq_bot (n : ℤ) :
    (Submodule.span ℂ (Set.range (scalarPairMode L n)))ᗮ = ⊥ := by
  classical
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  apply PiLp.ext
  intro j
  apply (intervalShiftedBasis L (componentShift n j)).repr.injective
  apply lp.ext
  funext k
  rw [HilbertBasis.repr_apply_apply]
  have horth := (Submodule.mem_orthogonal _ _).mp hx
    (scalarPairMode L n (j, k)) (Submodule.subset_span ⟨(j, k), rfl⟩)
  fin_cases j <;> simpa [scalarPairMode, PiLp.inner_apply] using horth


#print axioms scalarPairMode_orthogonal_eq_bot

def scalarPairBasis (n : ℤ) : HilbertBasis (Fin 2 × ℤ) ℂ (ScalarPair L) :=
  HilbertBasis.mkOfOrthogonalEqBot (scalarPairMode_orthonormal L n)
    (scalarPairMode_orthogonal_eq_bot L n)


#print axioms scalarPairBasis

def vectorModeBasis (n : ℤ) : HilbertBasis (Fin 2 × ℤ) ℂ (VectorInterval L) :=
  HilbertBasis.ofRepr ((vectorComponentsIsometry L).trans (scalarPairBasis L n).repr)

#print axioms vectorModeBasis

theorem vectorModeBasis_apply (n : ℤ) (j : Fin 2) (k : ℤ) :
    vectorModeBasis L n (j, k) =
      intervalFiberInsert L j (intervalShiftedBasis L (componentShift n j) k) := by
  classical
  rw [← HilbertBasis.repr_symm_single (vectorModeBasis L n) (j, k)]
  unfold vectorModeBasis
  change ((vectorComponentsIsometry L).trans (scalarPairBasis L n).repr).symm
      (lp.single 2 (j, k) (1 : ℂ)) = _
  rw [LinearIsometryEquiv.symm_trans, LinearIsometryEquiv.trans_apply,
    HilbertBasis.repr_symm_single]
  change componentsToVectorLinear L (scalarPairBasis L n (j, k)) = _
  fin_cases j
  · simp [scalarPairBasis, scalarPairMode, componentsToVectorLinear,
      componentShift, intervalFiberInsert]
    exact ContinuousLinearMap.map_zero
      ((fiberInsert (1 : Fin 2)).toContinuousLinearMap.compLpL 2
        (volume.restrict (Set.Ioc 0 L)))
  · simp [scalarPairBasis, scalarPairMode, componentsToVectorLinear,
      componentShift, intervalFiberInsert]
    exact ContinuousLinearMap.map_zero
      ((fiberInsert (0 : Fin 2)).toContinuousLinearMap.compLpL 2
        (volume.restrict (Set.Ioc 0 L)))


#print axioms vectorModeBasis_apply

theorem fiberInsert_scalar (j : Fin 2) (a : ℂ) :
    fiberInsert j a = a • EuclideanSpace.single j (1 : ℂ) := by
  apply PiLp.ext
  intro i
  simp [fiberInsert, fiberInsertLinear, EuclideanSpace.single_apply]


#print axioms fiberInsert_scalar

theorem halfFrequencyMode_eq_source (n k : ℤ) (j : Fin 2) (x : ℝ) :
    halfFrequencyPhase L (componentShift n j) x *
        QuantumNLS.Fourier.mode L (sourceModeIndex j k) (x : AddCircle L) =
      (((Real.sqrt L)⁻¹ : ℝ) : ℂ) *
        Complex.exp (LocalSpectral.rate L (n + 2 * k) j * (x : ℂ)) := by
  have hexp :
      ((((Real.pi * (componentShift n j : ℝ) * x / L : ℝ) : ℂ) * Complex.I) +
        (2 * Real.pi * Complex.I * (sourceModeIndex j k : ℂ) * x / L)) =
        LocalSpectral.rate L (n + 2 * k) j * (x : ℂ) := by
    fin_cases j <;>
      simp [componentShift, sourceModeIndex, LocalSpectral.rate,
        LocalSpectral.sgn, LocalSpectral.pm] <;>
      push_cast <;> ring
  unfold halfFrequencyPhase
  rw [QuantumNLS.Fourier.mode_coe]
  calc
    Complex.exp ((((Real.pi * (componentShift n j : ℝ) * x / L : ℝ) : ℂ) * Complex.I)) *
        ((((Real.sqrt L)⁻¹ : ℝ) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * (sourceModeIndex j k : ℂ) * x / L)) =
        (((Real.sqrt L)⁻¹ : ℝ) : ℂ) *
          (Complex.exp ((((Real.pi * (componentShift n j : ℝ) * x / L : ℝ) : ℂ) * Complex.I)) *
            Complex.exp (2 * Real.pi * Complex.I * (sourceModeIndex j k : ℂ) * x / L)) := by
          ring
    _ = (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * Complex.exp
          ((((Real.pi * (componentShift n j : ℝ) * x / L : ℝ) : ℂ) * Complex.I) +
            (2 * Real.pi * Complex.I * (sourceModeIndex j k : ℂ) * x / L)) := by
          rw [← Complex.exp_add]
    _ = (((Real.sqrt L)⁻¹ : ℝ) : ℂ) *
        Complex.exp (LocalSpectral.rate L (n + 2 * k) j * (x : ℂ)) := by rw [hexp]


#print axioms halfFrequencyMode_eq_source

theorem vectorModeBasis_eq_chi (n : ℤ) (j : Fin 2) (k : ℤ) :
    vectorModeBasis L n (j, sourceModeIndex j k) =
      LocalSpectral.chi L (n + 2 * k) j := by
  rw [vectorModeBasis_apply]
  apply Lp.ext
  have hinsert :
      (intervalFiberInsert L j
        (intervalShiftedBasis L (componentShift n j) (sourceModeIndex j k)) : VectorInterval L) =ᵐ[
          volume.restrict (Set.Ioc 0 L)]
        fun x => fiberInsert j
          (intervalShiftedBasis L (componentShift n j) (sourceModeIndex j k) x) := by
    have h := (fiberInsert j).toContinuousLinearMap.coeFn_compLpL
      (intervalShiftedBasis L (componentShift n j) (sourceModeIndex j k))
    filter_upwards [h] with x hx
    change ((fiberInsert j).toContinuousLinearMap.compLpL 2
      (volume.restrict (Set.Ioc 0 L))
      (intervalShiftedBasis L (componentShift n j) (sourceModeIndex j k))) x = _ at hx
    exact hx
  have hshift :
      (intervalShiftedBasis L (componentShift n j) (sourceModeIndex j k) : ℝ → ℂ) =ᵐ[μI L]
        fun x => halfFrequencyPhase L (componentShift n j) x *
          QuantumNLS.Fourier.mode L (sourceModeIndex j k) (x : AddCircle L) := by
    rw [intervalShiftedBasis_apply]
    filter_upwards [halfFrequencyMultiply_coe L (componentShift n j)
        (intervalMode L (sourceModeIndex j k)), intervalMode_coe L (sourceModeIndex j k)]
      with x hx hm
    rw [hx, hm]
  have hchi := (memLp_chiFun L (n + 2 * k) j).coeFn_toLp
  filter_upwards [hinsert, hshift, hchi] with x hi hs hc
  rw [hi, hs]
  change fiberInsert j
      (halfFrequencyPhase L (componentShift n j) x *
        QuantumNLS.Fourier.mode L (sourceModeIndex j k) (x : AddCircle L)) =
    ((memLp_chiFun L (n + 2 * k) j).toLp (chiFun L (n + 2 * k) j)) x
  rw [hc, fiberInsert_scalar, halfFrequencyMode_eq_source]
  rfl




#print axioms vectorModeBasis_eq_chi

theorem sourceMode_parity (n : ℤ) (i : Fin 2 × ℤ) :
    LocalSpectral.parity (sourceMode n i) = LocalSpectral.parity n := by
  let t := sourceModeIndex i.1 i.2
  have hm : sourceMode n i = n + 2 * t := by simp [sourceMode, t]
  rcases Int.even_or_odd' n with ⟨a, ha | ha⟩
  · have hn : Even n := by rw [ha]; exact even_two_mul a
    have hmode : sourceMode n i = 2 * (a + t) := by rw [hm, ha]; ring
    have hmn : Even (sourceMode n i) := by rw [hmode]; exact even_two_mul (a + t)
    simp [LocalSpectral.parity, hn, hmn]
  · have hn : ¬ Even n := by rw [ha]; exact Int.not_even_two_mul_add_one a
    have hmode : sourceMode n i = 2 * (a + t) + 1 := by rw [hm, ha]; ring
    have hmn : ¬ Even (sourceMode n i) := by
      rw [hmode]
      exact Int.not_even_two_mul_add_one (a + t)
    simp [LocalSpectral.parity, hn, hmn]


#print axioms sourceMode_parity

end QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
