import QuantumNLS.BetheGeneralSlice

/-! Literal singleton placement endpoints for arbitrary spectator count.
Source periodic_basis.tex:316–333 and the source periodic boundary balance.
This is an action bridge, not an assumed Bethe eigenrelation. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace ComplexConjugate
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
namespace QuantumNLS.BetheGeneralSliceEndpoints
open TensorCarrier TensorPlacements PhysicalTensor TensorFourier BetheIntegralOperator
open BetheTensorSlice BetheTransferOperators BetheTransferKernelAdjoint BetheExtension
open BetheWeakGradient BetheFiniteNAction
variable (L : ℝ) [Fact (0 < L)]

/-- Ordinary-volume conversion for a scalar torus representative. -/
theorem integral_scalar_representative (f : ℝ → ℂ) (hf : Measurable f) :
    (∫ t : AddCircle L, f (representatives L (fun _ : Fin 1 => t) 0)) =
      ∫ t in Icc 0 L, f t := by
  calc
    _ = ∫ t : Fin 1 → AddCircle L, f (representatives L t 0) := by
      symm
      rw [volume_pi]
      convert (measurePreserving_funUnique (volume : Measure (AddCircle L)) (Fin 1)).integral_comp'
          (fun t => f (representatives L (fun _ : Fin 1 => t) 0)) using 1
      simp only [MeasurableEquiv.funUnique_apply, Fin.default_eq_zero, representatives]
      rfl
    _ = ∫ t, f (t 0) ∂cubeMeasure 1 L := by
      conv_lhs => rw [volume_pi]
      exact integral_representatives L (fun t : Fin 1 → ℝ => f (t 0))
        (hf.comp (measurable_pi_apply 0))
    _ = _ := by
      rw [cubeMeasure_eq_pi]
      exact (measurePreserving_funUnique (volume.restrict (Icc (0 : ℝ) L))
        (Fin 1)).integral_comp' f

/-- Exact upper one-body kernel acting on a two-body slice. -/
theorem rawPlus_slice {L u : ℝ} (hu : u ∈ Ioo 0 L) (f : ℝ → ℂ) (z : ℂ) :
    (∫ t in Icc 0 L, rawPlus L z (fun _ : Fin 1 => u) (fun _ => t) * f t) =
      ∫ t in 0..u, Complex.exp (Complex.I*z*(u-t)) * f t := by
  have he (t : ℝ) : rawPlus L z (fun _ : Fin 1 => u) (fun _ => t) * f t =
      (Ioo 0 u).indicator (fun t => Complex.exp (Complex.I*z*(u-t)) * f t) t := by
    have ho : PlusOrder L (fun _ : Fin 1 => u) (fun _ => t) ↔ t ∈ Ioo 0 u := by
      simp [PlusOrder, hu.2]
    simp only [rawPlus, ho, displacement, Fin.sum_univ_one]
    by_cases ht : t ∈ Ioo 0 u <;> simp [ht]
  simp_rw [he]
  rw [integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
    inter_eq_left.mpr (show Ioo 0 u ⊆ Icc 0 L from fun t ht => ⟨ht.1.le, ht.2.le.trans hu.2.le⟩),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hu.1.le]

/-- Exact lower branch, with its full physical exp(izL) multiplier. -/
theorem rawMinus_slice {L u : ℝ} (hu : u ∈ Ioo 0 L) (f : ℝ → ℂ) (z : ℂ) :
    (∫ t in Icc 0 L, rawMinus L z (fun _ : Fin 1 => u) (fun _ => t) * f t) =
      Complex.exp (Complex.I*z*L) *
        ∫ t in u..L, Complex.exp (Complex.I*z*(u-t)) * f t := by
  have he (t : ℝ) : rawMinus L z (fun _ : Fin 1 => u) (fun _ => t) * f t =
      (Ioo u L).indicator (fun t => Complex.exp (Complex.I*z*L) *
        (Complex.exp (Complex.I*z*(u-t)) * f t)) t := by
    have ho : MinusOrder L (fun _ : Fin 1 => u) (fun _ => t) ↔ t ∈ Ioo u L := by
      simp [MinusOrder, PlusOrder, hu.1]
    simp only [rawMinus, ho, Fin.sum_univ_one]
    by_cases ht : t ∈ Ioo u L
    · simp only [ht, ite_true, indicator_of_mem ht, ← mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    · simp [ht]
  simp_rw [he]
  rw [integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
    inter_eq_left.mpr (show Ioo u L ⊆ Icc 0 L from fun t ht => ⟨hu.1.le.trans ht.1.le, ht.2.le⟩),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hu.2.le,
    intervalIntegral.integral_const_mul]


/-- A continuous N-body function with all spectator coordinates held fixed. -/
def line (q : ℕ) (F : C(Fin (1+q) → AddCircle L, ℂ))
    (x : Fin (1+q) → AddCircle L) (t : ℝ) : ℂ :=
  F (Fin.append (fun _ : Fin 1 => (t : AddCircle L))
    (fun i : Fin q => x (Fin.natAdd 1 i)))

/-- The literal first placement, with all physical endpoints and the full
lower-branch exp(izL), for every continuous input and any spectator count. -/
theorem slice_endpoints (q : ℕ) (z : ℂ)
    (F : C(Fin (1+q) → AddCircle L, ℂ)) (x : Fin (1+q) → AddCircle L)
    (hx : representatives L x (Fin.castAdd q 0) ∈ Ioo 0 L) :
    BetheGeneralSlice.slice L q (physicalScalarKernel L z) F x =
      (∫ t in 0..representatives L x (Fin.castAdd q 0),
        Complex.exp (Complex.I*z*(representatives L x (Fin.castAdd q 0)-t)) * line L q F x t) +
      Complex.exp (Complex.I*z*L) *
        ∫ t in representatives L x (Fin.castAdd q 0)..L,
          Complex.exp (Complex.I*z*(representatives L x (Fin.castAdd q 0)-t)) * line L q F x t := by
  have hp := BetheGeneralSlice.integrable_slice L q (scalarPull L (plusKernel L 1 z)) F x
  have hm := BetheGeneralSlice.integrable_slice L q (scalarPull L (minusKernel L 1 z)) F x
  change (∫ t : AddCircle L,
    ((scalarPull L (plusKernel L 1 z)).fn (x (Fin.castAdd q 0),t) +
      (scalarPull L (minusKernel L 1 z)).fn (x (Fin.castAdd q 0),t)) *
        F (Fin.append (fun _ : Fin 1 => t) (fun i : Fin q => x (Fin.natAdd 1 i)))) = _
  simp_rw [add_mul]
  rw [integral_add hp hm]
  have hc : Continuous (line L q F x) := by unfold line; fun_prop
  have he (t : AddCircle L) :
      line L q F x (representatives L (fun _ : Fin 1 => t) 0) =
        F (Fin.append (fun _ : Fin 1 => t) (fun i : Fin q => x (Fin.natAdd 1 i))) := by
    unfold line
    congr 1
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]
      exact AddCircle.coe_equivIco
    · rw [Fin.append_right, Fin.append_right]
  have hpmeas : Measurable (fun t : ℝ => rawPlus L z
      (fun _ : Fin 1 => representatives L x (Fin.castAdd q 0)) (fun _ => t) * line L q F x t) :=
    ((measurable_rawPlus 1 L z).comp
      (show Measurable (fun t : ℝ => ((fun _ : Fin 1 => representatives L x (Fin.castAdd q 0)),
        (fun _ : Fin 1 => t))) by fun_prop)).mul hc.measurable
  have hmmeas : Measurable (fun t : ℝ => rawMinus L z
      (fun _ : Fin 1 => representatives L x (Fin.castAdd q 0)) (fun _ => t) * line L q F x t) :=
    ((measurable_rawMinus 1 L z).comp
      (show Measurable (fun t : ℝ => ((fun _ : Fin 1 => representatives L x (Fin.castAdd q 0)),
        (fun _ : Fin 1 => t))) by fun_prop)).mul hc.measurable
  have hpconv := integral_scalar_representative L _ hpmeas
  have hmconv := integral_scalar_representative L _ hmmeas
  simp_rw [he] at hpconv hmconv
  change (∫ t : AddCircle L, rawPlus L z
      (fun _ : Fin 1 => representatives L x (Fin.castAdd q 0))
      (fun _ => representatives L (fun _ : Fin 1 => t) 0) *
        F (Fin.append (fun _ : Fin 1 => t) (fun i : Fin q => x (Fin.natAdd 1 i)))) = _ at hpconv
  change (∫ t : AddCircle L, rawMinus L z
      (fun _ : Fin 1 => representatives L x (Fin.castAdd q 0))
      (fun _ => representatives L (fun _ : Fin 1 => t) 0) *
        F (Fin.append (fun _ : Fin 1 => t) (fun i : Fin q => x (Fin.natAdd 1 i)))) = _ at hmconv
  change (∫ t : AddCircle L, rawPlus L z
      (fun _ : Fin 1 => representatives L x (Fin.castAdd q 0))
      (fun _ => representatives L (fun _ : Fin 1 => t) 0) *
        F (Fin.append (fun _ : Fin 1 => t) (fun i : Fin q => x (Fin.natAdd 1 i)))) +
    (∫ t : AddCircle L, rawMinus L z
      (fun _ : Fin 1 => representatives L x (Fin.castAdd q 0))
      (fun _ => representatives L (fun _ : Fin 1 => t) 0) *
        F (Fin.append (fun _ : Fin 1 => t) (fun i : Fin q => x (Fin.natAdd 1 i)))) = _
  rw [hpconv, hmconv, rawPlus_slice hx, rawMinus_slice hx]

/-- The completed-tensor placement has the displayed endpoint action a.e.
No coordinate-action hypothesis is an input. -/
theorem physical_firstPlacement_ae (q : ℕ) (z : ℂ)
    (F : C(Fin (1+q) → AddCircle L, ℂ)) :
    physUnitary (firstPlacement (q := q) (BethePhysicalTransfer.physicalKernel L 1 z)
      ((physUnitary (L := L) (N := 1+q)).symm
        (ContinuousMap.toLp 2 (torusPiMeasure L (1+q)) ℂ F))) =ᵐ[torusPiMeasure L (1+q)]
      BetheGeneralSlice.slice L q (physicalScalarKernel L z) F := by
  have h := congrArg (fun M : C(Fin (1+q) → AddCircle L, ℂ) →L[ℂ] L2TN L (1+q) => M F)
    (BetheGeneralSlice.physical_tensorMap_eq_sliceMap L q z)
  change physUnitary (firstPlacement (q := q) (BethePhysicalTransfer.physicalKernel L 1 z)
      ((physUnitary (L := L) (N := 1+q)).symm
        (ContinuousMap.toLp 2 (torusPiMeasure L (1+q)) ℂ F))) = _ at h
  rw [h]
  exact BetheGeneralSlice.coe_sliceMap L q _ F

/-- Cancellation of the ACTUAL source's paired physical outer endpoints.
The lower endpoint keeps exp(izL). Periodicity is derived from the source
Bethe roots by the frozen outer-face theorem, for any spectator configuration.
This does not cancel the remaining cross-degree transfer terms. -/
theorem source_outer_endpoint_cancel {N : ℕ} {c : ℝ} (hc : 0 < c)
    {n : Fin (N+1) → ℤ} (hn : Antitone n) (s : Fin N → ℝ)
    (hs : ∀ i, s i ∈ Icc 0 L) (z : ℂ) (u : ℝ) :
    Complex.exp (Complex.I*z*L) * Complex.exp (Complex.I*z*(u-L)) *
        symmetricExtension L c n (Fin.cons L s) -
      Complex.exp (Complex.I*z*u) * symmetricExtension L c n (Fin.cons 0 s) = 0 := by
  rw [symmetricExtension_outer_faces (Fact.out : 0 < L) hc hn s hs,
    ← Complex.exp_add]
  have he : Complex.I*z*(L : ℂ) + Complex.I*z*((u : ℂ)-(L : ℂ)) = Complex.I*z*u := by
    ring
  rw [he, sub_self]

/-- Every fixed coordinate avoids the periodic seam a.e., in every dimension. -/
theorem representatives_interior_ae (M : ℕ) (i : Fin M) :
    ∀ᵐ x ∂torusPiMeasure L M, representatives L x i ∈ Ioo 0 L := by
  have hne : ∀ᵐ x ∂cubeMeasure M L, x i ≠ 0 := by
    apply ae_restrict_of_ae
    rw [volume_pi]
    exact Measure.ae_eval_ne (fun _ : Fin M => (volume : Measure ℝ)) i 0
  have hh : ∀ᵐ x ∂cubeMeasure M L,
      representatives L (fun j => (x j : AddCircle L)) i ∈ Ioo 0 L := by
    filter_upwards [representatives_coe_ae M L, hne] with x hx hn
    have ht : representatives L (fun j => (x j : AddCircle L)) i ∈ Ico 0 L := by
      simpa [representatives] using (AddCircle.equivIco L 0 (x i : AddCircle L)).property
    rw [hx] at ht ⊢
    exact ⟨lt_of_le_of_ne ht.1 (Ne.symm hn), ht.2⟩
  have hp := cube_to_torus_measurePreserving M L
  rw [show torusPiMeasure L M = volume by rfl, ← hp.map_eq]
  exact (ae_map_iff hp.aemeasurable (measurableSet_Ioo.preimage
    ((measurable_pi_apply i).comp (measurable_representatives M L)))).mpr hh

/-- Completed physical tensor action by the two literal interval integrals,
for every particle count 1+q and every continuous input, at every complex z. -/
theorem physical_firstPlacement_endpoints_ae (q : ℕ) (z : ℂ)
    (F : C(Fin (1+q) → AddCircle L, ℂ)) :
    physUnitary (firstPlacement (q := q) (BethePhysicalTransfer.physicalKernel L 1 z)
      ((physUnitary (L := L) (N := 1+q)).symm
        (ContinuousMap.toLp 2 (torusPiMeasure L (1+q)) ℂ F))) =ᵐ[torusPiMeasure L (1+q)]
      fun x =>
        (∫ t in 0..representatives L x (Fin.castAdd q 0),
          Complex.exp (Complex.I*z*(representatives L x (Fin.castAdd q 0)-t)) * line L q F x t) +
        Complex.exp (Complex.I*z*L) *
          ∫ t in representatives L x (Fin.castAdd q 0)..L,
            Complex.exp (Complex.I*z*(representatives L x (Fin.castAdd q 0)-t)) * line L q F x t := by
  filter_upwards [physical_firstPlacement_ae L q z F,
    representatives_interior_ae L (1+q) (Fin.castAdd q 0)] with x hx hi
  exact hx.trans (slice_endpoints L q z F x hi)

/-- Continuous packaging of the actual positive-c source-root Bethe wave. -/
def sourceInput {M : ℕ} {c : ℝ} (hc : 0 < c) {n : Fin M → ℤ} (hn : Antitone n) :
    C(Fin M → AddCircle L, ℂ) :=
  ⟨torusExtension L c n, by
    cases M with
    | zero =>
      have he : torusExtension L c n = fun _ : Fin 0 → AddCircle L =>
          torusExtension L c n (fun _ => 0) :=
        funext (fun x => congrArg (torusExtension L c n) (Subsingleton.elim x _))
      rw [he]
      exact continuous_const
    | succ N => exact continuous_torusExtension hc hn⟩

/-- The new continuous packaging realizes exactly the frozen source vector,
with its original normalization, in the original completed tensor carrier. -/
theorem sourceInput_tensor_eq {N : ℕ} {c : ℝ} (hc : 0 < c)
    {n : Fin (N+1) → ℤ} (hn : Antitone n) :
    (physUnitary (L := L) (N := N+1)).symm
      (ContinuousMap.toLp 2 (torusPiMeasure L (N+1)) ℂ (sourceInput L hc hn)) =
        (BetheFiniteNAction.physicalWave L hc hn).1 := by
  apply (physUnitary (L := L) (N := N+1)).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  have h := BetheFiniteNAction.positionInclusion_physicalWave L hc hn
  change physUnitary (BetheFiniteNAction.physicalWave L hc hn).1 = _ at h
  rw [h]
  apply Lp.ext
  filter_upwards [ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (𝕜 := ℂ)
    (torusPiMeasure L (N+1)) (sourceInput L hc hn), BetheH1.coe_wave (L := L) hc hn]
    with x hx hy
  exact hx.trans hy.symm

/-- The source's actual all-N singleton placement has the proved slice action.
The input vector is bound to physicalWave by sourceInput_tensor_eq. -/
theorem source_firstPlacement_ae (q : ℕ) {c : ℝ} (hc : 0 < c)
    {n : Fin (1+q) → ℤ} (hn : Antitone n) (z : ℂ) :
    physUnitary (firstPlacement (q := q) (BethePhysicalTransfer.physicalKernel L 1 z)
      ((physUnitary (L := L) (N := 1+q)).symm
        (ContinuousMap.toLp 2 (torusPiMeasure L (1+q)) ℂ (sourceInput L hc hn)))) =ᵐ[torusPiMeasure L (1+q)]
      fun x =>
        (∫ t in 0..representatives L x (Fin.castAdd q 0),
          Complex.exp (Complex.I*z*(representatives L x (Fin.castAdd q 0)-t)) *
            line L q (sourceInput L hc hn) x t) +
        Complex.exp (Complex.I*z*L) *
          ∫ t in representatives L x (Fin.castAdd q 0)..L,
            Complex.exp (Complex.I*z*(representatives L x (Fin.castAdd q 0)-t)) *
              line L q (sourceInput L hc hn) x t :=
  physical_firstPlacement_endpoints_ae L q z (sourceInput L hc hn)

/-- Exact P_N normalization of the degree-one placement: the average of
literal slice outputs, with no probability-volume or extra factorial change.
The sole premise identifies the continuous representative of the input. -/
theorem normalized_placement (q : ℕ) (z : ℂ)
    (F : C(Fin (1+q) → AddCircle L, ℂ))
    (ψ : SymSector ℂ (L2T L) (1+q))
    (hψ : physUnitary ψ.1 = ContinuousMap.toLp 2 (torusPiMeasure L (1+q)) ℂ F) :
    physUnitary ((BethePhysicalTransfer.placement (q := q)
      (BethePhysicalTransfer.physicalKernel L 1 z) ψ).1) =
      ((((1+q).factorial : ℂ)⁻¹) •
        ∑ σ : Equiv.Perm (Fin (1+q)), physPerm σ
          (BetheGeneralSlice.sliceMap L q (physicalScalarKernel L z) F)) := by
  have hi : ψ.1 = (physUnitary (L := L) (N := 1+q)).symm
      (ContinuousMap.toLp 2 (torusPiMeasure L (1+q)) ℂ F) := by
    rw [← hψ, LinearIsometryEquiv.symm_apply_apply]
  have hs := congrArg (fun M : C(Fin (1+q) → AddCircle L, ℂ) →L[ℂ] L2TN L (1+q) => M F)
    (BetheGeneralSlice.physical_tensorMap_eq_sliceMap L q z)
  change physUnitary (firstPlacement (q := q) (BethePhysicalTransfer.physicalKernel L 1 z)
    ((physUnitary (L := L) (N := 1+q)).symm
      (ContinuousMap.toLp 2 (torusPiMeasure L (1+q)) ℂ F))) = _ at hs
  change physUnitary (((SymSector ℂ (L2T L) (1+q)).subtypeL.adjoint
    (firstPlacement (q := q) (BethePhysicalTransfer.physicalKernel L 1 z) ψ.1)).1) = _
  rw [Submodule.adjoint_subtypeL, Submodule.coe_orthogonalProjectionOnto_apply,
    ← symProj_eq_starProjection, symProj_eq_factorial_average]
  simp only [smul_apply, sum_apply, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  change physEmbed (L := L) (N := 1+q) ((permRep ℂ (L2T L) (1+q) σ : HilbertTensorPower ℂ (L2T L) (1+q) →L[ℂ] HilbertTensorPower ℂ (L2T L) (1+q))
    (firstPlacement (q := q) (BethePhysicalTransfer.physicalKernel L 1 z) ψ.1)) = _
  rw [physEmbed_permRep]
  change physPerm σ (physUnitary (firstPlacement (q := q)
    (BethePhysicalTransfer.physicalKernel L 1 z) ψ.1)) = _
  rw [hi, hs]

/-- The source total-particle wrapper retains the actual singleton placement. -/
theorem totalPlacement_one (q : ℕ)
    (A : SymSector ℂ (L2T L) 1 →L[ℂ] SymSector ℂ (L2T L) 1) :
    BethePhysicalTransfer.totalPlacement (1+q) 1 (by omega) A =
      BethePhysicalTransfer.placement (q := q) A := by
  have hcast (r : ℕ) (hr : 1+r=1+q) (hrq : r=q) :
      KernelDefinition.castSymSectorOperator hr
        (BethePhysicalTransfer.placement (q := r) A) =
          BethePhysicalTransfer.placement (q := q) A := by
    subst r
    rfl
  exact hcast ((1+q)-1) (Nat.add_sub_of_le (by omega)) (by omega)

/-- The literal degree-one source contribution at every N=1+q. Its scalar
is exactly c*N and its P_N average is exactly 1/N!, with no extra factor. -/
theorem transferTerm_one (q : ℕ) (c : ℝ) (z : ℂ)
    (F : C(Fin (1+q) → AddCircle L, ℂ))
    (ψ : SymSector ℂ (L2T L) (1+q))
    (hψ : physUnitary ψ.1 = ContinuousMap.toLp 2 (torusPiMeasure L (1+q)) ℂ F) :
    physUnitary ((BethePhysicalTransfer.transferTerm L (1+q) c z ⟨1,by omega⟩ ψ).1) =
      ((c * (1+q) : ℝ) : ℂ) •
        (((((1+q).factorial : ℂ)⁻¹)) •
          ∑ σ : Equiv.Perm (Fin (1+q)), physPerm σ
            (BetheGeneralSlice.sliceMap L q (physicalScalarKernel L z) F)) := by
  simp only [BethePhysicalTransfer.transferTerm, zero_lt_one, ↓reduceIte,
    pow_one, Nat.descFactorial_one, totalPlacement_one]
  change physUnitary (((c * (((1+q : ℕ) : ℝ)) : ℝ) : ℂ) •
    ((BethePhysicalTransfer.placement (q := q)
      (BethePhysicalTransfer.physicalKernel L 1 z) ψ).1)) = _
  rw [map_smul, normalized_placement L q z F ψ hψ]
  push_cast
  rfl

end QuantumNLS.BetheGeneralSliceEndpoints

#print axioms QuantumNLS.BetheGeneralSliceEndpoints.integral_scalar_representative
#print axioms QuantumNLS.BetheGeneralSliceEndpoints.rawPlus_slice
#print axioms QuantumNLS.BetheGeneralSliceEndpoints.rawMinus_slice
#print axioms QuantumNLS.BetheGeneralSliceEndpoints.line
#print axioms QuantumNLS.BetheGeneralSliceEndpoints.slice_endpoints
#print axioms QuantumNLS.BetheGeneralSliceEndpoints.physical_firstPlacement_ae
#print axioms QuantumNLS.BetheGeneralSliceEndpoints.source_outer_endpoint_cancel
#print axioms QuantumNLS.BetheGeneralSliceEndpoints.representatives_interior_ae
#print axioms QuantumNLS.BetheGeneralSliceEndpoints.physical_firstPlacement_endpoints_ae
#print axioms QuantumNLS.BetheGeneralSliceEndpoints.sourceInput
#print axioms QuantumNLS.BetheGeneralSliceEndpoints.sourceInput_tensor_eq
#print axioms QuantumNLS.BetheGeneralSliceEndpoints.source_firstPlacement_ae
#print axioms QuantumNLS.BetheGeneralSliceEndpoints.normalized_placement
#print axioms QuantumNLS.BetheGeneralSliceEndpoints.totalPlacement_one
#print axioms QuantumNLS.BetheGeneralSliceEndpoints.transferTerm_one

#check QuantumNLS.BetheGeneralSlice.physical_tensorMap_eq_sliceMap
#check QuantumNLS.BetheGeneralSliceEndpoints.physical_firstPlacement_endpoints_ae
#check QuantumNLS.BetheGeneralSliceEndpoints.sourceInput_tensor_eq
#check QuantumNLS.BetheGeneralSliceEndpoints.source_firstPlacement_ae
#check QuantumNLS.BetheGeneralSliceEndpoints.normalized_placement
#check QuantumNLS.BetheGeneralSliceEndpoints.transferTerm_one
#check QuantumNLS.BetheGeneralSliceEndpoints.source_outer_endpoint_cancel

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.BetheGeneralSliceEndpoints.physical_firstPlacement_endpoints_ae,
    ``QuantumNLS.BetheGeneralSliceEndpoints.sourceInput_tensor_eq,
    ``QuantumNLS.BetheGeneralSliceEndpoints.source_firstPlacement_ae,
    ``QuantumNLS.BetheGeneralSliceEndpoints.normalized_placement,
    ``QuantumNLS.BetheGeneralSliceEndpoints.transferTerm_one,
    ``QuantumNLS.BetheGeneralSliceEndpoints.source_outer_endpoint_cancel]
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  for n in #[``QuantumNLS.BetheGeneralSlice.firstPlacement_product,
      ``QuantumNLS.BetheGeneralSlice.append_split,
      ``QuantumNLS.BetheGeneralSlice.tensorMap_product,
      ``QuantumNLS.BetheGeneralSlice.sliceMap_product,
      ``QuantumNLS.BetheGeneralSlice.tensorMap_eq_sliceMap,
      ``QuantumNLS.PhysicalTensor.prodAlgebra_dense,
      ``QuantumNLS.TensorCarrier.splitIsometry,
      ``QuantumNLS.TensorCarrier.splitIsometry_ptprod_append,
      ``QuantumNLS.TensorPlacements.firstPlacement,
      ``QuantumNLS.PhysicalTensor.physUnitary,
      ``QuantumNLS.BetheIntegralOperator.Kernel.operator_apply_ae,
      ``QuantumNLS.BethePhysicalTransfer.physicalKernel,
      ``QuantumNLS.BetheTransferKernelAdjoint.rawPlus,
      ``QuantumNLS.BetheTransferKernelAdjoint.rawMinus,
      ``QuantumNLS.TensorCarrier.symProj_eq_factorial_average,
      ``QuantumNLS.BethePhysicalTransfer.transferTerm,
      ``Nat.descFactorial,
      ``QuantumNLS.BetheFiniteNAction.physicalWave,
      ``QuantumNLS.BetheExtension.symmetricExtension_outer_faces,
      ``QuantumNLS.BethePeriodic.sourceRoots_term_periodic,
      ``QuantumNLS.BetheSmooth.sourceRoots] do
    unless seen.contains n do
      throwError "General singleton route missed literal ingredient: {n}"
  for n in seen do
    if n.toString.startsWith "QuantumNLS.BetheOneParticleAction." ||
        n.toString.startsWith "QuantumNLS.BetheTwoParticleTransfer." ||
        n.toString.startsWith "QuantumNLS.BetheTwoParticleEigen." ||
        n.toString.startsWith "QuantumNLS.BetheTwoParticleEntire." then
      throwError "General singleton route used a special-particle action: {n}"
  for n in #[``QuantumNLS.BetheTensorSlice.firstPlacement_product,
      ``QuantumNLS.BetheTensorSlice.tensorMap_product,
      ``QuantumNLS.BetheTensorSlice.sliceMap_product,
      ``QuantumNLS.BetheTensorSlice.tensorMap_eq_sliceMap,
      ``QuantumNLS.BetheTensorSlice.physical_tensorMap_eq_sliceMap] do
    if seen.contains n then
      throwError "General singleton route used the N2 tensor-to-slice bridge: {n}"
  Lean.logInfo m!"General-N singleton placement route PASS: {seen.size} transitive constants; arbitrary spectators, density, literal integrals/endpoints, actual P_N average and c*N, source tensor identity and physical outer-endpoint cancellation. No N2 action/eigenrelation dependency; higher-degree and full transfer cancellation remain open."
