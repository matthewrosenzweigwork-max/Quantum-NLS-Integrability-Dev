import QuantumNLS.BethePhysicalTransfer
import QuantumNLS.BetheOnShell
import QuantumNLS.BetheContinuityInputs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Direct action of the literal physical ordered kernels in the one-particle
sector. Source: periodic_basis.tex:316–364 and Vlaar (2.5.7)–(2.5.9).
This is the physical integral seed, not an assumed off-shell action interface.
The many-particle action and coordinate/QISM identification remain open. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ComplexConjugate InnerProductSpace NNReal
set_option maxHeartbeats 2000000

namespace QuantumNLS.BetheOneParticleAction
open BetheTransferKernelAdjoint BetheTransferOperators BetheWeakGradient
open PhysicalTensor BetheSmooth BetheWavefunctions BetheExtension

/-- One-particle positive-i coordinate wave, before imposing periodicity. -/
def exponential (q : ℝ) (x : ℝ) : ℂ := Complex.exp (Complex.I * q * x)

/-- Exact upper ordered-kernel action, including its boundary contribution. -/
theorem upper_integral {L x q : ℝ} (hx : x ∈ Ioo 0 L) {z : ℂ}
    (hz : z ≠ (q : ℂ)) :
    (∫ y in Icc 0 L, rawPlus L z (fun _ : Fin 1 => x) (fun _ => y) * exponential q y) =
      (exponential q x - Complex.exp (Complex.I * z * x)) / (Complex.I * (q-z)) := by
  classical
  have ho (y : ℝ) : PlusOrder L (fun _ : Fin 1 => x) (fun _ => y) ↔ y ∈ Ioo 0 x := by
    simp only [PlusOrder, Fin.forall_fin_one, lt_self_iff_false, false_implies, and_true]
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hx.2⟩⟩
  have he (y : ℝ) : rawPlus L z (fun _ : Fin 1 => x) (fun _ => y) * exponential q y =
      (Ioo 0 x).indicator (fun y => Complex.exp (Complex.I * z * x) *
        Complex.exp ((Complex.I * ((q : ℂ)-z)) * y)) y := by
    simp only [rawPlus, ho, displacement, Fin.sum_univ_one, exponential, indicator_apply]
    split_ifs
    · rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    · simp
  simp_rw [he]
  rw [integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo]
  have hs : Ioo 0 x ∩ Icc 0 L = Ioo 0 x := inter_eq_left.mpr
    (fun y hy => ⟨hy.1.le, hy.2.le.trans hx.2.le⟩)
  rw [hs, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hx.1.le,
    intervalIntegral.integral_const_mul, integral_exp_mul_complex
      (mul_ne_zero Complex.I_ne_zero (sub_ne_zero.mpr hz.symm))]
  have hp : Complex.exp (Complex.I * z * x) *
      Complex.exp (Complex.I * ((q : ℂ)-z) * x) = exponential q x := by
    rw [← Complex.exp_add]
    congr 1
    ring
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [← mul_div_assoc, mul_sub, mul_one, hp]

/-- Exact lower ordered-kernel action, retaining the full exp(izL) phase. -/
theorem lower_integral {L x q : ℝ} (hx : x ∈ Ioo 0 L) {z : ℂ}
    (hz : z ≠ (q : ℂ)) :
    (∫ y in Icc 0 L, rawMinus L z (fun _ : Fin 1 => x) (fun _ => y) * exponential q y) =
      (Complex.exp (Complex.I * z * x) * exponential q L -
        Complex.exp (Complex.I * z * L) * exponential q x) / (Complex.I * (q-z)) := by
  classical
  have ho (y : ℝ) : MinusOrder L (fun _ : Fin 1 => x) (fun _ => y) ↔ y ∈ Ioo x L := by
    simp only [MinusOrder, PlusOrder, Fin.forall_fin_one, lt_self_iff_false,
      false_implies, and_true]
    exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨hx.1, h.1, h.2⟩⟩
  have he (y : ℝ) : rawMinus L z (fun _ : Fin 1 => x) (fun _ => y) * exponential q y =
      (Ioo x L).indicator (fun y => Complex.exp (Complex.I * z * L + Complex.I * z * x) *
        Complex.exp ((Complex.I * ((q : ℂ)-z)) * y)) y := by
    simp only [rawMinus, ho, Fin.sum_univ_one, exponential, indicator_apply]
    split_ifs
    · rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    · simp
  simp_rw [he]
  rw [integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo]
  have hs : Ioo x L ∩ Icc 0 L = Ioo x L := inter_eq_left.mpr
    (fun y hy => ⟨hx.1.le.trans hy.1.le, hy.2.le⟩)
  rw [hs, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hx.2.le,
    intervalIntegral.integral_const_mul, integral_exp_mul_complex
      (mul_ne_zero Complex.I_ne_zero (sub_ne_zero.mpr hz.symm))]
  rw [← mul_div_assoc, mul_sub]
  simp only [exponential, ← Complex.exp_add]
  congr 2 <;> (congr 1; ring)

/-- The actual off-shell boundary defect, computed from both integral branches.
It vanishes by the one-particle Bethe equation, not by an action assumption. -/
theorem raw_integral_offShell {L x q : ℝ} (hx : x ∈ Ioo 0 L) {z : ℂ}
    (hz : z ≠ (q : ℂ)) :
    (∫ y in Icc 0 L, rawPlus L z (fun _ : Fin 1 => x) (fun _ => y) * exponential q y) +
    (∫ y in Icc 0 L, rawMinus L z (fun _ : Fin 1 => x) (fun _ => y) * exponential q y) =
      (1-Complex.exp (Complex.I*z*L)) / (Complex.I*(q-z)) * exponential q x +
      (exponential q L-1) / (Complex.I*(q-z)) * Complex.exp (Complex.I*z*x) := by
  rw [upper_integral hx hz, lower_integral hx hz]
  ring

/-- On the actual constructed one-particle root the boundary defect is zero. -/
theorem sourceRoot_periodic {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (n : Fin 1 → ℤ) : exponential (sourceRoots L n c 0) L = 1 := by
  have hn : Antitone n := fun i j _ => by rw [Subsingleton.elim i j]
  have h := BetheOnShell.sourceRoots_deleted_balance hL hc hn (0 : Fin 1)
  simpa [BetheOnShell.deletedPlus, BetheOnShell.deletedMinus, exponential,
    mul_comm, mul_left_comm, mul_assoc] using h.symm

/-- Concrete coordinate transfer action of the physical kernels on the
actual one-particle Bethe wave, at spectral parameters away from its root. -/
theorem sourceRoot_coordinate_transfer {L c x : ℝ} (hL : 0 < L) (hc : 0 < c)
    (n : Fin 1 → ℤ) (hx : x ∈ Ioo 0 L) {z : ℂ}
    (hz : z ≠ (sourceRoots L n c 0 : ℂ)) :
    (1+Complex.exp (Complex.I*L*z)) * exponential (sourceRoots L n c 0) x +
      (c : ℂ) * ((∫ y in Icc 0 L,
        rawPlus L z (fun _ : Fin 1 => x) (fun _ => y) * exponential (sourceRoots L n c 0) y) +
      (∫ y in Icc 0 L,
        rawMinus L z (fun _ : Fin 1 => x) (fun _ => y) * exponential (sourceRoots L n c 0) y)) =
    TransferSeparation.sFun L c (sourceRoots L n c) z * exponential (sourceRoots L n c 0) x := by
  rw [raw_integral_offShell hx hz, sourceRoot_periodic hL hc n]
  simp only [sub_self, zero_div, zero_mul, add_zero, TransferSeparation.sFun,
    Fin.prod_univ_one]
  have hd := sub_ne_zero.mpr hz
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- Ordinary torus measure agrees with the scalar interval integral for
one coordinate. No probability-measure normalization is introduced. -/
theorem integral_representatives_one (L : ℝ) [Fact (0 < L)]
    (f : ℝ → ℂ) (hf : Measurable f) :
    (∫ y : Fin 1 → AddCircle L, f (representatives L y 0)) = ∫ t in Icc 0 L, f t := by
  have hm : Measurable (fun y : Fin 1 → AddCircle L => f (representatives L y 0)) :=
    hf.comp ((measurable_pi_apply (0 : Fin 1)).comp (measurable_representatives 1 L))
  rw [torus_integral_cube L _ hm.aestronglyMeasurable]
  calc
    _ = ∫ y : Fin 1 → ℝ, f (y 0) ∂cubeMeasure 1 L := by
      apply integral_congr_ae
      filter_upwards [representatives_coe_ae 1 L] with y hy
      rw [hy]
    _ = _ := by
      rw [cubeMeasure_eq_pi]
      exact (measurePreserving_funUnique (volume.restrict (Icc (0 : ℝ) L)) (Fin 1)).integral_comp' f

/-- The already constructed Bethe extension is literally the single
exponential in canonical physical coordinates. -/
theorem torusExtension_one (L : ℝ) [Fact (0 < L)] (c : ℝ) (n : Fin 1 → ℤ)
    (y : Fin 1 → AddCircle L) :
    torusExtension L c n y = exponential (sourceRoots L n c 0) (representatives L y 0) := by
  rw [torusExtension, symmetricExtension_eq L c n
    (fun i j _ => by rw [Subsingleton.elim i j])]
  rw [wavefunction, coordinateAnsatz_one]
  simp only [exponential, representatives, Complex.ofReal_mul, mul_assoc]

/-- The strict output chamber omits only a null torus seam. -/
theorem representatives_one_interior_ae (L : ℝ) [Fact (0 < L)] :
    ∀ᵐ y : Fin 1 → AddCircle L, representatives L y 0 ∈ Ioo 0 L := by
  have hne : ∀ᵐ x ∂cubeMeasure 1 L, x 0 ≠ 0 := by
    apply ae_restrict_of_ae
    rw [volume_pi]
    exact Measure.ae_eval_ne (fun _ : Fin 1 => (volume : Measure ℝ)) 0 0
  have hh : ∀ᵐ x ∂cubeMeasure 1 L,
      representatives L (fun j => (x j : AddCircle L)) 0 ∈ Ioo 0 L := by
    filter_upwards [representatives_coe_ae 1 L, hne, ae_restrict_mem measurableSet_Icc]
      with x hx hn hm
    have ht : representatives L (fun j => (x j : AddCircle L)) 0 ∈ Ico 0 L := by
      simpa [representatives] using (AddCircle.equivIco L 0 (x 0 : AddCircle L)).property
    rw [hx] at ht ⊢
    exact ⟨lt_of_le_of_ne ht.1 (Ne.symm hn), ht.2⟩
  have hp := cube_to_torus_measurePreserving 1 L
  rw [← hp.map_eq]
  exact (ae_map_iff hp.aemeasurable (measurableSet_Ioo.preimage
    ((measurable_pi_apply (0 : Fin 1)).comp (measurable_representatives 1 L)))).mpr hh

/-- Every one-coordinate tuple is constant at its unique coordinate. -/
theorem one_tuple {A : Type*} (y : Fin 1 → A) : y = fun _ => y 0 := by
  funext i
  rw [Subsingleton.elim i 0]

/-- Actual upper physical integral on an L² input represented by the
one-particle coordinate wave. -/
theorem plusKernel_integral_one (L : ℝ) [Fact (0 < L)] (q : ℝ) (z : ℂ)
    (g : L2TN L 1)
    (hg : g =ᵐ[torusPiMeasure L 1] fun y => exponential q (representatives L y 0))
    (x : Fin 1 → AddCircle L) :
    (∫ y, (plusKernel L 1 z).fn (x,y) * g y ∂torusPiMeasure L 1) =
    ∫ t in Icc 0 L, rawPlus L z (fun _ : Fin 1 => representatives L x 0) (fun _ => t) * exponential q t := by
  have hm : Measurable (fun t : ℝ => rawPlus L z
      (fun _ : Fin 1 => representatives L x 0) (fun _ => t) * exponential q t) := by
    apply Measurable.mul
    · exact (measurable_rawPlus 1 L z).comp
        (show Measurable (fun t : ℝ => ((fun _ : Fin 1 => representatives L x 0), (fun _ : Fin 1 => t))) by fun_prop)
    · unfold exponential; fun_prop
  calc
    _ = ∫ y : Fin 1 → AddCircle L, rawPlus L z
        (fun _ : Fin 1 => representatives L x 0) (fun _ => representatives L y 0) *
        exponential q (representatives L y 0) := by
      conv_rhs => rw [volume_pi]
      apply integral_congr_ae
      filter_upwards [hg] with y hy
      change rawPlus L z (representatives L x) (representatives L y) * g y = _
      rw [hy, one_tuple (representatives L x), one_tuple (representatives L y)]
    _ = _ := integral_representatives_one L _ hm

/-- Actual lower physical integral, with the original full interval phase. -/
theorem minusKernel_integral_one (L : ℝ) [Fact (0 < L)] (q : ℝ) (z : ℂ)
    (g : L2TN L 1)
    (hg : g =ᵐ[torusPiMeasure L 1] fun y => exponential q (representatives L y 0))
    (x : Fin 1 → AddCircle L) :
    (∫ y, (minusKernel L 1 z).fn (x,y) * g y ∂torusPiMeasure L 1) =
    ∫ t in Icc 0 L, rawMinus L z (fun _ : Fin 1 => representatives L x 0) (fun _ => t) * exponential q t := by
  have hm : Measurable (fun t : ℝ => rawMinus L z
      (fun _ : Fin 1 => representatives L x 0) (fun _ => t) * exponential q t) := by
    apply Measurable.mul
    · exact (measurable_rawMinus 1 L z).comp
        (show Measurable (fun t : ℝ => ((fun _ : Fin 1 => representatives L x 0), (fun _ : Fin 1 => t))) by fun_prop)
    · unfold exponential; fun_prop
  calc
    _ = ∫ y : Fin 1 → AddCircle L, rawMinus L z
        (fun _ : Fin 1 => representatives L x 0) (fun _ => representatives L y 0) *
        exponential q (representatives L y 0) := by
      conv_rhs => rw [volume_pi]
      apply integral_congr_ae
      filter_upwards [hg] with y hy
      change rawMinus L z (representatives L x) (representatives L y) * g y = _
      rw [hy, one_tuple (representatives L x), one_tuple (representatives L y)]
    _ = _ := integral_representatives_one L _ hm

/-- The actual frozen raw bounded operator has the on-shell one-particle
wave as eigenvector. Its action is derived from the integrals above. -/
theorem rawOperator_sourceWave (L : ℝ) [Fact (0 < L)] {c : ℝ} (hc : 0 < c)
    {n : Fin 1 → ℤ} (hn : Antitone n) {z : ℂ}
    (hz : z ≠ (sourceRoots L n c 0 : ℂ)) :
    rawOperator L 1 z (BetheH1.wave (L := L) hc hn) =
      ((1-Complex.exp (Complex.I*z*L)) / (Complex.I*((sourceRoots L n c 0 : ℂ)-z))) •
        BetheH1.wave (L := L) hc hn := by
  let g := BetheH1.wave (L := L) hc hn
  have hg : g =ᵐ[torusPiMeasure L 1] fun y =>
      exponential (sourceRoots L n c 0) (representatives L y 0) := by
    filter_upwards [BetheH1.coe_wave (L := L) hc hn] with y hy
    rw [hy, torusExtension_one]
  apply Lp.ext
  change (plusKernel L 1 z).operator g + (minusKernel L 1 z).operator g =ᵐ[_] _
  filter_upwards [Lp.coeFn_add ((plusKernel L 1 z).operator g) ((minusKernel L 1 z).operator g),
    (plusKernel L 1 z).operator_apply_ae g, (minusKernel L 1 z).operator_apply_ae g,
    Lp.coeFn_smul ((1-Complex.exp (Complex.I*z*L)) /
      (Complex.I*((sourceRoots L n c 0 : ℂ)-z))) g,
    hg, (show ∀ᵐ y ∂torusPiMeasure L 1, representatives L y 0 ∈ Ioo 0 L from by
      simpa only [volume_pi] using representatives_one_interior_ae L)] with x ha hp hm hs hw hx
  rw [ha]
  simp only [Pi.add_apply]
  rw [hp, hm, hs]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [plusKernel_integral_one L _ z g hg, minusKernel_integral_one L _ z g hg,
    raw_integral_offShell hx hz, sourceRoot_periodic (Fact.out : 0 < L) hc n,
    hw, sub_self, zero_div, zero_mul, add_zero]

section EmptySpectators
open TensorCarrier TensorPlacements BethePhysicalTransfer
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Splitting off zero spectators retains exactly the scalar unit tensor. -/
theorem split_zero_right (m : ℕ) (v : HilbertTensorPower ℂ H m) :
    splitIsometry m 0 v = htmul v (htpow 0 (0 : H)) := by
  induction v using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (splitIsometry m 0).continuous
      (by unfold htmul; fun_prop)
  | ih v =>
    induction v using AlgTensorPower.induction_on with
    | smul_ptprod a f =>
      have hf : Fin.append f (fun _ : Fin 0 => (0 : H)) = f := by
        funext i
        exact Fin.append_left f _ i
      have hs := splitIsometry_ptprod_append (𝕜 := ℂ) (E := H)
        (a := f) (b := fun _ : Fin 0 => (0 : H))
      rw [hf] at hs
      simpa only [UniformSpace.Completion.coe_smul, map_smul, htmul_smul_left,
        htpow] using congrArg (fun w => a • w) hs
    | add v w hv hw =>
      simp only [UniformSpace.Completion.coe_add, map_add, htmul_add_left, hv, hw]

/-- The literal split placement with no spectators is the zero extension. -/
theorem firstPlacement_no_spectators {m : ℕ}
    (A : SymSector ℂ H m →L[ℂ] SymSector ℂ H m) :
    firstPlacement (q := 0) A = extendSymKernel A := by
  ext v
  apply (splitIsometry m 0).injective
  change splitIsometry m 0 ((splitIsometry m 0).symm
    (htmap (extendSymKernel A) (ContinuousLinearMap.id ℂ _) (splitIsometry m 0 v))) = _
  rw [LinearIsometryEquiv.apply_symm_apply, split_zero_right, htmap_htmul,
    ContinuousLinearMap.id_apply, split_zero_right]

/-- At full particle degree the source normalized placement is the kernel
itself. This checks the N=1 coefficient without an extra factorial. -/
theorem totalPlacement_self [CompleteSpace H] (m : ℕ)
    (A : SymSector ℂ H m →L[ℂ] SymSector ℂ H m) :
    totalPlacement m m le_rfl A = A := by
  have he : placement (q := 0) A = A := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [placement, ContinuousLinearMap.comp_apply, firstPlacement_no_spectators]
    have hv : symProjToSector m v.val = v := by
      rw [symProjToSector_eq_adjoint, Submodule.adjoint_subtypeL]
      exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self v
    change (SymSector ℂ H m).subtypeL.adjoint
      ((A (symProjToSector m v.val)).val) = A v
    rw [hv, Submodule.adjoint_subtypeL]
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (A v)
  have hcast (q : ℕ) (hq : m+q=m) (hz : q=0) :
      KernelDefinition.castSymSectorOperator hq (placement (q := q) A) = A := by
    subst q
    exact he
  exact hcast (m-m) (Nat.add_sub_of_le (le_refl m)) (Nat.sub_self m)
end EmptySpectators

open BethePhysicalTransfer ContactOperator

/-- The continued physical wave used by the basis project is exactly the
L² input to the direct kernel calculation, for positive coupling. -/
theorem continuedWave_one_eq (L : ℝ) [Fact (0 < L)] {c : ℝ≥0} (hc : 0 < (c : ℝ))
    (n : BetheFreeFamily.Label 1) :
    ((BetheContinuityInputs.wave (L := L) c n : SymL2 L 1) : L2TN L 1) =
      BetheH1.wave (L := L) hc n.property := by
  rw [BetheContinuityInputs.wave_pos hc]
  exact BetheH1.waveH1_val hc n.property

/-- Actual compressed position-operator action on the existing physical wave. -/
theorem compressedOperator_sourceWave (L : ℝ) [Fact (0 < L)] {c : ℝ≥0}
    (hc : 0 < (c : ℝ)) (n : BetheFreeFamily.Label 1) {z : ℂ}
    (hz : z ≠ (sourceRoots L n.val c 0 : ℂ)) :
    compressedOperator L 1 z (BetheContinuityInputs.wave (L := L) c n) =
      ((1-Complex.exp (Complex.I*z*L)) / (Complex.I*((sourceRoots L n.val c 0 : ℂ)-z))) •
        BetheContinuityInputs.wave (L := L) c n := by
  change (SymL2 L 1).subtypeL.adjoint
    (rawOperator L 1 z ((BetheContinuityInputs.wave (L := L) c n : SymL2 L 1) : L2TN L 1)) = _
  rw [continuedWave_one_eq L hc n, rawOperator_sourceWave L hc n.property hz,
    ← continuedWave_one_eq L hc n, map_smul, Submodule.adjoint_subtypeL,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

/-- Actual physical symmetric-tensor kernel action, using the frozen position
unitary and the existing positive-coupling wave. -/
theorem physicalKernel_sourceWave (L : ℝ) [Fact (0 < L)] {c : ℝ≥0}
    (hc : 0 < (c : ℝ)) (n : BetheFreeFamily.Label 1) {z : ℂ}
    (hz : z ≠ (sourceRoots L n.val c 0 : ℂ)) :
    physicalKernel L 1 z ((symmetricPosition L 1).symm (BetheContinuityInputs.wave (L := L) c n)) =
      ((1-Complex.exp (Complex.I*z*L)) / (Complex.I*((sourceRoots L n.val c 0 : ℂ)-z))) •
        (symmetricPosition L 1).symm (BetheContinuityInputs.wave (L := L) c n) := by
  rw [physicalKernel_eq_positionCompression]
  change (symmetricPosition L 1).toLinearIsometry.toContinuousLinearMap.adjoint
    (compressedOperator L 1 z ((symmetricPosition L 1)
      ((symmetricPosition L 1).symm (BetheContinuityInputs.wave (L := L) c n)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply, compressedOperator_sourceWave L hc n hz,
    adjoint_isometryEquiv]
  exact map_smul _ _ _

/-- Exact one-particle specialization of the frozen finite transfer series. -/
theorem transfer_one (L : ℝ) [Fact (0 < L)] (c : ℝ) (z : ℂ) :
    transfer L 1 c z = (1+Complex.exp (Complex.I*L*z)) • ContinuousLinearMap.id ℂ _ +
      (c : ℂ) • physicalKernel L 1 z := by
  rw [transfer, Fin.sum_univ_two]
  simp [transferTerm, totalPlacement_self, Nat.descFactorial_succ]

/-- The literal physical transfer eigenrelation is proved in the one-particle
sector by direct integration. No off-shell action or QISM identity is assumed.
The general interacting N-particle eigenrelation is still open. -/
theorem transfer_sourceWave_one (L : ℝ) [Fact (0 < L)] {c : ℝ≥0}
    (hc : 0 < (c : ℝ)) (n : BetheFreeFamily.Label 1) {z : ℂ}
    (hz : z ≠ (sourceRoots L n.val c 0 : ℂ)) :
    transfer L 1 c z ((symmetricPosition L 1).symm (BetheContinuityInputs.wave (L := L) c n)) =
      TransferSeparation.sFun L c (sourceRoots L n.val c) z •
        (symmetricPosition L 1).symm (BetheContinuityInputs.wave (L := L) c n) := by
  rw [transfer_one, add_apply, smul_apply,
    ContinuousLinearMap.id_apply, smul_apply,
    physicalKernel_sourceWave L hc n hz, smul_smul, ← add_smul]
  congr 1
  simp only [TransferSeparation.sFun, Fin.prod_univ_one]
  have hd := sub_ne_zero.mpr hz
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The upper ordered integral at its resonant spectral parameter is a
literal interval length times the coordinate wave. -/
theorem upper_integral_at_root {L x q : ℝ} (hx : x ∈ Ioo 0 L) :
    (∫ y in Icc 0 L, rawPlus L q (fun _ : Fin 1 => x) (fun _ => y) * exponential q y) =
      (x : ℂ) * exponential q x := by
  classical
  have ho (y : ℝ) : PlusOrder L (fun _ : Fin 1 => x) (fun _ => y) ↔ y ∈ Ioo 0 x := by
    simp only [PlusOrder, Fin.forall_fin_one, lt_self_iff_false, false_implies, and_true]
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hx.2⟩⟩
  have he (y : ℝ) : rawPlus L q (fun _ : Fin 1 => x) (fun _ => y) * exponential q y =
      (Ioo 0 x).indicator (fun _ => exponential q x) y := by
    simp only [rawPlus, ho, displacement, Fin.sum_univ_one, exponential, indicator_apply]
    split_ifs
    · rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    · simp
  simp_rw [he]
  rw [integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo]
  have hs : Ioo 0 x ∩ Icc 0 L = Ioo 0 x := inter_eq_left.mpr
    (fun y hy => ⟨hy.1.le, hy.2.le.trans hx.2.le⟩)
  rw [hs, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hx.1.le,
    intervalIntegral.integral_const]
  simp only [sub_zero, Complex.real_smul]

/-- The lower resonant integral retains its periodic boundary factor. -/
theorem lower_integral_at_root {L x q : ℝ} (hx : x ∈ Ioo 0 L) :
    (∫ y in Icc 0 L, rawMinus L q (fun _ : Fin 1 => x) (fun _ => y) * exponential q y) =
      ((L-x : ℝ) : ℂ) * (exponential q L * exponential q x) := by
  classical
  have ho (y : ℝ) : MinusOrder L (fun _ : Fin 1 => x) (fun _ => y) ↔ y ∈ Ioo x L := by
    simp only [MinusOrder, PlusOrder, Fin.forall_fin_one, lt_self_iff_false,
      false_implies, and_true]
    exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨hx.1, h.1, h.2⟩⟩
  have he (y : ℝ) : rawMinus L q (fun _ : Fin 1 => x) (fun _ => y) * exponential q y =
      (Ioo x L).indicator (fun _ => exponential q L * exponential q x) y := by
    simp only [rawMinus, ho, Fin.sum_univ_one, exponential, indicator_apply]
    split_ifs
    · simp only [← Complex.exp_add]
      congr 1
      push_cast
      ring
    · simp
  simp_rw [he]
  rw [integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo]
  have hs : Ioo x L ∩ Icc 0 L = Ioo x L := inter_eq_left.mpr
    (fun y hy => ⟨hx.1.le.trans hy.1.le, hy.2.le⟩)
  rw [hs, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hx.2.le,
    intervalIntegral.integral_const]
  rfl

/-- Actual raw operator action at the apparent pole. The value is L, rather
than the value zero assigned to the quotient by totalized field division. -/
theorem rawOperator_sourceWave_at_root (L : ℝ) [Fact (0 < L)] {c : ℝ} (hc : 0 < c)
    {n : Fin 1 → ℤ} (hn : Antitone n) :
    rawOperator L 1 (sourceRoots L n c 0) (BetheH1.wave (L := L) hc hn) =
      (L : ℂ) • BetheH1.wave (L := L) hc hn := by
  let g := BetheH1.wave (L := L) hc hn
  let q := sourceRoots L n c 0
  have hg : g =ᵐ[torusPiMeasure L 1] fun y => exponential q (representatives L y 0) := by
    filter_upwards [BetheH1.coe_wave (L := L) hc hn] with y hy
    rw [hy, torusExtension_one]
  apply Lp.ext
  change (plusKernel L 1 q).operator g + (minusKernel L 1 q).operator g =ᵐ[_] _
  filter_upwards [Lp.coeFn_add ((plusKernel L 1 q).operator g) ((minusKernel L 1 q).operator g),
    (plusKernel L 1 q).operator_apply_ae g, (minusKernel L 1 q).operator_apply_ae g,
    Lp.coeFn_smul (L : ℂ) g, hg,
    (show ∀ᵐ y ∂torusPiMeasure L 1, representatives L y 0 ∈ Ioo 0 L from by
      simpa only [volume_pi] using representatives_one_interior_ae L)] with x ha hp hm hs hw hx
  rw [ha]
  simp only [Pi.add_apply]
  rw [hp, hm, hs]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [plusKernel_integral_one L q q g hg, minusKernel_integral_one L q q g hg,
    upper_integral_at_root hx, lower_integral_at_root hx,
    sourceRoot_periodic (Fact.out : 0 < L) hc n, one_mul, hw, Complex.ofReal_sub]
  ring

/-- The actual compressed physical kernel at the apparent pole. -/
theorem compressedOperator_sourceWave_at_root (L : ℝ) [Fact (0 < L)] {c : ℝ≥0}
    (hc : 0 < (c : ℝ)) (n : BetheFreeFamily.Label 1) :
    compressedOperator L 1 (sourceRoots L n.val c 0) (BetheContinuityInputs.wave (L := L) c n) =
      (L : ℂ) • BetheContinuityInputs.wave (L := L) c n := by
  change (SymL2 L 1).subtypeL.adjoint
    (rawOperator L 1 (sourceRoots L n.val c 0)
      ((BetheContinuityInputs.wave (L := L) c n : SymL2 L 1) : L2TN L 1)) = _
  rw [continuedWave_one_eq L hc n, rawOperator_sourceWave_at_root L hc n.property,
    ← continuedWave_one_eq L hc n, map_smul, Submodule.adjoint_subtypeL,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

/-- Physical tensor transport of the resonant integral action. -/
theorem physicalKernel_sourceWave_at_root (L : ℝ) [Fact (0 < L)] {c : ℝ≥0}
    (hc : 0 < (c : ℝ)) (n : BetheFreeFamily.Label 1) :
    physicalKernel L 1 (sourceRoots L n.val c 0)
      ((symmetricPosition L 1).symm (BetheContinuityInputs.wave (L := L) c n)) =
      (L : ℂ) • (symmetricPosition L 1).symm (BetheContinuityInputs.wave (L := L) c n) := by
  rw [physicalKernel_eq_positionCompression]
  change (symmetricPosition L 1).toLinearIsometry.toContinuousLinearMap.adjoint
    (compressedOperator L 1 (sourceRoots L n.val c 0) ((symmetricPosition L 1)
      ((symmetricPosition L 1).symm (BetheContinuityInputs.wave (L := L) c n)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply, compressedOperator_sourceWave_at_root L hc n,
    adjoint_isometryEquiv]
  exact map_smul _ _ _

/-- The actual physical transfer at the removable pole has eigenvalue 2+cL.
Using the totalized rational sFun at that point would give the wrong value. -/
theorem transfer_sourceWave_one_at_root (L : ℝ) [Fact (0 < L)] {c : ℝ≥0}
    (hc : 0 < (c : ℝ)) (n : BetheFreeFamily.Label 1) :
    transfer L 1 c (sourceRoots L n.val c 0)
      ((symmetricPosition L 1).symm (BetheContinuityInputs.wave (L := L) c n)) =
      (2 + (c : ℂ) * L) •
        (symmetricPosition L 1).symm (BetheContinuityInputs.wave (L := L) c n) := by
  rw [transfer_one, add_apply, smul_apply, ContinuousLinearMap.id_apply, smul_apply,
    physicalKernel_sourceWave_at_root L hc n, smul_smul, ← add_smul]
  have hp := sourceRoot_periodic (Fact.out : 0 < L) hc n.val
  simp only [exponential] at hp
  have he : Complex.exp (Complex.I*L*(sourceRoots L n.val c 0 : ℂ)) = 1 := by
    convert hp using 1
    congr 1
    ring
  rw [he]
  congr 2
  ring

/-- Explicit entire one-particle transfer scalar, with its removable value
supplied by the derivative of exp(iLz), rather than totalized division. -/
def entireScalar (L c q : ℝ) (z : ℂ) : ℂ :=
  1 + Complex.exp (Complex.I*L*z) + (c : ℂ) *
    (dslope (fun w : ℂ => Complex.exp (Complex.I*L*w)) (q : ℂ) z / Complex.I)

theorem entireScalar_differentiable (L c q : ℝ) : Differentiable ℂ (entireScalar L c q) := by
  have he : Differentiable ℂ (fun w : ℂ => Complex.exp (Complex.I*L*w)) := by fun_prop
  have hd : Differentiable ℂ (dslope (fun w : ℂ => Complex.exp (Complex.I*L*w)) (q : ℂ)) := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope Filter.univ_mem).mpr he.differentiableOn
  exact ((differentiable_const (1 : ℂ)).add he).add
    ((differentiable_const (c : ℂ)).mul (hd.div_const _))

/-- Off the root this entire scalar is exactly the frozen report sFun. -/
theorem entireScalar_eq_sFun {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (n : Fin 1 → ℤ) {z : ℂ} (hz : z ≠ (sourceRoots L n c 0 : ℂ)) :
    entireScalar L c (sourceRoots L n c 0) z = TransferSeparation.sFun L c (sourceRoots L n c) z := by
  unfold entireScalar
  rw [dslope_of_ne _ hz, slope_def_field]
  have hp := sourceRoot_periodic hL hc n
  have he : Complex.exp (Complex.I*L*(sourceRoots L n c 0 : ℂ)) = 1 := by
    convert hp using 1
    unfold exponential
    congr 1
    ring
  rw [he]
  simp only [TransferSeparation.sFun, Fin.prod_univ_one]
  have hd := sub_ne_zero.mpr hz
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The removable eigenvalue is exactly 2+cL. -/
theorem entireScalar_at_root {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (n : Fin 1 → ℤ) :
    entireScalar L c (sourceRoots L n c 0) (sourceRoots L n c 0) = 2+(c : ℂ)*L := by
  let q := sourceRoots L n c 0
  have hp := sourceRoot_periodic hL hc n
  have he : Complex.exp (Complex.I*L*(q : ℂ)) = 1 := by
    convert hp using 1
    unfold exponential
    congr 1
    ring
  have hd : HasDerivAt (fun w : ℂ => Complex.exp (Complex.I*L*w))
      (Complex.exp (Complex.I*L*q) * (Complex.I*L)) q := by
    simpa only [mul_one, id_eq] using! ((hasDerivAt_id (q : ℂ)).const_mul (Complex.I*L)).cexp
  change 1+Complex.exp (Complex.I*L*q)+(c : ℂ)*
    (dslope (fun w : ℂ => Complex.exp (Complex.I*L*w)) (q : ℂ) q / Complex.I) = _
  rw [dslope_same, hd.deriv, he, one_mul]
  field_simp
  ring

/-- Physical one-particle eigenrelation for all complex spectral parameters,
including the removable pole. The entire scalar agrees with sFun off the root. -/
theorem transfer_sourceWave_one_entire (L : ℝ) [Fact (0 < L)] {c : ℝ≥0}
    (hc : 0 < (c : ℝ)) (n : BetheFreeFamily.Label 1) (z : ℂ) :
    transfer L 1 c z ((symmetricPosition L 1).symm (BetheContinuityInputs.wave (L := L) c n)) =
      entireScalar L c (sourceRoots L n.val c 0) z •
        (symmetricPosition L 1).symm (BetheContinuityInputs.wave (L := L) c n) := by
  by_cases hz : z = (sourceRoots L n.val c 0 : ℂ)
  · subst z
    rw [entireScalar_at_root (Fact.out : 0 < L) hc n.val]
    exact transfer_sourceWave_one_at_root L hc n
  · rw [entireScalar_eq_sFun (Fact.out : 0 < L) hc n.val hz]
    exact transfer_sourceWave_one L hc n hz

/-- This physical scalar is the same unique analytic continuation established
by BOS1, now identified by the direct one-particle operator calculation. -/
theorem entireScalar_unique_extension (L : ℝ) [Fact (0 < L)] {c : ℝ≥0}
    (hc : 0 < (c : ℝ)) (n : BetheFreeFamily.Label 1) :
    (AnalyticOnNhd ℂ (entireScalar L c (sourceRoots L n.val c 0)) univ ∧
      ∀ z : ℂ, (∀ k, z ≠ (sourceRoots L n.val c k : ℂ)) →
        entireScalar L c (sourceRoots L n.val c 0) z = TransferSeparation.sFun L c (sourceRoots L n.val c) z) ∧
    ∀ f : ℂ → ℂ, (AnalyticOnNhd ℂ f univ ∧
      ∀ z : ℂ, (∀ k, z ≠ (sourceRoots L n.val c k : ℂ)) → f z = TransferSeparation.sFun L c (sourceRoots L n.val c) z) →
      f = entireScalar L c (sourceRoots L n.val c 0) := by
  have hd := entireScalar_differentiable L (c : ℝ) (sourceRoots L n.val c 0)
  have he : ∀ z : ℂ, (∀ k, z ≠ (sourceRoots L n.val c k : ℂ)) →
      entireScalar L c (sourceRoots L n.val c 0) z = TransferSeparation.sFun L c (sourceRoots L n.val c) z :=
    fun _ hz => entireScalar_eq_sFun (Fact.out : 0 < L) hc n.val (hz 0)
  refine ⟨⟨fun z _ => hd.analyticAt z, he⟩, ?_⟩
  rintro f ⟨hf, hfe⟩
  apply BetheOnShell.sourceRoots_entire_extension_unique
    (fun z => (hf z (mem_univ z)).differentiableAt) hd
  intro z hz
  rw [hfe z hz, he z hz]

/-- The physical vector in the eigenrelation is nonzero, with the existing
positive-coupling and free-endpoint nonvanishing theorem as its input. -/
theorem physicalWave_one_ne_zero (L : ℝ) [Fact (0 < L)] (c : ℝ≥0)
    (n : BetheFreeFamily.Label 1) :
    (symmetricPosition L 1).symm (BetheContinuityInputs.wave (L := L) c n) ≠ 0 := by
  intro h
  apply BetheContinuityInputs.wave_ne_zero (L := L) c n
  have hh := congrArg (symmetricPosition L 1) h
  simpa only [LinearIsometryEquiv.apply_symm_apply, map_zero] using hh

end QuantumNLS.BetheOneParticleAction

#print axioms QuantumNLS.BetheOneParticleAction.exponential
#print axioms QuantumNLS.BetheOneParticleAction.upper_integral
#print axioms QuantumNLS.BetheOneParticleAction.lower_integral
#print axioms QuantumNLS.BetheOneParticleAction.raw_integral_offShell
#print axioms QuantumNLS.BetheOneParticleAction.sourceRoot_periodic
#print axioms QuantumNLS.BetheOneParticleAction.sourceRoot_coordinate_transfer
#print axioms QuantumNLS.BetheOneParticleAction.integral_representatives_one
#print axioms QuantumNLS.BetheOneParticleAction.torusExtension_one
#print axioms QuantumNLS.BetheOneParticleAction.representatives_one_interior_ae
#print axioms QuantumNLS.BetheOneParticleAction.one_tuple
#print axioms QuantumNLS.BetheOneParticleAction.plusKernel_integral_one
#print axioms QuantumNLS.BetheOneParticleAction.minusKernel_integral_one
#print axioms QuantumNLS.BetheOneParticleAction.rawOperator_sourceWave
#print axioms QuantumNLS.BetheOneParticleAction.split_zero_right
#print axioms QuantumNLS.BetheOneParticleAction.firstPlacement_no_spectators
#print axioms QuantumNLS.BetheOneParticleAction.totalPlacement_self
#print axioms QuantumNLS.BetheOneParticleAction.continuedWave_one_eq
#print axioms QuantumNLS.BetheOneParticleAction.compressedOperator_sourceWave
#print axioms QuantumNLS.BetheOneParticleAction.physicalKernel_sourceWave
#print axioms QuantumNLS.BetheOneParticleAction.transfer_one
#print axioms QuantumNLS.BetheOneParticleAction.transfer_sourceWave_one
#print axioms QuantumNLS.BetheOneParticleAction.upper_integral_at_root
#print axioms QuantumNLS.BetheOneParticleAction.lower_integral_at_root
#print axioms QuantumNLS.BetheOneParticleAction.rawOperator_sourceWave_at_root
#print axioms QuantumNLS.BetheOneParticleAction.compressedOperator_sourceWave_at_root
#print axioms QuantumNLS.BetheOneParticleAction.physicalKernel_sourceWave_at_root
#print axioms QuantumNLS.BetheOneParticleAction.transfer_sourceWave_one_at_root
#print axioms QuantumNLS.BetheOneParticleAction.entireScalar
#print axioms QuantumNLS.BetheOneParticleAction.entireScalar_differentiable
#print axioms QuantumNLS.BetheOneParticleAction.entireScalar_eq_sFun
#print axioms QuantumNLS.BetheOneParticleAction.entireScalar_at_root
#print axioms QuantumNLS.BetheOneParticleAction.transfer_sourceWave_one_entire
#print axioms QuantumNLS.BetheOneParticleAction.entireScalar_unique_extension
#print axioms QuantumNLS.BetheOneParticleAction.physicalWave_one_ne_zero

/- The final equality must reach the actual physical operator construction,
its literal pointwise integral action, the existing physical Bethe vector,
and the proved actual-root balance. No abstract action premise is used. -/
set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.BetheOneParticleAction.transfer_sourceWave_one_entire,
    ``QuantumNLS.BetheOneParticleAction.entireScalar_unique_extension,
    ``QuantumNLS.BetheOneParticleAction.physicalWave_one_ne_zero]
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
  for n in #[``QuantumNLS.BethePhysicalTransfer.transfer,
      ``QuantumNLS.BethePhysicalTransfer.transferTerm,
      ``QuantumNLS.BethePhysicalTransfer.totalPlacement,
      ``QuantumNLS.BethePhysicalTransfer.physicalKernel,
      ``QuantumNLS.BethePhysicalTransfer.symmetricPosition,
      ``QuantumNLS.BetheTransferOperators.rawOperator,
      ``QuantumNLS.BetheTransferOperators.compressedOperator,
      ``QuantumNLS.BetheTransferOperators.plusKernel,
      ``QuantumNLS.BetheTransferOperators.minusKernel,
      ``QuantumNLS.BetheTransferKernelAdjoint.rawPlus,
      ``QuantumNLS.BetheTransferKernelAdjoint.rawMinus,
      ``QuantumNLS.BetheTransferKernelAdjoint.PlusOrder,
      ``QuantumNLS.BetheIntegralOperator.Kernel.operator_apply_ae,
      ``QuantumNLS.BetheWeakGradient.cube_to_torus_measurePreserving,
      ``QuantumNLS.BetheOneParticleAction.upper_integral,
      ``QuantumNLS.BetheOneParticleAction.lower_integral,
      ``QuantumNLS.BetheOneParticleAction.upper_integral_at_root,
      ``QuantumNLS.BetheOneParticleAction.lower_integral_at_root,
      ``QuantumNLS.BetheOneParticleAction.totalPlacement_self,
      ``QuantumNLS.BetheOneParticleAction.rawOperator_sourceWave,
      ``QuantumNLS.BetheOneParticleAction.rawOperator_sourceWave_at_root,
      ``QuantumNLS.BetheOneParticleAction.entireScalar_at_root,
      ``QuantumNLS.BetheOnShell.sourceRoots_deleted_balance,
      ``QuantumNLS.BetheOnShell.sourceRoots_entire_extension_unique,
      ``QuantumNLS.BethePeriodic.sourceRoots_exponential_printed,
      ``QuantumNLS.BetheContinuityInputs.wave,
      ``QuantumNLS.BetheContinuityInputs.wave_ne_zero,
      ``QuantumNLS.BetheH1.coe_wave,
      ``QuantumNLS.BetheWavefunctions.coordinateAnsatz_one,
      ``QuantumNLS.PhysicalTensor.physUnitary,
      ``Nat.descFactorial] do
    unless seen.contains n do
      throwError "One-particle physical action route missed source ingredient: {n}"
  Lean.logInfo m!"One-particle physical action route PASS: {seen.size} transitive constants; actual upper/lower integrals, regular and resonant action, ordinary physical measure, existing nonzero wave, tensor placement and literal transfer, actual-root balance and unique entire scalar reached. Interacting N>=2 physical action and basis remain open."
