import QuantumNLS.FiniteCellSupport
import QuantumNLS.DynSeedR47b
import QuantumNLS.ExactShiftResidual
import QuantumNLS.FiniteCellFinal
import QuantumNLS.FiniteCellGauge

/-! Scalar estimates for the full corrected occupation arrays and the finite-cell gauge. -/

/-! Polar completion of an exact full-array seed edge. The estimate uses the
forward and adjoint residuals together and has no bound on the seed norm. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
open scoped ComplexConjugate

namespace QuantumNLS.RetargetPolarR48b
open Occupation OccupationHilbert FullOccupationAffinity FiniteCellSupport

variable {N : ℕ}

theorem polar_edge_identity (c x y : ℂ) (ζ : Phase) (s : ℝ) :
    (c * x - (s : ℂ) * ζ.1 * y) -
      (ζ.1 * (completePhase c).1) * (conj c * y - (s : ℂ) * conj ζ.1 * x) =
    ((‖c‖ + s : ℝ) : ℂ) * ((completePhase c).1 * x - ζ.1 * y) := by
  let α := completePhase c
  have hc : c = α.1 * (‖c‖ : ℂ) := (completePhase_polar c).symm
  have hca : conj c = conj α.1 * (‖c‖ : ℂ) := by
    calc
      conj c = conj (α.1 * (‖c‖ : ℂ)) := congrArg _ hc
      _ = _ := by rw [map_mul, Complex.conj_ofReal]
  change _ = ((‖c‖ + s : ℝ) : ℂ) * (α.1 * x - ζ.1 * y)
  conv_lhs => rw [show c * x = (α.1 * (‖c‖ : ℂ)) * x from congrArg (· * x) hc, hca]
  have ha : α.1 * conj α.1 = 1 := (mul_comm _ _).trans (phase_conj_mul α)
  have hz : ζ.1 * conj ζ.1 = 1 := (mul_comm _ _).trans (phase_conj_mul ζ)
  push_cast
  change _ = ((‖c‖ : ℂ) + (s : ℂ)) * (α.1 * x - ζ.1 * y)
  calc
    _ = (‖c‖ : ℂ) * α.1 * x - (s : ℂ) * ζ.1 * y -
        ζ.1 * (α.1 * conj α.1) * (‖c‖ : ℂ) * y +
        (s : ℂ) * (ζ.1 * conj ζ.1) * α.1 * x := by
      change (α.1 * (‖c‖ : ℂ) * x - (s : ℂ) * ζ.1 * y) -
        (ζ.1 * α.1) * (conj α.1 * (‖c‖ : ℂ) * y - (s : ℂ) * conj ζ.1 * x) = _
      ring
    _ = _ := by rw [ha, hz]; ring

/-- The two residuals of a graded seed control the completed phase uniformly
for every positive target modulus, even where some seed coefficients vanish. -/
theorem completed_forward_bound (a b : ℤ) (hab : a ≠ b)
    (C : H N →L[ℂ] H N) (c : Donor N a → ℂ)
    (hf : ∀ v m, C v (destination N a b m) = c m * v m.1)
    (hadj : ∀ v (m : Donor N a), C.adjoint v m.1 = conj (c m) * v (destination N a b m))
    (hoff : ∀ v (m : Arr N), ¬ DonorOK b m.1 → C v m = 0)
    (g : H N) (ζ : Phase) (s : ℝ) (hs : 0 ≤ s) :
    s * ‖completedSeed a b c g - ζ.1 • g‖ ≤
      ‖C g - ((s : ℂ) * ζ.1) • g‖ +
        ‖C.adjoint g - ((s : ℂ) * conj ζ.1) • g‖ := by
  let W := completedSeed a b c
  let f : H N := C g - ((s : ℂ) * ζ.1) • g
  let e : H N := C.adjoint g - ((s : ℂ) * conj ζ.1) • g
  have hpoint : ‖(s : ℂ) • (W g - ζ.1 • g)‖ ≤ ‖f - ζ.1 • W e‖ := by
    apply lp.norm_mono (p := 2) (by norm_num)
    intro m
    by_cases h : DonorOK b m.1
    · obtain ⟨d, rfl⟩ := (destination_range a b hab m).mpr h
      simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.coeFn_sub, Pi.sub_apply]
      change ‖(s : ℂ) * (transfer a b (fun d => completePhase (c d)) g (destination N a b d) -
        ζ.1 * g (destination N a b d))‖ ≤
        ‖f (destination N a b d) - ζ.1 * transfer a b
          (fun d => completePhase (c d)) e (destination N a b d)‖
      rw [transfer_at_destination, transfer_at_destination]
      have hfd : f (destination N a b d) = c d * g d.1 - (s : ℂ) * ζ.1 * g (destination N a b d) := by
        simp only [f, lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hf]
      have hed : e d.1 = conj (c d) * g (destination N a b d) - (s : ℂ) * conj ζ.1 * g d.1 := by
        simp only [e, lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hadj]
      rw [hfd, hed, ← mul_assoc, polar_edge_identity, norm_mul, norm_mul, Complex.norm_real,
        Complex.norm_real, Real.norm_of_nonneg hs, Real.norm_of_nonneg (by positivity : 0 ≤ ‖c d‖ + s)]
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (norm_nonneg _)) (norm_nonneg _)
    · have hwg : W g m = 0 := transfer_off_receiver a b hab _ g m h
      have hwe : W e m = 0 := transfer_off_receiver a b hab _ e m h
      simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.coeFn_sub, Pi.sub_apply, hwg, hwe,
        f, hoff g m h, mul_zero, sub_zero, zero_sub, mul_neg, mul_assoc]
      exact le_rfl
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hs] at hpoint
  have hwe := W.le_opNorm e
  have hwn : ‖W‖ ≤ 1 := transfer_norm_le _ _ _
  calc
    _ ≤ ‖f - ζ.1 • W e‖ := hpoint
    _ ≤ ‖f‖ + ‖ζ.1 • W e‖ := norm_sub_le _ _
    _ = ‖f‖ + ‖W e‖ := by rw [norm_smul, ζ.2, one_mul]
    _ ≤ ‖f‖ + ‖e‖ := add_le_add le_rfl
      (hwe.trans (mul_le_of_le_one_left (norm_nonneg _) hwn))

end QuantumNLS.RetargetPolarR48b

#print axioms QuantumNLS.RetargetPolarR48b.completed_forward_bound
end

/-! Transport of the graded physical seed to the full corrected occupation
arrays. This uses the actual normalized Bethe coefficient isometry. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false
noncomputable section
open scoped ComplexConjugate InnerProductSpace

namespace QuantumNLS.RetargetEdgeR48b
open PhysicalTensor BetheCoefficientTransform BetheLabels
open Occupation OccupationHilbert FullOccupationAffinity FiniteCellSupport

variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-- Basis columns agree across the decidable equality instances used in
the frozen coefficient and extension lemmas. -/
theorem single_classical {I : Type*} [d : DecidableEq I] (i : I) (z : ℂ) :
    (lp.single 2 i z : L2 I) = @lp.single I (fun _ : I => ℂ) _ (Classical.decEq I) 2 i z := by
  have h : d = Classical.decEq I := Subsingleton.elim _ _
  cases h
  rfl

/-- Unrephased coefficients, including every array. -/
abbrev J (B : BetheBasis L N) := occupationCoefficient B

theorem J_basis (B : BetheBasis L N) (m : MArr N) :
    J B (B m) = lp.single 2 (marrArr N m) 1 := by
  change (reindexBasis (marrArr N) B).repr _ = _
  rw [← (show reindexBasis (marrArr N) B (marrArr N m) = B m by
    rw [reindexBasis_apply, Equiv.symm_apply_apply]), HilbertBasis.repr_self]

/-- Transfer an operator to the unweighted coordinate basis. -/
def inCoefficients (B : BetheBasis L N) (C : HN L N →L[ℂ] HN L N) :
    H N →L[ℂ] H N :=
  (J B).toLinearIsometry.toContinuousLinearMap ∘L C ∘L
    (J B).symm.toLinearIsometry.toContinuousLinearMap

theorem inCoefficients_apply (B : BetheBasis L N) (C : HN L N →L[ℂ] HN L N)
    (g : H N) : inCoefficients B C g = J B (C ((J B).symm g)) := rfl

theorem inCoefficients_adjoint (B : BetheBasis L N) (C : HN L N →L[ℂ] HN L N) :
    (inCoefficients B C).adjoint = inCoefficients B C.adjoint := by
  simp only [inCoefficients, ContinuousLinearMap.adjoint_comp,
    BethePhysicalTransfer.adjoint_isometryEquiv, LinearIsometryEquiv.symm_symm,
    ContinuousLinearMap.comp_assoc]

theorem residual_inCoefficients (B : BetheBasis L N) (C : HN L N →L[ℂ] HN L N)
    (ψ : HN L N) (z : ℂ) :
    ‖inCoefficients B C (J B ψ) - z • J B ψ‖ = ‖C ψ - z • ψ‖ := by
  rw [inCoefficients_apply, LinearIsometryEquiv.symm_apply_apply, ← map_smul, ← map_sub,
    LinearIsometryEquiv.norm_map]

/-- Weighted transfer with arbitrary bounded coefficients. The scalar polar
completion uses these coefficients even when their bound exceeds one. -/
def raw (a b : ℤ) (c : Donor N a → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hc : ∀ m, ‖c m‖ ≤ M) : H N →L[ℂ] H N :=
  (injectL2 (destination N a b) (destination_injective N a b)).toContinuousLinearMap ∘L
    diagonal c M hM hc ∘L restrictL2 (Subtype.val : Donor N a → Arr N) Subtype.val_injective

theorem raw_basis (a b : ℤ) (c : Donor N a → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hc : ∀ m, ‖c m‖ ≤ M) (m : Arr N) :
    raw a b c M hM hc (lp.single 2 m 1) =
      if hm : DonorOK a m.1 then c ⟨m, hm⟩ • lp.single 2 (shiftArr a b m hm) 1 else 0 := by
  rw [raw, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, restrict_donor_single]
  split_ifs with hm
  · have he : diagonal c M hM hc (lp.single 2 (⟨m, hm⟩ : Donor N a) 1) =
        c ⟨m, hm⟩ • lp.single 2 (⟨m, hm⟩ : Donor N a) 1 := by
      apply lp.ext
      funext d
      by_cases h : d = ⟨m, hm⟩ <;> simp [lp.single_apply, h]
    simp only [he, map_smul, LinearIsometry.coe_toContinuousLinearMap]
    simpa only [single_classical, destination] using congrArg (fun v : H N => c ⟨m, hm⟩ • v)
      (injectL2_single (destination N a b) (destination_injective N a b) ⟨m, hm⟩ 1)
  · simp

theorem raw_at_destination (a b : ℤ) (c : Donor N a → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hc : ∀ m, ‖c m‖ ≤ M) (v : H N) (m : Donor N a) :
    raw a b c M hM hc v (destination N a b m) = c m * v m.1 := by
  change injectL2 (destination N a b) (destination_injective N a b)
    (diagonal c M hM hc (restrictL2 (Subtype.val : Donor N a → Arr N) Subtype.val_injective v))
    (destination N a b m) = _
  rw [inject_at_image, diagonal_apply, restrictL2_apply]

theorem raw_off_receiver (a b : ℤ) (hab : a ≠ b)
    (c : Donor N a → ℂ) (M : ℝ) (hM : 0 ≤ M) (hc : ∀ m, ‖c m‖ ≤ M)
    (v : H N) (m : Arr N) (hd : ¬ DonorOK b m.1) :
    raw a b c M hM hc v m = 0 :=
  inject_off_image (destination N a b) (destination_injective N a b) _ m
    (fun i hi => hd ((destination_range a b hab m).mp ⟨i, hi⟩))

theorem raw_adjoint_apply (a b : ℤ) (c : Donor N a → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hc : ∀ m, ‖c m‖ ≤ M) (v : H N) (m : Arr N) :
    (raw a b c M hM hc).adjoint v m =
      if hd : DonorOK a m.1 then conj (c ⟨m, hd⟩) * v (shiftArr a b m hd) else 0 := by
  have h := (raw a b c M hM hc).adjoint_inner_right (lp.single 2 m 1) v
  rw [raw_basis] at h
  split_ifs with hd
  · simp only [dite_eq_left hd] at h
    simpa only [lp.inner_single_left, RCLike.inner_apply, map_one, mul_one,
      inner_smul_left] using h
  · simp only [dite_eq_right hd] at h
    simpa only [lp.inner_single_left, RCLike.inner_apply, map_one, mul_one, inner_zero_left] using h

theorem graded_is_raw (B : BetheBasis L N) (C : HN L N →L[ℂ] HN L N)
    (a b : ℤ) (hC : DynSeedGradingR47b.Graded B a b C) :
    ∃ (c : Donor N a → ℂ) (hc : ∀ d, ‖c d‖ ≤ ‖inCoefficients B C‖),
      inCoefficients B C = raw a b c ‖inCoefficients B C‖ (norm_nonneg _) hc := by
  obtain ⟨f, hf⟩ := hC
  let C₀ := inCoefficients B C
  let c : Donor N a → ℂ := fun d => f ((marrArr N).symm d.1)
  have hformula (m : Arr N) : C₀ (lp.single 2 m 1) =
      if hd : DonorOK a m.1 then c ⟨m, hd⟩ • lp.single 2 (shiftArr a b m hd) 1 else 0 := by
    let m' := (marrArr N).symm m
    have hm' : marrArr N m' = m := (marrArr N).apply_symm_apply m
    rw [← hm']
    rw [← J_basis B m', inCoefficients_apply, LinearIsometryEquiv.symm_apply_apply, hf m']
    by_cases hd : DonorOK a m'.val
    · have hd' : DonorOK a (marrArr N m').1 := hd
      rw [dite_eq_left hd, dite_eq_left hd', map_smul, J_basis,
        DynSeedGradingR47b.transfer, Equiv.apply_symm_apply]
      simp only [c, Equiv.symm_apply_apply]
    · have hd' : ¬ DonorOK a (marrArr N m').1 := hd
      rw [dite_eq_right hd, dite_eq_right hd', map_zero]
  have hc (d : Donor N a) : ‖c d‖ ≤ ‖C₀‖ := by
    have hob := C₀.le_opNorm (lp.single 2 d.1 (1 : ℂ))
    rw [hformula, dite_eq_left d.2, norm_smul, lp.norm_single (by norm_num),
      lp.norm_single (by norm_num), norm_one, mul_one, mul_one] at hob
    exact hob
  refine ⟨c, hc, ?_⟩
  apply ExactShiftResidual.ext_single
  intro m
  have hm := (hformula m).trans (raw_basis a b c ‖C₀‖ (norm_nonneg _) hc m).symm
  simpa only [single_classical] using hm

/-- Reversal of a raw edge conjugates its coefficient at the inverse full
array, exactly as for the unit-phase edge. -/
def rawReverse (a b : ℤ) (hab : a ≠ b) (c : Donor N a → ℂ) : Donor N b → ℂ :=
  fun d => conj (c ((donorEquiv a b hab).symm d))

theorem rawReverse_bound (a b : ℤ) (hab : a ≠ b) (c : Donor N a → ℂ)
    (M : ℝ) (hc : ∀ d, ‖c d‖ ≤ M) (d : Donor N b) :
    ‖rawReverse a b hab c d‖ ≤ M := by
  rw [rawReverse, Complex.norm_conj]
  exact hc _

theorem raw_adjoint (a b : ℤ) (hab : a ≠ b) (c : Donor N a → ℂ)
    (M : ℝ) (hM : 0 ≤ M) (hc : ∀ d, ‖c d‖ ≤ M) :
    (raw a b c M hM hc).adjoint =
      raw b a (rawReverse a b hab c) M hM (rawReverse_bound a b hab c M hc) := by
  ext v m
  rw [raw_adjoint_apply]
  split_ifs with h
  · let d : Donor N a := ⟨m,h⟩
    have hdest := raw_at_destination b a (rawReverse a b hab c) M hM
      (rawReverse_bound a b hab c M hc) v (donorEquiv a b hab d)
    rw [destination_reverse] at hdest
    simp only [rawReverse, Equiv.symm_apply_apply] at hdest
    exact hdest.symm
  · exact (raw_off_receiver b a hab.symm _ _ _ _ v m h).symm

theorem completePhase_conj (z : ℂ) : (completePhase (conj z)).1 = conj (completePhase z).1 := by
  by_cases h : z = 0
  · simp [h, completePhase_zero]
  · rw [completePhase_nonzero _ ((map_ne_zero (starRingEnd ℂ)).2 h), completePhase_nonzero z h,
      Complex.norm_conj, map_div₀, Complex.conj_ofReal]

theorem complete_reverse (a b : ℤ) (hab : a ≠ b) (c : Donor N a → ℂ) :
    (completedSeed a b c).adjoint = completedSeed b a (rawReverse a b hab c) := by
  rw [completedSeed_adjoint a b hab, completedSeed]
  congr 1
  funext d
  apply Subtype.ext
  exact (completePhase_conj _).symm

theorem raw_polar_bounds (a b : ℤ) (hab : a ≠ b) (c : Donor N a → ℂ)
    (M : ℝ) (hM : 0 ≤ M) (hc : ∀ d, ‖c d‖ ≤ M)
    (g : H N) (ζ : Phase) (s : ℝ) (hs : 0 ≤ s) :
    let C := raw a b c M hM hc
    let e := ‖C g - ((s : ℂ) * ζ.1) • g‖ +
      ‖C.adjoint g - ((s : ℂ) * conj ζ.1) • g‖
    s * ‖completedSeed a b c g - ζ.1 • g‖ ≤ e ∧
      s * ‖(completedSeed a b c).adjoint g - conj ζ.1 • g‖ ≤ e := by
  let C := raw a b c M hM hc
  let fwd := RetargetPolarR48b.completed_forward_bound a b hab C c
    (raw_at_destination a b c M hM hc)
    (fun v m => by rw [raw_adjoint_apply, dite_eq_left m.2]; rfl)
    (raw_off_receiver a b hab c M hM hc) g ζ s hs
  refine ⟨fwd, ?_⟩
  let c' := rawReverse a b hab c
  let hc' := rawReverse_bound a b hab c M hc
  let ζ' : Phase := ⟨conj ζ.1, by rw [Complex.norm_conj, ζ.2]⟩
  have h := RetargetPolarR48b.completed_forward_bound b a hab.symm
    (raw b a c' M hM hc') c' (raw_at_destination b a c' M hM hc')
    (fun v m => by rw [raw_adjoint_apply, dite_eq_left m.2]; rfl)
    (raw_off_receiver b a hab.symm c' M hM hc') g ζ' s hs
  have hraw : raw b a c' M hM hc' = C.adjoint := (raw_adjoint a b hab c M hM hc).symm
  have hcomp : completedSeed b a c' = (completedSeed a b c).adjoint :=
    (complete_reverse a b hab c).symm
  simp only [hraw, hcomp, ContinuousLinearMap.adjoint_adjoint, ζ', starRingEnd_self_apply] at h
  exact h.trans_eq (add_comm _ _)

/-- The one raw seed chosen for an increasing pair yields both completed
residuals in the full corrected coefficient space. -/
theorem graded_polar_bounds (B : BetheBasis L N) (C : HN L N →L[ℂ] HN L N)
    (a b : ℤ) (hab : a ≠ b) (hC : DynSeedGradingR47b.Graded B a b C) :
    ∃ c : Donor N a → ℂ, ∀ (ψ : HN L N) (ζ : Phase) (s : ℝ), 0 ≤ s →
      let g := J B ψ
      let e := DynSeedPolynomialR47b.residual C ((s : ℂ) * ζ.1) ψ
      s * ‖completedSeed a b c g - ζ.1 • g‖ ≤ e ∧
        s * ‖(completedSeed a b c).adjoint g - conj ζ.1 • g‖ ≤ e := by
  obtain ⟨c,hc,he⟩ := graded_is_raw B C a b hC
  refine ⟨c, fun ψ ζ s hs => ?_⟩
  have h := raw_polar_bounds a b hab c ‖inCoefficients B C‖ (norm_nonneg _) hc (J B ψ) ζ s hs
  dsimp only at h
  rw [← he, inCoefficients_adjoint, residual_inCoefficients, residual_inCoefficients] at h
  simpa only [DynSeedPolynomialR47b.residual, map_mul, Complex.conj_ofReal] using h

end QuantumNLS.RetargetEdgeR48b

#print axioms QuantumNLS.RetargetEdgeR48b.graded_is_raw
#print axioms QuantumNLS.RetargetEdgeR48b.graded_polar_bounds
end

/-! Uniform Cartesian control from the actual intensive diagonals and the
finite-cell phase estimates. The square-root inequality includes zero actions. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
open scoped ComplexConjugate ENNReal

namespace QuantumNLS.RetargetWeightsR48b
open Occupation OccupationHilbert FullOccupationAffinity
open FiniteCellSupport FiniteCellGauge RetargetEdgeR48b
variable {N : ℕ}

def cartesian (q : Arr N → Phase) (a b : ℤ) : H N →L[ℂ] H N :=
  sectorEq N (fun m => (q m).1) (fun m => by rw [Complex.normSq_eq_norm_sq, (q m).2]; norm_num) a b

theorem cartesian_adjoint (q : Arr N → Phase) (a b : ℤ) :
    (cartesian q a b).adjoint = cartesian q b a := Eq_adjoint _ _ _ _ _

theorem cartesian_diag (q : Arr N → Phase) (a : ℤ) :
    cartesian q a a = E N a a := Eq_diag _ _ _ _

def weight (N : ℕ) (a b : ℤ) : H N →L[ℂ] H N :=
  diagonal (fun m : Arr N => (coef N a b m.1 : ℂ)) 1 zero_le_one
    (fun m => coefficient_bound N a b m)

theorem weight_single (N : ℕ) (a b : ℤ) (m : Arr N) :
    weight N a b (lp.single 2 m 1) = (coef N a b m.1 : ℂ) • lp.single 2 m 1 := by
  have he : (coef N a b m.1 : ℂ) • (lp.single 2 m 1 : H N) =
      lp.single 2 m (coef N a b m.1 : ℂ) := by
    rw [← lp.single_smul]
    simp only [smul_eq_mul, mul_one]
  rw [he]
  apply lp.ext
  funext d
  by_cases h : d = m <;> simp [weight, lp.single_apply, h]

theorem cartesian_single (q : Arr N → Phase) (a b : ℤ) (m : Arr N) :
    cartesian q a b (lp.single 2 m 1) =
      if h : DonorOK a m.1 then
        lp.single 2 (shiftArr a b m h)
          ((q m).1 * conj (q (shiftArr a b m h)).1 * (coef N a b m.1 : ℂ))
      else 0 := by
  simpa only [cartesian, single_classical, mul_one] using sectorEq_single N (fun m => (q m).1) (fun m => by
    rw [Complex.normSq_eq_norm_sq, (q m).2]
    norm_num) a b m (1 : ℂ)

theorem cartesian_factor (q : Arr N → Phase) (a b : ℤ) :
    cartesian q a b = FiniteCellGauge.W q a b ∘L weight N a b := by
  apply ExactShiftResidual.ext_single
  intro m
  have hC := cartesian_single q a b m
  have hW := W_basis q a b m
  have hw := weight_single N a b m
  simp only [single_classical] at hC hW hw ⊢
  rw [hC, ContinuousLinearMap.comp_apply, hw, map_smul, hW]
  split_ifs with h
  · simp only [ratio, ← lp.single_smul, smul_eq_mul, mul_one]
    congr 1
    ring
  · simp

def frac (N : ℕ) (a : ℤ) (m : Arr N) : ℝ := (m.1 a : ℝ) / N

theorem frac_nonnegative (N : ℕ) (a : ℤ) (m : Arr N) : 0 ≤ frac N a m := by
  unfold frac
  positivity

theorem frac_le_one (hN : 0 < N) (a : ℤ) (m : Arr N) : frac N a m ≤ 1 := by
  rw [frac, ← coef_diag]
  exact coef_le_one hN m.2 _ _

theorem weighted_sq (hN : 0 < N) (a b : ℤ) (hab : a ≠ b) (m : Arr N) :
    coef N a b m.1 ^ 2 = frac N a m * (frac N b m + (N : ℝ)⁻¹) := by
  rw [coef_offdiag hab, div_pow, Real.sq_sqrt (by positivity)]
  unfold frac
  field_simp

theorem sqrt_sub_sq_bound {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.sqrt x - Real.sqrt y| ^ 2 ≤ |x - y| := by
  rw [sq_abs]
  rcases le_total y x with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    have hxy := Real.sqrt_le_sqrt h
    nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy,
      mul_nonneg (Real.sqrt_nonneg y) (sub_nonneg.mpr hxy)]
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    have hxy := Real.sqrt_le_sqrt h
    nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy,
      mul_nonneg (Real.sqrt_nonneg x) (sub_nonneg.mpr hxy)]

/-- With no endpoint lower bound, the Cartesian weight residual is at most
the square root of the intensive product residual. -/
theorem weight_residual (hN : 0 < N) (a b : ℤ) (hab : a ≠ b)
    (g : H N) (hg : ‖g‖ = 1) (A B δ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hA₁ : A ≤ 1)
    (ha : ‖E N a a g - (A : ℂ) • g‖ ≤ δ)
    (hb : ‖E N b b g - (B : ℂ) • g‖ ≤ δ) :
    ‖weight N a b g - (Real.sqrt (A*B) : ℂ) • g‖ ≤ Real.sqrt (2*δ + (N : ℝ)⁻¹) := by
  let U := E N a a g - (A : ℂ) • g
  let V := E N b b g - (B : ℂ) • g
  let d := E N b b U + (A : ℂ) • V + ((N : ℝ)⁻¹ : ℂ) • E N a a g
  have hd (m : Arr N) :
      d m = ((frac N a m * (frac N b m + (N : ℝ)⁻¹) - A*B : ℝ) : ℂ) * g m := by
    simp only [d, U, V, lp.coeFn_add, Pi.add_apply, E_diag_apply, coef_diag, lp.coeFn_sub, Pi.sub_apply,
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, frac]
    push_cast
    ring
  have hE (i : ℤ) (v : H N) : ‖E N i i v‖ ≤ ‖v‖ :=
    ((E N i i).le_opNorm v).trans (mul_le_of_le_one_left (norm_nonneg _) (E_norm_le ..))
  have hdB : ‖d‖ ≤ 2*δ + (N : ℝ)⁻¹ := by
    calc
      _ ≤ (‖E N b b U‖ + ‖(A : ℂ) • V‖) +
          ‖((N : ℝ)⁻¹ : ℂ) • E N a a g‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ (‖U‖ + ‖V‖) + (N : ℝ)⁻¹ * ‖g‖ := by
        rw [norm_smul, norm_smul, ← Complex.ofReal_inv, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonneg hA, Real.norm_of_nonneg (by positivity : 0 ≤ (N : ℝ)⁻¹)]
        exact add_le_add
          (add_le_add (hE b U) (mul_le_of_le_one_left (norm_nonneg _) hA₁))
          (mul_le_mul_of_nonneg_left (hE a g) (by positivity))
      _ ≤ _ := by rw [hg, mul_one, two_mul]; exact add_le_add (add_le_add ha hb) le_rfl
  let y := weight N a b g - (Real.sqrt (A*B) : ℂ) • g
  have hpoint (m : Arr N) : ‖y m‖ ^ 2 ≤ ‖d m‖ * ‖g m‖ := by
    let x := frac N a m * (frac N b m + (N : ℝ)⁻¹)
    have hx : 0 ≤ x := by
      unfold x
      exact mul_nonneg (frac_nonnegative ..) (add_nonneg (frac_nonnegative ..) (by positivity))
    have hs : Real.sqrt x = coef N a b m.1 := by
      dsimp only [x]
      rw [← weighted_sq hN a b hab m, Real.sqrt_sq (coef_nonneg ..)]
    change ‖y m‖ ^ 2 ≤ ‖d m‖ * ‖g m‖
    rw [hd, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hy : y m = ((Real.sqrt x - Real.sqrt (A*B) : ℝ) : ℂ) * g m := by
      simp only [y, weight, lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul, diagonal_apply, hs, Complex.ofReal_sub, sub_mul]
    rw [hy, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (sqrt_sub_sq_bound hx (mul_nonneg hA hB))
      (sq_nonneg ‖g m‖)).trans_eq (by dsimp [x]; ring)
  have hp : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hn : ‖y‖ ^ 2 ≤ 2*δ + (N : ℝ)⁻¹ := by
    rw [ExactShiftResidual.norm_sq_tsum]
    calc
      _ ≤ ∑' m, ‖d m‖ * ‖g m‖ :=
        (ExactShiftResidual.summable_norm_sq y).tsum_le_tsum hpoint (lp.summable_mul hp d g)
      _ ≤ ‖d‖ * ‖g‖ := lp.tsum_mul_le_mul_norm' hp d g
      _ ≤ _ := by rw [hg, mul_one]; exact hdB
  exact Real.le_sqrt_of_sq_le hn

/-- The same comparison covers a zero target. The phase is then any
unit completion with the required scalar factorization. -/
theorem cartesian_residual (q : Arr N → Phase) (hN : 0 < N) (a b : ℤ) (hab : a ≠ b)
    (g : H N) (hg : ‖g‖ = 1) (A B δ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hA₁ : A ≤ 1)
    (ha : ‖E N a a g - (A : ℂ) • g‖ ≤ δ)
    (hb : ‖E N b b g - (B : ℂ) • g‖ ≤ δ) (ζ : Phase) :
    ‖cartesian q a b g - ((Real.sqrt (A*B) : ℂ) * ζ.1) • g‖ ≤
      Real.sqrt (2*δ + (N : ℝ)⁻¹) +
        Real.sqrt (A*B) * ‖FiniteCellGauge.W q a b g - ζ.1 • g‖ := by
  let W := FiniteCellGauge.W q a b
  let s := Real.sqrt (A*B)
  have hW (v : H N) : ‖W v‖ ≤ ‖v‖ :=
    (W.le_opNorm v).trans (mul_le_of_le_one_left (norm_nonneg _) (W_norm_le q a b))
  rw [cartesian_factor, ContinuousLinearMap.comp_apply]
  have he : W (weight N a b g) - ((s : ℂ) * ζ.1) • g =
      W (weight N a b g - (s : ℂ) • g) + (s : ℂ) • (W g - ζ.1 • g) := by
    rw [map_sub, map_smul, smul_sub, smul_smul]
    abel
  change ‖W (weight N a b g) - ((s : ℂ) * ζ.1) • g‖ ≤ _
  rw [he]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact add_le_add ((hW _).trans (weight_residual hN a b hab g hg A B δ hA hB hA₁ ha hb)) le_rfl

end QuantumNLS.RetargetWeightsR48b

#print axioms QuantumNLS.RetargetWeightsR48b.weight_residual
#print axioms QuantumNLS.RetargetWeightsR48b.cartesian_residual
end

/-! Apply the accepted scalar finite-cell theorem to the selected coordinates.
The weighted estimate is uniform even when an action lies below the cutoff. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
open scoped ComplexConjugate BigOperators

namespace QuantumNLS.RetargetCellR48b
open Occupation OccupationHilbert FullOccupationAffinity FiniteCellSupport FiniteCellGauge
open RetargetWeightsR48b
variable {N : ℕ}

/-- Positive targets yield the printed phase. Zero targets have a specified
unit completion, which cancels from the Cartesian symbol. -/
def pairPhase (z w : ℂ) : Phase :=
  ⟨(completePhase z).1 * conj (completePhase w).1, by
    rw [norm_mul, Complex.norm_conj, (completePhase z).2, (completePhase w).2, one_mul]⟩

theorem pair_factor (z w : ℂ) :
    (Real.sqrt (‖z‖ ^ 2 * ‖w‖ ^ 2) : ℂ) * (pairPhase z w).1 = z * conj w := by
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _),
    Complex.ofReal_mul]
  change _ * ((completePhase z).1 * conj (completePhase w).1) = _
  calc
    _ = ((completePhase z).1 * (‖z‖ : ℂ)) * conj ((completePhase w).1 * (‖w‖ : ℂ)) := by
      rw [map_mul, Complex.conj_ofReal]
      ring
    _ = _ := by rw [completePhase_polar, completePhase_polar]

theorem pairPhase_eq_printed (z w : ℂ) (hz : z ≠ 0) (hw : w ≠ 0) :
    (pairPhase z w).1 = FiniteCellFinal.symbol z w :=
  FiniteCellFinal.completePhase_symbol z w hz hw

theorem phase_reverse (z w : ℂ) : (pairPhase w z).1 = conj (pairPhase z w).1 := by
  simp [pairPhase, mul_comm]

/-- Per-directed-edge bounds imply the actual ordered-pair hypothesis of the
accepted theorem using only the cardinality of the chosen finite head. -/
theorem stage_residual_sum (I : Finset ℤ) (ell : ℕ) (c : SelectedSeeds I N) (w : ↥I → ℂ)
    (g : H N) (η : ℝ) (hI : 0 < I.card) (hη : 0 ≤ η)
    (herr : ∀ (a b : ℤ) (hab : a ≠ b), a ∈ FiniteCellFinal.good I ell w →
      b ∈ FiniteCellFinal.good I ell w →
      ‖seedTransfer (extendSeeds I c) a b hab g -
        ((FiniteCellFinal.phases I w a).1 * conj (FiniteCellFinal.phases I w b).1) • g‖ ≤ η / I.card) :
    (∑ a : ↥(FiniteCellFinal.good I ell w), ∑ b : ↥((FiniteCellFinal.good I ell w).erase a.1),
      ‖seedTransfer (extendSeeds I c) a.1 b.1 (Finset.mem_erase.mp b.2).1.symm g -
        ((FiniteCellFinal.phases I w a.1).1 * conj (FiniteCellFinal.phases I w b.1).1) • g‖ ^ 2) ≤ η^2 := by
  let G := FiniteCellFinal.good I ell w
  have hcard : G.card ≤ I.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hcast : (0 : ℝ) < I.card := Nat.cast_pos.mpr hI
  have hbound : 0 ≤ η / I.card := div_nonneg hη hcast.le
  calc
    _ ≤ ∑ a : ↥G, ∑ b : ↥(G.erase a.1), (η / (I.card : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      exact pow_le_pow_left₀ (norm_nonneg _)
        (herr a.1 b.1 (Finset.mem_erase.mp b.2).1.symm a.2 (Finset.mem_erase.mp b.2).2) 2
    _ ≤ ∑ _ : ↥G, (I.card : ℝ) * (η / (I.card : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro a ha
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast (Finset.card_erase_le.trans hcard)) (sq_nonneg _)
    _ ≤ η^2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      calc
        _ ≤ (I.card : ℝ) * ((I.card : ℝ) * (η / (I.card : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
        _ = _ := by field_simp

/-- The fixed-cell Cartesian bound covers all selected pairs; the phase bound
requires the two endpoint lower bounds. -/
theorem cell_cartesian (I : Finset ℤ) (ell : ℕ) (hI : 2 ≤ I.card) (hell : 2 ≤ ell) (hN : ell ≤ N)
    (c : SelectedSeeds I N) (g : H N) (w : ↥I → ℂ) (δ η : ℝ)
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hg : ‖g‖ = 1) (hw : ∀ a, ‖w a‖ ≤ 1)
    (haction : ∀ a : ↥I, ‖E N a.1 a.1 g - ((‖w a‖ ^ 2 : ℝ) : ℂ) • g‖ ≤ δ)
    (hseed : ∀ (a b : ℤ) (hab : a ≠ b), a ∈ FiniteCellFinal.good I ell w →
      b ∈ FiniteCellFinal.good I ell w →
      ‖seedTransfer (extendSeeds I c) a b hab g -
        ((FiniteCellFinal.phases I w a).1 * conj (FiniteCellFinal.phases I w b).1) • g‖ ≤ η / I.card) :
    let q := q_N I ell c
    (∀ a b : ↥I, ‖cartesian q a.1 b.1 g - (w a * conj (w b)) • g‖ ≤
      max δ (Real.sqrt (2*δ + (N : ℝ)⁻¹) +
        max (FiniteCellFinal.printedBound I ell δ η) (2 * Real.sqrt (4 / (ell : ℝ))))) ∧
    (∀ a b : ↥I, a.1 ≠ b.1 → 4 / (ell : ℝ) ≤ ‖w a‖^2 → 4 / (ell : ℝ) ≤ ‖w b‖^2 →
      ‖FiniteCellGauge.W q a.1 b.1 g - (pairPhase (w a) (w b)).1 • g‖ ≤
        FiniteCellFinal.printedBound I ell δ η) := by
  let q := q_N I ell c
  have hsum := stage_residual_sum I ell c w g η (by omega) hη hseed
  have hphase (a b : ↥I) (hab : a.1 ≠ b.1) (ha : 4 / (ell : ℝ) ≤ ‖w a‖^2)
      (hb : 4 / (ell : ℝ) ≤ ‖w b‖^2) :
      ‖FiniteCellGauge.W q a.1 b.1 g - (pairPhase (w a) (w b)).1 • g‖ ≤
        FiniteCellFinal.printedBound I ell δ η :=
    (FiniteCellFinal.finite_target_bounds I ell hI hell hN c g w δ η hδ hη hg
      haction hsum a b hab ha hb).1
  refine ⟨?_, hphase⟩
  intro a b
  by_cases hab : a.1 = b.1
  · have he : a = b := Subtype.ext hab
    subst b
    have hh : w a * conj (w a) = (‖w a‖ ^ 2 : ℝ) := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    rw [cartesian_diag, hh]
    exact (haction a).trans (le_max_left _ _)
  let ζ := pairPhase (w a) (w b)
  let A := ‖w a‖ ^ 2
  let B := ‖w b‖ ^ 2
  have hA : 0 ≤ A := sq_nonneg _
  have hB : 0 ≤ B := sq_nonneg _
  have hA₁ : A ≤ 1 := pow_le_one₀ (norm_nonneg _) (hw a)
  have hB₁ : B ≤ 1 := pow_le_one₀ (norm_nonneg _) (hw b)
  have hs : 0 ≤ Real.sqrt (A*B) := Real.sqrt_nonneg _
  have hs₁ : Real.sqrt (A*B) ≤ 1 :=
    Real.sqrt_le_one.mpr ((mul_le_of_le_one_left hB hA₁).trans hB₁)
  have hcalc := cartesian_residual q (by omega) a.1 b.1 hab g hg A B δ hA hB hA₁
    (haction a) (haction b) ζ
  rw [pair_factor] at hcalc
  apply hcalc.trans
  apply le_trans _ (le_max_right _ _)
  gcongr
  by_cases hlarge : 4 / (ell : ℝ) ≤ A ∧ 4 / (ell : ℝ) ≤ B
  · exact ((mul_le_of_le_one_left (norm_nonneg _) hs₁).trans
      (hphase a b hab hlarge.1 hlarge.2)).trans (le_max_left _ _)
  · have hsmall : A*B ≤ 4 / (ell : ℝ) := by
      push Not at hlarge
      by_cases ha : 4 / (ell : ℝ) ≤ A
      · exact (mul_le_of_le_one_left hB hA₁).trans (hlarge ha).le
      · exact (mul_le_of_le_one_right hA hB₁).trans (lt_of_not_ge ha).le
    have hw₂ : ‖FiniteCellGauge.W q a.1 b.1 g - ζ.1 • g‖ ≤ 2 := by
      apply (norm_sub_le _ _).trans
      rw [norm_smul, ζ.2, hg, mul_one]
      have ht := ((FiniteCellGauge.W q a.1 b.1).le_opNorm g).trans
        (mul_le_mul_of_nonneg_right (W_norm_le q a.1 b.1) (norm_nonneg _))
      rw [hg, mul_one] at ht
      linarith
    exact ((mul_le_mul (Real.sqrt_le_sqrt hsmall) hw₂ (norm_nonneg _) (Real.sqrt_nonneg _)).trans_eq
      (mul_comm _ _)).trans (le_max_right _ _)

end QuantumNLS.RetargetCellR48b

#print axioms QuantumNLS.RetargetCellR48b.cell_cartesian
end

/-! Q06 consequences for the literal full-array gauge ratios. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
open scoped ComplexConjugate InnerProductSpace

namespace QuantumNLS.RetargetAffinityR48b
open Occupation OccupationHilbert FullOccupationAffinity FiniteCellGauge RetargetEdgeR48b
variable {N : ℕ}

theorem overlap_error (q : Arr N → Phase) (a b : ℤ) (ζ : Phase)
    (g : UnitCoefficients N) :
    ‖overlap a b (edgePhase q a b) g.1 - ζ.1‖ ≤
      ‖FiniteCellGauge.W q a b g.1 - ζ.1 • g.1‖ := by
  have hg : ⟪g.1, g.1⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, g.2]
    norm_num
  have he : overlap a b (edgePhase q a b) g.1 - ζ.1 =
      ⟪g.1, FiniteCellGauge.W q a b g.1 - ζ.1 • g.1⟫_ℂ := by
    rw [inner_sub_right, inner_smul_right, hg, mul_one]
    exact congrArg (· - ζ.1) (inner_transfer a b (edgePhase q a b) g.1).symm
  rw [he]
  simpa only [g.2, one_mul] using
    (norm_inner_le_norm (𝕜 := ℂ) g.1 (FiniteCellGauge.W q a b g.1 - ζ.1 • g.1))

theorem phase_errors (q : Arr N → Phase) (a b : ℤ) (hab : a ≠ b) (ζ : Phase)
    (g : UnitCoefficients N) (ε : ℝ) (_hε : 0 ≤ ε)
    (hf : ‖FiniteCellGauge.W q a b g.1 - ζ.1 • g.1‖ ≤ ε)
    (hr : ‖(FiniteCellGauge.W q a b).adjoint g.1 - conj ζ.1 • g.1‖ ≤ ε) :
    ExactShiftResidual.missing a g.1 ≤ 2*ε^2 ∧ ExactShiftResidual.missing b g.1 ≤ 2*ε^2 ∧
      |affinity a b g.1 - 1| ≤ ε^2 ∧ |defect a b (edgePhase q a b) ζ g.1| ≤ ε^2 ∧
      ‖overlap a b (edgePhase q a b) g.1 - ζ.1‖ ≤ ε := by
  have hsq : ‖FiniteCellGauge.W q a b g.1 - ζ.1 • g.1‖ ^ 2 +
      ‖(FiniteCellGauge.W q a b).adjoint g.1 - conj ζ.1 • g.1‖ ^ 2 ≤ 2*ε^2 := by
    rw [two_mul]
    exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) hf 2)
      (pow_le_pow_left₀ (norm_nonneg _) hr 2)
  obtain ⟨ha, hb, hA, hD⟩ := ExactShiftResidual.all_errors_le a b hab (edgePhase q a b) ζ g _ hsq
  have hhalf : 2 * ε^2 / 2 = ε^2 := by ring
  rw [hhalf] at hA hD
  exact ⟨ha, hb, hA, hD,
    (overlap_error q a b ζ g).trans hf⟩

theorem exterior_exact (q : Arr N → Phase) (a b i : ℤ) (m : Arr N) (hd : DonorOK a m.1)
    (hia : i ≠ a) (hib : i ≠ b) :
    FiniteCellGauge.W q a b (lp.single 2 m 1) =
      ((q m).1 * conj (q (shiftArr a b m hd)).1) • (lp.single 2 (shiftArr a b m hd) 1 : H N) ∧
    (shiftArr a b m hd).1 i = m.1 i := by
  refine ⟨?_, shift_apply_exterior _ hia hib⟩
  have h := W_basis q a b m
  rw [dite_eq_left hd] at h
  simpa only [single_classical, ratio] using h

end QuantumNLS.RetargetAffinityR48b

#print axioms QuantumNLS.RetargetAffinityR48b.phase_errors
#print axioms QuantumNLS.RetargetAffinityR48b.exterior_exact
end

/-! Finite-cell tolerances selected before any profile.
Only an increasing exhaustion is asserted in R-D51987CA. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
open Set Filter Topology

namespace QuantumNLS.RetargetTuneR48b

/-- Terms in the Cartesian estimate, with the inverse particle number
bounded by the inverse width since every tested sector has (N ge ell). -/
def budget (I : Finset ℤ) (ell : ℕ) (δ : ℝ) : ℝ :=
  max δ (Real.sqrt (2*δ + (ell : ℝ)⁻¹) +
    max (FiniteCellFinal.printedBound I ell δ δ) (2 * Real.sqrt (4 / (ell : ℝ))))

theorem budget_continuous (I : Finset ℤ) (ell : ℕ) : Continuous (budget I ell) := by
  have h : Continuous (fun δ : ℝ => FiniteCellFinal.printedBound I ell δ δ) := by
    unfold FiniteCellFinal.printedBound FiniteCellFinal.boundaryBound
    fun_prop
  unfold budget
  exact continuous_id.max ((Real.continuous_sqrt.comp (by fun_prop)).add (h.max continuous_const))

theorem tune (I : Finset ℤ) (ε ρ : ℝ) (hε : 0 < ε) (hρ : 0 < ρ) :
    ∃ (ell : ℕ) (δ : ℝ), 2 ≤ ell ∧ 0 < δ ∧
      4 / (ell : ℝ) < ρ ∧ budget I ell δ < ε := by
  let e := ε / 4
  have he : 0 < e := by dsimp [e]; positivity
  obtain ⟨ell, hell⟩ := exists_nat_gt (max (16/e^2) (max (4/ρ) 2))
  have hℓ : 2 < (ell : ℝ) :=
    (le_max_right (4/ρ) 2).trans_lt ((le_max_right (16/e^2) _).trans_lt hell)
  have hℓ' : (0 : ℝ) < ell := by linarith
  have hℓ₂ : 2 ≤ ell := by exact_mod_cast hℓ.le
  have hcut : 4 / (ell : ℝ) < ρ := by
    have h := (le_max_left (4/ρ) 2).trans_lt ((le_max_right (16/e^2) _).trans_lt hell)
    apply (div_lt_iff₀ hℓ').2
    have hh := (div_lt_iff₀ hρ).1 h
    simpa only [mul_comm] using hh
  have hsmall : 16 / (ell : ℝ) < e^2 := by
    have h := (le_max_left (16/e^2) _).trans_lt hell
    apply (div_lt_iff₀ hℓ').2
    have hh := (div_lt_iff₀ (by positivity : 0 < e^2)).1 h
    simpa only [mul_comm] using hh
  have h1 : Real.sqrt ((ell : ℝ)⁻¹) < e := by
    apply (Real.sqrt_lt' he).2
    rw [← one_div]
    exact (div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 16) hℓ'.le).trans_lt hsmall
  have h2 : Real.sqrt (8 / (ell : ℝ)) < e := by
    apply (Real.sqrt_lt' he).2
    exact (div_le_div_of_nonneg_right (by norm_num : (8 : ℝ) ≤ 16) hℓ'.le).trans_lt hsmall
  have h3 : 2 * Real.sqrt (4 / (ell : ℝ)) < e := by
    have h4 : Real.sqrt (4 / (ell : ℝ)) < e/2 := by
      apply (Real.sqrt_lt' (by positivity : 0 < e/2)).2
      have href : 4 / (ell : ℝ) = (16 / (ell : ℝ))/4 := by ring
      rw [href]
      nlinarith
    linarith
  have hzero : budget I ell 0 < ε := by
    unfold budget FiniteCellFinal.printedBound FiniteCellFinal.boundaryBound
    simp only [mul_zero, zero_pow (by decide : 2 ≠ 0), zero_add, Real.sqrt_zero, add_zero]
    exact max_lt hε (by have hh := max_lt h2 h3; dsimp [e] at *; linarith)
  have hn : {δ : ℝ | budget I ell δ < ε} ∈ 𝓝 0 :=
    (budget_continuous I ell).continuousAt (gt_mem_nhds hzero)
  obtain ⟨r, hr, hs⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨ell, r/2, hℓ₂, by positivity, hcut, hs ?_⟩
  rw [Metric.mem_ball, dist_zero_right, Real.norm_of_nonneg (by positivity : 0 ≤ r/2)]
  linarith

theorem phase_le_budget (I : Finset ℤ) (ell : ℕ) (δ : ℝ) :
    FiniteCellFinal.printedBound I ell δ δ ≤ budget I ell δ := by
  unfold budget
  exact (le_max_left _ _).trans ((le_add_of_nonneg_left (Real.sqrt_nonneg _)).trans (le_max_right _ _))

end QuantumNLS.RetargetTuneR48b

#print axioms QuantumNLS.RetargetTuneR48b.tune
end

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (name, _) in env.constants.toList do
    let prefixes := ["QuantumNLS.RetargetPolarR48b.", "QuantumNLS.RetargetEdgeR48b.", "QuantumNLS.RetargetWeightsR48b.", "QuantumNLS.RetargetCellR48b.", "QuantumNLS.RetargetAffinityR48b.", "QuantumNLS.RetargetTuneR48b."]
    if prefixes.any (fun start => name.toString.startsWith start) ||
        name.toString.startsWith "_private.QuantumNLS.RetargetScalarR48b." then
      pending := pending.push name
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    unless seen.contains name do
      seen := seen.insert name
      if (name.toString.splitOn "HeldGP14Tonelli").length > 1 then
        throwError "Rejected dependency: {name}"
      if let some info := env.find? name then
        match info with
        | .axiomInfo _ =>
          unless name == ``propext || name == ``Classical.choice || name == ``Quot.sound do
            throwError "Nonstandard dependency: {name}"
        | _ => pure ()
        pending := pending ++ info.type.getUsedConstants
        if let some value := info.value? (allowOpaque := true) then
          pending := pending ++ value.getUsedConstants
      else
        throwError "Missing dependency: {name}"
  Lean.logInfo m!"R48b aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only."
