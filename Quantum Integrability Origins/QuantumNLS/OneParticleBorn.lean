import Mathlib
import QuantumNLS.RootMeasureNoLoss
import QuantumNLS.Fourier
import QuantumNLS.BetheOneParticleAction

/-!
# R-28C650F0 `prop:root-free`, free-limit clause, step (i): the `N = 1` Born law is the Fourier-coefficient law

Source: `ROOT_spectral_measure.tex`, `prop:root-free` (proof: "The periodic version of eq:root-approximate-identity and Parseval give
`a_1(z) = Σ_n |û(n)|² ∫_0^L e^{i(z−2πn/L)t} dt = i(1−e^{izL}) Σ_n |û(n)|²/(z−2πn/L)`").

For the accepted physical Bethe basis at `N = 1` (UBB1, coupling `κ/1`):
* `roots_one`: the DEF-006 root of the occupation array `m ∈ 𝓜_1` is `2π n_m/L`, where `n_m = idx m` is the integer label, and `idxEquiv : 𝓜_1 ≃ ℤ`;
* `born_one`: `bornLaw(Ψ_{1,m}, u) = |û(idx m)|²` with `û(n) = coeff L u n = ⟨e_n, u⟩` the report's Fourier coefficient (DEF-001, `Fourier.lean`);
* `hasSum_a1_fourier`: `a_1(z) = ⟨u, K_{1,z} u⟩ = Σ_{n∈ℤ} |û(n)|² · i(1−e^{izL})/(z − 2πn/L)`, `Im z > 0`, unit `u`.
No EXT-025 contract is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal NNReal

noncomputable section

namespace QuantumNLS.OneParticleBorn

open QuantumNLS.PhysicalTensor (L2T L2TN prodLp prodFun memLp_prodFun torusPiMeasure)
open QuantumNLS.BetheLabels (MArr arrRoots)
open QuantumNLS.BetheFreeFamily (Label)
open QuantumNLS.BetheConditionalBasis (labelArr normalizedWave)
open QuantumNLS.Fourier (coeff mode modeLp fourierL2 coeFn_modeLp fourierL2_modeLp fourierL2_apply)
open QuantumNLS.BetheCoefficientTransform (bornLaw productVec)

variable {L : ℝ} [Fact (0 < L)]

/-! ### Labels of one particle -/

/-- The integer attached to the occupation array `m ∈ 𝓜_1` (`n = (labelArr)⁻¹ m`, `n : Fin 1 → ℤ`). -/
def idx (m : MArr 1) : ℤ := ((labelArr 1).symm m).1 0

/-- `𝓜_1 ≃ ℤ`. -/
def idxEquiv : MArr 1 ≃ ℤ :=
  (labelArr 1).symm.trans
    { toFun := fun n => n.1 0
      invFun := fun k => ⟨fun _ => k, fun _ _ _ => le_rfl⟩
      left_inv := fun n => Subtype.ext (funext fun i => by rw [Subsingleton.elim i 0])
      right_inv := fun k => rfl }

theorem idxEquiv_apply (m : MArr 1) : idxEquiv m = idx m := rfl

theorem sourceRoot_one {c : ℝ} (hc : 0 < c) (n : Fin 1 → ℤ) :
    QuantumNLS.BetheSmooth.sourceRoots L n c 0 = 2 * Real.pi * (n 0) / L := by
  have hL : 0 < L := Fact.out
  have h := congrFun (QuantumNLS.BetheSmooth.sourceRoots_solves hL hc n) 0
  simp only [QuantumNLS.BetheAdmission.logMap, QuantumNLS.BetheSmooth.sourceNumbers, Fin.sum_univ_one, sub_self,
    zero_div, Real.arctan_zero, mul_zero, add_zero, Nat.cast_one, Fin.val_zero, Nat.cast_zero, sub_zero] at h
  field_simp
  linarith

theorem roots_one {κ : ℝ} (hκ : 0 < κ) (m : MArr 1) :
    arrRoots L (κ / ((1 : ℕ) : ℝ)) m 0 = 2 * Real.pi * (idx m) / L := by
  have hL : 0 < L := Fact.out
  have hc : 0 < κ / ((1 : ℕ) : ℝ) := by simpa using hκ
  have h1 : QuantumNLS.BetheSmooth.sourceRoots L (QuantumNLS.NormalityBridge.label m).1 (κ / ((1 : ℕ) : ℝ)) 0 =
      arrRoots L (κ / ((1 : ℕ) : ℝ)) m (Fin.rev 0) := by
    rw [QuantumNLS.RootMeasureTransfer.label_val]
    exact QuantumNLS.BetheLabels.sourceRoots_eq_roots_rev hL hc _ 0
  have h2 : Fin.rev (0 : Fin 1) = 0 := Subsingleton.elim _ _
  rw [h2] at h1
  rw [← h1, sourceRoot_one hc]
  rfl

/-! ### Fourier modes -/

theorem norm_modeLp (n : ℤ) : ‖modeLp L n‖ = 1 := by
  rw [← (fourierL2 L).norm_map, fourierL2_modeLp]
  rw [lp.norm_single (by norm_num)]
  simp

theorem inner_modeLp (n : ℤ) (u : L2T L) : ⟪modeLp L n, u⟫_ℂ = coeff L (u : AddCircle L → ℂ) n := by
  calc ⟪modeLp L n, u⟫_ℂ = ⟪fourierL2 L (modeLp L n), fourierL2 L u⟫_ℂ := ((fourierL2 L).inner_map_map _ _).symm
    _ = ⟪lp.single 2 n (1 : ℂ), fourierL2 L u⟫_ℂ := by rw [fourierL2_modeLp]
    _ = fourierL2 L u n := by rw [lp.inner_single_left]; simp
    _ = coeff L (u : AddCircle L → ℂ) n := fourierL2_apply L u n

theorem norm_prodLp_mode (n : ℤ) : ‖prodLp (fun _ : Fin 1 => modeLp L n)‖ = 1 := by
  have h2 : ‖prodLp (fun _ : Fin 1 => modeLp L n)‖ ^ 2 = 1 := by
    have := norm_sq_eq_re_inner (𝕜 := ℂ) (prodLp (fun _ : Fin 1 => modeLp L n))
    rw [this, QuantumNLS.PhysicalTensor.inner_prodLp, Fin.prod_univ_one, inner_self_eq_norm_sq_to_K,
      norm_modeLp]
    simp
  nlinarith [norm_nonneg (prodLp (fun _ : Fin 1 => modeLp L n))]

/-- The one-particle Bethe wave is `√L` times the product of one Fourier mode. -/
theorem wave_eq {c : ℝ} (hc : 0 < c) (n : Fin 1 → ℤ) (hn : Antitone n) :
    (QuantumNLS.BetheH1.wave (L := L) hc hn : L2TN L 1) =
      ((Real.sqrt L : ℝ) : ℂ) • prodLp (fun _ : Fin 1 => modeLp L (n 0)) := by
  have hL : 0 < L := Fact.out
  apply Lp.ext
  have hmode : ∀ᵐ y ∂(torusPiMeasure L 1),
      (modeLp L (n 0) : AddCircle L → ℂ) (y 0) = mode L (n 0) (y 0) := by
    have hp := measurePreserving_funUnique (volume : Measure (AddCircle L)) (Fin 1)
    have := hp.quasiMeasurePreserving.ae (coeFn_modeLp L (n 0))
    rw [show torusPiMeasure L 1 = Measure.pi (fun _ : Fin 1 => (volume : Measure (AddCircle L))) from rfl]
    exact this
  filter_upwards [QuantumNLS.BetheH1.coe_wave hc hn,
    Lp.coeFn_smul ((Real.sqrt L : ℝ) : ℂ) (prodLp (fun _ : Fin 1 => modeLp L (n 0))),
    (memLp_prodFun (fun _ : Fin 1 => modeLp L (n 0))).coeFn_toLp, hmode] with y h1 h2 h3 h4
  rw [h1, QuantumNLS.BetheOneParticleAction.torusExtension_one L c n y, h2]
  simp only [Pi.smul_apply, smul_eq_mul]
  have h3' : (prodLp (fun _ : Fin 1 => modeLp L (n 0)) : (Fin 1 → AddCircle L) → ℂ) y = mode L (n 0) (y 0) := by
    have : (prodLp (fun _ : Fin 1 => modeLp L (n 0)) : (Fin 1 → AddCircle L) → ℂ) y =
        prodFun (fun _ : Fin 1 => modeLp L (n 0)) y := h3
    rw [this]
    simp only [prodFun, Fin.prod_univ_one]
    exact h4
  rw [h3']
  unfold mode QuantumNLS.BetheOneParticleAction.exponential
  rw [sourceRoot_one hc n]
  have hy : (y 0) = (((QuantumNLS.BetheWeakGradient.representatives L y 0 : ℝ)) : AddCircle L) := by
    unfold QuantumNLS.BetheWeakGradient.representatives
    exact (AddCircle.coe_equivIco).symm
  have hs : (Real.sqrt L : ℝ) ≠ 0 := (Real.sqrt_pos.2 hL).ne'
  rw [hy, fourier_coe_apply]
  have hsc : ((Real.sqrt L : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hs, Complex.ofReal_one, one_mul]
  congr 1
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  push_cast
  field_simp

/-- **The coefficient of the `N = 1` physical basis against `u`** is the Fourier coefficient. -/
theorem coef_one {x : ℝ} (hx : 0 < x) (ℓ : Label 1) (u : L2T L) :
    ⟪normalizedWave L 1 ⟨x, hx.le⟩ ℓ, QuantumNLS.BethePhysicalTransfer.symmetricPosition L 1 (productVec L 1 u)⟫_ℂ =
      coeff L (u : AddCircle L → ℂ) (ℓ.1 0) := by
  have hL : 0 < L := Fact.out
  set c : ℝ≥0 := ⟨x, hx.le⟩ with hcdef
  have hc : 0 < (c : ℝ) := hx
  have hW : ((QuantumNLS.BetheContinuityInputs.wave (L := L) c ℓ : QuantumNLS.ContactOperator.SymL2 L 1) : L2TN L 1) =
      ((Real.sqrt L : ℝ) : ℂ) • prodLp (fun _ : Fin 1 => modeLp L (ℓ.1 0)) := by
    rw [QuantumNLS.BetheOneParticleAction.continuedWave_one_eq L hc ℓ]
    exact wave_eq hc ℓ.1 ℓ.2
  have hV : ((QuantumNLS.BethePhysicalTransfer.symmetricPosition L 1 (productVec L 1 u) :
      QuantumNLS.ContactOperator.SymL2 L 1) : L2TN L 1) = prodLp (fun _ : Fin 1 => u) :=
    QuantumNLS.PhysicalTensor.physUnitary_ptprod (fun _ : Fin 1 => u)
  have hnorm : ‖(QuantumNLS.BetheContinuityInputs.wave (L := L) c ℓ : QuantumNLS.ContactOperator.SymL2 L 1)‖ =
      Real.sqrt L := by
    rw [← Submodule.norm_coe, hW, norm_smul, norm_prodLp_mode, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_one]
  have hsrc : QuantumNLS.BetheConditionalBasis.sourceWave L 1 c ℓ =
      QuantumNLS.BetheContinuityInputs.wave (L := L) c ℓ := rfl
  set W : QuantumNLS.ContactOperator.SymL2 L 1 := QuantumNLS.BetheContinuityInputs.wave (L := L) c ℓ with hWdef
  set V : QuantumNLS.ContactOperator.SymL2 L 1 :=
    QuantumNLS.BethePhysicalTransfer.symmetricPosition L 1 (productVec L 1 u) with hVdef
  have hI : ⟪W, V⟫_ℂ = ⟪(W : L2TN L 1), (V : L2TN L 1)⟫_ℂ := rfl
  have hs : (Real.sqrt L : ℝ) ≠ 0 := (Real.sqrt_pos.2 hL).ne'
  have hsc : ((Real.sqrt L : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  have hstep : ⟪(((‖W‖ : ℝ) : ℂ))⁻¹ • W, V⟫_ℂ = (starRingEnd ℂ) ((((‖W‖ : ℝ) : ℂ))⁻¹) * ⟪W, V⟫_ℂ :=
    inner_smul_left (𝕜 := ℂ) (E := QuantumNLS.ContactOperator.SymL2 L 1) W V _
  have hstep2 : ⟪(((Real.sqrt L : ℝ) : ℂ)) • prodLp (fun _ : Fin 1 => modeLp L (ℓ.1 0)),
      prodLp (fun _ : Fin 1 => u)⟫_ℂ =
      (starRingEnd ℂ) ((Real.sqrt L : ℝ) : ℂ) * ⟪prodLp (fun _ : Fin 1 => modeLp L (ℓ.1 0)),
        prodLp (fun _ : Fin 1 => u)⟫_ℂ :=
    inner_smul_left (𝕜 := ℂ) (E := L2TN L 1) _ _ _
  show ⟪(((‖W‖ : ℝ) : ℂ))⁻¹ • W, V⟫_ℂ = _
  rw [hstep, hI, hW, hV, hstep2, QuantumNLS.PhysicalTensor.inner_prodLp]
  simp only [Fin.prod_univ_one, inner_modeLp, hnorm, Complex.conj_ofReal, map_inv₀]
  field_simp

/-! ### The Born law -/

theorem born_one {κ : ℝ} (hκ : 0 < κ) (u : L2T L) (m : MArr 1) :
    bornLaw (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L 1 Nat.one_pos hκ) u m =
      ‖coeff L (u : AddCircle L → ℂ) (idx m)‖ ^ 2 := by
  have hc : 0 < κ / ((1 : ℕ) : ℝ) := by simpa using hκ
  have h1 := QuantumNLS.BetheCoefficientTransform.bornLaw_eq_coefficient
    (QuantumNLS.UnconditionalBetheBasis.physicalBasis L 1 Nat.one_pos (κ / ((1 : ℕ) : ℝ)) hc) u m
  have h2 := QuantumNLS.UnconditionalBetheBasis.coefficientTransform_apply L 1 Nat.one_pos
    (κ / ((1 : ℕ) : ℝ)) hc (productVec L 1 u) m
  have h3 := coef_one hc ((labelArr 1).symm m) u
  change bornLaw (QuantumNLS.UnconditionalBetheBasis.physicalBasis L 1 Nat.one_pos (κ / ((1 : ℕ) : ℝ)) hc) u m = _
  rw [h1]
  change ‖QuantumNLS.UnconditionalBetheBasis.coefficientTransform L 1 Nat.one_pos (κ / ((1 : ℕ) : ℝ)) hc
    (productVec L 1 u) m‖ ^ 2 = _
  rw [h2, h3]
  rfl

/-- **`a_1(z) = Σ_n |û(n)|² · i(1−e^{izL})/(z − 2πn/L)`** (the periodic approximate-identity formula, via the accepted `N = 1` basis). -/
theorem hasSum_a1_fourier {κ : ℝ} (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {z : ℂ} (hz : 0 < z.im) :
    HasSum (fun n : ℤ => ((‖coeff L (u : AddCircle L → ℂ) n‖ ^ 2 : ℝ) : ℂ) *
        (Complex.I * (1 - Complex.exp (Complex.I * z * L)) / (z - ((2 * Real.pi * n / L : ℝ) : ℂ))))
      (QuantumNLS.KernelDefinition.kernelProductSymbol (QuantumNLS.NormalizedTransfer.orderedKernel L 1 z) u) := by
  have h := QuantumNLS.RootMeasureNoLoss.hasSum_a1 hκ u hu hz
  refine (idxEquiv.hasSum_iff (f := fun n : ℤ => ((‖coeff L (u : AddCircle L → ℂ) n‖ ^ 2 : ℝ) : ℂ) *
        (Complex.I * (1 - Complex.exp (Complex.I * z * L)) / (z - ((2 * Real.pi * n / L : ℝ) : ℂ))))).1 ?_
  convert h using 1
  funext m
  simp only [Function.comp_apply, idxEquiv_apply]
  rw [born_one hκ u m, roots_one hκ m]

/-- **Parseval for the Fourier law**: `Σ_n |û(n)|² = ‖u‖²`. -/
theorem hasSum_coeff_sq (u : L2T L) :
    HasSum (fun n : ℤ => ‖coeff L (u : AddCircle L → ℂ) n‖ ^ 2) (‖u‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) (fourierL2 L u)
  have e1 : ((2 : ENNReal).toReal) = 2 := by norm_num
  simp only [e1, Real.rpow_two] at h
  rw [(fourierL2 L).norm_map] at h
  convert h using 1
  funext n
  rw [fourierL2_apply]

end QuantumNLS.OneParticleBorn

#print axioms QuantumNLS.OneParticleBorn.roots_one
#print axioms QuantumNLS.OneParticleBorn.wave_eq
#print axioms QuantumNLS.OneParticleBorn.coef_one
#print axioms QuantumNLS.OneParticleBorn.born_one
#print axioms QuantumNLS.OneParticleBorn.hasSum_a1_fourier
#print axioms QuantumNLS.OneParticleBorn.hasSum_coeff_sq
