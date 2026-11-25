import Mathlib
import QuantumNLS.RootTorusConversion
import QuantumNLS.NormalizedTransfer
import QuantumNLS.L2SpatialTransfer

/-!
# R-7E0532E7 `eq:root-trace-symbol`, quantum side: the ordered-kernel product symbol as iterated interval integrals

For the actual physical ordered kernels (`NormalizedTransfer.orderedKernel L r z = BethePhysicalTransfer.physicalKernel`,
the compression `P_r (K̃⁺ + K̃⁻) P_r` of the literal raw alternating-chamber operators) and every physical `L²` class `u`:

**`kps_eq`**: `kernelProductSymbol (orderedKernel L r z) u = Wr (ū) u z r L + e^{izL} · Wr u ū (−z) r L`

with `Wr` the iterated interval integral of `RootChamberIntegral` and `profile u` the canonical pullback of `u` to `[0,L]`.
Chain: `inner_physicalKernel` (compression adjoint), `physUnitary(u^{⊗r}) = prodLp`, `Kernel.inner_operator`/`form`,
a.e. identification of the product wave function with `∏ profile(reps x_j)`, `RootTorusConversion.torus_pair_integral`,
`RootChamberIntegral.Theta_eq_Wr`.  The minus kernel is treated through the coordinate swap `integral_prod_swap`.
No EXT-025 contract, no normalization on `u`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open MeasureTheory Set Filter ComplexConjugate
open scoped InnerProductSpace

namespace QuantumNLS.RootTraceSymbolQuantum

open QuantumNLS.PhysicalTensor (L2T L2TN torusPiMeasure prodLp)
open QuantumNLS.BetheWeakGradient (representatives measurable_representatives)
open QuantumNLS.BetheTransferKernelAdjoint (rawPlus rawMinus PlusOrder displacement)
open QuantumNLS.BetheTransferOperators (plusKernel minusKernel rawOperator measurable_rawPlus measurable_rawMinus)
open QuantumNLS.RootChamberIntegral QuantumNLS.RootTorusConversion
open QuantumNLS.L2SpatialTransfer (profile intervalIntegrable_profile)

variable {L : ℝ} [Fact (0 < L)]

theorem measurable_profile (u : L2T L) : Measurable (profile u) :=
  ((Lp.stronglyMeasurable u).measurable).comp AddCircle.measurable_mk'

theorem u_eq_profile_rep (u : L2T L) {r : ℕ} (x : Fin r → AddCircle L) (j : Fin r) :
    u (x j) = profile u (representatives L x j) := by
  unfold profile representatives
  rw [AddCircle.coe_equivIco]

/-- The product wave function is a.e. `∏ profile (reps x_j)`. -/
theorem prod_ae (u : L2T L) (r : ℕ) :
    ((prodLp (fun _ : Fin r => u) : L2TN L r) : (Fin r → AddCircle L) → ℂ) =ᵐ[torusPiMeasure L r]
      fun x => ∏ j, profile u (representatives L x j) := by
  have h := QuantumNLS.PhysicalTensor.memLp_prodFun (L := L) (N := r) (fun _ : Fin r => u)
  filter_upwards [h.coeFn_toLp] with x hx
  rw [QuantumNLS.PhysicalTensor.prodLp, hx, QuantumNLS.PhysicalTensor.prodFun]
  exact Finset.prod_congr rfl (fun j _ => u_eq_profile_rep u x j)

/-- Integrand of the bilinear form against a kernel function, with the product wave function replaced. -/
theorem form_eq_pair (u : L2T L) (r : ℕ) (k : QuantumNLS.BetheIntegralOperator.Kernel (torusPiMeasure L r)) (K : (Fin r → ℝ) → (Fin r → ℝ) → ℂ)
    (hk : ∀ p, k.fn p = K (representatives L p.1) (representatives L p.2)) :
    k.form (prodLp (fun _ : Fin r => u)) (prodLp (fun _ : Fin r => u)) =
      ∫ p : (Fin r → AddCircle L) × (Fin r → AddCircle L),
        conj (∏ j, profile u (representatives L p.1 j)) * K (representatives L p.1) (representatives L p.2) *
          ∏ j, profile u (representatives L p.2 j) ∂((torusPiMeasure L r).prod (torusPiMeasure L r)) := by
  unfold QuantumNLS.BetheIntegralOperator.Kernel.form
  refine integral_congr_ae ?_
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := torusPiMeasure L r) (ν := torusPiMeasure L r)).ae_eq_comp (prod_ae u r)
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := torusPiMeasure L r) (ν := torusPiMeasure L r)).ae_eq_comp (prod_ae u r)
  filter_upwards [h1, h2] with p hp1 hp2
  simp only [Function.comp_apply] at hp1 hp2
  simp only [QuantumNLS.BetheIntegralOperator.Kernel.integrand]
  rw [hp1, hp2, hk]

/-! ### The plus and minus parts -/

section Parts

variable (z : ℂ) (u : L2T L) (r : ℕ)

/-- `Ψ⁺ a b = conj(∏ prof a_j) · rawPlus a b · ∏ prof b_j`. -/
def PsiP (a b : Fin r → ℝ) : ℂ :=
  conj (∏ j, profile u (a j)) * rawPlus L z a b * ∏ j, profile u (b j)

def PsiM (a b : Fin r → ℝ) : ℂ :=
  conj (∏ j, profile u (a j)) * rawMinus L z a b * ∏ j, profile u (b j)

theorem measurable_PsiP : Measurable (fun p : (Fin r → ℝ) × (Fin r → ℝ) => PsiP z u r p.1 p.2) := by
  have hp : Measurable (profile u) := measurable_profile u
  have h1 : Measurable (fun p : (Fin r → ℝ) × (Fin r → ℝ) => conj (∏ j, profile u (p.1 j))) :=
    Complex.continuous_conj.measurable.comp (Finset.measurable_prod _ (fun j _ => hp.comp ((measurable_pi_apply j).comp measurable_fst)))
  have h2 : Measurable (fun p : (Fin r → ℝ) × (Fin r → ℝ) => ∏ j, profile u (p.2 j)) :=
    Finset.measurable_prod _ (fun j _ => hp.comp ((measurable_pi_apply j).comp measurable_snd))
  exact (h1.mul (measurable_rawPlus r L z)).mul h2

theorem measurable_PsiM : Measurable (fun p : (Fin r → ℝ) × (Fin r → ℝ) => PsiM z u r p.1 p.2) := by
  have hp : Measurable (profile u) := measurable_profile u
  have h1 : Measurable (fun p : (Fin r → ℝ) × (Fin r → ℝ) => conj (∏ j, profile u (p.1 j))) :=
    Complex.continuous_conj.measurable.comp (Finset.measurable_prod _ (fun j _ => hp.comp ((measurable_pi_apply j).comp measurable_fst)))
  have h2 : Measurable (fun p : (Fin r → ℝ) × (Fin r → ℝ) => ∏ j, profile u (p.2 j)) :=
    Finset.measurable_prod _ (fun j _ => hp.comp ((measurable_pi_apply j).comp measurable_snd))
  exact (h1.mul (measurable_rawMinus r L z)).mul h2

theorem supp_of_plusOrder {a b : Fin r → ℝ} (h : PlusOrder L a b) (j : Fin r) :
    a j ∈ Ioo (0 : ℝ) L ∧ b j ∈ Ioo (0 : ℝ) L := by
  obtain ⟨h1, h2, h3⟩ := h.1 j
  exact ⟨⟨h1.trans h2, h3⟩, ⟨h1, h2.trans h3⟩⟩

theorem supp_PsiP : ∀ a b, PsiP z u r a b ≠ 0 → ∀ j, a j ∈ Ioo (0 : ℝ) L ∧ b j ∈ Ioo (0 : ℝ) L := by
  classical
  intro a b h j
  by_cases hP : PlusOrder L a b
  · exact supp_of_plusOrder r hP j
  · exfalso; apply h
    simp [PsiP, rawPlus, hP]

theorem supp_PsiM : ∀ a b, PsiM z u r a b ≠ 0 → ∀ j, a j ∈ Ioo (0 : ℝ) L ∧ b j ∈ Ioo (0 : ℝ) L := by
  classical
  intro a b h j
  by_cases hP : PlusOrder L b a
  · exact (supp_of_plusOrder r hP j).symm
  · exfalso; apply h
    simp [PsiM, rawMinus, QuantumNLS.BetheTransferKernelAdjoint.MinusOrder, hP]

theorem PsiP_eq_Phi (a b : Fin r → ℝ) :
    PsiP z u r a b = Phi (fun s => conj (profile u s)) (profile u) z r L
      (fun j => (a j, b j)) := by
  classical
  unfold PsiP Phi rawPlus
  by_cases hP : PlusOrder L a b
  · simp only [hP, ↓reduceIte, one_mul]
    rw [show (Complex.exp (Complex.I * z * (displacement a b : ℝ))) =
        ∏ j, Complex.exp (Complex.I * z * ((a j - b j : ℝ) : ℂ)) by
      rw [← Complex.exp_sum]; congr 1; simp only [displacement, Complex.ofReal_sum, Finset.mul_sum]]
    rw [map_prod]
    simp only [Finset.prod_mul_distrib]
    ring
  · simp [hP]

theorem PsiM_swap_eq_Phi (a b : Fin r → ℝ) :
    PsiM z u r b a = Complex.exp (Complex.I * z * L) * Phi (profile u) (fun s => conj (profile u s)) (-z) r L
      (fun j => (a j, b j)) := by
  classical
  unfold PsiM Phi rawMinus QuantumNLS.BetheTransferKernelAdjoint.MinusOrder
  by_cases hP : PlusOrder L a b
  · simp only [hP, ↓reduceIte, one_mul]
    have hsum : ∑ j, Complex.I * (-z) * ((a j - b j : ℝ) : ℂ) =
        -(Complex.I * z * ((∑ j, (a j - b j) : ℝ) : ℂ)) := by
      push_cast
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have hs : Complex.exp (Complex.I * z * L - Complex.I * z * ((∑ j, (a j - b j) : ℝ) : ℂ)) =
        Complex.exp (Complex.I * z * L) * ∏ j, Complex.exp (Complex.I * (-z) * ((a j - b j : ℝ) : ℂ)) := by
      rw [← Complex.exp_sum, ← Complex.exp_add, hsum]; congr 1; try ring
    rw [hs, map_prod]
    simp only [Finset.prod_mul_distrib]
    ring
  · simp [hP]

end Parts

section Assembly

theorem hfi_conj (u : L2T L) : IntervalIntegrable (fun s => conj (profile u s)) volume 0 L := by
  have h := intervalIntegrable_profile u
  exact ⟨Complex.conjCLE.toContinuousLinearMap.integrable_comp h.1,
    Complex.conjCLE.toContinuousLinearMap.integrable_comp h.2⟩

theorem hfm_conj (u : L2T L) : Measurable (fun s => conj (profile u s)) :=
  Complex.continuous_conj.measurable.comp (measurable_profile u)

theorem form_plus (u : L2T L) (r : ℕ) (z : ℂ) :
    (plusKernel L r z).form (prodLp (fun _ : Fin r => u)) (prodLp (fun _ : Fin r => u)) =
      Wr (fun s => conj (profile u s)) (profile u) z r L := by
  rw [form_eq_pair u r (plusKernel L r z) (rawPlus L z) (fun p => rfl)]
  have hmain := torus_pair_integral (L := L) (PsiP z u r) (measurable_PsiP z u r) (supp_PsiP z u r)
  have e : (fun p : (Fin r → AddCircle L) × (Fin r → AddCircle L) =>
      conj (∏ j, profile u (representatives L p.1 j)) * rawPlus L z (representatives L p.1) (representatives L p.2) *
        ∏ j, profile u (representatives L p.2 j)) =
      fun p => PsiP z u r (representatives L p.1) (representatives L p.2) := rfl
  rw [e, hmain]
  have e2 : ∀ q : Fin r → ℝ × ℝ, PsiP z u r (fun j => (q j).1) (fun j => (q j).2) =
      Phi (fun s => conj (profile u s)) (profile u) z r L q := fun q => PsiP_eq_Phi z u r _ _
  simp_rw [e2]
  exact Theta_eq_Wr (hfm_conj u) (measurable_profile u) (hfi_conj u) (intervalIntegrable_profile u)
    (Fact.out : 0 < L).le r L (Fact.out : 0 < L).le le_rfl

theorem measurable_PsiM_swap (u : L2T L) (r : ℕ) (z : ℂ) :
    Measurable (fun p : (Fin r → ℝ) × (Fin r → ℝ) => PsiM z u r p.2 p.1) := by
  have hp : Measurable (profile u) := measurable_profile u
  have h1 : Measurable (fun p : (Fin r → ℝ) × (Fin r → ℝ) => conj (∏ j, profile u (p.2 j))) :=
    Complex.continuous_conj.measurable.comp (Finset.measurable_prod _ (fun j _ => hp.comp ((measurable_pi_apply j).comp measurable_snd)))
  have h2 : Measurable (fun p : (Fin r → ℝ) × (Fin r → ℝ) => ∏ j, profile u (p.1 j)) :=
    Finset.measurable_prod _ (fun j _ => hp.comp ((measurable_pi_apply j).comp measurable_fst))
  have h3 : Measurable (fun p : (Fin r → ℝ) × (Fin r → ℝ) => rawMinus L z p.2 p.1) := by
    have := measurable_rawMinus r L z
    have hs : Measurable (fun p : (Fin r → ℝ) × (Fin r → ℝ) => (p.2, p.1)) := measurable_snd.prodMk measurable_fst
    exact this.comp hs
  exact (h1.mul h3).mul h2

theorem torus_PsiM (u : L2T L) (r : ℕ) (z : ℂ) :
    ∫ p : (Fin r → AddCircle L) × (Fin r → AddCircle L),
      PsiM z u r (representatives L p.2) (representatives L p.1)
        ∂((torusPiMeasure L r).prod (torusPiMeasure L r)) =
      ∫ q : Fin r → ℝ × ℝ, PsiM z u r (fun j => (q j).2) (fun j => (q j).1) :=
  torus_pair_integral (L := L) (fun a b => PsiM z u r b a) (measurable_PsiM_swap u r z)
    (fun a b h j => (supp_PsiM z u r b a h j).symm)

theorem swap_PsiM (u : L2T L) (r : ℕ) (z : ℂ) :
    ∫ p : (Fin r → AddCircle L) × (Fin r → AddCircle L),
      PsiM z u r (representatives L p.1) (representatives L p.2)
        ∂((torusPiMeasure L r).prod (torusPiMeasure L r)) =
    ∫ p : (Fin r → AddCircle L) × (Fin r → AddCircle L),
      PsiM z u r (representatives L p.2) (representatives L p.1)
        ∂((torusPiMeasure L r).prod (torusPiMeasure L r)) :=
  (integral_prod_swap (μ := torusPiMeasure L r) (ν := torusPiMeasure L r)
    (fun p : (Fin r → AddCircle L) × (Fin r → AddCircle L) =>
      PsiM z u r (representatives L p.1) (representatives L p.2))).symm

theorem form_minus (u : L2T L) (r : ℕ) (z : ℂ) :
    (minusKernel L r z).form (prodLp (fun _ : Fin r => u)) (prodLp (fun _ : Fin r => u)) =
      Complex.exp (Complex.I * z * L) * Wr (profile u) (fun s => conj (profile u s)) (-z) r L := by
  rw [form_eq_pair u r (minusKernel L r z) (rawMinus L z) (fun p => rfl)]
  have e : (fun p : (Fin r → AddCircle L) × (Fin r → AddCircle L) =>
      conj (∏ j, profile u (representatives L p.1 j)) * rawMinus L z (representatives L p.1) (representatives L p.2) *
        ∏ j, profile u (representatives L p.2 j)) =
      fun p => PsiM z u r (representatives L p.1) (representatives L p.2) := rfl
  rw [e, swap_PsiM u r z, torus_PsiM u r z]
  have e2 : ∀ q : Fin r → ℝ × ℝ, PsiM z u r (fun j => (q j).2) (fun j => (q j).1) =
      Complex.exp (Complex.I * z * L) * Phi (profile u) (fun s => conj (profile u s)) (-z) r L q :=
    fun q => PsiM_swap_eq_Phi z u r _ _
  simp_rw [e2]
  rw [integral_const_mul]
  congr 1
  exact Theta_eq_Wr (measurable_profile u) (hfm_conj u) (intervalIntegrable_profile u) (hfi_conj u)
    (Fact.out : 0 < L).le r L (Fact.out : 0 < L).le le_rfl

open QuantumNLS.TensorCarrier in
theorem kps_eq (r : ℕ) (z : ℂ) (u : L2T L) :
    QuantumNLS.KernelDefinition.kernelProductSymbol (QuantumNLS.NormalizedTransfer.orderedKernel L r z) u =
      Wr (fun s => conj (profile u s)) (profile u) z r L +
        Complex.exp (Complex.I * z * L) * Wr (profile u) (fun s => conj (profile u s)) (-z) r L := by
  have h0 : QuantumNLS.KernelDefinition.kernelProductSymbol (QuantumNLS.NormalizedTransfer.orderedKernel L r z) u =
      ⟪(⟨QuantumNLS.TensorCarrier.htpow r u, htpow_mem_symSector r u⟩ : SymSector ℂ (L2T L) r),
        QuantumNLS.BethePhysicalTransfer.physicalKernel L r z
          ⟨QuantumNLS.TensorCarrier.htpow r u, htpow_mem_symSector r u⟩⟫_ℂ := rfl
  rw [h0, QuantumNLS.BethePhysicalTransfer.inner_physicalKernel]
  have hpos : QuantumNLS.BethePhysicalTransfer.positionInclusion L r
      (⟨QuantumNLS.TensorCarrier.htpow r u, htpow_mem_symSector r u⟩ : SymSector ℂ (L2T L) r) =
        prodLp (fun _ : Fin r => u) :=
    QuantumNLS.PhysicalTensor.physEmbed_htpow u
  rw [hpos]
  have hraw : rawOperator L r z (prodLp (fun _ : Fin r => u)) =
      (plusKernel L r z).operator (prodLp (fun _ : Fin r => u)) +
        (minusKernel L r z).operator (prodLp (fun _ : Fin r => u)) := rfl
  rw [hraw, inner_add_right, QuantumNLS.BetheIntegralOperator.Kernel.inner_operator,
    QuantumNLS.BetheIntegralOperator.Kernel.inner_operator, form_plus, form_minus]

end Assembly

#print axioms QuantumNLS.RootTraceSymbolQuantum.prod_ae
#print axioms QuantumNLS.RootTraceSymbolQuantum.form_eq_pair
#print axioms QuantumNLS.RootTraceSymbolQuantum.PsiP_eq_Phi
#print axioms QuantumNLS.RootTraceSymbolQuantum.PsiM_swap_eq_Phi
#print axioms QuantumNLS.RootTraceSymbolQuantum.kps_eq
