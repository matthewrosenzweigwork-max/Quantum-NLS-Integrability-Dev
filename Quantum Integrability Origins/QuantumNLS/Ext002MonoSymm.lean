import Mathlib
import QuantumNLS.Ext002MonoSlice

/-!
# EXT-002 / V-01 full monodromy (owner decision D4), stage M4b: symmetrization

A04.tex:92-95: "For almost every `w`, the functions `F(·,w)` and `G(·,w)` are symmetric in
their first `r` variables. Hence `Ã` can be replaced by `P_r Ã P_r = A` in the matrix element."

Here: for `F, G` in the physical symmetric sector `H_{m+q}` and any bounded kernel `k`, the weak
matrix element of the slice operator of `k` equals that of its doubly averaged kernel
(`inner_sliceOp_avg`). The proof is the change of variables `x ↦ x∘σ`, `y ↦ y∘τ` on the
mass-preserving product torus and the permutation invariance of symmetric wave functions.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate InnerProductSpace

namespace QuantumNLS.Ext002MonoSymm
open PhysicalTensor TensorCarrier BethePhysicalTransfer BetheIntegralOperator
open Ext002MonoLift Ext002MonoFields Ext002MonoSlice

variable (L : ℝ) [Fact (0 < L)]

/-- Integrability of every weak matrix-element integrand with a bounded multiplier. -/
theorem integrable_form {r s q : ℕ} (F : L2TN L (r+q)) (G : L2TN L (s+q))
    (φ : Trip L r s q → ℂ) (hφ : Measurable φ) (C : ℝ) (hb : ∀ p, ‖φ p‖ ≤ C) :
    Integrable (fun p => conj (F (outPt L p)) * φ p * G (inPt L p)) (tripMeasure L r s q) := by
  refine (L2.integrable_inner (𝕜 := ℂ) (liftOut L r s q F)
    (mulOp (μ := tripMeasure L r s q) φ hφ C hb (liftIn L r s q G))).congr ?_
  filter_upwards [coeFn_liftOut L r s q F,
    coeFn_mulOp (μ := tripMeasure L r s q) φ hφ C hb (liftIn L r s q G),
    coeFn_liftIn L r s q G] with p h1 h2 h3
  rw [RCLike.inner_apply', h1, h2, h3]
  ring

/-- Block permutation `σ ⊕ id` of `Fin (m+q)`. -/
def blockPerm {m q : ℕ} (σ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m+q)) :=
  finSumFinEquiv.permCongr (Equiv.sumCongr σ (Equiv.refl (Fin q)))

theorem coordPerm_blockPerm {m q : ℕ} (σ : Equiv.Perm (Fin m)) (x : Fin m → AddCircle L)
    (w : Fin q → AddCircle L) :
    coordPerm (blockPerm σ) (Fin.append x w) = Fin.append (coordPerm σ x) w := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [coordPerm_apply, blockPerm, Equiv.permCongr_apply, finSumFinEquiv_symm_apply_castAdd,
      Fin.append_left]
  · simp [coordPerm_apply, blockPerm, Equiv.permCongr_apply, finSumFinEquiv_symm_apply_natAdd,
      Fin.append_right]

/-- A permutation-invariant position wave function is a.e. invariant pointwise. -/
theorem sym_ae {n : ℕ} (F : L2TN L n) (hF : ∀ π : Equiv.Perm (Fin n), physPerm π F = F)
    (π : Equiv.Perm (Fin n)) :
    ∀ᵐ u ∂torusPiMeasure L n, F (coordPerm π u) = F u := by
  filter_upwards [coeFn_physPerm π F] with u hu
  rw [hF π] at hu
  exact hu.symm

/-- The coordinate change `((x,w),y) ↦ ((x∘σ,w), y∘τ)` of the triple space. -/
def tripPerm {m q : ℕ} (σ τ : Equiv.Perm (Fin m)) : Trip L m m q ≃ᵐ Trip L m m q :=
  MeasurableEquiv.prodCongr (MeasurableEquiv.prodCongr (coordPerm σ) (MeasurableEquiv.refl _))
    (coordPerm τ)

theorem measurePreserving_tripPerm {m q : ℕ} (σ τ : Equiv.Perm (Fin m)) :
    MeasurePreserving (tripPerm L (q := q) σ τ) (tripMeasure L m m q) (tripMeasure L m m q) :=
  ((measurePreserving_coordPerm σ).prod (MeasurePreserving.id _)).prod
    (measurePreserving_coordPerm τ)

/-- Permuting the creation and annihilation variables of the kernel does not change the
matrix element between symmetric wave functions. -/
theorem form_perm {m q : ℕ} (k : Kernel (torusPiMeasure L m)) (F G : L2TN L (m+q))
    (hF : ∀ π : Equiv.Perm (Fin (m+q)), physPerm π F = F)
    (hG : ∀ π : Equiv.Perm (Fin (m+q)), physPerm π G = G) (σ τ : Equiv.Perm (Fin m)) :
    ∫ p, conj (F (outPt L p)) * k.fn (coordPerm σ p.1.1, coordPerm τ p.2) * G (inPt L p)
        ∂tripMeasure L m m q =
      ∫ p, conj (F (outPt L p)) * k.fn (p.1.1, p.2) * G (inPt L p) ∂tripMeasure L m m q := by
  rw [← (measurePreserving_tripPerm L (q := q) σ τ).integral_comp'
    (fun p => conj (F (outPt L p)) * k.fn (p.1.1, p.2) * G (inPt L p))]
  have hFs := (qmp_outPt L m m q).ae (sym_ae L F hF (blockPerm σ))
  have hGs := (qmp_inPt L m m q).ae (sym_ae L G hG (blockPerm τ))
  apply integral_congr_ae
  filter_upwards [hFs, hGs] with p h1 h2
  have e1 : outPt L (tripPerm L (q := q) σ τ p) = coordPerm (blockPerm σ) (outPt L p) := by
    simp only [outPt, coordPerm_blockPerm]
    rfl
  have e2 : inPt L (tripPerm L (q := q) σ τ p) = coordPerm (blockPerm τ) (inPt L p) := by
    simp only [inPt, coordPerm_blockPerm]
    rfl
  have e3 : (tripPerm L (q := q) σ τ p).1.1 = coordPerm σ p.1.1 := rfl
  have e4 : (tripPerm L (q := q) σ τ p).2 = coordPerm τ p.2 := rfl
  show conj (F (outPt L p)) * k.fn (coordPerm σ p.1.1, coordPerm τ p.2) * G (inPt L p) =
    conj (F (outPt L (tripPerm L (q := q) σ τ p))) *
      k.fn ((tripPerm L (q := q) σ τ p).1.1, (tripPerm L (q := q) σ τ p).2) *
        G (inPt L (tripPerm L (q := q) σ τ p))
  rw [e1, e2, h1, h2, e3, e4]

theorem avgKernel_fn {m : ℕ} (k : Kernel (torusPiMeasure L m))
    (p : (Fin m → AddCircle L) × (Fin m → AddCircle L)) :
    (avgKernel L k).fn p = ∑ σ : Equiv.Perm (Fin m), ((m.factorial : ℂ)⁻¹ *
      ∑ τ : Equiv.Perm (Fin m), ((m.factorial : ℂ)⁻¹ * k.fn (coordPerm σ p.1, coordPerm τ.symm p.2))) := by
  simp only [avgKernel, BetheCompressedKernel.outputAverage, BetheCompressedKernel.inputAverage,
    BetheCompressedKernel.weightedKernel, BetheCompressedKernel.permutedKernel]
  rfl

/-- **A04.tex:92-95.** Between symmetric wave functions, `Ã` and its double average have the
same weak matrix elements. -/
theorem inner_sliceOp_avg {m : ℕ} (q : ℕ) (k : Kernel (torusPiMeasure L m))
    (F G : SymSector ℂ (L2T L) (m+q)) :
    ⟪positionInclusion L (m+q) F,
        sliceOp L q (ofKernel L (avgKernel L k)) (positionInclusion L (m+q) G)⟫_ℂ =
      ⟪positionInclusion L (m+q) F,
        sliceOp L q (ofKernel L k) (positionInclusion L (m+q) G)⟫_ℂ := by
  set Fh := positionInclusion L (m+q) F with hFh
  set Gh := positionInclusion L (m+q) G with hGh
  have hF : ∀ π : Equiv.Perm (Fin (m+q)), physPerm π Fh = Fh :=
    (mem_physSector_iff (F : HilbertTensorPower ℂ (L2T L) (m+q))).mp F.property
  have hG : ∀ π : Equiv.Perm (Fin (m+q)), physPerm π Gh = Gh :=
    (mem_physSector_iff (G : HilbertTensorPower ℂ (L2T L) (m+q))).mp G.property
  have hmeas : ∀ σ τ : Equiv.Perm (Fin m), Measurable (fun p : Trip L m m q =>
      k.fn (coordPerm σ p.1.1, coordPerm τ.symm p.2)) := fun σ τ =>
    k.measurable.comp (((coordPerm σ).measurable.comp (measurable_fst.comp measurable_fst)).prodMk
      ((coordPerm τ.symm).measurable.comp measurable_snd))
  have hint : ∀ σ τ : Equiv.Perm (Fin m), Integrable (fun p : Trip L m m q =>
      conj (Fh (outPt L p)) * k.fn (coordPerm σ p.1.1, coordPerm τ.symm p.2) * Gh (inPt L p))
      (tripMeasure L m m q) := fun σ τ =>
    integrable_form L Fh Gh _ (hmeas σ τ) k.bound (fun p => k.norm_le _)
  rw [inner_sliceOp, inner_sliceOp]
  calc ∫ p, conj (Fh (outPt L p)) * (ofKernel L (avgKernel L k)).fn (p.1.1, p.2) * Gh (inPt L p)
          ∂tripMeasure L m m q
      = ∫ p, ∑ σ : Equiv.Perm (Fin m), ((m.factorial : ℂ)⁻¹ * ∑ τ : Equiv.Perm (Fin m),
          ((m.factorial : ℂ)⁻¹ * (conj (Fh (outPt L p)) *
            k.fn (coordPerm σ p.1.1, coordPerm τ.symm p.2) * Gh (inPt L p))))
          ∂tripMeasure L m m q := by
        apply integral_congr_ae
        filter_upwards with p
        change conj (Fh (outPt L p)) * (avgKernel L k).fn (p.1.1, p.2) * Gh (inPt L p) = _
        rw [avgKernel_fn]
        simp only [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro σ _
        apply Finset.sum_congr rfl
        intro τ _
        ring
    _ = ∑ σ : Equiv.Perm (Fin m), ((m.factorial : ℂ)⁻¹ * ∑ τ : Equiv.Perm (Fin m),
          ((m.factorial : ℂ)⁻¹ * ∫ p, conj (Fh (outPt L p)) *
            k.fn (coordPerm σ p.1.1, coordPerm τ.symm p.2) * Gh (inPt L p)
              ∂tripMeasure L m m q)) := by
        rw [integral_finset_sum _ (fun σ _ => (integrable_finset_sum _
          (fun τ _ => (hint σ τ).const_mul _)).const_mul _)]
        apply Finset.sum_congr rfl
        intro σ _
        rw [integral_const_mul, integral_finset_sum _ (fun τ _ => (hint σ τ).const_mul _)]
        congr 1
        apply Finset.sum_congr rfl
        intro τ _
        rw [integral_const_mul]
    _ = ∑ σ : Equiv.Perm (Fin m), ((m.factorial : ℂ)⁻¹ * ∑ τ : Equiv.Perm (Fin m),
          ((m.factorial : ℂ)⁻¹ * ∫ p, conj (Fh (outPt L p)) * k.fn (p.1.1, p.2) * Gh (inPt L p)
              ∂tripMeasure L m m q)) := by
        apply Finset.sum_congr rfl
        intro σ _
        congr 1
        apply Finset.sum_congr rfl
        intro τ _
        rw [form_perm L k Fh Gh hF hG σ τ.symm]
    _ = ∫ p, conj (Fh (outPt L p)) * (ofKernel L k).fn (p.1.1, p.2) * Gh (inPt L p)
          ∂tripMeasure L m m q := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
          nsmul_eq_mul]
        have hm : ((m.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
        rw [mul_inv_cancel_left₀ hm, mul_inv_cancel_left₀ hm]
        rfl

end QuantumNLS.Ext002MonoSymm

#print axioms QuantumNLS.Ext002MonoSymm.integrable_form
#print axioms QuantumNLS.Ext002MonoSymm.coordPerm_blockPerm
#print axioms QuantumNLS.Ext002MonoSymm.form_perm
#print axioms QuantumNLS.Ext002MonoSymm.avgKernel_fn
#print axioms QuantumNLS.Ext002MonoSymm.inner_sliceOp_avg
