import QuantumNLS.Prop025OMain
import QuantumNLS.BornTranslation
import QuantumNLS.TensorFourier
import QuantumNLS.IntrinsicContact
import QuantumNLS.TraceIdeal
import QuantumNLS.TraceCompact
import QuantumNLS.R52CFEvol
import QuantumNLS.RB7BindFinal

/-! PROP-025 (thm:MP-mixed, mixed_propagation.tex sha256 24ab083b...), stage O6b:
**orders zero and one** ("Orders zero and one may also be included, with their exact common-phase and translation
flows", source line 89, inside the theorem) and **the headline in the consumer form
`ActualModelCorollaryR56a.PROP025Input`**.

Quantum side: `Q_{N,0} = N+1` (`eigenvalue_zero`), so `exp(−i t_0 Q_{N,0})` is a global phase; `Q_{N,1} = Σ_j q_j`, and
`exp(−i s Q_{N,1})` is the diagonal translation `τ_{−s}^{⊗(N+1)}`: every actual Bethe vector is an eigenvector of the
diagonal translation with eigenvalue `e^{i a Σ_j q_j}` (accepted `BornTranslation.transN_wave` with the accepted
`physicalBasis_position`).  Classical side: the R53a flows of orders `0, 1` are `phaseFlow`, `transFlow`, and the
joint flow is `phase ∘ translation ∘ (joint flow of the orders ≥ 2)`.  The marginal of a translated vector is the
conjugated marginal, the translated projector is the conjugated projector, and the trace norm does not increase
under conjugation by a contraction; so each orders-`R` term is bounded by the orders-`R ∩ [2,∞)` term, and the
largest order `d = max(2, max R)` is unchanged.

* `trans_add`, `trans_zero`, `transE`: the translation unitary;
* `prodLp_trans`, `phys_tensorPower`: `τ_a^{⊗n}` on the completed tensor power is the coordinate translation;
* `tensorPower_basis`, `evolution_translate`, `evolution_const`, `chargeUnitary_split`: the low charges;
* `rd_htmap`, `rdN_tensorPower`, `tensorProj_map`, `tensorProj_smul`, `traceNorm_conj_le`: covariance;
* `sort_split`, `joint_split`, `physical_low`, `target_split`: the classical low flows;
* `box_low`, `d_low`, **`prop025`** (the headline, all finite `R ⊆ ℕ`, all ranks), **`prop025_actual`**.
No hypothesis is added beyond the named inputs; all inherited modules are read-only.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open scoped Topology NNReal ENNReal InnerProductSpace ComplexConjugate
open MeasureTheory Filter Set

namespace QuantumNLS.Prop025OLow
open QuantumNLS.PhysicalTensor (L2T L2TN prodLp prodFun memLp_prodFun torusPiMeasure physUnitary physUnitary_ptprod)
open QuantumNLS.TensorCarrier (HilbertTensorPower HilbertTensor htpow ptprod AlgTensorPower reducedDensity
  reducedDensityPower htmap htmap_comp adjoint_htmap inner_reducedDensity_left SymSector)
open QuantumNLS.TensorFourier (tensorPower tensorPower_ptprod tensorPower_htpow tensorPower_split tensorPower_trans
  tensorPower_refl tensorPower_mem_symSector_iff)
open QuantumNLS.BornTranslation (trans transN coeFn_trans coeFn_transN measurePreserving_shift)
open QuantumNLS.TraceClass (traceNorm)
open QuantumNLS.BetheLabels (MArr)
open QuantumNLS.BetheCoefficientTransform (HN)
open QuantumNLS.BetheSpectralCharges (evolution evolution_coord eigenvalue)
open QuantumNLS.Def033HierarchyR24m (Smooth physical jointSmooth)
open QuantumNLS.HierarchyFlow (jointClassicalFlow)
open QuantumNLS.Def024LowFlows (phaseFlow transFlow)
open QuantumNLS.ActualModelTargetR53a (HigherFlows hamFlows flowMap higher target)
open QuantumNLS.ActualModelCorollaryR53a (MainEstimate boxError)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-! ### 1. Covariance of marginals, projectors and the trace norm -/

section Generic
variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

theorem adj_rankOne_comp (U : X →L[ℂ] X) (a b : X) :
    ContinuousLinearMap.adjoint U ∘L InnerProductSpace.rankOne ℂ a b ∘L U =
      InnerProductSpace.rankOne ℂ (ContinuousLinearMap.adjoint U a) (ContinuousLinearMap.adjoint U b) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, InnerProductSpace.rankOne_apply, map_smul,
    ContinuousLinearMap.adjoint_inner_left]

/-- The reduced density of `(U ⊗̂ V) ψ` with `V† V = 1` is `U ρ U†`. -/
theorem rd_htmap (U : X →L[ℂ] X) (V : Y →L[ℂ] Y)
    (hV : ContinuousLinearMap.adjoint V ∘L V = ContinuousLinearMap.id ℂ Y) (ψ : HilbertTensor ℂ X Y) :
    reducedDensity (htmap U V ψ) = U ∘L reducedDensity ψ ∘L ContinuousLinearMap.adjoint U := by
  ext φ
  refine ext_inner_right ℂ fun φ' => ?_
  have hL : ⟪htmap U V ψ, htmap (InnerProductSpace.rankOne ℂ φ' φ) (ContinuousLinearMap.id ℂ Y) (htmap U V ψ)⟫_ℂ =
      ⟪ψ, htmap (InnerProductSpace.rankOne ℂ (ContinuousLinearMap.adjoint U φ') (ContinuousLinearMap.adjoint U φ))
        (ContinuousLinearMap.id ℂ Y) ψ⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, adjoint_htmap]
    have e : htmap (ContinuousLinearMap.adjoint U) (ContinuousLinearMap.adjoint V)
        (htmap (InnerProductSpace.rankOne ℂ φ' φ) (ContinuousLinearMap.id ℂ Y) (htmap U V ψ)) =
        htmap (ContinuousLinearMap.adjoint U ∘L InnerProductSpace.rankOne ℂ φ' φ ∘L U)
          (ContinuousLinearMap.adjoint V ∘L ContinuousLinearMap.id ℂ Y ∘L V) ψ := by
      rw [htmap_comp, htmap_comp]
      rfl
    rw [e, adj_rankOne_comp, ContinuousLinearMap.id_comp, hV]
  rw [inner_reducedDensity_left, hL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.adjoint_inner_right U, inner_reducedDensity_left]

/-- An isometric equivalence satisfies `U† U = 1`. -/
theorem adj_comp_self (e : X ≃ₗᵢ[ℂ] X) :
    ContinuousLinearMap.adjoint e.toContinuousLinearEquiv.toContinuousLinearMap ∘L
      e.toContinuousLinearEquiv.toContinuousLinearMap = ContinuousLinearMap.id ℂ X := by
  ext y
  refine ext_inner_left ℂ fun z => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.id_apply]
  exact e.inner_map_map z y

theorem norm_clm_le (e : X ≃ₗᵢ[ℂ] X) : ‖e.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => le_of_eq (by rw [one_mul]; exact e.norm_map x)

/-- The trace norm does not increase under conjugation by a contraction. -/
theorem traceNorm_conj_le (U : X →L[ℂ] X) (hU : ‖U‖ ≤ 1) (A : X →L[ℂ] X) :
    traceNorm (U ∘L A ∘L ContinuousLinearMap.adjoint U) ≤ traceNorm A := by
  have h1 := TraceCompact.traceNorm_mul_left_le U (A * ContinuousLinearMap.adjoint U)
  have h2 := TraceIdeal.traceNorm_mul_right_le A (ContinuousLinearMap.adjoint U)
  have hU' : ‖ContinuousLinearMap.adjoint U‖ ≤ 1 := by
    rw [LinearIsometryEquiv.norm_map]; exact hU
  have e1 : ENNReal.ofReal ‖U‖ ≤ 1 := ENNReal.ofReal_le_one.2 hU
  have e2 : ENNReal.ofReal ‖ContinuousLinearMap.adjoint U‖ ≤ 1 := ENNReal.ofReal_le_one.2 hU'
  calc traceNorm (U ∘L A ∘L ContinuousLinearMap.adjoint U) = traceNorm (U * (A * ContinuousLinearMap.adjoint U)) :=
        rfl
    _ ≤ ENNReal.ofReal ‖U‖ * traceNorm (A * ContinuousLinearMap.adjoint U) := h1
    _ ≤ 1 * (traceNorm A * 1) := mul_le_mul' e1 (h2.trans (mul_le_mul' le_rfl e2))
    _ = traceNorm A := by rw [one_mul, mul_one]

end Generic

/-- The reduced density of a transported vector. -/
theorem rdPower_tensorPower (e : L2T L ≃ₗᵢ[ℂ] L2T L) (k m : ℕ) (x : HilbertTensorPower ℂ (L2T L) (k + m)) :
    reducedDensityPower k m (tensorPower e (k + m) x) =
      (tensorPower e k).toContinuousLinearEquiv.toContinuousLinearMap ∘L reducedDensityPower k m x ∘L
        ContinuousLinearMap.adjoint (tensorPower e k).toContinuousLinearEquiv.toContinuousLinearMap := by
  unfold reducedDensityPower
  rw [tensorPower_split, rd_htmap _ _ (adj_comp_self (tensorPower e m))]

theorem castHTP_tensorPower (e : L2T L ≃ₗᵢ[ℂ] L2T L) {n m : ℕ} (h : n = m) (x : HilbertTensorPower ℂ (L2T L) n) :
    PhysicalTensor.castHTP h (tensorPower e n x) = tensorPower e m (PhysicalTensor.castHTP h x) := by
  subst h; rfl

theorem rdN_tensorPower (e : L2T L ≃ₗᵢ[ℂ] L2T L) (N k : ℕ) (hk : k ≤ N) (x : HilbertTensorPower ℂ (L2T L) N) :
    PhysicalTensor.reducedDensityN N k hk (tensorPower e N x) =
      (tensorPower e k).toContinuousLinearEquiv.toContinuousLinearMap ∘L PhysicalTensor.reducedDensityN N k hk x ∘L
        ContinuousLinearMap.adjoint (tensorPower e k).toContinuousLinearEquiv.toContinuousLinearMap := by
  unfold PhysicalTensor.reducedDensityN
  rw [castHTP_tensorPower, rdPower_tensorPower]

/-- The transported projector. -/
theorem tensorProj_map (e : L2T L ≃ₗᵢ[ℂ] L2T L) (k : ℕ) (v : L2T L) :
    Prop025OInputs.tensorProj k (e v) =
      (tensorPower e k).toContinuousLinearEquiv.toContinuousLinearMap ∘L Prop025OInputs.tensorProj k v ∘L
        ContinuousLinearMap.adjoint (tensorPower e k).toContinuousLinearEquiv.toContinuousLinearMap := by
  unfold Prop025OInputs.tensorProj
  rw [← tensorPower_htpow]
  ext y
  simp only [ContinuousLinearMap.comp_apply, InnerProductSpace.rankOne_apply, map_smul]
  rw [ContinuousLinearMap.adjoint_inner_right]
  rfl

/-- The projector is phase invariant. -/
theorem tensorProj_smul (k : ℕ) (c : ℂ) (hc : ‖c‖ = 1) (v : L2T L) :
    Prop025OInputs.tensorProj k (c • v) = Prop025OInputs.tensorProj k v := by
  unfold Prop025OInputs.tensorProj
  rw [IntrinsicContact.htpow_smul]
  have hck : (starRingEnd ℂ) (c ^ k) * c ^ k = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow, hc, one_pow]
    norm_num
  ext y
  simp only [InnerProductSpace.rankOne_apply, inner_smul_left, smul_smul]
  congr 1
  linear_combination (⟪(htpow k v : HilbertTensorPower ℂ (L2T L) k), y⟫_ℂ) * hck

/-! ### 2. The translation unitary and the order-one charge -/

theorem trans_add (a b : ℝ) (u : L2T L) : trans a (trans b u) = trans (a + b) u := by
  apply Lp.ext
  have h2 := (measurePreserving_add_right (volume : Measure (AddCircle L)) (a : AddCircle L)).quasiMeasurePreserving.ae
    (coeFn_trans (L := L) b u)
  filter_upwards [coeFn_trans a (trans b u), h2, coeFn_trans (a + b) u] with x h1 h2' h3
  rw [h1, h2', h3, AddCircle.coe_add, add_assoc]

theorem trans_zero (u : L2T L) : trans 0 u = u := by
  apply Lp.ext
  filter_upwards [coeFn_trans (L := L) 0 u] with x h
  rw [h, AddCircle.coe_zero, add_zero]

/-- The translation `τ_a` as a unitary. -/
def transE (a : ℝ) : L2T L ≃ₗᵢ[ℂ] L2T L :=
  LinearIsometryEquiv.ofSurjective (trans a) (fun v => ⟨trans (-a) v, by rw [trans_add, add_neg_cancel, trans_zero]⟩)

theorem transE_apply (a : ℝ) (u : L2T L) : transE a u = trans a u := rfl

theorem transE_inv (s : ℝ) : (transE (L := L) (-s)).trans (transE s) = LinearIsometryEquiv.refl ℂ (L2T L) := by
  refine LinearIsometryEquiv.ext fun u => ?_
  show trans s (trans (-s) u) = u
  rw [trans_add, add_neg_cancel, trans_zero]

/-- `(τ_a f_1) ⊗ ⋯ ⊗ (τ_a f_n) = τ_a^{⊗n}(f_1 ⊗ ⋯ ⊗ f_n)` in coordinates. -/
theorem prodLp_trans {n : ℕ} (a : ℝ) (f : Fin n → L2T L) :
    prodLp (fun j => trans a (f j)) = transN n a (prodLp f) := by
  apply Lp.ext
  have hA3 := (measurePreserving_shift (L := L) n a).quasiMeasurePreserving.ae ((memLp_prodFun f).coeFn_toLp)
  have hA4 : ∀ᵐ y ∂(torusPiMeasure L n), ∀ j : Fin n,
      (trans a (f j) : AddCircle L → ℂ) (y j) = f j (y j + (a : AddCircle L)) :=
    ae_all_iff.2 (fun j => (Measure.quasiMeasurePreserving_eval (fun _ => (volume : Measure (AddCircle L))) j).ae
      (coeFn_trans a (f j)))
  filter_upwards [(memLp_prodFun (fun j => trans a (f j))).coeFn_toLp, coeFn_transN n a (prodLp f), hA3, hA4]
    with y h1 h2 h3 h4
  rw [h2]
  change (prodLp (fun j => trans a (f j)) : (Fin n → AddCircle L) → ℂ) y = _
  have h1' : (prodLp (fun j => trans a (f j)) : (Fin n → AddCircle L) → ℂ) y =
      prodFun (fun j => trans a (f j)) y := h1
  have h3' : (prodLp f : (Fin n → AddCircle L) → ℂ) (fun j => y j + (a : AddCircle L)) =
      prodFun f (fun j => y j + (a : AddCircle L)) := h3
  rw [h1', h3']
  unfold prodFun
  exact Finset.prod_congr rfl (fun j _ => h4 j)

/-- `τ_a^{⊗n}` on the completed tensor power is the coordinate translation. -/
theorem phys_tensorPower (n : ℕ) (a : ℝ) (x : HilbertTensorPower ℂ (L2T L) n) :
    physUnitary (L := L) (N := n) (tensorPower (transE a) n x) = transN n a (physUnitary (L := L) (N := n) x) := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq ((physUnitary (L := L) (N := n)).continuous.comp (tensorPower (transE (L := L) a) n).continuous)
      ((transN (L := L) n a).continuous.comp (physUnitary (L := L) (N := n)).continuous)
  | ih z =>
    induction z using AlgTensorPower.induction_on with
    | smul_ptprod r f =>
      simp only [UniformSpace.Completion.coe_smul, map_smul, tensorPower_ptprod, physUnitary_ptprod, transE_apply,
        prodLp_trans]
    | add z w hz hw => simp only [UniformSpace.Completion.coe_add, map_add, hz, hw]

/-- **Every actual Bethe vector is a translation eigenvector**: `τ_a^{⊗(N+1)} Ψ_m = e^{i a Q_{N,1}(m)} Ψ_m`. -/
theorem tensorPower_basis (hκ : 0 < κ) (N : ℕ) (a : ℝ) (m : MArr (N + 1)) :
    tensorPower (transE a) (N + 1)
        ((Def044D1SpectralR51a.basis (L := L) hκ N m : HN L (N + 1)) : HilbertTensorPower ℂ (L2T L) (N + 1)) =
      Complex.exp (Complex.I * ((a * eigenvalue L (N + 1) (κ / ((N + 1 : ℕ) : ℝ)) 1 m : ℝ) : ℂ)) •
        ((Def044D1SpectralR51a.basis (L := L) hκ N m : HN L (N + 1)) : HilbertTensorPower ℂ (L2T L) (N + 1)) := by
  apply (physUnitary (L := L) (N := N + 1)).injective
  rw [phys_tensorPower, map_smul]
  have hc0 : 0 < κ / ((N + 1 : ℕ) : ℝ) := div_pos hκ (by positivity)
  set c : ℝ≥0 := ⟨κ / ((N + 1 : ℕ) : ℝ), hc0.le⟩ with hcdef
  have hc : 0 < (c : ℝ) := hc0
  set ℓ := (BetheConditionalBasis.labelArr (N + 1)).symm m with hℓ
  have hpos : physUnitary (L := L) (N := N + 1)
      ((Def044D1SpectralR51a.basis (L := L) hκ N m : HN L (N + 1)) : HilbertTensorPower ℂ (L2T L) (N + 1)) =
      ((BetheConditionalBasis.normalizedWave L (N + 1) c ℓ : ContactOperator.SymL2 L (N + 1)) : L2TN L (N + 1)) :=
    congrArg Subtype.val (UnconditionalBetheBasis.physicalBasis_position L (N + 1) (by omega)
      (κ / ((N + 1 : ℕ) : ℝ)) hc0 m)
  have hW : ((BetheConditionalBasis.sourceWave L (N + 1) c ℓ : ContactOperator.SymL2 L (N + 1)) :
      L2TN L (N + 1)) = BetheH1.wave (L := L) (c := (c : ℝ)) hc ℓ.2 := BornTranslation.wave_coe (c := c) hc ℓ
  have hev : eigenvalue L (N + 1) (κ / ((N + 1 : ℕ) : ℝ)) 1 m =
      WaveTranslation.totalRoot L (κ / ((N + 1 : ℕ) : ℝ)) ℓ.1 := by
    simp only [eigenvalue, BetheSpectralCharges.rapidity, WaveTranslation.totalRoot, pow_one, hℓ]
  rw [hpos]
  unfold BetheConditionalBasis.normalizedWave
  rw [Submodule.coe_smul, map_smul, hW, BornTranslation.transN_wave hc ℓ.2 a, hev, smul_comm]
  rfl

/-- The HN-level translation. -/
def Tsec (a : ℝ) (N : ℕ) (ψ : HN L N) : HN L N :=
  ⟨tensorPower (transE a) N (ψ : HilbertTensorPower ℂ (L2T L) N),
    (tensorPower_mem_symSector_iff (transE (L := L) a) (ψ : HilbertTensorPower ℂ (L2T L) N)).2 ψ.2⟩

/-- **`exp(−i s Q_{N,1}) = τ_{−s}^{⊗(N+1)}`** on the whole sector. -/
theorem evolution_translate (hκ : 0 < κ) (N : ℕ) (s : ℝ) (ψ : HN L (N + 1)) :
    evolution (Def044D1SpectralR51a.basis (L := L) hκ N)
        (fun m => s * eigenvalue L (N + 1) (κ / ((N + 1 : ℕ) : ℝ)) 1 m) 1 ψ = Tsec (-s) (N + 1) ψ := by
  set b := Def044D1SpectralR51a.basis (L := L) hκ N with hb
  have hinv : tensorPower (transE (L := L) s) (N + 1) (tensorPower (transE (-s)) (N + 1)
      (ψ : HilbertTensorPower ℂ (L2T L) (N + 1))) = ψ := by
    rw [← tensorPower_trans, transE_inv, tensorPower_refl]
  apply b.repr.injective
  ext m
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply, evolution_coord]
  have hR : ⟪b m, Tsec (L := L) (-s) (N + 1) ψ⟫_ℂ =
      (starRingEnd ℂ) (Complex.exp (Complex.I *
        ((s * eigenvalue L (N + 1) (κ / ((N + 1 : ℕ) : ℝ)) 1 m : ℝ) : ℂ))) * ⟪b m, ψ⟫_ℂ := by
    have h := (tensorPower (transE (L := L) s) (N + 1)).inner_map_map
      ((b m : HN L (N + 1)) : HilbertTensorPower ℂ (L2T L) (N + 1))
      (tensorPower (transE (-s)) (N + 1) (ψ : HilbertTensorPower ℂ (L2T L) (N + 1)))
    rw [hinv, tensorPower_basis hκ N s m, inner_smul_left] at h
    exact h.symm
  rw [hR]
  congr 1
  unfold DiagonalMultiplier.phase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- A constant symbol is a global phase. -/
theorem evolution_const {N : ℕ} (b : BetheCoefficientTransform.BetheBasis L N) (c : ℝ) (φ : HN L N) :
    evolution b (fun _ => c) 1 φ = Complex.exp (-((c : ℝ) : ℂ) * Complex.I) • φ := by
  apply b.repr.injective
  ext m
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply, evolution_coord, inner_smul_right]
  unfold DiagonalMultiplier.phase
  congr 2
  push_cast
  ring

theorem low_sum (R : Finset ℕ) (f : ℕ → ℝ) :
    ∑ r ∈ R.filter (fun r => ¬ 2 ≤ r), f r = (if 0 ∈ R then f 0 else 0) + (if 1 ∈ R then f 1 else 0) := by
  have e : R.filter (fun r => ¬ 2 ≤ r) = ({0, 1} : Finset ℕ).filter (fun r => r ∈ R) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, by omega⟩
  rw [e, Finset.sum_filter, Finset.sum_pair (by norm_num)]

/-- The low/high split of the charge symbol. -/
theorem chargeSymbol_split (R : Finset ℕ) (t : ℕ → ℝ) (N : ℕ) (m : MArr (N + 1)) :
    ActualModelQuantumR52a.chargeSymbol (L := L) (κ := κ) R t N m =
      ((if 0 ∈ R then t 0 else 0) * ((N + 1 : ℕ) : ℝ) +
        (if 1 ∈ R then t 1 else 0) * eigenvalue L (N + 1) (κ / ((N + 1 : ℕ) : ℝ)) 1 m) +
      ActualModelQuantumR52a.chargeSymbol (L := L) (κ := κ) (R.filter (fun r => 2 ≤ r)) t N m := by
  unfold ActualModelQuantumR52a.chargeSymbol
  rw [← Finset.sum_filter_add_sum_filter_not R (fun r => 2 ≤ r), low_sum]
  have hc : ((N : ℝ) + 1) = ((N + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hc, BetheSpectralCharges.eigenvalue_zero]
  have e0 : (if 0 ∈ R then t 0 * ((N + 1 : ℕ) : ℝ) else 0) = (if 0 ∈ R then t 0 else 0) * ((N + 1 : ℕ) : ℝ) := by
    split_ifs <;> ring
  have e1 : (if 1 ∈ R then t 1 * eigenvalue L (N + 1) (κ / ((N + 1 : ℕ) : ℝ)) 1 m else 0) =
      (if 1 ∈ R then t 1 else 0) * eigenvalue L (N + 1) (κ / ((N + 1 : ℕ) : ℝ)) 1 m := by
    split_ifs <;> ring
  rw [e0, e1]
  ring

/-- **The low charges of the printed `U_N(t)`**: `U_N(t) = e^{−i t_0 (N+1)} τ_{−t_1}^{⊗(N+1)} U_N^{≥2}(t)`. -/
theorem chargeUnitary_split (hκ : 0 < κ) (R : Finset ℕ) (t : ℕ → ℝ) (N : ℕ) (ψ : HN L (N + 1)) :
    ((ActualModelQuantumR52a.chargeUnitary hκ R t N ψ : HN L (N + 1)) : HilbertTensorPower ℂ (L2T L) (N + 1)) =
      Complex.exp (-((((if 0 ∈ R then t 0 else 0) * ((N + 1 : ℕ) : ℝ) : ℝ)) : ℂ) * Complex.I) •
        tensorPower (transE (-(if 1 ∈ R then t 1 else 0))) (N + 1)
          ((ActualModelQuantumR52a.chargeUnitary hκ (R.filter (fun r => 2 ≤ r)) t N ψ : HN L (N + 1)) :
            HilbertTensorPower ℂ (L2T L) (N + 1)) := by
  unfold ActualModelQuantumR52a.chargeUnitary
  have hs : ActualModelQuantumR52a.chargeSymbol (L := L) (κ := κ) R t N = fun m =>
      (fun m => (fun _ => (if 0 ∈ R then t 0 else 0) * ((N + 1 : ℕ) : ℝ)) m +
        (fun m => (if 1 ∈ R then t 1 else 0) * eigenvalue L (N + 1) (κ / ((N + 1 : ℕ) : ℝ)) 1 m) m) m +
      ActualModelQuantumR52a.chargeSymbol (L := L) (κ := κ) (R.filter (fun r => 2 ≤ r)) t N m :=
    funext fun m => chargeSymbol_split R t N m
  rw [hs, Prop025OUnit.evolution_add_symbol, Prop025OUnit.evolution_add_symbol, evolution_const,
    evolution_translate]
  rfl

/-! ### 3. The classical low flows -/

theorem sort_split (R : Finset ℕ) :
    R.sort (· ≤ ·) = (R.filter (fun r => ¬ 2 ≤ r)).sort (· ≤ ·) ++ (R.filter (fun r => 2 ≤ r)).sort (· ≤ ·) := by
  have hperm : List.Perm (R.sort (· ≤ ·)) ((R.filter (fun r => ¬ 2 ≤ r)).sort (· ≤ ·) ++
      (R.filter (fun r => 2 ≤ r)).sort (· ≤ ·)) := by
    rw [← Multiset.coe_eq_coe, ← Multiset.coe_add, Finset.sort_eq, Finset.sort_eq, Finset.sort_eq,
      Finset.filter_val, Finset.filter_val, add_comm, Multiset.filter_add_not]
  refine List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (Finset.pairwise_sort _ _) ?_ hperm
  refine List.pairwise_append.2 ⟨Finset.pairwise_sort _ _, Finset.pairwise_sort _ _, fun a ha b hb => ?_⟩
  rw [Finset.mem_sort, Finset.mem_filter] at ha hb
  omega

theorem foldr_comp_apply {α : Type*} (l : List (α → α)) (g : α → α) (x : α) :
    l.foldr (· ∘ ·) g x = l.foldr (· ∘ ·) id (g x) := by
  induction l generalizing x with
  | nil => rfl
  | cons f l ih =>
    simp only [List.foldr_cons, Function.comp_apply]
    exact congrArg f (ih x)

theorem phaseFlow_zero (v : ℝ → ℂ) : phaseFlow 0 v = v := by
  funext x; simp [phaseFlow]

theorem transFlow_zero (v : ℝ → ℂ) : transFlow 0 v = v := by
  funext x; simp [transFlow]

/-- The joint flow is `phase ∘ translation ∘ (joint flow of the orders ≥ 2)`. -/
theorem joint_split (F : HigherFlows L κ) (R : Finset ℕ) (t : ℕ → ℝ) (v : ℝ → ℂ) :
    jointClassicalFlow (hamFlows F R) t v =
      phaseFlow (if 0 ∈ R then t 0 else 0) (transFlow (if 1 ∈ R then t 1 else 0)
        (jointClassicalFlow (hamFlows F (R.filter (fun r => 2 ≤ r))) t v)) := by
  unfold jointClassicalFlow
  rw [sort_split, List.map_append, List.foldr_append,
    foldr_comp_apply (((R.filter (fun r => ¬ 2 ≤ r)).sort (· ≤ ·)).map _)]
  by_cases h0 : 0 ∈ R <;> by_cases h1 : 1 ∈ R
  · have e : R.filter (fun r => ¬ 2 ≤ r) = {0, 1} := by
      ext r; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨-, h⟩; omega
      · rintro (rfl | rfl) <;> exact ⟨by assumption, by omega⟩
    rw [e, Def024LowFlows.sort_zero_one, if_pos h0, if_pos h1]
    rfl
  · have e : R.filter (fun r => ¬ 2 ≤ r) = {0} := by
      ext r; simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hr, h⟩; rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
        · rfl
        · exact absurd hr h1
      · rintro rfl; exact ⟨h0, by omega⟩
    rw [e, Finset.sort_singleton, if_pos h0, if_neg h1, transFlow_zero]
    rfl
  · have e : R.filter (fun r => ¬ 2 ≤ r) = {1} := by
      ext r; simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hr, h⟩; rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
        · exact absurd hr h0
        · rfl
      · rintro rfl; exact ⟨h1, by omega⟩
    rw [e, Finset.sort_singleton, if_neg h0, if_pos h1, phaseFlow_zero]
    rfl
  · have e : R.filter (fun r => ¬ 2 ≤ r) = ∅ := by
      ext r; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro hr h
      rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
      · exact h0 hr
      · exact h1 hr
    rw [e, Finset.sort_empty, if_neg h0, if_neg h1, phaseFlow_zero, transFlow_zero]
    rfl

/-- A smooth profile obtained by a phase and a translation has the corresponding `L²` class. -/
theorem physical_low (X Y : Smooth L) (c : ℂ) (a : ℝ) (h : ∀ y, X.val y = c * Y.val (y + a)) :
    physical X = c • trans a (physical Y) := by
  apply Lp.ext
  have hX : (physical X : AddCircle L → ℂ) =ᵐ[volume]
      (WeakDerivatives.liftC X.property.smooth.continuous X.property.periodic : AddCircle L → ℂ) :=
    PhysicalProductPreparation.smoothClass_ae X.property
  have hY : (physical Y : AddCircle L → ℂ) =ᵐ[volume]
      (WeakDerivatives.liftC Y.property.smooth.continuous Y.property.periodic : AddCircle L → ℂ) :=
    PhysicalProductPreparation.smoothClass_ae Y.property
  have hY' := (measurePreserving_add_right (volume : Measure (AddCircle L)) (a : AddCircle L)).quasiMeasurePreserving.ae
    hY
  filter_upwards [hX, Lp.coeFn_smul c (trans a (physical Y)), coeFn_trans a (physical Y), hY'] with x h1 h2 h3 h4
  rw [h1, h2, Pi.smul_apply, h3, h4, smul_eq_mul]
  clear h1 h2 h3 h4
  induction x using QuotientAddGroup.induction_on with
  | H y =>
    rw [← AddCircle.coe_add, WeakDerivatives.liftC_coe, WeakDerivatives.liftC_coe]
    exact h y

/-- **The classical target with the low orders**: `Φ_t(Φ_I(θ)u) = e^{−i t_0} τ_{−t_1} Φ_t^{≥2}(Φ_I(θ)u)`. -/
theorem target_split {hκ : 0 < κ} (C : Def021ChartR41b.Chart L κ hκ) (F : HigherFlows L κ) (I : Finset ℤ)
    (R : Finset ℕ) (θ : ℤ → ℝ) (t : ℕ → ℝ) (u : Smooth L) :
    target C F I R θ t u =
      Complex.exp (-Complex.I * ((if 0 ∈ R then t 0 else 0 : ℝ) : ℂ)) •
        trans (-(if 1 ∈ R then t 1 else 0)) (target C F I (R.filter (fun r => 2 ≤ r)) θ t u) := by
  unfold target
  apply physical_low
  intro y
  rw [RB7BindTopology.jointSmooth_val, RB7BindTopology.jointSmooth_val, joint_split]
  simp only [phaseFlow, transFlow, sub_eq_add_neg]

/-! ### 4. The reduction and the headline -/

/-- Each orders-`R` box term is at most the orders-`R ∩ [2,∞)` box term. -/
theorem box_low (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ) (F : HigherFlows L κ) (u : Smooth L)
    (I : Finset ℤ) (R : Finset ℕ) (k N : ℕ) (hk : k ≤ N + 1) (ψ : HN L (N + 1)) (t : ℕ → ℝ) (θ : ℤ → ℝ) :
    traceNorm (PhysicalTensor.reducedDensityN (N + 1) k hk
        (ActualModelQuantumR52a.chargeUnitary hκ R t N (ActualModelQuantumR52a.countUnitary hκ I θ N ψ) :
          HilbertTensorPower ℂ (L2T L) (N + 1)) - Prop025OInputs.tensorProj k (target C F I R θ t u)) ≤
      traceNorm (PhysicalTensor.reducedDensityN (N + 1) k hk
        (ActualModelQuantumR52a.chargeUnitary hκ (R.filter (fun r => 2 ≤ r)) t N
          (ActualModelQuantumR52a.countUnitary hκ I θ N ψ) : HilbertTensorPower ℂ (L2T L) (N + 1)) -
        Prop025OInputs.tensorProj k (target C F I (R.filter (fun r => 2 ≤ r)) θ t u)) := by
  have hc1 : ‖Complex.exp (-((((if 0 ∈ R then t 0 else 0) * ((N + 1 : ℕ) : ℝ) : ℝ)) : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]; simp
  have hc2 : ‖Complex.exp (-Complex.I * ((if 0 ∈ R then t 0 else 0 : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  rw [chargeUnitary_split hκ R t N, R52CFEvol.reducedDensityN_phase (N + 1) k hk _ hc1, rdN_tensorPower,
    target_split C F I R θ t u, tensorProj_smul k _ hc2, ← transE_apply,
    tensorProj_map (transE (-(if 1 ∈ R then t 1 else 0))) k, ← ContinuousLinearMap.comp_sub,
    ← ContinuousLinearMap.sub_comp]
  exact traceNorm_conj_le _ (norm_clm_le _) _

/-- The largest order `d = max(2, max R)` is unchanged by removing the orders `0, 1`. -/
theorem d_low (R : Finset ℕ) : max 2 (R.sup id) = max 2 ((R.filter (fun r => 2 ≤ r)).sup id) := by
  apply le_antisymm
  · refine max_le (le_max_left _ _) (Finset.sup_le fun r hr => ?_)
    by_cases h : 2 ≤ r
    · exact (Finset.le_sup (f := id) (Finset.mem_filter.2 ⟨hr, h⟩)).trans (le_max_right _ _)
    · exact (show id r ≤ 2 by simp only [id]; omega).trans (le_max_left _ _)
  · exact max_le_max le_rfl (Finset.sup_mono (Finset.filter_subset _ _))

/-- **PROP-025 (thm:MP-mixed), headline**, in the consumer form `ActualModelCorollaryR56a.PROP025Input`: for every
smooth unit profile, every DEF-044 interface `M` (`Def044BindingR26m.MixedInterface`), every finite `I ⊆ ℤ`, every
finite `R ⊆ ℕ` (orders `0` and `1` included, with their exact flows), every rank `k` (including `0`) and all boxes:
`MainEstimate` (one `C`, one `ζ_{I,N} → 0` with `ζ ≡ 0` for empty `I`, one threshold; uniform in times, angles and
normalized preparations).  Named inputs: PROP-021 (`Prop021Input`) and R-E59628C9 (`WindowInput`); the R-7B122087
hierarchy enters through `M` (`M.dynamics.hierarchy`). -/
theorem prop025 (hκ : 0 < κ) (H21 : Prop025OInputs.Prop021Input (L := L))
    (HW : Prop025OInputs.WindowInput (L := L) hκ) : ActualModelCorollaryR56a.PROP025Input (L := L) hκ := by
  intro u hu M I R k Θ T hΘ hT
  rcases Nat.eq_zero_or_pos k with rfl | _
  · exact Prop025OMain.rank_zero hκ _ _ u I R Θ T
  have hT2 : ∀ r ∈ R.filter (fun r => 2 ≤ r), 0 ≤ T r := fun r hr => hT r (Finset.mem_filter.1 hr).1
  obtain ⟨A, hA, ζ, hζ, hemp, N₀, hest⟩ := Prop025OMain.main_hi hκ H21 HW u hu M I (R.filter (fun r => 2 ≤ r)) k Θ T
    hΘ hT2 (fun r hr => (Finset.mem_filter.1 hr).2)
  refine ⟨A, hA, ζ, hζ, hemp, N₀, fun N hN hk ψ hψ => ?_⟩
  have h2 := hest N hN hk ψ hψ
  rw [← d_low R] at h2
  refine le_trans ?_ h2
  unfold boxError
  refine iSup_le fun t => iSup_le fun θ => ?_
  refine (box_low hκ _ _ u I R k N hk ψ t.val θ.val).trans ?_
  exact le_iSup₂_of_le (f := fun (t' : {t : ℕ → ℝ // ∀ r ∈ R.filter (fun r => 2 ≤ r), |t r| ≤ T r})
      (θ' : {θ : ℤ → ℝ // ∀ n ∈ I, |θ n| ≤ Θ n}) =>
      traceNorm (PhysicalTensor.reducedDensityN (N + 1) k hk
        (ActualModelQuantumR52a.chargeUnitary hκ (R.filter (fun r => 2 ≤ r)) t'.val N
          (ActualModelQuantumR52a.countUnitary hκ I θ'.val N ψ) : HilbertTensorPower ℂ (L2T L) (N + 1)) -
        Prop025OInputs.tensorProj k (target M.chart.chart (higher M.dynamics.hierarchy) I
          (R.filter (fun r => 2 ≤ r)) θ'.val t'.val u)))
    ⟨t.val, fun r hr => t.property r (Finset.mem_filter.1 hr).1⟩ θ le_rfl

/-- The actual-model instance with the three named inputs: PROP-021, R-E59628C9 and R-7B122087 (the shared
`HierarchyInputR25m.HierarchyR7B122087Input`, which builds the actual DEF-044 interface). -/
theorem prop025_actual_named (hκ : 0 < κ) (H21 : Prop025OInputs.Prop021Input (L := L))
    (HW : Prop025OInputs.WindowInput (L := L) hκ) (HH : Prop025OInputs.HierarchyInput (L := L) hκ)
    (u : Smooth L) (hu : ‖physical u‖ = 1) (I : Finset ℤ) (R : Finset ℕ) (k : ℕ) (Θ : ℤ → ℝ) (T : ℕ → ℝ)
    (hΘ : ∀ n ∈ I, 0 ≤ Θ n) (hT : ∀ r ∈ R, 0 ≤ T r) :
    MainEstimate hκ (ActualModelBindingR53a.chart (L := L) hκ)
      (higher (ActualModelBindingR53a.hierarchy_intermediate hκ HH)) u I R k Θ T :=
  ActualModelCorollaryR56a.cor_MP_actual_model_intermediate hκ (prop025 hκ H21 HW) HH u hu I R k Θ T hΘ hT

/-- **R-E679E41D binding** (cor:MP-actual-model): the actual chart and the actual hierarchy, with the certified
shared R-7B122087 input (`RB7BindFinal.hierarchyInputR25m_unconditional`, review record r86); the remaining named
inputs are PROP-021 and R-E59628C9. -/
theorem prop025_actual (hκ : 0 < κ) (H21 : Prop025OInputs.Prop021Input (L := L))
    (HW : Prop025OInputs.WindowInput (L := L) hκ)
    (u : Smooth L) (hu : ‖physical u‖ = 1) (I : Finset ℤ) (R : Finset ℕ) (k : ℕ) (Θ : ℤ → ℝ) (T : ℕ → ℝ)
    (hΘ : ∀ n ∈ I, 0 ≤ Θ n) (hT : ∀ r ∈ R, 0 ≤ T r) :
    MainEstimate hκ (ActualModelBindingR53a.chart (L := L) hκ)
      (higher (ActualModelBindingR53a.hierarchy_intermediate hκ (RB7BindFinal.hierarchyInputR25m_unconditional hκ)))
      u I R k Θ T :=
  ActualModelCorollaryR56a.cor_MP_actual_model_intermediate hκ (prop025 hκ H21 HW)
    (RB7BindFinal.hierarchyInputR25m_unconditional hκ) u hu I R k Θ T hΘ hT

end QuantumNLS.Prop025OLow

#print axioms QuantumNLS.Prop025OLow.rd_htmap
#print axioms QuantumNLS.Prop025OLow.tensorPower_basis
#print axioms QuantumNLS.Prop025OLow.evolution_translate
#print axioms QuantumNLS.Prop025OLow.chargeUnitary_split
#print axioms QuantumNLS.Prop025OLow.target_split
#print axioms QuantumNLS.Prop025OLow.box_low
#print axioms QuantumNLS.Prop025OLow.prop025
#print axioms QuantumNLS.Prop025OLow.prop025_actual_named
#print axioms QuantumNLS.Prop025OLow.prop025_actual
#print QuantumNLS.ActualModelCorollaryR56a.PROP025Input
-- Recursive type/value audit of every own declaration: standard axioms only, and no held
-- identifier (HeldGP14Tonelli, the superseded pre-D1 `RegularCut`) in the transitive closure.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop025OLow." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 ||
          n.components.any (fun c => c.toString == "RegularCut") then
        throwError "Held dependency: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Prop025OLow aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only, no held identifiers."
