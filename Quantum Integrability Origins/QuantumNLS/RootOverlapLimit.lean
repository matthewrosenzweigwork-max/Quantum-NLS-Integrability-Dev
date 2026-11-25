import QuantumNLS.RootOverlapCommutator
import QuantumNLS.SymplecticBracket
import QuantumNLS.PlacementFiberCanonicalPrefix

/-!
# R-32EBD5C1 `lem:root-overlap`, stage 2: the fixed-order limit `eq:root-overlap-limit`
(ROOT_transfer_involution.tex:25 ff)

Proved (`root_overlap_limit`): for fixed `p, q`, bounded kernels `A : Sym^p H → Sym^p H`,
`B : Sym^q H → Sym^q H` on a generic complex Hilbert space and every unit `u`,
`lim_{N→∞} −iN ⟨u^{⊗N}, [Q_{N,p}(A), Q_{N,q}(B)] u^{⊗N}⟩ = {a, b}(u)`,
with `Q_{N,r} = genericU_N_r` (DEF-009), `a(v) = ⟨v^{⊗p}, A v^{⊗p}⟩`, `b(v) = ⟨v^{⊗q}, B v^{⊗q}⟩`
(`kernelProductSymbol`) and `{·,·} = pbC`, the realized DEF-015 complex-bilinear bracket
(`SymplecticBracket`); the sequence is `limSeq` (value `0` for `N < max p q`).
Proof following the printed one:
* overlap-size expansion: `⟨u^N,[Q_p,Q_q]u^N⟩ = c_{N,1}·E₁ + R_N`, `|R_N| ≤ 2‖A‖‖B‖Σ_{s≥2}c_{N,s}`
  (`expect_formula`, `expect_decomp`: disjoint pairs commute, the expectation `E(z)` is relabel-invariant
  (`Eexp_relabel`) hence constant on the overlap-one class via Luna's transitivity
  (`Eexp_eq_of_overlap_eq`), class sizes by `card_Z1`, `card_Z2`);
* single-overlap expectation: for self-adjoint kernels `E₁ = ⟨α,β⟩ − ⟨β,α⟩`, with the contractions
  `⟨h, α⟩ = ⟨h ⊗ u^{⊗(p-1)}, A u^{⊗p}⟩` (`alphaIns`, `inner_XY`, `core_ptC`, `Eexp_zcan`);
* symbols: `∇a(u) = p α(u)`, `{a,b}(u) = 2pq Im⟨α,β⟩` (`gradient_symbolR`, `pbR_symbolR`,
  `pbR_value`), `da(u)[h] = 2p Re⟨α,h⟩` (`fderiv_symbolR`);
* limits from OverlapMoments: `N c_{N,1} → pq`, `N Σ_{s≥2} c_{N,s} → 0` (`limit_selfAdj`);
* the self-adjoint reduction: general `A, B` are `reK + i·imK` (`reK_imK`), the commutator expectation is
  complex-bilinear (`ExN_decomp`, linearity of `genericU_N_r`), and `pbC` is its bilinear extension
  (`re_kps`, `im_kps`); the cases `p = 0` or `q = 0` are trivial (`ExN_zero_left/right`, `pbC_zero_*`).
The printed remark that the bracket "can be computed on the full Hilbert space or on the phase
quotient of the unit sphere" is formalized as the tangential reduction `pbR_tangential`
(`Im⟨α_⊥,β_⊥⟩ = Im⟨α,β⟩` for `α_⊥ = α−⟨u,α⟩u`); the phase-quotient bracket itself is not part of the
realized DEF-015 (which is the full-space bracket) and is not formalized separately.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped InnerProductSpace TensorProduct
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements QuantumNLS.KernelDefinition
  QuantumNLS.PlacementFusion QuantumNLS.PlacementOverlap QuantumNLS.PlacementProduct
  QuantumNLS.PlacementCovariance QuantumNLS.PlacementGrouping QuantumNLS.PlacementUnionReindex
  QuantumNLS.PlacementFiberOperator QuantumNLS.RootOverlapCommutator

namespace QuantumNLS.RootOverlapLimit

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Derivative of `u ↦ u^{⊗n}` (real Fréchet) -/

theorem ptprod_one_add' (u v : H) :
    (ptprod (fun _ : Fin 1 => u + v) : AlgTensorPower ℂ H 1) =
      ptprod (fun _ : Fin 1 => u) + ptprod (fun _ : Fin 1 => v) := by
  have h : (fun _ : Fin 1 => u + v) = Function.update (fun _ : Fin 1 => u) 0 (u + v) := by
    ext i; fin_cases i; simp
  have h1 := (PiTensorProduct.tprod ℂ (s := fun _ : Fin 1 => H)).map_update_add
    (fun _ : Fin 1 => u) 0 u v
  have e1 : Function.update (fun _ : Fin 1 => u) 0 u = fun _ => u := by
    ext i; fin_cases i; simp
  have e2 : Function.update (fun _ : Fin 1 => u) 0 v = fun _ => v := by
    ext i; fin_cases i; simp
  rw [e1, e2, ← h] at h1
  exact h1

theorem ptprod_one_smul' (c : ℂ) (u : H) :
    (ptprod (fun _ : Fin 1 => c • u) : AlgTensorPower ℂ H 1) =
      c • ptprod (fun _ : Fin 1 => u) := by
  have h : (fun _ : Fin 1 => c • u) = Function.update (fun _ : Fin 1 => u) 0 (c • u) := by
    ext i; fin_cases i; simp
  have h1 := (PiTensorProduct.tprod ℂ (s := fun _ : Fin 1 => H)).map_update_smul
    (fun _ : Fin 1 => u) 0 c u
  have e1 : Function.update (fun _ : Fin 1 => u) 0 u = fun _ => u := by
    ext i; fin_cases i; simp
  rw [e1, ← h] at h1
  exact h1

/-- `H → H^{⊗̂ 1}`, `h ↦ h`, as a continuous linear map (isometric). -/
def lift1 : H →L[ℂ] HilbertTensorPower ℂ H 1 :=
  LinearMap.mkContinuous
    { toFun := fun h => ptC (fun _ : Fin 1 => h)
      map_add' := fun u v => by
        show ((ptprod (fun _ : Fin 1 => u + v) : AlgTensorPower ℂ H 1) :
          HilbertTensorPower ℂ H 1) = _
        rw [ptprod_one_add', UniformSpace.Completion.coe_add]
      map_smul' := fun c u => by
        show ((ptprod (fun _ : Fin 1 => c • u) : AlgTensorPower ℂ H 1) :
          HilbertTensorPower ℂ H 1) = _
        rw [ptprod_one_smul', UniformSpace.Completion.coe_smul]; rfl } 1 (by
    intro h
    simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
    show ‖((ptprod (fun _ : Fin 1 => h) : AlgTensorPower ℂ H 1) : HilbertTensorPower ℂ H 1)‖ ≤ _
    rw [UniformSpace.Completion.norm_coe, norm_ptprod]
    simp [Finset.univ_unique])

theorem lift1_apply (h : H) : lift1 h = ptC (fun _ : Fin 1 => h) := rfl

section Deriv
open Filter Topology

def ptprodML (n : ℕ) : MultilinearMap ℂ (fun _ : Fin n => H) (AlgTensorPower ℂ H n) where
  toFun := fun f => ptprod f
  map_update_add' := fun m i x y =>
    (PiTensorProduct.tprod ℂ (s := fun _ : Fin n => H)).map_update_add m i x y
  map_update_smul' := fun m i c x =>
    (PiTensorProduct.tprod ℂ (s := fun _ : Fin n => H)).map_update_smul m i c x

def htpowML (n : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => H) (HilbertTensorPower ℂ H n) :=
  ((MultilinearMap.mkContinuous
    ((UniformSpace.Completion.toComplL : AlgTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n).toLinearMap.compMultilinearMap
      (ptprodML n)) 1 (by
      intro f
      simp only [LinearMap.compMultilinearMap_apply, ContinuousLinearMap.coe_coe, one_mul]
      show ‖((ptprod f : AlgTensorPower ℂ H n) : HilbertTensorPower ℂ H n)‖ ≤ _
      rw [UniformSpace.Completion.norm_coe, norm_ptprod]) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => H) (HilbertTensorPower ℂ H n))).restrictScalars ℝ

theorem htpowML_apply (n : ℕ) (f : Fin n → H) :
    htpowML n f = ptC f := by
  simp [htpowML, ptprodML]
  rfl

def diagL (n : ℕ) : H →L[ℝ] (Fin n → H) := ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℝ H

def dP (n : ℕ) (u : H) : H →L[ℝ] HilbertTensorPower ℂ H n :=
  (htpowML n).linearDeriv (fun _ => u) ∘L diagL n

theorem dP_apply (n : ℕ) (u h : H) :
    dP n u h = ∑ i : Fin n, ptC (Function.update (fun _ : Fin n => u) i h) := by
  simp [dP, diagL, ContinuousMultilinearMap.linearDeriv_apply, htpowML_apply]

theorem hasFDerivAt_htpow (n : ℕ) (u : H) :
    HasFDerivAt (fun v : H => (htpow n v : HilbertTensorPower ℂ H n)) (dP n u) u := by
  have h1 := (htpowML n).hasFDerivAt (fun _ : Fin n => u)
  have h2 := h1.comp u (diagL n).hasFDerivAt
  have h3 : (⇑(htpowML n) ∘ ⇑(diagL n)) =
      fun v : H => (htpow n v : HilbertTensorPower ℂ H n) := by
    funext v
    simp only [Function.comp_apply, htpowML_apply]
    rfl
  rw [h3] at h2
  exact h2

end Deriv

section Ins

/-- Insert `h` in the last slot of a `(p'+1)`-fold power, `u` in the other `p'` slots. -/
def insA (p' : ℕ) (u : H) : H →L[ℂ] HilbertTensorPower ℂ H (p' + 1) :=
  (splitIsometry (𝕜 := ℂ) (E := H) p' 1).symm.toLinearIsometry.toContinuousLinearMap.comp
    ((htR (ptC (fun _ : Fin p' => u))).comp lift1)

/-- Insert `h` in the first slot of a `(1+q')`-fold power, `u` in the other `q'` slots. -/
def insB (q' : ℕ) (u : H) : H →L[ℂ] HilbertTensorPower ℂ H (1 + q') :=
  (splitIsometry (𝕜 := ℂ) (E := H) 1 q').symm.toLinearIsometry.toContinuousLinearMap.comp
    ((htL (ptC (fun _ : Fin q' => u))).comp lift1)

theorem insA_apply (p' : ℕ) (u h : H) :
    insA p' u h = ptC (Fin.append (fun _ : Fin p' => u) (fun _ : Fin 1 => h)) := by
  simp only [insA, ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometry.coe_toContinuousLinearMap, htR_apply, lift1_apply]
  exact split_symm_ptC _ _

theorem insB_apply (q' : ℕ) (u h : H) :
    insB q' u h = ptC (Fin.append (fun _ : Fin 1 => h) (fun _ : Fin q' => u)) := by
  simp only [insB, ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometry.coe_toContinuousLinearMap, htL_apply, lift1_apply]
  exact split_symm_ptC _ _

theorem append_single_last (p' : ℕ) (u h : H) :
    Fin.append (fun _ : Fin p' => u) (fun _ : Fin 1 => h) =
      Function.update (fun _ : Fin (p' + 1) => u) (Fin.last p') h := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · have : Fin.castAdd 1 j ≠ Fin.last p' := by
      intro h'; have h2 := congrArg Fin.val h'; simp at h2; have := j.2; omega
    simp [Function.update_of_ne this]
  · have hk : k = 0 := Subsingleton.elim _ _
    subst hk
    have : (Fin.natAdd p' (0 : Fin 1)) = Fin.last p' := by ext; simp
    rw [Fin.append_right, this, Function.update_self]

theorem inner_ptC_update_sym {n : ℕ} (u h : H) (w : HilbertTensorPower ℂ H n)
    (hw : w ∈ SymSector ℂ H n) (i j : Fin n) :
    ⟪ptC (Function.update (fun _ : Fin n => u) i h), w⟫_ℂ =
      ⟪ptC (Function.update (fun _ : Fin n => u) j h), w⟫_ℂ := by
  have hperm : ptC (Function.update (fun _ : Fin n => u) j h) =
      (permRep ℂ H n (Equiv.swap i j) : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n)
        (ptC (Function.update (fun _ : Fin n => u) i h)) := by
    rw [permRep_ptC]
    congr 1
    funext k
    by_cases hk : k = j
    · subst hk; simp [Equiv.swap_apply_right]
    · by_cases hki : k = i
      · subst hki
        have hij : k ≠ j := hk
        simp [Equiv.swap_apply_left, Function.update_of_ne hk, Function.update_of_ne hij.symm]
      · rw [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne hki hk,
          Function.update_of_ne hk, Function.update_of_ne hki]
  have hfix : (permRep ℂ H n (Equiv.swap i j) : HilbertTensorPower ℂ H n →L[ℂ]
      HilbertTensorPower ℂ H n) w = w := hw (Equiv.swap i j)
  rw [hperm]
  conv_rhs => rw [← hfix]
  exact ((permHilbertIsometry (𝕜 := ℂ) (E := H) (Equiv.swap i j)).inner_map_map _ _).symm

end Ins

section Gradient
open Filter Topology QuantumNLS.SymplecticBracket

/-- Inner-product form of self-adjointness of a kernel. -/
def SelfAdj {r : ℕ} (A : BoundedSymmetricKernel H r) : Prop :=
  ∀ x y : SymSector ℂ H r, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ

theorem extend_htpow {r : ℕ} (A : BoundedSymmetricKernel H r) (u : H) :
    extendSymKernel A (htpow r u : HilbertTensorPower ℂ H r) =
      ((A ⟨htpow r u, htpow_mem_symSector r u⟩ : SymSector ℂ H r) :
        HilbertTensorPower ℂ H r) := by
  have : symProjToSector r (htpow r u : HilbertTensorPower ℂ H r) =
      ⟨htpow r u, htpow_mem_symSector r u⟩ := by
    apply Subtype.ext
    change symProj ℂ H r _ = _
    change groupAverage (permRep ℂ H r) _ = _
    exact groupAverage_apply_of_mem (permRep ℂ H r) (htpow_mem_symSector r u)
  show ((SymSector ℂ H r).subtypeL (A (symProjToSector r _))) = _
  rw [this]; rfl

theorem inner_symProj_right {r : ℕ} {z y : HilbertTensorPower ℂ H r} (hz : z ∈ SymSector ℂ H r) :
    ⟪z, y⟫_ℂ = ⟪z, ((symProjToSector r y : SymSector ℂ H r) : HilbertTensorPower ℂ H r)⟫_ℂ := by
  change ⟪z, y⟫_ℂ = ⟪z, symProj ℂ H r y⟫_ℂ
  rw [symProj_eq_starProjection]
  have h1 := Submodule.inner_starProjection_left_eq_right (SymSector ℂ H r) z y
  rwa [Submodule.starProjection_eq_self_iff.mpr hz] at h1

theorem extend_selfAdj {r : ℕ} {A : BoundedSymmetricKernel H r} (hA : SelfAdj A)
    (x y : HilbertTensorPower ℂ H r) :
    ⟪extendSymKernel A x, y⟫_ℂ = ⟪x, extendSymKernel A y⟫_ℂ := by
  have h1 : ⟪extendSymKernel A x, y⟫_ℂ = ⟪A (symProjToSector r x), symProjToSector r y⟫_ℂ := by
    show ⟪((A (symProjToSector r x) : SymSector ℂ H r) : HilbertTensorPower ℂ H r), y⟫_ℂ = _
    rw [inner_symProj_right (A (symProjToSector r x)).2, ← Submodule.coe_inner]
  have h2 : ⟪x, extendSymKernel A y⟫_ℂ = ⟪symProjToSector r x, A (symProjToSector r y)⟫_ℂ := by
    show ⟪x, ((A (symProjToSector r y) : SymSector ℂ H r) : HilbertTensorPower ℂ H r)⟫_ℂ = _
    rw [← inner_conj_symm, inner_symProj_right (A (symProjToSector r y)).2, inner_conj_symm,
      ← Submodule.coe_inner]
  rw [h1, h2, hA]


/-- The contraction vector `α ∈ H`: `⟨h, α⟩ = ⟨ins h, A u^{⊗r}⟩`, where `ins h` puts `h` in one
slot and `u` in the other `r-1` slots (`⟨h, α⟩ = ⟨h ⊗ u^{⊗(r-1)}, A u^{⊗r}⟩`). -/
def alphaIns {r : ℕ} (ins : H →L[ℂ] HilbertTensorPower ℂ H r) (A : BoundedSymmetricKernel H r)
    (u : H) : H :=
  ContinuousLinearMap.adjoint ins
    ((A ⟨htpow r u, htpow_mem_symSector r u⟩ : SymSector ℂ H r) : HilbertTensorPower ℂ H r)

/-- The real homogeneous symbol `Re ⟨u^{⊗r}, A u^{⊗r}⟩` of a kernel. -/
def symbolR {r : ℕ} (A : BoundedSymmetricKernel H r) (v : H) : ℝ := (kernelProductSymbol A v).re

theorem fderiv_symbolR {r : ℕ} (i0 : Fin r) {A : BoundedSymmetricKernel H r} (hA : SelfAdj A)
    (u : H) (ins : H →L[ℂ] HilbertTensorPower ℂ H r)
    (hins : ∀ h, ins h = ptC (Function.update (fun _ : Fin r => u) i0 h)) (h : H) :
    fderiv ℝ (symbolR A) u h = (r : ℝ) * (2 * (⟪h, alphaIns ins A u⟫_ℂ).re) := by
  set Ae := extendSymKernel A with hAe
  have hP := hasFDerivAt_htpow r u
  have hAeD : HasFDerivAt (fun v : H => Ae (htpow r v : HilbertTensorPower ℂ H r))
      ((Ae.restrictScalars ℝ).comp (dP r u)) u :=
    ((Ae.restrictScalars ℝ).hasFDerivAt).comp u hP
  have hI := hP.inner ℂ hAeD
  have hRe := Complex.reCLM.hasFDerivAt.comp u hI
  have hfun : symbolR A = ⇑Complex.reCLM ∘ fun t => ⟪(htpow r t :
      HilbertTensorPower ℂ H r), Ae (htpow r t)⟫_ℂ := by
    funext v
    simp only [symbolR, kernelProductSymbol, hAe, extend_htpow, Function.comp_apply,
      Complex.reCLM_apply]
  have hd : fderiv ℝ (symbolR A) u = Complex.reCLM.comp ((fderivInnerCLM ℂ
      (htpow r u, Ae (htpow r u))).comp ((dP r u).prod
      ((Ae.restrictScalars ℝ).comp (dP r u)))) := by
    rw [hfun]; exact hRe.fderiv
  rw [hd]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, Complex.reCLM_apply,
    fderivInnerCLM_apply]
  have hw : Ae (htpow r u : HilbertTensorPower ℂ H r) ∈ SymSector ℂ H r := by
    rw [hAe, extend_htpow]; exact (A ⟨htpow r u, htpow_mem_symSector r u⟩).2
  have h1 : ⟪(dP r u) h, Ae (htpow r u : HilbertTensorPower ℂ H r)⟫_ℂ =
      (r : ℂ) * ⟪h, alphaIns ins A u⟫_ℂ := by
    rw [dP_apply]
    erw [sum_inner (𝕜 := ℂ)]
    have h2 : ∀ i : Fin r,
        ⟪ptC (Function.update (fun _ : Fin r => u) i h),
          Ae (htpow r u : HilbertTensorPower ℂ H r)⟫_ℂ =
        ⟪h, alphaIns ins A u⟫_ℂ := by
      intro i
      rw [inner_ptC_update_sym u h _ hw i i0, ← hins]
      unfold alphaIns
      rw [ContinuousLinearMap.adjoint_inner_right, hAe, extend_htpow]
    refine (Finset.sum_congr rfl (fun i _ => h2 i)).trans ?_
    simp
  have h3 : ⟪(htpow r u : HilbertTensorPower ℂ H r),
      (ContinuousLinearMap.restrictScalars ℝ Ae) ((dP r u) h)⟫_ℂ =
      (starRingEnd ℂ) ⟪(dP r u) h, Ae (htpow r u : HilbertTensorPower ℂ H r)⟫_ℂ := by
    exact (extend_selfAdj hA _ _).symm.trans (inner_conj_symm _ _).symm
  erw [h3, Complex.add_re, Complex.conj_re, h1]
  simp [Complex.mul_re]
  ring

section Grad2
attribute [local instance] InnerProductSpace.complexToReal

theorem gradient_symbolR {r : ℕ} (i0 : Fin r) {A : BoundedSymmetricKernel H r} (hA : SelfAdj A)
    (u : H) (ins : H →L[ℂ] HilbertTensorPower ℂ H r)
    (hins : ∀ h, ins h = ptC (Function.update (fun _ : Fin r => u) i0 h)) :
    QuantumNLS.SymplecticBracket.gradient (symbolR A) u = (r : ℝ) • alphaIns ins A u := by
  have hgrad : ∀ h : H, fderiv ℝ (symbolR A) u h =
      2 * inner ℝ ((r : ℝ) • alphaIns ins A u) h := by
    intro h
    rw [fderiv_symbolR i0 hA u ins hins h, real_inner_smul_left, real_inner_eq_re_inner ℂ,
      ← inner_conj_symm, Complex.conj_re]
    simp only [RCLike.re_to_complex]
    ring
  have hg := fun h => QuantumNLS.SymplecticBracket.fderiv_eq_two_inner_gradient (symbolR A) u h
  apply ext_inner_right ℝ
  intro h
  have := hg h
  rw [hgrad h] at this
  linarith

/-- **`{a,b}(u) = 2 p q Im ⟨α, β⟩`** for the real symbols of self-adjoint kernels. -/
theorem pbR_symbolR {p q : ℕ} (i0 : Fin p) (j0 : Fin q) {A : BoundedSymmetricKernel H p}
    {B : BoundedSymmetricKernel H q} (hA : SelfAdj A) (hB : SelfAdj B) (u : H)
    (insA : H →L[ℂ] HilbertTensorPower ℂ H p)
    (hinsA : ∀ h, insA h = ptC (Function.update (fun _ : Fin p => u) i0 h))
    (insB : H →L[ℂ] HilbertTensorPower ℂ H q)
    (hinsB : ∀ h, insB h = ptC (Function.update (fun _ : Fin q => u) j0 h)) :
    QuantumNLS.SymplecticBracket.pbR (symbolR A) (symbolR B) u =
      2 * ((p : ℝ) * q) * (⟪alphaIns insA A u, alphaIns insB B u⟫_ℂ).im := by
  rw [QuantumNLS.SymplecticBracket.pbR_eq_omega, gradient_symbolR i0 hA u insA hinsA,
    gradient_symbolR j0 hB u insB hinsB]
  unfold QuantumNLS.SymplecticBracket.omega
  rw [← Complex.coe_smul, ← Complex.coe_smul, inner_smul_left, inner_smul_right]
  simp only [Complex.conj_ofReal]
  rw [← mul_assoc, ← Complex.ofReal_mul]
  rw [Complex.im_ofReal_mul]
  ring

end Grad2

end Gradient

section Core

theorem inner_ptC_ptC {n : ℕ} (f g : Fin n → H) :
    ⟪(ptC f : HilbertTensorPower ℂ H n), ptC g⟫_ℂ = ∏ i, ⟪f i, g i⟫_ℂ := by
  show ⟪((ptprod f : AlgTensorPower ℂ H n) : HilbertTensorPower ℂ H n),
    ((ptprod g : AlgTensorPower ℂ H n) : HilbertTensorPower ℂ H n)⟫_ℂ = _
  rw [UniformSpace.Completion.inner_coe, inner_ptprod]

theorem kappaA_ptC (p' : ℕ) (u : H) (a : Fin (p' + 1) → H) :
    ContinuousLinearMap.adjoint (insA p' u) (ptC a) =
      (∏ i : Fin p', ⟪u, a (Fin.castAdd 1 i)⟫_ℂ) • a (Fin.last p') := by
  apply ext_inner_left ℂ
  intro h
  rw [ContinuousLinearMap.adjoint_inner_right, insA_apply, append_single_last]
  refine (inner_ptC_ptC _ _).trans (Eq.trans ?_ (inner_smul_right _ _ _).symm)
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Function.update_of_ne (Fin.castSucc_lt_last i).ne]
    rfl
  · rw [Function.update_self]

theorem kappaB_ptC (q' : ℕ) (u : H) (b : Fin (1 + q') → H) :
    ContinuousLinearMap.adjoint (insB q' u) (ptC b) =
      (∏ j : Fin q', ⟪u, b (Fin.natAdd 1 j)⟫_ℂ) • b (Fin.castAdd q' 0) := by
  apply ext_inner_left ℂ
  intro h
  rw [ContinuousLinearMap.adjoint_inner_right, insB_apply]
  refine (inner_ptC_ptC _ _).trans (Eq.trans ?_ (inner_smul_right _ _ _).symm)
  rw [Fin.prod_univ_add, mul_comm]
  congr 1
  · refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [Fin.append_right]
  · rw [Fin.prod_univ_one, Fin.append_left]

end Core

section CoreProd

theorem append_apply_lt {α : Type*} {n m : ℕ} (a : Fin n → α) (b : Fin m → α) (k : Fin (n + m))
    (hk : k.val < n) : Fin.append a b k = a ⟨k.val, hk⟩ := by
  exact (congrArg (Fin.append a b) (Fin.ext rfl : k = Fin.castAdd m ⟨k.val, hk⟩)).trans
    (Fin.append_left a b _)

theorem append_const_ge {α : Type*} {n m : ℕ} (a : Fin n → α) (x : α) (k : Fin (n + m))
    (hk : n ≤ k.val) : Fin.append a (fun _ : Fin m => x) k = x := by
  exact (congrArg (Fin.append a (fun _ : Fin m => x))
    (Fin.ext (by simp; omega) : k = Fin.natAdd n ⟨k.val - n, by omega⟩)).trans
    (Fin.append_right a _ _)

/-- Left placement vector `A`-side: `V1 v = (v ⊗ u^{⊗ m1})` transported to `N`. -/
def V1 (p' q' r m1 : ℕ) (h1 : p' + 1 + m1 = p' + ((1 + q') + r)) (u : H) :
    HilbertTensorPower ℂ H (p' + 1) →L[ℂ] HilbertTensorPower ℂ H (p' + ((1 + q') + r)) :=
  (cIso h1).toLinearIsometry.toContinuousLinearMap.comp
    ((splitIsometry (𝕜 := ℂ) (E := H) (p' + 1) m1).symm.toLinearIsometry.toContinuousLinearMap.comp
      (htL (htpow m1 u : HilbertTensorPower ℂ H m1)))

/-- Middle placement vector `B`-side: `w ↦ u^{p'} ⊗ (w ⊗ u^r)`. -/
def V2 (p' q' r : ℕ) (u : H) :
    HilbertTensorPower ℂ H (1 + q') →L[ℂ] HilbertTensorPower ℂ H (p' + ((1 + q') + r)) :=
  (splitIsometry (𝕜 := ℂ) (E := H) p' ((1 + q') + r)).symm.toLinearIsometry.toContinuousLinearMap.comp
    ((htR (htpow p' u : HilbertTensorPower ℂ H p')).comp
      ((splitIsometry (𝕜 := ℂ) (E := H) (1 + q') r).symm.toLinearIsometry.toContinuousLinearMap.comp
        (htL (htpow r u : HilbertTensorPower ℂ H r))))

theorem V1_ptC (p' q' r m1 : ℕ) (h1 : p' + 1 + m1 = p' + ((1 + q') + r)) (u : H)
    (a : Fin (p' + 1) → H) :
    V1 p' q' r m1 h1 u (ptC a) =
      ptC (fun i => Fin.append a (fun _ : Fin m1 => u) (Fin.cast h1.symm i)) := by
  simp only [V1, ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometry.coe_toContinuousLinearMap, htL_apply]
  have : (htpow m1 u : HilbertTensorPower ℂ H m1) = ptC (fun _ : Fin m1 => u) := rfl
  rw [this, split_symm_ptC, cIso_ptC]

theorem V2_ptC (p' q' r : ℕ) (u : H) (b : Fin (1 + q') → H) :
    V2 p' q' r u (ptC b) =
      ptC (Fin.append (fun _ : Fin p' => u) (Fin.append b (fun _ : Fin r => u))) := by
  simp only [V2, ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometry.coe_toContinuousLinearMap, htL_apply, htR_apply]
  have h1 : (htpow r u : HilbertTensorPower ℂ H r) = ptC (fun _ : Fin r => u) := rfl
  have h2 : (htpow p' u : HilbertTensorPower ℂ H p') = ptC (fun _ : Fin p' => u) := rfl
  rw [h1, h2, split_symm_ptC, split_symm_ptC]

end CoreProd

section CoreProd2

theorem f1_lt (p' q' r m1 : ℕ) (h1 : p' + 1 + m1 = p' + ((1 + q') + r)) (u : H)
    (a : Fin (p' + 1) → H) (i : Fin (p' + ((1 + q') + r))) (hi : i.val < p' + 1) :
    Fin.append a (fun _ : Fin m1 => u) (Fin.cast h1.symm i) = a ⟨i.val, hi⟩ :=
  append_apply_lt a _ _ (by simpa using hi)

theorem f1_ge (p' q' r m1 : ℕ) (h1 : p' + 1 + m1 = p' + ((1 + q') + r)) (u : H)
    (a : Fin (p' + 1) → H) (i : Fin (p' + ((1 + q') + r))) (hi : p' + 1 ≤ i.val) :
    Fin.append a (fun _ : Fin m1 => u) (Fin.cast h1.symm i) = u :=
  append_const_ge a u _ (by simpa using hi)

theorem core_ptC (p' q' r m1 : ℕ) (h1 : p' + 1 + m1 = p' + ((1 + q') + r)) (u : H)
    (hu : ‖u‖ = 1) (a : Fin (p' + 1) → H) (b : Fin (1 + q') → H) :
    ⟪V1 p' q' r m1 h1 u (ptC a), V2 p' q' r u (ptC b)⟫_ℂ =
      ⟪ContinuousLinearMap.adjoint (insA p' u) (ptC a),
        ContinuousLinearMap.adjoint (insB q' u) (ptC b)⟫_ℂ := by
  have huu : ⟪u, u⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hu]; norm_num
  rw [V1_ptC, V2_ptC, kappaA_ptC, kappaB_ptC]
  refine (inner_ptC_ptC _ _).trans ?_
  have hR : ∀ (c d : ℂ) (x y : H), ⟪c • x, d • y⟫_ℂ = (starRingEnd ℂ) c * (d * ⟪x, y⟫_ℂ) := by
    intro c d x y
    erw [inner_smul_left, inner_smul_right]
  erw [hR]
  rw [Fin.prod_univ_add]
  rw [Fin.prod_univ_add]
  rw [Fin.prod_univ_add]
  have e1 : (∏ i : Fin p', ⟪Fin.append a (fun _ : Fin m1 => u)
        (Fin.cast h1.symm (Fin.castAdd (1 + q' + r) i)),
      Fin.append (fun _ : Fin p' => u) (Fin.append b fun _ : Fin r => u)
        (Fin.castAdd (1 + q' + r) i)⟫_ℂ) = ∏ i : Fin p', ⟪a (Fin.castAdd 1 i), u⟫_ℂ := by
    refine Finset.prod_congr rfl (fun i _ => ?_)
    have hi : (Fin.castAdd (1 + q' + r) i).val < p' + 1 := by
      simp only [Fin.coe_castAdd]; have := i.2; omega
    rw [f1_lt p' q' r m1 h1 u a _ hi, Fin.append_left]
    have : (⟨(Fin.castAdd (1 + q' + r) i).val, hi⟩ : Fin (p' + 1)) = Fin.castAdd 1 i :=
      Fin.ext (by simp)
    rw [this]
  have e2 : (∏ i : Fin 1, ⟪Fin.append a (fun _ : Fin m1 => u)
        (Fin.cast h1.symm (Fin.natAdd p' (Fin.castAdd r (Fin.castAdd q' i)))),
      Fin.append (fun _ : Fin p' => u) (Fin.append b fun _ : Fin r => u)
        (Fin.natAdd p' (Fin.castAdd r (Fin.castAdd q' i)))⟫_ℂ) =
      ⟪a (Fin.last p'), b (Fin.castAdd q' 0)⟫_ℂ := by
    rw [Fin.prod_univ_one]
    have hi : (Fin.natAdd p' (Fin.castAdd r (Fin.castAdd q' (0 : Fin 1)))).val < p' + 1 := by
      simp
    rw [f1_lt p' q' r m1 h1 u a _ hi, Fin.append_right, Fin.append_left]
    have : (⟨(Fin.natAdd p' (Fin.castAdd r (Fin.castAdd q' (0 : Fin 1)))).val, hi⟩ :
        Fin (p' + 1)) = Fin.last p' := Fin.ext (by simp)
    rw [this]
  have e3 : (∏ i : Fin q', ⟪Fin.append a (fun _ : Fin m1 => u)
        (Fin.cast h1.symm (Fin.natAdd p' (Fin.castAdd r (Fin.natAdd 1 i)))),
      Fin.append (fun _ : Fin p' => u) (Fin.append b fun _ : Fin r => u)
        (Fin.natAdd p' (Fin.castAdd r (Fin.natAdd 1 i)))⟫_ℂ) =
      ∏ i : Fin q', ⟪u, b (Fin.natAdd 1 i)⟫_ℂ := by
    refine Finset.prod_congr rfl (fun i _ => ?_)
    have hi : p' + 1 ≤ (Fin.natAdd p' (Fin.castAdd r (Fin.natAdd 1 i))).val := by
      simp only [Fin.coe_natAdd, Fin.coe_castAdd]; omega
    rw [f1_ge p' q' r m1 h1 u a _ hi, Fin.append_right, Fin.append_left]
  have e4 : (∏ i : Fin r, ⟪Fin.append a (fun _ : Fin m1 => u)
        (Fin.cast h1.symm (Fin.natAdd p' (Fin.natAdd (1 + q') i))),
      Fin.append (fun _ : Fin p' => u) (Fin.append b fun _ : Fin r => u)
        (Fin.natAdd p' (Fin.natAdd (1 + q') i))⟫_ℂ) = 1 := by
    rw [Finset.prod_eq_one]
    intro i _
    have hi : p' + 1 ≤ (Fin.natAdd p' (Fin.natAdd (1 + q') i)).val := by
      simp only [Fin.coe_natAdd]; omega
    rw [f1_ge p' q' r m1 h1 u a _ hi, Fin.append_right, Fin.append_right]
    exact huu
  rw [e1, e2, e3, e4, map_prod]
  have e5 : ∀ i : Fin p', (starRingEnd ℂ) ⟪u, a (Fin.castAdd 1 i)⟫_ℂ = ⟪a (Fin.castAdd 1 i), u⟫_ℂ :=
    fun i => inner_conj_symm _ _
  rw [Finset.prod_congr rfl (fun i _ => e5 i)]
  ring

theorem Phi_eq (p' q' r m1 : ℕ) (h1 : p' + 1 + m1 = p' + ((1 + q') + r)) (u : H) (hu : ‖u‖ = 1)
    (v : HilbertTensorPower ℂ H (p' + 1)) (w : HilbertTensorPower ℂ H (1 + q')) :
    ⟪V1 p' q' r m1 h1 u v, V2 p' q' r u w⟫_ℂ =
      ⟪ContinuousLinearMap.adjoint (insA p' u) v, ContinuousLinearMap.adjoint (insB q' u) w⟫_ℂ := by
  have step1 : ∀ a : Fin (p' + 1) → H, ∀ w : HilbertTensorPower ℂ H (1 + q'),
      ⟪V1 p' q' r m1 h1 u (ptC a), V2 p' q' r u w⟫_ℂ =
        ⟪ContinuousLinearMap.adjoint (insA p' u) (ptC a),
          ContinuousLinearMap.adjoint (insB q' u) w⟫_ℂ := by
    intro a w
    have := eq_of_eq_on_ptC
      ((innerSL ℂ (V1 p' q' r m1 h1 u (ptC a))).comp (V2 p' q' r u))
      ((innerSL ℂ (ContinuousLinearMap.adjoint (insA p' u) (ptC a))).comp
        (ContinuousLinearMap.adjoint (insB q' u)))
      (fun b => core_ptC p' q' r m1 h1 u hu a b)
    exact congrArg (fun F : _ →L[ℂ] ℂ => F w) this
  have step2 : ∀ v : HilbertTensorPower ℂ H (p' + 1),
      ⟪V2 p' q' r u w, V1 p' q' r m1 h1 u v⟫_ℂ =
        ⟪ContinuousLinearMap.adjoint (insB q' u) w,
          ContinuousLinearMap.adjoint (insA p' u) v⟫_ℂ := by
    have := eq_of_eq_on_ptC
      ((innerSL ℂ (V2 p' q' r u w)).comp (V1 p' q' r m1 h1 u))
      ((innerSL ℂ (ContinuousLinearMap.adjoint (insB q' u) w)).comp
        (ContinuousLinearMap.adjoint (insA p' u)))
      (fun a => by
        have h := step1 a w
        have h2 := congrArg (starRingEnd ℂ) h
        rw [inner_conj_symm, inner_conj_symm] at h2
        exact h2)
    intro v
    exact congrArg (fun F : _ →L[ℂ] ℂ => F v) this
  have := congrArg (starRingEnd ℂ) (step2 v)
  rw [inner_conj_symm, inner_conj_symm] at this
  exact this

end CoreProd2

section Canon

open QuantumNLS.PlacementFiberTransport

theorem subsetPlacement_first {p m : ℕ} (S : PlacementSubset p m)
    (hS : S.1 = firstPositions (p := p) (q := m)) (A : BoundedSymmetricKernel H p) :
    subsetPlacement S A = firstPlacement (q := m) A := by
  have hperm : placementSubsetOfPerm (p := p) (q := m) (1 : Equiv.Perm (Fin (p + m))) = S := by
    apply Subtype.ext
    simp only [placementSubsetOfPerm, hS]
    ext x; simp [Equiv.Perm.one_def]
  have := permutedPlacement_eq_subsetPlacement (1 : Equiv.Perm (Fin (p + m))) S hperm A
  rw [← this]
  have hb : (1 : Equiv.Perm (Fin (p + m))) =
      blockPerm (1 : Equiv.Perm (Fin p)) (1 : Equiv.Perm (Fin m)) := by
    ext i; simp [blockPerm]
  rw [hb]
  exact permutedPlacement_blockPerm_eq 1 1 A

theorem firstPlacement_htpow (p m : ℕ) (A : BoundedSymmetricKernel H p) (u : H) :
    firstPlacement (q := m) A (htpow (p + m) u : HilbertTensorPower ℂ H (p + m)) =
      (splitIsometry (𝕜 := ℂ) (E := H) p m).symm
        (htmul ((A ⟨htpow p u, htpow_mem_symSector p u⟩ : SymSector ℂ H p) :
            HilbertTensorPower ℂ H p) (htpow m u : HilbertTensorPower ℂ H m)) := by
  unfold firstPlacement
  simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometry.coe_toContinuousLinearMap]
  rw [split_htpow, htmap_htmul, extend_htpow, ContinuousLinearMap.id_apply]

theorem midPlacement_htpow (p0 q r : ℕ) (B : BoundedSymmetricKernel H q) (u : H) :
    midPlacement p0 q r B (htpow (p0 + (q + r)) u : HilbertTensorPower ℂ H (p0 + (q + r))) =
      (splitIsometry (𝕜 := ℂ) (E := H) p0 (q + r)).symm
        (htmul (htpow p0 u : HilbertTensorPower ℂ H p0)
          ((splitIsometry (𝕜 := ℂ) (E := H) q r).symm
            (htmul ((B ⟨htpow q u, htpow_mem_symSector q u⟩ : SymSector ℂ H q) :
              HilbertTensorPower ℂ H q) (htpow r u : HilbertTensorPower ℂ H r)))) := by
  unfold midPlacement
  simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometry.coe_toContinuousLinearMap]
  rw [split_htpow, htmap_htmul, ContinuousLinearMap.id_apply, firstPlacement_htpow]

end Canon

section Canon2

open QuantumNLS.PlacementFiberTransport

theorem hp_can (p' q' r : ℕ) : p' + 1 ≤ p' + ((1 + q') + r) := by omega
theorem hq_can (p' q' r : ℕ) : 1 + q' ≤ p' + ((1 + q') + r) := by omega

/-- The canonical pair of slot sets `[0,p'+1)` and `[p', p'+1+q')` (overlap exactly one slot). -/
def zcan (p' q' r : ℕ) : ActualPairPlacement (p' + ((1 + q') + r)) (p' + 1) (1 + q') :=
  (⟨firstPositions, card_firstPositions _ _⟩,
    sourcePlacementOfSlots (hq_can p' q' r) (slotsB p' (1 + q') r) (card_slotsB p' (1 + q') r))

theorem leftSlots_zcan (p' q' r : ℕ) :
    leftSlots (hp_can p' q' r) (zcan p' q' r) =
      castSlotSet (Nat.add_sub_of_le (hp_can p' q' r)) firstPositions := rfl

theorem rightSlots_zcan (p' q' r : ℕ) :
    rightSlots (hq_can p' q' r) (zcan p' q' r) = slotsB p' (1 + q') r :=
  slots_sourcePlacementOfSlots (hq_can p' q' r) (slotsB p' (1 + q') r)
    (card_slotsB p' (1 + q') r)

theorem Xu (p' q' r : ℕ) (A : BoundedSymmetricKernel H (p' + 1)) (u : H) :
    rawSubsetPlacement (p' + ((1 + q') + r)) (p' + 1) (hp_can p' q' r) (zcan p' q' r).1 A
        (htpow (p' + ((1 + q') + r)) u : HilbertTensorPower ℂ H (p' + ((1 + q') + r))) =
      V1 p' q' r (p' + ((1 + q') + r) - (p' + 1)) (Nat.add_sub_of_le (hp_can p' q' r)) u
        ((A ⟨htpow (p' + 1) u, htpow_mem_symSector (p' + 1) u⟩ : SymSector ℂ H (p' + 1)) :
          HilbertTensorPower ℂ H (p' + 1)) := by
  unfold rawSubsetPlacement
  rw [subsetPlacement_first (zcan p' q' r).1 rfl A, castTensorOperator_eq_conj]
  have h1 := Nat.add_sub_of_le (hp_can p' q' r)
  have : ((cIso h1).symm (htpow (p' + ((1 + q') + r)) u : HilbertTensorPower ℂ H
      (p' + ((1 + q') + r))) : HilbertTensorPower ℂ H (p' + 1 + (p' + ((1 + q') + r) - (p' + 1)))) =
      htpow (p' + 1 + (p' + ((1 + q') + r) - (p' + 1))) u := by
    have := cIso_symm_ptC (H := H) h1 (fun _ => u)
    exact this
  rw [this, firstPlacement_htpow]
  simp only [V1, ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometry.coe_toContinuousLinearMap, htL_apply]

theorem Yu (p' q' r : ℕ) (B : BoundedSymmetricKernel H (1 + q')) (u : H) :
    rawSubsetPlacement (p' + ((1 + q') + r)) (1 + q') (hq_can p' q' r) (zcan p' q' r).2 B
        (htpow (p' + ((1 + q') + r)) u : HilbertTensorPower ℂ H (p' + ((1 + q') + r))) =
      V2 p' q' r u
        ((B ⟨htpow (1 + q') u, htpow_mem_symSector (1 + q') u⟩ : SymSector ℂ H (1 + q')) :
          HilbertTensorPower ℂ H (1 + q')) := by
  unfold rawSubsetPlacement
  rw [rawMid p' (1 + q') r B _ (Nat.add_sub_of_le (hq_can p' q' r)) (zcan p' q' r).2
    (rightSlots_zcan p' q' r)]
  rw [midPlacement_htpow]
  simp only [V2, ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometry.coe_toContinuousLinearMap, htL_apply, htR_apply]

/-- The expectation core: `⟨X u^N, Y u^N⟩ = ⟨α, β⟩`. -/
theorem inner_XY (p' q' r : ℕ) (A : BoundedSymmetricKernel H (p' + 1))
    (B : BoundedSymmetricKernel H (1 + q')) (u : H) (hu : ‖u‖ = 1) :
    ⟪rawSubsetPlacement (p' + ((1 + q') + r)) (p' + 1) (hp_can p' q' r) (zcan p' q' r).1 A
        (htpow (p' + ((1 + q') + r)) u : HilbertTensorPower ℂ H (p' + ((1 + q') + r))),
      rawSubsetPlacement (p' + ((1 + q') + r)) (1 + q') (hq_can p' q' r) (zcan p' q' r).2 B
        (htpow (p' + ((1 + q') + r)) u : HilbertTensorPower ℂ H (p' + ((1 + q') + r)))⟫_ℂ =
      ⟪alphaIns (insA p' u) A u, alphaIns (insB q' u) B u⟫_ℂ := by
  rw [Xu, Yu]
  exact Phi_eq p' q' r _ (Nat.add_sub_of_le (hp_can p' q' r)) u hu _ _

end Canon2

section Expect

open QuantumNLS.PlacementFiberTransport

/-- The expectation in the product state of the commutator of the placements of a pair. -/
def Eexp (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N) (A : BoundedSymmetricKernel H p)
    (B : BoundedSymmetricKernel H q) (u : H) (z : ActualPairPlacement N p q) : ℂ :=
  ⟪(htpow N u : HilbertTensorPower ℂ H N),
    ((rawSubsetPlacement N p hp z.1 A).comp (rawSubsetPlacement N q hq z.2 B) -
      (rawSubsetPlacement N q hq z.2 B).comp (rawSubsetPlacement N p hp z.1 A))
      (htpow N u)⟫_ℂ

theorem conj_comp_eq {n : ℕ} (σ : Equiv.Perm (Fin n))
    (X Y : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n) :
    (((permRep ℂ H n σ : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n).comp X).comp
        (permRep ℂ H n σ⁻¹ : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n)).comp
      (((permRep ℂ H n σ : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n).comp Y).comp
        (permRep ℂ H n σ⁻¹ : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n)) =
      ((permRep ℂ H n σ : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n).comp
        (X.comp Y)).comp
        (permRep ℂ H n σ⁻¹ : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply]
  rw [permRep_cancel]

theorem permRep_htpow {n : ℕ} (σ : Equiv.Perm (Fin n)) (u : H) :
    (permRep ℂ H n σ : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n)
      (htpow n u : HilbertTensorPower ℂ H n) = htpow n u :=
  htpow_mem_symSector n u σ

theorem inner_conj_invariant {n : ℕ} (σ : Equiv.Perm (Fin n)) (u : H)
    (Z : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n) :
    ⟪(htpow n u : HilbertTensorPower ℂ H n),
      (((permRep ℂ H n σ : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n).comp Z).comp
        (permRep ℂ H n σ⁻¹ : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n))
        (htpow n u)⟫_ℂ = ⟪(htpow n u : HilbertTensorPower ℂ H n), Z (htpow n u)⟫_ℂ := by
  have h1 : (permRep ℂ H n σ⁻¹ : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n)
      (htpow n u : HilbertTensorPower ℂ H n) = htpow n u := htpow_mem_symSector n u σ⁻¹
  simp only [ContinuousLinearMap.comp_apply]
  rw [h1]
  calc ⟪(htpow n u : HilbertTensorPower ℂ H n), (permRep ℂ H n σ :
        HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n) (Z (htpow n u))⟫_ℂ
      = ⟪(permRep ℂ H n σ : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n)
          (htpow n u), (permRep ℂ H n σ : HilbertTensorPower ℂ H n →L[ℂ]
            HilbertTensorPower ℂ H n) (Z (htpow n u))⟫_ℂ := by rw [permRep_htpow]
    _ = _ := (permHilbertIsometry (𝕜 := ℂ) (E := H) σ).inner_map_map _ _

theorem Eexp_relabel (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N) (A : BoundedSymmetricKernel H p)
    (B : BoundedSymmetricKernel H q) (u : H) (σ : Equiv.Perm (Fin N))
    (z : ActualPairPlacement N p q) :
    Eexp N p q hp hq A B u (relabelActualPair hp hq σ z) = Eexp N p q hp hq A B u z := by
  have e1 : ((permRep ℂ H N σ : HilbertTensorPower ℂ H N →L[ℂ] HilbertTensorPower ℂ H N).comp
        (rawSubsetPlacement N p hp z.1 A)).comp
        (permRep ℂ H N σ⁻¹ : HilbertTensorPower ℂ H N →L[ℂ] HilbertTensorPower ℂ H N) =
      rawSubsetPlacement N p hp (relabelActualPair hp hq σ z).1 A :=
    castSubsetPlacement_conjugate (Nat.add_sub_of_le hp) σ z.1 A
  have e2 : ((permRep ℂ H N σ : HilbertTensorPower ℂ H N →L[ℂ] HilbertTensorPower ℂ H N).comp
        (rawSubsetPlacement N q hq z.2 B)).comp
        (permRep ℂ H N σ⁻¹ : HilbertTensorPower ℂ H N →L[ℂ] HilbertTensorPower ℂ H N) =
      rawSubsetPlacement N q hq (relabelActualPair hp hq σ z).2 B :=
    castSubsetPlacement_conjugate (Nat.add_sub_of_le hq) σ z.2 B
  have hop : (rawSubsetPlacement N p hp (relabelActualPair hp hq σ z).1 A).comp
        (rawSubsetPlacement N q hq (relabelActualPair hp hq σ z).2 B) -
      (rawSubsetPlacement N q hq (relabelActualPair hp hq σ z).2 B).comp
        (rawSubsetPlacement N p hp (relabelActualPair hp hq σ z).1 A) =
      ((permRep ℂ H N σ : HilbertTensorPower ℂ H N →L[ℂ] HilbertTensorPower ℂ H N).comp
        ((rawSubsetPlacement N p hp z.1 A).comp (rawSubsetPlacement N q hq z.2 B) -
          (rawSubsetPlacement N q hq z.2 B).comp (rawSubsetPlacement N p hp z.1 A))).comp
        (permRep ℂ H N σ⁻¹ : HilbertTensorPower ℂ H N →L[ℂ] HilbertTensorPower ℂ H N) := by
    rw [← e1, ← e2, conj_comp_eq, conj_comp_eq, ContinuousLinearMap.comp_sub,
      ContinuousLinearMap.sub_comp]
  unfold Eexp
  rw [hop, inner_conj_invariant]

end Expect

section Trans

open QuantumNLS.PlacementFiberTransport QuantumNLS.PlacementFiberCanonicalPrefix

theorem canonicalPrefix_eq {N p q : ℕ} (b1 b2 : PairPlacementBase N p q)
    (h : overlapSizeOfBase b1 = overlapSizeOfBase b2) :
    canonicalPrefixPairBase b1 = canonicalPrefixPairBase b2 := by
  have hmem : ∀ (b : PairPlacementBase N p q) (x : Fin N),
      x ∈ (canonicalPrefixPairBase b).1.2 ↔ x.val < unionSize p q (overlapSizeOfBase b) := by
    intro b x
    simp only [canonicalPrefixPairBase, Finset.mem_map, Finset.mem_univ, true_and,
      Fin.castLEEmb_apply]
    constructor
    · rintro ⟨i, rfl⟩; exact i.2
    · intro hx; exact ⟨⟨x.val, hx⟩, Fin.ext rfl⟩
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext h
  · ext x
    show x ∈ (canonicalPrefixPairBase b1).1.2 ↔ x ∈ (canonicalPrefixPairBase b2).1.2
    rw [hmem, hmem, h]

theorem Eexp_eq_of_overlap_eq (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N)
    (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) (u : H)
    (z1 z2 : ActualPairPlacement N p q)
    (h : (leftSlots hp z1 ∩ rightSlots hq z1).card = (leftSlots hp z2 ∩ rightSlots hq z2).card) :
    Eexp N p q hp hq A B u z1 = Eexp N p q hp hq A B u z2 := by
  set b1 := pairPlacementKey hp hq z1 with hb1
  set b2 := pairPlacementKey hp hq z2 with hb2
  have hov : overlapSizeOfBase b1 = overlapSizeOfBase b2 := h
  obtain ⟨σ1, hσ1⟩ := exists_relabel_pairBase_eq_canonicalPrefix b1
  obtain ⟨σ2, hσ2⟩ := exists_relabel_pairBase_eq_canonicalPrefix b2
  have hcp := canonicalPrefix_eq b1 b2 hov
  set z1' := relabelActualPair hp hq σ1 z1 with hz1'
  set z2' := relabelActualPair hp hq σ2 z2 with hz2'
  have k1 : pairPlacementKey hp hq z1' = canonicalPrefixPairBase b1 := by
    rw [hz1', pairPlacementKey_relabelActualPair]; exact hσ1
  have k2 : pairPlacementKey hp hq z2' = canonicalPrefixPairBase b1 := by
    rw [hz2', pairPlacementKey_relabelActualPair, hcp]; exact hσ2
  obtain ⟨σ3, hσ3, _⟩ := exists_ambient_relabel_pair_eq hp hq (canonicalPrefixPairBase b1)
    ⟨z1', k1⟩ ⟨z2', k2⟩
  have e1 := Eexp_relabel N p q hp hq A B u σ1 z1
  have e2 := Eexp_relabel N p q hp hq A B u σ2 z2
  have e3 := Eexp_relabel N p q hp hq A B u σ3 z1'
  have hz3 : relabelActualPair hp hq σ3 z1' = z2' := hσ3
  rw [hz3] at e3
  rw [← e1, ← e3, e2]

end Trans

section Overlap1

open QuantumNLS.PlacementFiberTransport

theorem mem_leftSlots_zcan (p' q' r : ℕ) (x : Fin (p' + ((1 + q') + r))) :
    x ∈ leftSlots (hp_can p' q' r) (zcan p' q' r) ↔ x.val < p' + 1 := by
  rw [leftSlots_zcan]
  simp only [castSlotSet, Finset.mem_map, firstPositions, Finset.mem_univ, true_and,
    Fin.castAddEmb_apply, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [equivCast_eq_finCast (Nat.add_sub_of_le (hp_can p' q' r))]; have := i.2; simp; omega
  · intro hx
    refine ⟨Fin.castAdd _ ⟨x.val, hx⟩, ⟨⟨x.val, hx⟩, rfl⟩, ?_⟩
    rw [equivCast_eq_finCast (Nat.add_sub_of_le (hp_can p' q' r))]; exact Fin.ext (by simp)

theorem mem_slotsB (p' q' r : ℕ) (x : Fin (p' + ((1 + q') + r))) :
    x ∈ slotsB p' (1 + q') r ↔ p' ≤ x.val ∧ x.val < p' + (1 + q') := by
  simp only [slotsB, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩; simp
  · intro hx
    refine ⟨⟨x.val - p', by omega⟩, Fin.ext ?_⟩
    simp; omega

theorem card_overlap_zcan (p' q' r : ℕ) :
    (leftSlots (hp_can p' q' r) (zcan p' q' r) ∩
      rightSlots (hq_can p' q' r) (zcan p' q' r)).card = 1 := by
  rw [rightSlots_zcan]
  have : leftSlots (hp_can p' q' r) (zcan p' q' r) ∩ slotsB p' (1 + q') r =
      {(⟨p', by omega⟩ : Fin (p' + ((1 + q') + r)))} := by
    ext x
    rw [Finset.mem_inter, mem_leftSlots_zcan, mem_slotsB, Finset.mem_singleton, Fin.ext_iff]
    simp only
    omega
  rw [this]; rfl

end Overlap1

section Count2

open QuantumNLS.PlacementFiberTransport QuantumNLS.OverlapMoments

theorem card_placements_filter {N q : ℕ} (hq : q ≤ N) (pred : Finset (Fin N) → Prop)
    [DecidablePred pred] :
    (Finset.univ.filter (fun T : PlacementSubset q (N - q) =>
        pred (castSlotSet (Nat.add_sub_of_le hq) T.1))).card =
      (((Finset.univ : Finset (Fin N)).powersetCard q).filter pred).card := by
  classical
  refine Finset.card_bij (fun T _ => castSlotSet (Nat.add_sub_of_le hq) T.1) ?_ ?_ ?_
  · intro T hT
    obtain ⟨_, h2⟩ := Finset.mem_filter.mp hT
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩, h2⟩
    simp [castSlotSet, T.2]
  · intro T1 _ T2 _ h
    apply Subtype.ext
    exact Finset.map_injective _ h
  · intro Q hQ
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hQ
    have hcard : Q.card = q := (Finset.mem_powersetCard.mp h1).2
    refine ⟨sourcePlacementOfSlots hq Q hcard, ?_, slots_sourcePlacementOfSlots hq Q hcard⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [slots_sourcePlacementOfSlots]; exact h2

theorem card_meeting_ge {N p q : ℕ} (P : Finset (Fin N)) (hP : P.card = p) {m : ℕ} (hm : 1 ≤ m) :
    (((Finset.univ : Finset (Fin N)).powersetCard q).filter (fun Q => m ≤ (P ∩ Q).card)).card =
      ∑ s ∈ (Finset.range (q + 1)).filter (fun s => m ≤ s),
        p.choose s * (N - p).choose (q - s) := by
  classical
  set S := ((Finset.univ : Finset (Fin N)).powersetCard q).filter (fun Q => m ≤ (P ∩ Q).card)
    with hS
  have hmaps : ∀ Q ∈ S, (P ∩ Q).card ∈ (Finset.range (q + 1)).filter (fun s => m ≤ s) := by
    intro Q hQ
    obtain ⟨hQ1, hQ2⟩ := Finset.mem_filter.mp hQ
    have hq : Q.card = q := (Finset.mem_powersetCard.mp hQ1).2
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, hQ2⟩
    have := Finset.card_le_card (Finset.inter_subset_right (s₁ := P) (s₂ := Q))
    omega
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  obtain ⟨hs1, hs2⟩ := Finset.mem_filter.mp hs
  have hsq : s ≤ q := by have := Finset.mem_range.mp hs1; omega
  rw [← card_overlapFiber P hP hsq]
  congr 1
  ext Q
  simp only [hS, overlapFiber, Finset.mem_filter]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩
    exact ⟨⟨h1, by rw [h3]; exact hs2⟩, h3⟩

theorem card_class_pairs {N p q : ℕ} (hp : p ≤ N) (hq : q ≤ N) (pred : Finset (Fin N) → Prop)
    [DecidablePred pred] (W : ℕ) (hW : ∀ P : Finset (Fin N), P.card = p →
      (((Finset.univ : Finset (Fin N)).powersetCard q).filter (fun Q => pred (P ∩ Q))).card = W) :
    (Finset.univ.filter (fun z : ActualPairPlacement N p q =>
        pred (leftSlots hp z ∩ rightSlots hq z))).card = N.choose p * W := by
  classical
  rw [Finset.card_filter, Fintype.sum_prod_type]
  have h : ∀ S : PlacementSubset p (N - p),
      (∑ T : PlacementSubset q (N - q),
        if pred (leftSlots hp (S, T) ∩ rightSlots hq (S, T)) then 1 else 0) = W := by
    intro S
    have hP : (castSlotSet (Nat.add_sub_of_le hp) S.1).card = p := by
      simp [castSlotSet, S.2]
    rw [← hW _ hP, ← card_placements_filter hq (fun Q => pred (castSlotSet (Nat.add_sub_of_le hp) S.1 ∩ Q)),
      Finset.card_filter]
    rfl
  rw [Finset.sum_congr rfl (fun S _ => h S), Finset.sum_const, Finset.card_univ,
    card_placementSubset, smul_eq_mul]
  rw [Nat.add_sub_of_le hp]

end Count2

section Assemble

open QuantumNLS.PlacementFiberTransport QuantumNLS.OverlapMoments

/-- The normalized expectation of the commutator as a sum over pairs. -/
theorem expect_comm_eq (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N) (A : BoundedSymmetricKernel H p)
    (B : BoundedSymmetricKernel H q) (u : H) :
    ⟪(htpow N u : HilbertTensorPower ℂ H N),
      ((((genericU_N_r N p hp A).comp (genericU_N_r N q hq B) -
          (genericU_N_r N q hq B).comp (genericU_N_r N p hp A))
        ⟨htpow N u, htpow_mem_symSector N u⟩ : SymSector ℂ H N) : HilbertTensorPower ℂ H N)⟫_ℂ =
      (((N.choose p : ℂ)⁻¹) * ((N.choose q : ℂ)⁻¹)) *
        ∑ z : ActualPairPlacement N p q, Eexp N p q hp hq A B u z := by
  have e : ((((genericU_N_r N p hp A).comp (genericU_N_r N q hq B) -
        (genericU_N_r N q hq B).comp (genericU_N_r N p hp A))
          ⟨htpow N u, htpow_mem_symSector N u⟩ : SymSector ℂ H N) : HilbertTensorPower ℂ H N) =
      ((rawSubsetAverage N p hp A).comp (rawSubsetAverage N q hq B) -
        (rawSubsetAverage N q hq B).comp (rawSubsetAverage N p hp A))
          (htpow N u : HilbertTensorPower ℂ H N) := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, Submodule.coe_sub,
      coe_genericU]
  rw [e, average_commutator_eq]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply]
  rw [inner_smul_right, inner_sum]
  congr 1
  simp_rw [inner_sum]
  rw [Fintype.sum_prod_type]
  rfl

theorem norm_Eexp_le (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N) (A : BoundedSymmetricKernel H p)
    (B : BoundedSymmetricKernel H q) (u : H) (hu : ‖u‖ = 1) (z : ActualPairPlacement N p q) :
    ‖Eexp N p q hp hq A B u z‖ ≤ 2 * (‖A‖ * ‖B‖) := by
  have h1 : ‖(htpow N u : HilbertTensorPower ℂ H N)‖ = 1 := by rw [norm_htpow, hu]; simp
  unfold Eexp
  refine (norm_inner_le_norm _ _).trans ?_
  refine (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)).trans ?_
  rw [h1]
  have := norm_pair_comm_le N p q hp hq A B z
  simpa using this

theorem Eexp_zero_of_disjoint (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N) (A : BoundedSymmetricKernel H p)
    (B : BoundedSymmetricKernel H q) (u : H) (z : ActualPairPlacement N p q)
    (hc : (leftSlots hp z ∩ rightSlots hq z).card = 0) :
    Eexp N p q hp hq A B u z = 0 := by
  have hd : Disjoint (leftSlots hp z) (rightSlots hq z) := by
    rw [Finset.disjoint_iff_inter_eq_empty]; exact Finset.card_eq_zero.mp hc
  unfold Eexp
  rw [rawPlacement_commute_of_disjoint N p q hp hq A B z hd, sub_self]
  simp

end Assemble

section Decomp

open QuantumNLS.PlacementFiberTransport QuantumNLS.OverlapMoments

theorem card_Z1 {N p q : ℕ} (hp : p ≤ N) (hq : q ≤ N) (hq1 : 1 ≤ q) :
    (Finset.univ.filter (fun z : ActualPairPlacement N p q =>
        (leftSlots hp z ∩ rightSlots hq z).card = 1)).card =
      N.choose p * (p.choose 1 * (N - p).choose (q - 1)) := by
  classical
  refine card_class_pairs hp hq (fun I => I.card = 1) _ (fun P hP => ?_)
  have := card_overlapFiber (N := N) (p := p) (q := q) (s := 1) P hP hq1
  simpa [overlapFiber] using this

theorem card_Z2 {N p q : ℕ} (hp : p ≤ N) (hq : q ≤ N) :
    (Finset.univ.filter (fun z : ActualPairPlacement N p q =>
        2 ≤ (leftSlots hp z ∩ rightSlots hq z).card)).card =
      N.choose p * ∑ s ∈ (Finset.range (q + 1)).filter (fun s => 2 ≤ s),
        p.choose s * (N - p).choose (q - s) := by
  classical
  refine card_class_pairs hp hq (fun I => 2 ≤ I.card) _ (fun P hP => ?_)
  exact card_meeting_ge P hP (by norm_num)

end Decomp

section Decomp2

open QuantumNLS.PlacementFiberTransport QuantumNLS.OverlapMoments

theorem expect_decomp (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N) (hq1 : 1 ≤ q)
    (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) (u : H) (hu : ‖u‖ = 1)
    (zref : ActualPairPlacement N p q)
    (hz : (leftSlots hp zref ∩ rightSlots hq zref).card = 1) :
    ∃ R : ℂ,
      ⟪(htpow N u : HilbertTensorPower ℂ H N),
        ((((genericU_N_r N p hp A).comp (genericU_N_r N q hq B) -
            (genericU_N_r N q hq B).comp (genericU_N_r N p hp A))
          ⟨htpow N u, htpow_mem_symSector N u⟩ : SymSector ℂ H N) :
            HilbertTensorPower ℂ H N)⟫_ℂ =
        ((overlapCoefficient N p q 1 : ℝ) : ℂ) * Eexp N p q hp hq A B u zref + R ∧
      ‖R‖ ≤ 2 * (‖A‖ * ‖B‖) * ∑ s ∈ (Finset.range (q + 1)).filter (fun s => 2 ≤ s),
        overlapCoefficient N p q s := by
  classical
  let c : ActualPairPlacement N p q → ℕ := fun z => (leftSlots hp z ∩ rightSlots hq z).card
  let f := Eexp N p q hp hq A B u
  have hpt : ∀ z, f z = (if c z = 0 then f z else 0) + (if c z = 1 then f z else 0) +
      (if 2 ≤ c z then f z else 0) := by
    intro z
    rcases Nat.lt_or_ge (c z) 2 with h | h
    · interval_cases hcz : c z <;> simp
    · have h0 : c z ≠ 0 := by omega
      have h1 : c z ≠ 1 := by omega
      simp [h0, h1, h]
  have hsum : ∑ z, f z = (∑ z ∈ Finset.univ.filter (fun z => c z = 0), f z) +
      (∑ z ∈ Finset.univ.filter (fun z => c z = 1), f z) +
      (∑ z ∈ Finset.univ.filter (fun z => 2 ≤ c z), f z) := by
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun z _ => hpt z)
  have h0 : (∑ z ∈ Finset.univ.filter (fun z => c z = 0), f z) = 0 :=
    Finset.sum_eq_zero (fun z hz0 =>
      Eexp_zero_of_disjoint N p q hp hq A B u z (Finset.mem_filter.mp hz0).2)
  have h1 : (∑ z ∈ Finset.univ.filter (fun z => c z = 1), f z) =
      ((Finset.univ.filter (fun z => c z = 1)).card : ℂ) * f zref := by
    rw [Finset.sum_congr rfl (fun z hz1 => Eexp_eq_of_overlap_eq N p q hp hq A B u z zref
      ((Finset.mem_filter.mp hz1).2.trans hz.symm)), Finset.sum_const, nsmul_eq_mul]
  have hcb : (N.choose p : ℝ) * (N.choose q : ℝ) ≠ 0 := by
    have := Nat.choose_ne_zero hp; have := Nat.choose_ne_zero hq
    positivity
  have hcbC : ((N.choose p : ℂ)⁻¹) * ((N.choose q : ℂ)⁻¹) =
      (((N.choose p : ℝ) * (N.choose q : ℝ))⁻¹ : ℝ) := by
    push_cast; rw [mul_inv]
  refine ⟨(((N.choose p : ℂ)⁻¹) * ((N.choose q : ℂ)⁻¹)) *
    ∑ z ∈ Finset.univ.filter (fun z => 2 ≤ c z), f z, ?_, ?_⟩
  · rw [expect_comm_eq, hsum, h0, h1, zero_add]
    have hc1 : (Finset.univ.filter (fun z => c z = 1)).card =
        N.choose p * (p.choose 1 * (N - p).choose (q - 1)) := card_Z1 hp hq hq1
    have hocf : overlapCoefficient N p q 1 =
        ((p.choose 1 * (N - p).choose (q - 1) : ℕ) : ℝ) / (N.choose q : ℝ) :=
      overlapCoefficient_of_le hq1
    rw [mul_add, hc1, hocf]
    congr 1
    have hq0 : (N.choose q : ℂ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hq
    have hp0 : (N.choose p : ℂ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hp
    push_cast
    field_simp
    rfl
  · rw [norm_mul, hcbC, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hb : ‖∑ z ∈ Finset.univ.filter (fun z => 2 ≤ c z), f z‖ ≤
        ((Finset.univ.filter (fun z => 2 ≤ c z)).card : ℝ) * (2 * (‖A‖ * ‖B‖)) := by
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum (fun z _ => norm_Eexp_le N p q hp hq A B u hu z)).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
    have hc2 : ((Finset.univ.filter (fun z => 2 ≤ c z)).card : ℝ) =
        (N.choose p : ℝ) * ((N.choose q : ℝ) * ∑ s ∈ (Finset.range (q + 1)).filter (fun s => 2 ≤ s),
          overlapCoefficient N p q s) := by
      rw [card_Z2 hp hq]
      push_cast
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun s hs => ?_)
      have hsq : s ≤ q := by
        have := Finset.mem_range.mp (Finset.mem_filter.mp hs).1; omega
      rw [overlapCoefficient_of_le hsq]
      have hq0 : (N.choose q : ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hq
      push_cast
      field_simp
    calc ((N.choose p : ℝ) * (N.choose q : ℝ))⁻¹ * ‖∑ z ∈ Finset.univ.filter (fun z => 2 ≤ c z), f z‖
        ≤ ((N.choose p : ℝ) * (N.choose q : ℝ))⁻¹ *
          (((Finset.univ.filter (fun z => 2 ≤ c z)).card : ℝ) * (2 * (‖A‖ * ‖B‖))) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = 2 * (‖A‖ * ‖B‖) * ∑ s ∈ (Finset.range (q + 1)).filter (fun s => 2 ≤ s),
          overlapCoefficient N p q s := by
        rw [hc2]
        have hcp : (N.choose p : ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hp
        have hcq : (N.choose q : ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hq
        field_simp

end Decomp2

section SA

/-- Inner-product form of self-adjointness of a bounded operator. -/
def IsSA {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] (T : X →L[ℂ] X) : Prop :=
  ∀ x y, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ

theorem adjoint_eq_of_isSA {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [CompleteSpace X] {T : X →L[ℂ] X} (h : IsSA T) : ContinuousLinearMap.adjoint T = T := by
  ext y
  apply ext_inner_left ℂ
  intro x
  exact (ContinuousLinearMap.adjoint_inner_right T x y).trans (h x y)

theorem isSA_of_adjoint_eq {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [CompleteSpace X] {T : X →L[ℂ] X} (h : ContinuousLinearMap.adjoint T = T) : IsSA T := by
  intro x y
  have := ContinuousLinearMap.adjoint_inner_right T x y
  rw [h] at this
  exact this.symm

theorem htmap_isSA {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {S : E →L[ℂ] E} {T : F →L[ℂ] F} (hS : IsSA S) (hT : IsSA T) : IsSA (htmap S T) := by
  apply isSA_of_adjoint_eq
  rw [adjoint_htmap, adjoint_eq_of_isSA hS, adjoint_eq_of_isSA hT]

theorem isSA_extend {r : ℕ} {A : BoundedSymmetricKernel H r} (hA : SelfAdj A) :
    IsSA (extendSymKernel A) := fun x y => extend_selfAdj hA x y

theorem isSA_firstPlacement {p m : ℕ} {A : BoundedSymmetricKernel H p} (hA : SelfAdj A) :
    IsSA (firstPlacement (q := m) A) := by
  intro x y
  unfold firstPlacement
  simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometry.coe_toContinuousLinearMap]
  set e := splitIsometry (𝕜 := ℂ) (E := H) p m with he
  have hM : IsSA (htmap (extendSymKernel A) (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ H m))) :=
    htmap_isSA (isSA_extend hA) (fun x y => rfl)
  calc ⟪e.symm (htmap (extendSymKernel A) (ContinuousLinearMap.id ℂ _) (e x)), y⟫_ℂ
      = ⟪e (e.symm (htmap (extendSymKernel A) (ContinuousLinearMap.id ℂ _) (e x))),
          e y⟫_ℂ := (e.inner_map_map _ _).symm
    _ = ⟪htmap (extendSymKernel A) (ContinuousLinearMap.id ℂ _) (e x), e y⟫_ℂ := by
        rw [e.apply_symm_apply]
    _ = ⟪e x, htmap (extendSymKernel A) (ContinuousLinearMap.id ℂ _) (e y)⟫_ℂ := hM _ _
    _ = _ := by
        have := e.inner_map_map x (e.symm (htmap (extendSymKernel A)
          (ContinuousLinearMap.id ℂ _) (e y)))
        rw [e.apply_symm_apply] at this
        exact this

theorem isSA_midPlacement {p0 q r : ℕ} {B : BoundedSymmetricKernel H q} (hB : SelfAdj B) :
    IsSA (midPlacement p0 q r B) := by
  intro x y
  unfold midPlacement
  simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometry.coe_toContinuousLinearMap]
  set e := splitIsometry (𝕜 := ℂ) (E := H) p0 (q + r) with he
  have hM : IsSA (htmap (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ H p0))
      (firstPlacement (q := r) B)) :=
    htmap_isSA (fun x y => rfl) (isSA_firstPlacement hB)
  calc ⟪e.symm (htmap (ContinuousLinearMap.id ℂ _) (firstPlacement (q := r) B) (e x)), y⟫_ℂ
      = ⟪e (e.symm (htmap (ContinuousLinearMap.id ℂ _) (firstPlacement (q := r) B) (e x))),
          e y⟫_ℂ := (e.inner_map_map _ _).symm
    _ = ⟪htmap (ContinuousLinearMap.id ℂ _) (firstPlacement (q := r) B) (e x), e y⟫_ℂ := by
        rw [e.apply_symm_apply]
    _ = ⟪e x, htmap (ContinuousLinearMap.id ℂ _) (firstPlacement (q := r) B) (e y)⟫_ℂ := hM _ _
    _ = _ := by
        have := e.inner_map_map x (e.symm (htmap (ContinuousLinearMap.id ℂ _)
          (firstPlacement (q := r) B) (e y)))
        rw [e.apply_symm_apply] at this
        exact this

theorem isSA_cast {m n : ℕ} (h : m = n) {T : HilbertTensorPower ℂ H m →L[ℂ] HilbertTensorPower ℂ H m}
    (hT : IsSA T) : IsSA (castTensorOperator h T) := by
  cases h
  exact hT

end SA

section E1

open QuantumNLS.PlacementFiberTransport

theorem isSA_P1 (p' q' r : ℕ) {A : BoundedSymmetricKernel H (p' + 1)} (hA : SelfAdj A) :
    IsSA (rawSubsetPlacement (p' + ((1 + q') + r)) (p' + 1) (hp_can p' q' r)
      (zcan p' q' r).1 A) := by
  unfold rawSubsetPlacement
  rw [subsetPlacement_first (zcan p' q' r).1 rfl A]
  exact isSA_cast _ (isSA_firstPlacement hA)

theorem isSA_P2 (p' q' r : ℕ) {B : BoundedSymmetricKernel H (1 + q')} (hB : SelfAdj B) :
    IsSA (rawSubsetPlacement (p' + ((1 + q') + r)) (1 + q') (hq_can p' q' r)
      (zcan p' q' r).2 B) := by
  unfold rawSubsetPlacement
  rw [rawMid p' (1 + q') r B _ (Nat.add_sub_of_le (hq_can p' q' r)) (zcan p' q' r).2
    (rightSlots_zcan p' q' r)]
  exact isSA_midPlacement hB

theorem Eexp_zcan (p' q' r : ℕ) {A : BoundedSymmetricKernel H (p' + 1)}
    {B : BoundedSymmetricKernel H (1 + q')} (hA : SelfAdj A) (hB : SelfAdj B) (u : H)
    (hu : ‖u‖ = 1) :
    Eexp (p' + ((1 + q') + r)) (p' + 1) (1 + q') (hp_can p' q' r) (hq_can p' q' r) A B u
        (zcan p' q' r) =
      ⟪alphaIns (insA p' u) A u, alphaIns (insB q' u) B u⟫_ℂ -
        (starRingEnd ℂ) ⟪alphaIns (insA p' u) A u, alphaIns (insB q' u) B u⟫_ℂ := by
  set P1 := rawSubsetPlacement (p' + ((1 + q') + r)) (p' + 1) (hp_can p' q' r)
      (zcan p' q' r).1 A with hP1
  set P2 := rawSubsetPlacement (p' + ((1 + q') + r)) (1 + q') (hq_can p' q' r)
      (zcan p' q' r).2 B with hP2
  have h1 : ⟪(htpow (p' + ((1 + q') + r)) u : HilbertTensorPower ℂ H (p' + ((1 + q') + r))),
      (P1.comp P2 - P2.comp P1) (htpow (p' + ((1 + q') + r)) u)⟫_ℂ =
      ⟪P1 (htpow (p' + ((1 + q') + r)) u), P2 (htpow (p' + ((1 + q') + r)) u)⟫_ℂ -
      (starRingEnd ℂ) ⟪P1 (htpow (p' + ((1 + q') + r)) u), P2 (htpow (p' + ((1 + q') + r)) u)⟫_ℂ := by
    rw [ContinuousLinearMap.sub_apply, inner_sub_right, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply]
    have a1 := (isSA_P1 p' q' r hA) (htpow (p' + ((1 + q') + r)) u)
      (P2 (htpow (p' + ((1 + q') + r)) u))
    have a2 := (isSA_P2 p' q' r hB) (htpow (p' + ((1 + q') + r)) u)
      (P1 (htpow (p' + ((1 + q') + r)) u))
    have a3 := inner_conj_symm (𝕜 := ℂ) (P2 (htpow (p' + ((1 + q') + r)) u))
      (P1 (htpow (p' + ((1 + q') + r)) u))
    erw [← a1, ← a2, ← a3]
  unfold Eexp
  show ⟪(htpow (p' + ((1 + q') + r)) u : HilbertTensorPower ℂ H (p' + ((1 + q') + r))),
      (P1.comp P2 - P2.comp P1) (htpow (p' + ((1 + q') + r)) u)⟫_ℂ = _
  rw [h1]
  have := inner_XY p' q' r A B u hu
  rw [hP1, hP2, this]

end E1

section Limit

open Filter Topology QuantumNLS.OverlapMoments

/-- `w = ⟨α, β⟩`. -/
def wAB (p' q' : ℕ) (A : BoundedSymmetricKernel H (p' + 1)) (B : BoundedSymmetricKernel H (1 + q'))
    (u : H) : ℂ :=
  ⟪alphaIns (insA p' u) A u, alphaIns (insB q' u) B u⟫_ℂ

/-- Exact finite-`N` formula: the expectation of the commutator in `u^{⊗N}` is
`c_{N,1}·(⟨α,β⟩ − ⟨β,α⟩) + R_N` with `‖R_N‖ ≤ 2‖A‖‖B‖ Σ_{s≥2} c_{N,s}`. -/
theorem expect_formula (p' q' : ℕ) {A : BoundedSymmetricKernel H (p' + 1)}
    {B : BoundedSymmetricKernel H (1 + q')} (hA : SelfAdj A) (hB : SelfAdj B) (u : H)
    (hu : ‖u‖ = 1) (N : ℕ) (hN : p' + 1 + (1 + q') ≤ N) (hp : p' + 1 ≤ N) (hq : 1 + q' ≤ N) :
    ∃ R : ℂ,
      ⟪(htpow N u : HilbertTensorPower ℂ H N),
        ((((genericU_N_r N (p' + 1) hp A).comp (genericU_N_r N (1 + q') hq B) -
            (genericU_N_r N (1 + q') hq B).comp (genericU_N_r N (p' + 1) hp A))
          ⟨htpow N u, htpow_mem_symSector N u⟩ : SymSector ℂ H N) :
            HilbertTensorPower ℂ H N)⟫_ℂ =
        ((overlapCoefficient N (p' + 1) (1 + q') 1 : ℝ) : ℂ) *
          (wAB p' q' A B u - (starRingEnd ℂ) (wAB p' q' A B u)) + R ∧
      ‖R‖ ≤ 2 * (‖A‖ * ‖B‖) * ∑ s ∈ (Finset.range ((1 + q') + 1)).filter (fun s => 2 ≤ s),
        overlapCoefficient N (p' + 1) (1 + q') s := by
  obtain ⟨r, hr⟩ : ∃ r, N = p' + ((1 + q') + r) := ⟨N - p' - (1 + q'), by omega⟩
  subst hr
  obtain ⟨R, hR1, hR2⟩ := expect_decomp (p' + ((1 + q') + r)) (p' + 1) (1 + q') hp hq
    (by omega) A B u hu (zcan p' q' r) (card_overlap_zcan p' q' r)
  refine ⟨R, ?_, hR2⟩
  rw [hR1]
  congr 2
  exact Eexp_zcan p' q' r hA hB u hu

end Limit

section Limit2

open Filter Topology QuantumNLS.OverlapMoments

theorem append_single_first (q' : ℕ) (u h : H) :
    Fin.append (fun _ : Fin 1 => h) (fun _ : Fin q' => u) =
      Function.update (fun _ : Fin (1 + q') => u) (Fin.castAdd q' 0) h := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simp
  · have : Fin.natAdd 1 k ≠ Fin.castAdd q' (0 : Fin 1) := by
      intro h'; have := congrArg Fin.val h'; simp at this
    simp [Function.update_of_ne this]

theorem pbR_value (p' q' : ℕ) {A : BoundedSymmetricKernel H (p' + 1)}
    {B : BoundedSymmetricKernel H (1 + q')} (hA : SelfAdj A) (hB : SelfAdj B) (u : H) :
    QuantumNLS.SymplecticBracket.pbR (symbolR A) (symbolR B) u =
      2 * (((p' + 1 : ℕ) : ℝ) * ((1 + q' : ℕ) : ℝ)) * (wAB p' q' A B u).im := by
  have := pbR_symbolR (Fin.last p') (Fin.castAdd q' (0 : Fin 1)) hA hB u (insA p' u)
    (fun h => by rw [insA_apply, append_single_last])
    (insB q' u) (fun h => by rw [insB_apply, append_single_first])
  rw [this]; rfl

theorem limit_selfAdj (p' q' : ℕ) {A : BoundedSymmetricKernel H (p' + 1)}
    {B : BoundedSymmetricKernel H (1 + q')} (hA : SelfAdj A) (hB : SelfAdj B) (u : H)
    (hu : ‖u‖ = 1) :
    Tendsto (fun N : ℕ =>
      if h : p' + 1 ≤ N ∧ 1 + q' ≤ N then
        (-Complex.I) * (N : ℂ) *
          ⟪(htpow N u : HilbertTensorPower ℂ H N),
            ((((genericU_N_r N (p' + 1) h.1 A).comp (genericU_N_r N (1 + q') h.2 B) -
                (genericU_N_r N (1 + q') h.2 B).comp (genericU_N_r N (p' + 1) h.1 A))
              ⟨htpow N u, htpow_mem_symSector N u⟩ : SymSector ℂ H N) :
                HilbertTensorPower ℂ H N)⟫_ℂ
      else 0) atTop
      (𝓝 ((QuantumNLS.SymplecticBracket.pbR (symbolR A) (symbolR B) u : ℝ) : ℂ)) := by
  classical
  set w := wAB p' q' A B u with hw
  set K : ℂ := (-Complex.I) * (w - (starRingEnd ℂ) w) with hK
  have hKr : K = ((2 * w.im : ℝ) : ℂ) := by
    rw [hK]
    apply Complex.ext <;> simp [Complex.sub_im, Complex.sub_re] <;> ring
  have hlim1 : Tendsto (fun N : ℕ => (((N : ℝ) * overlapCoefficient N (p' + 1) (1 + q') 1 : ℝ) : ℂ)
      * K) atTop (𝓝 ((((p' + 1 : ℕ) : ℝ) * ((1 + q' : ℕ) : ℝ) : ℝ) * K)) := by
    have := (Complex.continuous_ofReal.tendsto _).comp (tendsto_N_c_one (p' + 1) (1 + q'))
    simpa using this.mul_const K
  set tailS : ℕ → ℝ := fun N => (N : ℝ) * ∑ s ∈ (Finset.range ((1 + q') + 1)).filter (fun s => 2 ≤ s),
    overlapCoefficient N (p' + 1) (1 + q') s with htail
  have hD : Tendsto (fun N : ℕ => (if h : p' + 1 ≤ N ∧ 1 + q' ≤ N then
        (-Complex.I) * (N : ℂ) *
          ⟪(htpow N u : HilbertTensorPower ℂ H N),
            ((((genericU_N_r N (p' + 1) h.1 A).comp (genericU_N_r N (1 + q') h.2 B) -
                (genericU_N_r N (1 + q') h.2 B).comp (genericU_N_r N (p' + 1) h.1 A))
              ⟨htpow N u, htpow_mem_symSector N u⟩ : SymSector ℂ H N) :
                HilbertTensorPower ℂ H N)⟫_ℂ
      else 0) - (((N : ℝ) * overlapCoefficient N (p' + 1) (1 + q') 1 : ℝ) : ℂ) * K)
      atTop (𝓝 0) := by
    have hT := (tendsto_N_tail (p' + 1) (1 + q')).const_mul (2 * (‖A‖ * ‖B‖))
    rw [mul_zero] at hT
    refine squeeze_zero_norm' ?_ hT
    filter_upwards [eventually_ge_atTop (p' + 1 + (1 + q'))] with N hN
    have hp : p' + 1 ≤ N := by omega
    have hq : 1 + q' ≤ N := by omega
    obtain ⟨R, hR1, hR2⟩ := expect_formula p' q' hA hB u hu N hN hp hq
    rw [dif_pos ⟨hp, hq⟩, hR1]
    have : (-Complex.I) * (N : ℂ) * (((overlapCoefficient N (p' + 1) (1 + q') 1 : ℝ) : ℂ) *
        (w - (starRingEnd ℂ) w) + R) -
        (((N : ℝ) * overlapCoefficient N (p' + 1) (1 + q') 1 : ℝ) : ℂ) * K =
        (-Complex.I) * (N : ℂ) * R := by
      rw [hK]; push_cast; ring
    rw [this, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_natCast]
    calc (N : ℝ) * ‖R‖ ≤ (N : ℝ) * (2 * (‖A‖ * ‖B‖) * ∑ s ∈ (Finset.range ((1 + q') + 1)).filter
          (fun s => 2 ≤ s), overlapCoefficient N (p' + 1) (1 + q') s) :=
          mul_le_mul_of_nonneg_left hR2 (Nat.cast_nonneg _)
      _ = 2 * (‖A‖ * ‖B‖) * ((N : ℝ) * ∑ s ∈ (Finset.range ((1 + q') + 1)).filter
          (fun s => 2 ≤ s), overlapCoefficient N (p' + 1) (1 + q') s) := by ring
  have := hD.add hlim1
  simp only [sub_add_cancel, zero_add] at this
  convert this using 2
  rw [pbR_value p' q' hA hB u, hKr]
  push_cast
  ring

end Limit2

section Linear

theorem extendSymKernel_add {r : ℕ} (A B : BoundedSymmetricKernel H r) :
    extendSymKernel (A + B) = extendSymKernel A + extendSymKernel B := by
  ext x; simp [extendSymKernel]

theorem extendSymKernel_smul {r : ℕ} (c : ℂ) (A : BoundedSymmetricKernel H r) :
    extendSymKernel (c • A) = c • extendSymKernel A := by
  ext x; simp [extendSymKernel]

theorem firstPlacement_add {p m : ℕ} (A B : BoundedSymmetricKernel H p) :
    firstPlacement (q := m) (A + B) = firstPlacement (q := m) A + firstPlacement (q := m) B := by
  ext x
  simp only [firstPlacement, extendSymKernel_add, htmap_add_left, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, map_add]

theorem firstPlacement_smul {p m : ℕ} (c : ℂ) (A : BoundedSymmetricKernel H p) :
    firstPlacement (q := m) (c • A) = c • firstPlacement (q := m) A := by
  ext x
  simp only [firstPlacement, extendSymKernel_smul, htmap_smul_left, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, map_smul]

theorem subsetPlacement_add {p m : ℕ} (S : PlacementSubset p m) (A B : BoundedSymmetricKernel H p) :
    subsetPlacement S (A + B) = subsetPlacement S A + subsetPlacement S B := by
  ext x
  simp only [subsetPlacement, permutedPlacement, firstPlacement_add, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, map_add]

theorem subsetPlacement_smul {p m : ℕ} (S : PlacementSubset p m) (c : ℂ)
    (A : BoundedSymmetricKernel H p) :
    subsetPlacement S (c • A) = c • subsetPlacement S A := by
  ext x
  simp only [subsetPlacement, permutedPlacement, firstPlacement_smul, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, map_smul]

theorem castTensorOperator_add {m n : ℕ} (h : m = n)
    (T T' : HilbertTensorPower ℂ H m →L[ℂ] HilbertTensorPower ℂ H m) :
    castTensorOperator h (T + T') = castTensorOperator h T + castTensorOperator h T' := by
  cases h; rfl

theorem castTensorOperator_smul {m n : ℕ} (h : m = n) (c : ℂ)
    (T : HilbertTensorPower ℂ H m →L[ℂ] HilbertTensorPower ℂ H m) :
    castTensorOperator h (c • T) = c • castTensorOperator h T := by
  cases h; rfl

theorem rawSubsetAverage_add (N r : ℕ) (hr : r ≤ N) (A B : BoundedSymmetricKernel H r) :
    rawSubsetAverage N r hr (A + B) = rawSubsetAverage N r hr A + rawSubsetAverage N r hr B := by
  rw [rawSubsetAverage_eq_rawSubsetPlacementSum, rawSubsetAverage_eq_rawSubsetPlacementSum,
    rawSubsetAverage_eq_rawSubsetPlacementSum, ← smul_add]
  congr 1
  unfold rawSubsetPlacementSum rawSubsetPlacement
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [subsetPlacement_add, castTensorOperator_add]

theorem rawSubsetAverage_smul (N r : ℕ) (hr : r ≤ N) (c : ℂ) (A : BoundedSymmetricKernel H r) :
    rawSubsetAverage N r hr (c • A) = c • rawSubsetAverage N r hr A := by
  rw [rawSubsetAverage_eq_rawSubsetPlacementSum, rawSubsetAverage_eq_rawSubsetPlacementSum,
    smul_comm]
  congr 1
  unfold rawSubsetPlacementSum rawSubsetPlacement
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [subsetPlacement_smul, castTensorOperator_smul]

theorem genericU_add (N r : ℕ) (hr : r ≤ N) (A B : BoundedSymmetricKernel H r) :
    genericU_N_r N r hr (A + B) = genericU_N_r N r hr A + genericU_N_r N r hr B := by
  ext x
  rw [coe_genericU, rawSubsetAverage_add]
  simp [coe_genericU]

theorem genericU_smul (N r : ℕ) (hr : r ≤ N) (c : ℂ) (A : BoundedSymmetricKernel H r) :
    genericU_N_r N r hr (c • A) = c • genericU_N_r N r hr A := by
  ext x
  rw [coe_genericU, rawSubsetAverage_smul]
  simp [coe_genericU]

end Linear

section General

open Filter Topology QuantumNLS.OverlapMoments

/-- Real part `(A + A†)/2` of a kernel. -/
def reK {r : ℕ} (A : BoundedSymmetricKernel H r) : BoundedSymmetricKernel H r :=
  (1 / 2 : ℂ) • (A + ContinuousLinearMap.adjoint A)

/-- Imaginary part `(A - A†)/(2i)` of a kernel. -/
def imK {r : ℕ} (A : BoundedSymmetricKernel H r) : BoundedSymmetricKernel H r :=
  (-Complex.I / 2 : ℂ) • (A - ContinuousLinearMap.adjoint A)

theorem reK_imK {r : ℕ} (A : BoundedSymmetricKernel H r) : A = reK A + Complex.I • imK A := by
  have h1 : Complex.I * (-Complex.I / 2) = 1 / 2 := by
    have : Complex.I * (-Complex.I / 2) = -(Complex.I * Complex.I) / 2 := by ring
    rw [this, Complex.I_mul_I]; norm_num
  have h2 : Complex.I • imK A = (1 / 2 : ℂ) • (A - ContinuousLinearMap.adjoint A) := by
    unfold imK; rw [smul_smul, h1]
  rw [h2]
  unfold reK
  module

theorem selfAdj_reK {r : ℕ} (A : BoundedSymmetricKernel H r) : SelfAdj (reK A) := by
  intro x y
  unfold reK
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, inner_smul_left,
    inner_smul_right, inner_add_left, inner_add_right, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]
  simp only [map_div₀, map_one, map_ofNat]
  ring

theorem selfAdj_imK {r : ℕ} (A : BoundedSymmetricKernel H r) : SelfAdj (imK A) := by
  intro x y
  unfold imK
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, inner_smul_left,
    inner_smul_right, inner_sub_left, inner_sub_right, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]
  simp only [map_div₀, map_neg, Complex.conj_I, map_ofNat]
  ring

theorem kps_add_smul {r : ℕ} (A B : BoundedSymmetricKernel H r) (c : ℂ) (v : H) :
    kernelProductSymbol (A + c • B) v = kernelProductSymbol A v + c * kernelProductSymbol B v := by
  simp [kernelProductSymbol, inner_add_right, inner_smul_right]

theorem kps_im_zero {r : ℕ} {A : BoundedSymmetricKernel H r} (hA : SelfAdj A) (v : H) :
    (kernelProductSymbol A v).im = 0 := by
  unfold kernelProductSymbol
  set x : SymSector ℂ H r := ⟨htpow r v, htpow_mem_symSector r v⟩ with hx
  have h1 : ⟪(htpow r v : HilbertTensorPower ℂ H r), ((A x : SymSector ℂ H r) :
      HilbertTensorPower ℂ H r)⟫_ℂ = ⟪x, A x⟫_ℂ := rfl
  rw [h1]
  have h2 := hA x x
  have h3 : (starRingEnd ℂ) ⟪x, A x⟫_ℂ = ⟪A x, x⟫_ℂ := (inner_conj_symm (𝕜 := ℂ) (A x) x)
  rw [h2] at h3
  have := congrArg Complex.im h3
  rw [Complex.conj_im] at this
  linarith

end General

section Final

open Filter Topology QuantumNLS.OverlapMoments

/-- The commutator `[Q_{N,p}(A), Q_{N,q}(B)]` on `Sym^N H`. -/
def CommQ (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N) (A : BoundedSymmetricKernel H p)
    (B : BoundedSymmetricKernel H q) : SymSector ℂ H N →L[ℂ] SymSector ℂ H N :=
  (genericU_N_r N p hp A).comp (genericU_N_r N q hq B) -
    (genericU_N_r N q hq B).comp (genericU_N_r N p hp A)

/-- `⟨u^{⊗N}, [Q_{N,p}(A), Q_{N,q}(B)] u^{⊗N}⟩`. -/
def ExN (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N) (A : BoundedSymmetricKernel H p)
    (B : BoundedSymmetricKernel H q) (u : H) : ℂ :=
  ⟪(htpow N u : HilbertTensorPower ℂ H N),
    ((CommQ N p q hp hq A B ⟨htpow N u, htpow_mem_symSector N u⟩ : SymSector ℂ H N) :
      HilbertTensorPower ℂ H N)⟫_ℂ

theorem CommQ_add_left (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N) (A A' : BoundedSymmetricKernel H p)
    (B : BoundedSymmetricKernel H q) :
    CommQ N p q hp hq (A + A') B = CommQ N p q hp hq A B + CommQ N p q hp hq A' B := by
  unfold CommQ
  rw [genericU_add]
  ext x; simp; abel

theorem CommQ_smul_left (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N) (c : ℂ)
    (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) :
    CommQ N p q hp hq (c • A) B = c • CommQ N p q hp hq A B := by
  unfold CommQ
  rw [genericU_smul]
  ext x; simp [smul_sub]

theorem CommQ_add_right (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N) (A : BoundedSymmetricKernel H p)
    (B B' : BoundedSymmetricKernel H q) :
    CommQ N p q hp hq A (B + B') = CommQ N p q hp hq A B + CommQ N p q hp hq A B' := by
  unfold CommQ
  rw [genericU_add]
  ext x; simp; abel

theorem CommQ_smul_right (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N) (c : ℂ)
    (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) :
    CommQ N p q hp hq A (c • B) = c • CommQ N p q hp hq A B := by
  unfold CommQ
  rw [genericU_smul]
  ext x; simp [smul_sub]

theorem ExN_decomp (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N) (A : BoundedSymmetricKernel H p)
    (B : BoundedSymmetricKernel H q) (u : H) :
    ExN N p q hp hq A B u = ExN N p q hp hq (reK A) (reK B) u +
      Complex.I * ExN N p q hp hq (reK A) (imK B) u +
      Complex.I * ExN N p q hp hq (imK A) (reK B) u -
      ExN N p q hp hq (imK A) (imK B) u := by
  have hA := reK_imK A
  have hB := reK_imK B
  have e : CommQ N p q hp hq A B = CommQ N p q hp hq (reK A) (reK B) +
      Complex.I • CommQ N p q hp hq (reK A) (imK B) +
      Complex.I • CommQ N p q hp hq (imK A) (reK B) -
      CommQ N p q hp hq (imK A) (imK B) := by
    conv_lhs => rw [hA, hB]
    rw [CommQ_add_left, CommQ_add_right, CommQ_add_right, CommQ_smul_left, CommQ_smul_left,
      CommQ_smul_right, CommQ_smul_right]
    have : Complex.I • Complex.I • CommQ N p q hp hq (imK A) (imK B) =
        - CommQ N p q hp hq (imK A) (imK B) := by
      rw [smul_smul, Complex.I_mul_I]; module
    rw [this]
    abel
  unfold ExN
  rw [e]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul,
    inner_sub_right, inner_add_right, inner_smul_right]

end Final

section Final2

open Filter Topology QuantumNLS.OverlapMoments QuantumNLS.SymplecticBracket
attribute [local instance] InnerProductSpace.complexToReal

theorem kps_const_zero {A : BoundedSymmetricKernel H 0} (v : H) :
    kernelProductSymbol A v = kernelProductSymbol A 0 := by
  have h : (htpow 0 v : HilbertTensorPower ℂ H 0) = htpow 0 0 := by
    unfold htpow
    congr 2
    exact Subsingleton.elim _ _
  have key : ∀ (w1 w2 : HilbertTensorPower ℂ H 0) (h1 : w1 ∈ SymSector ℂ H 0)
      (h2 : w2 ∈ SymSector ℂ H 0), w1 = w2 →
      ⟪w1, ((A ⟨w1, h1⟩ : SymSector ℂ H 0) : HilbertTensorPower ℂ H 0)⟫_ℂ =
        ⟪w2, ((A ⟨w2, h2⟩ : SymSector ℂ H 0) : HilbertTensorPower ℂ H 0)⟫_ℂ := by
    rintro _ _ _ _ rfl; rfl
  exact key _ _ _ _ h

theorem gradient_const (c : ℝ) (u : H) :
    QuantumNLS.SymplecticBracket.gradient (fun _ : H => c) u = 0 := by
  unfold QuantumNLS.SymplecticBracket.gradient
  simp

theorem pbR_const_left (c : ℝ) (G : H → ℝ) (u : H) : pbR (fun _ : H => c) G u = 0 := by
  rw [pbR_eq_omega, gradient_const]
  simp [omega]

theorem pbR_const_right (F : H → ℝ) (c : ℝ) (u : H) : pbR F (fun _ : H => c) u = 0 := by
  rw [pbR_eq_omega, gradient_const]
  simp [omega]

theorem pbC_zero_left (F G : H → ℂ) (hF : ∀ v, F v = F 0) (u : H) : pbC F G u = 0 := by
  have h1 : (fun v => (F v).re) = fun _ => (F 0).re := funext fun v => by rw [hF v]
  have h2 : (fun v => (F v).im) = fun _ => (F 0).im := funext fun v => by rw [hF v]
  unfold pbC
  rw [h1, h2]
  apply Complex.ext <;> simp [pbR_const_left]

theorem pbC_zero_right (F G : H → ℂ) (hG : ∀ v, G v = G 0) (u : H) : pbC F G u = 0 := by
  have h1 : (fun v => (G v).re) = fun _ => (G 0).re := funext fun v => by rw [hG v]
  have h2 : (fun v => (G v).im) = fun _ => (G 0).im := funext fun v => by rw [hG v]
  unfold pbC
  rw [h1, h2]
  apply Complex.ext <;> simp [pbR_const_right]

theorem re_kps {r : ℕ} (A : BoundedSymmetricKernel H r) (v : H) :
    (kernelProductSymbol A v).re = symbolR (reK A) v := by
  have h := kps_add_smul (reK A) (imK A) Complex.I v
  rw [← reK_imK A] at h
  have hr := kps_im_zero (selfAdj_reK A) v
  have hi := kps_im_zero (selfAdj_imK A) v
  rw [h]
  simp [symbolR, hr, hi, Complex.mul_re]

theorem im_kps {r : ℕ} (A : BoundedSymmetricKernel H r) (v : H) :
    (kernelProductSymbol A v).im = symbolR (imK A) v := by
  have h := kps_add_smul (reK A) (imK A) Complex.I v
  rw [← reK_imK A] at h
  have hr := kps_im_zero (selfAdj_reK A) v
  have hi := kps_im_zero (selfAdj_imK A) v
  rw [h]
  simp [symbolR, hr, hi, Complex.mul_im]

end Final2

section Final3

open Filter Topology QuantumNLS.OverlapMoments QuantumNLS.SymplecticBracket

/-- `−i N ⟨u^{⊗N}, [Q_{N,p}(A), Q_{N,q}(B)] u^{⊗N}⟩` (set to `0` when `N < max p q`). -/
def limSeq (p q : ℕ) (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) (u : H)
    (N : ℕ) : ℂ :=
  if h : p ≤ N ∧ q ≤ N then (-Complex.I) * (N : ℂ) * ExN N p q h.1 h.2 A B u else 0

theorem ExN_zero_left (N q : ℕ) (hp : 0 ≤ N) (hq : q ≤ N) (A : BoundedSymmetricKernel H 0)
    (B : BoundedSymmetricKernel H q) (u : H) : ExN N 0 q hp hq A B u = 0 := by
  rw [show ExN N 0 q hp hq A B u = _ from expect_comm_eq N 0 q hp hq A B u]
  apply mul_eq_zero_of_right
  refine Finset.sum_eq_zero (fun z _ => Eexp_zero_of_disjoint N 0 q hp hq A B u z ?_)
  have h1 : (leftSlots hp z ∩ rightSlots hq z).card ≤ (leftSlots hp z).card :=
    Finset.card_le_card Finset.inter_subset_left
  rw [card_leftSlots] at h1; omega

theorem ExN_zero_right (N p : ℕ) (hp : p ≤ N) (hq : 0 ≤ N) (A : BoundedSymmetricKernel H p)
    (B : BoundedSymmetricKernel H 0) (u : H) : ExN N p 0 hp hq A B u = 0 := by
  rw [show ExN N p 0 hp hq A B u = _ from expect_comm_eq N p 0 hp hq A B u]
  apply mul_eq_zero_of_right
  refine Finset.sum_eq_zero (fun z _ => Eexp_zero_of_disjoint N p 0 hp hq A B u z ?_)
  have h1 : (leftSlots hp z ∩ rightSlots hq z).card ≤ (rightSlots hq z).card :=
    Finset.card_le_card Finset.inter_subset_right
  rw [card_rightSlots] at h1; omega

/-- **R-32EBD5C1, `eq:root-overlap-limit`.** For fixed `p, q`, all bounded kernels `A, B` and
every unit `u`: `lim_{N→∞} −iN ⟨u^{⊗N}, [Q_{N,p}(A), Q_{N,q}(B)] u^{⊗N}⟩ = {a, b}(u)`, where
`a(v) = ⟨v^{⊗p}, A v^{⊗p}⟩`, `b(v) = ⟨v^{⊗q}, B v^{⊗q}⟩` and `{·,·}` is the DEF-015 complex-bilinear
Poisson bracket `pbC`. -/
theorem root_overlap_limit (p q : ℕ) (A : BoundedSymmetricKernel H p)
    (B : BoundedSymmetricKernel H q) (u : H) (hu : ‖u‖ = 1) :
    Tendsto (limSeq p q A B u) atTop
      (𝓝 (pbC (kernelProductSymbol A) (kernelProductSymbol B) u)) := by
  classical
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · have h0 : limSeq 0 q A B u = fun _ => 0 := by
      funext N
      unfold limSeq
      split_ifs with h
      · rw [ExN_zero_left N q h.1 h.2 A B u]; simp
      · rfl
    rw [h0, pbC_zero_left _ _ (fun v => kps_const_zero v) u]
    exact tendsto_const_nhds
  rcases Nat.eq_zero_or_pos q with rfl | hq0
  · have h0 : limSeq p 0 A B u = fun _ => 0 := by
      funext N
      unfold limSeq
      split_ifs with h
      · rw [ExN_zero_right N p h.1 h.2 A B u]; simp
      · rfl
    rw [h0, pbC_zero_right _ _ (fun v => kps_const_zero v) u]
    exact tendsto_const_nhds
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  obtain ⟨q', rfl⟩ : ∃ q', q = 1 + q' := ⟨q - 1, by omega⟩
  have h11 := limit_selfAdj p' q' (selfAdj_reK A) (selfAdj_reK B) u hu
  have h12 := limit_selfAdj p' q' (selfAdj_reK A) (selfAdj_imK B) u hu
  have h21 := limit_selfAdj p' q' (selfAdj_imK A) (selfAdj_reK B) u hu
  have h22 := limit_selfAdj p' q' (selfAdj_imK A) (selfAdj_imK B) u hu
  have hfun : limSeq (p' + 1) (1 + q') A B u = fun N =>
      limSeq (p' + 1) (1 + q') (reK A) (reK B) u N +
        Complex.I * limSeq (p' + 1) (1 + q') (reK A) (imK B) u N +
        Complex.I * limSeq (p' + 1) (1 + q') (imK A) (reK B) u N -
        limSeq (p' + 1) (1 + q') (imK A) (imK B) u N := by
    funext N
    unfold limSeq
    split_ifs with h
    · rw [ExN_decomp N (p' + 1) (1 + q') h.1 h.2 A B u]
      ring
    · simp
  have e1 : (fun v => (kernelProductSymbol A v).re) = symbolR (reK A) := funext (re_kps A)
  have e2 : (fun v => (kernelProductSymbol A v).im) = symbolR (imK A) := funext (im_kps A)
  have e3 : (fun v => (kernelProductSymbol B v).re) = symbolR (reK B) := funext (re_kps B)
  have e4 : (fun v => (kernelProductSymbol B v).im) = symbolR (imK B) := funext (im_kps B)
  have hlim : pbC (kernelProductSymbol A) (kernelProductSymbol B) u =
      ((pbR (symbolR (reK A)) (symbolR (reK B)) u : ℝ) : ℂ) +
        Complex.I * ((pbR (symbolR (reK A)) (symbolR (imK B)) u : ℝ) : ℂ) +
        Complex.I * ((pbR (symbolR (imK A)) (symbolR (reK B)) u : ℝ) : ℂ) -
        ((pbR (symbolR (imK A)) (symbolR (imK B)) u : ℝ) : ℂ) := by
    unfold pbC
    rw [e1, e2, e3, e4]
    apply Complex.ext <;> simp <;> ring
  rw [hfun, hlim]
  exact ((h11.add (h12.const_mul Complex.I)).add (h21.const_mul Complex.I)).sub h22

end Final3

section Tangential

theorem insA_self (p' : ℕ) (u : H) : insA p' u u = (htpow (p' + 1) u : HilbertTensorPower ℂ H (p' + 1)) := by
  rw [insA_apply, append_single_last, Function.update_eq_self]
  rfl

theorem insB_self (q' : ℕ) (u : H) : insB q' u u = (htpow (1 + q') u : HilbertTensorPower ℂ H (1 + q')) := by
  rw [insB_apply, append_single_first, Function.update_eq_self]
  rfl

theorem alphaA_radial_real (p' : ℕ) {A : BoundedSymmetricKernel H (p' + 1)} (hA : SelfAdj A) (u : H) :
    (⟪u, alphaIns (insA p' u) A u⟫_ℂ).im = 0 := by
  unfold alphaIns
  have h : ⟪u, ContinuousLinearMap.adjoint (insA p' u)
      ((A ⟨htpow (p' + 1) u, htpow_mem_symSector (p' + 1) u⟩ : SymSector ℂ H (p' + 1)) :
        HilbertTensorPower ℂ H (p' + 1))⟫_ℂ = kernelProductSymbol A u := by
    rw [ContinuousLinearMap.adjoint_inner_right, insA_self]; rfl
  rw [h]
  exact kps_im_zero hA u

theorem alphaB_radial_real (q' : ℕ) {B : BoundedSymmetricKernel H (1 + q')} (hB : SelfAdj B) (u : H) :
    (⟪u, alphaIns (insB q' u) B u⟫_ℂ).im = 0 := by
  unfold alphaIns
  have h : ⟪u, ContinuousLinearMap.adjoint (insB q' u)
      ((B ⟨htpow (1 + q') u, htpow_mem_symSector (1 + q') u⟩ : SymSector ℂ H (1 + q')) :
        HilbertTensorPower ℂ H (1 + q'))⟫_ℂ = kernelProductSymbol B u := by
    rw [ContinuousLinearMap.adjoint_inner_right, insB_self]; rfl
  rw [h]
  exact kps_im_zero hB u

/-- The reduction used in the printed proof: removing the radial components of the contractions
does not change `Im ⟨α, β⟩` when `⟨u,α⟩` and `⟨u,β⟩` are real (self-adjoint kernels, unit `u`). -/
theorem im_inner_tangential (u α β : H) (hu : ‖u‖ = 1) (ha : (⟪u, α⟫_ℂ).im = 0)
    (hb : (⟪u, β⟫_ℂ).im = 0) :
    (⟪α - ⟪u, α⟫_ℂ • u, β - ⟪u, β⟫_ℂ • u⟫_ℂ).im = (⟪α, β⟫_ℂ).im := by
  have huu : ⟪u, u⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hu]; norm_num
  have hcα : (starRingEnd ℂ) ⟪u, α⟫_ℂ = ⟪α, u⟫_ℂ := inner_conj_symm α u
  have e : ⟪α - ⟪u, α⟫_ℂ • u, β - ⟪u, β⟫_ℂ • u⟫_ℂ =
      ⟪α, β⟫_ℂ - (starRingEnd ℂ) ⟪u, α⟫_ℂ * ⟪u, β⟫_ℂ := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_smul_left, inner_smul_right,
      inner_smul_left, inner_smul_right, huu, ← hcα]
    ring
  rw [e, Complex.sub_im]
  have : ((starRingEnd ℂ) ⟪u, α⟫_ℂ * ⟪u, β⟫_ℂ).im = 0 := by
    rw [Complex.mul_im, Complex.conj_re, Complex.conj_im, ha, hb]; ring
  rw [this]; ring

/-- For self-adjoint kernels the printed bracket formula is unchanged by removing the radial parts:
`{a,b}(u) = 2pq Im⟨α_⊥, β_⊥⟩` with `α_⊥ = α − ⟨u,α⟩u`, `β_⊥ = β − ⟨u,β⟩u`. -/
theorem pbR_tangential (p' q' : ℕ) {A : BoundedSymmetricKernel H (p' + 1)}
    {B : BoundedSymmetricKernel H (1 + q')} (hA : SelfAdj A) (hB : SelfAdj B) (u : H)
    (hu : ‖u‖ = 1) :
    QuantumNLS.SymplecticBracket.pbR (symbolR A) (symbolR B) u =
      2 * (((p' + 1 : ℕ) : ℝ) * ((1 + q' : ℕ) : ℝ)) *
        (⟪alphaIns (insA p' u) A u - ⟪u, alphaIns (insA p' u) A u⟫_ℂ • u,
          alphaIns (insB q' u) B u - ⟪u, alphaIns (insB q' u) B u⟫_ℂ • u⟫_ℂ).im := by
  rw [im_inner_tangential u _ _ hu (alphaA_radial_real p' hA u) (alphaB_radial_real q' hB u)]
  exact pbR_value p' q' hA hB u

end Tangential

#print axioms pbR_tangential


#print axioms root_overlap_limit
#print axioms limit_selfAdj
#print axioms gradient_symbolR
#print axioms pbR_symbolR
#print axioms inner_XY
#print axioms Eexp_eq_of_overlap_eq
#print axioms expect_decomp

end QuantumNLS.RootOverlapLimit
