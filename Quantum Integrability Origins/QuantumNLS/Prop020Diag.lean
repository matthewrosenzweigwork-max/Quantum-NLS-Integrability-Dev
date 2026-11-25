import QuantumNLS.MPOps

/-!
# PROP-020 (`Q7A:thm:main`), input 1: the operators of the window reconstruction act diagonally on joint eigenvectors

Generic complex Hilbert space. Used to identify, on the actual Bethe vectors, the bounded operators of the PROP-026 chain
(`MPOps.C0op = Re ∫ u_θ f_θ(S_θ) dν`, `MPOps.Lop = Re ∫ u_θ d_θ S_θ dν`, the evolutions `evol`) with the eigenvalue
expressions of PROP-018 (`Prop018Phase.C0ev`), as the source does ("these are bounded self-adjoint operators ... All the
operators commute with each other and with all actual charges", `window_reconstruction.tex`, after `Q7A:eq:scalar`).

* `star_eigen`: a normal `N` with `N v = μ v` has `N^* v = μ̄ v`;
* `cfcHom_eigen`, `cfc_eigen`: **the continuous functional calculus on an eigenvector**: for normal `T` with `T v = μ v`,
  `v ≠ 0`, and `g` continuous on the spectrum, `cfc g T v = g(μ) v` (the set of `f` with `cfcHom f v = f(μ) v` is a closed
  star subalgebra containing `id`; Stone–Weierstrass);
* `exp_eigen`, `evol_eigen`: `e^{X} v = e^{μ} v` and `evol T t v = e^{−itμ} v`; `evol_isometry` for self-adjoint `T`;
* `reOp_smul_eigen`, `C0op_eigen`, `Lop_eigen`: `C0op ν S u g v = (∫ Re(u_θ g_θ(λ_θ)) dν) v` and
  `Lop ν S u d v = (∫ Re(u_θ d_θ λ_θ) dν) v` for a family of normal `S_θ` with `S_θ v = λ_θ v`;
* `reducedDensityPower_phase`: a unimodular phase does not change the reduced density.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace QuantumNLS.Prop020Diag

open QuantumNLS.MixedQuadratures (reOp adjSL integral_reOp norm_adjoint_apply_eq)
open QuantumNLS.MPOps (C0op Lop)
open QuantumNLS.FunctionalLinearization (evol)

section Generic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- For a normal `N` with `N v = μ v`: `N^* v = μ̄ v`. -/
theorem star_eigen {N : H →L[ℂ] H} (hN : IsStarNormal N) {v : H} {μ : ℂ}
    (hv : N v = μ • v) : star N v = (starRingEnd ℂ μ) • v := by
  set M := N - algebraMap ℂ (H →L[ℂ] H) μ with hMdef
  have hM' : Commute (star M) M := by
    rw [hMdef, star_sub, ← algebraMap_star_comm]
    refine Commute.sub_left ?_ ?_
    · exact hN.star_comm_self.sub_right (Algebra.commute_algebraMap_right _ _)
    · exact Algebra.commute_algebraMap_left _ _
  have hM : Commute (ContinuousLinearMap.adjoint M) M := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact hM'
  have h0 : M v = 0 := by
    rw [hMdef, sub_apply, Algebra.algebraMap_eq_smul_one, smul_apply, one_apply_eq_self, hv, sub_self]
  have h1 := norm_adjoint_apply_eq M hM v
  rw [h0, norm_zero, norm_eq_zero, ← ContinuousLinearMap.star_eq_adjoint, hMdef, star_sub,
    ← algebraMap_star_comm, sub_apply, Algebra.algebraMap_eq_smul_one, smul_apply, one_apply_eq_self,
    sub_eq_zero] at h1
  exact h1

/-- **The continuous functional calculus on an eigenvector** (homomorphism form). -/
theorem cfcHom_eigen {T : H →L[ℂ] H} (hT : IsStarNormal T) {v : H} {μ : ℂ} (hv : T v = μ • v)
    (hμ : μ ∈ spectrum ℂ T) (f : C(spectrum ℂ T, ℂ)) : cfcHom hT f v = f ⟨μ, hμ⟩ • v := by
  let V : StarSubalgebra ℂ C(spectrum ℂ T, ℂ) :=
    { carrier := {f | cfcHom hT f v = f ⟨μ, hμ⟩ • v}
      mul_mem' := fun {f g} hf hg => by
        simp only [Set.mem_ofPred_eq] at hf hg ⊢
        rw [map_mul]
        change cfcHom hT f (cfcHom hT g v) = _
        rw [hg, map_smul, hf, smul_smul, ContinuousMap.mul_apply, mul_comm]
      add_mem' := fun {f g} hf hg => by
        simp only [Set.mem_ofPred_eq] at hf hg ⊢
        rw [map_add, add_apply, hf, hg, ContinuousMap.add_apply, add_smul]
      algebraMap_mem' := fun c => by
        simp only [Set.mem_ofPred_eq]
        rw [AlgHomClass.commutes, Algebra.algebraMap_eq_smul_one, smul_apply, one_apply_eq_self]
        simp [Algebra.algebraMap_eq_smul_one]
      star_mem' := fun {f} hf => by
        simp only [Set.mem_ofPred_eq] at hf ⊢
        rw [map_star]
        have hn : IsStarNormal (cfcHom hT f) := by
          refine ⟨?_⟩
          rw [← map_star]
          exact (Commute.all (star f) f).map (cfcHom hT)
        rw [star_eigen hn hf]
        rfl }
  have hid : ContinuousMap.restrict (spectrum ℂ T) (ContinuousMap.id ℂ) ∈ V := by
    show cfcHom hT _ v = _
    rw [cfcHom_id hT, hv]; rfl
  have hclosed : IsClosed (V : Set C(spectrum ℂ T, ℂ)) := by
    have hc1 : Continuous fun f : C(spectrum ℂ T, ℂ) => cfcHom hT f v :=
      (ContinuousLinearMap.apply ℂ H v).continuous.comp (cfcHom_continuous hT)
    have hc2 : Continuous fun f : C(spectrum ℂ T, ℂ) => f ⟨μ, hμ⟩ • v :=
      (continuous_eval_const _).smul continuous_const
    exact isClosed_eq hc1 hc2
  have hX : (Polynomial.toContinuousMapOnAlgHom (spectrum ℂ T)) Polynomial.X =
      ContinuousMap.restrict (spectrum ℂ T) (ContinuousMap.id ℂ) := by
    ext x; simp
  have hpoly : polynomialFunctions (spectrum ℂ T) ≤ V.toSubalgebra := by
    rw [polynomialFunctions.eq_adjoin_X, Algebra.adjoin_le_iff, Set.singleton_subset_iff, hX]
    exact hid
  have htop := polynomialFunctions.starClosure_topologicalClosure (𝕜 := ℂ) (spectrum ℂ T)
  have hle : (polynomialFunctions (spectrum ℂ T)).starClosure.topologicalClosure ≤ V :=
    StarSubalgebra.topologicalClosure_minimal (Subalgebra.starClosure_le_iff.2 hpoly) hclosed
  rw [htop] at hle
  exact hle (Set.mem_univ f)

theorem mem_spectrum_of_eigen {T : H →L[ℂ] H} {v : H} {μ : ℂ} (hv : T v = μ • v) (hv0 : v ≠ 0) :
    μ ∈ spectrum ℂ T := by
  rw [spectrum.mem_iff]
  intro hu
  apply hv0
  have h0 : (algebraMap ℂ (H →L[ℂ] H) μ - T) v = 0 := by
    rw [sub_apply, Algebra.algebraMap_eq_smul_one, smul_apply, one_apply_eq_self, hv, sub_self]
  obtain ⟨u, hu'⟩ := hu
  have h1 : v = ((↑u⁻¹ : H →L[ℂ] H) * ↑u) v := by rw [Units.inv_mul]; rfl
  rw [h1]
  change (↑u⁻¹ : H →L[ℂ] H) ((↑u : H →L[ℂ] H) v) = 0
  rw [hu', h0, map_zero]

/-- **`cfc g T v = g(μ) v`** for a normal `T`, an eigenvector `v ≠ 0` and `g` continuous on the spectrum. -/
theorem cfc_eigen {T : H →L[ℂ] H} (hT : IsStarNormal T) {v : H} {μ : ℂ} (hv : T v = μ • v) (hv0 : v ≠ 0)
    (g : ℂ → ℂ) (hg : ContinuousOn g (spectrum ℂ T)) : cfc g T v = g μ • v := by
  rw [cfc_apply g T hT hg, cfcHom_eigen hT hv (mem_spectrum_of_eigen hv hv0)]
  rfl

theorem pow_eigen (X : H →L[ℂ] H) {v : H} {μ : ℂ} (hv : X v = μ • v) (n : ℕ) : (X ^ n) v = μ ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change X ((X ^ n) v) = _
    rw [ih, map_smul, hv, smul_smul, pow_succ, mul_comm]

theorem exp_eigen (X : H →L[ℂ] H) {v : H} {μ : ℂ} (hv : X v = μ • v) :
    NormedSpace.exp X v = Complex.exp μ • v := by
  rw [NormedSpace.exp_eq_tsum ℂ, Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum ℂ]
  have hs := NormedSpace.expSeries_summable' (𝕂 := ℂ) X
  have h1 := (ContinuousLinearMap.apply ℂ H v).map_tsum hs
  simp only [ContinuousLinearMap.apply_apply] at h1
  show (∑' n : ℕ, ((n.factorial : ℂ)⁻¹ • X ^ n)) v = _
  rw [h1]
  simp only [smul_apply, pow_eigen X hv, smul_smul]
  rw [← Summable.tsum_smul_const (NormedSpace.expSeries_summable' (𝕂 := ℂ) μ)]
  rfl

variable [Nontrivial H]

/-- `evol T t v = e^{−itμ} v` on an eigenvector. -/
theorem evol_eigen (T : H →L[ℂ] H) {v : H} {μ : ℂ} (hv : T v = μ • v) (t : ℝ) :
    evol T t v = Complex.exp (-(t : ℂ) * (Complex.I * μ)) • v := by
  unfold evol
  refine exp_eigen _ ?_
  rw [smul_apply, smul_apply, hv, smul_smul, ← Complex.coe_smul, smul_smul]
  push_cast
  ring_nf

/-- `evol T t` is an isometry for self-adjoint `T`. -/
theorem evol_isometry (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (t : ℝ) (x : H) : ‖evol T t x‖ = ‖x‖ := by
  have hsa : IsSelfAdjoint ((-t : ℂ) • T) := by
    refine IsSelfAdjoint.smul ?_ hT
    simp [IsSelfAdjoint, Complex.conj_ofReal]
  set U := selfAdjoint.expUnitary ⟨(-t : ℂ) • T, hsa⟩
  have hU : (U : H →L[ℂ] H) = evol T t := by
    rw [selfAdjoint.expUnitary_coe]
    unfold evol
    congr 1
    rw [← Complex.coe_smul]
    show Complex.I • ((-t : ℂ) • T) = _
    rw [smul_smul, smul_smul]; push_cast; ring_nf
  rw [← hU]
  exact Unitary.norm_map U x

end Generic

section Ops

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `Re(c X) v = Re(cμ) v` for a normal `X` with `X v = μ v`. -/
theorem reOp_smul_eigen {X : H →L[ℂ] H} (hX : IsStarNormal X) {v : H} {μ : ℂ} (hv : X v = μ • v) (c : ℂ) :
    reOp (c • X) v = (((c * μ).re : ℝ) : ℂ) • v := by
  have hs := star_eigen hX hv
  rw [ContinuousLinearMap.star_eq_adjoint] at hs
  unfold reOp
  rw [smul_apply, add_apply, map_smulₛₗ, smul_apply, smul_apply, hv, hs, smul_smul, smul_smul, ← add_smul,
    smul_smul]
  congr 1
  rw [Complex.re_eq_add_conj]
  simp only [map_mul]
  ring

variable {Θ : Type*} [MeasurableSpace Θ]

/-- **`C0op` on a joint eigenvector**: `C0op ν S u g v = (∫ Re(u_θ g_θ(λ_θ)) dν) v`. -/
theorem C0op_eigen (ν : Measure Θ) (S : Θ → H →L[ℂ] H) (hS : ∀ θ, IsStarNormal (S θ)) (u : Θ → ℂ)
    (g : Θ → ℂ → ℂ) (hg : ∀ θ, Continuous (g θ)) (hint : Integrable (fun θ => u θ • cfc (g θ) (S θ)) ν)
    {v : H} (hv0 : v ≠ 0) (lam : Θ → ℂ) (hv : ∀ θ, S θ v = lam θ • v) :
    C0op ν S u g v = (((∫ θ, (u θ * g θ (lam θ)).re ∂ν : ℝ)) : ℂ) • v := by
  unfold C0op
  rw [← integral_reOp ν hint]
  have hint' : Integrable (fun θ => reOp (u θ • cfc (g θ) (S θ))) ν := by
    unfold reOp
    exact (hint.add (adjSL.integrable_comp hint)).smul (1 / 2 : ℂ)
  rw [ContinuousLinearMap.integral_apply hint']
  have hpt : ∀ θ, reOp (u θ • cfc (g θ) (S θ)) v = (((u θ * g θ (lam θ)).re : ℝ) : ℂ) • v := by
    intro θ
    have hn : IsStarNormal (cfc (g θ) (S θ)) := by
      refine ⟨?_⟩
      rw [← cfc_star]
      exact cfc_commute_cfc _ _ _
    exact reOp_smul_eigen hn (cfc_eigen (hS θ) (hv θ) hv0 (g θ) (hg θ).continuousOn) (u θ)
  simp_rw [hpt]
  rw [integral_smul_const, integral_complex_ofReal]

/-- **`Lop` on a joint eigenvector**: `Lop ν S u d v = (∫ Re(u_θ d_θ λ_θ) dν) v`. -/
theorem Lop_eigen (ν : Measure Θ) (S : Θ → H →L[ℂ] H) (hS : ∀ θ, IsStarNormal (S θ)) (u d : Θ → ℂ)
    (hint : Integrable (fun θ => (u θ * d θ) • S θ) ν)
    {v : H} (lam : Θ → ℂ) (hv : ∀ θ, S θ v = lam θ • v) :
    Lop ν S u d v = (((∫ θ, (u θ * d θ * lam θ).re ∂ν : ℝ)) : ℂ) • v := by
  unfold Lop
  rw [← integral_reOp ν hint]
  have hint' : Integrable (fun θ => reOp ((u θ * d θ) • S θ)) ν := by
    unfold reOp
    exact (hint.add (adjSL.integrable_comp hint)).smul (1 / 2 : ℂ)
  rw [ContinuousLinearMap.integral_apply hint']
  simp_rw [fun θ => reOp_smul_eigen (hS θ) (hv θ) (u θ * d θ)]
  rw [integral_smul_const, integral_complex_ofReal]

end Ops

/-! ## The phase invariance of reduced densities -/

section Phase

open QuantumNLS.TensorCarrier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem reducedDensity_phase {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (ψ : HilbertTensor ℂ X Y) {c : ℂ} (hc : ‖c‖ = 1) : reducedDensity (c • ψ) = reducedDensity ψ := by
  ext1 φ
  refine ext_inner_right ℂ fun φ' => ?_
  rw [inner_reducedDensity_left, inner_reducedDensity_left, map_smul, inner_smul_left, inner_smul_right,
    ← mul_assoc, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hc]
  simp

theorem reducedDensityPower_phase (k m : ℕ) (ψ : HilbertTensorPower ℂ E (k + m)) {c : ℂ} (hc : ‖c‖ = 1) :
    reducedDensityPower k m (c • ψ) = reducedDensityPower k m ψ := by
  unfold reducedDensityPower
  rw [map_smul, reducedDensity_phase _ hc]

end Phase

end QuantumNLS.Prop020Diag

#print axioms QuantumNLS.Prop020Diag.cfc_eigen
#print axioms QuantumNLS.Prop020Diag.evol_eigen
#print axioms QuantumNLS.Prop020Diag.evol_isometry
#print axioms QuantumNLS.Prop020Diag.C0op_eigen
#print axioms QuantumNLS.Prop020Diag.Lop_eigen
#print axioms QuantumNLS.Prop020Diag.reducedDensityPower_phase
