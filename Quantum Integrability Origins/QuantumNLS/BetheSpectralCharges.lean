import QuantumNLS.BetheConditionalBasis
import QuantumNLS.DiagonalMultiplier

/-! DEF-008, definitions.tex:49. Maximal spectral multiplication, on all
occupation labels. Only the actual interacting complete-basis instantiation
uses BCB1's explicit AbstractContinuity premise. No local differential
operator identification is asserted for the higher charges. -/
noncomputable section
open scoped BigOperators InnerProductSpace NNReal
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.BetheSpectralCharges
open BetheLabels BetheCoefficientTransform PhysicalTensor
local instance (α : Type) : DecidableEq α := Classical.decEq α

variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-- The real rapidities, in the frozen source enumeration (no sign change). -/
def rapidity (L : ℝ) (N : ℕ) (c : ℝ) (m : MArr N) (j : Fin N) : ℝ :=
  BetheSmooth.sourceRoots L ((BetheConditionalBasis.labelArr N).symm m).val c j

/-- All orders, including order zero, with its value N. -/
def eigenvalue (L : ℝ) (N : ℕ) (c : ℝ) (r : ℕ) (m : MArr N) : ℝ :=
  ∑ j, rapidity L N c m j ^ r

theorem eigenvalue_zero (L : ℝ) (N : ℕ) (c : ℝ) (m : MArr N) :
    eigenvalue L N c 0 m = N := by simp [eigenvalue]

/-- The exact maximal domain; square summability is imposed only AFTER
multiplying by the full symbol, permitting cancellations in combinations. -/
def domain (b : BetheBasis L N) (ev : MArr N → ℝ) : Submodule ℂ (HN L N) where
  carrier := {ψ | Memℓp (fun m => (ev m : ℂ) * b.repr ψ m) 2}
  zero_mem' := by
    change Memℓp (fun m => (ev m : ℂ) * b.repr 0 m) 2
    convert (zero_memℓp : Memℓp (0 : MArr N → ℂ) 2) using 1
    funext m
    simp
  add_mem' := by
    intro ψ φ hψ hφ
    change Memℓp (fun m => (ev m : ℂ) * b.repr (ψ + φ) m) 2
    rw [b.repr.map_add]
    convert hψ.add hφ using 1
    funext m
    change (ev m : ℂ) * (b.repr ψ m + b.repr φ m) = _
    exact mul_add _ _ _
  smul_mem' := by
    intro a ψ hψ
    change Memℓp (fun m => (ev m : ℂ) * b.repr (a • ψ) m) 2
    simpa only [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm] using hψ.const_mul a

/-- Literal weighted-square domain criterion. Summable nonnegative terms
means that the nonnegative series is finite, rather than Lean's default
value for a divergent real tsum. -/
theorem mem_domain (b : BetheBasis L N) (ev : MArr N → ℝ) (ψ : HN L N) :
    ψ ∈ domain b ev ↔ Summable (fun m => |ev m| ^ 2 * ‖⟪b m, ψ⟫_ℂ‖ ^ 2) := by
  change Memℓp _ 2 ↔ _
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, HilbertBasis.repr_apply_apply]

/-- A partial linear operator with precisely the maximal domain. -/
def multiplier (b : BetheBasis L N) (ev : MArr N → ℝ) : HN L N →ₗ.[ℂ] HN L N where
  domain := domain b ev
  toFun :=
    { toFun := fun ψ => b.repr.symm ⟨fun m => (ev m : ℂ) * b.repr ψ.val m, ψ.property⟩
      map_add' := by
        intro ψ φ
        apply b.repr.injective
        rw [b.repr.map_add, LinearIsometryEquiv.apply_symm_apply,
          LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
        ext m
        change (ev m : ℂ) * b.repr (ψ.val + φ.val) m =
          (ev m : ℂ) * b.repr ψ.val m + (ev m : ℂ) * b.repr φ.val m
        rw [b.repr.map_add]
        exact mul_add _ _ _
      map_smul' := by
        intro a ψ
        apply b.repr.injective
        ext m
        simp [mul_left_comm] }

theorem multiplier_coord (b : BetheBasis L N) (ev : MArr N → ℝ)
    (ψ : (multiplier b ev).domain) (m : MArr N) :
    ⟪b m, multiplier b ev ψ⟫_ℂ = (ev m : ℂ) * ⟪b m, (ψ : HN L N)⟫_ℂ := by
  rw [← HilbertBasis.repr_apply_apply]
  change b.repr (b.repr.symm _) m = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  change (ev m : ℂ) * b.repr ψ.val m = _
  rw [HilbertBasis.repr_apply_apply]

/-- Existence and uniqueness of the vector with multiplied coordinates
characterizes domain membership in both directions. -/
theorem maximal (b : BetheBasis L N) (ev : MArr N → ℝ) (ψ : HN L N) :
    ψ ∈ (multiplier b ev).domain ↔
      ∃! φ : HN L N, ∀ m, ⟪b m, φ⟫_ℂ = (ev m : ℂ) * ⟪b m, ψ⟫_ℂ := by
  constructor
  · intro h
    refine ⟨multiplier b ev ⟨ψ, h⟩, fun m => multiplier_coord b ev ⟨ψ,h⟩ m, ?_⟩
    intro φ hφ
    apply b.repr.injective
    ext m
    simpa only [HilbertBasis.repr_apply_apply] using (hφ m).trans (multiplier_coord b ev ⟨ψ,h⟩ m).symm
  · rintro ⟨φ, hφ, _⟩
    change Memℓp _ 2
    have heq : (fun m => (ev m : ℂ) * b.repr ψ m) = (fun m => b.repr φ m) := by
      funext m
      simpa only [HilbertBasis.repr_apply_apply] using (hφ m).symm
    rw [heq]
    exact lp.memℓp _

theorem basis_mem_domain (b : BetheBasis L N) (ev : MArr N → ℝ) (m : MArr N) :
    b m ∈ (multiplier b ev).domain := by
  apply (maximal b ev (b m)).mpr
  refine ⟨(ev m : ℂ) • b m, ?_, ?_⟩
  · intro k
    simp only [inner_smul_right]
    by_cases h : k = m
    · subst k; rfl
    · rw [b.orthonormal.inner_eq_zero h]
      simp
  · intro φ hφ
    apply b.repr.injective
    ext k
    simp only [HilbertBasis.repr_apply_apply]
    rw [hφ k, inner_smul_right]
    by_cases h : k = m
    · subst k; rfl
    · rw [b.orthonormal.inner_eq_zero h]; simp

theorem multiplier_basis (b : BetheBasis L N) (ev : MArr N → ℝ) (m : MArr N) :
    multiplier b ev ⟨b m, basis_mem_domain b ev m⟩ = (ev m : ℂ) • b m := by
  apply b.repr.injective
  ext k
  simp only [HilbertBasis.repr_apply_apply]
  rw [multiplier_coord, inner_smul_right]
  by_cases h : k = m
  · subst k; rfl
  · rw [b.orthonormal.inner_eq_zero h]; simp

theorem domain_dense (b : BetheBasis L N) (ev : MArr N → ℝ) :
    (multiplier b ev).domain.topologicalClosure = ⊤ := by
  apply top_unique
  rw [← b.dense_span]
  exact Submodule.topologicalClosure_mono (Submodule.span_le.mpr (by
    rintro _ ⟨m, rfl⟩; exact basis_mem_domain b ev m))

theorem constant_domain (b : BetheBasis L N) (a : ℝ) :
    (multiplier b (fun _ => a)).domain = ⊤ := by
  apply top_unique
  intro ψ _
  exact (lp.memℓp (b.repr ψ)).const_mul (a : ℂ)

theorem constant_apply (b : BetheBasis L N) (a : ℝ) (ψ : HN L N)
    (h : ψ ∈ (multiplier b (fun _ => a)).domain) :
    multiplier b (fun _ => a) ⟨ψ,h⟩ = (a : ℂ) • ψ := by
  apply b.repr.injective
  ext m
  simpa only [HilbertBasis.repr_apply_apply, inner_smul_right] using multiplier_coord b (fun _ => a) ⟨ψ,h⟩ m

/-- Spectral Q_{N,r}; order zero is literally N Id on the full space. -/
def charge (b : BetheBasis L N) (c : ℝ) (r : ℕ) : HN L N →ₗ.[ℂ] HN L N :=
  multiplier b (eigenvalue L N c r)

theorem charge_zero_domain (b : BetheBasis L N) (c : ℝ) :
    (charge b c 0).domain = ⊤ := by
  have he : eigenvalue L N c 0 = fun _ => (N : ℝ) := funext (eigenvalue_zero L N c)
  rw [charge, he]
  exact constant_domain b (N : ℝ)

theorem charge_zero_apply (b : BetheBasis L N) (c : ℝ) (ψ : (charge b c 0).domain) :
    charge b c 0 ψ = (N : ℂ) • (ψ : HN L N) := by
  unfold charge at ψ ⊢
  have h := multiplier_coord b (eigenvalue L N c 0)
    (⟨ψ.val, ψ.property⟩ : (multiplier b (eigenvalue L N c 0)).domain)
  apply b.repr.injective
  ext m
  simpa only [HilbertBasis.repr_apply_apply, inner_smul_right, eigenvalue_zero,
    Complex.ofReal_natCast] using h m


/-- A real polynomial in rapidity, equivalently a finite real combination
of charges, is multiplied as a single symbol on its own maximal domain. -/
def polynomialSymbol (L : ℝ) (N : ℕ) (c : ℝ) (p : Polynomial ℝ) (m : MArr N) : ℝ :=
  ∑ j, p.eval (rapidity L N c m j)

theorem polynomialSymbol_eq (L : ℝ) (N : ℕ) (c : ℝ) (p : Polynomial ℝ) (m : MArr N) :
    polynomialSymbol L N c p m = ∑ r ∈ p.support, p.coeff r * eigenvalue L N c r m := by
  simp only [polynomialSymbol, Polynomial.eval_eq_sum, Polynomial.sum, eigenvalue]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.mul_sum]

def polynomialCharge (b : BetheBasis L N) (c : ℝ) (p : Polynomial ℝ) : HN L N →ₗ.[ℂ] HN L N :=
  multiplier b (polynomialSymbol L N c p)

/-- Arbitrary real joint polynomial in finitely many selected charge orders.
The domain is imposed on the evaluated symbol, never on separate factors. -/
def jointPolynomialSymbol (L : ℝ) (N : ℕ) (c : ℝ) (d : ℕ) (orders : Fin d → ℕ)
    (p : MvPolynomial (Fin d) ℝ) (m : MArr N) : ℝ :=
  MvPolynomial.eval (fun i => eigenvalue L N c (orders i) m) p

def jointPolynomialCharge (b : BetheBasis L N) (c : ℝ) (d : ℕ) (orders : Fin d → ℕ)
    (p : MvPolynomial (Fin d) ℝ) : HN L N →ₗ.[ℂ] HN L N :=
  multiplier b (jointPolynomialSymbol L N c d orders p)

theorem jointPolynomial_domain (b : BetheBasis L N) (c : ℝ) (d : ℕ) (orders : Fin d → ℕ)
    (p : MvPolynomial (Fin d) ℝ) (ψ : HN L N) :
    ψ ∈ (jointPolynomialCharge b c d orders p).domain ↔
      Summable (fun m => |jointPolynomialSymbol L N c d orders p m| ^ 2 * ‖⟪b m, ψ⟫_ℂ‖ ^ 2) :=
  mem_domain b _ ψ

/-- The displayed spectral series converges in the physical Hilbert norm. -/
theorem multiplier_expansion (b : BetheBasis L N) (ev : MArr N → ℝ)
    (ψ : (multiplier b ev).domain) :
    HasSum (fun m => ((ev m : ℂ) * ⟪b m, (ψ : HN L N)⟫_ℂ) • b m)
      (multiplier b ev ψ) := by
  simpa only [HilbertBasis.repr_apply_apply, multiplier_coord] using b.hasSum_repr (multiplier b ev ψ)

/-- Diagonal multiplication by any unit phases, on every coefficient vector. -/
def phaseMap (w : MArr N → ℂ) (hw : ∀ m, ‖w m‖ = 1)
    (v : lp (fun _ : MArr N => ℂ) 2) : lp (fun _ : MArr N => ℂ) 2 :=
  DiagonalMultiplier.mulVec w (B := 1) (fun m => (hw m).le) v

theorem phaseMap_norm (w : MArr N → ℂ) (hw : ∀ m, ‖w m‖ = 1)
    (v : lp (fun _ : MArr N => ℂ) 2) : ‖phaseMap w hw v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [DiagonalMultiplier.norm_sq_eq_tsum, DiagonalMultiplier.norm_sq_eq_tsum]
  apply tsum_congr
  intro m
  simp only [phaseMap, DiagonalMultiplier.mulVec_apply, norm_mul, hw, one_mul]

/-- A full diagonal unitary, whose inverse is conjugate phase multiplication. -/
def phaseUnitary (w : MArr N → ℂ) (hw : ∀ m, ‖w m‖ = 1) :
    lp (fun _ : MArr N => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : MArr N => ℂ) 2 where
  toLinearEquiv :=
    { toFun := phaseMap w hw
      invFun := phaseMap (fun m => (starRingEnd ℂ) (w m)) (fun m => by simpa using hw m)
      left_inv := by
        intro v; ext m
        change (starRingEnd ℂ) (w m) * (w m * v m) = v m
        rw [← mul_assoc, Complex.conj_mul', hw, Complex.ofReal_one, one_pow]
        simp
      right_inv := by
        intro v; ext m
        change w m * ((starRingEnd ℂ) (w m) * v m) = v m
        rw [← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, hw, one_pow]
        simp
      map_add' := by intro v u; ext m; change w m * (v m + u m) = _; exact mul_add _ _ _
      map_smul' := by intro a v; ext m; change w m * (a * v m) = a * (w m * v m); ring }
  norm_map' := phaseMap_norm w hw

/-- exp(-it ev) needs no charge-domain membership. -/
def evolution (b : BetheBasis L N) (ev : MArr N → ℝ) (t : ℝ) : HN L N ≃ₗᵢ[ℂ] HN L N :=
  (b.repr.trans (phaseUnitary (DiagonalMultiplier.phase ev t)
    (DiagonalMultiplier.norm_phase ev t))).trans b.repr.symm

theorem evolution_coord (b : BetheBasis L N) (ev : MArr N → ℝ) (t : ℝ)
    (ψ : HN L N) (m : MArr N) :
    ⟪b m, evolution b ev t ψ⟫_ℂ = DiagonalMultiplier.phase ev t m * ⟪b m, ψ⟫_ℂ := by
  rw [← HilbertBasis.repr_apply_apply]
  change b.repr (b.repr.symm _) m = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  change DiagonalMultiplier.phase ev t m * b.repr ψ m = _
  rw [HilbertBasis.repr_apply_apply]

/-- The charge domain is invariant under every spectral evolution. -/
theorem evolution_domain (b : BetheBasis L N) (ev μ : MArr N → ℝ) (t : ℝ) (ψ : HN L N) :
    evolution b μ t ψ ∈ domain b ev ↔ ψ ∈ domain b ev := by
  rw [mem_domain, mem_domain]
  simp only [evolution_coord, norm_mul, DiagonalMultiplier.norm_phase, one_mul]

/-- Identity time and the group law hold on the full physical Hilbert space. -/
theorem evolution_zero (b : BetheBasis L N) (ev : MArr N → ℝ) (ψ : HN L N) :
    evolution b ev 0 ψ = ψ := by
  apply b.repr.injective
  ext m
  simp only [HilbertBasis.repr_apply_apply, evolution_coord, DiagonalMultiplier.phase,
    zero_mul, Complex.ofReal_zero, neg_zero, Complex.exp_zero, one_mul]

theorem evolution_add (b : BetheBasis L N) (ev : MArr N → ℝ) (s t : ℝ) (ψ : HN L N) :
    evolution b ev (s+t) ψ = evolution b ev s (evolution b ev t ψ) := by
  apply b.repr.injective
  ext m
  simp only [HilbertBasis.repr_apply_apply, evolution_coord]
  have hp : DiagonalMultiplier.phase ev (s+t) m =
      DiagonalMultiplier.phase ev s m * DiagonalMultiplier.phase ev t m := by
    unfold DiagonalMultiplier.phase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hp, mul_assoc]

/-- Every pair of spectral unitary groups commute on every vector. -/
theorem evolution_commute (b : BetheBasis L N) (ev μ : MArr N → ℝ) (s t : ℝ) (ψ : HN L N) :
    evolution b ev s (evolution b μ t ψ) = evolution b μ t (evolution b ev s ψ) := by
  apply b.repr.injective
  ext m
  simp only [HilbertBasis.repr_apply_apply, evolution_coord]
  ring

/-- Strong continuity holds even off every unbounded charge domain. -/
theorem evolution_continuous (b : BetheBasis L N) (ev : MArr N → ℝ) (ψ : HN L N) :
    Continuous (fun t : ℝ => evolution b ev t ψ) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hc (m : MArr N) : Continuous (fun s : ℝ => DiagonalMultiplier.phase ev s m) := by
    unfold DiagonalMultiplier.phase
    fun_prop
  have hs := tendsto_tsum_of_dominated_convergence
    ((DiagonalMultiplier.summable_sq (b.repr ψ)).mul_left 4)
    (f := fun s m => ‖(DiagonalMultiplier.phase ev s m - DiagonalMultiplier.phase ev t m) *
      b.repr ψ m‖ ^ 2)
    (g := fun _ => (0 : ℝ))
    (fun m => by simpa using (((hc m).tendsto t).sub_const
      (DiagonalMultiplier.phase ev t m)).mul_const (b.repr ψ m) |>.norm |>.pow 2)
    (Filter.Eventually.of_forall fun s m => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
      have hh : ‖DiagonalMultiplier.phase ev s m - DiagonalMultiplier.phase ev t m‖ ≤ 2 := by
        calc
          _ ≤ ‖DiagonalMultiplier.phase ev s m‖ + ‖DiagonalMultiplier.phase ev t m‖ := norm_sub_le _ _
          _ = 2 := by rw [DiagonalMultiplier.norm_phase, DiagonalMultiplier.norm_phase]; norm_num
      exact mul_le_mul_of_nonneg_right
        (by nlinarith [norm_nonneg (DiagonalMultiplier.phase ev s m - DiagonalMultiplier.phase ev t m)])
        (sq_nonneg _))
  have he (s : ℝ) : ‖evolution b ev s ψ - evolution b ev t ψ‖ ^ 2 =
      ∑' m, ‖(DiagonalMultiplier.phase ev s m - DiagonalMultiplier.phase ev t m) * b.repr ψ m‖ ^ 2 := by
    rw [← b.repr.norm_map, DiagonalMultiplier.norm_sq_eq_tsum]
    apply tsum_congr
    intro m
    rw [map_sub]
    change ‖b.repr (evolution b ev s ψ) m - b.repr (evolution b ev t ψ) m‖ ^ 2 = _
    simp only [HilbertBasis.repr_apply_apply, evolution_coord]
    rw [sub_mul]
  have hsq : Filter.Tendsto (fun s => ‖evolution b ev s ψ - evolution b ev t ψ‖ ^ 2)
      (nhds t) (nhds 0) := by
    simpa only [he, tsum_zero] using hs
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hroot

/-- Literal instantiated eigenrelation for every complete occupation array. -/
theorem betheCharge_basis (hcont : BetheConditionalBasis.AbstractContinuity) (L : ℝ) [Fact (0 < L)]
    (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c) (r : ℕ) (m : MArr N) :
    ∃ h : BetheConditionalBasis.physicalBasis hcont L N hN c hc m ∈
      (charge (BetheConditionalBasis.physicalBasis hcont L N hN c hc) c r).domain,
      charge (BetheConditionalBasis.physicalBasis hcont L N hN c hc) c r
        ⟨BetheConditionalBasis.physicalBasis hcont L N hN c hc m, h⟩ =
          (eigenvalue L N c r m : ℂ) • BetheConditionalBasis.physicalBasis hcont L N hN c hc m :=
  ⟨basis_mem_domain _ _ _, multiplier_basis _ _ _⟩

/-- Concrete interacting charges on the BCB1 basis, with the exact same
explicit premise; N>=2 completeness is its only use. -/
def betheCharge (hcont : BetheConditionalBasis.AbstractContinuity) (L : ℝ) [Fact (0 < L)]
    (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c) (r : ℕ) : HN L N →ₗ.[ℂ] HN L N :=
  charge (BetheConditionalBasis.physicalBasis hcont L N hN c hc) c r

theorem betheCharge_domain (hcont : BetheConditionalBasis.AbstractContinuity) (L : ℝ) [Fact (0 < L)]
    (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c) (r : ℕ) (ψ : HN L N) :
    ψ ∈ (betheCharge hcont L N hN c hc r).domain ↔
      Summable (fun m => |eigenvalue L N c r m| ^ 2 *
        ‖BetheConditionalBasis.coefficientTransform hcont L N hN c hc ψ m‖ ^ 2) := by
  simpa only [betheCharge, charge, multiplier, HilbertBasis.repr_apply_apply,
    BetheConditionalBasis.coefficientTransform, coefficientTransform_apply] using
    mem_domain (BetheConditionalBasis.physicalBasis hcont L N hN c hc) (eigenvalue L N c r) ψ

/-- An unconditional one-particle Hilbert basis built from BOP1 density. -/
def oneCoordinateBasis (L : ℝ) [Fact (0 < L)] (c : ℝ) (hc : 0 < c) :
    HilbertBasis (BetheFreeFamily.Label 1) ℂ (ContactOperator.SymL2 L 1) :=
  HilbertBasis.mk (BetheBasisOrthogonality.unitWave_orthonormal L (N := 0)
    (c := (⟨c,hc.le⟩ : ℝ≥0)) hc)
    (by
      have h := congrArg Submodule.topologicalClosure
        (BetheBasisOrthogonality.span_unitWave L (N := 0) (⟨c,hc.le⟩ : ℝ≥0))
      exact le_of_eq ((h.trans (BetheBasisOneParticle.one_dense L (⟨c,hc.le⟩ : ℝ≥0))).symm))

theorem oneCoordinateBasis_eq (hcont : BetheConditionalBasis.AbstractContinuity)
    (L : ℝ) [Fact (0 < L)] (c : ℝ) (hc : 0 < c) :
    oneCoordinateBasis L c hc = BetheConditionalBasis.coordinateBasis hcont L 1 (by omega) c hc := by
  apply DFunLike.ext
  intro n
  rw [BetheConditionalBasis.coordinateBasis_apply]
  simp only [oneCoordinateBasis, HilbertBasis.coe_mk]
  rfl

/-- Same physical Bethe basis at N=1, with no continuity premise. -/
def onePhysicalBasis (L : ℝ) [Fact (0 < L)] (c : ℝ) (hc : 0 < c) : BetheBasis L 1 :=
  reindexBasis (BetheConditionalBasis.labelArr 1)
    (HilbertBasis.ofRepr ((BethePhysicalTransfer.symmetricPosition L 1).trans (oneCoordinateBasis L c hc).repr))

theorem onePhysicalBasis_eq (hcont : BetheConditionalBasis.AbstractContinuity)
    (L : ℝ) [Fact (0 < L)] (c : ℝ) (hc : 0 < c) :
    onePhysicalBasis L c hc = BetheConditionalBasis.physicalBasis hcont L 1 (by omega) c hc := by
  simp only [onePhysicalBasis, oneCoordinateBasis_eq hcont, BetheConditionalBasis.physicalBasis]

/-- Every number sector: canonical vacuum, unconditional actual N=1,
and the frozen BCB1 interacting basis for N>=2. -/
def sectorBasis (hcont : BetheConditionalBasis.AbstractContinuity) (L : ℝ) [Fact (0 < L)]
    (c : ℝ) (hc : 0 < c) : (N : ℕ) → BetheBasis L N
  | 0 => freeBasis L 0
  | 1 => onePhysicalBasis L c hc
  | n+2 => BetheConditionalBasis.physicalBasis hcont L (n+2) (by omega) c hc

def sectorCharge (hcont : BetheConditionalBasis.AbstractContinuity) (L : ℝ) [Fact (0 < L)]
    (c : ℝ) (hc : 0 < c) (N r : ℕ) : HN L N →ₗ.[ℂ] HN L N :=
  charge (sectorBasis hcont L c hc N) c r

end QuantumNLS.BetheSpectralCharges

#print axioms QuantumNLS.BetheSpectralCharges.rapidity
#print axioms QuantumNLS.BetheSpectralCharges.eigenvalue
#print axioms QuantumNLS.BetheSpectralCharges.eigenvalue_zero
#print axioms QuantumNLS.BetheSpectralCharges.domain
#print axioms QuantumNLS.BetheSpectralCharges.mem_domain
#print axioms QuantumNLS.BetheSpectralCharges.multiplier
#print axioms QuantumNLS.BetheSpectralCharges.multiplier_coord
#print axioms QuantumNLS.BetheSpectralCharges.maximal
#print axioms QuantumNLS.BetheSpectralCharges.basis_mem_domain
#print axioms QuantumNLS.BetheSpectralCharges.multiplier_basis
#print axioms QuantumNLS.BetheSpectralCharges.domain_dense
#print axioms QuantumNLS.BetheSpectralCharges.constant_domain
#print axioms QuantumNLS.BetheSpectralCharges.constant_apply
#print axioms QuantumNLS.BetheSpectralCharges.charge
#print axioms QuantumNLS.BetheSpectralCharges.charge_zero_domain
#print axioms QuantumNLS.BetheSpectralCharges.charge_zero_apply
#print axioms QuantumNLS.BetheSpectralCharges.polynomialSymbol
#print axioms QuantumNLS.BetheSpectralCharges.polynomialSymbol_eq
#print axioms QuantumNLS.BetheSpectralCharges.polynomialCharge
#print axioms QuantumNLS.BetheSpectralCharges.jointPolynomialSymbol
#print axioms QuantumNLS.BetheSpectralCharges.jointPolynomialCharge
#print axioms QuantumNLS.BetheSpectralCharges.jointPolynomial_domain
#print axioms QuantumNLS.BetheSpectralCharges.multiplier_expansion
#print axioms QuantumNLS.BetheSpectralCharges.phaseMap
#print axioms QuantumNLS.BetheSpectralCharges.phaseMap_norm
#print axioms QuantumNLS.BetheSpectralCharges.phaseUnitary
#print axioms QuantumNLS.BetheSpectralCharges.evolution
#print axioms QuantumNLS.BetheSpectralCharges.evolution_coord
#print axioms QuantumNLS.BetheSpectralCharges.evolution_domain
#print axioms QuantumNLS.BetheSpectralCharges.evolution_zero
#print axioms QuantumNLS.BetheSpectralCharges.evolution_add
#print axioms QuantumNLS.BetheSpectralCharges.evolution_commute
#print axioms QuantumNLS.BetheSpectralCharges.evolution_continuous
#print axioms QuantumNLS.BetheSpectralCharges.betheCharge_basis
#print axioms QuantumNLS.BetheSpectralCharges.betheCharge
#print axioms QuantumNLS.BetheSpectralCharges.betheCharge_domain
#print axioms QuantumNLS.BetheSpectralCharges.oneCoordinateBasis
#print axioms QuantumNLS.BetheSpectralCharges.oneCoordinateBasis_eq
#print axioms QuantumNLS.BetheSpectralCharges.onePhysicalBasis
#print axioms QuantumNLS.BetheSpectralCharges.onePhysicalBasis_eq
#print axioms QuantumNLS.BetheSpectralCharges.sectorBasis
#print axioms QuantumNLS.BetheSpectralCharges.sectorCharge

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.BetheSpectralCharges.rapidity,
    ``QuantumNLS.BetheSpectralCharges.eigenvalue,
    ``QuantumNLS.BetheSpectralCharges.eigenvalue_zero,
    ``QuantumNLS.BetheSpectralCharges.domain,
    ``QuantumNLS.BetheSpectralCharges.mem_domain,
    ``QuantumNLS.BetheSpectralCharges.multiplier,
    ``QuantumNLS.BetheSpectralCharges.multiplier_coord,
    ``QuantumNLS.BetheSpectralCharges.maximal,
    ``QuantumNLS.BetheSpectralCharges.basis_mem_domain,
    ``QuantumNLS.BetheSpectralCharges.multiplier_basis,
    ``QuantumNLS.BetheSpectralCharges.domain_dense,
    ``QuantumNLS.BetheSpectralCharges.constant_domain,
    ``QuantumNLS.BetheSpectralCharges.constant_apply,
    ``QuantumNLS.BetheSpectralCharges.charge,
    ``QuantumNLS.BetheSpectralCharges.charge_zero_domain,
    ``QuantumNLS.BetheSpectralCharges.charge_zero_apply,
    ``QuantumNLS.BetheSpectralCharges.polynomialSymbol,
    ``QuantumNLS.BetheSpectralCharges.polynomialSymbol_eq,
    ``QuantumNLS.BetheSpectralCharges.polynomialCharge,
    ``QuantumNLS.BetheSpectralCharges.jointPolynomialSymbol,
    ``QuantumNLS.BetheSpectralCharges.jointPolynomialCharge,
    ``QuantumNLS.BetheSpectralCharges.jointPolynomial_domain,
    ``QuantumNLS.BetheSpectralCharges.multiplier_expansion,
    ``QuantumNLS.BetheSpectralCharges.phaseMap,
    ``QuantumNLS.BetheSpectralCharges.phaseMap_norm,
    ``QuantumNLS.BetheSpectralCharges.phaseUnitary,
    ``QuantumNLS.BetheSpectralCharges.evolution,
    ``QuantumNLS.BetheSpectralCharges.evolution_coord,
    ``QuantumNLS.BetheSpectralCharges.evolution_domain,
    ``QuantumNLS.BetheSpectralCharges.evolution_zero,
    ``QuantumNLS.BetheSpectralCharges.evolution_add,
    ``QuantumNLS.BetheSpectralCharges.evolution_commute,
    ``QuantumNLS.BetheSpectralCharges.evolution_continuous,
    ``QuantumNLS.BetheSpectralCharges.betheCharge_basis,
    ``QuantumNLS.BetheSpectralCharges.betheCharge,
    ``QuantumNLS.BetheSpectralCharges.betheCharge_domain,
    ``QuantumNLS.BetheSpectralCharges.oneCoordinateBasis,
    ``QuantumNLS.BetheSpectralCharges.oneCoordinateBasis_eq,
    ``QuantumNLS.BetheSpectralCharges.onePhysicalBasis,
    ``QuantumNLS.BetheSpectralCharges.onePhysicalBasis_eq,
    ``QuantumNLS.BetheSpectralCharges.sectorBasis,
    ``QuantumNLS.BetheSpectralCharges.sectorCharge]
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Spectral charges nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  let mut todo := #[``QuantumNLS.BetheSpectralCharges.rapidity,
    ``QuantumNLS.BetheSpectralCharges.eigenvalue,
    ``QuantumNLS.BetheSpectralCharges.eigenvalue_zero,
    ``QuantumNLS.BetheSpectralCharges.domain,
    ``QuantumNLS.BetheSpectralCharges.mem_domain,
    ``QuantumNLS.BetheSpectralCharges.multiplier,
    ``QuantumNLS.BetheSpectralCharges.multiplier_coord,
    ``QuantumNLS.BetheSpectralCharges.maximal,
    ``QuantumNLS.BetheSpectralCharges.basis_mem_domain,
    ``QuantumNLS.BetheSpectralCharges.multiplier_basis,
    ``QuantumNLS.BetheSpectralCharges.domain_dense,
    ``QuantumNLS.BetheSpectralCharges.constant_domain,
    ``QuantumNLS.BetheSpectralCharges.constant_apply,
    ``QuantumNLS.BetheSpectralCharges.charge,
    ``QuantumNLS.BetheSpectralCharges.charge_zero_domain,
    ``QuantumNLS.BetheSpectralCharges.charge_zero_apply,
    ``QuantumNLS.BetheSpectralCharges.polynomialSymbol,
    ``QuantumNLS.BetheSpectralCharges.polynomialSymbol_eq,
    ``QuantumNLS.BetheSpectralCharges.polynomialCharge,
    ``QuantumNLS.BetheSpectralCharges.jointPolynomialSymbol,
    ``QuantumNLS.BetheSpectralCharges.jointPolynomialCharge,
    ``QuantumNLS.BetheSpectralCharges.jointPolynomial_domain,
    ``QuantumNLS.BetheSpectralCharges.multiplier_expansion,
    ``QuantumNLS.BetheSpectralCharges.phaseMap,
    ``QuantumNLS.BetheSpectralCharges.phaseMap_norm,
    ``QuantumNLS.BetheSpectralCharges.phaseUnitary,
    ``QuantumNLS.BetheSpectralCharges.evolution,
    ``QuantumNLS.BetheSpectralCharges.evolution_coord,
    ``QuantumNLS.BetheSpectralCharges.evolution_domain,
    ``QuantumNLS.BetheSpectralCharges.evolution_zero,
    ``QuantumNLS.BetheSpectralCharges.evolution_add,
    ``QuantumNLS.BetheSpectralCharges.evolution_commute,
    ``QuantumNLS.BetheSpectralCharges.evolution_continuous,
    ``QuantumNLS.BetheSpectralCharges.oneCoordinateBasis,
    ``QuantumNLS.BetheSpectralCharges.onePhysicalBasis]
  let mut checked : Std.HashSet Lean.Name := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    unless checked.contains n do
      checked := checked.insert n
      if n == ``QuantumNLS.BetheConditionalBasis.AbstractContinuity then
        throwError "Generic definition reached EXT-001 premise: {n}"
      if let some ci := env.find? n then
        todo := todo ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          todo := todo ++ v.getUsedConstants
  Lean.logInfo m!"Spectral charges aggregate audit PASS: {seen.size} transitive constants. Generic definitions independent of EXT-001; actual BCB1 instantiation carries its explicit Prop premise."
