import QuantumNLS.ContactDistributionFull
import QuantumNLS.ContactOperator
import QuantumNLS.CollisionIdentification
import QuantumNLS.ProductPermutation

/-!
# R-98129FE7 `contact:thm:form` (A01.tex:37-60), assembled

Imports (read-only): `ContactDistributionFull 0bebb11e`, `ContactOperator c847ea9b`,
`CollisionIdentification ffd608f4`.

Contents: (§1-3) permutation covariance of `q_{N,c}` (trace relabelling `T_{σa,σb}(V_σ x) = T_{ab} x`
on Fourier fibres, `T_ba = T_ab`); (§4) the printed "symmetric tests suffice" step: averaging an
arbitrary smooth lattice-periodic test over permutations leaves its pairing with a symmetric
`ψ`, `f` unchanged; (§5) uniqueness of the associated self-adjoint operator; (§6) the assembled
theorem.
-/

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ENNReal ComplexConjugate
open MeasureTheory QuantumNLS.Energy QuantumNLS.PhysicalEnergy QuantumNLS.PhysicalTensor
  QuantumNLS.CollisionTrace QuantumNLS.ProductWeakDerivatives QuantumNLS.Fourier
  QuantumNLS.ContactForm QuantumNLS.ContactOperator QuantumNLS.ContactDistribution
  QuantumNLS.CollisionIdentification QuantumNLS.ContactDistributionFull QuantumNLS.ProductPermutation

namespace QuantumNLS.ContactFormTheorem

section TraceCov
variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-- Relabelling of the trace index set under a permutation: `(s, ρ) ↦ (s, ρ ∘ σ)`. -/
def idxEquiv (σ : Equiv.Perm (Fin N)) (a b : Fin N) :
    TIdx N (σ a) (σ b) ≃ TIdx N a b where
  toFun τ := (τ.1, fun k => τ.2 ⟨σ k.1, fun h => k.2.1 (σ.injective h),
    fun h => k.2.2 (σ.injective h)⟩)
  invFun ρ := (ρ.1, fun l => ρ.2 ⟨σ.symm l.1, fun h => l.2.1 (σ.symm_apply_eq.1 h),
    fun h => l.2.2 (σ.symm_apply_eq.1 h)⟩)
  left_inv τ := by
    refine Prod.ext rfl (funext fun l => ?_)
    simp
  right_inv ρ := by
    refine Prod.ext rfl (funext fun k => ?_)
    simp

theorem fib_comp (σ : Equiv.Perm (Fin N)) (a b : Fin N) (hab : a ≠ b)
    (hσ : σ a ≠ σ b) (τ : TIdx N (σ a) (σ b)) (a' : ℤ) :
    (fun l => fib (σ a) (σ b) hσ τ a' (σ l)) = fib a b hab (idxEquiv σ a b τ) a' := by
  symm
  rw [fib_eq_iff]
  have hτ := (fib_eq_iff (σ a) (σ b) hσ τ a' (fib (σ a) (σ b) hσ τ a')).1 rfl
  refine ⟨Prod.ext ?_ (funext fun k => ?_), ?_⟩
  · simp only [idxEquiv, Equiv.coe_fn_mk, collapse, fib_i, fib_j]
    ring
  · simp only [idxEquiv, Equiv.coe_fn_mk, collapse]
    exact congrArg (fun t : TIdx N (σ a) (σ b) => t.2 ⟨σ k.1, fun h => k.2.1 (σ.injective h),
      fun h => k.2.2 (σ.injective h)⟩) hτ.1
  · simp [fib_i]

/-- **Trace covariance**: for `x' = V_σ x`, `(T_{σa,σb} x')(τ) = (T_{ab} x)(relabel τ)`. -/
theorem trace_perm_apply (σ : Equiv.Perm (Fin N)) (a b : Fin N) (hab : a ≠ b)
    (hσ : σ a ≠ σ b) (x x' : PhysH1 L N) (hx : x'.val = physPerm σ x.val)
    (τ : TIdx N (σ a) (σ b)) :
    (traceCLM (σ a) (σ b) hσ x' : TIdx N (σ a) (σ b) → ℂ) τ =
      (traceCLM a b hab x : TIdx N a b → ℂ) (idxEquiv σ a b τ) := by
  rw [traceCLM_apply, traceCLM_apply, traceMap_apply, traceMap_apply]
  unfold traceCoeff
  congr 1
  refine tsum_congr fun a' => ?_
  have h1 : coeffFun x' (fib (σ a) (σ b) hσ τ a') =
      coeffFun x (fun l => fib (σ a) (σ b) hσ τ a' (σ l)) := by
    unfold coeffFun
    rw [hx, momUnitary_physPerm]
    rfl
  rw [h1, fib_comp σ a b hab hσ τ a']

/-- The trace as an `ℓ²`-coefficient inner product. -/
theorem inner_trace_perm (σ : Equiv.Perm (Fin N)) (a b : Fin N) (hab : a ≠ b)
    (hσ : σ a ≠ σ b) (x x' y y' : PhysH1 L N) (hx : x'.val = physPerm σ x.val)
    (hy : y'.val = physPerm σ y.val) :
    ⟪traceCLM (σ a) (σ b) hσ x', traceCLM (σ a) (σ b) hσ y'⟫_ℂ =
      ⟪traceCLM a b hab x, traceCLM a b hab y⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  rw [← (idxEquiv σ a b).tsum_eq]
  refine tsum_congr fun τ => ?_
  rw [trace_perm_apply σ a b hab hσ x x' hx τ, trace_perm_apply σ a b hab hσ y y' hy τ]

/-- Swapping the order of the colliding pair does not change the trace pairing. -/
def swapIdx (i j : Fin N) : TIdx N i j ≃ TIdx N j i where
  toFun τ := (τ.1, fun l => τ.2 ⟨l.1, l.2.2, l.2.1⟩)
  invFun τ := (τ.1, fun l => τ.2 ⟨l.1, l.2.2, l.2.1⟩)
  left_inv τ := by refine Prod.ext rfl (funext fun l => ?_); rfl
  right_inv τ := by refine Prod.ext rfl (funext fun l => ?_); rfl

theorem fib_swap (i j : Fin N) (hij : i ≠ j) (τ : TIdx N i j) (a' : ℤ) :
    fib j i hij.symm (swapIdx i j τ) a' = fib i j hij τ (τ.1 - a') := by
  rw [fib_eq_iff]
  have hτ := (fib_eq_iff i j hij τ (τ.1 - a') (fib i j hij τ (τ.1 - a'))).1 rfl
  refine ⟨Prod.ext ?_ (funext fun l => ?_), ?_⟩
  · simp only [swapIdx, Equiv.coe_fn_mk, collapse, fib_i, fib_j]
    ring
  · simp only [swapIdx, Equiv.coe_fn_mk, collapse]
    exact congrArg (fun t : TIdx N i j => t.2 ⟨l.1, l.2.2, l.2.1⟩) hτ.1
  · simp [fib_j]

theorem inner_trace_swap (i j : Fin N) (hij : i ≠ j) (x y : PhysH1 L N) :
    ⟪traceCLM j i hij.symm x, traceCLM j i hij.symm y⟫_ℂ =
      ⟪traceCLM i j hij x, traceCLM i j hij y⟫_ℂ := by
  have key : ∀ (z : PhysH1 L N) (τ : TIdx N i j),
      (traceCLM j i hij.symm z : TIdx N j i → ℂ) (swapIdx i j τ) =
        (traceCLM i j hij z : TIdx N i j → ℂ) τ := by
    intro z τ
    rw [traceCLM_apply, traceCLM_apply, traceMap_apply, traceMap_apply]
    unfold traceCoeff
    congr 1
    refine (tsum_congr fun a' => ?_).trans
      ((Equiv.subLeft τ.1).tsum_eq (fun a' => coeffFun z (fib i j hij τ a')))
    simp only [Equiv.subLeft_apply]
    rw [fib_swap i j hij τ a']
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum, ← (swapIdx i j).tsum_eq]
  refine tsum_congr fun τ => ?_
  rw [key x τ, key y τ]


/-- **Kinetic covariance**: `Σ_j⟨∂_jφ',∂_jψ'⟩ = Σ_j⟨∂_jφ,∂_jψ⟩` for `φ' = V_σφ`, `ψ' = V_σψ`. -/
theorem kinSum_perm (σ : Equiv.Perm (Fin N)) (φ φ' ψ ψ' : PhysH1 L N)
    (hφ : φ'.val = physPerm σ φ.val) (hψ : ψ'.val = physPerm σ ψ.val) :
    kinSum φ' ψ' = kinSum φ ψ := by
  have hg : ∀ (z z' : PhysH1 L N), z'.val = physPerm σ z.val → ∀ j,
      gradientCLM (σ j) z' = physPerm σ (gradientCLM j z) := fun z z' h j =>
    gradientCLM_eq_of_weak (σ j) z' _ (by
      rw [h]; exact hasWeakPartial_physPerm σ (gradientCLM_hasWeakPartial j z))
  unfold kinSum
  simp_rw [← gradientCLM_inner]
  rw [← Equiv.sum_comp σ (fun j => ⟪gradientCLM j φ', gradientCLM j ψ'⟫_ℂ)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hg φ φ' hφ j, hg ψ ψ' hψ j]
  exact (physPerm σ).inner_map_map _ _

/-- The pair pairing `⟨T_abφ,T_abψ⟩` for `a ≠ b` (and `0` on the diagonal). -/
def Gp (φ ψ : PhysH1 L N) (a b : Fin N) : ℂ :=
  if h : a ≠ b then ⟪traceCLM a b h φ, traceCLM a b h ψ⟫_ℂ else 0

theorem Gp_diag (φ ψ : PhysH1 L N) (a : Fin N) : Gp φ ψ a a = 0 := by simp [Gp]

theorem Gp_swap (φ ψ : PhysH1 L N) (a b : Fin N) : Gp φ ψ b a = Gp φ ψ a b := by
  by_cases h : a = b
  · subst h; rfl
  · have h' : b ≠ a := Ne.symm h
    simp only [Gp, h, h', ne_eq, not_false_eq_true, dite_true]
    exact inner_trace_swap a b h φ ψ

theorem Gp_perm (σ : Equiv.Perm (Fin N)) (φ φ' ψ ψ' : PhysH1 L N)
    (hφ : φ'.val = physPerm σ φ.val) (hψ : ψ'.val = physPerm σ ψ.val) (a b : Fin N) :
    Gp φ' ψ' (σ a) (σ b) = Gp φ ψ a b := by
  by_cases h : a = b
  · subst h; simp [Gp_diag]
  · have hσ : σ a ≠ σ b := fun e => h (σ.injective e)
    simp only [Gp, h, hσ, ne_eq, not_false_eq_true, dite_true]
    exact inner_trace_perm σ a b h hσ φ φ' ψ ψ' hφ hψ

theorem contactSum_eq_Gp (φ ψ : PhysH1 L N) :
    contactSum φ ψ = ∑ p : Pair N, Gp φ ψ p.1.1 p.1.2 := by
  unfold contactSum
  refine Finset.sum_congr rfl fun p _ => ?_
  have h : p.1.1 ≠ p.1.2 := ne_of_lt p.2
  simp only [Gp, h, ne_eq, not_false_eq_true, dite_true]
  rfl

theorem sum_pair_double (g : Fin N → Fin N → ℂ) (hdiag : ∀ a, g a a = 0)
    (hsymm : ∀ a b, g b a = g a b) :
    2 * ∑ p : Pair N, g p.1.1 p.1.2 = ∑ a, ∑ b, g a b := by
  have h1 : ∑ p : Pair N, g p.1.1 p.1.2 =
      ∑ p ∈ (Finset.univ : Finset (Fin N × Fin N)).filter (fun p => p.1 < p.2), g p.1 p.2 :=
    (Finset.sum_subtype _ (fun x => by simp) (fun p : Fin N × Fin N => g p.1 p.2)).symm
  have h2 : ∑ a, ∑ b, g a b = ∑ p : Fin N × Fin N, g p.1 p.2 :=
    (Fintype.sum_prod_type' (fun a b => g a b)).symm
  have h3 : ∑ p ∈ (Finset.univ : Finset (Fin N × Fin N)).filter (fun p => ¬ p.1 < p.2), g p.1 p.2 =
      ∑ p ∈ (Finset.univ : Finset (Fin N × Fin N)).filter (fun p => p.1 < p.2), g p.1 p.2 := by
    have e1 : ∑ p ∈ (Finset.univ : Finset (Fin N × Fin N)).filter (fun p => p.2 < p.1), g p.1 p.2 =
        ∑ p ∈ (Finset.univ : Finset (Fin N × Fin N)).filter (fun p => ¬ p.1 < p.2), g p.1 p.2 := by
      refine Finset.sum_subset (fun p hp => ?_) (fun p hp hn => ?_)
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        exact not_lt.2 hp.le
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hp hn
        have : p.1 = p.2 := le_antisymm hn hp
        rw [← this]; exact hdiag _
    rw [← e1]
    refine Finset.sum_equiv (Equiv.prodComm _ _) (fun p => by simp) (fun p _ => ?_)
    exact hsymm p.2 p.1
  rw [h1, h2, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p : Fin N × Fin N => p.1 < p.2),
    h3]
  ring

theorem contactSum_perm (σ : Equiv.Perm (Fin N)) (φ φ' ψ ψ' : PhysH1 L N)
    (hφ : φ'.val = physPerm σ φ.val) (hψ : ψ'.val = physPerm σ ψ.val) :
    contactSum φ' ψ' = contactSum φ ψ := by
  have key : ∀ (u v : PhysH1 L N), 2 * contactSum u v = ∑ a, ∑ b, Gp u v a b := fun u v => by
    rw [contactSum_eq_Gp]
    exact sum_pair_double (Gp u v) (Gp_diag u v) (Gp_swap u v)
  have h2 : (2 : ℂ) * contactSum φ' ψ' = 2 * contactSum φ ψ := by
    rw [key, key]
    calc ∑ a, ∑ b, Gp φ' ψ' a b = ∑ a, ∑ b, Gp φ' ψ' (σ a) (σ b) := by
          rw [← Equiv.sum_comp σ (fun a => ∑ b, Gp φ' ψ' a b)]
          exact Finset.sum_congr rfl fun a _ => (Equiv.sum_comp σ (fun b => Gp φ' ψ' (σ a) b)).symm
      _ = ∑ a, ∑ b, Gp φ ψ a b := by
          simp_rw [Gp_perm σ φ φ' ψ ψ' hφ hψ]
  exact mul_left_cancel₀ two_ne_zero h2

/-- **Permutation covariance of the contact form**: `q(V_σφ, V_σψ) = q(φ,ψ)`. -/
theorem q_perm (c : ℝ) (σ : Equiv.Perm (Fin N)) (φ φ' ψ ψ' : PhysH1 L N)
    (hφ : φ'.val = physPerm σ φ.val) (hψ : ψ'.val = physPerm σ ψ.val) :
    q c φ' ψ' = q c φ ψ := by
  unfold q
  rw [kinSum_perm σ φ φ' ψ ψ' hφ hψ, contactSum_perm σ φ φ' ψ ψ' hφ hψ]

end TraceCov


section Averaging
variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-- The permuted test function `x ↦ φ(x∘σ)`. -/
def permTest (σ : Equiv.Perm (Fin N)) (φ : (Fin N → ℝ) → ℂ) : (Fin N → ℝ) → ℂ :=
  fun x => φ (fun i => x (σ i))

omit [Fact (0 < L)] in
theorem isTorusTest_perm {φ : (Fin N → ℝ) → ℂ} (hφ : IsTorusTest L φ) (σ : Equiv.Perm (Fin N)) :
    IsTorusTest L (permTest σ φ) where
  smooth := hφ.smooth.comp (contDiff_pi.2 fun i => contDiff_apply ℝ ℝ (σ i))
  periodic := fun x m => by
    have := hφ.periodic (fun i => x (σ i)) (fun i => m (σ i))
    simpa [permTest] using this

/-- The permutation average of a test function. -/
def avgTest (φ : (Fin N → ℝ) → ℂ) : (Fin N → ℝ) → ℂ := fun x =>
  (((Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ : ℝ) : ℂ) *
    ∑ σ : Equiv.Perm (Fin N), permTest σ φ x

omit [Fact (0 < L)] in
theorem isTorusTest_avg {φ : (Fin N → ℝ) → ℂ} (hφ : IsTorusTest L φ) :
    IsTorusTest L (avgTest φ) where
  smooth := contDiff_const.mul (ContDiff.sum fun σ _ => (isTorusTest_perm hφ σ).smooth)
  periodic := fun x m => by
    unfold avgTest
    congr 1
    exact Finset.sum_congr rfl fun σ _ => (isTorusTest_perm hφ σ).periodic x m

theorem symmFun_avg (φ : (Fin N → ℝ) → ℂ) : SymmFun (avgTest φ) := by
  intro τ x
  unfold avgTest
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ : Equiv.Perm (Fin N) => permTest σ φ x)

theorem coeFn_finsetSum {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Finset ι) (F : ι → Lp ℂ 2 μ) :
    ((∑ i ∈ s, F i : Lp ℂ 2 μ) : α → ℂ) =ᵐ[μ] ∑ i ∈ s, (F i : α → ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Lp.coeFn_zero ℂ 2 μ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (Lp.coeFn_add _ _).trans (Filter.EventuallyEq.add Filter.EventuallyEq.rfl ih)

theorem smoothH1_perm_val {φ : (Fin N → ℝ) → ℂ} (hφ : IsTorusTest L φ) (σ : Equiv.Perm (Fin N)) :
    (smoothH1 (isTorusTest_perm hφ σ)).val = physPerm σ (smoothH1 hφ).val := by
  rw [smoothH1_val, smoothH1_val]
  refine Lp.ext ?_
  have h1 := (memLp_liftK (L := L) (isTorusTest_perm hφ σ).smooth.continuous).coeFn_toLp
  have h2 := coeFn_physPerm σ ((memLp_liftK (L := L) hφ.smooth.continuous).toLp (liftK (L := L) φ))
  have h3 := (measurePreserving_coordPerm (L := L) σ).quasiMeasurePreserving.ae_eq_comp
    (memLp_liftK (L := L) hφ.smooth.continuous).coeFn_toLp
  filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
  rw [hy1, hy2]
  exact hy3.symm

/-- The `H¹` element of the permutation average is the average of the permuted `H¹` elements. -/
theorem smoothH1_avg_val {φ : (Fin N → ℝ) → ℂ} (hφ : IsTorusTest L φ) :
    (smoothH1 (isTorusTest_avg hφ)).val =
      (((Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ : ℝ) : ℂ) •
        ∑ σ : Equiv.Perm (Fin N), physPerm σ (smoothH1 hφ).val := by
  rw [smoothH1_val]
  refine Lp.ext ?_
  have h1 := (memLp_liftK (L := L) (isTorusTest_avg hφ).smooth.continuous).coeFn_toLp
  have h2 := Lp.coeFn_smul (((Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ : ℝ) : ℂ)
    (∑ σ : Equiv.Perm (Fin N), physPerm σ (smoothH1 hφ).val)
  have h3 := coeFn_finsetSum (μ := torusPiMeasure L N) Finset.univ
    (fun σ : Equiv.Perm (Fin N) => physPerm σ (smoothH1 hφ).val)
  have h4 : ∀ᵐ y ∂(torusPiMeasure L N), ∀ σ : Equiv.Perm (Fin N),
      (physPerm σ (smoothH1 hφ).val : (Fin N → AddCircle L) → ℂ) y =
        liftK (L := L) (permTest σ φ) y := by
    rw [ae_all_iff]
    intro σ
    have := (memLp_liftK (L := L) (isTorusTest_perm hφ σ).smooth.continuous).coeFn_toLp
    rw [← smoothH1_val (isTorusTest_perm hφ σ), smoothH1_perm_val hφ σ] at this
    exact this
  filter_upwards [h1, h2, h3, h4] with y hy1 hy2 hy3 hy4
  rw [hy1, hy2]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hy3]
  simp only [Finset.sum_apply]
  change _ * ∑ σ : Equiv.Perm (Fin N), liftK (L := L) (permTest σ φ) y = _
  exact congrArg _ (Finset.sum_congr rfl fun σ _ => (hy4 σ).symm)

theorem q_sum_left (c : ℝ) {ι : Type*} (s : Finset ι) (F : ι → PhysH1 L N) (ψ : PhysH1 L N) :
    q c (∑ i ∈ s, F i) ψ = ∑ i ∈ s, q c (F i) ψ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := q_smul_left c 0 (0 : PhysH1 L N) ψ
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, q_add_left, ih]


theorem inner_smoothH1_rhs {φ : (Fin N → ℝ) → ℂ} (hφ : IsTorusTest L φ) (F : L2TN L N) :
    ⟪(smoothH1 hφ).val, F⟫_ℂ =
      ∫ y, conj (liftK (L := L) φ y) * (F : (Fin N → AddCircle L) → ℂ) y ∂(torusPiMeasure L N) := by
  apply inner_eq_integral
  rw [smoothH1_val hφ]
  exact (memLp_liftK (L := L) hφ.smooth.continuous).coeFn_toLp

theorem cN_mul_card : (((Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ : ℝ) : ℂ) *
    (Fintype.card (Equiv.Perm (Fin N)) : ℂ) = 1 := by
  have h : (Fintype.card (Equiv.Perm (Fin N)) : ℝ) ≠ 0 := by
    have := Fintype.card_pos (α := Equiv.Perm (Fin N))
    positivity
  have h' : (Fintype.card (Equiv.Perm (Fin N)) : ℂ) ≠ 0 := by exact_mod_cast h
  push_cast
  field_simp

/-- **Averaging leaves `q(·, x)` unchanged for symmetric `x`.** -/
theorem q_avg_eq (c : ℝ) {φ : (Fin N → ℝ) → ℂ} (hφ : IsTorusTest L φ) (x : VSym L N) :
    q c (smoothH1 (isTorusTest_avg hφ)) x.1 = q c (smoothH1 hφ) x.1 := by
  set cN : ℂ := (((Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ : ℝ) : ℂ) with hcN
  have hv : smoothH1 (isTorusTest_avg hφ) =
      cN • ∑ σ : Equiv.Perm (Fin N), smoothH1 (isTorusTest_perm hφ σ) := by
    apply PhysH1.val_injective
    rw [smoothH1_avg_val hφ]
    show _ = PhysH1.valₗ (cN • ∑ σ : Equiv.Perm (Fin N), smoothH1 (isTorusTest_perm hφ σ))
    rw [map_smul, map_sum]
    congr 1
    exact Finset.sum_congr rfl fun σ _ => (smoothH1_perm_val hφ σ).symm
  have hx : ∀ σ : Equiv.Perm (Fin N), x.1.val = physPerm σ x.1.val := fun σ =>
    ((PhysH1.mem_sym_iff x.1).1 x.2 σ).symm
  rw [hv, q_smul_left, q_sum_left]
  have : ∀ σ : Equiv.Perm (Fin N),
      q c (smoothH1 (isTorusTest_perm hφ σ)) x.1 = q c (smoothH1 hφ) x.1 := fun σ =>
    q_perm c σ (smoothH1 hφ) _ x.1 x.1 (smoothH1_perm_val hφ σ) (hx σ)
  simp_rw [this]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcN, Complex.conj_ofReal, ← mul_assoc,
    cN_mul_card, one_mul]

/-- **Averaging leaves the pairing with a symmetric `f` unchanged.** -/
theorem inner_avg_eq {φ : (Fin N → ℝ) → ℂ} (hφ : IsTorusTest L φ) (f : SymL2 L N) :
    ⟪(smoothH1 (isTorusTest_avg hφ)).val, (f : L2TN L N)⟫_ℂ =
      ⟪(smoothH1 hφ).val, (f : L2TN L N)⟫_ℂ := by
  rw [smoothH1_avg_val hφ, inner_smul_left, sum_inner]
  have : ∀ σ : Equiv.Perm (Fin N),
      ⟪physPerm σ (smoothH1 hφ).val, (f : L2TN L N)⟫_ℂ = ⟪(smoothH1 hφ).val, (f : L2TN L N)⟫_ℂ :=
    fun σ => by
      have hf := (mem_SymL2_iff _).1 f.2 σ
      conv_lhs => rw [← hf]
      exact (physPerm σ).inner_map_map _ _
  simp_rw [this]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Complex.conj_ofReal, ← mul_assoc,
    cN_mul_card, one_mul]

/-- **"Symmetric tests suffice" (printed step): `contact:eq:distdomain` with arbitrary smooth
lattice-periodic tests.**  `ψ ∈ D(H_{N,c})`, `Hψ = f` iff `ψ ∈ H¹_sym` and, for EVERY smooth
lattice-periodic `φ` (no symmetry assumed),
`Σ_j ∫ conj(∂_jφ)∂_jψ + 2cΣ_{i<j}∫ conj(φ|_{x_i=x_j}) T_ijψ dy_ij = ∫ conj(φ) f`. -/
theorem contact_distdomain_all {c : ℝ} (hc : 0 ≤ c) (ψ f : SymL2 L N) :
    (∃ h : ψ ∈ (Hop (L := L) (N := N) c hc).domain, Hop c hc ⟨ψ, h⟩ = f) ↔
      ∃ x : VSym L N, (valSym x : SymL2 L N) = ψ ∧
        ∀ (φ : (Fin N → ℝ) → ℂ) (hφ : IsTorusTest L φ),
          kinPairing hφ x.1 + contactPairing c hφ x.1 =
            ∫ y, conj (liftK (L := L) φ y) * ((f : L2TN L N) : _ → ℂ) y ∂(torusPiMeasure L N) := by
  rw [contact_distdomain hc ψ f]
  refine exists_congr fun x => and_congr_right fun _ => ⟨fun h φ hφ => ?_, fun h φ hφ _ => h φ hφ⟩
  have hS := h (avgTest φ) (isTorusTest_avg hφ) (symmFun_avg φ)
  calc kinPairing hφ x.1 + contactPairing c hφ x.1 = q c (smoothH1 hφ) x.1 :=
        (q_smooth_eq_pairings c hφ x.1).symm
    _ = q c (smoothH1 (isTorusTest_avg hφ)) x.1 := (q_avg_eq c hφ x).symm
    _ = kinPairing (isTorusTest_avg hφ) x.1 + contactPairing c (isTorusTest_avg hφ) x.1 :=
        q_smooth_eq_pairings c _ x.1
    _ = _ := hS
    _ = ⟪(smoothH1 (isTorusTest_avg hφ)).val, (f : L2TN L N)⟫_ℂ :=
        (inner_smoothH1_rhs (isTorusTest_avg hφ) _).symm
    _ = ⟪(smoothH1 hφ).val, (f : L2TN L N)⟫_ℂ := inner_avg_eq hφ f
    _ = _ := inner_smoothH1_rhs hφ _

end Averaging


section Uniqueness
open scoped LinearPMap
variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-- `H_{N,c}` is symmetric on its domain (consequence of self-adjointness). -/
theorem Hop_symmetric {c : ℝ} (hc : 0 ≤ c) (x y : (Hop (L := L) (N := N) c hc).domain) :
    ⟪Hop c hc x, (y : SymL2 L N)⟫_ℂ = ⟪(x : SymL2 L N), Hop c hc y⟫_ℂ := by
  have h : (Hop (L := L) (N := N) c hc)† = Hop c hc := Hop_isSelfAdjoint hc
  have hD : Dense ((Hop (L := L) (N := N) c hc).domain : Set (SymL2 L N)) :=
    (Hop_isSelfAdjoint hc).dense_domain
  obtain ⟨hdom, hval⟩ := (le_of_eq h.symm : Hop (L := L) (N := N) c hc ≤ (Hop c hc)†)
  have key := LinearPMap.adjoint_isFormalAdjoint hD ⟨(x : SymL2 L N), hdom x.2⟩ y
  have hx : Hop c hc x = (Hop c hc)† ⟨(x : SymL2 L N), hdom x.2⟩ := hval rfl
  rw [hx]
  exact key

/-- **Uniqueness of the associated self-adjoint operator** (source: "its unique associated
self-adjoint nonnegative operator"; "this also proves uniqueness"): any self-adjoint operator `T`
on `L²_sym` whose domain/action satisfy the variational identity
`q(φ,ψ) = ⟨φ, Tψ⟩` for all `φ ∈ D(q) = H¹_sym` is `H_{N,c}`. -/
theorem eq_Hop_of_selfAdjoint_variational {c : ℝ} (hc : 0 ≤ c)
    (T : SymL2 L N →ₗ.[ℂ] SymL2 L N) (hT : IsSelfAdjoint T)
    (hvar : ∀ ψ : T.domain, ∃ x : VSym L N, (valSym x : SymL2 L N) = (ψ : SymL2 L N) ∧
      ∀ φ : VSym L N, q c φ.1 x.1 = ⟪(valSym φ : SymL2 L N), T ψ⟫_ℂ) :
    T = Hop c hc := by
  -- `T ≤ H`
  have hsub : ∀ ψ : T.domain, ∃ h : (ψ : SymL2 L N) ∈ (Hop (L := L) (N := N) c hc).domain,
      Hop c hc ⟨ψ, h⟩ = T ψ := by
    intro ψ
    obtain ⟨x, hx, hq⟩ := hvar ψ
    obtain ⟨h, hH⟩ := mem_domain_of_variational hc x (T ψ) hq
    have hψ : (ψ : SymL2 L N) = valSym x := hx.symm
    refine ⟨hψ ▸ h, ?_⟩
    have : (⟨(ψ : SymL2 L N), hψ ▸ h⟩ : (Hop (L := L) (N := N) c hc).domain) =
        ⟨valSym x, h⟩ := Subtype.ext hψ
    rw [this]
    exact hH
  have hTH : T ≤ Hop c hc := by
    refine ⟨fun ψ hψ => (hsub ⟨ψ, hψ⟩).1, fun x y hxy => ?_⟩
    obtain ⟨h, hH⟩ := hsub x
    have : y = ⟨(x : SymL2 L N), h⟩ := Subtype.ext hxy.symm
    rw [this, hH]
  -- `H ≤ T†  = T`
  have hfa : T.IsFormalAdjoint (Hop c hc) := by
    intro x y
    obtain ⟨h, hH⟩ := hsub x
    have h1 : Hop c hc ⟨(x : SymL2 L N), h⟩ = T x := hH
    rw [← h1]
    exact Hop_symmetric hc ⟨(x : SymL2 L N), h⟩ y
  have hHT : Hop c hc ≤ T := by
    have := LinearPMap.IsFormalAdjoint.le_adjoint hT.dense_domain hfa
    have hT' : T† = T := hT
    rwa [hT'] at this
  exact LinearPMap.eq_of_le_of_domain_eq hTH (le_antisymm hTH.1 hHT.1)

end Uniqueness


section Assembled
open scoped LinearPMap
variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-- `T` is the operator associated with the form `q_{N,c}` with form domain `H¹_sym`:
`ψ ∈ D(T)`, `Tψ = f` iff `ψ = val x`, `x ∈ H¹_sym`, and `q(φ,x) = ⟨φ,f⟩` for every `φ ∈ H¹_sym`. -/
def IsAssociated (c : ℝ) (T : SymL2 L N →ₗ.[ℂ] SymL2 L N) : Prop :=
  ∀ ψ f : SymL2 L N, (∃ h : ψ ∈ T.domain, T ⟨ψ, h⟩ = f) ↔
    ∃ x : VSym L N, (valSym x : SymL2 L N) = ψ ∧
      ∀ φ : VSym L N, q c φ.1 x.1 = ⟪(valSym φ : SymL2 L N), f⟫_ℂ

theorem Hop_isAssociated {c : ℝ} (hc : 0 ≤ c) : IsAssociated c (Hop (L := L) (N := N) c hc) := by
  intro ψ f
  refine (mem_domain_iff_testwise hc Set.univ (fun _ _ _ => Set.mem_univ _) ψ f).trans ?_
  simp only [Set.mem_univ, forall_const]

theorem eq_Hop_of_isAssociated {c : ℝ} (hc : 0 ≤ c) (T : SymL2 L N →ₗ.[ℂ] SymL2 L N)
    (hT : IsSelfAdjoint T) (h : IsAssociated c T) : T = Hop c hc :=
  eq_Hop_of_selfAdjoint_variational hc T hT fun ψ => (h ψ (T ψ)).1 ⟨ψ.2, rfl⟩

theorem Hop_apply_of_Rop {c : ℝ} (hc : 0 ≤ c) (ψ : (Hop (L := L) (N := N) c hc).domain)
    (g : SymL2 L N) (hg : Rop c hc g = (ψ : SymL2 L N)) : Hop c hc ψ = g - Rop c hc g := by
  obtain ⟨h, hH⟩ := Hop_Rop hc g
  have : ψ = ⟨Rop c hc g, h⟩ := Subtype.ext hg.symm
  rw [this]
  exact eq_sub_of_add_eq hH

theorem Hop_domain_nonneg {c : ℝ} (hc : 0 ≤ c) (ψ : (Hop (L := L) (N := N) c hc).domain) :
    0 ≤ (⟪(ψ : SymL2 L N), Hop c hc ψ⟫_ℂ).re := by
  obtain ⟨g, hg⟩ := ψ.2
  have hg' : Rop c hc g = (ψ : SymL2 L N) := hg
  rw [Hop_apply_of_Rop hc ψ g hg', ← hg']
  exact Hop_nonneg hc g

theorem Rop_Hop_add {c : ℝ} (hc : 0 ≤ c) (ψ : (Hop (L := L) (N := N) c hc).domain) :
    Rop c hc (Hop c hc ψ + (ψ : SymL2 L N)) = ψ := by
  obtain ⟨g, hg⟩ := ψ.2
  have hg' : Rop c hc g = (ψ : SymL2 L N) := hg
  rw [Hop_apply_of_Rop hc ψ g hg', ← hg']
  congr 1
  abel

/-- The exact printed measure on the collision coordinates: `dy_ij` is Lebesgue on the common
coordinate times the product Lebesgue measure on the remaining `N-2` circles (not the surface
measure `dS = √2 dy`). -/
theorem dyij_eq (i j : Fin N) :
    (dyij (L := L) i j) =
      (volume : Measure (AddCircle L)).prod
        (Measure.pi fun _ : Rest N i j => (volume : Measure (AddCircle L))) := rfl

/-- **`contact:thm:form` (R-98129FE7, `A01.tex:37-60`), assembled** for `c ≥ 0`:
(i) `D(q) = H¹_sym` is dense in `L²_sym`; (ii) `q` is closed (complete in the form norm, limits
symmetric); (iii) `q` is Hermitian and nonnegative; (iv) there is a unique self-adjoint operator
associated with `q` (exact form-domain characterization), and it is nonnegative;
(v) its resolvent `R = (H+I)⁻¹` is compact; (vi) its domain is exactly the distributional domain
`{ψ ∈ H¹_sym : -Δψ + 2c Σ δ_L(x_i-x_j) T_ijψ is represented by `f ∈ 𝓗_N`}` with arbitrary smooth
lattice-periodic test functions, `H ψ = f`, coefficient `2c` and the coordinate measure `dy_ij`
(`kinPairing`, `contactPairing`); `f` is unique. -/
theorem contact_thm_form {c : ℝ} (hc : 0 ≤ c) :
    DenseRange (valSym : (PhysH1.sym : Submodule ℂ (PhysH1 L N)) →L[ℂ] SymL2 L N) ∧
    (∀ u : ℕ → PhysH1 L N, (∀ n, u n ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L N))) →
      (∀ ε > 0, ∃ n₀ : ℕ, ∀ m n, n₀ ≤ m → n₀ ≤ n → formNormSq c (u m - u n) < ε) →
      ∃ x : PhysH1 L N, x ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L N)) ∧
        Filter.Tendsto (fun n => formNormSq c (u n - x)) Filter.atTop (nhds 0)) ∧
    ((∀ φ ψ : PhysH1 L N, conj (q c φ ψ) = q c ψ φ) ∧ ∀ ψ : PhysH1 L N, 0 ≤ (q c ψ ψ).re) ∧
    (∃! T : SymL2 L N →ₗ.[ℂ] SymL2 L N, IsSelfAdjoint T ∧ IsAssociated c T ∧
      ∀ ψ : T.domain, 0 ≤ (⟪(ψ : SymL2 L N), T ψ⟫_ℂ).re) ∧
    (IsCompactOperator (Rop c hc : SymL2 L N →L[ℂ] SymL2 L N) ∧
      (∀ g : SymL2 L N, ∃ h : Rop c hc g ∈ (Hop (L := L) (N := N) c hc).domain,
        Hop c hc ⟨Rop c hc g, h⟩ + Rop c hc g = g) ∧
      ∀ ψ : (Hop (L := L) (N := N) c hc).domain,
        Rop c hc (Hop c hc ψ + (ψ : SymL2 L N)) = ψ) ∧
    (∀ ψ f : SymL2 L N,
      ((∃ h : ψ ∈ (Hop (L := L) (N := N) c hc).domain, Hop c hc ⟨ψ, h⟩ = f) ↔
        ∃ x : VSym L N, (valSym x : SymL2 L N) = ψ ∧
          ∀ (φ : (Fin N → ℝ) → ℂ) (hφ : IsTorusTest L φ),
            kinPairing hφ x.1 + contactPairing c hφ x.1 =
              ∫ y, conj (liftK (L := L) φ y) * ((f : L2TN L N) : _ → ℂ) y
                ∂(torusPiMeasure L N)) ∧
      ∀ f' : SymL2 L N, (∃ h : ψ ∈ (Hop (L := L) (N := N) c hc).domain, Hop c hc ⟨ψ, h⟩ = f) →
        (∃ h : ψ ∈ (Hop (L := L) (N := N) c hc).domain, Hop c hc ⟨ψ, h⟩ = f') → f = f') := by
  refine ⟨denseRange_valSym, fun u hs hu => form_complete_sym hc u hs hu,
    ⟨fun φ ψ => q_conj_symm c φ ψ, fun ψ => q_nonneg hc ψ⟩, ?_, ?_, ?_⟩
  · refine ⟨Hop c hc, ⟨Hop_isSelfAdjoint hc, Hop_isAssociated hc, Hop_domain_nonneg hc⟩, ?_⟩
    rintro T ⟨hT, hA, -⟩
    exact eq_Hop_of_isAssociated hc T hT hA
  · exact ⟨Hop_compact_resolvent hc, Hop_Rop hc, Rop_Hop_add hc⟩
  · intro ψ f
    refine ⟨contact_distdomain_all hc ψ f, ?_⟩
    rintro f' ⟨h, hf⟩ ⟨h', hf'⟩
    rw [← hf, ← hf']

end Assembled

end QuantumNLS.ContactFormTheorem
