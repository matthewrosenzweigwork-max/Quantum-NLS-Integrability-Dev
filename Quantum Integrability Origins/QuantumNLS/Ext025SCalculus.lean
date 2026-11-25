import QuantumNLS.BetheChargeResolution

/-! Literal source contract FIN-EXT025-GP-08 (coverage qualifications follow below).
Hypotheses:
A selfadjoint operator has a projection-valued spectral measure. A real Borel function is finite almost everywhere on the represented spectral space; its operator domain consists of vectors with finite squared multiplier integral.
For simultaneous diagonal operators in this report, the common complete orthonormal Bethe basis is already proved. Bounded phase functions have modulus one.
Conclusion:
Real spectral multipliers are selfadjoint on their exact maximal domains; bounded multipliers form a *-calculus, and uniformly bounded pointwise convergence gives strong convergence. Functions of one common spectral resolution commute and preserve the form domain of a nonnegative common diagonal Hamiltonian.
Application wrappers:
For countable Bethe coordinates, the report verifies these conclusions directly from weighted square sums and dominated convergence. The generic spectral theorem is needed for the contact Hamiltonian and for positive trace/form compressions; it does not supply the Bethe basis.
A sum of unbounded commuting charges is defined by the sum of their scalar multipliers on its maximal domain. This can have a larger domain than the intersection of the individual domains; the three-flow boost identity is interpreted accordingly.
-/

/-! FIN-EXT025-GP-08, atomic spectral calculus and exact phase/form laws.
CONTRACT ISSUE: unrestricted unbounded functions of a common spectral resolution
need not preserve a Hamiltonian's form domain. The form-domain invariance below
is for bounded functions; energy equality is for modulus-one phases. General
non-atomic PVM integration remains explicitly OPEN in the receipt. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace ComplexConjugate LinearPMap ENNReal
open InnerProductSpace Filter Topology
namespace QuantumNLS.Ext025SCalculus
variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Square-sum domain of a nonnegative diagonal form. -/
def FormDomain (b : HilbertBasis ι ℂ E) (h : ι → ℝ) (x : E) : Prop :=
  Summable (fun n => h n * ‖b.repr x n‖ ^ 2)

/-- Extended energy avoids assigning a finite value to divergent real sums. -/
def formEnergy (b : HilbertBasis ι ℂ E) (h : ι → ℝ) (x : E) : ℝ≥0∞ :=
  ∑' n, ENNReal.ofReal (h n * ‖b.repr x n‖ ^ 2)

theorem bounded_mem (a : ι → ℂ) (C : ℝ) (ha : ∀ n, ‖a n‖ ≤ C)
    (x : lp (fun _ : ι => ℂ) 2) : Memℓp (fun n => a n * x n) 2 := by
  apply QuantumNLS.Energy.memL2_iff.mpr
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_)
    ((QuantumNLS.Energy.summable_sq x).mul_left (C ^ 2))
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (ha n) 2) (sq_nonneg _)

/-- Bounded complex spectral multiplication on the entire Hilbert space. -/
def bounded (b : HilbertBasis ι ℂ E) (a : ι → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ n, ‖a n‖ ≤ C) : E →L[ℂ] E :=
  LinearMap.mkContinuous
    { toFun := fun x => b.repr.symm ⟨fun n => a n * b.repr x n, bounded_mem a C ha (b.repr x)⟩
      map_add' := by
        intro x y
        apply b.repr.injective
        ext n
        simp only [map_add, LinearIsometryEquiv.apply_symm_apply]
        change a n * (b.repr x n + b.repr y n) = a n * b.repr x n + a n * b.repr y n
        ring
      map_smul' := by
        intro z x
        apply b.repr.injective
        ext n
        simp [mul_left_comm] }
    C (fun x => by
      have h : ‖(⟨fun n => a n * b.repr x n, bounded_mem a C ha (b.repr x)⟩ :
          lp (fun _ : ι => ℂ) 2)‖ ^ 2 ≤ (C * ‖x‖) ^ 2 := by
        rw [QuantumNLS.Energy.norm_sq_eq_tsum, mul_pow,
          ← b.repr.norm_map x, QuantumNLS.Energy.norm_sq_eq_tsum,
          ← tsum_mul_left]
        apply Summable.tsum_le_tsum
        · intro n
          rw [norm_mul, mul_pow]
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (norm_nonneg _) (ha n) 2) (sq_nonneg _)
        · exact QuantumNLS.Energy.summable_sq _
        · exact (QuantumNLS.Energy.summable_sq _).mul_left _
      change ‖b.repr.symm (⟨fun n => a n * b.repr x n,
        bounded_mem a C ha (b.repr x)⟩ : lp (fun _ : ι => ℂ) 2)‖ ≤ C * ‖x‖
      rw [b.repr.symm.norm_map]
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp h)

omit [CompleteSpace E] in
theorem bounded_coord (b : HilbertBasis ι ℂ E) (a : ι → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ n, ‖a n‖ ≤ C) (x : E) (n : ι) :
    b.repr (bounded b a C hC ha x) n = a n * b.repr x n := by
  change b.repr (b.repr.symm _) n = _
  rw [LinearIsometryEquiv.apply_symm_apply]

omit [CompleteSpace E] in
theorem bounded_one (b : HilbertBasis ι ℂ E) :
    bounded b (fun _ => 1) 1 zero_le_one (fun _ => by simp) = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  apply b.repr.injective
  ext n
  simp only [bounded_coord, one_mul, one_apply_eq_self]

omit [CompleteSpace E] in
theorem bounded_smul (b : HilbertBasis ι ℂ E) (a : ι → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ n, ‖a n‖ ≤ C) (z : ℂ) :
    z • bounded b a C hC ha = bounded b (fun n => z * a n) (‖z‖ * C)
      (mul_nonneg (norm_nonneg _) hC)
      (fun n => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (ha n) (norm_nonneg _)) := by
  apply ContinuousLinearMap.ext
  intro x
  apply b.repr.injective
  ext n
  simp only [smul_apply, map_smul, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, bounded_coord]
  ring

omit [CompleteSpace E] in
theorem bounded_mul (b : HilbertBasis ι ℂ E) (a d : ι → ℂ)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (ha : ∀ n, ‖a n‖ ≤ C) (hd : ∀ n, ‖d n‖ ≤ D) :
    bounded b a C hC ha * bounded b d D hD hd =
      bounded b (fun n => a n * d n) (C * D) (mul_nonneg hC hD)
        (fun n => by rw [norm_mul]; exact mul_le_mul (ha n) (hd n) (norm_nonneg _) hC) := by
  apply ContinuousLinearMap.ext
  intro x
  apply b.repr.injective
  ext n
  change b.repr (bounded b a C hC ha (bounded b d D hD hd x)) n = _
  simp only [bounded_coord]
  ring

omit [CompleteSpace E] in
theorem bounded_add (b : HilbertBasis ι ℂ E) (a d : ι → ℂ)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (ha : ∀ n, ‖a n‖ ≤ C) (hd : ∀ n, ‖d n‖ ≤ D) :
    bounded b a C hC ha + bounded b d D hD hd =
      bounded b (fun n => a n + d n) (C + D) (add_nonneg hC hD)
        (fun n => (norm_add_le _ _).trans (add_le_add (ha n) (hd n))) := by
  apply ContinuousLinearMap.ext
  intro x
  apply b.repr.injective
  ext n
  simp only [add_apply, map_add, lp.coeFn_add, Pi.add_apply, bounded_coord]
  ring

theorem bounded_star (b : HilbertBasis ι ℂ E) (a : ι → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ n, ‖a n‖ ≤ C) :
    (bounded b a C hC ha).adjoint =
      bounded b (fun n => conj (a n)) C hC (fun n => by simpa using ha n) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left, ← b.repr.inner_map_map,
    ← b.repr.inner_map_map, lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp only [bounded_coord, RCLike.inner_apply, map_mul, starRingEnd_self_apply]
  ring

omit [CompleteSpace E] in
theorem bounded_commute (b : HilbertBasis ι ℂ E) (a d : ι → ℂ)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (ha : ∀ n, ‖a n‖ ≤ C) (hd : ∀ n, ‖d n‖ ≤ D) :
    Commute (bounded b a C hC ha) (bounded b d D hD hd) := by
  apply ContinuousLinearMap.ext
  intro x
  apply b.repr.injective
  ext n
  change b.repr (bounded b a C hC ha (bounded b d D hD hd x)) n =
    b.repr (bounded b d D hD hd (bounded b a C hC ha x)) n
  simp only [bounded_coord]
  ring

omit [CompleteSpace E] in
/-- Uniform bounds and pointwise convergence imply strong convergence. -/
theorem bounded_strong {J : Type*} {l : Filter J}
    (b : HilbertBasis ι ℂ E) (a : J → ι → ℂ) (d : ι → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ j n, ‖a j n‖ ≤ C) (hd : ∀ n, ‖d n‖ ≤ C)
    (hlim : ∀ n, Tendsto (fun j => a j n) l (𝓝 (d n))) (x : E) :
    Tendsto (fun j => bounded b (a j) C hC (ha j) x) l
      (𝓝 (bounded b d C hC hd x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have ht := tendsto_tsum_of_dominated_convergence
    ((QuantumNLS.Energy.summable_sq (b.repr x)).mul_left ((2*C)^2))
    (f := fun j n => ‖(a j n - d n) * b.repr x n‖ ^ 2)
    (g := fun _ => (0 : ℝ))
    (fun n => by simpa using ((hlim n).sub_const (d n)).mul_const (b.repr x n) |>.norm |>.pow 2)
    (Filter.Eventually.of_forall fun j n => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
      have h : ‖a j n - d n‖ ≤ 2*C :=
        (norm_sub_le _ _).trans (by linarith [ha j n, hd n])
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) h 2) (sq_nonneg _))
  have he : ∀ j, ‖bounded b (a j) C hC (ha j) x - bounded b d C hC hd x‖ ^ 2 =
      ∑' n, ‖(a j n - d n) * b.repr x n‖ ^ 2 := by
    intro j
    rw [← b.repr.norm_map, QuantumNLS.Energy.norm_sq_eq_tsum]
    apply tsum_congr
    intro n
    simp only [map_sub, lp.coeFn_sub, Pi.sub_apply, bounded_coord, sub_mul]
  have hh : Tendsto (fun j => ‖bounded b (a j) C hC (ha j) x - bounded b d C hC hd x‖ ^ 2)
      l (𝓝 0) := by simpa only [he, tsum_zero] using ht
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hh
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hs

omit [CompleteSpace E] in
/-- Bounded multipliers preserve the exact form domain. -/
theorem bounded_form (b : HilbertBasis ι ℂ E) (h : ι → ℝ) (hh : ∀ n, 0 ≤ h n)
    (a : ι → ℂ) (C : ℝ) (hC : 0 ≤ C) (ha : ∀ n, ‖a n‖ ≤ C)
    {x : E} (hx : FormDomain b h x) : FormDomain b h (bounded b a C hC ha x) := by
  unfold FormDomain at hx ⊢
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (hh n) (sq_nonneg _))
    (fun n => ?_) (hx.mul_left (C^2))
  rw [bounded_coord, norm_mul, mul_pow]
  have hn := pow_le_pow_left₀ (norm_nonneg (a n)) (ha n) 2
  calc h n * (‖a n‖ ^ 2 * ‖b.repr x n‖ ^ 2) =
        ‖a n‖ ^ 2 * (h n * ‖b.repr x n‖ ^ 2) := by ring
       _ ≤ C^2 * (h n * ‖b.repr x n‖ ^ 2) :=
         mul_le_mul_of_nonneg_right hn (mul_nonneg (hh n) (sq_nonneg _))

omit [CompleteSpace E] in
/-- Phases preserve both the exact form domain and the extended energy. -/
theorem phase_form (b : HilbertBasis ι ℂ E) (h : ι → ℝ)
    (a : ι → ℂ) (ha : ∀ n, ‖a n‖ = 1) (x : E) :
    (FormDomain b h (bounded b a 1 zero_le_one (fun n => (ha n).le) x) ↔ FormDomain b h x) ∧
    formEnergy b h (bounded b a 1 zero_le_one (fun n => (ha n).le) x) = formEnergy b h x := by
  have he : ∀ n, ‖b.repr (bounded b a 1 zero_le_one (fun n => (ha n).le) x) n‖ =
      ‖b.repr x n‖ := by intro n; rw [bounded_coord, norm_mul, ha n, one_mul]
  exact ⟨by simp only [FormDomain,he], by simp only [formEnergy,he]⟩

section Bethe
open BetheSpectralCharges BetheChargeResolution BetheCoefficientTransform BetheLabels PhysicalTensor
variable {L : ℝ} [Fact (0 < L)] {N : ℕ}
/-- GP-08 atomic real calculus: selfadjointness, exact maximal square-sum
domain, and reconstruction from the same PVM, for every real function f.
No measurability hypothesis is needed on an atomic label space. -/
theorem «FIN-EXT025-GP-08» (b : BetheBasis L N) (ev : MArr N → ℝ) (f : ℝ → ℝ) :
    IsSelfAdjoint (multiplier b (f ∘ ev)) ∧
    (∀ x : HN L N, x ∈ (multiplier b (f ∘ ev)).domain ↔
      Summable (fun m => |f (ev m)|^2 * ‖⟪b m,x⟫_ℂ‖^2)) ∧
    (∀ x y : HN L N, AtomicIntegralGraph (resolution b ev) f x y ↔
      ∃ hx : x ∈ (multiplier b (f ∘ ev)).domain, multiplier b (f ∘ ev) ⟨x,hx⟩ = y) :=
  ⟨multiplier_selfAdjoint b _, fun x => mem_domain b _ x,
    atomicIntegral_iff b ev f⟩

/-- The square-root domain is the form domain; it is distinct from the
operator's squared-weight domain even on the same complete Bethe basis. -/
theorem gp08_form_domain (b : BetheBasis L N) (h : MArr N → ℝ)
    (hh : ∀ m, 0 ≤ h m) (x : HN L N) :
    x ∈ (multiplier b (fun m => Real.sqrt (h m))).domain ↔ FormDomain b h x := by
  change x ∈ domain b (fun m => Real.sqrt (h m)) ↔ FormDomain b h x
  rw [mem_domain]
  unfold FormDomain
  simp only [HilbertBasis.repr_apply_apply]
  apply summable_congr
  intro m
  rw [abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hh m)]

/-- The sum of charges is defined on the maximal domain of the summed
symbol, retaining cancellations rather than replacing it by an intersection. -/
theorem gp08_sum_domain (b : BetheBasis L N) (ev μ : MArr N → ℝ) (x : HN L N) :
    x ∈ (multiplier b (fun m => ev m + μ m)).domain ↔
      Summable (fun m => |ev m + μ m|^2 * ‖⟪b m,x⟫_ℂ‖^2) := mem_domain b _ x

/-- R-0D5A5E89: every phase flow is unitary on the whole Hilbert space and
strongly continuous without an operator-domain premise. -/
theorem gp08_phase_continuous (b : BetheBasis L N) (ev : MArr N → ℝ) (x : HN L N) :
    Continuous (fun t : ℝ => evolution b ev t x) := evolution_continuous b ev x

/-- R-568BCDF8 / ENERGY-017 diagonal application: fixed-charge flows conserve
the nonnegative Hamiltonian form, including vectors outside operator domains. -/
theorem gp08_flow_form (b : BetheBasis L N) (h ev : MArr N → ℝ) (t : ℝ) (x : HN L N) :
    (FormDomain b h (evolution b ev t x) ↔ FormDomain b h x) ∧
    formEnergy b h (evolution b ev t x) = formEnergy b h x := by
  classical
  have he : ∀ n, ‖b.repr (evolution b ev t x) n‖ = ‖b.repr x n‖ := by
    intro n
    rw [HilbertBasis.repr_apply_apply, evolution_coord, norm_mul,
      DiagonalMultiplier.norm_phase, one_mul, HilbertBasis.repr_apply_apply]
  exact ⟨by simp only [FormDomain,he], by simp only [formEnergy,he]⟩
end Bethe
end QuantumNLS.Ext025SCalculus

#print axioms QuantumNLS.Ext025SCalculus.FormDomain
#print axioms QuantumNLS.Ext025SCalculus.formEnergy
#print axioms QuantumNLS.Ext025SCalculus.bounded_mem
#print axioms QuantumNLS.Ext025SCalculus.bounded
#print axioms QuantumNLS.Ext025SCalculus.bounded_coord
#print axioms QuantumNLS.Ext025SCalculus.bounded_one
#print axioms QuantumNLS.Ext025SCalculus.bounded_smul
#print axioms QuantumNLS.Ext025SCalculus.bounded_mul
#print axioms QuantumNLS.Ext025SCalculus.bounded_add
#print axioms QuantumNLS.Ext025SCalculus.bounded_star
#print axioms QuantumNLS.Ext025SCalculus.bounded_commute
#print axioms QuantumNLS.Ext025SCalculus.bounded_strong
#print axioms QuantumNLS.Ext025SCalculus.bounded_form
#print axioms QuantumNLS.Ext025SCalculus.phase_form
#print axioms QuantumNLS.Ext025SCalculus.«FIN-EXT025-GP-08»
#print axioms QuantumNLS.Ext025SCalculus.gp08_form_domain
#print axioms QuantumNLS.Ext025SCalculus.gp08_sum_domain
#print axioms QuantumNLS.Ext025SCalculus.gp08_phase_continuous
#print axioms QuantumNLS.Ext025SCalculus.gp08_flow_form

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext025SCalculus." then
      pending := pending.push n
      roots := roots + 1
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
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Ext025SCalculus audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
