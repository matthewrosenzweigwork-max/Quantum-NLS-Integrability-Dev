import QuantumNLS.LinearTailSourceStrong
import QuantumNLS.LinearTailSourceEstimates
import QuantumNLS.MarginalEnergy
import QuantumNLS.ContactOperator
import QuantumNLS.TraceIdeal

/-! The actual fixed-rank source error, as a supremum over finite tail
weights and positive trace-one states with bounded kinetic energy. Compactness
of the kinetic inverse, rather than operator-norm convergence of T, controls it. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Filter Topology Set
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.LinearTailKineticError
open TensorCarrier PhysicalTensor EnergyPreparationDef PhysicalEnergyTrace
open LinearTailGenerator LinearTailSourceStrong GridStrongSum TraceClass TraceIdeal
variable (L : ℝ) [Fact (0 < L)]

/-- Literal zero extension of the finite-support rank-r source kernel. -/
def fullT (n : ℕ) (s : Finset ℤ) (t : ℤ → ℝ) : Xk L (n + 1) →L[ℂ] Xk L (n + 1) :=
  TensorPlacements.extendSymKernel (finiteT L (n + 1) s t)

theorem fullT_norm (n : ℕ) (s : Finset ℤ) (t : ℤ → ℝ) (ht : ∀ m ∈ s, |t m| ≤ 1) :
    ‖fullT L n s t‖ ≤ Bd L (n + 1) :=
  (TensorPlacements.norm_extendSymKernel_le _).trans (finiteT_norm L n s t ht)

/-- Compactness of the actual inverse kinetic square root on the marginal carrier. -/
theorem compact_weight (r : ℕ) : IsCompactOperator (W L r) := by
  unfold W physW pull
  exact ((ContactOperator.isCompactOperator_AhalfInv (L := L) (N := r)).comp_clm
    (eK L r).toContinuousLinearEquiv.toContinuousLinearMap).clm_comp
      (eK L r).symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- Strong compact-uniform tail, applied to the compact kinetic image of
the full marginal unit ball. This is an operator-norm estimate for T W,
not an assertion that T itself converges in operator norm. -/
theorem weighted_tail (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ : ℕ, ∀ R ≥ R₀, ∀ (s : Finset ℤ) (t : ℤ → ℝ),
      (∀ m ∈ s, |t m| ≤ 1) → (∀ m ∈ s, (R : ℤ) < |m|) →
      ‖fullT L n s t * W L (n + 1)‖ ≤ ε := by
  let P := TensorPlacements.symProjToSector (H := L2T L) (n + 1)
  let K := P.comp (W L (n + 1))
  have hc : IsCompactOperator K := (compact_weight L (n + 1)).clm_comp P
  let C := closure (K '' Metric.closedBall 0 1)
  have hC : IsCompact C := hc.isCompact_closure_image_closedBall 1
  obtain ⟨R₀, hR₀⟩ := finiteT_compact_tail L n C hC ε hε
  refine ⟨R₀, fun R hR s t ht hs => ?_⟩
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hε.le
  intro v hv
  have hv' : v ∈ Metric.closedBall (0 : Xk L (n + 1)) 1 := by simp [hv]
  have hh := hR₀ R hR s t ht hs (K v) (subset_closure (mem_image_of_mem K hv'))
  exact hh

/-- Square root of the actual positive sandwich trace, the source
quadratic error for a marginal. -/
def quadraticError {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    (S ρ : X →L[ℂ] X) : ℝ :=
  Real.sqrt ((traceNorm (S * ρ * ContinuousLinearMap.adjoint S)).toReal)

/-- The uniform factorial bound, independent of the energy. -/
theorem quadraticError_bound (n : ℕ) (s : Finset ℤ) (t : ℤ → ℝ)
    (ht : ∀ m ∈ s, |t m| ≤ 1) {ρ : Xk L (n + 1) →L[ℂ] Xk L (n + 1)}
    (hρ : ρ.IsPositive) (htr : posTrace ρ = 1) :
    quadraticError (fullT L n s t) ρ ≤ Bd L (n + 1) := by
  have htρ : traceNorm ρ = 1 := by rw [traceNorm_of_isPositive hρ, htr]
  have hh := traceNorm_mul_mul_le (fullT L n s t) ρ (ContinuousLinearMap.adjoint (fullT L n s t))
  rw [htρ, mul_one, LinearIsometryEquiv.norm_map] at hh
  have hb := fullT_norm L n s t ht
  have hB := Bd_nonneg L (n + 1)
  have hh' : traceNorm (fullT L n s t * ρ * ContinuousLinearMap.adjoint (fullT L n s t)) ≤
      ENNReal.ofReal (Bd L (n + 1) ^ 2) := by
    refine hh.trans ?_
    rw [pow_two, ENNReal.ofReal_mul hB]
    gcongr
  exact (Real.sqrt_le_iff).mpr ⟨hB, ENNReal.toReal_le_of_le_ofReal (sq_nonneg _) hh'⟩

/-- Energy realization turns compactness of W into the uniform source
quadratic estimate. No marginal-tail conclusion is supplied as a hypothesis. -/
theorem quadraticError_energy_bound (n : ℕ) (S : Xk L (n + 1) →L[ℂ] Xk L (n + 1))
    {ρ : Xk L (n + 1) →L[ℂ] Xk L (n + 1)} (hρ : ρ.IsPositive)
    {C : ℝ} (hC : 0 ≤ C) (henergy : energyTrace ρ ≤ ENNReal.ofReal C) :
    quadraticError S ρ ≤ ‖S * W L (n + 1)‖ * Real.sqrt C := by
  have hfin : energyTrace ρ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top henergy
  obtain ⟨T, hT, -, hspec, htr⟩ := phys_realization hρ hfin
  have ht : traceNorm T ≤ ENNReal.ofReal C := by rw [traceNorm_of_isPositive hT, htr]; exact henergy
  have hW : ContinuousLinearMap.adjoint (W L (n + 1)) = W L (n + 1) := by
    exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr
      (fun x y => W_inner x y)
  have he : S * ρ * ContinuousLinearMap.adjoint S =
      (S * W L (n + 1)) * T * ContinuousLinearMap.adjoint (S * W L (n + 1)) := by
    rw [hspec]
    simp only [← ContinuousLinearMap.star_eq_adjoint, star_mul]
    rw [show star (W L (n + 1)) = W L (n + 1) from hW]
    noncomm_ring
  have hh := traceNorm_mul_mul_le (S * W L (n + 1)) T
    (ContinuousLinearMap.adjoint (S * W L (n + 1)))
  rw [LinearIsometryEquiv.norm_map] at hh
  have hb : traceNorm (S * ρ * ContinuousLinearMap.adjoint S) ≤
      ENNReal.ofReal ((‖S * W L (n + 1)‖ * Real.sqrt C) ^ 2) := by
    rw [he]
    refine hh.trans ?_
    rw [mul_pow, Real.sq_sqrt hC, pow_two,
      ENNReal.ofReal_mul (mul_nonneg (norm_nonneg _) (norm_nonneg _)),
      ENNReal.ofReal_mul (norm_nonneg _)]
    calc
      _ ≤ ENNReal.ofReal ‖S * W L (n + 1)‖ * ENNReal.ofReal C *
          ENNReal.ofReal ‖S * W L (n + 1)‖ := by gcongr
      _ = _ := by ring
  exact Real.sqrt_le_iff.mpr ⟨mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg C),
    ENNReal.toReal_le_of_le_ofReal (sq_nonneg _) hb⟩

/-- Uniform vanishing over the actual positive trace-one kinetic-energy
set and all finitely supported high-label real contractions. -/
theorem uniform_quadratic_tail (n : ℕ) {E : ℝ} (hE : 0 ≤ E) {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ : ℕ, ∀ R ≥ R₀, ∀ (s : Finset ℤ) (t : ℤ → ℝ),
      (∀ m ∈ s, |t m| ≤ 1) → (∀ m ∈ s, (R : ℤ) < |m|) →
      ∀ ρ : Xk L (n + 1) →L[ℂ] Xk L (n + 1), ρ.IsPositive →
      posTrace ρ = 1 → energyTrace ρ ≤ ENNReal.ofReal (1 + (n + 1 : ℝ) * E) →
      quadraticError (fullT L n s t) ρ ≤ ε := by
  let C : ℝ := 1 + (n + 1 : ℝ) * E
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let δ : ℝ := ε / (Real.sqrt C + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨R₀, hR₀⟩ := weighted_tail L n hδ
  refine ⟨R₀, fun R hR s t ht hs ρ hρ _ henergy => ?_⟩
  refine (quadraticError_energy_bound L n (fullT L n s t) hρ hC henergy).trans ?_
  refine (mul_le_mul_of_nonneg_right (hR₀ R hR s t ht hs) (Real.sqrt_nonneg _)).trans ?_
  dsimp [δ]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : 0 < Real.sqrt C + 1)).mpr
  nlinarith [Real.sqrt_nonneg C]

/-- Positive-sandwich trace interpretation of the quadratic error. -/
theorem quadraticError_eq_posTrace (n : ℕ)
    (S ρ : Xk L (n + 1) →L[ℂ] Xk L (n + 1)) (hρ : ρ.IsPositive) :
    quadraticError S ρ = Real.sqrt ((posTrace
      (S * ρ * ContinuousLinearMap.adjoint S)).toReal) := by
  unfold quadraticError
  have hp : (S * ρ * ContinuousLinearMap.adjoint S).IsPositive := by
    simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc] using hρ.conj_adjoint S
  rw [traceNorm_of_isPositive hp]

/-- The source's admissible quadratic errors, including zero so that the
supremum is defined even when the state constraint is empty. -/
def errors (n : ℕ) (E : ℝ) (R : ℕ) : Set ℝ :=
  {a | a = 0 ∨ ∃ (s : Finset ℤ) (t : ℤ → ℝ)
    (ρ : Xk L (n + 1) →L[ℂ] Xk L (n + 1)),
    (∀ m ∈ s, |t m| ≤ 1) ∧ (∀ m ∈ s, (R : ℤ) < |m|) ∧
    ρ.IsPositive ∧ posTrace ρ = 1 ∧
    energyTrace ρ ≤ ENNReal.ofReal (1 + (n + 1 : ℝ) * E) ∧
    a = quadraticError (fullT L n s t) ρ}

/-- Literal supremum error for r=n+1, uniformly over the state and all
finite tail weights. -/
def sourceError (n : ℕ) (E : ℝ) (R : ℕ) : ℝ := sSup (errors L n E R)

theorem errors_bounded (n : ℕ) (E : ℝ) (R : ℕ) : BddAbove (errors L n E R) := by
  refine ⟨Bd L (n + 1), ?_⟩
  intro a ha
  rcases ha with rfl | ⟨s, t, ρ, ht, _, hρ, htr, _, rfl⟩
  · exact Bd_nonneg L _
  · exact quadraticError_bound L n s t ht hρ htr

theorem error_nonneg (n : ℕ) (E : ℝ) (R : ℕ) : 0 ≤ sourceError L n E R :=
  le_csSup (errors_bounded L n E R) (Or.inl rfl)

theorem error_bound (n : ℕ) (E : ℝ) (R : ℕ) : sourceError L n E R ≤ Bd L (n + 1) := by
  refine csSup_le (s := errors L n E R) ⟨0, Or.inl rfl⟩ ?_
  intro a ha
  rcases ha with rfl | ⟨s, t, ρ, ht, _, hρ, htr, _, rfl⟩
  · exact Bd_nonneg L _
  · exact quadraticError_bound L n s t ht hρ htr

theorem quadraticError_le_error (n : ℕ) (E : ℝ) (R : ℕ)
    (s : Finset ℤ) (t : ℤ → ℝ) (ht : ∀ m ∈ s, |t m| ≤ 1)
    (hs : ∀ m ∈ s, (R : ℤ) < |m|)
    {ρ : Xk L (n + 1) →L[ℂ] Xk L (n + 1)} (hρ : ρ.IsPositive)
    (htr : posTrace ρ = 1) (henergy : energyTrace ρ ≤ ENNReal.ofReal (1 + (n + 1 : ℝ) * E)) :
    quadraticError (fullT L n s t) ρ ≤ sourceError L n E R :=
  le_csSup (errors_bounded L n E R) (Or.inr ⟨s, t, ρ, ht, hs, hρ, htr, henergy, rfl⟩)

/-- Vanishing of the actual supremum error, with its exact factorial bound. -/
theorem error_tendsto (n : ℕ) {E : ℝ} (hE : 0 ≤ E) :
    Tendsto (sourceError L n E) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨R₀, hR₀⟩ := uniform_quadratic_tail L n hE (half_pos hε)
  refine ⟨R₀, fun R hR => ?_⟩
  have hb : sourceError L n E R ≤ ε / 2 := by
    refine csSup_le (s := errors L n E R) ⟨0, Or.inl rfl⟩ ?_
    intro a ha
    rcases ha with rfl | ⟨s, t, ρ, ht, hs, hρ, htr, he, rfl⟩
    · linarith
    · exact hR₀ R hR s t ht hs ρ hρ htr he
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (error_nonneg L n E R)]
  linarith

/-- The literal source rank series now vanishes for the constructed error,
with no supplied per-rank convergence premise. -/
theorem source_error_series {κ E : ℝ} (hκ : 0 ≤ κ) (hE : 0 ≤ E) :
    (∀ R, Summable (fun n : ℕ => ((n : ℝ) + 1) * κ ^ n * sourceError L n E R)) ∧
      Tendsto (fun R => ∑' n : ℕ, ((n : ℝ) + 1) * κ ^ n * sourceError L n E R) atTop (𝓝 0) :=
  LinearTailSourceEstimates.error_series_tendsto L κ hκ (fun n R => sourceError L n E R)
    (fun n R => error_nonneg L n E R) (fun n R => error_bound L n E R)
    (fun n => error_tendsto L n hE)

end QuantumNLS.LinearTailKineticError

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.LinearTailKineticError.fullT
#print axioms QuantumNLS.LinearTailKineticError.fullT_norm
#print axioms QuantumNLS.LinearTailKineticError.compact_weight
#print axioms QuantumNLS.LinearTailKineticError.weighted_tail
#print axioms QuantumNLS.LinearTailKineticError.quadraticError
#print axioms QuantumNLS.LinearTailKineticError.quadraticError_bound
#print axioms QuantumNLS.LinearTailKineticError.quadraticError_energy_bound
#print axioms QuantumNLS.LinearTailKineticError.uniform_quadratic_tail
#print axioms QuantumNLS.LinearTailKineticError.quadraticError_eq_posTrace
#print axioms QuantumNLS.LinearTailKineticError.errors
#print axioms QuantumNLS.LinearTailKineticError.sourceError
#print axioms QuantumNLS.LinearTailKineticError.errors_bounded
#print axioms QuantumNLS.LinearTailKineticError.error_nonneg
#print axioms QuantumNLS.LinearTailKineticError.error_bound
#print axioms QuantumNLS.LinearTailKineticError.quadraticError_le_error
#print axioms QuantumNLS.LinearTailKineticError.error_tendsto
#print axioms QuantumNLS.LinearTailKineticError.source_error_series

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.LinearTailKineticError." then
      pending := pending.push n
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
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
