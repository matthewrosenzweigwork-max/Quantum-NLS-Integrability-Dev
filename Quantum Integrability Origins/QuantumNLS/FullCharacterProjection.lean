import QuantumNLS.CountRotations

/-! DEF-054, ledger and dynamic_full_torus.tex, eq:dynft-Haar-seed.
The strong integral is taken on each vector, with the full product Haar probability.
The normalized complete physical basis is an explicit parameter. No seed, grading,
convergence, target-selected gauge, or nonlinear physical chart is assumed here.
The analytic support below proves continuity and integrability of the defining action.
-/
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal
noncomputable section
namespace QuantumNLS.FullCharacterProjection
open QuantumNLS.CountRotations QuantumNLS.BetheLabels
  QuantumNLS.BetheCoefficientTransform QuantumNLS.BetheOccupationGauge
local instance (α : Type*) : DecidableEq α := Classical.decEq α

theorem lp_sq_eq {ι : Type*} (x : lp (fun _ : ι => ℂ) 2) :
    ‖x‖ ^ 2 = ∑' n, ‖x n‖ ^ 2 := by
  simpa [Real.rpow_two] using
    (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) x).tsum_eq.symm

theorem lp_sq_summable {ι : Type*} (x : lp (fun _ : ι => ℂ) 2) :
    Summable (fun n => ‖x n‖ ^ 2) := by
  simpa [Real.rpow_two] using
    (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) x).summable

theorem continuousAt_lp_of_tail {ι X : Type*} [TopologicalSpace X] (Φ : X → lp (fun _ : ι => ℂ) 2) (p : X) (g : ι → ℝ)
    (hg : Summable g) (hdom : ∀ q n, ‖Φ q n - Φ p n‖ ^ 2 ≤ g n)
    (hcoord : ∀ n, ContinuousAt (fun q => Φ q n) p) : ContinuousAt Φ p := by
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε ^ 2 / 2 := by positivity
  obtain ⟨F, hF⟩ := ((tendsto_tsum_compl_atTop_zero g).eventually (gt_mem_nhds hε2)).exists
  have hη : 0 < ε ^ 2 / (2 * ((F.card : ℝ) + 1)) := by positivity
  have hn : ∀ n : ι, ∀ᶠ q in 𝓝 p, ‖Φ q n - Φ p n‖ ^ 2 < ε ^ 2 / (2 * ((F.card : ℝ) + 1)) := by
    intro n
    have h1 : Tendsto (fun q => ‖Φ q n - Φ p n‖ ^ 2) (𝓝 p) (𝓝 (‖Φ p n - Φ p n‖ ^ 2)) :=
      (((hcoord n).tendsto.sub_const _).norm).pow 2
    have h2 : ‖Φ p n - Φ p n‖ ^ 2 = 0 := by simp
    rw [h2] at h1
    exact h1.eventually (gt_mem_nhds hη)
  filter_upwards [(Filter.eventually_all_finset F).2 (fun n _ => hn n)] with q hq
  rw [dist_eq_norm]
  have hsq : ‖Φ q - Φ p‖ ^ 2 < ε ^ 2 := by
    rw [lp_sq_eq, ← (lp_sq_summable (Φ q - Φ p)).sum_add_tsum_subtype_compl F]
    have hfin : ∑ n ∈ F, ‖(Φ q - Φ p) n‖ ^ 2 ≤ F.card * (ε ^ 2 / (2 * ((F.card : ℝ) + 1))) := by
      calc ∑ n ∈ F, ‖(Φ q - Φ p) n‖ ^ 2
          ≤ ∑ n ∈ F, (ε ^ 2 / (2 * ((F.card : ℝ) + 1))) :=
            Finset.sum_le_sum (fun n hn' => (hq n hn').le)
        _ = _ := by simp
    have hfin2 : (F.card : ℝ) * (ε ^ 2 / (2 * ((F.card : ℝ) + 1))) < ε ^ 2 / 2 := by
      have hc : (0 : ℝ) ≤ F.card := Nat.cast_nonneg _
      have : (F.card : ℝ) * (ε ^ 2 / (2 * ((F.card : ℝ) + 1))) =
          ε ^ 2 / 2 * ((F.card : ℝ) / ((F.card : ℝ) + 1)) := by
        field_simp
      rw [this]
      have h3 : (F.card : ℝ) / ((F.card : ℝ) + 1) < 1 := by
        rw [div_lt_one (by positivity)]; linarith
      nlinarith
    have htail : ∑' n : {x : ι // x ∉ F}, ‖(Φ q - Φ p) n‖ ^ 2 ≤ ∑' n : {x : ι // x ∉ F}, g n := by
      refine Summable.tsum_le_tsum (fun n => ?_)
        ((lp_sq_summable (Φ q - Φ p)).comp_injective Subtype.val_injective)
        (hg.comp_injective Subtype.val_injective)
      simpa using hdom q n
    linarith
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hsq


variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

theorem countPhase_continuous (m : MArr N) : Continuous (fun θ => countPhase θ m) := by
  unfold countPhase Finsupp.prod
  exact continuous_finsetProd _ (fun n _ => (continuous_apply n).inv.pow _)

theorem rotation_coeff (b : BetheBasis L N) (θ : AngleTorus) (x : HN L N) (m : MArr N) :
    b.repr (quantumRotation b θ x) m = (countPhase θ m : ℂ) * b.repr x m := by
  change b.repr (b.repr.symm (diagonal (phaseGauge θ) N (b.repr x))) m = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem rotation_strong_continuous (b : BetheBasis L N) (x : HN L N) :
    Continuous (fun θ : AngleTorus => quantumRotation b θ x) := by
  have hc : Continuous (fun θ : AngleTorus => b.repr (quantumRotation b θ x)) := by
    rw [continuous_iff_continuousAt]
    intro θ
    apply continuousAt_lp_of_tail _ θ (fun m => 4 * ‖b.repr x m‖ ^ 2)
      ((lp_sq_summable (b.repr x)).mul_left 4)
    · intro φ m
      rw [rotation_coeff, rotation_coeff]
      have h := norm_sub_le ((countPhase φ m : ℂ) * b.repr x m)
        ((countPhase θ m : ℂ) * b.repr x m)
      simp only [norm_mul, Circle.norm_coe, one_mul] at h
      nlinarith [norm_nonneg (b.repr x m), norm_nonneg
        ((countPhase φ m : ℂ) * b.repr x m - (countPhase θ m : ℂ) * b.repr x m)]
    · intro m
      simp_rw [rotation_coeff]
      exact (((continuous_subtype_val.comp (countPhase_continuous m)).mul
        continuous_const)).continuousAt
  simpa only [Function.comp_def, LinearIsometryEquiv.symm_apply_apply] using b.repr.symm.continuous.comp hc

theorem inverse_rotation_strong_continuous (b : BetheBasis L N) (x : HN L N) :
    Continuous (fun θ : AngleTorus => (quantumRotation b θ).symm x) := by
  have he : ∀ θ : AngleTorus, (quantumRotation b θ).symm x = quantumRotation b θ⁻¹ x := by
    intro θ
    apply (quantumRotation b θ).injective
    apply b.repr.injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    ext m
    rw [rotation_coeff, rotation_coeff]
    have hi : countPhase θ⁻¹ (N := N) = fun m => (countPhase θ m)⁻¹ := by
      funext m
      simp [countPhase, Finsupp.prod, ← Finset.prod_inv_distrib]
    rw [hi]
    simp
  simp_rw [he]
  exact (rotation_strong_continuous b x).comp continuous_inv

/-- The full character `e^{i(θ_a-θ_b)}`. No coordinate is truncated. -/
def character (a c : ℤ) (θ : AngleTorus) : ℂ := ((θ a / θ c : Circle) : ℂ)

/-- The vector integrand `e^{i(θ_a-θ_b)} V_N(θ)^* T_N V_N(θ) x`. -/
def integrand (b : BetheBasis L N) (T : HN L N →L[ℂ] HN L N)
    (a c : ℤ) (x : HN L N) (θ : AngleTorus) : HN L N :=
  character a c θ • (quantumRotation b θ).symm (T (quantumRotation b θ x))

theorem integrand_continuous (b : BetheBasis L N) (T : HN L N →L[ℂ] HN L N)
    (a c : ℤ) (x : HN L N) : Continuous (integrand b T a c x) := by
  have hV : Continuous (fun p : HN L N × AngleTorus => (quantumRotation b p.2).symm p.1) := by
    apply continuous_prod_of_continuous_lipschitzWith _ 1
    · intro y; exact inverse_rotation_strong_continuous b y
    · intro θ; exact (quantumRotation b θ).symm.isometry.lipschitzWith
  exact (continuous_subtype_val.comp ((continuous_apply a).div' (continuous_apply c))).smul
    (hV.comp ((T.continuous.comp (rotation_strong_continuous b x)).prodMk continuous_id))

instance productHaar_probability : IsProbabilityMeasure productHaar := by
  unfold productHaar
  infer_instance

theorem integrand_integrable (b : BetheBasis L N) (T : HN L N →L[ℂ] HN L N)
    (a c : ℤ) (x : HN L N) : Integrable (integrand b T a c x) productHaar :=
  (integrand_continuous b T a c x).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integrand_bound (b : BetheBasis L N) (T : HN L N →L[ℂ] HN L N)
    (a c : ℤ) (x : HN L N) (θ : AngleTorus) :
    ‖integrand b T a c x θ‖ ≤ ‖T‖ * ‖x‖ := by
  simpa [integrand, character, norm_smul] using T.le_opNorm (quantumRotation b θ x)

/-- The vector-strong full Haar integral. -/
def componentVector (b : BetheBasis L N) (T : HN L N →L[ℂ] HN L N)
    (a c : ℤ) (x : HN L N) : HN L N := ∫ θ, integrand b T a c x θ ∂productHaar

/-- The same vector-strong integral, as a linear map. -/
def componentLinear (b : BetheBasis L N) (T : HN L N →L[ℂ] HN L N)
    (a c : ℤ) : HN L N →ₗ[ℂ] HN L N where
  toFun := componentVector b T a c
  map_add' x y := by
    have he : integrand b T a c (x + y) = integrand b T a c x + integrand b T a c y := by
      funext θ; simp [integrand, smul_add]
    unfold componentVector
    rw [he]
    exact integral_add (integrand_integrable b T a c x) (integrand_integrable b T a c y)
  map_smul' z x := by
    have he : integrand b T a c (z • x) = z • integrand b T a c x := by
      funext θ
      simp only [integrand, map_smul, Pi.smul_apply]
      exact smul_comm _ _ _
    unfold componentVector
    rw [he]
    exact integral_smul z (integrand b T a c x)

theorem componentVector_bound (b : BetheBasis L N) (T : HN L N →L[ℂ] HN L N)
    (a c : ℤ) (x : HN L N) : ‖componentVector b T a c x‖ ≤ ‖T‖ * ‖x‖ := by
  simpa [componentVector] using norm_integral_le_of_norm_le_const
    (μ := productHaar) (Filter.Eventually.of_forall (integrand_bound b T a c x))

/-- DEF-054: the bounded full-character component of the physical operator.
This is the vector-strong integral, rather than an integral in operator norm. -/
def component (b : BetheBasis L N) (T : HN L N →L[ℂ] HN L N)
    (a c : ℤ) : HN L N →L[ℂ] HN L N :=
  (componentLinear b T a c).mkContinuous ‖T‖ (componentVector_bound b T a c)

theorem component_apply (b : BetheBasis L N) (T : HN L N →L[ℂ] HN L N)
    (a c : ℤ) (x : HN L N) : component b T a c x =
      ∫ θ, character a c θ • (quantumRotation b θ).symm (T (quantumRotation b θ x)) ∂productHaar := rfl

end QuantumNLS.FullCharacterProjection

#print axioms QuantumNLS.FullCharacterProjection.lp_sq_eq
#print axioms QuantumNLS.FullCharacterProjection.lp_sq_summable
#print axioms QuantumNLS.FullCharacterProjection.continuousAt_lp_of_tail
#print axioms QuantumNLS.FullCharacterProjection.countPhase_continuous
#print axioms QuantumNLS.FullCharacterProjection.rotation_coeff
#print axioms QuantumNLS.FullCharacterProjection.rotation_strong_continuous
#print axioms QuantumNLS.FullCharacterProjection.inverse_rotation_strong_continuous
#print axioms QuantumNLS.FullCharacterProjection.character
#print axioms QuantumNLS.FullCharacterProjection.integrand
#print axioms QuantumNLS.FullCharacterProjection.integrand_continuous
#print axioms QuantumNLS.FullCharacterProjection.integrand_integrable
#print axioms QuantumNLS.FullCharacterProjection.integrand_bound
#print axioms QuantumNLS.FullCharacterProjection.componentVector
#print axioms QuantumNLS.FullCharacterProjection.componentLinear
#print axioms QuantumNLS.FullCharacterProjection.componentVector_bound
#print axioms QuantumNLS.FullCharacterProjection.component
#print axioms QuantumNLS.FullCharacterProjection.component_apply

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.FullCharacterProjection.lp_sq_eq,
    ``QuantumNLS.FullCharacterProjection.lp_sq_summable,
    ``QuantumNLS.FullCharacterProjection.continuousAt_lp_of_tail,
    ``QuantumNLS.FullCharacterProjection.countPhase_continuous,
    ``QuantumNLS.FullCharacterProjection.rotation_coeff,
    ``QuantumNLS.FullCharacterProjection.rotation_strong_continuous,
    ``QuantumNLS.FullCharacterProjection.inverse_rotation_strong_continuous,
    ``QuantumNLS.FullCharacterProjection.character,
    ``QuantumNLS.FullCharacterProjection.integrand,
    ``QuantumNLS.FullCharacterProjection.integrand_continuous,
    ``QuantumNLS.FullCharacterProjection.integrand_integrable,
    ``QuantumNLS.FullCharacterProjection.integrand_bound,
    ``QuantumNLS.FullCharacterProjection.componentVector,
    ``QuantumNLS.FullCharacterProjection.componentLinear,
    ``QuantumNLS.FullCharacterProjection.componentVector_bound,
    ``QuantumNLS.FullCharacterProjection.component,
    ``QuantumNLS.FullCharacterProjection.component_apply]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.FullCharacterProjection." then
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
            throwError "Result nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  let mut todo := #[``QuantumNLS.FullCharacterProjection.lp_sq_eq,
    ``QuantumNLS.FullCharacterProjection.lp_sq_summable,
    ``QuantumNLS.FullCharacterProjection.continuousAt_lp_of_tail,
    ``QuantumNLS.FullCharacterProjection.countPhase_continuous,
    ``QuantumNLS.FullCharacterProjection.rotation_coeff,
    ``QuantumNLS.FullCharacterProjection.rotation_strong_continuous,
    ``QuantumNLS.FullCharacterProjection.inverse_rotation_strong_continuous,
    ``QuantumNLS.FullCharacterProjection.character,
    ``QuantumNLS.FullCharacterProjection.integrand,
    ``QuantumNLS.FullCharacterProjection.integrand_continuous,
    ``QuantumNLS.FullCharacterProjection.integrand_integrable,
    ``QuantumNLS.FullCharacterProjection.integrand_bound,
    ``QuantumNLS.FullCharacterProjection.componentVector,
    ``QuantumNLS.FullCharacterProjection.componentLinear,
    ``QuantumNLS.FullCharacterProjection.componentVector_bound,
    ``QuantumNLS.FullCharacterProjection.component,
    ``QuantumNLS.FullCharacterProjection.component_apply]
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
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; {checked.size} generic constants independent of EXT-001. Concrete instantiations require its explicit Prop hypothesis only."
