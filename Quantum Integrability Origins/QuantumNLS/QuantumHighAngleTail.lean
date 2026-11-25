import QuantumNLS.HighAngleEvolutionBridge

/-! R-F1423202, uniform quantum high-angle tail on the full product torus.
The finite bound is derived from the actual common Bethe diagonal. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Complex Filter Topology Set
open scoped BigOperators InnerProductSpace
namespace QuantumNLS.QuantumHighAngleTail
open TensorCarrier PhysicalTensor KernelDefinition LinearTailGenerator LinearTailPhysicalEvolution
open HaarSpectralTail HaarNonlinearTail HaarNonlinearAbstract HighAngleReconstruction
open HighAngleLinearEvolution HighAngleEvolutionBridge CountRotations HighAngleRotations

lemma marginal_triangle {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N k : ℕ) (hk : k ≤ N) (x y z : SymSector ℂ H N) :
    TraceClass.traceNorm (reducedDensityN N k hk x.val - reducedDensityN N k hk z.val) ≤
      TraceClass.traceNorm (reducedDensityN N k hk x.val - reducedDensityN N k hk y.val) +
      TraceClass.traceNorm (reducedDensityN N k hk y.val - reducedDensityN N k hk z.val) := by
  convert TraceClass.traceNorm_add_le
    (reducedDensityN N k hk x.val - reducedDensityN N k hk y.val)
    (reducedDensityN N k hk y.val - reducedDensityN N k hk z.val) using 1
  abel_nf

variable (L : ℝ) [Fact (0 < L)]

/-- The three uniform finite-support errors, including the pi scaling and
the factor two for the vector-to-marginal comparison. -/
theorem finite_tail {κ E : ℝ} (hκ : 0 < κ) (hE : 0 < E) {k : ℕ} (hk : 1 ≤ k) :
    ∃ NE : ℕ, ∃ R₀ C D : ℝ, 0 < NE ∧ 2 ≤ R₀ ∧ 0 ≤ C ∧ 0 ≤ D ∧
      ∀ (N : ℕ) (_hNN : NE ≤ N) (hkN : k ≤ N)
        (P : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N),
        (∀ m, P (bas L hκ (hk.trans hkN) m) = mask L κ N E m • bas L hκ (hk.trans hkN) m) →
        ∀ ψ : SymSector ℂ (L2T L) N, P ψ = ψ → ‖ψ‖ = 1 →
        ∀ R : ℕ, R₀ ≤ (R : ℝ) → ∀ θ : AngleTorus,
        (∀ n : ℤ, |n| ≤ (R : ℤ) → θ n = 1) → ∀ a : Finset ℤ,
          TraceClass.traceNorm (reducedDensityN N k hkN
            (quantumRotation (bas L hκ (hk.trans hkN)) (truncate a θ) ψ).val -
              reducedDensityN N k hkN ψ.val) ≤
            ENNReal.ofReal (2 * Real.pi * C / R + Real.pi * D / Real.sqrt R + epsilonPi L κ E k R) := by
  classical
  obtain ⟨NE, RE, C, hNE, hRE, hC, herr⟩ := HighAngleSpectralBridge.actual_combined_error L hκ hE
  obtain ⟨RN, D, hRN, hD, hnl⟩ := HighAngleNonlinearEvolution.nonlinear_evolution L hκ hE hk
  refine ⟨NE, max RE RN, C, D, hNE, hRE.trans (le_max_left _ _), hC, hD, ?_⟩
  intro N hNN hkN P hP ψ hPψ hn R hR θ hθ a
  have hN : 0 < N := hk.trans hkN
  have hRE : RE ≤ (R : ℝ) := (le_max_left _ _).trans hR
  have hRN' : RN ≤ (R : ℝ) := (le_max_right _ _).trans hR
  have hRpos : (0 : ℝ) < R := by linarith
  let a' := a.filter fun n => (R : ℤ) < |n|
  have ha' (n : ℤ) (hn : n ∈ a') : (R : ℤ) < |n| := (Finset.mem_filter.mp hn).2
  have har (n : ℤ) (hn : n ∈ a') : (R : ℝ) < |(n : ℝ)| := by
    exact_mod_cast ha' n hn
  have htr : truncate a θ = truncate a' θ := by
    funext n
    by_cases hn : n ∈ a
    · by_cases hr : (R : ℤ) < |n|
      · simp [truncate, a', hn, hr]
      · simp [truncate, a', hn, hr, hθ n (le_of_not_gt hr)]
    · simp [truncate, a', hn]
  rw [htr]
  let t := unitAngle θ
  obtain ⟨B, hB, hBsa, hPB, hb⟩ := hnl N hkN P hP R hRN' a' har t (unitAngle_le θ)
  let A := (N : ℂ) • genSum L κ N a' t
  let μ := fun m => (N : ℂ) * LinearTailCommute.genEigen L κ hκ N hN a' t m
  have hA (m : BetheLabels.MArr N) : A (bas L hκ hN m) = μ m • bas L hκ hN m := by
    simp only [A, μ, smul_apply, LinearTailCommute.genSum_meanField, smul_smul]
  have hAsa : IsSelfAdjoint A :=
    (show IsSelfAdjoint (N : ℂ) from by simp [isSelfAdjoint_iff]).smul
      (show IsSelfAdjoint (genSum L κ N a' t) from by
        simpa only [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint] using
          LinearTailSelfadjoint.genSum_selfadjoint L κ N a' t)
  have hAr := diagonal_real (bas L hκ hN) A hAsa μ hA
  have hAc (m : BetheLabels.MArr N) :
      A (bas L hκ hN m) = ((μ m).re : ℂ) • bas L hκ hN m := by
    exact (hA m).trans (congrArg (fun c : ℂ => c • bas L hκ hN m) (hAr m))
  have hBc (m : BetheLabels.MArr N) :
      B (bas L hκ hN m) = ((rEig L hκ hN E a' t m).re : ℂ) • bas L hκ hN m := by
    exact (hB m).trans (congrArg (fun c : ℂ => c • bas L hκ hN m)
      (diagonal_real (bas L hκ hN) B hBsa _ hB m))
  have hPA : Commute P A := IsDiagC.commute (diagC_P hκ hN hP) (diagC_of_apply hA)
  let v := evolution A Real.pi ψ
  let w := evolution B Real.pi v
  have hvP : P v = v := evolution_fixed hPA hPψ _
  have hvn : ‖v‖ = 1 := by
    dsimp only [v]
    rw [evolution_norm hAsa, hn]
  have hwn : ‖w‖ = 1 := by
    dsimp only [w]
    rw [evolution_norm hBsa, hvn]
  have hcmp : ‖quantumRotation (bas L hκ hN) (truncate a' θ) ψ - w‖ ≤ Real.pi * C / R := by
    have he := diagonal_evolution_comparison (bas L hκ hN)
      (quantumRotation (bas L hκ hN) (truncate a' θ)) A B
      (countEigen a' t) (fun m => (μ m).re) (fun m => (rEig L hκ hN E a' t m).re) Real.pi
      (fun m => by rw [quantumRotation_basis, countPhase_exp]; congr 2; push_cast; ring)
      hAc hBc (adm L κ N E) (div_nonneg hC hRpos.le)
      (fun m hm => by
        simpa only [μ, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
          using herr N hN hNN m hm R hRE a' har t (unitAngle_le θ)) ψ
      (by simpa only [hPψ] using supp_P hκ hN hP ψ)
    simpa only [hn, mul_one, abs_of_pos Real.pi_pos, mul_div_assoc, w, v] using he
  have hvec := MarginalPureState.traceNorm_reducedDensityN_sub_le N k hkN
    (quantumRotation (bas L hκ hN) (truncate a' θ) ψ).val w.val
  have hfirst : TraceClass.traceNorm (reducedDensityN N k hkN
      (quantumRotation (bas L hκ hN) (truncate a' θ) ψ).val - reducedDensityN N k hkN w.val) ≤
      ENNReal.ofReal (2 * Real.pi * C / R) := by
    have hu : ‖quantumRotation (bas L hκ hN) (truncate a' θ) ψ‖ = 1 := by
      rw [LinearIsometryEquiv.norm_map, hn]
    refine hvec.trans (ENNReal.ofReal_le_ofReal ?_)
    change ‖quantumRotation (bas L hκ hN) (truncate a' θ) ψ - w‖ *
      (‖quantumRotation (bas L hκ hN) (truncate a' θ) ψ‖ + ‖w‖) ≤ _
    rw [hu, hwn]
    have heq : 2 * Real.pi * C / (R : ℝ) = 2 * (Real.pi * C / R) := by ring
    rw [heq]
    nlinarith [hcmp]
  have hsecond := hb v hvP hvn Real.pi
  have hthird := linear_sector L hκ hE.le hN hkN P hP ψ hPψ hn R a' t
    (fun n _ => unitAngle_le θ n) ha' Real.pi
  have hn2 : 0 ≤ Real.pi * D / Real.sqrt R := by positivity
  have hn3 := epsilonPi_nonneg L hκ.le E k R
  have h12 := marginal_triangle N k hkN
    (quantumRotation (bas L hκ hN) (truncate a' θ) ψ) w ψ
  have h23 := marginal_triangle N k hkN w v ψ
  refine h12.trans ((add_le_add le_rfl h23).trans ?_)
  have hsecond' : TraceClass.traceNorm (reducedDensityN N k hkN w.val - reducedDensityN N k hkN v.val) ≤
      ENNReal.ofReal (Real.pi * D / Real.sqrt R) := by
    simpa only [w, abs_of_pos Real.pi_pos, div_mul_eq_mul_div, mul_comm D Real.pi] using hsecond
  have hthird' : TraceClass.traceNorm (reducedDensityN N k hkN v.val - reducedDensityN N k hkN ψ.val) ≤
      ENNReal.ofReal (epsilonPi L κ E k R) := by
    simpa only [v, A, abs_of_pos Real.pi_pos, epsilonPi, mul_comm Real.pi] using hthird
  exact (add_le_add hfirst (add_le_add hsecond' hthird')).trans (by
    rw [← ENNReal.ofReal_add hn2 hn3, ← ENNReal.ofReal_add (by positivity) (add_nonneg hn2 hn3)]
    apply le_of_eq
    congr 1
    ring)

/-- One named source theorem over the entire product of angle circles.
The energy projection is chosen independently of R, theta and the state. -/
theorem natural_tail {κ E : ℝ} (hκ : 0 < κ) (hE : 0 < E) {k : ℕ} (hk : 1 ≤ k) :
    ∃ NE : ℕ, ∃ η : ℕ → ℝ, 0 < NE ∧ (∀ R, 0 ≤ η R) ∧ Tendsto η atTop (𝓝 0) ∧
      ∀ (N : ℕ) (_hNN : NE ≤ N) (hkN : k ≤ N),
        ∃ P : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N,
          (∀ m, P (bas L hκ (hk.trans hkN) m) = mask L κ N E m • bas L hκ (hk.trans hkN) m) ∧
          ∀ ψ : SymSector ℂ (L2T L) N, P ψ = ψ → ‖ψ‖ = 1 →
          ∀ (R : ℕ) (θ : AngleTorus), (∀ n : ℤ, |n| ≤ (R : ℤ) → θ n = 1) →
            TraceClass.traceNorm (reducedDensityN N k hkN
              (quantumRotation (bas L hκ (hk.trans hkN)) θ ψ).val -
                reducedDensityN N k hkN ψ.val) ≤ ENNReal.ofReal (η R) := by
  classical
  obtain ⟨NE, R₀, C, D, hNE, hR₀, hC, hD, hfinite⟩ := finite_tail L hκ hE hk
  let η : ℕ → ℝ := fun R => if R₀ ≤ (R : ℝ) then
    2 * Real.pi * C / R + Real.pi * D / Real.sqrt R + epsilonPi L κ E k R else 4
  have hη (R : ℕ) : 0 ≤ η R := by
    have heps := epsilonPi_nonneg L hκ.le E k R
    dsimp [η]
    split_ifs <;> positivity
  have hlim : Tendsto η atTop (𝓝 0) := by
    have hnat : Tendsto (fun R : ℕ => (R : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hroot : Tendsto (fun R : ℕ => Real.sqrt (R : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp hnat
    have h1 : Tendsto (fun R : ℕ => 2 * Real.pi * C / (R : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hnat
    have h2 : Tendsto (fun R : ℕ => Real.pi * D / Real.sqrt (R : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hroot
    have h3 := epsilonPi_tendsto L hκ.le hE.le k
    have hsum := (h1.add h2).add h3
    simp only [add_zero] at hsum
    apply hsum.congr'
    filter_upwards [hnat.eventually_ge_atTop R₀] with R hR
    exact (ite_eq_left hR).symm
  refine ⟨NE, η, hNE, hη, hlim, ?_⟩
  intro N hNN hkN
  obtain ⟨P, hP⟩ := energyProjection_exists L hκ (hk.trans hkN) E
  refine ⟨P, hP, ?_⟩
  intro ψ hPψ hn R θ hθ
  by_cases hR : R₀ ≤ (R : ℝ)
  · change _ ≤ ENNReal.ofReal (if R₀ ≤ (R : ℝ) then _ else _)
    rw [ite_eq_left hR]
    have heps := epsilonPi_nonneg L hκ.le E k R
    apply finite_to_full (bas L hκ (hk.trans hkN)) θ ψ k hkN _ (by positivity)
    exact hfinite N hNN hkN P hP ψ hPψ hn R hR θ hθ
  · change _ ≤ ENNReal.ofReal (if R₀ ≤ (R : ℝ) then _ else _)
    rw [ite_eq_right hR]
    have h := MarginalPureState.traceNorm_reducedDensityN_sub_le N k hkN
      (quantumRotation (bas L hκ (hk.trans hkN)) θ ψ).val ψ.val
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    have hu : ‖quantumRotation (bas L hκ (hk.trans hkN)) θ ψ‖ = 1 := by
      rw [LinearIsometryEquiv.norm_map, hn]
    change ‖quantumRotation (bas L hκ (hk.trans hkN)) θ ψ - ψ‖ *
      (‖quantumRotation (bas L hκ (hk.trans hkN)) θ ψ‖ + ‖ψ‖) ≤ 4
    have hb := norm_sub_le (quantumRotation (bas L hκ (hk.trans hkN)) θ ψ) ψ
    rw [hu, hn] at hb ⊢
    nlinarith

/-- R-F1423202 with arbitrary real tail radius and the full product torus. -/
theorem «R-F1423202» {κ E : ℝ} (hκ : 0 < κ) (hE : 0 < E) {k : ℕ} (hk : 1 ≤ k) :
    ∃ NE : ℕ, ∃ η : ℝ → ℝ, 0 < NE ∧ (∀ R, 0 ≤ η R) ∧ Tendsto η atTop (𝓝 0) ∧
      ∀ (N : ℕ) (_hNN : NE ≤ N) (hkN : k ≤ N),
        ∃ P : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N,
          (∀ m, P (bas L hκ (hk.trans hkN) m) = mask L κ N E m • bas L hκ (hk.trans hkN) m) ∧
          ∀ ψ : SymSector ℂ (L2T L) N, P ψ = ψ → ‖ψ‖ = 1 →
          ∀ R : ℝ, 0 ≤ R → ∀ θ : AngleTorus,
            (∀ n : ℤ, |(n : ℝ)| ≤ R → θ n = 1) →
            TraceClass.traceNorm (reducedDensityN N k hkN
              (quantumRotation (bas L hκ (hk.trans hkN)) θ ψ).val -
                reducedDensityN N k hkN ψ.val) ≤ ENNReal.ofReal (η R) := by
  obtain ⟨NE, η, hNE, hη, hlim, hmain⟩ := natural_tail L hκ hE hk
  refine ⟨NE, fun R => η ⌊R⌋₊, hNE, fun R => hη _, hlim.comp tendsto_nat_floor_atTop, ?_⟩
  intro N hNN hkN
  obtain ⟨P, hP, hb⟩ := hmain N hNN hkN
  refine ⟨P, hP, fun ψ hPψ hn R hR θ hθ => hb ψ hPψ hn ⌊R⌋₊ θ ?_⟩
  intro n hn
  apply hθ n
  have hn' : |(n : ℝ)| ≤ (⌊R⌋₊ : ℝ) := by exact_mod_cast hn
  exact hn'.trans (Nat.floor_le hR)

end QuantumNLS.QuantumHighAngleTail

#print axioms QuantumNLS.QuantumHighAngleTail.marginal_triangle
#print axioms QuantumNLS.QuantumHighAngleTail.finite_tail
#print axioms QuantumNLS.QuantumHighAngleTail.natural_tail
#print axioms QuantumNLS.QuantumHighAngleTail.«R-F1423202»

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.QuantumHighAngleTail." then
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
