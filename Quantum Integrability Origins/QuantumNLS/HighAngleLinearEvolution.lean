import QuantumNLS.HighAngleNonlinearEvolution
import QuantumNLS.Prop020Vector

/-! The linear tail estimate for arbitrary signed time, with the literal
sector exponential and the pi-scaled modulus. All cutoffs are physical. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Filter Topology Set
open scoped InnerProductSpace
namespace QuantumNLS.HighAngleLinearEvolution
open TensorCarrier PhysicalTensor KernelDefinition LinearTailGenerator LinearTailHamiltonian
open LinearTailPhysicalEvolution PhysicalCutoffEvolutionBounds SourceGeneratorBound SourceMarginalEvolution

section Generic
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma intertwine_exp (e : H →L[ℂ] K) (A : H →L[ℂ] H) (B : K →L[ℂ] K)
    (h : ∀ v, e (A v) = B (e v)) (v : H) :
    e (NormedSpace.exp A v) = NormedSpace.exp B (e v) := by
  have hp (n : ℕ) : e ((A ^ n) v) = (B ^ n) (e v) := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [pow_succ', mul_apply_eq_comp, h, ih]
  rw [NormedSpace.exp_eq_tsum ℂ, NormedSpace.exp_eq_tsum ℂ]
  have h1 := (ContinuousLinearMap.apply ℂ H v).map_tsum (NormedSpace.expSeries_summable' (𝕂 := ℂ) A)
  have h2 := (ContinuousLinearMap.apply ℂ K (e v)).map_tsum (NormedSpace.expSeries_summable' (𝕂 := ℂ) B)
  simp only [ContinuousLinearMap.apply_apply] at h1 h2
  change e ((∑' n : ℕ, (n.factorial : ℂ)⁻¹ • A ^ n) v) =
    (∑' n : ℕ, (n.factorial : ℂ)⁻¹ • B ^ n) (e v)
  have h3 := e.map_tsum ((ContinuousLinearMap.apply ℂ H v).summable
    (NormedSpace.expSeries_summable' (𝕂 := ℂ) A))
  simp only [ContinuousLinearMap.apply_apply] at h3
  rw [h1, h2, h3]
  apply tsum_congr
  intro n
  simp only [smul_apply, map_smul, hp]

lemma evolution_eigen (A : H →L[ℂ] H) {v : H} {μ : ℂ}
    (h : A v = μ • v) (s : ℝ) :
    evolution A s v = Complex.exp (-(s : ℂ) * Complex.I * μ) • v := by
  apply Prop020Diag.exp_eigen
  simp only [smul_apply, h, smul_smul]
  congr 1
  ring
end Generic

variable (L : ℝ) [Fact (0 < L)]

lemma sectorOrbit_eq (κ : ℝ) (N : ℕ) (a : Finset ℤ) (t : ℤ → ℝ) (s : ℝ)
    (ψ : ContactOperator.SymL2 L N) :
    sectorOrbit L κ N a t s ψ = evolution ((N : ℂ) • genSum L κ N a t) s
      ((BethePhysicalTransfer.symmetricPosition L N).symm ψ) := by
  unfold sectorOrbit physicalEvolution evolution
  let e := (BethePhysicalTransfer.symmetricPosition L N).symm.toContinuousLinearEquiv.toContinuousLinearMap
  apply intertwine_exp e
    ((s : ℂ) • ((-Complex.I) • ((N : ℂ) • symGen L κ N a t)))
    ((s : ℂ) • ((-Complex.I) • ((N : ℂ) • genSum L κ N a t)))
  intro v
  simp only [smul_apply, map_smul]
  congr 2
  congr 1
  have h := symGen_sp L κ N a t ((BethePhysicalTransfer.symmetricPosition L N).symm v)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact (congrArg (BethePhysicalTransfer.symmetricPosition L N).symm h).trans
    (LinearIsometryEquiv.symm_apply_apply _ _)

/-- The same differentiated commutator as the accepted linear theorem,
integrated on [-|s|,|s|], rather than restricted to unit time. -/
theorem linear_all_time (κ : ℝ) (hκ : 0 < κ) (N k : ℕ) (hN : 1 ≤ N) (hk : k ≤ N)
    (E : ℝ) (hE : 0 ≤ E)
    (P : ContactOperator.SymL2 L N →L[ℂ] ContactOperator.SymL2 L N)
    (hP : IsEnergyCutoff L κ N hκ hN E P)
    (ψ : ContactOperator.SymL2 L N) (hψ : P ψ = ψ) (hnorm : ‖ψ‖ = 1)
    (R : ℕ) (a : Finset ℤ) (t : ℤ → ℝ)
    (ht : ∀ m ∈ a, |t m| ≤ 1) (ha : ∀ m ∈ a, (R : ℤ) < |m|) (s : ℝ) :
    TraceClass.traceNorm (reducedDensityN N k hk (sectorOrbit L κ N a t s ψ).val -
      reducedDensityN N k hk ((BethePhysicalTransfer.symmetricPosition L N).symm ψ).val) ≤
        ENNReal.ofReal (epsilon L κ E k R * |s|) := by
  apply marginal_duality N k hk
  intro J hJ
  obtain ⟨Q, hQ, herror⟩ := PhysicalPlacementError.cutoff_placement_error L κ hκ N hN E hE a t
  have hPQ := cutoff_unique L κ hκ N hN E hP hQ
  subst Q
  let F := fun q => ⟪sectorOrbit L κ N a t q ψ,
    genericU_N_r N k hk J (sectorOrbit L κ N a t q ψ)⟫_ℂ
  have hd (q : ℝ) : ‖deriv F q‖ ≤ epsilon L κ E k R := by
    rw [(expectation_derivative L κ N k hk a t J ψ q).deriv, norm_mul, Complex.norm_I, one_mul]
    exact generator_bound L κ hκ N k hN hk E hE R a t J hJ
      (sectorOrbit L κ N a t q ψ) (by rw [sectorOrbit_norm, hnorm])
      (fun n hn S => herror ψ hψ hnorm q n hn R a t ht ha S)
  have hi := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun q (_ : q ∈ Icc (-|s|) |s|) => (expectation_derivative L κ N k hk a t J ψ q).differentiableAt)
    (fun q (_ : q ∈ Icc (-|s|) |s|) => hd q) (convex_Icc (-|s|) |s|)
    (show (0 : ℝ) ∈ Icc (-|s|) |s| from ⟨neg_nonpos.mpr (abs_nonneg _), abs_nonneg _⟩)
    (show s ∈ Icc (-|s|) |s| from ⟨neg_abs_le _, le_abs_self _⟩)
  simpa only [F, sectorOrbit_zero, sub_zero, Real.norm_eq_abs] using hi

/-- pi times the accepted linear modulus, independent of N and angles. -/
def epsilonPi (κ E : ℝ) (k R : ℕ) : ℝ := Real.pi * epsilon L κ E k R

lemma epsilonPi_nonneg {κ : ℝ} (hκ : 0 ≤ κ) (E : ℝ) (k R : ℕ) :
    0 ≤ epsilonPi L κ E k R := mul_nonneg Real.pi_pos.le (epsilon_nonneg L hκ E k R)

lemma epsilonPi_tendsto {κ E : ℝ} (hκ : 0 ≤ κ) (hE : 0 ≤ E) (k : ℕ) :
    Tendsto (epsilonPi L κ E k) atTop (𝓝 0) := by
  change Tendsto (fun R => Real.pi * epsilon L κ E k R) atTop (𝓝 0)
  simpa only [mul_zero] using (epsilon_tendsto L hκ hE k).const_mul Real.pi

end QuantumNLS.HighAngleLinearEvolution

namespace QuantumNLS.HighAngleLinearEvolution
open TensorCarrier PhysicalTensor KernelDefinition LinearTailGenerator LinearTailPhysicalEvolution
open HaarSpectralTail HaarNonlinearAbstract
variable (L : ℝ) [Fact (0 < L)]

/-- Transport the actual source estimate to any bounded projection with the
energy-mask diagonal. The projection is fixed before angles and time. -/
theorem linear_sector {κ E : ℝ} (hκ : 0 < κ) (hE : 0 ≤ E)
    {N k : ℕ} (hN : 0 < N) (hk : k ≤ N)
    (P : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N)
    (hP : ∀ m, P (bas L hκ hN m) = mask L κ N E m • bas L hκ hN m)
    (ψ : SymSector ℂ (L2T L) N) (hψ : P ψ = ψ) (hnorm : ‖ψ‖ = 1)
    (R : ℕ) (a : Finset ℤ) (t : ℤ → ℝ)
    (ht : ∀ m ∈ a, |t m| ≤ 1) (ha : ∀ m ∈ a, (R : ℤ) < |m|) (s : ℝ) :
    TraceClass.traceNorm (reducedDensityN N k hk
      (evolution ((N : ℂ) • genSum L κ N a t) s ψ).val -
      reducedDensityN N k hk ψ.val) ≤ ENNReal.ofReal (SourceGeneratorBound.epsilon L κ E k R * |s|) := by
  obtain ⟨P₀, hP₀, -, -, hQ⟩ := energyProjection_phys L hκ hN E a t
  let e := BethePhysicalTransfer.symmetricPosition L N
  let Q := e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (P₀.comp e.toContinuousLinearEquiv.toContinuousLinearMap)
  have hQP : Q = P := by
    apply TransferNormality.ext_of_hilbertBasis (bas L hκ hN)
    intro m
    exact (hQ m).trans (hP m).symm
  have hfix : P₀ (e ψ) = e ψ := by
    apply e.symm.injective
    rw [e.symm_apply_apply]
    change Q ψ = ψ
    rw [hQP, hψ]
  have h := linear_all_time L κ hκ N k hN hk E hE P₀ hP₀ (e ψ) hfix
    (by rw [LinearIsometryEquiv.norm_map, hnorm]) R a t ht ha s
  simpa only [sectorOrbit_eq, e, LinearIsometryEquiv.symm_apply_apply] using h
end QuantumNLS.HighAngleLinearEvolution

#print axioms QuantumNLS.HighAngleLinearEvolution.intertwine_exp
#print axioms QuantumNLS.HighAngleLinearEvolution.evolution_eigen
#print axioms QuantumNLS.HighAngleLinearEvolution.sectorOrbit_eq
#print axioms QuantumNLS.HighAngleLinearEvolution.linear_all_time
#print axioms QuantumNLS.HighAngleLinearEvolution.epsilonPi
#print axioms QuantumNLS.HighAngleLinearEvolution.epsilonPi_nonneg
#print axioms QuantumNLS.HighAngleLinearEvolution.epsilonPi_tendsto
#print axioms QuantumNLS.HighAngleLinearEvolution.linear_sector

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.HighAngleLinearEvolution." then
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
