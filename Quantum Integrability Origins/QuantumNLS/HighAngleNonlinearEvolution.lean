import QuantumNLS.HaarNonlinearTail
import QuantumNLS.SourceMarginalEvolution

/-! R-F1423202: integration of the accepted nonlinear commutator estimate
for the literal selfadjoint remainder, preserving the actual energy cutoff.
No derivative, invariance, or marginal estimate is supplied as a premise. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Filter Topology Set
open scoped BigOperators InnerProductSpace ComplexConjugate
namespace QuantumNLS.HighAngleNonlinearEvolution
open HaarSpectralTail HaarNonlinearTail HaarNonlinearAbstract
open TensorCarrier PhysicalTensor KernelDefinition LinearTailPhysicalEvolution

section Generic
variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A bounded real spectral multiplier is selfadjoint on the entire Hilbert space. -/
lemma real_diagonal_selfadjoint (b : HilbertBasis ι ℂ H) (A : H →L[ℂ] H) (μ : ι → ℝ)
    (hA : IsDiagC b A (fun i => (μ i : ℂ))) : IsSelfAdjoint A := by
  have hadj := hA.adjoint
  change ContinuousLinearMap.adjoint A = A
  apply ContinuousLinearMap.ext
  intro v
  apply ext_coeff (b := b)
  intro i
  simp only [hadj, hA, Complex.conj_ofReal]

/-- The actual exponential commutator derivative, integrated for arbitrary
signed time. The bound is used on the evolving vector, proved to stay in P. -/
lemma integrate_commutator (A P J : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hPA : Commute P A) (c : ℝ) (_hc : 0 ≤ c)
    (hb : ∀ v : H, P v = v → ‖v‖ = 1 → ‖⟪v, (A * J - J * A) v⟫_ℂ‖ ≤ c)
    (ψ : H) (hPψ : P ψ = ψ) (hn : ‖ψ‖ = 1) (s : ℝ) :
    ‖⟪evolution A s ψ, J (evolution A s ψ)⟫_ℂ - ⟪ψ, J ψ⟫_ℂ‖ ≤ c * |s| := by
  let F := fun q : ℝ => ⟪evolution A q ψ, J (evolution A q ψ)⟫_ℂ
  have hd (q : ℝ) : ‖deriv F q‖ ≤ c := by
    rw [(hasDerivAt_expectation_commutator hA J ψ q).deriv, norm_mul,
      Complex.norm_I, one_mul]
    exact hb _ (evolution_fixed hPA hPψ q) (by rw [evolution_norm hA, hn])
  have hi := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun q (_ : q ∈ Icc (-|s|) |s|) =>
      (hasDerivAt_expectation_commutator hA J ψ q).differentiableAt)
    (fun q (_ : q ∈ Icc (-|s|) |s|) => hd q) (convex_Icc (-|s|) |s|)
    (show (0 : ℝ) ∈ Icc (-|s|) |s| from ⟨neg_nonpos.mpr (abs_nonneg _), abs_nonneg _⟩)
    (show s ∈ Icc (-|s|) |s| from ⟨neg_abs_le _, le_abs_self _⟩)
  simpa only [F, evolution_zero, one_ap, sub_zero, Real.norm_eq_abs] using hi
end Generic

variable (L : ℝ) [Fact (0 < L)]

/-- R-9C3CC17D integrated along its actual nonlinear remainder. The resulting
bound is uniform in N, the finite label support, the unit cutoff state, and
time. The diagonal existence clause is retained for the source assembly. -/
theorem nonlinear_evolution {κ E : ℝ} (hκ : 0 < κ) (hE : 0 < E) {k : ℕ} (hk : 1 ≤ k) :
    ∃ R₀ C : ℝ, 2 ≤ R₀ ∧ 0 ≤ C ∧
      ∀ (N : ℕ) (hkN : k ≤ N)
        (P : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N),
        (∀ m, P (bas L hκ (hk.trans hkN) m) =
          mask L κ N E m • bas L hκ (hk.trans hkN) m) →
        ∀ R : ℝ, R₀ ≤ R → ∀ a : Finset ℤ, (∀ n ∈ a, R < |(n : ℝ)|) →
          ∀ t : ℤ → ℝ, (∀ n, |t n| ≤ 1) →
          ∃ B : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N,
            (∀ m, B (bas L hκ (hk.trans hkN) m) =
              rEig L hκ (hk.trans hkN) E a t m • bas L hκ (hk.trans hkN) m) ∧
            IsSelfAdjoint B ∧ Commute P B ∧
            ∀ ψ : SymSector ℂ (L2T L) N, P ψ = ψ → ‖ψ‖ = 1 → ∀ s : ℝ,
              TraceClass.traceNorm (reducedDensityN N k hkN (evolution B s ψ).val -
                reducedDensityN N k hkN ψ.val) ≤ ENNReal.ofReal (C / Real.sqrt R * |s|) := by
  obtain ⟨-, R₀, C, hR₀, hC, hmain⟩ := haar_nonlinear_tail L hκ hE hk
  refine ⟨R₀, C, hR₀, hC, ?_⟩
  intro N hkN P hP R hR a ha t ht
  obtain ⟨-, hrest⟩ := hmain N hkN P hP
  obtain ⟨⟨B, hB⟩, hb⟩ := hrest R hR a ha t ht
  have hBd : IsDiagC (bas L hκ (hk.trans hkN)) B (rEig L hκ (hk.trans hkN) E a t) :=
    diagC_of_apply hB
  have hreal (m : BetheLabels.MArr N) :
      starRingEnd ℂ (rEig L hκ (hk.trans hkN) E a t m) = rEig L hκ (hk.trans hkN) E a t m := by
    unfold rEig
    split_ifs <;> simp only [Complex.conj_ofReal, map_zero]
  have hBsa : IsSelfAdjoint B := by
    change ContinuousLinearMap.adjoint B = B
    apply ContinuousLinearMap.ext
    intro v
    apply ext_coeff (b := bas L hκ (hk.trans hkN))
    intro m
    simp only [hBd.adjoint, hBd, hreal]
  have hPB : Commute P B := IsDiagC.commute (diagC_P hκ (hk.trans hkN) hP) hBd
  refine ⟨B, hB, hBsa, hPB, ?_⟩
  intro ψ hPψ hn s
  apply SourceMarginalEvolution.marginal_duality N k hkN (evolution B s ψ) ψ
  intro J hJ
  have hc : 0 ≤ C / Real.sqrt R := div_nonneg hC (Real.sqrt_nonneg _)
  have hi := integrate_commutator B P (genericU_N_r N k hkN J) hBsa hPB
    (C / Real.sqrt R) hc (fun v hv hvn => ?_) ψ hPψ hn s
  · exact hi
  · have h := (hb B hB J v hv hvn).1
    exact h.trans (by
      calc
        C * ‖J‖ / Real.sqrt R ≤ C * 1 / Real.sqrt R :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hJ hC) (Real.sqrt_nonneg _)
        _ = C / Real.sqrt R := by rw [mul_one])

end QuantumNLS.HighAngleNonlinearEvolution

-- Author audits: every own declaration and its generated/transitive constants.
#print axioms QuantumNLS.HighAngleNonlinearEvolution.real_diagonal_selfadjoint
#print axioms QuantumNLS.HighAngleNonlinearEvolution.integrate_commutator
#print axioms QuantumNLS.HighAngleNonlinearEvolution.nonlinear_evolution

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.HighAngleNonlinearEvolution." then
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
