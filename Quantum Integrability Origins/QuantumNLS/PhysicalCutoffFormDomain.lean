import QuantumNLS.LinearTailPhysicalEvolution
import QuantumNLS.ContactFormTheorem

/-! Cutoff form-domain membership and energy from the actual contact resolvent.
No form-domain or energy conclusion is supplied as a hypothesis. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set Filter Topology
open scoped InnerProductSpace
namespace QuantumNLS.PhysicalCutoffFormDomain
open ContactOperator ContactFormTheorem EnergyProjection
variable (L : ℝ) [Fact (0 < L)]

theorem cutoff_form_bound (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 1 ≤ N)
    (E : ℝ) (hE : 0 ≤ E)
    (P : SymL2 L N →L[ℂ] SymL2 L N)
    (hP : ∀ n : BetheFreeFamily.Label N,
      P (BetheConditionalBasis.normalizedWave L N ⟨κ / (N : ℝ),
          (div_pos hκ (by exact_mod_cast (show 0 < N by omega))).le⟩ n) =
        ((if energyEig L κ N n ≤ (N : ℝ) * E then (1 : ℝ) else 0 : ℝ) : ℂ) •
          BetheConditionalBasis.normalizedWave L N ⟨κ / (N : ℝ),
            (div_pos hκ (by exact_mod_cast (show 0 < N by omega))).le⟩ n)
    (ψ : SymL2 L N) (hψ : P ψ = ψ) :
    ∃ v : VSym L N, valSym v = ψ ∧
      (ContactForm.q (κ / (N : ℝ)) v.1 v.1).re ≤ (N : ℝ) * E * ‖ψ‖ ^ 2 := by
  classical
  have hc : 0 < κ / (N : ℝ) := div_pos hκ (by exact_mod_cast (show 0 < N by omega))
  obtain ⟨-, -, -, -, -, hortho, hdense, heig⟩ :=
    UnconditionalBetheBasis.basis L N hN (κ / (N : ℝ)) hc
  let B := HilbertBasis.mk hortho hdense.ge
  have hB : ∀ n, B n = BetheConditionalBasis.normalizedWave L N ⟨κ / (N : ℝ), hc.le⟩ n :=
    fun n => congrFun (HilbertBasis.coe_mk hortho hdense.ge) n
  have hmem : ∀ n, B n ∈ (Hop (L := L) (N := N) (κ / (N : ℝ)) hc.le).domain := by
    intro n
    rw [hB n]
    exact (heig n).choose
  have hval : ∀ n, Hop (L := L) (N := N) (κ / (N : ℝ)) hc.le ⟨B n, hmem n⟩ =
      (energyEig L κ N n : ℂ) • B n := by
    intro n
    have hv : Hop (L := L) (N := N) (κ / (N : ℝ)) hc.le
        ⟨BetheConditionalBasis.normalizedWave L N ⟨κ / (N : ℝ), hc.le⟩ n, (heig n).choose⟩ =
        (energyEig L κ N n : ℂ) • BetheConditionalBasis.normalizedWave L N ⟨κ / (N : ℝ), hc.le⟩ n :=
      (heig n).choose_spec
    have key : ∀ (x : SymL2 L N) (hx : x ∈ (Hop (L := L) (N := N) (κ / (N : ℝ)) hc.le).domain),
        x = BetheConditionalBasis.normalizedWave L N ⟨κ / (N : ℝ), hc.le⟩ n →
        Hop (κ / (N : ℝ)) hc.le ⟨x, hx⟩ = (energyEig L κ N n : ℂ) • x := by
      rintro x hx rfl
      exact hv
    exact key (B n) (hmem n) (hB n)
  let lam : BetheFreeFamily.Label N → ℝ := fun n =>
    if energyEig L κ N n ≤ (N : ℝ) * E then energyEig L κ N n + 1 else 0
  have hC : 0 ≤ (N : ℝ) * E + 1 := by positivity
  have hlam : ∀ n, ‖(lam n : ℂ)‖ ≤ (N : ℝ) * E + 1 := by
    intro n
    dsimp [lam]
    split_ifs with h
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [energyEig_nonneg L κ N n])]
      linarith
    · simpa using hC
  obtain ⟨Q, hcoef, hnorm⟩ := HilbertDiagOp.diag_exists B (fun n => (lam n : ℂ)) ((N : ℝ) * E + 1) hlam hC
  have hQ : ∀ n, Q (B n) = (lam n : ℂ) • B n := by
    intro n
    apply B.repr.injective
    ext m
    rw [map_smul]
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, HilbertBasis.repr_apply_apply, hcoef]
    by_cases hmn : m = n
    · subst m; rfl
    · rw [B.orthonormal.inner_eq_zero hmn]
      simp
  have hRQ : Rop (κ / (N : ℝ)) hc.le * Q = P := by
    apply TransferNormality.ext_of_hilbertBasis B
    intro n
    rw [mul_apply_eq_comp, hQ]
    have hp : P (B n) =
        ((if energyEig L κ N n ≤ (N : ℝ) * E then (1 : ℝ) else 0 : ℝ) : ℂ) • B n := by
      simpa only [hB] using hP n
    rw [hp]
    dsimp [lam]
    split_ifs with h
    · have hh := Rop_Hop_add hc.le ⟨B n, hmem n⟩
      rw [hval] at hh
      simpa only [add_smul, Complex.ofReal_add, Complex.ofReal_one, one_smul] using hh
    · simp
  have hRψ : Rop (κ / (N : ℝ)) hc.le (Q ψ) = ψ :=
    (congrArg (fun A : SymL2 L N →L[ℂ] SymL2 L N => A ψ) hRQ).trans hψ
  have hd : ψ ∈ (Hop (L := L) (N := N) (κ / (N : ℝ)) hc.le).domain := by
    rw [← hRψ]
    exact (Hop_Rop hc.le (Q ψ)).choose
  have hH : Hop (L := L) (N := N) (κ / (N : ℝ)) hc.le ⟨ψ, hd⟩ = Q ψ - ψ := by
    simpa [hRψ] using Hop_apply_of_Rop hc.le ⟨ψ, hd⟩ (Q ψ) hRψ
  obtain ⟨v, hv, hq⟩ := (Hop_isAssociated hc.le ψ
    (Hop (L := L) (N := N) (κ / (N : ℝ)) hc.le ⟨ψ, hd⟩)).mp ⟨hd, rfl⟩
  refine ⟨v, hv, ?_⟩
  rw [hq v, hv, hH, inner_sub_right, Complex.sub_re]
  have hself : (⟪ψ, ψ⟫_ℂ).re = ‖ψ‖ ^ 2 :=
    (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) ψ).symm
  rw [hself]
  have hi := (Complex.re_le_norm ⟪ψ, Q ψ⟫_ℂ).trans (norm_inner_le_norm ψ (Q ψ))
  have hb := Q.le_opNorm ψ
  have hbb := mul_le_mul_of_nonneg_right hnorm (norm_nonneg ψ)
  have hbbb := mul_le_mul_of_nonneg_left (hb.trans hbb) (norm_nonneg ψ)
  nlinarith

end QuantumNLS.PhysicalCutoffFormDomain

#print axioms QuantumNLS.PhysicalCutoffFormDomain.cutoff_form_bound

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.PhysicalCutoffFormDomain." then
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
