import QuantumNLS.ContactOperator
import QuantumNLS.EnergyDifferences
import QuantumNLS.PhysicalEnergyTrace
import QuantumNLS.TraceIdeal

/-! Uniform trace-norm finite-rank approximation of positive energy-bounded
marginals. All operators are the literal Fourier kinetic multipliers. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Filter Topology Set
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.KineticMarginalCompression
open Energy EnergyRealization EnergyDifferences ContactOperator TraceClass TraceIdeal
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Two-sided trace-ideal estimate for replacing a compact kinetic weight
by a finite-rank approximation, uniformly on a trace-norm ball. -/
theorem sandwich_error (W V T : H →L[ℂ] H) {δ E : ℝ}
    (hδ : 0 ≤ δ) (hE : 0 ≤ E) (hW : ‖W‖ ≤ 1) (hV : ‖V‖ ≤ 1)
    (hd : ‖W - V‖ ≤ δ) (hT : traceNorm T ≤ ENNReal.ofReal E) :
    traceNorm (W * T * W - V * T * V) ≤ ENNReal.ofReal (2 * δ * E) := by
  have he : W * T * W - V * T * V =
      (W - V) * T * W + V * T * (W - V) := by noncomm_ring
  rw [he]
  have h₁ := traceNorm_mul_mul_le (W - V) T W
  have h₂ := traceNorm_mul_mul_le V T (W - V)
  have hW' : ENNReal.ofReal ‖W‖ ≤ 1 := by simpa using ENNReal.ofReal_le_ofReal hW
  have hV' : ENNReal.ofReal ‖V‖ ≤ 1 := by simpa using ENNReal.ofReal_le_ofReal hV
  calc
    traceNorm ((W - V) * T * W + V * T * (W - V)) ≤
      traceNorm ((W - V) * T * W) + traceNorm (V * T * (W - V)) := traceNorm_add_le _ _
    _ ≤ ENNReal.ofReal δ * ENNReal.ofReal E * 1 +
        1 * ENNReal.ofReal E * ENNReal.ofReal δ := by
      apply add_le_add (h₁.trans _) (h₂.trans _) <;> gcongr
    _ = ENNReal.ofReal (2 * δ * E) := by
      simp only [mul_one, one_mul]
      rw [mul_comm (ENNReal.ofReal E), ← ENNReal.ofReal_mul hδ,
        ← ENNReal.ofReal_add (mul_nonneg hδ hE) (mul_nonneg hδ hE)]
      congr 1; ring

variable (L : ℝ) [Fact (0 < L)] (k : ℕ)

/-- The explicit compact-kinetic truncation error. -/
def tailBound (R : ℕ) : ℝ := L / (2 * Real.pi * ((R : ℝ) + 1))

theorem tailBound_nonneg (R : ℕ) : 0 ≤ tailBound L R := by
  have : 0 < L := Fact.out
  unfold tailBound; positivity

omit [Fact (0 < L)] in
theorem tailBound_tendsto : Tendsto (tailBound L) atTop (𝓝 0) := by
  have h : Tendsto (fun R : ℕ => (2 * Real.pi) * ((R : ℝ) + 1)) atTop atTop :=
    Tendsto.const_mul_atTop (by positivity)
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  change Tendsto (fun R : ℕ => L / (2 * Real.pi * ((R : ℝ) + 1))) atTop (𝓝 0)
  exact h.const_div_atTop L

/-- A literal Fourier cube projection, independent of the state. -/
def cubeProj (R : ℕ) : L2 (Mom k) →L[ℂ] L2 (Mom k) :=
  mulCLM (fun w => if w ∈ cube k R then 1 else 0) 1 zero_le_one (by intro w; split_ifs <;> norm_num)

omit [Fact (0 < L)] in
theorem cubeProj_mul_weight (R : ℕ) :
    cubeProj k R * AhalfInv L k = truncMul L k R := by
  ext x w
  simp only [mul_apply_eq_comp, cubeProj, mulCLM_apply, AhalfInv, invCLM_apply,
    truncMul]
  by_cases h : w ∈ cube k R <;> simp [h]

omit [Fact (0 < L)] in
theorem weight_mul_cubeProj (R : ℕ) :
    AhalfInv L k * cubeProj k R = truncMul L k R := by
  ext x w
  simp only [mul_apply_eq_comp, cubeProj, mulCLM_apply, AhalfInv, invCLM_apply,
    truncMul]
  by_cases h : w ∈ cube k R <;> simp [h]

/-- The actual compression Q_R ρ Q_R approximates every positive kinetic
energy-bounded state uniformly in trace norm. No compactness is a premise. -/
theorem kinetic_compression {ρ : L2 (Mom k) →L[ℂ] L2 (Mom k)} (hρ : ρ.IsPositive)
    {E : ℝ} (hE : 0 ≤ E) (henergy : kinTrace L k ρ ≤ ENNReal.ofReal E) (R : ℕ) :
    traceNorm (ρ - cubeProj k R * ρ * cubeProj k R) ≤
      ENNReal.ofReal (2 * tailBound L R * E) := by
  have hfin : kinTrace L k ρ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top henergy
  obtain ⟨⟨T, hT, -, hspec, htr⟩, -⟩ := kinetic_realization L k hρ hfin
  have htn : traceNorm T ≤ ENNReal.ofReal E := by rw [traceNorm_of_isPositive hT, htr]; exact henergy
  have hdiff : ‖AhalfInv L k - truncMul L k R‖ ≤ tailBound L R := by
    have he : AhalfInv L k - truncMul L k R = tailMul L k R := by
      rw [← truncMul_add_tailMul R]; abel
    rw [he]
    exact norm_mulCLM_le _ _ _ _
  have hh := sandwich_error (AhalfInv L k) (truncMul L k R) T
    (tailBound_nonneg L R) hE (norm_AhalfInv_le L k) (norm_mulCLM_le _ _ _ _) hdiff htn
  have he : cubeProj k R * ρ * cubeProj k R = truncMul L k R * T * truncMul L k R := by
    rw [hspec]
    calc
      _ = (cubeProj k R * AhalfInv L k) * T * (AhalfInv L k * cubeProj k R) := by noncomm_ring
      _ = _ := by rw [cubeProj_mul_weight, weight_mul_cubeProj]
  rw [he, hspec]
  exact hh

/-- Per-rank uniform trace-norm tightness from the compact kinetic
resolvent. The cube R is common to the entire energy-bounded set. -/
theorem uniform_kinetic_compression {E : ℝ} (hE : 0 ≤ E) {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ : ℕ, ∀ R ≥ R₀, ∀ ρ : L2 (Mom k) →L[ℂ] L2 (Mom k),
      ρ.IsPositive → kinTrace L k ρ ≤ ENNReal.ofReal E →
      traceNorm (ρ - cubeProj k R * ρ * cubeProj k R) ≤ ENNReal.ofReal ε := by
  have ht : Tendsto (fun R => 2 * tailBound L R * E) atTop (𝓝 0) := by
    simpa using ((tailBound_tendsto L).const_mul 2).mul_const E
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp ((tendsto_order.mp ht).2 ε hε)
  exact ⟨R₀, fun R hR ρ hρ henergy => (kinetic_compression L k hρ hE henergy R).trans
    (ENNReal.ofReal_le_ofReal (hR₀ R hR).le)⟩

end QuantumNLS.KineticMarginalCompression

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.KineticMarginalCompression.sandwich_error
#print axioms QuantumNLS.KineticMarginalCompression.tailBound
#print axioms QuantumNLS.KineticMarginalCompression.tailBound_nonneg
#print axioms QuantumNLS.KineticMarginalCompression.tailBound_tendsto
#print axioms QuantumNLS.KineticMarginalCompression.cubeProj
#print axioms QuantumNLS.KineticMarginalCompression.cubeProj_mul_weight
#print axioms QuantumNLS.KineticMarginalCompression.weight_mul_cubeProj
#print axioms QuantumNLS.KineticMarginalCompression.kinetic_compression
#print axioms QuantumNLS.KineticMarginalCompression.uniform_kinetic_compression

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.KineticMarginalCompression." then
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
