import QuantumNLS.FiniteTraceCompression
import QuantumNLS.KineticMarginalCompression

/-! Energy-bounded positive marginals have uniform finite nets in trace
norm, by literal Fourier compression and finite-dimensional matrix compactness. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Set Filter Topology
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.EnergyMarginalTraceNets
open Energy EnergyRealization ContactOperator TraceClass KineticMarginalCompression
variable (L : ℝ) [Fact (0 < L)] (k : ℕ)

/-- The Fourier multiplier projection equals the orthogonal basis projection. -/
theorem cubeProj_eq_basis (R : ℕ) :
    cubeProj k R = FiniteTraceCompression.proj
      (stdBasis : HilbertBasis (Mom k) ℂ (L2 (Mom k))) (cube k R) := by
  classical
  ext x w
  change (cubeProj k R x : Mom k → ℂ) w =
    (FiniteTraceCompression.proj (stdBasis : HilbertBasis (Mom k) ℂ (L2 (Mom k))) (cube k R) x : Mom k → ℂ) w
  rw [← inner_ev_left w (FiniteTraceCompression.proj
    (stdBasis : HilbertBasis (Mom k) ℂ (L2 (Mom k))) (cube k R) x)]
  simp only [FiniteTraceCompression.proj_apply, inner_sum, inner_smul_right]
  have ho := orthonormal_iff_ite.mp (stdBasis (ι := Mom k)).orthonormal
  have hcoeff : ∀ j : Mom k, ⟪stdBasis j, x⟫_ℂ = (x : Mom k → ℂ) j :=
    fun j => inner_ev_left j x
  simp [cubeProj, mulCLM_apply, ev, ho, hcoeff]
  split_ifs <;> simp

/-- Uniform trace norm finite-net form of kinetic compactness. Centers are
finite-rank matrices; the net is common to the entire positive energy set. -/
theorem finite_energy_trace_net {E ε : ℝ} (hE : 0 ≤ E) (hε : 0 < ε) :
    ∃ S : Finset (L2 (Mom k) →L[ℂ] L2 (Mom k)),
      ∀ ρ : L2 (Mom k) →L[ℂ] L2 (Mom k), ρ.IsPositive →
      kinTrace L k ρ ≤ ENNReal.ofReal E →
      ∃ C ∈ S, traceNorm (ρ - C) ≤ ENNReal.ofReal ε := by
  classical
  obtain ⟨R, hR⟩ := uniform_kinetic_compression L k hE (half_pos hε)
  let b : HilbertBasis (Mom k) ℂ (L2 (Mom k)) := stdBasis
  let F := cube k R
  let Q := FiniteTraceCompression.proj b F
  obtain ⟨S, hS⟩ := FiniteTraceCompression.finite_trace_net b F (M := E) (half_pos hε)
  refine ⟨S, fun ρ hρ henergy => ?_⟩
  have htr : traceNorm ρ ≤ ENNReal.ofReal E := by
    rw [traceNorm_of_isPositive hρ]
    apply (posTrace_le_formTrace (kinSqrt L k) (one_le_kinSqrt L k) hρ).trans
    simpa only [kinTrace_eq_formTrace] using henergy
  have hn : ‖ρ‖ ≤ E := by
    have hh := ENNReal.toReal_le_of_le_ofReal hE ((norm_le_traceNorm ρ).trans htr)
    simpa only [ENNReal.toReal_ofReal (norm_nonneg _)] using hh
  have hQ : ‖Q‖ ≤ 1 := FiniteTraceCompression.norm_proj_le b F
  have hnQ : ‖Q * ρ * Q‖ ≤ E := by
    calc
      _ ≤ ‖Q‖ * ‖ρ‖ * ‖Q‖ := (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
      _ ≤ 1 * E * 1 := by gcongr
      _ = E := by ring
  obtain ⟨C, hCS, hC⟩ := hS (Q * ρ * Q) (FiniteTraceCompression.compression_mem b F ρ) hnQ
  refine ⟨C, hCS, ?_⟩
  have hcomp : traceNorm (ρ - Q * ρ * Q) ≤ ENNReal.ofReal (ε / 2) := by
    have hh := hR R le_rfl ρ hρ henergy
    rwa [cubeProj_eq_basis] at hh
  calc
    _ = traceNorm ((ρ - Q * ρ * Q) + (Q * ρ * Q - C)) := by congr 1; abel
    _ ≤ traceNorm (ρ - Q * ρ * Q) + traceNorm (Q * ρ * Q - C) := traceNorm_add_le _ _
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hcomp hC
    _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; congr 1; ring

end QuantumNLS.EnergyMarginalTraceNets

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.EnergyMarginalTraceNets.cubeProj_eq_basis
#print axioms QuantumNLS.EnergyMarginalTraceNets.finite_energy_trace_net

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.EnergyMarginalTraceNets." then
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
