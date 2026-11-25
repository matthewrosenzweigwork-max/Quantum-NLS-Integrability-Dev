import QuantumNLS.EnergyMarginalCompactness
import QuantumNLS.MarginalEnergy
import QuantumNLS.LinearTailKineticError

/-! Transfer the compact energy set to the actual physical tensor carrier.
The Fourier equivalence is an isometry for the literal trace norm. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Filter Topology Set
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.PhysicalMarginalCompactness
open TraceClass TraceNormTopology PhysicalEnergyTrace Energy EnergyRealization
open TensorCarrier PhysicalTensor EnergyPreparationDef PhysicalEnergy
variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

/-- Transport bounded operators with their actual extended trace metric. -/
def pullOp (e : X ≃ₗᵢ[ℂ] Y) (A : Op Y) : Op X := ⟨pull e A.val⟩

theorem pullOp_isometry (e : X ≃ₗᵢ[ℂ] Y) : Isometry (pullOp e) := by
  intro A B
  change traceNorm (pull e A.val - pull e B.val) = traceNorm (A.val - B.val)
  rw [← pull_sub, traceNorm_pull]

variable (L : ℝ) [Fact (0 < L)] (k : ℕ)

/-- The compact state set on the actual full physical marginal space. -/
def states (E : ℝ) : Set (Op (Xk L k)) :=
  {A | A.val.IsPositive ∧ posTrace A.val = 1 ∧ energyTrace A.val ≤ ENNReal.ofReal E}

theorem states_eq_image (E : ℝ) : states L k E =
    pullOp (eK L k) '' EnergyMarginalCompactness.states L k E := by
  ext A
  constructor
  · intro hA
    let B : Op (L2 (Mom k)) := pullOp (eK L k).symm A
    refine ⟨B, ?_, ?_⟩
    · refine ⟨isPositive_pull _ hA.1, ?_, ?_⟩
      · change posTrace (pull (eK L k).symm A.val) = 1
        rw [posTrace_pull _ hA.1]
        exact hA.2.1
      · exact hA.2.2
    · apply Op.ext
      exact pull_pull_symm (eK L k) A.val
  · rintro ⟨B, hB, rfl⟩
    refine ⟨isPositive_pull _ hB.1, ?_, ?_⟩
    · change posTrace (pull (eK L k) B.val) = 1
      rw [posTrace_pull _ hB.1]
      exact hB.2.1
    · change kinTrace L k (pull (eK L k).symm (pull (eK L k) B.val)) ≤ _
      rw [pull_symm_pull]
      exact hB.2.2

/-- Actual full physical tensor marginals form a compact set in trace norm. -/
theorem isCompact_states {E : ℝ} (hE : 0 ≤ E) : IsCompact (states L k E) := by
  rw [states_eq_image]
  exact (EnergyMarginalCompactness.isCompact_states L k hE).image (pullOp_isometry _).continuous

/-- Every normalized symmetric physical H1 state satisfying the literal
repulsive form bound has its k-marginal in this compact set, uniformly in N. -/
theorem marginal_mem {N : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ N) {κ E : ℝ}
    (hκ : 0 ≤ κ) {ψ : Xk L N} (hsec : ψ ∈ physSector L N) (hnorm : ‖ψ‖ = 1)
    (x : PhysH1 L N) (hx : x.val = physUnitary ψ)
    (henergy : hN κ N x ≤ (N : ℝ) * E) :
    (⟨reducedDensityN N k hk ψ⟩ : Op (Xk L k)) ∈ states L k (1 + (k : ℝ) * E) := by
  obtain ⟨_, hp, ht, _, _, _, _, he⟩ := MarginalEnergy.marginal_physical_inputs (L := L) hk1 hk hsec hnorm x hx
  refine ⟨hp, ht, (he κ hκ).trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hN : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hkn : 0 ≤ (k / N : ℝ) := div_nonneg (Nat.cast_nonneg k) hN.le
  have hh := mul_le_mul_of_nonneg_left henergy hkn
  have heq : (k / N : ℝ) * ((N : ℝ) * E) = k * E := by field_simp
  rw [heq] at hh
  linarith

/-- The constructed source error controls the actual physical marginal
of every normalized symmetric H1 state in the literal form-energy bound. -/
theorem marginal_quadratic_error {N n : ℕ} (hn : n + 1 ≤ N) {κ E : ℝ}
    (hκ : 0 ≤ κ) {ψ : Xk L N} (hsec : ψ ∈ physSector L N) (hnorm : ‖ψ‖ = 1)
    (x : PhysH1 L N) (hx : x.val = physUnitary ψ)
    (henergy : hN κ N x ≤ (N : ℝ) * E) (R : ℕ)
    (a : Finset ℤ) (t : ℤ → ℝ) (ht : ∀ m ∈ a, |t m| ≤ 1)
    (ha : ∀ m ∈ a, (R : ℤ) < |m|) :
    LinearTailKineticError.quadraticError (LinearTailKineticError.fullT L n a t)
      (reducedDensityN N (n + 1) hn ψ) ≤ LinearTailKineticError.sourceError L n E R := by
  have hm := marginal_mem L (n + 1) (by omega) hn hκ hsec hnorm x hx henergy
  exact LinearTailKineticError.quadraticError_le_error L n E R a t ht ha
    hm.1 hm.2.1 (by simpa only [Nat.cast_add, Nat.cast_one] using hm.2.2)

end QuantumNLS.PhysicalMarginalCompactness

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.PhysicalMarginalCompactness.pullOp
#print axioms QuantumNLS.PhysicalMarginalCompactness.pullOp_isometry
#print axioms QuantumNLS.PhysicalMarginalCompactness.states
#print axioms QuantumNLS.PhysicalMarginalCompactness.states_eq_image
#print axioms QuantumNLS.PhysicalMarginalCompactness.isCompact_states
#print axioms QuantumNLS.PhysicalMarginalCompactness.marginal_mem
#print axioms QuantumNLS.PhysicalMarginalCompactness.marginal_quadratic_error

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.PhysicalMarginalCompactness." then
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
