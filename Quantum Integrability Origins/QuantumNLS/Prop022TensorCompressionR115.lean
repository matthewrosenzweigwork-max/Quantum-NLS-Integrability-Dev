import QuantumNLS.Ext005PhysicalSymmetryR114

/-! Literal tensor contractions for the factorial Hamiltonian's two quadratic
coefficients. The derivative identification and evolution are separate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap
namespace QuantumNLS.Prop022TensorCompressionR115
open TensorCarrier PhysicalTensor IntrinsicContact BetheCoefficientTransform
variable {L : ℝ} [Fact (0 < L)]

/-- Insert k free symmetric slots after r copies of the physical profile. -/
def insertion (r k : ℕ) (u : L2T L) : HN L k →L[ℂ] HN L (r + k) :=
  (physSector L (r + k)).orthogonalProjectionOnto ∘L
    (splitIsometry (𝕜 := ℂ) (E := L2T L) r k).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    htmulR (htpow r u) ∘L (physSector L k).subtypeL

lemma insertion_bound (r k : ℕ) (u : L2T L) (x : HN L k) :
    ‖insertion r k u x‖ ≤ ‖u‖ ^ r * ‖x‖ := by
  change ‖(physSector L (r+k)).orthogonalProjectionOnto
    ((splitIsometry (𝕜 := ℂ) (E := L2T L) r k).symm
      (htmul (htpow r u) (x : HilbertTensorPower ℂ (L2T L) k)))‖ ≤ _
  calc
    _ ≤ ‖(splitIsometry (𝕜 := ℂ) (E := L2T L) r k).symm
      (htmul (htpow r u) (x : HilbertTensorPower ℂ (L2T L) k))‖ :=
      Submodule.norm_orthogonalProjectionOnto_apply_le _ _
    _ = _ := by rw [LinearIsometryEquiv.norm_map, norm_htmul, norm_htpow]; rfl

lemma insertion_norm (r k : ℕ) (u : L2T L) : ‖insertion r k u‖ ≤ ‖u‖ ^ r :=
  opNorm_le_bound _ (by positivity) (insertion_bound r k u)

lemma insertion_unit (r k : ℕ) (u : L2T L) (hu : ‖u‖ = 1) :
    ‖insertion r k u‖ ≤ 1 := by simpa [hu] using insertion_norm r k u

def power (m : ℕ) (u : L2T L) : HN L m := ⟨htpow m u, htpow_mem_symSector m u⟩

lemma power_norm (m : ℕ) (u : L2T L) : ‖power m u‖ = ‖u‖ ^ m := norm_htpow m u

/-- m^2 mixed-derivative contractions, indexed by m=r+1. -/
def mixedTerm (B : ∀ m, HN L m →L[ℂ] HN L m) (u : L2T L) (r : ℕ) :
    HN L 1 →L[ℂ] HN L 1 :=
  (((r + 1 : ℕ) : ℂ) ^ 2) • ((insertion r 1 u).adjoint ∘L B (r + 1) ∘L insertion r 1 u)

/-- m(m-1) output contractions, indexed by m=r+2. -/
def pairTerm (B : ∀ m, HN L m →L[ℂ] HN L m) (u : L2T L) (r : ℕ) : HN L 2 :=
  (((r + 2 : ℕ) : ℂ) * ((r + 1 : ℕ) : ℂ)) •
    (insertion r 2 u).adjoint (B (r + 2) (power (r + 2) u))

lemma mixedTerm_norm (B : ∀ m, HN L m →L[ℂ] HN L m) (u : L2T L)
    (hu : ‖u‖ = 1) (r : ℕ) :
    ‖mixedTerm B u r‖ ≤ ((r + 1 : ℕ) : ℝ) ^ 2 * ‖B (r + 1)‖ := by
  have hi := insertion_unit r 1 u hu
  have hc : ‖(insertion r 1 u).adjoint ∘L B (r + 1) ∘L insertion r 1 u‖ ≤ ‖B (r + 1)‖ := by
    calc
      _ ≤ ‖(insertion r 1 u).adjoint‖ * (‖B (r+1)‖ * ‖insertion r 1 u‖) :=
        (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1 * (‖B (r+1)‖ * 1) := by rw [adjoint.norm_map]; gcongr
      _ = _ := by ring
  apply opNorm_le_bound _ (by positivity)
  intro x
  change ‖(((r+1 : ℕ) : ℂ) ^ 2) •
    (((insertion r 1 u).adjoint ∘L B (r+1) ∘L insertion r 1 u) x)‖ ≤ _
  rw [norm_smul, norm_pow, Complex.norm_natCast]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    ((le_opNorm _ x).trans (mul_le_mul_of_nonneg_right hc (norm_nonneg x)))
    (sq_nonneg (((r+1 : ℕ) : ℝ)))

lemma pairTerm_norm (B : ∀ m, HN L m →L[ℂ] HN L m) (u : L2T L)
    (hu : ‖u‖ = 1) (r : ℕ) :
    ‖pairTerm B u r‖ ≤ (((r+2 : ℕ) : ℝ) * ((r+1 : ℕ) : ℝ)) * ‖B (r+2)‖ := by
  have hi := insertion_unit r 2 u hu
  have hp : ‖power (r+2) u‖ = 1 := by rw [power_norm, hu, one_pow]
  have hc : ‖(insertion r 2 u).adjoint (B (r+2) (power (r+2) u))‖ ≤ ‖B (r+2)‖ := by
    calc
      _ ≤ ‖(insertion r 2 u).adjoint‖ * ‖B (r+2) (power (r+2) u)‖ := le_opNorm _ _
      _ ≤ 1 * (‖B (r+2)‖ * 1) := by
        rw [adjoint.norm_map]
        exact mul_le_mul hi (by simpa [hp] using le_opNorm (B (r+2)) (power (r+2) u))
          (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  simpa only [pairTerm, norm_smul, norm_mul, Complex.norm_natCast] using
    mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ (((r+2 : ℕ) : ℝ) * ((r+1 : ℕ) : ℝ)))

lemma mixedTerm_adjoint (B : ∀ m, HN L m →L[ℂ] HN L m)
    (hB : ∀ m, (B m).adjoint = B m) (u : L2T L) (r : ℕ) :
    (mixedTerm B u r).adjoint = mixedTerm B u r := by
  simp only [mixedTerm, map_smulₛₗ, map_pow, map_natCast, adjoint_comp,
    adjoint_adjoint, hB, comp_assoc]

/-- Actual pair contraction matrix element, with the exact degree factor. -/
lemma pairTerm_matrix (B : ∀ m, HN L m →L[ℂ] HN L m)
    (u : L2T L) (r : ℕ) (x : HN L 2) :
    ⟪x, pairTerm B u r⟫_ℂ = (((r+2 : ℕ) : ℂ) * ((r+1 : ℕ) : ℂ)) *
      ⟪insertion r 2 u x, B (r+2) (power (r+2) u)⟫_ℂ := by
  rw [pairTerm, inner_smul_right, adjoint_inner_right]

end QuantumNLS.Prop022TensorCompressionR115
#print axioms QuantumNLS.Prop022TensorCompressionR115.mixedTerm_norm
#print axioms QuantumNLS.Prop022TensorCompressionR115.pairTerm_norm
#print axioms QuantumNLS.Prop022TensorCompressionR115.mixedTerm_adjoint
#print axioms QuantumNLS.Prop022TensorCompressionR115.pairTerm_matrix

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022TensorCompressionR115." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022TensorCompressionR115." then
      pending := pending.push n
  let roots := pending.size
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
  Lean.logInfo m!"R115 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
