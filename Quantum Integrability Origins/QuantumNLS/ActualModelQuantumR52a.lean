import QuantumNLS.Def044InterfacesR51a
import QuantumNLS.MixedCommutator
import QuantumNLS.KernelFactorialBound

/-! R-E679E41D: discharge the exact quantum part of DEF-044 from
accepted theorems. All particle numbers here are positive (N+1).
The imported R51a source/object pair was cmp-verified before reuse.
No monodromy B/C identification is used. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
namespace QuantumNLS.ActualModelQuantumR52a
open PhysicalTensor BetheLabels BetheSpectralCharges BetheCoefficientTransform
open Def044D1SpectralR51a
variable {L κ : ℝ} [Fact (0 < L)]

/-- Inhabited from the accepted actual basis, transfer and kernel theorems;
no quantum requirement is an input hypothesis. -/
theorem quantum_requirements (hκ : 0 < κ) : QuantumRequirements (L := L) hκ where
  entire := fun N => BoundedBetheTransfer.entire L
  diagonal := fun N z m => BoundedBetheTransfer.eigenrelation L hκ (by omega) z m
  exact_eigenvalue := by
    intro N m z hz
    have hf : Def044D1SpectralR51a.root (L := L) (κ := κ) N m =
        rapidity L (N+1) (κ/(N+1)) m := by
      funext j
      rfl
    rw [hf]
    simpa only [Nat.cast_add, Nat.cast_one] using
      BoundedBetheTransfer.spectral_formula L hκ (by omega : 0 < N+1) m z
        (by simpa only [hf, Nat.cast_add, Nat.cast_one] using hz)
  normal := fun N z => BoundedBetheTransfer.normal L hκ (by omega) z
  commute := fun N z w => BoundedBetheTransfer.commute L hκ (by omega) z w
  commute_adjoint := fun N z w => BoundedBetheTransfer.commute_adjoint L hκ (by omega) z w
  expansion := fun N z => rfl
  factorial_kernel := by
    intro m hm z
    simpa only [abs_of_pos hκ] using KernelFactorialBound.kernel_bound (L := L) κ m z

/-- The counts tested by the theorem retain the corrected array label. -/
def countSymbol (I : Finset ℤ) (θ : ℤ → ℝ) (N : ℕ) (m : MArr (N+1)) : ℝ :=
  ∑ n ∈ I, θ n * (marrArr (N+1) m).1 n

/-- The charges retain the actual rapidities at κ/(N+1), without time rescaling. -/
def chargeSymbol (R : Finset ℕ) (t : ℕ → ℝ) (N : ℕ) (m : MArr (N+1)) : ℝ :=
  ∑ r ∈ R, t r * eigenvalue L (N+1) (κ/(N+1)) r m

/-- Both exponentials are defined on the entire sector through the same
complete Bethe resolution; this definition imposes no domain assumption. -/
def countUnitary (hκ : 0 < κ) (I : Finset ℤ) (θ : ℤ → ℝ) (N : ℕ) :
    HN L (N+1) ≃ₗᵢ[ℂ] HN L (N+1) :=
  evolution (basis (L := L) hκ N) (countSymbol I θ N) 1

def chargeUnitary (hκ : 0 < κ) (R : Finset ℕ) (t : ℕ → ℝ) (N : ℕ) :
    HN L (N+1) ≃ₗᵢ[ℂ] HN L (N+1) :=
  evolution (basis (L := L) hκ N) (chargeSymbol (L := L) (κ := κ) R t N) 1

/-- Strong commutation uses the shared diagonal spectral multipliers. -/
theorem unitaries_commute (hκ : 0 < κ) (I : Finset ℤ) (R : Finset ℕ)
    (θ : ℤ → ℝ) (t : ℕ → ℝ) (N : ℕ) (ψ : HN L (N+1)) :
    chargeUnitary hκ R t N (countUnitary hκ I θ N ψ) =
      countUnitary hκ I θ N (chargeUnitary hκ R t N ψ) :=
  evolution_commute _ _ _ _ _ _

end QuantumNLS.ActualModelQuantumR52a
#print axioms QuantumNLS.ActualModelQuantumR52a.quantum_requirements
#print axioms QuantumNLS.ActualModelQuantumR52a.unitaries_commute

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.ActualModelQuantumR52a." ||
        n.toString.startsWith "_private.QuantumNLS.ActualModelQuantumR52a." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 then
        throwError "Rejected dependency: {n}"
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
  Lean.logInfo m!"Round52 aggregate audit PASS: {own} own constants; {seen.size} transitive constants; standard only."
