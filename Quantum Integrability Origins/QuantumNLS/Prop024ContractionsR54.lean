import QuantumNLS.Prop024PhysicalHamiltonianR54
import QuantumNLS.Prop022TensorCompressionR115
import QuantumNLS.Ext006SourceWeylR44a

/-! Round 54: arbitrary creation/annihilation slot contractions of the
actual symmetric physical factorial kernels.  The contractions use the frozen
physical insertion maps; their norm bound follows from unit-profile
contraction and requires no compatibility premise. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace ComplexConjugate

namespace QuantumNLS.Prop024ContractionsR54

open BetheCoefficientTransform PhysicalTensor Ext025B3PhysicalSectors
  Prop022TensorCompressionR115 ContinuousLinearMap
open Ext006SourceWeylR44a Prop024PhysicalHamiltonianR54

variable {L : ℝ} [Fact (0 < L)]
attribute [local instance] InnerProductSpace.complexToReal

/-- The actual physical Weyl displacement `W(sqrt N u)`, imported from the
frozen EXT-006 implementation. EXT-006 writes its source Weyl as
`exp(i(a*(f)+a(f)))`; hence the printed `exp(a*(v)-a(v))` uses `f = -i v`. -/
def physicalWeyl (N : ℕ) (u : L2T L) :
    Fock L ≃ₗᵢ[ℂ] Fock L :=
  sourceWeyl ((-Complex.I * (Real.sqrt (N : ℝ) : ℂ)) • u)

theorem physicalWeyl_norm (N : ℕ) (u : L2T L) (x : Fock L) :
    ‖physicalWeyl N u x‖ = ‖x‖ :=
  (physicalWeyl N u).norm_map x

/-- The exact maximal-domain test for the physically translated vector. -/
theorem physicalWeyl_mem_interaction_domain_iff (N : ℕ)
    (B : ∀ m, HN L m →L[ℂ] HN L m) (u : L2T L) (x : Fock L) :
    physicalWeyl N u x ∈ (interaction N B).domain ↔
      Memℓp (fun n => interactionSector N n B (physicalWeyl N u x n)) 2 := by
  exact interaction_mem_domain_iff N B (physicalWeyl N u x)

/-- Transport a finite-sector map along equality of the two physical
particle counts. -/
def castSectorMapCod {m n k : ℕ} (h : m = n)
    (A : HN L k →L[ℂ] HN L m) : HN L k →L[ℂ] HN L n := by
  cases h
  exact A

theorem norm_castSectorMapCod {m n k : ℕ} (h : m = n)
    (A : HN L k →L[ℂ] HN L m) : ‖castSectorMapCod (L := L) h A‖ = ‖A‖ := by
  cases h
  rfl

/-- Insert a unit profile in all but `k` of the `m` symmetric slots. -/
def insertSector (m k : ℕ) (hk : k ≤ m) (u : L2T L) :
    HN L k →L[ℂ] HN L m :=
  castSectorMapCod (L := L) (Nat.sub_add_cancel hk)
    (insertion (m-k) k u)

theorem insertSector_norm_le (m k : ℕ) (hk : k ≤ m)
    (u : L2T L) (hu : ‖u‖ = 1) : ‖insertSector m k hk u‖ ≤ 1 := by
  rw [insertSector, norm_castSectorMapCod]
  exact insertion_unit (m-k) k u hu

/-- The physical `(a,b)` Wick kernel obtained by contracting the remaining
creation and annihilation slots against the same unit profile. -/
def contractedKernel (m a b : ℕ) (ha : a ≤ m) (hb : b ≤ m)
    (B : ∀ r, HN L r →L[ℂ] HN L r) (u : L2T L) :
    HN L b →L[ℂ] HN L a :=
  (insertSector m a ha u).adjoint ∘L B m ∘L insertSector m b hb u

/-- Contracting either side against a unit profile is a contraction, so the
actual physical Wick kernel has operator norm at most the original kernel. -/
theorem contractedKernel_norm_le (m a b : ℕ) (ha : a ≤ m) (hb : b ≤ m)
    (B : ∀ r, HN L r →L[ℂ] HN L r) (u : L2T L) (hu : ‖u‖ = 1) :
    ‖contractedKernel m a b ha hb B u‖ ≤ ‖B m‖ := by
  have hout := insertSector_norm_le m a ha u hu
  have hin := insertSector_norm_le m b hb u hu
  unfold contractedKernel
  calc
    _ ≤ ‖(insertSector m a ha u).adjoint‖ *
          (‖B m‖ * ‖insertSector m b hb u‖) :=
      (opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖B m‖ * 1) := by
      rw [adjoint.norm_map]
      gcongr
    _ = ‖B m‖ := by ring

/-- The source factorial envelope passes unchanged to every physical slot
contraction. -/
theorem contractedKernel_factorial_bound (m a b : ℕ)
    (ha : a ≤ m) (hb : b ≤ m)
    (B : ∀ r, HN L r →L[ℂ] HN L r) (u : L2T L)
    (hu : ‖u‖ = 1) (M A : ℝ)
    (hB : Prop022FactorialCoefficientsR115.FactorialBound B M A)
    (hm : 1 ≤ m) :
    ‖contractedKernel m a b ha hb B u‖ ≤
      M * A ^ m / Real.sqrt ((2*m).factorial : ℝ) := by
  exact (contractedKernel_norm_le m a b ha hb B u hu).trans
    (hB m hm)

end QuantumNLS.Prop024ContractionsR54

#print axioms QuantumNLS.Prop024ContractionsR54.contractedKernel_norm_le
#print axioms QuantumNLS.Prop024ContractionsR54.contractedKernel_factorial_bound

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop024ContractionsR54." ||
        n.toString.startsWith "_private.QuantumNLS.Prop024ContractionsR54." then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").any (fun s => s == "HeldGP14Tonelli" || s == "RegularCut") then
        throwError "Held identifier in dependency closure: {n}"
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
  Lean.logInfo m!"R54 contractions aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
