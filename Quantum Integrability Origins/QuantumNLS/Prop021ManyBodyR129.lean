import QuantumNLS.Prop021DuhamelR128
import QuantumNLS.LinearTailPhysicalEvolution
import QuantumNLS.GenericUAdjoint

/-! Literal Q7B many-body sectors and their whole-Fock unitary action.
The mean-field parameter N is independent of the sector particle count n.
Every finite placement coefficient is kept exactly. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 200000
open scoped InnerProductSpace Topology ENNReal
namespace QuantumNLS.Prop021ManyBodyR129
open BetheCoefficientTransform Ext025B3PhysicalSectors KernelDefinition
open LinearTailPhysicalEvolution
variable {L : ℝ} [Fact (0 < L)]

/-- N sum_{m=1}^n N^{-m} (n)_m U_{n,m}(B_m), with no m=0 term. -/
def sector (B : ∀ m, HN L m →L[ℂ] HN L m) (N n : ℕ) : HN L n →L[ℂ] HN L n :=
  (N : ℂ) • ∑ i : Fin n,
    (((N : ℝ)⁻¹ ^ (i.val+1) * (n.descFactorial (i.val+1) : ℝ) : ℝ) : ℂ) •
      genericU_N_r n (i.val+1) (Nat.succ_le_of_lt i.isLt) (B (i.val+1))

lemma sector_adjoint (B : ∀ m, HN L m →L[ℂ] HN L m)
    (hB : ∀ m, (B m).adjoint = B m) (N n : ℕ) :
    (sector B N n).adjoint = sector B N n := by
  simp only [sector, map_smulₛₗ, map_sum, Complex.conj_natCast,
    Complex.conj_ofReal, GenericUAdjoint.adjoint_genericU_N_r, hB]

lemma sector_vacuum (B : ∀ m, HN L m →L[ℂ] HN L m) (N : ℕ) :
    sector B N 0 = 0 := by simp [sector]

/-- The maximal Hilbert direct sum of the literal finite sector sums. -/
def hamiltonian (B : ∀ m, HN L m →L[ℂ] HN L m) (N : ℕ) : Fock L →ₗ.[ℂ] Fock L :=
  block (sector B N)

lemma hamiltonian_domain (B : ∀ m, HN L m →L[ℂ] HN L m) (N : ℕ) (x : Fock L) :
    x ∈ (hamiltonian B N).domain ↔ Memℓp (fun n => sector B N n (x n)) 2 := Iff.rfl

lemma hamiltonian_symmetric (B : ∀ m, HN L m →L[ℂ] HN L m)
    (hB : ∀ m, (B m).adjoint = B m) (N : ℕ)
    (x y : (hamiltonian B N).domain) :
    ⟪hamiltonian B N x,y.val⟫_ℂ = ⟪x.val,hamiltonian B N y⟫_ℂ :=
  Prop021DuhamelR128.block_symmetric _ (sector_adjoint B hB N) x y

/-- Hilbert direct sum of an arbitrary family of genuine sector unitaries. -/
def lift (U : ∀ n, HN L n ≃ₗᵢ[ℂ] HN L n) : Fock L ≃ₗᵢ[ℂ] Fock L where
  toFun x := ⟨fun n => U n (x n), by
    apply Memℓp.of_norm
    simpa only [LinearIsometryEquiv.norm_map] using (lp.memℓp x).norm⟩
  invFun x := ⟨fun n => (U n).symm (x n), by
    apply Memℓp.of_norm
    simpa only [LinearIsometryEquiv.norm_map] using (lp.memℓp x).norm⟩
  left_inv x := by apply lp.ext; funext n; exact (U n).symm_apply_apply (x n)
  right_inv x := by apply lp.ext; funext n; exact (U n).apply_symm_apply (x n)
  map_add' x y := by apply lp.ext; funext n; exact map_add (U n) (x n) (y n)
  map_smul' c x := by apply lp.ext; funext n; exact map_smul (U n) c (x n)
  norm_map' x := by
    rw [lp.norm_eq_tsum_rpow (by norm_num : (0:ℝ) < (2:ℝ≥0∞).toReal),
      lp.norm_eq_tsum_rpow (by norm_num : (0:ℝ) < (2:ℝ≥0∞).toReal)]
    congr 1
    apply tsum_congr
    intro n
    change ‖U n (x n)‖ ^ _ = _
    rw [LinearIsometryEquiv.norm_map]

lemma lift_apply (U : ∀ n, HN L n ≃ₗᵢ[ℂ] HN L n) (x : Fock L) (n : ℕ) :
    lift U x n = U n (x n) := rfl

/-- Each sector uses the actual bounded spectral exponential exp(-it H_{N,n}). -/
def sectorEvolution (B : ∀ m, HN L m →L[ℂ] HN L m)
    (hB : ∀ m, (B m).adjoint = B m) (N n : ℕ) (t : ℝ) :
    HN L n ≃ₗᵢ[ℂ] HN L n :=
  Unitary.linearIsometryEquiv ⟨evolution (sector B N n) t,
    evolution_unitary (show IsSelfAdjoint (sector B N n) from sector_adjoint B hB N n) t⟩

def manyBodyEvolution (B : ∀ m, HN L m →L[ℂ] HN L m)
    (hB : ∀ m, (B m).adjoint = B m) (N : ℕ) (t : ℝ) : Fock L ≃ₗᵢ[ℂ] Fock L :=
  lift (fun n => sectorEvolution B hB N n t)

lemma manyBodyEvolution_apply (B : ∀ m, HN L m →L[ℂ] HN L m)
    (hB : ∀ m, (B m).adjoint = B m) (N n : ℕ) (t : ℝ) (x : Fock L) :
    manyBodyEvolution B hB N t x n = evolution (sector B N n) t (x n) := rfl

/-- Number-sector extraction commutes exactly with the constructed evolution. -/
theorem projection_commutes (B : ∀ m, HN L m →L[ℂ] HN L m)
    (hB : ∀ m, (B m).adjoint = B m) (N n : ℕ) (t : ℝ) (x : Fock L) :
    projection L n (manyBodyEvolution B hB N t x) =
      manyBodyEvolution B hB N t (projection L n x) := by
  apply lp.ext
  funext m
  by_cases h : m = n
  · subst m; simp only [projection_same, manyBodyEvolution_apply]
  · simp only [projection_other L n m h, manyBodyEvolution_apply, map_zero]

/-- The exact N-particle orbit extracted from coherent data evolves under
precisely H_{N,N}; the falling-factorial coefficient is never replaced. -/
theorem exact_sector_extraction (B : ∀ m, HN L m →L[ℂ] HN L m)
    (hB : ∀ m, (B m).adjoint = B m) (N : ℕ) (t : ℝ) (x : Fock L)
    (ψ : HN L N) (c : ℂ) (hx : x N = c • ψ) :
    manyBodyEvolution B hB N t x N = c • evolution (sector B N N) t ψ := by
  rw [manyBodyEvolution_apply, hx, map_smul]

end QuantumNLS.Prop021ManyBodyR129
#print axioms QuantumNLS.Prop021ManyBodyR129.hamiltonian_symmetric
#print axioms QuantumNLS.Prop021ManyBodyR129.projection_commutes
#print axioms QuantumNLS.Prop021ManyBodyR129.exact_sector_extraction

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if ["Prop021ManyBodyR129"].any
        (fun m => n.toString.startsWith ("QuantumNLS." ++ m ++ ".") ||
          n.toString.startsWith ("_private.QuantumNLS." ++ m ++ ".")) then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").contains "HeldGP14Tonelli" ||
          (n.toString.splitOn ".").contains "RegularCut" then
        throwError "Forbidden held dependency: {n}"
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
  Lean.logInfo m!"R129 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
