import QuantumNLS.Ext006WeakDifferentiationR44a
import QuantumNLS.Ext006RowPairingR37a

/-! Irreducibility of the constructed bounded exponential family. These
statements quantify over arbitrary bounded commutants. The identification
with the source spectral Weyl operators remains a separate obligation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006ExponentialIrreducibleR44a
open Occupation Ext006BogoliubovAlg Ext006VacuumRecurrence Ext006SmoothOperatorsR34a
open Ext006StrongFieldR41a Ext006FieldBoundsR42a Ext006BoundedExponentialR43a
open Ext006AnalyticFieldR42a Ext006EntireFieldR43a
open Ext006WeakDifferentiationR44a Ext006IdentityCyclicR35a Ext006RowPairingR37a

/-- The two real smearings h and i h separate the actual annihilator and
creator in weak matrix elements. No field domain of T w is supplied. -/
theorem commutes_rows_weak (T : Fock →L[ℂ] Fock) (hT : CommutesExponential T)
    {N M : ℕ} (h : H) (v w : D)
    (hv : ParticleBound N v.1) (hw : ParticleBound M w.1) :
    inner ℂ (C h v).1 (T w.1) = inner ℂ v.1 (T (A h w).1) ∧
    inner ℂ (A h v).1 (T w.1) = inner ℂ v.1 (T (C h w).1) := by
  have he := commutes_field_weak T hT h v w hv hw
  have hi := commutes_field_weak T hT (Complex.I • h) v w hv hw
  simp [field,Ext006InverseGraphsR36a.A_smul,Ext006InverseGraphsR36a.C_smul,
    inner_smul_left,inner_smul_right] at he hi
  constructor
  · linear_combination (norm := (ring_nf; simp [Complex.I_sq]))
      (1/2 : ℂ)*he+(Complex.I/2)*hi
  · linear_combination (norm := (ring_nf; simp [Complex.I_sq]))
      (1/2 : ℂ)*he-(Complex.I/2)*hi

lemma commutant_vacuum_weak (T : Fock →L[ℂ] Fock) (hT : CommutesExponential T) :
    WeakVacuum (fun _ _ => 0) (T vacuum) := by
  intro a m
  have he := (commutes_rows_weak T hT (lp.single 2 a 1) (ketD m) (ketD 0)
    (ket_particleBound m) (ket_particleBound 0)).1
  rw [A_mode_ket] at he
  simp only [Finsupp.zero_apply,Nat.cast_zero,Real.sqrt_zero,Complex.ofReal_zero,
    zero_smul,Submodule.coe_zero,map_zero,inner_zero_right] at he
  rw [C_mode_ket,Submodule.coe_smul,inner_smul_left] at he
  simpa [ketD,vacuum,lp.inner_single_left,RCLike.inner_apply] using he

lemma commutant_vacuum (T : Fock →L[ℂ] Fock) (hT : CommutesExponential T) :
    T vacuum = (T vacuum) 0 • vacuum := by
  apply vacuum_coefficient_injective (commutant_vacuum_weak T hT)
    (vacuum_weak.smul ((T vacuum) 0))
  simp [vacuum,lp.single_apply]

lemma commutant_column_step (T : Fock →L[ℂ] Fock) (hT : CommutesExponential T)
    (z : ℂ) (m : Occ) (hm : T (ketD m).1 = z • (ketD m).1) (a : ℤ) :
    T (ketD (m+e a)).1 = z • (ketD (m+e a)).1 := by
  have hc : T (C (lp.single 2 a 1) (ketD m)).1 =
      z • (C (lp.single 2 a 1) (ketD m)).1 := by
    apply Ext006ClosedFieldGraphsR36a.ket_total
    intro n
    rw [← (commutes_rows_weak T hT (lp.single 2 a 1) (ketD n) (ketD m)
      (ket_particleBound n) (ket_particleBound m)).2,hm,inner_smul_right,
      ← C_adjoint,inner_smul_right]
  rw [C_mode_ket,Submodule.coe_smul,map_smul,smul_smul] at hc
  have hq : (Real.sqrt ((m a : ℝ)+1) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (show 0 < (m a : ℝ)+1 by positivity)).ne'
  rw [mul_comm z] at hc
  rw [← smul_smul] at hc
  exact (smul_right_injective _ hq) hc

/-- Every bounded operator commuting with all actual field exponentials is
scalar on the whole Fock completion. -/
theorem commutant_scalar (T : Fock →L[ℂ] Fock) (hT : CommutesExponential T) :
    ∃ z : ℂ, ∀ x : Fock, T x = z • x := by
  let z := (T vacuum) 0
  have hcol : ∀ k : ℕ, ∀ m : Occ, total m=k → T (ketD m).1=z • (ketD m).1 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro m hmk
      by_cases hm : m=0
      · subst m
        exact commutant_vacuum T hT
      · obtain ⟨a,ha⟩ : ∃ a, m a ≠ 0 := by
          by_contra! hz
          exact hm (Finsupp.ext hz)
        have hma : 1 ≤ m a := Nat.one_le_iff_ne_zero.mpr ha
        have ht := total_sub_e hma
        have hk := ih (total (m-e a)) (by omega) (m-e a) rfl
        have he := commutant_column_step T hT z (m-e a) hk a
        rwa [shift_sub_add hma] at he
  refine ⟨z,fun x => ?_⟩
  have hTsum := T.hasSum (lp.hasSum_single (by norm_num) x)
  have hzsum := (lp.hasSum_single (by norm_num) x).const_smul z
  have hterm (m : Occ) : T (lp.single 2 m (x m)) = z • (lp.single 2 m (x m)) := by
    have hs : (lp.single 2 m (x m) : Fock) = x m • (ketD m).1 := by
      rw [ketD,← lp.single_smul]
      simp
    rw [hs,map_smul,hcol (total m) m rfl,smul_smul,smul_smul,mul_comm]
  simp only [hterm] at hTsum
  exact hTsum.unique hzsum

/-- A unitary commutant has a scalar of norm one. -/
theorem unitary_commutant_phase (T : Fock ≃ₗᵢ[ℂ] Fock)
    (hT : CommutesExponential T.toLinearIsometry.toContinuousLinearMap) :
    ∃ z : ℂ, ‖z‖=1 ∧ ∀ x : Fock, T x=z • x := by
  obtain ⟨z,hz⟩ := commutant_scalar T.toLinearIsometry.toContinuousLinearMap hT
  refine ⟨z,?_,hz⟩
  have hn : ‖T vacuum‖ = ‖z • vacuum‖ := congrArg norm (hz vacuum)
  simpa only [LinearIsometryEquiv.norm_map,norm_smul,vacuum_norm,mul_one] using hn.symm

end QuantumNLS.Ext006ExponentialIrreducibleR44a
#print axioms QuantumNLS.Ext006ExponentialIrreducibleR44a.commutes_rows_weak
#print axioms QuantumNLS.Ext006ExponentialIrreducibleR44a.commutant_scalar
#print axioms QuantumNLS.Ext006ExponentialIrreducibleR44a.unitary_commutant_phase

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006ExponentialIrreducibleR44a." then
      pending := pending.push n
      roots := roots + 1
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
  Lean.logInfo m!"Round44a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
