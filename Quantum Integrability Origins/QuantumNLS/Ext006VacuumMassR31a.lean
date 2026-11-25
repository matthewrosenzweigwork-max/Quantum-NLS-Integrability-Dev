import QuantumNLS.Ext006FormalVacuumR31a

/-! EXT-006 R31a: an exact finite-mode norm criterion for the constructed
formal vacuum. The all-degree finite-core norm recurrence now controls an
explicit candidate, without assuming that a weak Fock vacuum already exists.
All sums are nonnegative extended sums; no exchange needs integrability.
The uniform bound from the source's HS strict-contraction condition is NOT
assumed or asserted, and neither is a unitary implementer. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped ENNReal
namespace QuantumNLS.Ext006VacuumMassR31a
open Occupation OccupationHilbert Ext006VacuumRecurrence Ext006CoreLimit
  Ext006CoreNorm Ext006PairCoreCommutator Ext006FormalVacuumR31a

variable {K : Kernel}

/-- Total squared coefficient norm, allowed to be infinite. -/
def mass (K : Kernel) : ℝ≥0∞ := ∑' m, ENNReal.ofReal (‖coefficient K m‖^2)

open Classical in
def modeMass (K : Kernel) (S : Finset ℤ) : ℝ≥0∞ :=
  ∑' m, if m.support ⊆ S then ENNReal.ofReal (‖coefficient K m‖^2) else 0

open Classical in
def sectorMass (K : Kernel) (S : Finset ℤ) (n : ℕ) : ℝ≥0∞ :=
  ∑' m, if m.support ⊆ S ∧ total m = 2*n then
    ENNReal.ofReal (‖coefficient K m‖^2) else 0

theorem sectorMass_eq_core (hK : ∀ a b, K a b = K b a) (S : Finset ℤ) (n : ℕ) :
    sectorMass K S n = ENNReal.ofReal (cc S K n).re := by
  classical
  rw [cc_re_eq, ENNReal.ofReal_sum_of_nonneg (fun _ _ => Complex.normSq_nonneg _)]
  unfold sectorMass
  rw [tsum_eq_sum (s := (coreTerm S K n).support)]
  · apply Finset.sum_congr rfl
    intro m hm
    obtain ⟨hmS, hmn⟩ := coreTerm_support S K n m (Finsupp.mem_support_iff.mp hm)
    rw [ite_eq_left ⟨hmS, hmn⟩, coefficient_even hK S m hmS hmn,
      Complex.normSq_eq_norm_sq]
  · intro m hm
    by_cases hp : m.support ⊆ S ∧ total m = 2*n
    · rw [ite_eq_left hp, coefficient_even hK S m hp.1 hp.2]
      have hz : coreTerm S K n m = 0 := Finsupp.notMem_support_iff.mp hm
      simp [hz]
    · rw [ite_eq_right hp]

/-- Exact all-degree finite-mode norm identity, even when the total is infinite. -/
theorem modeMass_eq_core_series (hK : ∀ a b, K a b = K b a) (S : Finset ℤ) :
    modeMass K S = ∑' n, ENNReal.ofReal (cc S K n).re := by
  classical
  simp_rw [← sectorMass_eq_core hK S]
  unfold sectorMass
  rw [ENNReal.tsum_comm]
  unfold modeMass
  apply tsum_congr
  intro m
  by_cases hmS : m.support ⊆ S
  · rw [ite_eq_left hmS]
    by_cases he : Even (total m)
    · obtain ⟨n, hn⟩ := he
      have ht : total m = 2*n := by omega
      rw [tsum_eq_single n]
      · simp [hmS, ht]
      · intro j hj
        have htj : total m ≠ 2*j := by omega
        simp [htj]
    · rw [coefficient_odd K he]
      simp
  · simp [hmS]

theorem modeMass_le (K : Kernel) (S : Finset ℤ) : modeMass K S ≤ mass K := by
  apply ENNReal.tsum_le_tsum
  intro m
  split_ifs <;> simp

theorem modeMass_mono (K : Kernel) {S T : Finset ℤ} (hST : S ⊆ T) :
    modeMass K S ≤ modeMass K T := by
  classical
  apply ENNReal.tsum_le_tsum
  intro m
  by_cases hm : m.support ⊆ S
  · simp [hm, hm.trans hST]
  · simp [hm]

/-- Finite-mode restrictions exhaust the squared norm of the candidate.
This proof works before Fock membership or a normalized vacuum is known. -/
theorem mass_eq_iSup_modeMass (K : Kernel) : mass K = ⨆ S : Finset ℤ, modeMass K S := by
  classical
  apply le_antisymm
  · unfold mass
    rw [ENNReal.tsum_eq_iSup_sum]
    apply iSup_le
    intro t
    let S := t.biUnion (fun m : Occ => m.support)
    calc
      (∑ m ∈ t, ENNReal.ofReal (‖coefficient K m‖^2)) =
          ∑ m ∈ t, if m.support ⊆ S then ENNReal.ofReal (‖coefficient K m‖^2) else 0 := by
        apply Finset.sum_congr rfl
        intro m hm
        have hs : m.support ⊆ S := Finset.subset_biUnion_of_mem (fun m : Occ => m.support) hm
        rw [ite_eq_left hs]
      _ ≤ modeMass K S := ENNReal.sum_le_tsum t
      _ ≤ ⨆ T : Finset ℤ, modeMass K T := le_iSup (fun T => modeMass K T) S
  · exact iSup_le (modeMass_le K)

/-- The exact finite-mode/all-degree core norm expression for the entire
candidate. This is the norm side still needing a uniform HS estimate. -/
theorem mass_eq_iSup_core_series (hK : ∀ a b, K a b = K b a) :
    mass K = ⨆ S : Finset ℤ, ∑' n, ENNReal.ofReal (cc S K n).re := by
  rw [mass_eq_iSup_modeMass]
  simp_rw [modeMass_eq_core_series hK]

theorem mass_ne_top_iff (K : Kernel) :
    mass K ≠ ⊤ ↔ Summable (fun m => ‖coefficient K m‖^2) := by
  constructor
  · intro hm
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using ENNReal.summable_toReal hm
  · exact Summable.tsum_ofReal_ne_top

/-- A normalized Fock vacuum exists exactly when the explicitly computed
finite-core norm series admit a common finite bound. This does not add that
bound to BD: deriving it from HS and norm<1 is the remaining analytic task. -/
theorem exists_normalized_iff_uniform_core_bound (hK : ∀ a b, K a b = K b a) :
    (∃ x : Fock, WeakVacuum K x ∧ ‖x‖ = 1) ↔
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
        ∀ S : Finset ℤ, (∑' n, ENNReal.ofReal (cc S K n).re) ≤ C := by
  rw [exists_normalized_iff hK, ← mass_ne_top_iff]
  constructor
  · intro hm
    refine ⟨mass K, hm, fun S => ?_⟩
    rw [← modeMass_eq_core_series hK]
    exact modeMass_le K S
  · rintro ⟨C, hC, hb⟩
    apply ne_top_of_le_ne_top hC
    rw [mass_eq_iSup_core_series hK]
    exact iSup_le hb

end QuantumNLS.Ext006VacuumMassR31a

#print axioms QuantumNLS.Ext006VacuumMassR31a.sectorMass_eq_core
#print axioms QuantumNLS.Ext006VacuumMassR31a.modeMass_eq_core_series
#print axioms QuantumNLS.Ext006VacuumMassR31a.mass_eq_iSup_core_series
#print axioms QuantumNLS.Ext006VacuumMassR31a.exists_normalized_iff_uniform_core_bound

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006VacuumMassR31a." then
      pending := pending.push n
      roots := roots + 1
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
  Lean.logInfo m!"Round31a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
