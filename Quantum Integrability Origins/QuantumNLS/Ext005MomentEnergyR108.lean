import QuantumNLS.Ext005PairSector
import Mathlib.MeasureTheory.Measure.Restrict

/-! R108: number-moment comparison and the energy interpretation on the actual
physical Fock space. These are static estimates, not an evolution theorem.
In particular no estimate on an as yet unconstructed solution is assumed. -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace QuantumNLS.Ext005MomentEnergyR108
open Ext025B3PhysicalSectors Ext005Moments BetheCoefficientTransform
open MeasureTheory
variable {L : ℝ} [Fact (0 < L)]

/-- The spectral energy series. Finiteness is always supplied separately by
membership in `momentDomain`; an unrestricted real `tsum` is not a domain test. -/
def energy (j : ℕ) (x : Fock L) : ℝ :=
  ∑' n, momentWeight j n * ‖x n‖ ^ 2

/-- Squared Q(A) norm, with the form-domain argument kept explicit. -/
def rootEnergy (j : ℕ) (x : momentDomain (L := L) j) : ℝ :=
  ‖momentRoot (L := L) j x‖ ^ 2

theorem energy_nonneg (j : ℕ) (x : Fock L) : 0 ≤ energy j x :=
  tsum_nonneg (fun n => mul_nonneg (momentWeight_nonneg j n) (sq_nonneg _))

theorem energy_eq_root (j : ℕ) (x : momentDomain (L := L) j) :
    energy j x.val = ‖momentRoot j x‖ ^ 2 :=
  (momentRoot_norm_sq j x).symm

theorem weight_mono {k j : ℕ} (hkj : k ≤ j) (n : ℕ) :
    momentWeight k n ≤ momentWeight j n := by
  apply pow_le_pow_right₀
  · nlinarith [Nat.cast_nonneg (α := ℝ) n]
  · exact hkj

/-- Every higher form domain embeds into every lower form domain. -/
theorem domain_mono {k j : ℕ} (hkj : k ≤ j) {x : Fock L}
    (hx : x ∈ momentDomain (L := L) j) : x ∈ momentDomain (L := L) k := by
  apply (momentDomain_iff k x).2
  exact Summable.of_nonneg_of_le
    (fun n => mul_nonneg (momentWeight_nonneg k n) (sq_nonneg _))
    (fun n => mul_le_mul_of_nonneg_right (weight_mono hkj n) (sq_nonneg _))
    ((momentDomain_iff j x).1 hx)

theorem energy_mono {k j : ℕ} (hkj : k ≤ j) {x : Fock L}
    (hx : x ∈ momentDomain (L := L) j) : energy k x ≤ energy j x := by
  exact ((momentDomain_iff k x).1 (domain_mono hkj hx)).tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_right (weight_mono hkj n) (sq_nonneg _))
    ((momentDomain_iff j x).1 hx)

theorem norm_sq_le_energy (j : ℕ) (x : momentDomain (L := L) j) :
    ‖x.val‖ ^ 2 ≤ energy j x.val := by
  rw [energy_eq_root]
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  apply lp.norm_mono (by norm_num)
  intro n
  change ‖x.val n‖ ≤ ‖(Real.sqrt (momentWeight j n) : ℂ) • x.val n‖
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  nlinarith [norm_nonneg (x.val n), Real.one_le_sqrt.mpr (momentWeight_one_le j n)]

/-- The entire zero-particle sector, hence every vacuum datum, has every
number moment equal to its Hilbert norm squared. -/
theorem vacuum_sector_energy (j : ℕ) (v : HN L 0) :
    inclusion L 0 v ∈ momentDomain (L := L) j ∧
      energy j (inclusion L 0 v) = ‖v‖ ^ 2 := by
  have hm : inclusion L 0 v ∈ momentDomain (L := L) j := by
    have h := sector_mem_momentDomain j 0 (inclusion L 0 v)
    have he : projection L 0 (inclusion L 0 v) = inclusion L 0 v := by
      change lp.single 2 0 ((lp.single 2 0 v) 0) = lp.single 2 0 v
      simp [lp.single_apply]
    rwa [he] at h
  refine ⟨hm, ?_⟩
  change (∑' n, momentWeight j n * ‖(lp.single 2 0 v) n‖ ^ 2) = ‖v‖ ^ 2
  rw [tsum_eq_single 0]
  · simp [lp.single_apply, momentWeight]
  · intro n hn
    simp [lp.single_apply, hn]

/-- Essential uniform comparison-energy bound on an interval or measurable
time set. Membership and the bound hold almost everywhere, as required by D3. -/
def EnergyBounded (j : ℕ) (I : Set ℝ) (x : ℝ → Fock L) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ t ∂volume.restrict I,
    x t ∈ momentDomain (L := L) j ∧ energy j (x t) ≤ C

theorem energyBounded_iff_root (j : ℕ) (I : Set ℝ) (x : ℝ → Fock L) :
    EnergyBounded j I x ↔ ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ t ∂volume.restrict I,
      ∃ hx : x t ∈ momentDomain (L := L) j,
        rootEnergy j ⟨x t, hx⟩ ≤ C := by
  constructor
  · rintro ⟨C, hC, h⟩
    refine ⟨C, hC, h.mono ?_⟩
    intro t ht
    refine ⟨ht.1, ?_⟩
    exact (energy_eq_root j (⟨x t, ht.1⟩ : momentDomain (L := L) j)).symm.le.trans ht.2
  · rintro ⟨C, hC, h⟩
    refine ⟨C, hC, h.mono ?_⟩
    rintro t ⟨hx, hb⟩
    refine ⟨hx, ?_⟩
    exact (energy_eq_root j (⟨x t, hx⟩ : momentDomain (L := L) j)).le.trans hb

theorem energyBounded_mono {k j : ℕ} (hkj : k ≤ j) (I : Set ℝ)
    (x : ℝ → Fock L) (h : EnergyBounded j I x) : EnergyBounded k I x := by
  obtain ⟨C, hC, hb⟩ := h
  refine ⟨C, hC, hb.mono ?_⟩
  intro t ht
  exact ⟨domain_mono hkj ht.1, (energy_mono hkj ht.1).trans ht.2⟩

end QuantumNLS.Ext005MomentEnergyR108
#print axioms QuantumNLS.Ext005MomentEnergyR108.domain_mono
#print axioms QuantumNLS.Ext005MomentEnergyR108.norm_sq_le_energy
#print axioms QuantumNLS.Ext005MomentEnergyR108.vacuum_sector_energy
#print axioms QuantumNLS.Ext005MomentEnergyR108.energyBounded_iff_root
#print axioms QuantumNLS.Ext005MomentEnergyR108.energyBounded_mono

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005MomentEnergyR108." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005MomentEnergyR108." then
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
  Lean.logInfo m!"R108 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
