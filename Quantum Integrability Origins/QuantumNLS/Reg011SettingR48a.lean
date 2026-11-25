import QuantumNLS.Reg011SequencesR48a
import QuantumNLS.TerraMultiRound79Characterization

/-! Literal REG-010 input and the native subspace V ∩ h^s. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.Fourier
open QuantumNLS.RootWeightedCellsR26
namespace QuantumNLS.Reg011SettingR48a
variable {L κ : ℝ} [Fact (0 < L)]
abbrev Seq := lp (fun _ : ℤ => ℂ) 2

/-- EXACT printed REG-010 statement (fractional_moments.tex:49): for every
0 ≤ s ≤ 2 and every L² field, H^s membership, shifted physical moment
finiteness, and shifted indexed action summability are equivalent. The
indexed action map is continuous into the displayed weighted ℓ¹ space and
sends bounded sets to bounded sets. The ℓ¹ realization multiplies each
coordinate by the displayed weight, an isometry for the weighted ℓ¹ norm.
This is the single unaccepted predecessor input, not a REG-011 conclusion. -/
def Reg010LowOrdersInput (hκ : 0 < κ) : Prop :=
  ∀ s : ℝ, 0 ≤ s → s ≤ 2 →
    (∀ u : L2T L,
      ((∃ v : H02 L s, v.val = u) ↔
        Integrable (fun t : ℝ => (1+|t|)^(2*s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) ∧
      (Integrable (fun t : ℝ => (1+|t|)^(2*s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) ↔
        Summable (fun n : ℤ => (1+|momentum L n|)^(2*s) * (QuantumNLS.RootIndexedMasses.masses hκ u).1 n))) ∧
    ∃ A : H02 L s → lp (fun _ : ℤ => ℝ) 1,
      (∀ u n, A u n = (1+|momentum L n|)^(2*s) * (QuantumNLS.RootIndexedMasses.masses hκ u.val).1 n) ∧
      Continuous A ∧ ∀ B : Set (H02 L s), Bornology.IsBounded B → Bornology.IsBounded (A '' B)

/-- Canonical coordinate-preserving inclusion h^s ↪ ℓ², with its norm
continuity proved by the Fourier realization of the existing spaces. -/
def toBase (s : ℝ) (hs : 0 ≤ s) : h02 L s →L[ℂ] Seq :=
  (fourierL2 L).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((H02.toL2 hs).comp
      (fourierHs (L := L) (one_le_def002 L hs)).symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem toBase_apply (s : ℝ) (hs : 0 ≤ s) (z : h02 L s) (n : ℤ) :
    toBase (L := L) s hs z n = z.val n := by
  exact congrArg (fun q : h02 L s => q.val n)
    ((fourierHs (L := L) (one_le_def002 L hs)).apply_symm_apply z)

/-- The subspace of h^s whose underlying ℓ² point belongs to V. Its topology
is the subtype h^s topology, exactly as in the printed theorem. -/
def Target (V : Set Seq) (s : ℝ) (hs : 0 ≤ s) := {z : h02 L s // toBase (L := L) s hs z ∈ V}

variable {V : Set Seq}

def ExactModuli (e : L2T L ≃ₜ V) (hκ : 0 < κ) : Prop :=
  ∀ u n, ‖(e u).val n‖^2 = (QuantumNLS.RootIndexedMasses.masses hκ u).1 n

def lift (e : L2T L ≃ₜ V) (hκ : 0 < κ) (he : ExactModuli e hκ)
    (s : ℝ) (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (u : H02 L s) : h02 L s :=
  PosWeight.WSeq.mk _ (fun n => (e u.val).val n) (by
    have hx := ((QuantumNLS.TerraMultiRound79Characterization.closed_interval_characterization κ hκ u.val s hs0 hs2).2).mp
      (((QuantumNLS.TerraMultiRound79Characterization.closed_interval_characterization κ hκ u.val s hs0 hs2).1).mp ⟨u,rfl⟩)
    refine hx.congr (fun n => ?_)
    change (1+|momentum L n|)^(2*s) * (QuantumNLS.RootIndexedMasses.masses hκ u.val).1 n =
      (1+|momentum L n|)^(2*s) * ‖(e u.val).val n‖^2
    exact congrArg (fun q : ℝ => (1+|momentum L n|)^(2*s)*q) (he u.val n).symm)

theorem lift_apply (e : L2T L ≃ₜ V) (hκ : 0 < κ) (he : ExactModuli e hκ)
    (s : ℝ) (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (u : H02 L s) (n : ℤ) :
    (lift e hκ he s hs0 hs2 u).val n = (e u.val).val n := rfl

theorem toBase_lift (e : L2T L ≃ₜ V) (hκ : 0 < κ) (he : ExactModuli e hκ)
    (s : ℝ) (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (u : H02 L s) :
    toBase (L := L) s hs0 (lift e hκ he s hs0 hs2 u) = (e u.val).val := by
  apply lp.ext
  funext n
  rw [toBase_apply,lift_apply]

def restriction (e : L2T L ≃ₜ V) (hκ : 0 < κ) (he : ExactModuli e hκ)
    (s : ℝ) (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (u : H02 L s) : Target (L := L) V s hs0 :=
  ⟨lift e hκ he s hs0 hs2 u, by rw [toBase_lift]; exact (e u.val).property⟩

def baseInverse (e : L2T L ≃ₜ V) (s : ℝ) (hs : 0 ≤ s) (z : Target (L := L) V s hs) : L2T L :=
  e.symm ⟨toBase (L := L) s hs z.val, z.property⟩

theorem inverse_moduli (e : L2T L ≃ₜ V) (hκ : 0 < κ) (he : ExactModuli e hκ)
    (s : ℝ) (hs : 0 ≤ s) (z : Target (L := L) V s hs) (n : ℤ) :
    (QuantumNLS.RootIndexedMasses.masses hκ (baseInverse e s hs z)).1 n = ‖z.val.val n‖^2 := by
  rw [← he (baseInverse e s hs z) n]
  change ‖(e (e.symm ⟨toBase (L := L) s hs z.val,z.property⟩)).val n‖^2 = _
  rw [e.apply_symm_apply,toBase_apply]

theorem inverse_mem (e : L2T L ≃ₜ V) (hκ : 0 < κ) (he : ExactModuli e hκ)
    (s : ℝ) (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (z : Target (L := L) V s hs0) :
    ∃ u : H02 L s, u.val = baseInverse e s hs0 z := by
  apply ((QuantumNLS.TerraMultiRound79Characterization.closed_interval_characterization κ hκ _ s hs0 hs2).1).mpr
  apply ((QuantumNLS.TerraMultiRound79Characterization.closed_interval_characterization κ hκ _ s hs0 hs2).2).mpr
  simpa only [inverse_moduli e hκ he s hs0 z, def002, sobolevWeight, momentum, QuantumNLS.Fourier.freq]
    using z.val.summable

def inverse (e : L2T L ≃ₜ V) (hκ : 0 < κ) (he : ExactModuli e hκ)
    (s : ℝ) (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (z : Target (L := L) V s hs0) : H02 L s :=
  (inverse_mem e hκ he s hs0 hs2 z).choose

theorem inverse_val (e : L2T L ≃ₜ V) (hκ : 0 < κ) (he : ExactModuli e hκ)
    (s : ℝ) (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (z : Target (L := L) V s hs0) :
    (inverse e hκ he s hs0 hs2 z).val = baseInverse e s hs0 z :=
  (inverse_mem e hκ he s hs0 hs2 z).choose_spec

#print axioms toBase_apply
#print axioms toBase_lift
#print axioms inverse_moduli
#print axioms inverse_mem
#print axioms inverse_val
end QuantumNLS.Reg011SettingR48a

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Reg011SettingR48a." ||
        n.toString.startsWith "_private.QuantumNLS.Reg011SettingR48a." then
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
  Lean.logInfo m!"Round48 aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
