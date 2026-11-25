import QuantumNLS.Reg010LowEmbeddingMap
import QuantumNLS.Reg010LowBootstrap
import QuantumNLS.Reg010LowPrinted

/-! REG-010 STEP 2, low orders: embedding, unconditional one-third bootstrap,
and the all-L2 fractional moment criterion and identity. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace QuantumNLS.Reg010LowFinal
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.FreeLimit
open QuantumNLS.Reg010LowL4Space QuantumNLS.Reg010LowEmbeddingMap
variable {L : ℝ} [Fact (0 < L)]

/-- A finite higher physical moment alone supplies the native L4 field.
No independent lower moment or field regularity hypothesis is imposed. -/
theorem higher_moment_L4 (κ : ℝ) (hκ : 0 < κ) (u : L2T L)
    (s : ℝ) (hs : 1/3 ≤ s)
    (hm : Integrable (fun t : ℝ => |t|^(2*s)) (PhysicalQuantumMeasure.measure hκ u)) :
    ∃ v : L4T L, toL2 v = u := by
  obtain ⟨v,hv⟩ := QuantumNLS.Reg010LowBootstrap.higher_moment_one_third κ hκ u s hs hm
  exact ⟨embeddingH02 v,(embeddingH02_toL2 v).trans hv⟩

/-- Lowering Sobolev order preserves the physical L2 field exactly. -/
theorem H02_lower_val (s t : ℝ) (hst : s ≤ t) (u : H02 L t) :
    (H02.mono hst u).val = u.val :=
  fieldIncl_val (def002 L s) (def002 L t) zero_le_one (def002_le_of_le L hst) u

theorem higher_sobolev_L4 (s : ℝ) (hs : 1/3 ≤ s) (u : H02 L s) :
    ∃ v : L4T L, toL2 v = u.val := by
  let w : H02 L (1/3) := H02.mono hs u
  exact ⟨embeddingH02 w,(embeddingH02_toL2 w).trans (H02_lower_val (1/3) s hs u)⟩

/-- The printed low-order characterization on every physical L2 field. -/
theorem low_characterization (κ : ℝ) (hκ : 0 < κ) (u : L2T L)
    (s : ℝ) (hs : 0 < s) (hs' : s < 1) :
    Integrable (fun t : ℝ => |t|^(2*s)) (PhysicalQuantumMeasure.measure hκ u) ↔
      ∃ v : H02 L s, v.val = u := by
  by_cases hsmall : s < 1/2
  · exact QuantumNLS.Reg010LowBootstrap.low_characterization κ hκ u s hs hsmall
  · have hthird : 1/3 ≤ s := by linarith
    constructor
    · intro hm
      obtain ⟨v,hv⟩ := higher_moment_L4 κ hκ u s hthird hm
      rw [← hv] at hm ⊢
      exact (QuantumNLS.Reg010LowBootstrap.L4_characterization κ hκ v s hs hs').mp hm
    · rintro ⟨v,hv⟩
      obtain ⟨w,hw⟩ := higher_sobolev_L4 s hthird v
      have h := (QuantumNLS.Reg010LowBootstrap.L4_characterization κ hκ w s hs hs').mpr
        ⟨v,hw.symm⟩
      simpa only [hw,hv] using h

/-- Equivalence with the positive free Fourier moment on every L2 field. -/
theorem physical_free_finiteness (κ : ℝ) (hκ : 0 < κ) (u : L2T L)
    (s : ℝ) (hs : 0 < s) (hs' : s < 1) :
    Integrable (fun t : ℝ => |t|^(2*s)) (PhysicalQuantumMeasure.measure hκ u) ↔
      Integrable (fun t : ℝ => |t|^(2*s)) (freeMeasure L u) :=
  (low_characterization κ hκ u s hs hs').trans
    (QuantumNLS.Reg010LowFreeSobolev.free_power_integrable_iff_H02 u s hs).symm

/-- The same criterion in terra_multi's extended Sobolev-norm interface. -/
theorem low_characterization_hsq (κ : ℝ) (hκ : 0 < κ) (u : L2T L)
    (s : ℝ) (hs : 0 < s) (hs' : s < 1) :
    Integrable (fun t : ℝ => |t|^(2*s)) (PhysicalQuantumMeasure.measure hκ u) ↔
      QuantumNLS.RiccatiSobolevE1.hsq L s
        (fun n => QuantumNLS.Fourier.coeff L (u : AddCircle L → ℂ) n) ≠ ⊤ :=
  (physical_free_finiteness κ hκ u s hs hs').trans
    (QuantumNLS.Reg010LowFreeSobolev.free_power_integrable_iff_hsq u s hs)

/-- The literal printed fractional moment formula, with the frozen
continuous correction J and no extra field hypothesis. -/
theorem fractional_identity (κ : ℝ) (hκ : 0 < κ) (u : L2T L)
    (s : ℝ) (hs : 0 < s) (hs' : s < 1)
    (hm : Integrable (fun t : ℝ => |t|^(2*s)) (PhysicalQuantumMeasure.measure hκ u)) :
    (∫ t : ℝ, |t|^(2*s) ∂PhysicalQuantumMeasure.measure hκ u) =
      (∫ t : ℝ, |t|^(2*s) ∂freeMeasure L u) + QuantumNLS.Reg010LowCorrection.J κ hκ s u := by
  by_cases hsmall : s < 1/2
  · exact QuantumNLS.Reg010LowPrinted.all_L2_fractional_identity κ hκ u s hs hsmall hm
  · obtain ⟨v,hv⟩ := higher_moment_L4 κ hκ u s (by linarith) hm
    rw [← hv] at hm ⊢
    exact QuantumNLS.Reg010LowPrinted.L4_fractional_identity κ hκ v s hs hs' hm

/-- Exact real free moment/Fourier sum, with the standard total-integral
convention when it is not finite. Finiteness is proved separately above. -/
theorem free_power_integral (u : L2T L) (s : ℝ) :
    (∫ t : ℝ, |t|^(2*s) ∂freeMeasure L u) =
      ∑' n : ℤ, |QuantumNLS.Fourier.freq L n|^(2*s) *
        ‖QuantumNLS.Fourier.fourierL2 L u n‖^2 := by
  unfold freeMeasure
  rw [integral_sum_dirac (fun n => ENNReal.ofReal_ne_top)]
  apply tsum_congr
  intro n
  rw [ENNReal.toReal_ofReal (sq_nonneg _)]
  simp only [smul_eq_mul,QuantumNLS.Fourier.freq,QuantumNLS.Fourier.fourierL2_apply]
  ring

/-- The source formula with Q_s written literally as the Fourier sum. -/
theorem fractional_identity_fourier (κ : ℝ) (hκ : 0 < κ) (u : L2T L)
    (s : ℝ) (hs : 0 < s) (hs' : s < 1)
    (hm : Integrable (fun t : ℝ => |t|^(2*s)) (PhysicalQuantumMeasure.measure hκ u)) :
    (∫ t : ℝ, |t|^(2*s) ∂PhysicalQuantumMeasure.measure hκ u) =
      (∑' n : ℤ, |QuantumNLS.Fourier.freq L n|^(2*s) *
        ‖QuantumNLS.Fourier.fourierL2 L u n‖^2) + QuantumNLS.Reg010LowCorrection.J κ hκ s u := by
  rw [← free_power_integral u s]
  exact fractional_identity κ hκ u s hs hs' hm

#print axioms free_power_integral
#print axioms fractional_identity_fourier
#print axioms low_characterization_hsq
#print axioms physical_free_finiteness
#print axioms higher_moment_L4
#print axioms H02_lower_val
#print axioms higher_sobolev_L4
#print axioms low_characterization
#print axioms fractional_identity
end QuantumNLS.Reg010LowFinal

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Reg010LowFinal." ||
        n.toString.startsWith "_private.QuantumNLS.Reg010LowFinal." then
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
  Lean.logInfo m!"Round46 aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
