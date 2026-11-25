import QuantumNLS.L1SpatialTransfer

/-! Parameter continuity for the actual L1 Volterra series, using a common
integrable coefficient majorant on the parameter set. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set
namespace QuantumNLS.L1TransferParameter
open QuantumNLS.LinearFundamental QuantumNLS.L1SpatialTransfer
variable {E X : Type*} [NormedRing E] [NormedAlgebra ℝ E] [CompleteSpace E]
variable {A : X → ℝ → E} {s : Set X} {L : ℝ} {g : ℝ → ℝ}

/-- A common integrable majorant gives a common factorial Dyson estimate. -/
theorem norm_dyson_le (hL : 0 ≤ L)
    (hA : ∀ z ∈ s, IntervalIntegrable (A z) volume 0 L)
    (hg : IntervalIntegrable g volume 0 L)
    (hb : ∀ z ∈ s, ∀ t ∈ Icc 0 L, ‖A z t‖ ≤ g t)
    {z : X} (hz : z ∈ s) (n : ℕ) {x : ℝ} (hx : x ∈ Icc 0 L) :
    ‖dyson (A z) n x‖ ≤
      ‖(1 : E)‖ * (∫ t in (0 : ℝ)..L, g t) ^ n / (n.factorial : ℝ) := by
  have hnorm : (∫ t in (0 : ℝ)..L, ‖A z t‖) ≤ ∫ t in (0 : ℝ)..L, g t :=
    intervalIntegral.integral_mono_on hL (hA z hz).norm hg (hb z hz)
  have hn0 : 0 ≤ ∫ t in (0 : ℝ)..L, ‖A z t‖ :=
    intervalIntegral.integral_nonneg hL (fun t _ => norm_nonneg _)
  have he := (uniform_dyson_bound hL (hA z hz)).2 n x hx
  exact he.trans (by gcongr)

variable [TopologicalSpace X] [FirstCountableTopology X]

/-- Parameter continuity of every Dyson term, even for merely measurable profiles. -/
theorem continuousOn_dyson (hL : 0 ≤ L)
    (hA : ∀ z ∈ s, IntervalIntegrable (A z) volume 0 L)
    (hg : IntervalIntegrable g volume 0 L)
    (hb : ∀ z ∈ s, ∀ t ∈ Icc 0 L, ‖A z t‖ ≤ g t)
    (hc : ∀ t ∈ Icc 0 L, ContinuousOn (fun z => A z t) s) :
    ∀ n, ∀ x ∈ Icc 0 L, ContinuousOn (fun z => dyson (A z) n x) s := by
  intro n
  induction n with
  | zero => intro x hx; exact continuousOn_const
  | succ n ih =>
    intro x hx
    have hsub : uIcc (0 : ℝ) x ⊆ uIcc (0 : ℝ) L := by
      rw [uIcc_of_le hx.1, uIcc_of_le hL]
      exact Icc_subset_Icc_right hx.2
    let C : ℝ := ‖(1 : E)‖ * (∫ t in (0 : ℝ)..L, g t) ^ n / (n.factorial : ℝ)
    have hi : Integrable (fun t => g t * C) (volume.restrict (Ioc 0 x)) := by
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hx.1).mp
        ((hg.mono_set hsub).mul_const C)
    have hd : ContinuousOn (fun z => ∫ t in Ioc (0 : ℝ) x,
        A z t * dyson (A z) n t) s := by
      apply continuousOn_of_dominated
      · intro z hz
        exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hx.1).mp
          ((integrable_dyson_product (hA z hz) n).mono_set hsub)).aestronglyMeasurable
      · intro z hz
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        have htL : t ∈ Icc 0 L := ⟨ht.1.le, ht.2.trans hx.2⟩
        exact (norm_mul_le _ _).trans (mul_le_mul
          (hb z hz t htL) (norm_dyson_le hL hA hg hb hz n htL)
          (norm_nonneg _) ((norm_nonneg _).trans (hb z hz t htL)))
      · exact hi
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        have htL : t ∈ Icc 0 L := ⟨ht.1.le, ht.2.trans hx.2⟩
        exact (hc t htL).mul (ih t htL)
    simpa only [dyson, intervalIntegral.integral_of_le hx.1] using hd

/-- Continuity of the summed L1 transfer in the spectral parameter. -/
theorem continuousOn_transfer (hL : 0 ≤ L)
    (hA : ∀ z ∈ s, IntervalIntegrable (A z) volume 0 L)
    (hg : IntervalIntegrable g volume 0 L)
    (hb : ∀ z ∈ s, ∀ t ∈ Icc 0 L, ‖A z t‖ ≤ g t)
    (hc : ∀ t ∈ Icc 0 L, ContinuousOn (fun z => A z t) s)
    {x : ℝ} (hx : x ∈ Icc 0 L) :
    ContinuousOn (fun z => transfer (A z) x) s := by
  apply continuousOn_tsum (fun n => continuousOn_dyson hL hA hg hb hc n x hx)
    (show Summable (fun n : ℕ =>
      ‖(1 : E)‖ * (∫ t in (0 : ℝ)..L, g t) ^ n / (n.factorial : ℝ)) from by
        simpa only [mul_div_assoc] using
          (Real.summable_pow_div_factorial (∫ t in (0 : ℝ)..L, g t)).mul_left ‖(1 : E)‖)
  exact fun n z hz => norm_dyson_le hL hA hg hb hz n hx

end QuantumNLS.L1TransferParameter

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.L1TransferParameter.norm_dyson_le
#print axioms QuantumNLS.L1TransferParameter.continuousOn_dyson
#print axioms QuantumNLS.L1TransferParameter.continuousOn_transfer

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.L1TransferParameter." then
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
