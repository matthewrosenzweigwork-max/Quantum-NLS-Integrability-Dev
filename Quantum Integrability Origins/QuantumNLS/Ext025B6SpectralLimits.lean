import QuantumNLS.Ext025B6GraphCore

/-! GP-13/GP-08, R-2E4C2F4E: actual bounded spectral-coordinate cutoffs
converge to the unbounded Bethe charge on its exact maximal domain. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Filter Topology
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.Ext025B6SpectralLimits
open BetheSpectralCharges BetheCoefficientTransform PhysicalTensor BetheLabels BoundedBetheTransfer
variable {L : ℝ} [Fact (0 < L)] {N : ℕ}
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def clipped (a : MArr N → ℝ) (n : ℕ) (m : MArr N) : ℂ :=
  if |a m| ≤ n then (a m : ℂ) else 0

theorem clipped_bound (a : MArr N → ℝ) (n : ℕ) (m : MArr N) :
    ‖clipped a n m‖ ≤ n := by
  unfold clipped
  split_ifs with h
  · simpa only [Complex.norm_real,Real.norm_eq_abs] using h
  · simp

def boundedCutoff (b : BetheBasis L N) (a : MArr N → ℝ) (n : ℕ) : HN L N →L[ℂ] HN L N :=
  Ext025SCalculus.bounded b (clipped a n) n (Nat.cast_nonneg n) (clipped_bound a n)

/-- The bounded spectral integral is exactly the symbol-support projection
of the actual unbounded charge, not an operator assumed to have that action. -/
theorem cutoff_eq_projection (b : BetheBasis L N) (a : MArr N → ℝ) (n : ℕ)
    (v : HN L N) (hv : v ∈ (multiplier b a).domain) :
    boundedCutoff b a n v =
      projection b {m | |a m| ≤ n} (multiplier b a ⟨v,hv⟩) := by
  have hc (m : MArr N) : b.repr (multiplier b a ⟨v,hv⟩) m = (a m : ℂ) * b.repr v m := by
    simpa only [HilbertBasis.repr_apply_apply] using multiplier_coord b a ⟨v,hv⟩ m
  apply b.repr.injective
  ext m
  rw [boundedCutoff,Ext025SCalculus.bounded_coord,projection_coord,hc]
  simp [clipped,ite_mul]

/-- Literal square-error density and its fixed weighted-coefficient majorant. -/
theorem cutoff_square_error (b : BetheBasis L N) (a : MArr N → ℝ) (n : ℕ)
    (v : HN L N) (hv : v ∈ (multiplier b a).domain) :
    ‖multiplier b a ⟨v,hv⟩ - boundedCutoff b a n v‖^2 =
      ∑' m, if |a m| ≤ n then 0 else |a m|^2 * ‖b.repr v m‖^2 := by
  rw [cutoff_eq_projection b a n v hv,Ext025B6GraphCore.vector_error]
  apply tsum_congr
  intro m
  have hc : b.repr (multiplier b a ⟨v,hv⟩) m = (a m : ℂ) * b.repr v m := by
    simpa only [HilbertBasis.repr_apply_apply] using multiplier_coord b a ⟨v,hv⟩ m
  simp only [Set.mem_ofPred_eq,hc,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs]

theorem cutoff_strong (b : BetheBasis L N) (a : MArr N → ℝ)
    (v : HN L N) (hv : v ∈ (multiplier b a).domain) :
    Tendsto (fun n => boundedCutoff b a n v) atTop (𝓝 (multiplier b a ⟨v,hv⟩)) := by
  have hs : Summable (fun m => |a m|^2 * ‖b.repr v m‖^2) := by
    simpa only [HilbertBasis.repr_apply_apply] using (mem_domain b a v).mp hv
  have ht := tendsto_tsum_of_dominated_convergence (𝓕 := (atTop : Filter ℕ)) hs
    (f := fun (n : ℕ) m => if |a m| ≤ (n : ℝ) then 0 else |a m|^2 * ‖b.repr v m‖^2)
    (g := fun _ => (0 : ℝ))
    (fun m => by
      have he : ∀ᶠ n : ℕ in atTop, |a m| ≤ (n : ℝ) :=
        tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop |a m|)
      exact tendsto_const_nhds.congr' (he.mono fun n hn => by simp [hn]))
    (Eventually.of_forall fun n m => by
      have hp : 0 ≤ |a m|^2 * ‖b.repr v m‖^2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
      split_ifs
      · simpa only [norm_zero] using hp
      · rw [Real.norm_eq_abs,abs_of_nonneg hp])
  have hh : Tendsto (fun n => ‖multiplier b a ⟨v,hv⟩ - boundedCutoff b a n v‖^2) atTop (𝓝 0) := by
    have he : (fun n => ‖multiplier b a ⟨v,hv⟩ - boundedCutoff b a n v‖^2) =
        (fun n : ℕ => ∑' m, if |a m| ≤ (n : ℝ) then 0 else |a m|^2 * ‖b.repr v m‖^2) :=
      funext (fun n => cutoff_square_error b a n v hv)
    rw [he]
    simpa only [tsum_zero] using ht
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hh
  have hnorm : Tendsto (fun n => ‖multiplier b a ⟨v,hv⟩ - boundedCutoff b a n v‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_zero,Real.sqrt_sq (norm_nonneg _)] using hroot
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact hnorm.congr' (Eventually.of_forall fun n => norm_sub_rev _ _)

end QuantumNLS.Ext025B6SpectralLimits

#print axioms QuantumNLS.Ext025B6SpectralLimits.clipped
#print axioms QuantumNLS.Ext025B6SpectralLimits.clipped_bound
#print axioms QuantumNLS.Ext025B6SpectralLimits.boundedCutoff
#print axioms QuantumNLS.Ext025B6SpectralLimits.cutoff_eq_projection
#print axioms QuantumNLS.Ext025B6SpectralLimits.cutoff_square_error
#print axioms QuantumNLS.Ext025B6SpectralLimits.cutoff_strong

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext025B6SpectralLimits." then
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
  Lean.logInfo m!"Ext025B6SpectralLimits audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
