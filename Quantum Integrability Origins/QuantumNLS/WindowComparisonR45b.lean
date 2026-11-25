import QuantumNLS.WindowRadialR45b
import QuantumNLS.WindowTorusR45b
import QuantumNLS.WindowRateEstimateR44b

/-! Quantitative finite-family comparison with multipliers DERIVED from the
actual scalar differentials. The conclusion is a support theorem, not the
source-final physical-hierarchy identification. All constants precede the cutoff. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.WindowInterpolationR44b QuantumNLS.WindowPhaseR44b
open QuantumNLS.WindowRateEstimateR44b QuantumNLS.WindowRadialR45b
open QuantumNLS.WindowGradientIdentificationR44b
namespace QuantumNLS.WindowComparisonR45b
variable {W : PosWeight}

def lowerCLM (W : PosWeight) (hW : ∀ j, 1 ≤ W.w j) : WSeq W →L[ℝ] WSeq unitWeight :=
  LinearMap.mkContinuous
    { toFun := lower W hW
      map_add' := fun _ _ => WSeq.ext rfl
      map_smul' := fun _ _ => WSeq.ext rfl }
    1 (fun z => by simpa using norm_lower_le W hW z)

/-- Scalar differential comparison implies the reciprocal-weight error for
the real multipliers of the two actual invariant functions. -/
theorem frequency_error (W : PosWeight) (F G : WSeq W → ℝ) (z : WSeq W)
    (hF : DifferentiableAt ℝ F z) (hG : DifferentiableAt ℝ G z)
    (hiF : ∀ α y, F (rotate α y) = F y) (hiG : ∀ α y, G (rotate α y) = G y) :
    ∃ e : WSeq (reciprocal W),
      (∀ j, e.val j = ((frequency F z j-frequency G z j : ℝ) : ℂ)*z.val j) ∧
      ‖e‖ ≤ ‖fderiv ℝ F z-fderiv ℝ G z‖ := by
  obtain ⟨e,he,hn⟩ := coordinate_gradient_error W (fderiv ℝ F z) (fderiv ℝ G z)
    (fun j => (frequency F z j : ℂ)*z.val j) (fun j => (frequency G z j : ℂ)*z.val j)
    (coordinate_gradient hF hiF) (coordinate_gradient hG hiG)
  refine ⟨e,fun j => ?_,hn⟩
  rw [he j]
  push_cast
  ring

/-- The signed joint angle in the DEF-015 convention. -/
def angle {ι : Type*} (S : Finset ι) (F : ι → WSeq W → ℝ)
    (t : ι → ℝ) (z : WSeq W) (j : ℤ) : ℝ := -∑ r ∈ S, t r*frequency (F r) z j

/-- Fixed compact classes and fixed time boxes give the quarter-power rate.
Only the scalar differential estimate is a quantitative hypothesis; no
frequency division estimate or trajectory error is supplied. -/
theorem uniform_comparison {ι : Type*} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (W : PosWeight) (hW : ∀ j, 1 ≤ W.w j)
    {K : Set (WSeq W)} (hK : IsCompact K)
    (f : WSeq unitWeight → E) (hf : ContDiff ℝ 1 f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (S : Finset ι) (F G : ι → WSeq W → ℝ)
      (T C : ι → ℝ) (B : ℝ),
      (∀ r, ∀ z ∈ K, DifferentiableAt ℝ (F r) z) →
      (∀ r, ∀ z ∈ K, DifferentiableAt ℝ (G r) z) →
      (∀ r α y, F r (rotate α y) = F r y) →
      (∀ r α y, G r (rotate α y) = G r y) →
      (∀ r ∈ S, 0 ≤ C r) → (∀ z ∈ K, ‖z‖ ≤ B) →
      ∀ (a : ℝ), 0 < a →
      (∀ r ∈ S, ∀ z ∈ K, ‖fderiv ℝ (F r) z-fderiv ℝ (G r) z‖ ≤ C r*a^(-(1/2 : ℝ))) →
      ∀ z ∈ K, ∀ t : ι → ℝ, (∀ r ∈ S, |t r| ≤ T r) →
      ‖f (lower W hW (rotate (angle S F t z) z))-
        f (lower W hW (rotate (angle S G t z) z))‖ ≤
        (M*Real.sqrt ((∑ r ∈ S, T r*C r)*(2*B)))*a^(-(1/4 : ℝ)) := by
  classical
  let K₀ := lower W hW '' WindowTorusR45b.hull W K
  have hK₀ : IsCompact K₀ :=
    (WindowTorusR45b.isCompact_hull W hK).image (lowerCLM W hW).continuous
  obtain ⟨M,hM,hbound⟩ := uniform_physical_rate W hW hK₀ f hf
  refine ⟨M,hM,?_⟩
  intro S F G T C B hF hG hiF hiG hC hB a ha hscalar z hz t ht
  have herr : ∀ r, ∃ e : WSeq (reciprocal W),
      (∀ j, e.val j = ((frequency (F r) z j-frequency (G r) z j : ℝ) : ℂ)*z.val j) ∧
      ‖e‖ ≤ ‖fderiv ℝ (F r) z-fderiv ℝ (G r) z‖ := fun r =>
    frequency_error W (F r) (G r) z (hF r z hz) (hG r z hz) (hiF r) (hiG r)
  choose err herr hnorm using herr
  let δ : WSeq (reciprocal W) := -∑ r ∈ S, t r • err r
  have hδ : ∀ j, δ.val j = (((angle S F t z j-angle S G t z j : ℝ) : ℂ)*z.val j) := by
    intro j
    change -(∑ r ∈ S, t r • err r).val j = _
    have hs : ∀ U : Finset ι, (∑ r ∈ U, t r • err r).val j =
        ∑ r ∈ U, (t r : ℂ)*(err r).val j := by
      intro U
      induction U using Finset.induction_on with
      | empty => simp
      | @insert r S hr ih => simp [hr,real_smul_val,ih]
    rw [hs S]
    simp only [herr,← mul_assoc]
    rw [← Finset.sum_mul]
    simp only [angle]
    push_cast
    simp only [mul_sub,Finset.sum_sub_distrib]
    ring
  have hnormδ : ‖δ‖ ≤ (∑ r ∈ S, T r*C r)*a^(-(1/2 : ℝ)) := by
    rw [show ‖δ‖ = ‖∑ r ∈ S, t r • err r‖ from norm_neg _]
    exact box_error_norm S W t T C err ha.le hC ht
      (fun r hr => (hnorm r).trans (hscalar r hr z hz))
  have hA : 0 ≤ ∑ r ∈ S, T r*C r := Finset.sum_nonneg fun r hr =>
    mul_nonneg ((abs_nonneg (t r)).trans (ht r hr)) (hC r hr)
  exact hbound B z (hB z hz) (angle S F t z) (angle S G t z) δ hδ ha hA hnormδ
    ⟨_,WindowTorusR45b.rotate_mem_hull W hz _,rfl⟩
    ⟨_,WindowTorusR45b.rotate_mem_hull W hz _,rfl⟩

end QuantumNLS.WindowComparisonR45b
#print axioms QuantumNLS.WindowComparisonR45b.frequency_error
#print axioms QuantumNLS.WindowComparisonR45b.uniform_comparison

-- Recursive type/value audit of every own declaration, including generated declarations.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.WindowComparisonR45b." ||
        n.toString.startsWith "_private.QuantumNLS.WindowComparisonR45b." then
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
  Lean.logInfo m!"R45b aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only."
