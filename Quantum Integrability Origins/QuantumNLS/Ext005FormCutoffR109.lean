import QuantumNLS.Ext005FormScaleR109
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-! R109: finite-sector regularization on the physical form scale.
The cutoffs converge in Q(A), and their bounded-form pairing error vanishes
after time integration under an essential uniform form bound. The weak
equation's chain rule and the physical time-dependent form are not assumed
or proved by these approximation lemmas. -/
noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace Topology
namespace QuantumNLS.Ext005FormCutoffR109
open Ext025B3PhysicalSectors Ext005Moments Ext005MomentEnergyR108
open Ext005FormScaleR109 BetheCoefficientTransform Filter MeasureTheory
variable {L : ℝ} [Fact (0 < L)]

/-- Orthogonal projection onto sectors 0,...,N-1. The sectors themselves
can be infinite dimensional; no finite-rank assertion is made. -/
def cutoff (N : ℕ) : Fock L →L[ℂ] Fock L :=
  ∑ n ∈ Finset.range N, projection L n

theorem cutoff_sum (N : ℕ) (x : Fock L) :
    cutoff N x = ∑ n ∈ Finset.range N, projection L n x := by
  simp only [cutoff, sum_apply]

@[simp] theorem cutoff_apply (N : ℕ) (x : Fock L) (n : ℕ) :
    cutoff N x n = if n < N then x n else 0 := by
  rw [cutoff_sum, lp.coeFn_sum, Finset.sum_apply]
  by_cases hn : n < N
  · rw [ite_eq_left hn]
    rw [Finset.sum_eq_single n]
    · exact projection_same L n x
    · intro i _ hin
      exact projection_other L i n (Ne.symm hin) x
    · intro h
      exact False.elim (h (Finset.mem_range.mpr hn))
  · rw [ite_eq_right hn]
    apply Finset.sum_eq_zero
    intro i hi
    apply projection_other
    have hi' := Finset.mem_range.mp hi
    omega

theorem cutoff_norm_le (N : ℕ) (x : Fock L) : ‖cutoff N x‖ ≤ ‖x‖ := by
  apply lp.norm_mono (by norm_num)
  intro n
  rw [cutoff_apply]
  split_ifs <;> simp

theorem cutoff_mem (j N : ℕ) (x : Fock L) :
    cutoff N x ∈ momentDomain (L := L) j := by
  rw [cutoff_sum]
  exact Submodule.sum_mem _ (fun n _ => sector_mem_momentDomain j n x)

theorem cutoff_symmetric (N : ℕ) (x y : Fock L) :
    ⟪cutoff N x, y⟫_ℂ = ⟪x, cutoff N y⟫_ℂ := by
  simp only [cutoff_sum, inner_sum, sum_inner]
  apply Finset.sum_congr rfl
  intro n _
  rw [← ContinuousLinearMap.adjoint_inner_left, projection_selfadjoint]

theorem cutoff_tendsto (x : Fock L) :
    Tendsto (fun N => cutoff N x) atTop (𝓝 x) := by
  simpa only [cutoff_sum] using (projection_hasSum L x).tendsto_sum_nat

theorem root_cutoff (j N : ℕ) (x : momentDomain (L := L) j) :
    momentRoot j ⟨cutoff N x.val, cutoff_mem j N x.val⟩ =
      cutoff N (momentRoot j x) := by
  apply Subtype.ext
  funext n
  change (Real.sqrt (momentWeight j n) : ℂ) • (cutoff N x.val n) =
    cutoff N (momentRoot j x) n
  simp only [cutoff_apply]
  split_ifs
  · rfl
  · exact smul_zero _

/-- Form-norm convergence is proved on the maximal physical form domain. -/
theorem root_cutoff_tendsto (j : ℕ) (x : momentDomain (L := L) j) :
    Tendsto (fun N => momentRoot j ⟨cutoff N x.val, cutoff_mem j N x.val⟩)
      atTop (𝓝 (momentRoot j x)) := by
  simpa only [root_cutoff] using cutoff_tendsto (momentRoot j x)

theorem cutoff_energy_le (j N : ℕ) (x : momentDomain (L := L) j) :
    energy j (cutoff N x.val) ≤ energy j x.val := by
  rw [energy_eq_root j ⟨cutoff N x.val, cutoff_mem j N x.val⟩,
    energy_eq_root j x]
  have h : ‖momentRoot j ⟨cutoff N x.val, cutoff_mem j N x.val⟩‖ ≤
      ‖momentRoot j x‖ := by
    exact (congrArg norm (root_cutoff j N x)).le.trans (cutoff_norm_le N _)
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- No moment energy is lost in the increasing cutoff limit. -/
theorem cutoff_energy_tendsto (j : ℕ) (x : momentDomain (L := L) j) :
    Tendsto (fun N => energy j (cutoff N x.val)) atTop (𝓝 (energy j x.val)) := by
  have h := (root_cutoff_tendsto j x).norm.pow 2
  have he : (fun N => energy j (cutoff N x.val)) =
      (fun N => ‖momentRoot j ⟨cutoff N x.val, cutoff_mem j N x.val⟩‖ ^ 2) :=
    funext (fun N => energy_eq_root j ⟨cutoff N x.val, cutoff_mem j N x.val⟩)
  rw [he]
  exact (energy_eq_root j x).symm ▸ h

/-- A bounded operator giving the root of a finite-sector truncation. -/
def rootCutoff (j N : ℕ) : Fock L →L[ℂ] Fock L :=
  ∑ n ∈ Finset.range N, (Real.sqrt (momentWeight j n) : ℂ) • projection L n

theorem rootCutoff_eq (j N : ℕ) (x : momentDomain (L := L) j) :
    rootCutoff j N x.val = cutoff N (momentRoot j x) := by
  simp only [rootCutoff, sum_apply, smul_apply, cutoff_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Subtype.ext
  funext n
  change (Real.sqrt (momentWeight j i) : ℂ) • (projection L i x.val n) =
    projection L i (momentRoot j x) n
  by_cases hn : n = i
  · subst n
    simp only [projection_same, momentRoot_apply]
  · rw [projection_other L i n hn, projection_other L i n hn, smul_zero]

/-- Zero off the form domain; only its a.e. domain values are used. -/
def rootLift (j : ℕ) (x : Fock L) : Fock L := by
  classical
  exact if hx : x ∈ momentDomain (L := L) j then momentRoot j ⟨x, hx⟩ else 0

theorem rootLift_eq (j : ℕ) (x : Fock L) (hx : x ∈ momentDomain (L := L) j) :
    rootLift j x = momentRoot j ⟨x, hx⟩ := by
  classical
  simp only [rootLift, dite_eq_left hx]

/-- Norm measurability of the physical curve suffices for a strongly
measurable root-coordinate lift, despite the root being unbounded. -/
theorem rootLift_aestronglyMeasurable (j : ℕ) (μ : Measure ℝ) (x : ℝ → Fock L)
    (hx : AEStronglyMeasurable x μ)
    (hd : ∀ᵐ t ∂μ, x t ∈ momentDomain (L := L) j) :
    AEStronglyMeasurable (fun t => rootLift j (x t)) μ := by
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun N t => rootCutoff j N (x t))
  · intro N
    exact (rootCutoff j N).continuous.comp_aestronglyMeasurable hx
  · filter_upwards [hd] with t ht
    have h := cutoff_tendsto (momentRoot j ⟨x t, ht⟩)
    have he : (fun N => rootCutoff j N (x t)) =
        (fun N => cutoff N (momentRoot j ⟨x t, ht⟩)) :=
      funext (fun N => rootCutoff_eq j N ⟨x t, ht⟩)
    rw [he, rootLift_eq j (x t) ht]
    exact h

/-- The D3 essential moment condition yields a Bochner-measurable bounded
coordinate lift, with the same bound, whenever the physical curve is
strongly measurable. In particular norm-continuous curves qualify. -/
theorem energyBounded_measurable_coordinates (j : ℕ) (I : Set ℝ)
    (x : ℝ → Fock L) (hx : AEStronglyMeasurable x (volume.restrict I))
    (hb : EnergyBounded j I x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ u : ℝ → FormSpace (L := L) j,
      AEStronglyMeasurable u (volume.restrict I) ∧
      ∀ᵐ t ∂volume.restrict I, embedding j (u t) = x t ∧ ‖u t‖ ^ 2 ≤ C := by
  obtain ⟨C, hC, h⟩ := hb
  refine ⟨C, hC, fun t => rootLift j (x t),
    rootLift_aestronglyMeasurable j _ x hx (h.mono fun _ ht => ht.1), h.mono ?_⟩
  intro t ht
  have he := rootLift_eq j (x t) ht.1
  exact ⟨(congrArg (embedding j) he).trans (embedding_root j ⟨x t, ht.1⟩),
    (congrArg (fun z : Fock L => ‖z‖ ^ 2) he).le.trans
      ((energy_eq_root j ⟨x t, ht.1⟩).symm.le.trans ht.2)⟩

/-- Error from testing a bounded form against a finite-sector cutoff in
square-root coordinates. No weak-solution norm derivative is postulated. -/
def pairingError (N : ℕ) (K : Fock L →L[ℂ] Fock L) (u : Fock L) : ℂ :=
  ⟪cutoff N u, K u⟫_ℂ - ⟪u, K u⟫_ℂ

theorem pairingError_bound (N : ℕ) (K : Fock L →L[ℂ] Fock L) (u : Fock L) :
    ‖pairingError N K u‖ ≤ 2 * ‖K‖ * ‖u‖ ^ 2 := by
  have h1 := norm_inner_le_norm (𝕜 := ℂ) (cutoff N u) (K u)
  have h2 := norm_inner_le_norm (𝕜 := ℂ) u (K u)
  have h3 := ContinuousLinearMap.le_opNorm K u
  have h4 := cutoff_norm_le N u
  have h5 := norm_sub_le ⟪cutoff N u, K u⟫_ℂ ⟪u, K u⟫_ℂ
  change ‖pairingError N K u‖ ≤ _ at h5
  calc
    _ ≤ ‖cutoff N u‖ * ‖K u‖ + ‖u‖ * ‖K u‖ := h5.trans (add_le_add h1 h2)
    _ ≤ ‖u‖ * (‖K‖ * ‖u‖) + ‖u‖ * (‖K‖ * ‖u‖) := by gcongr
    _ = _ := by ring

theorem pairingError_tendsto (K : Fock L →L[ℂ] Fock L) (u : Fock L) :
    Tendsto (fun N => pairingError N K u) atTop (𝓝 0) := by
  have h : Tendsto (fun N => ⟪cutoff N u, K u⟫_ℂ - ⟪u, K u⟫_ℂ) atTop
      (𝓝 (⟪u, K u⟫_ℂ - ⟪u, K u⟫_ℂ)) :=
    ((cutoff_tendsto u).inner tendsto_const_nhds).sub tendsto_const_nhds
  simpa only [pairingError, sub_self] using h

/-- On a finite time measure, the cutoff form error tends to zero in the
integral under the D3 type of essential uniform form-norm bound. This does
not infer the weak-energy identity from the weak equation. -/
theorem integral_pairingError_tendsto (μ : Measure ℝ) [IsFiniteMeasure μ]
    (u : ℝ → Fock L) (K : ℝ → Fock L →L[ℂ] Fock L) (C M : ℝ)
    (hM : 0 ≤ M) (hu : AEStronglyMeasurable u μ)
    (hK : AEStronglyMeasurable K μ)
    (hb : ∀ᵐ t ∂μ, ‖u t‖ ^ 2 ≤ C ∧ ‖K t‖ ≤ M) :
    Tendsto (fun N => ∫ t, pairingError N (K t) (u t) ∂μ) atTop (𝓝 0) := by
  have happ : Continuous (fun p : (Fock L →L[ℂ] Fock L) × Fock L => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hku : AEStronglyMeasurable (fun t => K t (u t)) μ :=
    happ.comp_aestronglyMeasurable (hK.prodMk hu)
  have hm (N : ℕ) : AEStronglyMeasurable (fun t => pairingError N (K t) (u t)) μ :=
    ((cutoff N).continuous.comp_aestronglyMeasurable hu).inner hku |>.sub (hu.inner hku)
  have hd (N : ℕ) : ∀ᵐ t ∂μ, ‖pairingError N (K t) (u t)‖ ≤ 2 * M * C := by
    filter_upwards [hb] with t ht
    exact (pairingError_bound N (K t) (u t)).trans (by
      nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sq_nonneg ‖u t‖),
        mul_nonneg hM (sub_nonneg.mpr ht.1)])
  have h := tendsto_integral_of_dominated_convergence (fun _ : ℝ => 2 * M * C)
    hm (integrable_const _) hd (Eventually.of_forall fun t => pairingError_tendsto (K t) (u t))
  simpa only [integral_zero] using h

end QuantumNLS.Ext005FormCutoffR109
#print axioms QuantumNLS.Ext005FormCutoffR109.root_cutoff_tendsto
#print axioms QuantumNLS.Ext005FormCutoffR109.cutoff_energy_tendsto
#print axioms QuantumNLS.Ext005FormCutoffR109.energyBounded_measurable_coordinates
#print axioms QuantumNLS.Ext005FormCutoffR109.integral_pairingError_tendsto

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005FormCutoffR109." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005FormCutoffR109." then
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
  Lean.logInfo m!"R109 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
