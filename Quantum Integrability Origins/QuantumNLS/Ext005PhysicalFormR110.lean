import QuantumNLS.Ext005CutoffChainR110

/-! R110: applying the proved distributional chain rule in the complete
physical moment/antidual scale. A symmetric bounded form K is an explicit
coefficient hypothesis; it is not identified with the factorial Hessian.
The weak equation is tested in the antidual. Cutoff identities and norm
conservation below are conclusions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 80000
open scoped InnerProductSpace Topology ContDiff
open MeasureTheory Set Filter Function
namespace QuantumNLS.Ext005PhysicalFormR110
open Ext025B3PhysicalSectors Ext005Moments Ext005MomentEnergyR108
open Ext005FormScaleR109 Ext005FormCutoffR109 Ext005CutoffChainR110
open BetheCoefficientTransform
variable {L : ℝ} [Fact (0 < L)]
local instance : NormedSpace ℝ (Fock L) := NormedSpace.restrictScalars ℝ ℂ (Fock L)
local instance : InnerProductSpace ℝ (Fock L) := InnerProductSpace.complexToReal

/-- Root-coordinate antidual forcing for i x'=H x. -/
def force (K : ℝ → Fock L →L[ℂ] Fock L) (u : ℝ → Fock L) (t : ℝ) : Fock L :=
  (-Complex.I) • (K t (u t))

theorem force_norm (K : ℝ → Fock L →L[ℂ] Fock L) (u : ℝ → Fock L) (t : ℝ) :
    ‖force K u t‖ = ‖K t (u t)‖ := by simp [force, norm_smul]

theorem force_measurable (K : ℝ → Fock L →L[ℂ] Fock L) (u : ℝ → Fock L)
    (hK : AEStronglyMeasurable K volume) (hu : AEStronglyMeasurable u volume) :
    AEStronglyMeasurable (force K u) volume := by
  have hc : Continuous (fun p : (Fock L →L[ℂ] Fock L) × Fock L => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  exact (hc.comp_aestronglyMeasurable (hK.prodMk hu)).const_smul (-Complex.I)

/-- Local essential bounds imply local Bochner integrability. -/
theorem locallyIntegrable_of_interval_bounds (g : ℝ → Fock L)
    (hg : AEStronglyMeasurable g volume)
    (hb : ∀ a b : ℝ, ∃ M : ℝ, ∀ᵐ t, t ∈ uIcc a b → ‖g t‖ ≤ M) :
    LocallyIntegrable g volume := by
  intro t
  obtain ⟨M, hM⟩ := hb (t - 1) (t + 1)
  have : IsFiniteMeasure (volume.restrict (uIcc (t - 1) (t + 1))) := ⟨by simp [uIcc]⟩
  refine ⟨uIcc (t - 1) (t + 1), ?_, hg.restrict, ?_⟩
  · rw [uIcc_of_le (by linarith)]
    exact Icc_mem_nhds (by linarith) (by linarith)
  · exact HasFiniteIntegral.of_bounded ((ae_restrict_iff' measurableSet_uIcc).mpr hM)

/-- The finite root cutoff sends the pivot-to-antidual inclusion back to
the physical sector cutoff. -/
theorem rootCutoff_embedding (j N : ℕ) (z : Fock L) :
    rootCutoff j N (embedding j z) = cutoff N z := by
  exact (rootCutoff_eq j N ⟨embedding j z, embedding_mem j z⟩).trans
    (congrArg (cutoff N) (root_embedding j z))

theorem rootCutoff_symmetric (j N : ℕ) (x y : Fock L) :
    ⟪rootCutoff j N x, y⟫_ℂ = ⟪x, rootCutoff j N y⟫_ℂ := by
  simp only [rootCutoff, sum_apply, smul_apply, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro n _
  rw [← ContinuousLinearMap.adjoint_inner_left, projection_selfadjoint]

theorem rootCutoff_apply (j N : ℕ) (x : Fock L) (n : ℕ) :
    rootCutoff j N x n = if n < N then (Real.sqrt (momentWeight j n) : ℂ) • x n else 0 := by
  simp only [rootCutoff, sum_apply, smul_apply, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply]
  by_cases hn : n < N
  · rw [ite_eq_left hn, Finset.sum_eq_single n]
    · rw [projection_same]
    · intro i _ hin
      rw [projection_other L i n (Ne.symm hin), smul_zero]
    · intro h
      exact False.elim (h (Finset.mem_range.mpr hn))
  · rw [ite_eq_right hn]
    apply Finset.sum_eq_zero
    intro i hi
    have hni : n ≠ i := by have := Finset.mem_range.mp hi; omega
    rw [projection_other L i n hni, smul_zero]

theorem rootCutoff_cutoff (j N : ℕ) (x : Fock L) :
    rootCutoff j N (cutoff N x) = rootCutoff j N x := by
  apply Subtype.ext
  funext n
  simp only [rootCutoff_apply, cutoff_apply]
  split_ifs <;> rfl

/-- Only coefficient and energy-class hypotheses are present: measurability,
local essential bounds and the literal distributional antidual equation. -/
theorem coordinate_norm_sq_conserved (j : ℕ) (x u : ℝ → Fock L)
    (K : ℝ → Fock L →L[ℂ] Fock L) (hx : Continuous x)
    (hu : AEStronglyMeasurable u volume) (hK : AEStronglyMeasurable K volume)
    (hlift : ∀ᵐ t, embedding j (u t) = x t)
    (hb : ∀ a b : ℝ, ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧
      ∀ᵐ t, t ∈ uIcc a b → ‖u t‖ ≤ C ∧ ‖K t‖ ≤ M)
    (hsym : ∀ᵐ t, (⟪u t, K t (u t)⟫_ℂ).im = 0)
    (hw : WeakDerivative (fun t => embedding j (x t)) (force K u))
    (a b : ℝ) (hab : a ≤ b) : ‖x b‖ ^ 2 = ‖x a‖ ^ 2 := by
  have hfm := force_measurable K u hK hu
  have hfi : LocallyIntegrable (force K u) volume := by
    apply locallyIntegrable_of_interval_bounds _ hfm
    intro s t
    obtain ⟨C, M, _, _, h⟩ := hb s t
    refine ⟨M * C, h.mono ?_⟩
    intro v hv hvst
    have hvI := hv hvst
    rw [force_norm]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul hvI.2 hvI.1 (norm_nonneg _) (by positivity))
  obtain ⟨C, M, hC, hM, hbd⟩ := hb a b
  have hid (N : ℕ) : ‖cutoff N (x b)‖ ^ 2 - ‖cutoff N (x a)‖ ^ 2 =
      ∫ t in a..b, 2 * ⟪cutoff N (u t), force K u t⟫_ℝ := by
    let T : Fock L →L[ℝ] Fock L := (rootCutoff (L := L) j N).restrictScalars ℝ
    have hTbd : ∀ᵐ t, t ∈ uIcc a b → ‖T (force K u t)‖ ≤ ‖rootCutoff (L := L) j N‖ * (M * C) := by
      filter_upwards [hbd] with t ht htI
      have ht' := ht htI
      apply (ContinuousLinearMap.le_opNorm (rootCutoff j N) _).trans
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      rw [force_norm]
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul ht'.2 ht'.1 (norm_nonneg _) hM)
    have hh := cutoff_norm_sq_identity T (fun t => embedding j (x t)) (force K u)
      ((embedding j).continuous.comp hx) hfi hw a b
      ⟨‖rootCutoff (L := L) j N‖ * (M * C), by positivity⟩ hTbd
    change ‖rootCutoff j N (embedding j (x b))‖ ^ 2 -
      ‖rootCutoff j N (embedding j (x a))‖ ^ 2 = _ at hh
    simp only [rootCutoff_embedding] at hh
    rw [hh]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hlift] with t ht _
    change 2 * (⟪rootCutoff j N (embedding j (x t)), rootCutoff j N (force K u t)⟫_ℂ).re = _
    rw [rootCutoff_embedding]
    rw [← rootCutoff_symmetric, rootCutoff_cutoff, ← ht, rootCutoff_embedding]
    rfl
  let μ := volume.restrict (Ioc a b)
  have : IsFiniteMeasure μ := ⟨by simp [μ]⟩
  have hbμ : ∀ᵐ t ∂μ, ‖u t‖ ≤ C ∧ ‖K t‖ ≤ M := by
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    filter_upwards [hbd] with t ht htI
    exact ht (by rw [uIcc_of_le hab]; exact Ioc_subset_Icc_self htI)
  have hm (N : ℕ) : AEStronglyMeasurable
      (fun t => 2 * ⟪cutoff N (u t), force K u t⟫_ℝ) μ :=
    aestronglyMeasurable_const.mul
      (((cutoff (L := L) N).continuous.comp_aestronglyMeasurable hu.restrict).inner hfm.restrict)
  have hd (N : ℕ) : ∀ᵐ t ∂μ,
      ‖2 * ⟪cutoff N (u t), force K u t⟫_ℝ‖ ≤ 2 * M * C ^ 2 := by
    filter_upwards [hbμ] with t ht
    have hfn : ‖force K u t‖ ≤ M * C := by
      rw [force_norm]
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul ht.2 ht.1 (norm_nonneg _) hM)
    calc
      _ = 2 * ‖⟪cutoff N (u t), force K u t⟫_ℝ‖ := by rw [norm_mul]; norm_num
      _ ≤ 2 * (‖cutoff N (u t)‖ * ‖force K u t‖) :=
        mul_le_mul_of_nonneg_left (norm_inner_le_norm (𝕜 := ℝ) _ _) (by norm_num)
      _ ≤ 2 * (C * (M * C)) := by gcongr; exact (cutoff_norm_le N _).trans ht.1
      _ = _ := by ring
  have hz : ∀ᵐ t ∂μ, 2 * ⟪u t, force K u t⟫_ℝ = 0 := by
    filter_upwards [ae_restrict_of_ae hsym] with t ht
    change 2 * (⟪u t, (-Complex.I) • (K t (u t))⟫_ℂ).re = 0
    simp [inner_smul_right, Complex.mul_re, ht]
  have hlim : ∀ᵐ t ∂μ, Tendsto
      (fun N => 2 * ⟪cutoff N (u t), force K u t⟫_ℝ) atTop (𝓝 0) := by
    filter_upwards [hz] with t ht
    rw [← ht]
    exact tendsto_const_nhds.mul ((cutoff_tendsto (u t)).inner tendsto_const_nhds)
  have htend := tendsto_integral_of_dominated_convergence
    (fun _ : ℝ => 2 * M * C ^ 2) hm (integrable_const _) hd hlim
  simp only [integral_zero] at htend
  have he : (fun N => ∫ t, 2 * ⟪cutoff N (u t), force K u t⟫_ℝ ∂μ) =
      (fun N => ‖cutoff N (x b)‖ ^ 2 - ‖cutoff N (x a)‖ ^ 2) := by
    funext N
    exact ((intervalIntegral.integral_of_le hab).symm.trans (hid N).symm)
  rw [he] at htend
  have hn := ((cutoff_tendsto (x b)).norm.pow 2).sub ((cutoff_tendsto (x a)).norm.pow 2)
  exact sub_eq_zero.mp (tendsto_nhds_unique hn htend)

/-- The D3 essential energy predicate supplies the measurable lift and all
local coordinate bounds used above. No bound for an application solution
is asserted: this theorem is about competitors already in the D3 class. -/
theorem energy_class_norm_sq_conserved (j : ℕ) (x : ℝ → Fock L)
    (K : ℝ → Fock L →L[ℂ] Fock L) (hx : Continuous x)
    (he : ∀ a b : ℝ, EnergyBounded j (uIcc a b) x)
    (hK : AEStronglyMeasurable K volume)
    (hKb : ∀ a b : ℝ, ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ t, t ∈ uIcc a b → ‖K t‖ ≤ M)
    (hs : ∀ᵐ t, ∀ v : Fock L, (⟪v, K t v⟫_ℂ).im = 0)
    (hw : WeakDerivative (fun t => embedding j (x t))
      (force K (fun t => rootLift j (x t))))
    (a b : ℝ) (hab : a ≤ b) : ‖x b‖ ^ 2 = ‖x a‖ ^ 2 := by
  have hdn (n : ℕ) : ∀ᵐ t, t ∈ uIcc (-(n : ℝ)) (n : ℝ) →
      x t ∈ momentDomain (L := L) j := by
    obtain ⟨_, _, hb⟩ := he (-(n : ℝ)) (n : ℝ)
    exact (ae_restrict_iff' measurableSet_uIcc).mp (hb.mono fun _ h => h.1)
  have hd : ∀ᵐ t, x t ∈ momentDomain (L := L) j := by
    filter_upwards [ae_all_iff.mpr hdn] with t ht
    obtain ⟨n, hn⟩ := exists_nat_gt |t|
    apply ht n
    rw [uIcc_of_le (by nlinarith [Nat.cast_nonneg (α := ℝ) n])]
    exact ⟨by linarith [neg_abs_le t], (le_abs_self t).trans hn.le⟩
  let u := fun t => rootLift j (x t)
  have hu : AEStronglyMeasurable u volume :=
    rootLift_aestronglyMeasurable j volume x hx.aestronglyMeasurable hd
  have hl : ∀ᵐ t, embedding j (u t) = x t := by
    filter_upwards [hd] with t ht
    dsimp [u]
    rw [rootLift_eq j (x t) ht]
    exact embedding_root j ⟨x t, ht⟩
  have hb : ∀ s t : ℝ, ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧
      ∀ᵐ v, v ∈ uIcc s t → ‖u v‖ ≤ C ∧ ‖K v‖ ≤ M := by
    intro s t
    obtain ⟨C, hC, henergy⟩ := he s t
    obtain ⟨M, hM, hbound⟩ := hKb s t
    refine ⟨C + 1, M, by linarith, hM, ?_⟩
    have hen := (ae_restrict_iff' measurableSet_uIcc).mp henergy
    filter_upwards [hen, hbound] with v hv hkv hvI
    have hv' := hv hvI
    refine ⟨?_, hkv hvI⟩
    have hroot : u v = momentRoot j ⟨x v, hv'.1⟩ := rootLift_eq j (x v) hv'.1
    have hnorm : ‖u v‖ ^ 2 ≤ C :=
      (congrArg (fun z : Fock L => ‖z‖ ^ 2) hroot).le.trans
        ((energy_eq_root j ⟨x v, hv'.1⟩).symm.le.trans hv'.2)
    nlinarith [sq_nonneg (‖u v‖ - 1), norm_nonneg (u v)]
  exact coordinate_norm_sq_conserved j x u K hx hu hK hl hb
    (hs.mono fun t ht => ht (u t)) hw a b hab

end QuantumNLS.Ext005PhysicalFormR110
#print axioms QuantumNLS.Ext005PhysicalFormR110.rootCutoff_embedding
#print axioms QuantumNLS.Ext005PhysicalFormR110.coordinate_norm_sq_conserved
#print axioms QuantumNLS.Ext005PhysicalFormR110.energy_class_norm_sq_conserved

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005PhysicalFormR110." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005PhysicalFormR110." then
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
  Lean.logInfo m!"R110 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
