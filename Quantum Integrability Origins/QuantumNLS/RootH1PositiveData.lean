import QuantumNLS.RootH1Ratio

/-! Bind all chain-rule hypotheses to the accepted physical small ratio. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory Set Filter Topology ComplexConjugate
open QuantumNLS.PhysicalTensor QuantumNLS.HaarResolvent QuantumNLS.RootH1Ratio
  QuantumNLS.RootH1RatioConvergence QuantumNLS.RootH1RatioAC
  QuantumNLS.RootH1RatioCompanion QuantumNLS.RootH1RatioNonlinear
namespace QuantumNLS.RootH1PositiveData
variable {L : ℝ} [hLf : Fact (0 < L)]

lemma continuous_bound {g : ℝ → ℂ} (hg : ContinuousOn g (Icc 0 L)) {C : ℝ}
    (ha : ∀ᵐ (t : ℝ) ∂volume.restrict (Icc 0 L), ‖g t‖ ≤ C) :
    ∀ t ∈ Icc (0:ℝ) L, ‖g t‖ ≤ C := by
  have he : (fun t => min ‖g t‖ C) =ᵐ[volume.restrict (Icc 0 L)] (fun t => ‖g t‖) :=
    ha.mono fun t ht => min_eq_left ht
  have heq := Measure.eqOn_Icc_of_ae_eq volume (ne_of_lt hLf.out) he
    (continuous_min.comp_continuousOn (hg.norm.prodMk continuousOn_const)) hg.norm
  intro t ht
  exact min_eq_left_iff.mp (heq ht)

/-- A periodic H¹ representative with its actual derivative and exact Riccati equation. -/
theorem curve {κ Y : ℝ} (hκ : 0 < κ) (u : L2T L) (hu : u ≠ 0)
    (hY : threshold κ u ≤ Y) :
    ∃ g d : ℝ → ℂ,
      IsH1Rep L (ratioAt hκ.le u Y) g d ∧ g L = g 0 ∧
      AbsolutelyContinuousOnInterval g 0 L ∧
      (∀ᵐ (t : ℝ) ∂volume.restrict (Icc 0 L), HasDerivAt g (d t) t) ∧
      (∀ᵐ (t : ℝ) ∂volume.restrict (Icc 0 L),
        d t = u (t:AddCircle L)-(Y:ℂ)*g t-(κ:ℂ)*conj (u (t:AddCircle L))*(g t)^2) ∧
      (∀ t ∈ Icc (0:ℝ) L, ‖g t‖ ≤ ‖ratioInfAt hκ.le u Y‖) ∧
      (∀ t ∈ Icc (0:ℝ) L, κ*‖g t‖^2 ≤ 1/4) := by
  rcases (root_H1_ratio hκ u hu).1 Y hY with ⟨_,_,_,ha,⟨g,d,hr,hper,hde⟩,hsmall,_,_⟩
  have hg := h1_ac hr
  have hge : ∀ᵐ (t : ℝ) ∂volume.restrict (Icc 0 L), (ratioAt hκ.le u Y) (t:AddCircle L) = g t := by
    filter_upwards [pull_ae hr.1,rep_ae (L := L)] with t ht hrep
    rw [hrep] at ht
    exact ht
  have hnorm : ∀ᵐ (t : ℝ) ∂volume.restrict (Icc 0 L), ‖g t‖ ≤ ‖ratioInfAt hκ.le u Y‖ := by
    filter_upwards [hge,pull_ae ha,pull_ae (ae_norm_le (ratioInfAt hκ.le u Y))] with t ht ha' hn
    rwa [← ha',ht] at hn
  have hbound := continuous_bound (by simpa [uIcc_of_le hLf.out.le] using hg.continuousOn) hnorm
  refine ⟨g,d,hr,hper,hg,h1_ae_deriv hr,?_,hbound,?_⟩
  · filter_upwards [pull_ae hde,rep_ae (L := L),hge] with t ht hrep hgt
    rwa [hrep,hgt] at ht
  · intro t ht
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hbound t ht) 2) hκ.le).trans hsmall

/-- The exact printed δ tends to zero for the full real height parameter. -/
theorem delta_tendsto {κ : ℝ} (hκ : 0 < κ) (u : L2T L) (hu : u ≠ 0) :
    Tendsto (fun Y : ℝ => κ*‖ratioInfAt hκ.le u Y‖^2) atTop (nhds 0) := by
  have hb : ∀ᶠ Y : ℝ in atTop, κ*‖ratioInfAt hκ.le u Y‖^2 ≤ 4*κ*‖u‖^2/Y := by
    filter_upwards [eventually_ge_atTop (threshold κ u)] with Y hY
    have hypos := (height_spec u hY).1
    have hn := ((root_H1_ratio hκ u hu).1 Y hY).1
    have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
    rw [mul_pow,Real.sq_sqrt (div_nonneg (sq_nonneg _) hypos.le)] at hs
    calc
      κ*‖ratioInfAt hκ.le u Y‖^2 ≤ κ*(2^2*(‖u‖^2/Y)) := mul_le_mul_of_nonneg_left hs hκ.le
      _ = _ := by ring
  exact squeeze_zero' (Eventually.of_forall fun _ => mul_nonneg hκ.le (sq_nonneg _)) hb
    (tendsto_const_nhds.div_atTop tendsto_id)

#print axioms continuous_bound
#print axioms curve
#print axioms delta_tendsto
end QuantumNLS.RootH1PositiveData

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootH1PositiveData." ||
        n.toString.startsWith "_private.QuantumNLS.RootH1PositiveData." then
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
