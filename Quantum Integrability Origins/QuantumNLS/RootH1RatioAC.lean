import QuantumNLS.RootH1RatioBounds
import QuantumNLS.L2SpatialTransfer

/-! Absolute-continuity tools at the actual rough-input regularity. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.HaarResolvent
  QuantumNLS.L1SpatialTransfer
namespace QuantumNLS.RootH1RatioAC
variable {L : ℝ}

lemma ac_exp {f : ℝ → ℂ} (hf : AbsolutelyContinuousOnInterval f 0 L) :
    AbsolutelyContinuousOnInterval (fun t => Complex.exp (f t)) 0 L := by
  obtain ⟨C,hC⟩ := isCompact_uIcc.exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨K,hK⟩ := (Complex.contDiff_exp : ContDiff ℝ 1 Complex.exp).contDiffOn.exists_lipschitzOnWith
    (by norm_num) (convex_closedBall (0:ℂ) C) (isCompact_closedBall (0:ℂ) C)
  exact hK.comp_absolutelyContinuousOnInterval
    (fun t ht => by simpa using hC t ht) hf

/-- The a.e. derivative determines an absolutely continuous Banach-valued function. -/
lemma ac_integral_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hL : 0 ≤ L) {f d : ℝ → E} (hf : AbsolutelyContinuousOnInterval f 0 L)
    (hd : IntervalIntegrable d volume 0 L)
    (hder : ∀ᵐ t ∂volume.restrict (Icc 0 L), HasDerivAt f (d t) t)
    {x : ℝ} (hx : x ∈ Icc 0 L) : f x = f 0 + ∫ t in (0:ℝ)..x, d t := by
  let F : ℝ → E := fun t => f t - ∫ s in (0:ℝ)..t, d s
  have hac : AbsolutelyContinuousOnInterval F 0 L := hf.sub (ac_integral hd)
  have hz : ∀ᵐ t, t ∈ uIcc (0:ℝ) L → HasDerivAt F 0 t := by
    have hder' := (ae_restrict_iff' measurableSet_Icc).mp hder
    filter_upwards [hder',hd.ae_hasDerivAt_integral] with t ht hi htL
    have htI : t ∈ Icc (0:ℝ) L := by simpa [uIcc_of_le hL] using htL
    simpa only [F, sub_self] using! (ht htI).sub (hi htL 0 (by simp))
  obtain ⟨C,hC⟩ := hac.const_of_ae_hasDerivAt_zero hz
  have he0 := hC 0 (by simp)
  have hex := hC x (by simpa [uIcc_of_le hL] using hx)
  simp only [F, intervalIntegral.integral_same, sub_zero] at he0
  dsimp [F] at hex
  rw [← he0] at hex
  exact sub_eq_iff_eq_add.mp hex

lemma h1_ac [hLf : Fact (0 < L)] {f : L2T L} {g h : ℝ → ℂ}
    (hf : IsH1Rep L f g h) : AbsolutelyContinuousOnInterval g 0 L := by
  have hi : IntervalIntegrable h volume 0 L :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hLf.out.le).mpr (hf.2.1.integrable (by norm_num))
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => g 0) 0 L :=
    (LipschitzWith.const (g 0)).lipschitzOnWith.absolutelyContinuousOnInterval
  exact (hc.add (ac_integral hi)).congr (fun t ht => (hf.2.2 t (by simpa [uIcc_of_le hLf.out.le] using ht)).symm)

lemma h1_ae_deriv [hLf : Fact (0 < L)] {f : L2T L} {g h : ℝ → ℂ}
    (hf : IsH1Rep L f g h) :
    ∀ᵐ t ∂volume.restrict (Icc 0 L), HasDerivAt g (h t) t := by
  have hi : IntervalIntegrable h volume 0 L :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hLf.out.le).mpr (hf.2.1.integrable (by norm_num))
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  have hn0 : ∀ᵐ t : ℝ, t ≠ 0 := by simp [ae_iff]
  have hnL : ∀ᵐ t : ℝ, t ≠ L := by simp [ae_iff]
  filter_upwards [hi.ae_hasDerivAt_integral,hn0,hnL] with t hd ht0 htL ht
  have hti : t ∈ Ioo (0:ℝ) L := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),lt_of_le_of_ne ht.2 htL⟩
  have hd' := (hd (by simpa [uIcc_of_le hLf.out.le] using ht) 0 (by simp)).const_add (g 0)
  apply hd'.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hti.1 hti.2] with s hs
  exact hf.2.2 s ⟨hs.1.le,hs.2.le⟩

#print axioms ac_exp
#print axioms ac_integral_eq
#print axioms h1_ac
#print axioms h1_ae_deriv
end QuantumNLS.RootH1RatioAC

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootH1RatioAC." ||
        n.toString.startsWith "_private.QuantumNLS.RootH1RatioAC." then
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
