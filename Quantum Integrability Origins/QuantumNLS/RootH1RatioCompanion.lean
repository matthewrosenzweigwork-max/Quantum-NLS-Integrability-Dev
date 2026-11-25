import QuantumNLS.RootH1RatioFloquet

/-! Bind the rough Floquet comparison to the constructed physical L² ratio. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory Set Filter Topology ComplexConjugate
open scoped InnerProductSpace ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.HaarResolvent
  QuantumNLS.RootH1RatioOperator QuantumNLS.RootH1RatioNonlinear
  QuantumNLS.RootH1RatioBounds QuantumNLS.RootH1RatioAC
namespace QuantumNLS.RootH1RatioCompanion
variable {L : ℝ} [hLf : Fact (0 < L)]

lemma pull_ae {P : AddCircle L → Prop} (h : ∀ᵐ x, P x) :
    ∀ᵐ t : ℝ ∂volume.restrict (Icc 0 L), P (t : AddCircle L) := by
  have hh := (AddCircle.measurePreserving_mk L 0).quasiMeasurePreserving.ae h
  rw [zero_add, restrict_Ioc_eq_restrict_Icc] at hh
  exact hh

lemma rep_ae : ∀ᵐ t : ℝ ∂volume.restrict (Icc 0 L), rep1 L (t : AddCircle L) = t := by
  have hn : ∀ᵐ t : ℝ ∂volume.restrict (Icc 0 L), t ≠ L := ae_restrict_of_ae (by simp [ae_iff])
  filter_upwards [ae_restrict_mem measurableSet_Icc,hn] with t ht htL
  exact rep1_coe L ⟨ht.1, lt_of_le_of_ne ht.2 htL⟩

lemma coe_forcing (κ : ℝ) (u : L2T L) (r : Linfty L) :
    forcing κ u r =ᵐ[volume] (fun x => u x-(κ:ℂ)*conj (u x)*(r x)^2) := by
  filter_upwards [Lp.coeFn_sub u ((κ:ℂ) • cubic u r),
    Lp.coeFn_smul (κ:ℂ) (cubic u r),coe_cubic u r] with x hs hm hc
  change (u-(κ:ℂ) • cubic u r) x = _
  rw [hs,Pi.sub_apply,hm,Pi.smul_apply,smul_eq_mul,hc]
  simp only [starRingEnd_apply]
  ring

lemma pairing_eq (u v : L2T L) {g : ℝ → ℂ} (hv : ∀ᵐ x, v x = g (rep1 L x)) :
    inner ℂ u v = ∫ t in (0:ℝ)..L, conj (u (t : AddCircle L))*g t := by
  rw [L2.inner_def]
  simp only [RCLike.inner_apply']
  have he := AddCircle.intervalIntegral_preimage L 0 (fun x => conj (u x)*v x)
  rw [zero_add] at he
  rw [← he]
  apply intervalIntegral.integral_congr_ae
  have hh := (ae_restrict_iff' measurableSet_Icc).mp (pull_ae hv)
  have hr := (ae_restrict_iff' measurableSet_Icc).mp (rep_ae (L := L))
  filter_upwards [hh,hr] with t ht hrt htL
  have htI : t ∈ Icc (0:ℝ) L := by
    have hm := uIoc_subset_uIcc htL
    simpa only [uIcc_of_le hLf.out.le] using hm
  rw [ht htI,hrt htI]

/-- No continuous-input monodromy hypothesis: the ratio's actual H¹ representative is used. -/
theorem ratio_trace {Y κ : ℝ} (hY : 0 < Y) (hlog : Real.log 3 ≤ Y*L)
    (hκ : 0 ≤ κ) (u : L2T L) (hsmall : 16*κ*‖u‖^2 ≤ Y) :
    L2SpatialTransfer.discriminant κ u ((Y:ℂ)*Complex.I) =
      Complex.exp ((Y:ℂ)*L/2+(κ:ℂ)*inner ℂ u (ratioL2 hY hlog hκ u hsmall)) +
      (Complex.exp ((Y:ℂ)*L/2+(κ:ℂ)*inner ℂ u (ratioL2 hY hlog hκ u hsmall)))⁻¹ := by
  let r := ratio hY hlog hκ u hsmall
  let v := ratioL2 hY hlog hκ u hsmall
  obtain ⟨g,h,hrep,hper,ha⟩ := ratio_H1 hY hlog hκ u hsmall
  have hrg : r =ᵐ[volume] (fun x => g (rep1 L x)) := (ratioL2_ae hY hlog hκ u hsmall).symm.trans hrep.1
  have hder : ∀ᵐ (t : ℝ) ∂volume.restrict (Icc 0 L),
      HasDerivAt g (u (t : AddCircle L)-(Y:ℂ)*g t-(κ:ℂ)*conj (u (t : AddCircle L))*(g t)^2) t := by
    have hcf := coe_forcing κ u r
    filter_upwards [pull_ae ha,pull_ae hcf,pull_ae hrg,rep_ae (L := L),h1_ae_deriv hrep]
      with t hat hft hrt hrep1 hd
    rw [hrep1] at hat hrt
    rw [hft,hrt] at hat
    have he : Complex.I*((Y:ℂ)*Complex.I) = -(Y:ℂ) := by
      linear_combination (Y:ℂ)*Complex.I_mul_I
    rw [he] at hat
    apply hd.congr_deriv
    linear_combination -hat
  have hbound := RootH1RatioFloquet.trace_ratio hLf.out hκ
    (L2SpatialTransfer.intervalIntegrable_profile u) (h1_ac hrep)
    (by simpa only [one_mul] using hper) hder
  have hj := pairing_eq u v hrep.1
  simp only [L2SpatialTransfer.profile] at hbound
  rw [← hj] at hbound
  exact hbound

#print axioms pull_ae
#print axioms rep_ae
#print axioms coe_forcing
#print axioms pairing_eq
#print axioms ratio_trace
end QuantumNLS.RootH1RatioCompanion

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootH1RatioCompanion." ||
        n.toString.startsWith "_private.QuantumNLS.RootH1RatioCompanion." then
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
