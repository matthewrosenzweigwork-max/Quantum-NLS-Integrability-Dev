import QuantumNLS.RootH1RatioResolvent

/-! Supporting results for R-D24009D4 / lem:root-H1-ratio, not its assembled proof.
The periodic derivative resolvent on the actual physical L² space. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace ENNReal
open QuantumNLS.HaarResolvent QuantumNLS.RootH1RatioResolvent
  QuantumNLS.PhysicalTensor
namespace QuantumNLS.RootH1RatioOperator
variable {L : ℝ} [hLf : Fact (0 < L)]

def resolvent (Y : ℝ) : L2T L →L[ℂ] L2T L :=
  R1 L (Real.exp (-Y*L)) ((Y:ℂ)*Complex.I)

lemma integral_norm_sq (f : L2T L) :
    (∫ x : AddCircle L, ‖f x‖^2) = ‖f‖^2 := by
  have h := L2.inner_def (𝕜 := ℂ) f f
  have e1 : ⟪f, f⟫_ℂ = ((‖f‖^2 : ℝ):ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  have e2 : ∀ x : AddCircle L, inner ℂ (f x : ℂ) (f x : ℂ) = ((‖f x‖^2 : ℝ):ℂ) := by
    intro x
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  simp_rw [e2] at h
  rw [integral_complex_ofReal, e1] at h
  exact_mod_cast h.symm

lemma integral_profile_sq (f : L2T L) :
    (∫ t in (0:ℝ)..L, ‖psi0 L f t‖^2) = ‖f‖^2 := by
  have h := AddCircle.intervalIntegral_preimage L 0 (fun x : AddCircle L => ‖f x‖^2)
  simpa only [zero_add, psi0] using h.trans (integral_norm_sq f)

lemma ae_resolvent_sq {Y : ℝ} (hY : 0 < Y) (hlog : Real.log 3 ≤ Y*L)
    (f : L2T L) :
    ∀ᵐ x : AddCircle L, ‖resolvent Y f x‖^2 ≤ (1/Y)*‖f‖^2 := by
  filter_upwards [R1_apply_ae L (Real.exp (-Y*L)) ((Y:ℂ)*Complex.I) f] with x hx
  change ‖R1 L (Real.exp (-Y*L)) ((Y:ℂ)*Complex.I) f x‖^2 ≤ _
  rw [hx]
  have h := row_bound hY hlog (rep1_bounds L x) (memLp_psi0 L f)
  rwa [integral_profile_sq f] at h

lemma ae_resolvent_bound {Y : ℝ} (hY : 0 < Y) (hlog : Real.log 3 ≤ Y*L)
    (f : L2T L) :
    ∀ᵐ x : AddCircle L, ‖resolvent Y f x‖ ≤ ‖f‖/Real.sqrt Y := by
  have hs : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY
  have he : (‖f‖/Real.sqrt Y)^2 = (1/Y)*‖f‖^2 := by
    rw [div_pow, Real.sq_sqrt hY.le]
    ring
  filter_upwards [ae_resolvent_sq hY hlog f] with x hx
  rw [← he] at hx
  exact (sq_le_sq₀ (norm_nonneg _) (div_nonneg (norm_nonneg _) hs.le)).mp hx

omit hLf in
lemma qOf_eq (Y : ℝ) : qOf L 1 ((Y:ℂ)*Complex.I) = (Real.exp (-Y*L):ℂ) := by
  unfold qOf
  rw [one_mul]
  have he : Complex.I * ((Y:ℂ)*Complex.I) * (L:ℂ) = ((-Y*L:ℝ):ℂ) := by
    push_cast
    calc
      Complex.I * ((Y:ℂ)*Complex.I) * (L:ℂ) =
          (Complex.I*Complex.I)*((Y:ℂ)*(L:ℂ)) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [he, Complex.ofReal_exp]

lemma resolvent_range {Y : ℝ} (hY : 0 < Y) (f : L2T L) :
    (resolvent Y f, f) ∈ graphD L 1 ((Y:ℂ)*Complex.I) := by
  have he : Real.exp (-Y*L) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [hLf.out])
  have hq : qOf L 1 ((Y:ℂ)*Complex.I) ≠ 1 := by
    rw [qOf_eq]
    exact_mod_cast he.ne
  have h := QuantumNLS.HaarResolvent.resolvent_range L (ρ := 1) (by norm_num) hq f
  rw [qOf_eq] at h
  exact h

abbrev Linfty (L : ℝ) [Fact (0 < L)] : Type := Lp ℂ ∞ (volume : Measure (AddCircle L))

lemma infinityMem {Y : ℝ} (hY : 0 < Y) (hlog : Real.log 3 ≤ Y*L)
    (f : L2T L) : MemLp (resolvent Y f) ∞ volume :=
  MemLp.of_bound (Lp.aestronglyMeasurable _) (‖f‖/Real.sqrt Y)
    (ae_resolvent_bound hY hlog f)

def infinityResolvent {Y : ℝ} (hY : 0 < Y) (hlog : Real.log 3 ≤ Y*L)
    (f : L2T L) : Linfty L := (infinityMem hY hlog f).toLp _

lemma coe_infinityResolvent {Y : ℝ} (hY : 0 < Y) (hlog : Real.log 3 ≤ Y*L)
    (f : L2T L) : infinityResolvent hY hlog f =ᵐ[volume] resolvent Y f :=
  MemLp.coeFn_toLp _

lemma infinityResolvent_norm {Y : ℝ} (hY : 0 < Y) (hlog : Real.log 3 ≤ Y*L)
    (f : L2T L) : ‖infinityResolvent hY hlog f‖ ≤ ‖f‖/Real.sqrt Y := by
  have hb : ∀ᵐ x : AddCircle L, ‖infinityResolvent hY hlog f x‖ ≤ ‖f‖/Real.sqrt Y := by
    filter_upwards [coe_infinityResolvent hY hlog f, ae_resolvent_bound hY hlog f]
      with x hx hb
    rwa [hx]
  have h := Lp.norm_le_of_ae_bound (by positivity : 0 ≤ ‖f‖/Real.sqrt Y) hb
  simpa only [ENNReal.toReal_top, inv_zero, Real.rpow_zero, one_mul] using h

#print axioms integral_norm_sq
#print axioms integral_profile_sq
#print axioms ae_resolvent_sq
#print axioms ae_resolvent_bound
#print axioms qOf_eq
#print axioms resolvent_range
#print axioms infinityMem
#print axioms coe_infinityResolvent
#print axioms infinityResolvent_norm
end QuantumNLS.RootH1RatioOperator

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootH1RatioOperator." ||
        n.toString.startsWith "_private.QuantumNLS.RootH1RatioOperator." then
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
