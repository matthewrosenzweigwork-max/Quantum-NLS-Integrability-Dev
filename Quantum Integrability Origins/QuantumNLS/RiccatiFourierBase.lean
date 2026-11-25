import QuantumNLS.RiccatiPointwiseDisc
import QuantumNLS.RiccatiChargeLevels
import QuantumNLS.ChargeEnergy

/-! Smooth periodic profiles have a base in every finite Sobolev weight.
The report coefficients include √L; reconstruction below uses the probability
Fourier coefficients and their everywhere convergent continuous Fourier series.
-/
set_option autoImplicit false
noncomputable section
open scoped ContDiff
open MeasureTheory

namespace QuantumNLS.RiccatiFourierBase
open QuantumNLS.ClassicalCharges QuantumNLS.WeakDerivatives
open QuantumNLS.RiccatiSobolevE1 QuantumNLS.RiccatiSobolevE2b
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevS
open QuantumNLS.RiccatiChargeLevels QuantumNLS.RiccatiPointwiseDisc

private lemma smooth_deriv {L : ℝ} {f : ℝ → ℂ} (hf : SmoothPeriodic L f) :
    SmoothPeriodic L (deriv f) :=
  ⟨(contDiff_infty_iff_deriv.mp hf.smooth).2, periodic_deriv hf.periodic⟩

/-- Repeated integration by parts and Parseval give every integer weighted sum. -/
private lemma smooth_weight_nat {L : ℝ} [Fact (0 < L)] (n : ℕ)
    {f : ℝ → ℂ} (hf : SmoothPeriodic L f) :
    Summable (fun k : ℤ => (1 + |freq L k|) ^ (2 * n) *
      ‖QuantumNLS.Fourier.coeff L (liftC hf.smooth.continuous hf.periodic) k‖ ^ 2) := by
  induction n generalizing f with
  | zero =>
    simpa using (QuantumNLS.Fourier.hasSum_sq_coeff L
      (QuantumNLS.Fourier.memLp_of_continuous
        (liftC hf.smooth.continuous hf.periodic).continuous)).summable
  | succ n ih =>
    have h0 := ih hf
    have h1 := ih (smooth_deriv hf)
    have hd (k : ℤ) :
        ‖QuantumNLS.Fourier.coeff L
          (liftC (smooth_deriv hf).smooth.continuous (smooth_deriv hf).periodic) k‖ ^ 2 =
        freq L k ^ 2 *
          ‖QuantumNLS.Fourier.coeff L (liftC hf.smooth.continuous hf.periodic) k‖ ^ 2 := by
      rw [QuantumNLS.ChargeEnergy.coeff_deriv hf, norm_ikn_mul_sq]
      rfl
    refine Summable.of_nonneg_of_le (fun k => by positivity) ?_ ((h0.add h1).mul_left 2)
    intro k
    simp only [hd]
    rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
    have hq : (1 + |freq L k|) ^ 2 ≤ 2 * (1 + freq L k ^ 2) := by
      nlinarith [sq_nonneg (|freq L k| - 1), sq_abs (freq L k)]
    have hm := mul_le_mul_of_nonneg_left hq
      (show 0 ≤ (1 + |freq L k|) ^ (2 * n) *
        ‖QuantumNLS.Fourier.coeff L (liftC hf.smooth.continuous hf.periodic) k‖ ^ 2 by positivity)
    nlinarith only [hm]

/-- Smoothness gives finite weighted ℓ² mass for every real weight. -/
private lemma smooth_weight {L : ℝ} [Fact (0 < L)] (S : ℝ)
    {f : ℝ → ℂ} (hf : SmoothPeriodic L f) :
    Summable (fun k : ℤ => wt L S k *
      ‖QuantumNLS.Fourier.coeff L (liftC hf.smooth.continuous hf.periodic) k‖ ^ 2) := by
  obtain ⟨n, hn⟩ := exists_nat_ge S
  have hs := smooth_weight_nat n hf
  have hs' : Summable (fun k : ℤ => wt L (n : ℝ) k *
      ‖QuantumNLS.Fourier.coeff L (liftC hf.smooth.continuous hf.periodic) k‖ ^ 2) := by
    unfold wt
    rw [show 2 * (n : ℝ) = ((2 * n : ℕ) : ℝ) by push_cast; ring]
    simpa only [Real.rpow_natCast] using hs
  exact Summable.of_nonneg_of_le
    (fun k => mul_nonneg (wt_nonneg L S k) (sq_nonneg _))
    (fun k => mul_le_mul_of_nonneg_right (wt_le_wt hn k) (sq_nonneg _)) hs'

/-- Every smooth periodic profile is represented everywhere by a base at weight S,
viewed at the bottom weight a. This applies in particular to every integer S in
`SmoothScalarMomentsPrerequisite.RiccatiPrintedConclusion`. -/
theorem riccati_fourier_base {L a S : ℝ} (hL : 0 < L) (ha : 1 / 2 < a)
    (haS : a ≤ S) {f : ℝ → ℂ} (hf : SmoothPeriodic L f) :
    ∃ base : Ell2, physRep L a (lowT L a S base) = f := by
  let : Fact (0 < L) := ⟨hL⟩
  let F : C(AddCircle L, ℂ) := liftC hf.smooth.continuous hf.periodic
  let c : ℤ → ℂ := QuantumNLS.Fourier.coeff L F
  have hc : Summable (fun k => wt L S k * ‖c k‖ ^ 2) := smooth_weight S hf
  let base : Ell2 := ⟨fun k => (pw L S k : ℂ) * c k, memℓp_of_summable hc⟩
  have hb : toField L S base = c := by
    funext k
    exact mul_div_cancel_left₀ (c k) (pw_ne_zero L S k)
  refine ⟨base, ?_⟩
  have hc1 : Summable (fun k => ‖c k‖) :=
    l1_summable hL ha (smooth_weight a hf)
  have hfc : Summable (fourierCoeff F) := by
    have he : fourierCoeff F = fun k =>
        (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * c k :=
      funext (QuantumNLS.Fourier.fourierCoeff_eq_coeff_div L F)
    rw [he]
    exact hc1.of_norm.mul_left _
  funext x
  change (((Real.sqrt L)⁻¹ : ℝ) : ℂ) *
    QuantumNLS.RiccatiPointwise.series L (toField L a (lowT L a S base)) x = f x
  rw [toField_lowT haS, hb, ← QuantumNLS.RiccatiPointwiseRep.seriesRep_coe]
  have hsum := has_pointwise_sum_fourier_series_of_summable hfc (x : AddCircle L)
  have he : QuantumNLS.Fourier.seriesRep L c (x : AddCircle L) =
      ∑' k : ℤ, fourierCoeff F k * fourier k (x : AddCircle L) := by
    apply tsum_congr
    intro k
    rw [QuantumNLS.Fourier.fourierCoeff_eq_coeff_div]
    change c k * ((((Real.sqrt L)⁻¹ : ℝ) : ℂ) * fourier k (x : AddCircle L)) = _
    ring
  rw [he, show (∑' k : ℤ, fourierCoeff F k * fourier k (x : AddCircle L)) =
      F (x : AddCircle L) from hsum.tsum_eq]
  exact liftC_coe _ _ x

end QuantumNLS.RiccatiFourierBase

#print axioms QuantumNLS.RiccatiFourierBase.riccati_fourier_base

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RiccatiFourierBase." ||
        n.toString.startsWith "_private.QuantumNLS.RiccatiFourierBase." then
      pending := pending.push n
  let ownCount := pending.size
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
  Lean.logInfo m!"Riccati Fourier base audit PASS: {ownCount} own/generated constants; {seen.size} transitive constants; standard only."
