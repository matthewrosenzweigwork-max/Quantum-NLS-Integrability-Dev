import QuantumNLS.FullMass
import QuantumNLS.RiccatiExpansions
import QuantumNLS.RootTraceSymbolFinal

/-! R-275B7656: physical Cauchy/Floquet binding, at arbitrary mass.
The frozen RiccatiExpansions.log_expansion is consumed read-only. The
quantum-derived measure is FullMass.Mmeas, never defined from a classical branch.
The larger comparison disk below avoids assuming a sharp mass bound on the
Riccati solution. No moment or coefficient identity is a premise. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory
namespace QuantumNLS.SmoothScalarMomentsBinding
open QuantumNLS.PhysicalTensor QuantumNLS.FullMass QuantumNLS.RootMeasureComplex
open QuantumNLS.CauchyUniqueness QuantumNLS.NormalizedTransfer
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE2b
open QuantumNLS.RiccatiSobolevE2 QuantumNLS.RiccatiChargeLevels
open QuantumNLS.RiccatiPicardBall QuantumNLS.RiccatiPointwiseDisc
open QuantumNLS.RiccatiMonodromy QuantumNLS.RiccatiExpansions
open QuantumNLS.ComplexifiedSobolevField QuantumNLS.RiccatiSobolevS

variable {L : ℝ} [Fact (0 < L)]

lemma mass_transfer {κ : ℝ} (hκ : 0 < κ) (u : L2T L) {z : ℂ}
    (hz : HighHalf L (κ * ‖u‖ ^ 2) z) (hzi : 0 < z.im) :
    ‖cauchyTransform (Mmeas κ u) z‖ ≤ ‖u‖ ^ 2 / z.im ∧
    fz L κ z (cauchyTransform (Mmeas κ u) z) = productSymbol L κ u z := by
  by_cases hu : u = 0
  · subst u
    obtain ⟨hG, hs, -⟩ := mass_characterization_zero (L := L) κ hzi
    rw [hG]
    exact ⟨by simp, hs⟩
  · exact ⟨(mass_characterization hκ hu hz).1, (mass_characterization hκ hu hz).2.1⟩

/-- Uniqueness on ANY disk of radius B/Im z, after raising the high-strip
threshold to κ B. B need not be the mass of the physical field. -/
lemma scaled_unique {κ B : ℝ} (hκ : 0 < κ) (hB : 0 < B) {z g g' : ℂ}
    (hz : HighHalf L (κ * B) z) (hg : ‖g‖ ≤ B / z.im)
    (hg' : ‖g'‖ ≤ B / z.im) (heq : fz L κ z g = fz L κ z g') : g = g' := by
  have hBc : (B : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hB.ne'
  have hb (v : ℂ) (hv : ‖v‖ ≤ B / z.im) : ‖v / (B : ℂ)‖ ≤ (z.im)⁻¹ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB, div_le_iff₀ hB]
    simpa only [div_eq_mul_inv, mul_comm] using hv
  have he : fz L (κ * B) z (g / (B : ℂ)) = fz L (κ * B) z (g' / (B : ℂ)) := by
    rw [← fz_scale, ← fz_scale, mul_div_cancel₀ _ hBc, mul_div_cancel₀ _ hBc, heq]
  have h := QuantumNLS.RootMeasureConcentration.unique_fixed (mul_pos hκ hB) hz
    (hb g hg) (hb g' hg') he
  exact (div_left_inj' hBc).mp h

/-- The growing multiplier determines the Cauchy value of the ALREADY
constructed quantum measure. Includes zero field and arbitrary mass. -/
theorem cauchy_eq_floquet {κ B : ℝ} (hκ : 0 < κ) (hB : 0 < B)
    (u : L2T L) (hm : ‖u‖ ^ 2 ≤ B) {z J : ℂ}
    (hz : HighHalf L (κ * B) z) (hzi : 0 < z.im)
    (hJ : ‖J‖ ≤ B / z.im)
    (htrace : Complex.exp (Complex.I * z * (L : ℂ) / 2) *
      (Complex.exp (-(Complex.I * z * (L : ℂ) / 2) + (κ : ℂ) * J) +
        (Complex.exp (-(Complex.I * z * (L : ℂ) / 2) + (κ : ℂ) * J))⁻¹)
      = productSymbol L κ u z) :
    J = Complex.I * cauchyTransform (Mmeas κ u) z := by
  have hz' : HighHalf L (κ * ‖u‖ ^ 2) z :=
    ⟨by nlinarith [hz.1], hz.2⟩
  obtain ⟨hG, ht⟩ := mass_transfer hκ u hz' hzi
  have hbG : ‖cauchyTransform (Mmeas κ u) z‖ ≤ B / z.im :=
    hG.trans (div_le_div_of_nonneg_right hm hzi.le)
  have hnorm : ‖J / Complex.I‖ ≤ B / z.im := by simpa using hJ
  have hf : fz L κ z (J / Complex.I) = productSymbol L κ u z := by
    rw [QuantumNLS.RiccatiFloquet.trace_exp_identity] at htrace
    convert htrace using 1
    unfold fz
    have h1 : Complex.I * (κ : ℂ) * (J / Complex.I) = (κ : ℂ) * J := by
      field_simp
    rw [h1, mul_add, mul_one]
    have ht : Complex.exp (Complex.I * z * (L : ℂ)) * Complex.exp (-((κ : ℂ) * J)) =
        Complex.exp ((κ : ℂ) * J) * Complex.exp (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * J) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      ring
    exact congrArg (fun w => Complex.exp ((κ : ℂ) * J) + w) ht
  have he := scaled_unique hκ hB hz hnorm hbG (hf.trans ht.symm)
  have hh := congrArg (fun w : ℂ => Complex.I * w) he
  convert hh using 1
  field_simp

/-- Direct read-only binding to frozen log_expansion, in physical κ.
Its actual expansion coefficients and explicit error bound are preserved. -/
theorem physical_log_expansion {a S : ℝ} {M : ℕ}
    (hL : 0 < L) (ha : 1 / 2 < a) (haS : a + (M : ℝ) + 1 ≤ S)
    (hM : 1 ≤ M) (κ : ℝ) (hκ : 0 < κ) (u : Ell2) (β : ℝ)
    (hβ : 0 < β) (hu : ‖u‖ ≤ β)
    (D : Ell2 →ₗ[ℂ] Ell2) (hD : ∀ y : dDom L, D (y : Ell2) = dmulEll L y)
    (δ : ℝ) (hδ : 0 < δ) (z : ℂ) (hz : 0 < z.im) (hsec : δ * ‖z‖ ≤ z.im)
    (hR : logR L a S M κ β δ ≤ ‖z‖)
    (r : Ell2) (hr : riccatiT hL ha hz (κ / L) (lowT L a S u)
      (jEll (lowT L a S u)) r = r) (hrn : ‖r‖ ≤ 2 * β / z.im)
    (B : ℝ) (hB : 0 < B)
    (hm : ‖fieldMap L a (by linarith : (0 : ℝ) ≤ a) (lowT L a S u)‖ ^ 2 ≤ B)
    (hb : 2 * L * (physK L a) ^ 2 * β ^ 2 ≤ B)
    (hhigh : HighHalf L (κ * B) z) :
    let U := fieldMap L a (by linarith : (0 : ℝ) ≤ a) (lowT L a S u)
    let G := cauchyTransform (Mmeas κ U) z
    floquetJ L a (lowT L a S u) r = Complex.I * G ∧
    ‖Complex.I * (κ : ℂ) * G +
        Complex.log (1 + Complex.exp (Complex.I * z * (L : ℂ) -
          2 * Complex.I * (κ : ℂ) * G)) -
        Complex.I * (κ : ℂ) * ∑ n ∈ Finset.Icc 1 M,
          modeCoef L a (jEll (lowT L a S u))
            (QuantumNLS.RiccatiChargeLevels.wAbs (mulLin hL ha) D
              (jEll (lowT L a S u)) (lowT L a S u) ((κ / L : ℝ) : ℂ) n) * (z⁻¹) ^ n‖
      ≤ logC L a S M κ β δ * (‖z‖ ^ (M + 1))⁻¹ := by
  dsimp only
  obtain ⟨_, hbnd⟩ := log_expansion L hL ha haS hM κ hκ u β hβ hu D hD
    δ hδ z hz hsec hR r hr hrn
  have hc := QuantumNLS.RootTraceSymbolFinal.traceSymbol_all (L := L) hκ.le
    (fieldMap L a (by linarith) (lowT L a S u)) z
  have htrace : Complex.exp (Complex.I * z * (L : ℂ) / 2) *
      (Complex.exp (-(Complex.I * z * (L : ℂ) / 2) + (κ : ℂ) *
        floquetJ L a (lowT L a S u) r) +
        (Complex.exp (-(Complex.I * z * (L : ℂ) / 2) + (κ : ℂ) *
          floquetJ L a (lowT L a S u) r))⁻¹) =
      productSymbol L κ (fieldMap L a (by linarith) (lowT L a S u)) z := by
    rw [QuantumNLS.RiccatiPointwiseDisc.l2_discriminant_monodromy L ha hz hκ
      (lowT L a S u) r hr, psi_floquet κ hL ha] at hc
    rw [← hc, ← mul_assoc, ← Complex.exp_add]
    simp
  have hpk : 0 ≤ physK L a := physK_nonneg (by linarith)
  have hul : ‖lowT L a S u‖ ≤ β := (norm_lowT_le L a S u).trans hu
  have hJ : ‖floquetJ L a (lowT L a S u) r‖ ≤ B / z.im := by
    have ht := QuantumNLS.RiccatiJBound.norm_J_le (f := physRep L a (lowT L a S u))
      (r := physRep L a r) hL.le (mul_nonneg hpk hβ.le)
      (fun t _ => (physRep_norm_le hL ha _ t).trans (mul_le_mul_of_nonneg_left hul hpk))
      (fun t _ => (physRep_norm_le hL ha r t).trans (mul_le_mul_of_nonneg_left hrn hpk))
    change ‖floquetJ L a (lowT L a S u) r‖ ≤ _ at ht
    calc _ ≤ L * (physK L a * β * (physK L a * (2 * β / z.im))) := ht
      _ = (2 * L * physK L a ^ 2 * β ^ 2) / z.im := by ring
      _ ≤ B / z.im := div_le_div_of_nonneg_right hb hz.le
  have hid := cauchy_eq_floquet hκ hB _ hm hhigh hz hJ htrace
  refine ⟨hid, ?_⟩
  rw [hid] at hbnd
  convert hbnd using 1
  unfold logS
  congr 2
  ring

omit [Fact (0 < L)] in
/-- Integrating the frozen H^a remainder preserves its inverse-power order. -/
theorem integrated_remainder {a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a)
    (x r : Ell2) (w : ℕ → Ell2) (M : ℕ) (z : ℂ) (C : ℝ)
    (hrem : ‖r - QuantumNLS.RiccatiRemainder.rMsum w (z⁻¹) M‖ ≤ C) :
    ‖floquetJ L a x r - Complex.I * ∑ n ∈ Finset.Icc 1 M,
        modeCoef L a (jEll x) (w n) * (z⁻¹) ^ n‖
      ≤ L * (physK L a * ‖x‖ * (physK L a * C)) := by
  have hpk : 0 ≤ physK L a := physK_nonneg (by linarith)
  have hs : QuantumNLS.RiccatiRemainder.rMsum w (z⁻¹) M +
      (r - QuantumNLS.RiccatiRemainder.rMsum w (z⁻¹) M) = r := by abel
  have hsplit := floquetJ_split hL ha x
    (QuantumNLS.RiccatiRemainder.rMsum w (z⁻¹) M)
    (r - QuantumNLS.RiccatiRemainder.rMsum w (z⁻¹) M)
  rw [hs, floquetJ_rMsum hL ha] at hsplit
  rw [hsplit, add_sub_cancel_left]
  exact QuantumNLS.RiccatiJBound.norm_J_le hL.le (mul_nonneg hpk (norm_nonneg x))
    (fun t _ => physRep_norm_le hL ha x t)
    (fun t _ => (physRep_norm_le hL ha _ t).trans (mul_le_mul_of_nonneg_left hrem hpk))

#print axioms integrated_remainder

#print axioms scaled_unique
#print axioms cauchy_eq_floquet
#print axioms physical_log_expansion
end QuantumNLS.SmoothScalarMomentsBinding

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.SmoothScalarMomentsBinding." ||
        n.toString.startsWith "_private.QuantumNLS.SmoothScalarMomentsBinding." then
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
