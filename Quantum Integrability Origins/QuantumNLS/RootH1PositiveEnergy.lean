import QuantumNLS.RootH1PositiveData
import QuantumNLS.RootH1PositiveIntegrals
import QuantumNLS.RootH1PositiveSpectral

/-! All auxiliary hypotheses are discharged for the physical ratio. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Set Filter Topology ComplexConjugate
open QuantumNLS.PhysicalTensor QuantumNLS.HaarResolvent QuantumNLS.RootH1Ratio
  QuantumNLS.RootH1RatioConvergence QuantumNLS.RootH1RatioCompanion
  QuantumNLS.RootH1PositiveAlgebra QuantumNLS.RootH1PositiveIntegrals
  QuantumNLS.RootH1PositiveSpectral
namespace QuantumNLS.RootH1PositiveEnergy
variable {L : ℝ} [hLf : Fact (0 < L)]

lemma cauchy_real {κ Y : ℝ} (hκ : 0 < κ) (u : L2T L) (hu : u ≠ 0)
    (hY : threshold κ u ≤ Y) {g d : ℝ → ℂ}
    (hr : IsH1Rep L (ratioAt hκ.le u Y) g d)
    (hg : AbsolutelyContinuousOnInterval g 0 L) :
    (CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) ((Y:ℂ)*Complex.I)).im =
      -(∫ t in (0:ℝ)..L, (conj (u (t:AddCircle L))*g t).re) := by
  rcases (root_H1_ratio hκ u hu).1 Y hY with ⟨_,_,_,_,_,_,_,hc⟩
  rw [← inner_interval,pairing_eq u _ hr.1] at hc
  have huI := intInt_psi0 L u
  have hcI : IntervalIntegrable (fun t => conj (u (t:AddCircle L))) volume 0 L :=
    ⟨Complex.conjCLE.toContinuousLinearMap.integrable_comp huI.1,
      Complex.conjCLE.toContinuousLinearMap.integrable_comp huI.2⟩
  have hpI := hcI.mul_continuousOn hg.continuousOn
  have hre := intervalIntegral.intervalIntegral_re hpI
  change (∫ t in (0:ℝ)..L, (conj (u (t:AddCircle L))*g t).re) =
    (∫ t in (0:ℝ)..L, conj (u (t:AddCircle L))*g t).re at hre
  rw [hre,hc]
  simp

/-- The exact identity on the physical carriers, with every side integrable. -/
theorem energy {κ Y : ℝ} (hκ : 0 < κ) (u : L2T L) (hu : u ≠ 0)
    (hY : threshold κ u ≤ Y) {g d : ℝ → ℂ}
    (hr : IsH1Rep L (ratioAt hκ.le u Y) g d) (hper : g L = g 0)
    (hg : AbsolutelyContinuousOnInterval g 0 L)
    (hder : ∀ᵐ t ∂volume.restrict (Icc 0 L), HasDerivAt g (d t) t)
    (he : ∀ᵐ (t : ℝ) ∂volume.restrict (Icc 0 L),
      d t = u (t:AddCircle L)-(Y:ℂ)*g t-(κ:ℂ)*conj (u (t:AddCircle L))*(g t)^2)
    (hb : ∀ t ∈ Icc (0:ℝ) L, κ*‖g t‖^2 ≤ 1/4) :
    (∫ t, kernel Y t ∂(FullMass.Mmeas κ u)) =
      Y^2*(∫ t in (0:ℝ)..L, ‖aux κ (g t) (d t)‖^2)+κ*Y^4*(∫ t in (0:ℝ)..L, w4 κ g t) ∧
    IntervalIntegrable (fun t => ‖aux κ (g t) (d t)‖^2) volume 0 L := by
  have hu2 : MemLp (fun t : ℝ => u (t:AddCircle L)) 2 (volume.restrict (Icc 0 L)) := by
    change MemLp (psi0 L u) 2 (volume.restrict (Icc 0 L))
    simpa only [restrict_Ioc_eq_restrict_Icc] using memLp_psi0 L u
  have hd2 : MemLp d 2 (volume.restrict (Icc 0 L)) := by
    simpa only [restrict_Ioc_eq_restrict_Icc] using hr.2.1
  have hs := splits hLf.out.le hκ hg hper hu2 hd2 hder he hb
  have hm : ‖u‖^2 = Y^2*(∫ t in (0:ℝ)..L, w2 κ g t)+(∫ t in (0:ℝ)..L, ‖aux κ (g t) (d t)‖^2) := by
    rw [← RootH1RatioOperator.integral_profile_sq u]
    exact hs.2.1
  have hw := continuous_weights hκ.le (by simpa [uIcc_of_le hLf.out.le] using hg.continuousOn) hb
  have hw1 : IntervalIntegrable (w1 κ g) volume 0 L := hw.1.intervalIntegrable_of_Icc hLf.out.le
  have hw2 : IntervalIntegrable (w2 κ g) volume 0 L := hw.2.1.intervalIntegrable_of_Icc hLf.out.le
  have hdiff : (∫ t in (0:ℝ)..L, w2 κ g t)-(∫ t in (0:ℝ)..L, w1 κ g t) =
      κ*(∫ t in (0:ℝ)..L, w4 κ g t) := by
    rw [← intervalIntegral.integral_sub hw2 hw1,← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    simpa only [w2,w1,w4,mul_div_assoc] using weight_difference κ (g t)
  refine ⟨?_,hs.2.2⟩
  rw [physical_identity (height_spec u hY).1 u,cauchy_real hκ u hu hY hr hg,hs.1,hm]
  linear_combination Y^4*hdiff

/-- The squared L² norm of the actual derivative of Yr is controlled by the spectral energy. -/
theorem derivative_control {κ Y : ℝ} (hκ : 0 < κ) (u : L2T L) (hu : u ≠ 0)
    (hY : threshold κ u ≤ Y) {g d : ℝ → ℂ}
    (hr : IsH1Rep L (ratioAt hκ.le u Y) g d) (hper : g L = g 0)
    (hg : AbsolutelyContinuousOnInterval g 0 L)
    (hder : ∀ᵐ t ∂volume.restrict (Icc 0 L), HasDerivAt g (d t) t)
    (he : ∀ᵐ (t : ℝ) ∂volume.restrict (Icc 0 L),
      d t = u (t:AddCircle L)-(Y:ℂ)*g t-(κ:ℂ)*conj (u (t:AddCircle L))*(g t)^2)
    (hn : ∀ t ∈ Icc (0:ℝ) L, ‖g t‖ ≤ ‖ratioInfAt hκ.le u Y‖)
    (hb : ∀ t ∈ Icc (0:ℝ) L, κ*‖g t‖^2 ≤ 1/4) :
    (∫ t in (0:ℝ)..L, ‖(Y:ℂ)*d t‖^2) ≤
      (1+κ*‖ratioInfAt hκ.le u Y‖^2)^2*(∫ t, kernel Y t ∂(FullMass.Mmeas κ u)) := by
  have hs := energy hκ u hu hY hr hper hg hder he hb
  have hiD : IntervalIntegrable (fun t => ‖d t‖^2) volume 0 L :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hLf.out.le).mpr (hr.2.1.integrable_norm_pow (by decide))
  have hm := intervalIntegral.integral_mono_on hLf.out.le hiD
    (hs.2.const_mul ((1+κ*‖ratioInfAt hκ.le u Y‖^2)^2)) (fun t ht =>
      derivative_le hκ.le (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hn t ht) 2) hκ.le)
        (den_ne hκ.le (hb t ht)).2)
  rw [intervalIntegral.integral_const_mul] at hm
  have hpos : 0 ≤ κ*Y^4*(∫ t in (0:ℝ)..L, w4 κ g t) := by
    apply mul_nonneg (mul_nonneg hκ.le (by positivity))
    apply intervalIntegral.integral_nonneg hLf.out.le
    intro t _
    unfold w4
    positivity
  have hE : Y^2*(∫ t in (0:ℝ)..L, ‖aux κ (g t) (d t)‖^2) ≤
      (∫ t, kernel Y t ∂(FullMass.Mmeas κ u)) := by rw [hs.1]; linarith
  calc
    (∫ t in (0:ℝ)..L, ‖(Y:ℂ)*d t‖^2) = Y^2*(∫ t in (0:ℝ)..L, ‖d t‖^2) := by
      simp only [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
      exact intervalIntegral.integral_const_mul _ _
    _ ≤ Y^2*((1+κ*‖ratioInfAt hκ.le u Y‖^2)^2*(∫ t in (0:ℝ)..L, ‖aux κ (g t) (d t)‖^2)) :=
      mul_le_mul_of_nonneg_left hm (sq_nonneg _)
    _ = (1+κ*‖ratioInfAt hκ.le u Y‖^2)^2*(Y^2*(∫ t in (0:ℝ)..L, ‖aux κ (g t) (d t)‖^2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hE (sq_nonneg _)

#print axioms cauchy_real
#print axioms energy
#print axioms derivative_control
end QuantumNLS.RootH1PositiveEnergy

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootH1PositiveEnergy." ||
        n.toString.startsWith "_private.QuantumNLS.RootH1PositiveEnergy." then
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
