import QuantumNLS.RootH1Ratio

/-! Ordinary absolutely continuous chain rules and periodic cancellations.
The application proves the derivative, integrability and denominator bounds. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory Set Filter Topology ComplexConjugate
open QuantumNLS.RootH1RatioAC
namespace QuantumNLS.RootH1PositiveChain

lemma ac_sq {L : ℝ} {g : ℝ → ℂ} (hg : AbsolutelyContinuousOnInterval g 0 L) :
    AbsolutelyContinuousOnInterval (fun t => ‖g t‖^2) 0 L := by
  have hn := (lipschitzWith_one_norm : LipschitzWith 1 (norm : ℂ → ℝ)).comp_absolutelyContinuousOnInterval hg
  convert hn.mul hn using 1
  ext t
  simp only [Function.comp_def,pow_two,Pi.mul_apply]

lemma ac_comp {L b : ℝ} {s F : ℝ → ℝ}
    (hs : AbsolutelyContinuousOnInterval s 0 L)
    (hrange : MapsTo s (uIcc 0 L) (Icc 0 b))
    (hF : ContDiffOn ℝ 1 F (Icc 0 b)) :
    AbsolutelyContinuousOnInterval (fun t => F (s t)) 0 L := by
  obtain ⟨K,hK⟩ := hF.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
  exact hK.comp_absolutelyContinuousOnInterval hrange hs

lemma periodic_cancel {L : ℝ} (hL : 0 ≤ L) {F q : ℝ → ℝ}
    (hF : AbsolutelyContinuousOnInterval F 0 L) (hper : F L = F 0)
    (hq : IntervalIntegrable q volume 0 L)
    (hd : ∀ᵐ t ∂volume.restrict (Icc 0 L), HasDerivAt F (q t) t) :
    (∫ t in (0:ℝ)..L, q t) = 0 := by
  have he := ac_integral_eq hL hF hq hd (x := L) ⟨hL,le_rfl⟩
  rw [hper] at he
  linarith

lemma chain_integrable {L κ : ℝ} (hL : 0 ≤ L) {g d : ℝ → ℂ}
    (hg : AbsolutelyContinuousOnInterval g 0 L)
    (hi : IntervalIntegrable d volume 0 L)
    (hb : ∀ t ∈ Icc (0:ℝ) L, κ*‖g t‖^2 ≤ 1/4) :
    IntervalIntegrable (fun t => (conj (g t)*d t).re/(1-κ*‖g t‖^2)) volume 0 L ∧
    IntervalIntegrable (fun t => (conj (g t)*d t).re/(1-κ*‖g t‖^2)^2) volume 0 L := by
  have hc := hg.continuousOn
  have hq : IntervalIntegrable (fun t => (conj (g t)*d t).re) volume 0 L := by
    have hh := hi.continuousOn_mul (Complex.continuous_conj.comp_continuousOn hc)
    exact ⟨Complex.reCLM.integrable_comp hh.1,Complex.reCLM.integrable_comp hh.2⟩
  have hden : ContinuousOn (fun t => (1-κ*‖g t‖^2)⁻¹) (uIcc 0 L) := by
    apply (continuousOn_const.sub (continuousOn_const.mul (hc.norm.pow 2))).inv₀
    intro t ht
    have hh := hb t (by simpa [uIcc_of_le hL] using ht)
    change 1-κ*‖g t‖^2 ≠ 0
    linarith
  constructor
  · simpa only [div_eq_mul_inv] using hq.mul_continuousOn hden
  · simpa only [div_eq_mul_inv,inv_pow,Pi.pow_apply] using hq.mul_continuousOn (hden.pow 2)

/-- Both exact derivative terms vanish at the printed rough regularity. -/
theorem cancellations {L κ : ℝ} (hL : 0 ≤ L) (hκ : 0 < κ) {g d : ℝ → ℂ}
    (hg : AbsolutelyContinuousOnInterval g 0 L) (hper : g L = g 0)
    (hi : IntervalIntegrable d volume 0 L)
    (hd : ∀ᵐ t ∂volume.restrict (Icc 0 L), HasDerivAt g (d t) t)
    (hb : ∀ t ∈ Icc (0:ℝ) L, κ*‖g t‖^2 ≤ 1/4) :
    (∫ t in (0:ℝ)..L, (conj (g t)*d t).re/(1-κ*‖g t‖^2)) = 0 ∧
    (∫ t in (0:ℝ)..L, (conj (g t)*d t).re/(1-κ*‖g t‖^2)^2) = 0 := by
  let s : ℝ → ℝ := fun t => ‖g t‖^2
  let q : ℝ → ℝ := fun t => (conj (g t)*d t).re
  have hs := ac_sq hg
  have hrange : MapsTo s (uIcc 0 L) (Icc 0 (1/(4*κ))) := by
    intro t ht
    refine ⟨sq_nonneg _,?_⟩
    have hh := hb t (by simpa [uIcc_of_le hL] using ht)
    dsimp [s]
    apply (le_div_iff₀ (by positivity : 0 < 4*κ)).mpr
    linarith
  have hden : ∀ x ∈ Icc (0:ℝ) (1/(4*κ)), 1-κ*x ≠ 0 := by
    intro x hx
    have hh := (le_div_iff₀ (by positivity : 0 < 4*κ)).mp hx.2
    linarith
  have hF1 : ContDiffOn ℝ 1 (fun x : ℝ => Real.log (1-κ*x)) (Icc 0 (1/(4*κ))) := by
    intro x hx
    exact ((contDiffAt_const.sub (contDiffAt_const.mul contDiffAt_id)).log (hden x hx)).contDiffWithinAt
  have hF2 : ContDiffOn ℝ 1 (fun x : ℝ => x/(1-κ*x)) (Icc 0 (1/(4*κ))) := by
    intro x hx
    exact (contDiffAt_id.div (contDiffAt_const.sub (contDiffAt_const.mul contDiffAt_id)) (hden x hx)).contDiffWithinAt
  have hac1 := ac_comp hs hrange hF1
  have hac2 := ac_comp hs hrange hF2
  have hiq := chain_integrable hL hg hi hb
  have hD : ∀ᵐ t ∂volume.restrict (Icc 0 L), HasDerivAt s (2*q t) t := by
    filter_upwards [hd] with t ht
    simpa only [s,q,Complex.inner,mul_comm] using ht.norm_sq
  have hd1 : ∀ᵐ t ∂volume.restrict (Icc 0 L),
      HasDerivAt (fun x => Real.log (1-κ*s x)) ((-2*κ)*(q t/(1-κ*s t))) t := by
    filter_upwards [hD,ae_restrict_mem measurableSet_Icc] with t ht hti
    have hn : 1-κ*s t ≠ 0 := by have := hb t hti; dsimp [s]; linarith
    have hh := (((hasDerivAt_const t 1).sub (ht.const_mul κ)).log hn)
    apply hh.congr_deriv
    change (0-κ*(2*q t))/(1-κ*s t) = _
    ring
  have hd2 : ∀ᵐ t ∂volume.restrict (Icc 0 L),
      HasDerivAt (fun x => s x/(1-κ*s x)) (2*(q t/(1-κ*s t)^2)) t := by
    filter_upwards [hD,ae_restrict_mem measurableSet_Icc] with t ht hti
    have hn : 1-κ*s t ≠ 0 := by have := hb t hti; dsimp [s]; linarith
    have hh := ht.div ((hasDerivAt_const t 1).sub (ht.const_mul κ)) hn
    apply hh.congr_deriv
    change (2*q t*(1-κ*s t)-s t*(0-κ*(2*q t)))/(1-κ*s t)^2 = _
    field_simp
    ring
  have he1 := periodic_cancel hL hac1 (by simp only [hper]) (hiq.1.const_mul (-2*κ)) hd1
  have he2 := periodic_cancel hL hac2 (by simp only [hper]) (hiq.2.const_mul 2) hd2
  rw [intervalIntegral.integral_const_mul] at he1 he2
  constructor <;> dsimp only [q,s] at * <;> nlinarith

#print axioms ac_sq
#print axioms ac_comp
#print axioms periodic_cancel
#print axioms chain_integrable
#print axioms cancellations
end QuantumNLS.RootH1PositiveChain

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootH1PositiveChain." ||
        n.toString.startsWith "_private.QuantumNLS.RootH1PositiveChain." then
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
