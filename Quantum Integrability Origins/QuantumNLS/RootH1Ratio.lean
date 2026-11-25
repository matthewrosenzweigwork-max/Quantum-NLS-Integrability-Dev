import QuantumNLS.RootH1RatioConvergence
import QuantumNLS.RootH1RatioCauchy

/-! R-D24009D4 / lem:root-H1-ratio, all printed clauses on the physical carriers. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory Set Filter Topology ComplexConjugate
open scoped InnerProductSpace
open QuantumNLS.PhysicalTensor QuantumNLS.RootH1RatioOperator
  QuantumNLS.RootH1RatioNonlinear QuantumNLS.RootH1RatioContraction
  QuantumNLS.RootH1RatioBounds QuantumNLS.RootH1RatioConvergence
namespace QuantumNLS.RootH1Ratio
variable {L : ℝ} [hLf : Fact (0 < L)]

lemma inner_interval (u v : L2T L) : inner ℂ u v =
    ∫ t in (0:ℝ)..L, conj (u (t:AddCircle L))*v (t:AddCircle L) := by
  rw [L2.inner_def]
  simp only [RCLike.inner_apply']
  have h := AddCircle.intervalIntegral_preimage L 0 (fun x => conj (u x)*v x)
  simpa only [zero_add] using h.symm

lemma infinityResolvent_smul {Y : ℝ} (hY : 0 < Y) (hlog : Real.log 3 ≤ Y*L)
    (a : ℂ) (f : L2T L) : infinityResolvent hY hlog (a • f) = a • infinityResolvent hY hlog f := by
  apply Lp.ext
  filter_upwards [coe_infinityResolvent hY hlog (a • f),coe_infinityResolvent hY hlog f,
    Lp.coeFn_smul a (infinityResolvent hY hlog f),
    Lp.coeFn_smul a (RootH1RatioOperator.resolvent Y f)] with x h1 h2 h3 h4
  have he : RootH1RatioOperator.resolvent Y (a • f) = a • RootH1RatioOperator.resolvent Y f :=
    (RootH1RatioOperator.resolvent Y).map_smul a f
  rw [h1,h3,Pi.smul_apply,smul_eq_mul,h2,he,h4,Pi.smul_apply,smul_eq_mul]

lemma ratioMap_eq_printed {Y : ℝ} (hY : 0 < Y) (hlog : Real.log 3 ≤ Y*L)
    (κ : ℝ) (u : L2T L) (r : Linfty L) :
    ratioMap hY hlog κ u r = infinityResolvent hY hlog u -
      (κ:ℂ) • infinityResolvent hY hlog (cubic u r) := by
  rw [ratioMap,forcing,← infinityResolvent_sub,infinityResolvent_smul]

/-- The printed small-ratio lemma, including uniqueness, periodic H¹, its a.e.
differential equation, both quantitative bounds, the full real-parameter L²
limit and the exact Cauchy identity. There are no hypotheses beyond L,κ>0,
u≠0 in physical L² and the printed height threshold. -/
theorem root_H1_ratio {κ : ℝ} (hκ : 0 < κ) (u : L2T L) (hu : u ≠ 0) :
    (∀ Y : ℝ, ∀ hY0 : max 1 (max (Real.log 3/L) (16*κ*‖u‖^2)) ≤ Y,
      let hY := (height_spec u hY0).1
      let hlog := (height_spec u hY0).2.1
      ‖ratioInfAt hκ.le u Y‖ ≤ 2*Real.sqrt (‖u‖^2/Y) ∧
      (infinityResolvent hY hlog u - (κ:ℂ) • infinityResolvent hY hlog (cubic u (ratioInfAt hκ.le u Y))) = ratioInfAt hκ.le u Y ∧
      (∀ s : Linfty L, ‖s‖ ≤ 2*Real.sqrt (‖u‖^2/Y) → (infinityResolvent hY hlog u - (κ:ℂ) • infinityResolvent hY hlog (cubic u s)) = s →
        s = ratioInfAt hκ.le u Y) ∧
      (ratioAt hκ.le u Y =ᵐ[volume] ratioInfAt hκ.le u Y) ∧
      (∃ g d : ℝ → ℂ,
        HaarResolvent.IsH1Rep L (ratioAt hκ.le u Y) g d ∧ g L = g 0 ∧
        ∀ᵐ x : AddCircle L, d (HaarResolvent.rep1 L x) = u x-(Y:ℂ)*ratioAt hκ.le u Y x-
          (κ:ℂ)*conj (u x)*(ratioAt hκ.le u Y x)^2) ∧
      κ*‖ratioInfAt hκ.le u Y‖^2 ≤ 1/4 ∧
      ‖ratioAt hκ.le u Y‖ ≤ 5*‖u‖/(4*Y) ∧
      CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) ((Y:ℂ)*Complex.I) =
        -Complex.I*(∫ t in (0:ℝ)..L, conj (u (t:AddCircle L))*ratioAt hκ.le u Y (t:AddCircle L))) ∧
    Tendsto (fun Y : ℝ => (Y:ℂ) • ratioAt hκ.le u Y) atTop (nhds u) := by
  refine ⟨?_, nonlinear_strong hκ.le u⟩
  intro Y hY0
  have hh := height_spec u hY0
  dsimp only
  simp only [← ratioMap_eq_printed]
  rw [ratioAt_eq hκ.le u hY0,ratioInfAt_eq hκ.le u hY0]
  refine ⟨?_,(ratio_spec hh.1 hh.2.1 hκ.le u hh.2.2).2,?_,
    ratioL2_ae hh.1 hh.2.1 hκ.le u hh.2.2,?_,
    ratio_small hh.1 hh.2.1 hκ.le u hh.2.2,
    ratioL2_norm hh.1 hh.2.1 hκ.le u hh.2.2,?_⟩
  · rw [← radius_printed hh.1]
    exact (ratio_spec hh.1 hh.2.1 hκ.le u hh.2.2).1
  · intro s hs hf
    rw [← radius_printed hh.1] at hs
    exact ratio_unique hh.1 hh.2.1 hκ.le u hh.2.2 hs hf
  · obtain ⟨g,d,hrep,hper,ha⟩ := ratio_H1 hh.1 hh.2.1 hκ.le u hh.2.2
    refine ⟨g,d,hrep,by simpa only [one_mul] using hper,?_⟩
    filter_upwards [ha,hrep.1,ratioL2_ae hh.1 hh.2.1 hκ.le u hh.2.2,
      RootH1RatioCompanion.coe_forcing κ u (ratio hh.1 hh.2.1 hκ.le u hh.2.2)]
      with x hax hxg hxr hxf
    rw [hxf,← hxr] at hax
    have he : Complex.I*((Y:ℂ)*Complex.I) = -(Y:ℂ) := by
      linear_combination (Y:ℂ)*Complex.I_mul_I
    rw [he,← hxg] at hax
    linear_combination -hax
  · rw [← inner_interval]
    exact RootH1RatioCauchy.ratio_cauchy hh.1 hh.2.1 hκ u hu hh.2.2

#print axioms inner_interval
#print axioms infinityResolvent_smul
#print axioms ratioMap_eq_printed
#print axioms root_H1_ratio
end QuantumNLS.RootH1Ratio

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootH1Ratio." ||
        n.toString.startsWith "_private.QuantumNLS.RootH1Ratio." then
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
