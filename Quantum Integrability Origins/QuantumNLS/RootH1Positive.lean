import QuantumNLS.RootH1PositiveEnergy

/-! R-F36DAC7F / lem:root-H1-positive, every printed clause. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory Set Filter Topology ComplexConjugate
open QuantumNLS.PhysicalTensor QuantumNLS.HaarResolvent
  QuantumNLS.RootH1RatioConvergence QuantumNLS.RootH1PositiveData
  QuantumNLS.RootH1PositiveAlgebra QuantumNLS.RootH1PositiveIntegrals
  QuantumNLS.RootH1PositiveSpectral QuantumNLS.RootH1PositiveEnergy
namespace QuantumNLS.RootH1Positive
variable {L : ℝ} [hLf : Fact (0 < L)]

/-- The positive regularized energy identity and derivative control for the
solution of lem:root-H1-ratio. The existential representative is periodic H¹;
its a.e. derivative is d. Thus the integral of ‖Yd‖² is exactly ‖(Yr)'‖₂².
The auxiliary a and s are the literal displayed formulas. No extra hypothesis
on u, the spectral measure, its moments, or any chain rule is added. -/
theorem root_H1_positive {κ : ℝ} (hκ : 0 < κ) (u : L2T L) (hu : u ≠ 0) :
    (∀ Y : ℝ, threshold κ u ≤ Y →
      ∃ g d : ℝ → ℂ,
        IsH1Rep L (ratioAt hκ.le u Y) g d ∧ g L = g 0 ∧
        (∀ᵐ t ∂volume.restrict (Icc 0 L), HasDerivAt g (d t) t) ∧
        (let s := fun t => ‖g t‖^2
         let a := fun t => (d t+(κ:ℂ)*(g t)^2*conj (d t))/((1-κ^2*(s t)^2:ℝ):ℂ)
         (∀ t ∈ Icc (0:ℝ) L, 3/4 ≤ 1-κ*s t ∧ 15/16 ≤ 1-κ^2*(s t)^2) ∧
         (∫ t : ℝ, Y^2*t^2/(Y^2+t^2) ∂(FullMass.Mmeas κ u)) =
           Y^2*(∫ t in (0:ℝ)..L, ‖a t‖^2)+κ*Y^4*(∫ t in (0:ℝ)..L, (s t)^2/(1-κ*s t)^2) ∧
         (∫ t in (0:ℝ)..L, ‖(Y:ℂ)*d t‖^2) ≤
           (1+κ*‖ratioInfAt hκ.le u Y‖^2)^2*
             (∫ t : ℝ, Y^2*t^2/(Y^2+t^2) ∂(FullMass.Mmeas κ u)))) ∧
    Tendsto (fun Y : ℝ => κ*‖ratioInfAt hκ.le u Y‖^2) atTop (nhds 0) := by
  refine ⟨?_,delta_tendsto hκ u hu⟩
  intro Y hY
  obtain ⟨g,d,hr,hper,hg,hder,he,hn,hb⟩ := curve hκ u hu hY
  refine ⟨g,d,hr,hper,hder,?_⟩
  dsimp only
  have hE := (energy hκ u hu hY hr hper hg hder he hb).1
  have hD := derivative_control hκ u hu hY hr hper hg hder he hn hb
  refine ⟨?_,?_,hD⟩
  · intro t ht
    have hh := den_bounds hκ.le (hb t ht)
    simpa only [← pow_mul] using hh
  · simpa only [aux,w4,kernel,← pow_mul] using hE

#print axioms root_H1_positive
end QuantumNLS.RootH1Positive

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootH1Positive." ||
        n.toString.startsWith "_private.QuantumNLS.RootH1Positive." then
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
