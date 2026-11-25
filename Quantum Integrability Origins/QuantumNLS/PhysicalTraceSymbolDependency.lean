import QuantumNLS.PhysicalL2Normalization
import QuantumNLS.PhysicalL2BandGeometry
import QuantumNLS.PhysicalVacuumSourceFacts

/-! The exact, unproved dependency assigned to sonnet_fourier (R-7E0532E7,
item 3). This module does not prove the trace-symbol identity. Its high
half-plane is the existing quantum high half-plane at the actual mass.
Boundary geometry below is a scalar lemma, not an asserted physical boundary
extension or a SourceFacts inhabitant. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
open MeasureTheory Filter Topology Set
namespace QuantumNLS.PhysicalTraceSymbolDependency
open PhysicalTensor (L2T)
variable {L κ : ℝ} [Fact (0 < L)]

/-- Sole external identity dependency, for the actual unnormalized input.
No boundary extension, density, or SourceFacts is hidden in this proposition. -/
def TraceSymbolIdentity (L κ : ℝ) [Fact (0 < L)] (u : L2T L) : Prop :=
  ∀ z : ℂ, RootMeasureComplex.HighHalf L (κ * ‖u‖ ^ 2) z →
    Complex.exp (-(Complex.I * z * L / 2)) *
      NormalizedTransfer.productSymbol L κ u z = L2SpatialTransfer.discriminant κ u z

/-- The named dependency gives the actual canonical quantum-phase identity
on the specified high half-plane; no alternative measure is chosen. -/
theorem high_cosine (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0)
    (htrace : TraceSymbolIdentity L κ u) {z : ℂ}
    (hz : RootMeasureComplex.HighHalf L (κ * ‖u‖ ^ 2) z) :
    2 * Complex.cos (SpatialTransfer.boundaryPhase L κ (PhysicalQuantumMeasure.measure hκ u) z) =
      L2SpatialTransfer.discriminant κ u z :=
  (PhysicalL2Normalization.cosine_physical_productSymbol hκ hu hz).trans (htrace z hz)

/-- For a nonzero input the dependency is exactly the high quantum cosine
identity, with the already constructed canonical measure. -/
theorem traceSymbolIdentity_iff_high_cosine (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) :
    TraceSymbolIdentity L κ u ↔
      ∀ z : ℂ, RootMeasureComplex.HighHalf L (κ * ‖u‖ ^ 2) z →
        2 * Complex.cos (SpatialTransfer.boundaryPhase L κ
          (PhysicalQuantumMeasure.measure hκ u) z) = L2SpatialTransfer.discriminant κ u z := by
  constructor
  · exact fun h z hz => high_cosine hκ hu h hz
  · intro h z hz
    exact (PhysicalL2Normalization.cosine_physical_productSymbol hκ hu hz).symm.trans (h z hz)

/-- The identity is invariant under the literal full-mass preparation.
This transports a future unit-input proof without reproving its kernel calculation. -/
theorem traceSymbolIdentity_normalization (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) :
    TraceSymbolIdentity L (PhysicalQuantumMeasure.preparation hκ u hu).effectiveCoupling
      (PhysicalQuantumMeasure.preparation hκ u hu).unitProfile ↔ TraceSymbolIdentity L κ u := by
  have hn : ‖(PhysicalQuantumMeasure.preparation hκ u hu).unitProfile‖ = 1 :=
    (PhysicalQuantumMeasure.preparation hκ u hu).norm_unitProfile
  constructor
  · intro h z hz
    have hz' : RootMeasureComplex.HighHalf L
        ((PhysicalQuantumMeasure.preparation hκ u hu).effectiveCoupling *
          ‖(PhysicalQuantumMeasure.preparation hκ u hu).unitProfile‖ ^ 2) z := by
      simpa only [hn, one_pow, mul_one, PhysicalQuantumMeasure.effectiveCoupling_eq] using hz
    have hh := h z hz'
    rw [PhysicalL2Normalization.productSymbol_normalization hκ hu,
      PhysicalL2Normalization.discriminant_normalization hκ hu] at hh
    exact hh
  · intro h z hz
    have hz' : RootMeasureComplex.HighHalf L (κ * ‖u‖ ^ 2) z := by
      simpa only [hn, one_pow, mul_one, PhysicalQuantumMeasure.effectiveCoupling_eq] using hz
    rw [PhysicalL2Normalization.productSymbol_normalization hκ hu,
      PhysicalL2Normalization.discriminant_normalization hκ hu]
    exact h z hz'

/-- The imaginary cosine identity in real coordinates. -/
theorem imaginary_cosine (z : ℂ) :
    (2 * Complex.cos z).im = -2 * Real.sin z.re * Real.sinh z.im := by
  rw [Complex.cos_eq]
  simp [Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re,
    Complex.cos_ofReal_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im,
    Complex.cosh_ofReal_re, Complex.cosh_ofReal_im, Complex.sinh_ofReal_re,
    Complex.sinh_ofReal_im]
  ring

/-- At a real-trace gap, every boundary value lies over an integer multiple
of pi. This is derived from the cosine equation, rather than supplied as a field. -/
theorem gap_value_integer_pi {z : ℂ} {d : ℝ}
    (hcos : 2 * Complex.cos z = (d : ℂ)) (hgap : 2 < |d|) :
    ∃ k : ℤ, z.re = (k : ℝ) * Real.pi := by
  have him : -2 * Real.sin z.re * Real.sinh z.im = 0 := by
    rw [← imaginary_cosine, hcos]; simp
  have hy : z.im ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hcos
    rw [BandPhaseBridge.real_cosine, hz, Real.cosh_zero, mul_one] at hre
    simp only [Complex.ofReal_re] at hre
    have hd : |d| ≤ 2 := by
      rw [← hre, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      nlinarith [Real.abs_cos_le_one z.re]
    linarith
  have hs : Real.sin z.re = 0 := by
    have hsy : Real.sinh z.im ≠ 0 := by simpa using hy
    rcases mul_eq_zero.mp him with h | h
    · exact (mul_eq_zero.mp h).resolve_left (by norm_num)
    · exact (hsy h).elim
  obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hs
  exact ⟨k, hk.symm⟩

/-- Continuity and the boundary cosine identity alone force one integer-pi
value on each open gap interval. Monotonicity is not an input. -/
theorem gap_constancy {γ : ℝ → ℂ} {d : ℝ → ℝ} (hc : Continuous γ)
    (hcos : ∀ x, 2 * Complex.cos (γ x) = (d x : ℂ))
    {a b : ℝ} (hab : a < b) (hg : ∀ x ∈ Ioo a b, 2 < |d x|) :
    ∃ k : ℤ, ∀ x ∈ Ioo a b, (γ x).re = (k : ℝ) * Real.pi := by
  let f : ℝ → ℝ := fun x => (γ x).re
  have hf : Continuous f := Complex.continuous_re.comp hc
  let S : Set ℝ := Set.range (fun k : ℤ => (k : ℝ) * Real.pi)
  have hmaps : f '' Ioo a b ⊆ S := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨k, hk⟩ := gap_value_integer_pi (hcos x) (hg x hx)
    exact ⟨k, hk.symm⟩
  have hpre : IsPreconnected (f '' Ioo a b) := isPreconnected_Ioo.image f hf.continuousOn
  have hsub : (f '' Ioo a b).Subsingleton :=
    (Set.countable_range (fun k : ℤ => (k : ℝ) * Real.pi)).isTotallyDisconnected _ hmaps hpre
  let x₀ := (a + b) / 2
  have hx₀ : x₀ ∈ Ioo a b := ⟨by dsimp [x₀]; linarith, by dsimp [x₀]; linarith⟩
  obtain ⟨k, hk⟩ := gap_value_integer_pi (hcos x₀) (hg x₀ hx₀)
  refine ⟨k, fun x hx => ?_⟩
  exact (hsub (mem_image_of_mem f hx) (mem_image_of_mem f hx₀)).trans hk

end QuantumNLS.PhysicalTraceSymbolDependency

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.PhysicalTraceSymbolDependency.TraceSymbolIdentity
#print axioms QuantumNLS.PhysicalTraceSymbolDependency.high_cosine
#print axioms QuantumNLS.PhysicalTraceSymbolDependency.traceSymbolIdentity_iff_high_cosine
#print axioms QuantumNLS.PhysicalTraceSymbolDependency.traceSymbolIdentity_normalization
#print axioms QuantumNLS.PhysicalTraceSymbolDependency.imaginary_cosine
#print axioms QuantumNLS.PhysicalTraceSymbolDependency.gap_value_integer_pi
#print axioms QuantumNLS.PhysicalTraceSymbolDependency.gap_constancy

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.PhysicalTraceSymbolDependency." then
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
