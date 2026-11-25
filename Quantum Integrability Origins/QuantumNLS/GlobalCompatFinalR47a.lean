import QuantumNLS.GlobalCompatUniquenessR47a
import QuantumNLS.GlobalCompatUniformR47a

/-!
R-CA92819A `thm:global-compatibility`, compatibility.tex:12.
`global_compatibility` is the complete named theorem. The constants and reviewed
local chart are obtained from accepted LOCAL-023, and an extending global
family exists by accepted R-F5355ABD. Every family satisfying exactly the
printed extension premise has all the conclusions in `Compatibility`.
The ball estimates are stated pointwise for EVERY point of each CLOSED ball;
this is the printed supremum assertion, including its boundary, and does not
require the supremum to be attained. `UniformC1` states the full epsilon limit
for both maps and both derivatives. Zero strata are explicit equivalences;
continuity and inverse identities hold on the entire spaces.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 8000000
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open scoped ComplexConjugate Topology
open Set Metric Filter
namespace QuantumNLS.GlobalCompatR47a
open PhysicalTensor (L2T)
open D01LocalPrimitive (K)
open Local021 (Setting SymKind Mono)
open RF535Final (Local023Body)
open RootIndexedMasses (masses)
open QuantumNLS.Fourier (fourierL2 modeLp)
open LocalSpectral (pm)
open ResetNormalizationUniqueness (Cphys)
variable {L : ℝ} [Fact (0 < L)]

/-- Every clause of the printed compatibility theorem. -/
def Compatibility (d CL : ℝ) (Φ : ℝ → L2T L → K) (Ψ : ℝ → K → L2T L) : Prop :=
  (∀ (κ : ℝ) (hκ : 0 < κ),
    -- Five physical covariance identities with exactly the printed indices.
    (∀ (u : L2T L) (n : ℤ),
      (∀ γ : ℝ, Φ κ (Complex.exp ((γ:ℂ)*Complex.I) • u) n =
        Complex.exp ((γ:ℂ)*Complex.I) * Φ κ u n) ∧
      (∀ y : ℝ, Φ κ (BornTranslation.trans y u) n =
        Complex.exp (Complex.I * ((pm L n:ℝ):ℂ) * (y:ℂ)) * Φ κ u n) ∧
      (∀ k : ℤ, Φ κ (RootMassBoostSymbol.boost k u) n = Φ κ u (n-k)) ∧
      Φ κ (ResetNormalizationUniqueness.reflectR L u) n = Φ κ u (-n) ∧
      Φ κ (star u) n = conj (Φ κ u (-n))) ∧
    fderiv ℝ (Φ κ) 0 = Setting.Fcl L ∧
    (∀ (a : ℂ) (k : ℤ), Φ κ (a • modeLp L k) = a • lp.single 2 k (1:ℂ)) ∧
    (∀ u : L2T L, Φ κ (Cphys L u) = star (Φ κ u)) ∧
    -- The joint parameter assertions hold for every point with κ>0.
    (∀ u : L2T L, AnalyticAt ℝ (fun p : ℝ × L2T L => Φ p.1 p.2) (κ,u)) ∧
    (∀ z : K, AnalyticAt ℝ (fun p : ℝ × K => Ψ p.1 p.2) (κ,z)) ∧
    -- The exact derivative and map estimates, also for the inverse.
    (∀ R : ℝ, κ*R^2 < d^2 →
      (∀ u : L2T L, ‖u‖ ≤ R →
        ‖fderiv ℝ (Φ κ) u - Setting.Fcl L‖ ≤ CL*κ*R^2 ∧
        ‖Φ κ u - Setting.Fcl L u‖ ≤ (CL/3)*κ*R^3) ∧
      (∀ z : K, ‖z‖ ≤ R →
        ‖fderiv ℝ (Ψ κ) z - ((Setting.Fcle L).symm : K →L[ℝ] L2T L)‖ ≤ CL*κ*R^2 ∧
        ‖Ψ κ z - (Setting.Fcle L).symm z‖ ≤ (CL/3)*κ*R^3)) ∧
    -- The competing chart has no local-agreement hypothesis.
    (∀ G : L2T L → K, StrongSymplectic.IsStronglySymplectic G →
      (∀ u, AnalyticAt ℝ G u) →
      (∀ u n, ‖G u n‖^2 = (masses hκ u).1 n) →
      (∀ v, fderiv ℝ G 0 v = fourierL2 L v) →
      (∀ u, G (Cphys L u) = star (G u)) → G = Φ κ) ∧
    -- All zero actions, arbitrary infinite support, and their boundaries.
    (∀ u n, (masses hκ u).1 n = 0 ↔ Φ κ u n = 0) ∧
    (∀ z n, (masses hκ (Ψ κ z)).1 n = 0 ↔ z n = 0) ∧
    Continuous (Φ κ) ∧ Continuous (Ψ κ) ∧
    (∀ u, Ψ κ (Φ κ u) = u) ∧ (∀ z, Φ κ (Ψ κ z) = z)) ∧
  (∀ κ : ℝ, 0 < κ → ∀ s : ℝ, 0 < s → ∀ u : L2T L,
    Φ κ (s • u) = s • Φ (κ*s^2) u) ∧
  UniformC1 Φ Ψ

theorem compatibility_of_family {d CL : ℝ}
    {Φl : ℝ → L2T L → K} {Ψl : ℝ → K → L2T L}
    {Φ : ℝ → L2T L → K} {Ψ : ℝ → K → L2T L}
    (hd : 0 < d) (hCL : 0 ≤ CL) (hl : Local023Body L d CL Φl Ψl)
    (hf : Family d Φl Ψl Φ Ψ) : Compatibility d CL Φ Ψ := by
  refine ⟨?_, fun κ hκ s hs u => scaling hd hl hf hκ hs u, uniform_C1 hd hCL hl hf⟩
  intro κ hκ
  let h := hf κ hκ
  refine ⟨?_, h.fourier_derivative hd hl, ?_, h.real_normalization hd hl,
    joint_analytic hd hl hf hκ, inverse_joint_analytic hd hl hf hκ,
    fun R hr => h.ball_estimates hd hCL hl hr, h.unique hd hl,
    h.zero_action, h.inverse_zero_action,
    continuous_iff_continuousAt.mpr (fun u => (h.analytic u).continuousAt),
    continuous_iff_continuousAt.mpr (fun z => (h.inverse_analytic z).continuousAt), h.left_inv, h.right_inv⟩
  · intro u n
    have H (s : SymKind) := congrArg (fun z : K => z n) (h.covariance hd hl s u)
    refine ⟨fun γ => ?_, fun y => ?_, fun k => ?_, ?_, ?_⟩
    · simpa [SymKind.phys, SymKind.mono, Mono.cj] using H (.phase γ)
    · simpa [SymKind.phys, SymKind.mono, Mono.cj] using H (.trans y)
    · simpa [SymKind.phys, SymKind.mono, Mono.cj, sub_eq_add_neg] using H (.boost k)
    · simpa [SymKind.phys, SymKind.mono, Mono.cj] using H .refl
    · simpa [SymKind.phys, SymKind.mono, Mono.cj] using H .cj
  · intro a k
    rw [h.plane hd hl, map_smul, QuantumNLS.Fourier.fourierL2_modeLp]

/-- **R-CA92819A: Compatibility of the global extension.** Only L>0.
Every extending family of the reviewed LOCAL-023 maps obeys every printed
clause; the extending-family premise is nonvacuous by R-F5355ABD. -/
theorem global_compatibility (L : ℝ) [Fact (0 < L)] :
    ∃ d CL : ℝ, 0 < d ∧ 0 ≤ CL ∧
      ∃ (Φl : ℝ → L2T L → K) (Ψl : ℝ → K → L2T L),
        Local023Body L d CL Φl Ψl ∧
        (∃ (Φ : ℝ → L2T L → K) (Ψ : ℝ → K → L2T L), Family d Φl Ψl Φ Ψ) ∧
        ∀ (Φ : ℝ → L2T L → K) (Ψ : ℝ → K → L2T L),
          Family d Φl Ψl Φ Ψ → Compatibility d CL Φ Ψ := by
  obtain ⟨d, CL, hd, hCL, Φl, Ψl, hl⟩ := RF535Final.local023 L
  refine ⟨d, CL, hd, hCL, Φl, Ψl, hl, ?_, fun Φ Ψ hf => compatibility_of_family hd hCL hl hf⟩
  have hex (κ : ℝ) : ∃ (Φ : L2T L → K) (Ψ : K → L2T L),
      ∀ hκ : 0 < κ, Extension κ hκ d (Φl κ) (Ψl κ) Φ Ψ := by
    by_cases hk : 0 < κ
    · obtain ⟨Φ, Ψ, h⟩ := extension_exists (hκ := hk) hd hl
      exact ⟨Φ, Ψ, fun _ => h⟩
    · exact ⟨0, 0, fun hκ => False.elim (hk hκ)⟩
  choose Φ Ψ hf using hex
  exact ⟨Φ, Ψ, hf⟩

#print axioms global_compatibility
#print axioms compatibility_of_family
end QuantumNLS.GlobalCompatR47a

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.GlobalCompatR47a." ||
        n.toString.startsWith "_private.QuantumNLS.GlobalCompatR47a." then
      pending := pending.push n
      roots := roots + 1
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
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Round47 aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
