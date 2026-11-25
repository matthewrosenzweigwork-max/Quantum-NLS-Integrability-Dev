import QuantumNLS.HierarchyInputR25m
import QuantumNLS.Prop022OMain
import QuantumNLS.Prop021ManyBodyR129
import QuantumNLS.Q07GradientRemovalR24
import QuantumNLS.FullMass

/-! PROP-025 (thm:MP-mixed, mixed_propagation.tex sha256 24ab083b...), stage I:
the named predecessor inputs, each as ONE Lean proposition equal to the printed
statement (at the physical carrier H = L2T L used by PROP-025).

* `HierarchyInput` : R-7B122087 (thm:hierarchy, DYNAMICS_LEMMAS.tex:117, sha256
  7f9760a1...).  REUSED verbatim: it is the shared frozen
  `HierarchyInputR25m.HierarchyR7B122087Input` (sol_multi, 4371326e; independent
  review r233), so every consumer binds to the same input.
* `WindowInput` : R-E59628C9 (prop:window, DYNAMICS_LEMMAS.tex:213).  The printed
  conditional statement: under the preceding scalar contour estimate
  (prop:Q07Bgradientremoval, R-C5645D32, accepted; `GradientRemovalAntecedent`,
  discharged by `gradient_removal`) and the new chart (PrintedChart with its Sobolev
  homeomorphisms), the physical window trajectory converges in L² to the full
  physical hierarchy trajectory at rate C a^{-1/4}, C independent of the cutoff,
  uniformly on every compact smooth initial class and compact joint-time box.
* `Prop021Input` : PROP-021 (Q7B:thm:main, fluctuations.tex:58-92, sha256 14830713...),
  at the physical one-particle space L2T L, with the objects of the accepted torus
  PROP-022 (kernels on positive ranks, `profile`, `classicalFlow`, `printedWeyl`,
  `vac`, `PhysicalQuasifreeSource`, `numberExpectation`, `pairMajorant` = C_A) and the
  literal Q7B many-body sectors / Fock evolution of `Prop021ManyBodyR129`.
* DEF-044 is a DEFINITION, not a theorem: it enters the PROP-025 headline as a
  definitional parameter (its source-faithful realization is in progress, sol_multi
  r26); nothing about it is assumed or constructed here.

Nothing is proved about the predecessors; `gradient_removal` only discharges the
antecedent of `WindowInput` by the accepted R-C5645D32 theorem, and the `*_spec`
lemmas only unfold the clauses consumed later. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open scoped InnerProductSpace Topology NNReal ENNReal
open MeasureTheory

namespace QuantumNLS.Prop025OInputs
open PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors TensorCarrier TraceClass
open Prop022FactorialCoefficientsR115 Prop022FactorialMajorantR115 Prop022ActualProfileR117
open Prop022ClassicalFlowR126 Prop022PositiveDataR126 Prop022OVacuum
open Ext006PhysQuasifree Ext006PhysFockCoord Ext006NumberPhase
open ClassicalCharges HierarchyFlow Def033HierarchyR24m

variable {L κ : ℝ} [Fact (0 < L)]

/-! ### R-7B122087 (thm:hierarchy): the shared frozen input, reused verbatim. -/

/-- R-7B122087, exactly `HierarchyInputR25m.HierarchyR7B122087Input` (no copy). -/
abbrev HierarchyInput (hκ : 0 < κ) : Prop :=
  HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ

/-! ### R-E59628C9 (prop:window). -/

/-- The preceding scalar contour estimate (prop:Q07Bgradientremoval, R-C5645D32), as
printed: every order `r ≥ 2`, every `H^{2r+4}` radius `B`, every contour height. -/
def GradientRemovalAntecedent (hκ : 0 < κ) : Prop :=
  ∀ r : ℕ, 2 ≤ r → ∀ B : ℝ, ∀ h : ℝ, 0 < h →
    ∃ C : ℝ, 0 ≤ C ∧ ∃ l0 : ℕ, ∀ l : ℕ, l0 ≤ l →
      (∀ u : Sobolev.H02 L (Q07TailBindingR24.regularity r), ‖u‖ ≤ B →
        DifferentiableAt ℝ (Q07GradientRemovalR24.T (L := L) hκ r h l) u) ∧
      sSup ((fun u : Sobolev.H02 L (Q07TailBindingR24.regularity r) =>
          ‖fderiv ℝ (Q07GradientRemovalR24.T (L := L) hκ r h l) u‖) ''
          Q07GradientRemovalR24.smoothBall (L := L) r B)
        ≤ C * (PROP017UniformN.cutSeq L l) ^ (-(1/2 : ℝ))

/-- The antecedent holds: it is the accepted R-C5645D32 theorem. -/
theorem gradient_removal (hκ : 0 < κ) : GradientRemovalAntecedent (L := L) hκ :=
  fun r hr B _h hh => Q07GradientRemovalR24.«prop:Q07Bgradientremoval» hκ r hr B hh

/-- The classical window Hamiltonian `h_{r,a}(v) = ∫_{(-a,a)} x^r dM_{κ,v}(x)`
(mixed_propagation.tex, "Identification of the whole classical vector field"),
with the full-mass measure `M_{κ,v}` (`FullMass.Mmeas`), defined on all of L². -/
def windowHam (κ : ℝ) (r : ℕ) (a : ℝ) (v : L2T L) : ℝ :=
  ∫ x in Set.Ioo (-a) a, x ^ r ∂(FullMass.Mmeas κ v)

/-- The joint window Hamiltonian `Σ_{r∈R} t_r h_{r,a}` at joint times `t`. -/
def windowFamily (κ : ℝ) (R : Finset ℕ) (t : ℕ → ℝ) (a : ℝ) (v : L2T L) : ℝ :=
  ∑ r ∈ R, t r * windowHam (L := L) κ r a v

/-- Physical gradient convention `dF(v)[w] = 2 Re⟪∇F(v), w⟫` for the full REAL
Fréchet differential on L² (all real directions, including radial ones). -/
def IsPhysGradient (F : L2T L → ℝ) (v g : L2T L) : Prop :=
  HasFDerivAt F ((2 : ℝ) • (Complex.reCLM.comp ((innerSL ℂ g).restrictScalars ℝ))) v

/-- A physical window trajectory at joint times `t`: the auxiliary-time solution
`y(0) = u`, `ẏ(τ) = -i ∇(Σ_r t_r h_{r,a})(y(τ))` on `[0,1]`; its time-one value is the
joint window trajectory (the window flows of a finite family commute). -/
def IsWindowTrajectory (κ : ℝ) (R : Finset ℕ) (t : ℕ → ℝ) (a : ℝ) (u : L2T L)
    (y : ℝ → L2T L) : Prop :=
  y 0 = u ∧ ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∃ g : L2T L,
    IsPhysGradient (windowFamily (L := L) κ R t a) (y τ) g ∧
    HasDerivWithinAt y ((-Complex.I) • g) (Set.Icc (0 : ℝ) 1) τ

/-- **R-E59628C9 (prop:window), the printed conditional statement.**  For the new
chart (PrintedChart, Sobolev homeomorphisms) and the preceding scalar contour estimate:
for every family of physical Hamiltonian flows of `I_{r+1}^{(κ)}` (`r ≥ 2`; unique by
thm:hierarchy), every finite charge family `R` with largest order at most `d ≥ 2`,
every compact time box and every compact smooth initial class `K` (a single smooth
datum is `K = {u}`), there are `C` (independent of the cutoff) and a cutoff threshold
such that at every regular cut `a = a_ℓ = (2ℓ+1)π/L`, `ℓ ≥ ℓ₀`, every physical window
trajectory from `u ∈ K` is within `C a^{-1/4}` in L² of the full physical hierarchy
trajectory `Φ_t u`, for all joint times in the box. -/
def WindowInput (hκ : 0 < κ) : Prop :=
  ∀ w : L2T L → REF88Chart.K, REF88PrintedChart.PrintedChart hκ w →
    HierarchyInputR25m.SobolevHomeomorphisms w → GradientRemovalAntecedent (L := L) hκ →
    ∀ (Φ : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ))
      (hΦ : ∀ r, 2 ≤ r → IsHamFlow L (hamiltonian L κ r) (Φ r)),
    ∀ d : ℕ, 2 ≤ d → ∀ (R : Finset ℕ) (hR : ∀ r ∈ R, 2 ≤ r ∧ r ≤ d),
    ∀ T : ℕ → ℝ, (∀ r, 0 ≤ T r) → ∀ K : Set (Smooth L), IsCompact K →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ l0 : ℕ, ∀ l : ℕ, l0 ≤ l → ∀ u ∈ K,
        ∀ t : ℕ → ℝ, (∀ r ∈ R, |t r| ≤ T r) →
        ∀ y : ℝ → L2T L,
          IsWindowTrajectory (L := L) κ R t (PROP017UniformN.cutSeq L l) (physical u) y →
          ‖y 1 - physical (jointSmooth (⟨Φ, fun r hr => hΦ r (hR r hr).1⟩ : HamFlows L κ R) t u)‖
            ≤ C * (PROP017UniformN.cutSeq L l) ^ (-(1/4 : ℝ))

/-! ### PROP-021 (Q7B:thm:main) at the physical carrier. -/

/-- `Q = 1 + C_A² T² M² P²`, `C_A = Σ_{m≥2} m(m-1) A^m/√(2m)!` (`pairMajorant`). -/
def Qpar (A T M P : ℝ) : ℝ := 1 + pairMajorant A ^ 2 * T ^ 2 * M ^ 2 * P ^ 2

/-- The rank-one projector `|v^{⊗k}⟩⟨v^{⊗k}|`. -/
def tensorProj (k : ℕ) (v : L2T L) :
    HilbertTensorPower ℂ (L2T L) k →L[ℂ] HilbertTensorPower ℂ (L2T L) k :=
  InnerProductSpace.rankOne ℂ (htpow k v : HilbertTensorPower ℂ (L2T L) k) (htpow k v)

/-- The exact `N`-particle evolution `e^{-itℍ_N|_N}` (placement factor `(N)_m/N^m` kept). -/
def nEvolution (B : ∀ m, HN L m →L[ℂ] HN L m) (N : ℕ) (t : ℝ) : HN L N →L[ℂ] HN L N :=
  LinearTailPhysicalEvolution.evolution (Prop021ManyBodyR129.sector B N N) t

/-- **PROP-021 (Q7B:thm:main), the printed statement at H = L2T L.**
For every `A > 0` there is `c_A`, and for every `T > 0` a `C_{A,T}`, such that for all
self-adjoint factorial kernels `B_m` (`m ≥ 1`, `‖B_m‖ ≤ M A^m/√(2m)!`, `M ≥ 1`), every
unit `u₀` and every `P ≥ 1` bounding `‖S(t,s)‖`, `S(t,s) = DΦ_{t-s}(u_s)`, on `[-T,T]`,
and every `N ≥ 1` with `N ≥ c_A Q`:
(eq:coherent, eq:depletion) a phase `θ_N(t)` and a normalized pure quasifree `ξ_t`,
`ξ_0 = Ω`, with `sup_{|t|≤T} ‖e^{-itℍ_N}W(√N u₀)Ω - e^{-iθ_N(t)}W(√N u_t)ξ_t‖ ≤
C_{A,T} M N^{-1/2} Q^{3/2}` and `⟨ξ_t, 𝒩 ξ_t⟩ ≤ Q - 1`;
(eq:marginal) for each `1 ≤ k ≤ N`, `‖γ^{(k)}_{ψ_{N,t}} - |u_t^{⊗k}⟩⟨u_t^{⊗k}|‖₁ ≤
C_{A,T} √k N^{-1/4}(M Q^{3/2} + √Q)` for the exact evolution `ψ_{N,t}` of `u₀^{⊗N}`;
and for normalized preparations `ψ̃_N` the additional error is `≤ 2‖ψ̃_N - u₀^{⊗N}‖`. -/
def Prop021Input : Prop :=
  ∀ A : ℝ, ∀ hA : 0 < A, ∃ cA : ℝ, ∀ T : ℝ, 0 < T → ∃ CAT : ℝ,
  ∀ (K : ∀ n, HN L (n+1) →L[ℂ] HN L (n+1)) (M : ℝ), 1 ≤ M →
  ∀ (hK : ∀ n, ‖K n‖ ≤ M * A ^ (n+1) / Real.sqrt ((2*(n+1)).factorial : ℝ))
    (hsK : ∀ n, (K n).adjoint = K n) (u₀ : Prop001.Sphere (L2T L)) (P : ℝ), 1 ≤ P →
  (∀ s t : ℝ, |s| ≤ T → |t| ≤ T →
    ‖fderiv ℝ (classicalFlow (positiveExtension K) M A hA.le (positiveExtension_bound K M A hK)
        (positiveExtension_selfAdjoint K hsK) (t - s))
      (profile (positiveExtension K) M A hA.le (positiveExtension_bound K M A hK)
        (positiveExtension_selfAdjoint K hsK) u₀ s)‖ ≤ P) →
  ∀ N : ℕ, 1 ≤ N → cA * Qpar A T M P ≤ N →
  (∃ (θ : ℝ → ℝ) (ξ : ℝ → Fock L), ξ 0 = vac ∧
    (∀ t, |t| ≤ T → ‖ξ t‖ = 1 ∧ PhysicalQuasifreeSource (ξ t)) ∧
    (∀ t, |t| ≤ T →
      ‖Prop021ManyBodyR129.manyBodyEvolution (positiveExtension K)
          (positiveExtension_selfAdjoint K hsK) N t
          (printedWeyl (((Real.sqrt N : ℝ) : ℂ) • (u₀ : L2T L)) vac) -
        Complex.exp (-(Complex.I * (θ t : ℂ))) •
          printedWeyl (((Real.sqrt N : ℝ) : ℂ) •
            profile (positiveExtension K) M A hA.le (positiveExtension_bound K M A hK)
              (positiveExtension_selfAdjoint K hsK) u₀ t) (ξ t)‖ ≤
        CAT * M * (N : ℝ) ^ (-(1/2 : ℝ)) * Qpar A T M P ^ ((3 : ℝ)/2)) ∧
    (∀ t, |t| ≤ T →
      numberExpectation (fun n => (n : ℝ≥0∞)) (ξ t) ≤ ENNReal.ofReal (Qpar A T M P - 1))) ∧
  (∀ k : ℕ, 1 ≤ k → ∀ hk : k ≤ N, ∀ t, |t| ≤ T →
    traceNorm (reducedDensityN N k hk
        ((nEvolution (positiveExtension K) N t (HighMomentsOps.wvec N (u₀ : L2T L)) : HN L N) :
          HilbertTensorPower ℂ (L2T L) N) -
      tensorProj k (profile (positiveExtension K) M A hA.le (positiveExtension_bound K M A hK)
        (positiveExtension_selfAdjoint K hsK) u₀ t)) ≤
    ENNReal.ofReal (CAT * Real.sqrt k * (N : ℝ) ^ (-(1/4 : ℝ)) *
      (M * Qpar A T M P ^ ((3 : ℝ)/2) + Real.sqrt (Qpar A T M P)))) ∧
  (∀ k : ℕ, 1 ≤ k → ∀ hk : k ≤ N, ∀ ψ : HN L N, ‖ψ‖ = 1 → ∀ t, |t| ≤ T →
    traceNorm (reducedDensityN N k hk
        ((nEvolution (positiveExtension K) N t ψ : HN L N) : HilbertTensorPower ℂ (L2T L) N) -
      tensorProj k (profile (positiveExtension K) M A hA.le (positiveExtension_bound K M A hK)
        (positiveExtension_selfAdjoint K hsK) u₀ t)) ≤
    ENNReal.ofReal (CAT * Real.sqrt k * (N : ℝ) ^ (-(1/4 : ℝ)) *
      (M * Qpar A T M P ^ ((3 : ℝ)/2) + Real.sqrt (Qpar A T M P)) +
      2 * ‖ψ - HighMomentsOps.wvec N (u₀ : L2T L)‖))

/-- The clause of PROP-021 consumed by PROP-025 (eq:MP-affine-propagation): the
marginal bound for normalized preparations, at one auxiliary time `t`, `|t| ≤ T`. -/
theorem prop021_preparation_spec (H : Prop021Input (L := L)) (A : ℝ) (hA : 0 < A) :
    ∃ cA : ℝ, ∀ T : ℝ, 0 < T → ∃ CAT : ℝ,
    ∀ (K : ∀ n, HN L (n+1) →L[ℂ] HN L (n+1)) (M : ℝ), 1 ≤ M →
    ∀ (hK : ∀ n, ‖K n‖ ≤ M * A ^ (n+1) / Real.sqrt ((2*(n+1)).factorial : ℝ))
      (hsK : ∀ n, (K n).adjoint = K n) (u₀ : Prop001.Sphere (L2T L)) (P : ℝ), 1 ≤ P →
    (∀ s t : ℝ, |s| ≤ T → |t| ≤ T →
      ‖fderiv ℝ (classicalFlow (positiveExtension K) M A hA.le (positiveExtension_bound K M A hK)
          (positiveExtension_selfAdjoint K hsK) (t - s))
        (profile (positiveExtension K) M A hA.le (positiveExtension_bound K M A hK)
          (positiveExtension_selfAdjoint K hsK) u₀ s)‖ ≤ P) →
    ∀ N : ℕ, 1 ≤ N → cA * Qpar A T M P ≤ N →
    ∀ k : ℕ, 1 ≤ k → ∀ hk : k ≤ N, ∀ ψ : HN L N, ‖ψ‖ = 1 → ∀ t, |t| ≤ T →
      traceNorm (reducedDensityN N k hk
          ((nEvolution (positiveExtension K) N t ψ : HN L N) : HilbertTensorPower ℂ (L2T L) N) -
        tensorProj k (profile (positiveExtension K) M A hA.le (positiveExtension_bound K M A hK)
          (positiveExtension_selfAdjoint K hsK) u₀ t)) ≤
      ENNReal.ofReal (CAT * Real.sqrt k * (N : ℝ) ^ (-(1/4 : ℝ)) *
        (M * Qpar A T M P ^ ((3 : ℝ)/2) + Real.sqrt (Qpar A T M P)) +
        2 * ‖ψ - HighMomentsOps.wvec N (u₀ : L2T L)‖) := by
  obtain ⟨cA, hc⟩ := H A hA
  refine ⟨cA, fun T hT => ?_⟩
  obtain ⟨CAT, hC⟩ := hc T hT
  exact ⟨CAT, fun K M hM hK hsK u₀ P hP hS N hN hNQ =>
    (hC K M hM hK hsK u₀ P hP hS N hN hNQ).2.2⟩

/-- The window clause consumed by PROP-025 (eq:MP-classical-window-error), with the
accepted R-C5645D32 antecedent discharged. -/
theorem window_spec (hκ : 0 < κ) (H : WindowInput (L := L) hκ)
    (w : L2T L → REF88Chart.K) (hw : REF88PrintedChart.PrintedChart hκ w)
    (hsob : HierarchyInputR25m.SobolevHomeomorphisms w)
    (Φ : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ))
    (hΦ : ∀ r, 2 ≤ r → IsHamFlow L (hamiltonian L κ r) (Φ r))
    (d : ℕ) (hd : 2 ≤ d) (R : Finset ℕ) (hR : ∀ r ∈ R, 2 ≤ r ∧ r ≤ d)
    (T : ℕ → ℝ) (hT : ∀ r, 0 ≤ T r) (K : Set (Smooth L)) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ l0 : ℕ, ∀ l : ℕ, l0 ≤ l → ∀ u ∈ K,
      ∀ t : ℕ → ℝ, (∀ r ∈ R, |t r| ≤ T r) →
      ∀ y : ℝ → L2T L,
        IsWindowTrajectory (L := L) κ R t (PROP017UniformN.cutSeq L l) (physical u) y →
        ‖y 1 - physical (jointSmooth (⟨Φ, fun r hr => hΦ r (hR r hr).1⟩ : HamFlows L κ R) t u)‖
          ≤ C * (PROP017UniformN.cutSeq L l) ^ (-(1/4 : ℝ)) :=
  H w hw hsob (gradient_removal hκ) Φ hΦ d hd R hR T hT K hK

end QuantumNLS.Prop025OInputs

#print axioms QuantumNLS.Prop025OInputs.gradient_removal
#print axioms QuantumNLS.Prop025OInputs.prop021_preparation_spec
#print axioms QuantumNLS.Prop025OInputs.window_spec

-- Recursive type/value audit of every own declaration: standard axioms only, and no held
-- identifier (HeldGP14Tonelli, the superseded pre-D1 `RegularCut`) in the transitive closure.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop025OInputs." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 ||
          n.components.any (fun c => c.toString == "RegularCut") then
        throwError "Held dependency: {n}"
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
  Lean.logInfo m!"Prop025OInputs aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only, no held identifiers."
