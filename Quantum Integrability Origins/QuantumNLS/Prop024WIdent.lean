import QuantumNLS.Prop024WQuadratic
import QuantumNLS.Prop024WRemainder
import QuantumNLS.Prop024WStepOne

/-! PROP-024 step (1), the identification with the PROP-021 low orders (Prop024WIdent).

`stepOne_lowOrders`: on a smooth vector `x` with the printed polynomial moment bounds,
`W(√N u)⁻¹ H_N W(√N u) x = lowOrders B N u x + R` with `R = remVec N B u x`, where
`lowOrders` is luna's `Prop021RemainderInputR131.lowOrders`
`= (N F(u)) x + √N linearHamiltonian(∇F(u)) x + quadraticAction(a_u, b_u) x`
(source `fluctuations.tex:274-276`).  The constant term is `Prop024WConstant`, the linear term is
`Prop024WLinear`, the quadratic term is `Prop024WQuadratic`.

`stepOneIdentification_lowOrders`: EXACTLY the `hStepOneIdentificationInput` of
`Prop024AssemblyR58.prop024_intermediate_scaffold`, for the four terms
`constantTermAt`, `linearTermAt`, `quadraticTermAt`, `remainderTermAt` below (the first three are the three
summands of `lowOrders`, the last is the entire Wick remainder `remVec`).

`prop024_scaffold_discharged`: the scaffold with both of its inputs discharged.

`prop024RemainderInput_holds`: luna's `Prop021RemainderInputR131.Prop024RemainderInput` (the printed
`Q7B:lem:remainder`, in the PROP-021 form with `printedWeyl ((√N : ℂ) • u)`), for every `A > 0`.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
open scoped InnerProductSpace ComplexConjugate Topology
namespace QuantumNLS.Prop024WIdent
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors Ext006PhysFockCoord
open Prop024WWeylPhysical Prop024WBlock Prop024WOrder Prop024WNorms Prop024WSeries Prop024WStepOne
open Prop024WConstant Prop024WLinear Prop024WQuadratic Prop024WRemainder
open Prop024ContractionsR54 Prop024PhysicalHamiltonianR54 Prop022FactorialCoefficientsR115
open Prop024HilbertConjugationR58 Prop022ClassicalTimeR116 Prop022StrongOperatorR125 Ext005Moments
open Ext006ModeDomainR33a
variable {L : ℝ} [Fact (0 < L)]

/-- **PROP-024 step (1) with the PROP-021 low orders.**  Under the printed polynomial number-moment bounds
of `x` and `N ≥ 256 e A Q`, the translated vector lies in the maximal domain of the interaction and the
pulled-back interaction is `lowOrders + remVec`. -/
theorem stepOne_lowOrders (N : ℕ) (hN : 0 < N) (B : ∀ r, HN L r →L[ℂ] HN L r)
    (hs : ∀ m, (B m).adjoint = B m) (M A Q : ℝ) (hM : 0 ≤ M) (hA : 0 < A) (hQ : 1 ≤ Q)
    (hNQ : 256 * Real.exp 1 * A * Q ≤ N) (hB : FactorialBound B M A) (u : L2T L) (hu : ‖u‖ = 1)
    {x : Fock L} (hxm : x ∈ physSmooth L) (hMom : PolyMoments Q x) :
    ∃ (hx : Smooth (Ext006PhysicalVacuum.coefficient x)) (h₂ : x ∈ momentDomain (L := L) 2)
      (hz : physicalWeyl N u x ∈ (interaction N B).domain),
      pulledInteraction N u B x hz =
        Prop021RemainderInputR131.lowOrders B N u x hx h₂ + remVec N B u x := by
  obtain ⟨hz, hid⟩ := stepOne_core N hN B M A Q hM hA hQ hNQ hB u hu ⟨x, hxm⟩ hMom
  have hid' : pulledInteraction N u B x hz =
      constScalar N B u • x + linVec N B u x + quadVec N B u x + remVec N B u x := hid
  have hx : Smooth (Ext006PhysicalVacuum.coefficient x) := smoothOf ⟨x, hxm⟩
  have h₂ : x ∈ momentDomain (L := L) 2 := ((mem_physSmooth_iff_moments x).1 hxm) 2
  refine ⟨hx, h₂, hz, ?_⟩
  have hlin : linVec N B u x = (Real.sqrt (N : ℝ) : ℂ) •
      Prop021PhaseR130.linearHamiltonian (Prop022GradientR118.gradient B u) x hx :=
    linVec_eq_linearHamiltonian N B hs M A hA.le hB u hu ⟨x, hxm⟩ hx
  rw [hid', constScalar_eq_classicalSeries N B hs u, hlin,
    quadVec_eq_quadraticAction N hN B hs M A hA.le hB u hu h₂ (momentFinite_of_mem ⟨x, hxm⟩)]
  unfold Prop021RemainderInputR131.lowOrders
  push_cast
  try abel

/-! ### The four terms of the scaffold -/

section Terms
open Classical

/-- The constant term `N F(u_t)` of `lowOrders`. -/
def constantTermAt (N : ℕ) (B : ∀ r, HN L r →L[ℂ] HN L r) (u : ℝ → L2T L) : ℝ → ℂ :=
  fun t => ((N : ℝ) * classicalSeries B (u t) : ℂ)

/-- The linear term `√N linearHamiltonian(∇F(u_t))` of `lowOrders` (zero where the vector is not smooth). -/
def linearTermAt (N : ℕ) (B : ∀ r, HN L r →L[ℂ] HN L r) (u : ℝ → L2T L) (V : ℝ → Fock L) :
    ℝ → Fock L :=
  fun t => if h : Smooth (Ext006PhysicalVacuum.coefficient (V t)) then
    (Real.sqrt (N : ℝ) : ℂ) • Prop021PhaseR130.linearHamiltonian (Prop022GradientR118.gradient B (u t)) (V t) h
  else 0

/-- The quadratic term of `lowOrders` (zero where the vector is not in the second moment domain). -/
def quadraticTermAt (B : ∀ r, HN L r →L[ℂ] HN L r) (u : ℝ → L2T L) (V : ℝ → Fock L) :
    ℝ → Fock L :=
  fun t => if h : V t ∈ momentDomain (L := L) 2 then
    quadraticAction (numberCoefficient B (u t)) (pairCoefficient B (u t)) ⟨V t, h⟩
  else 0

/-- The entire Wick remainder. -/
def remainderTermAt (N : ℕ) (B : ∀ r, HN L r →L[ℂ] HN L r) (u : ℝ → L2T L) (V : ℝ → Fock L) :
    ℝ → Fock L :=
  fun t => remVec N B (u t) (V t)

lemma lowOrders_eq_terms (N : ℕ) (B : ∀ r, HN L r →L[ℂ] HN L r) (u : ℝ → L2T L) (V : ℝ → Fock L)
    (t : ℝ) (hx : Smooth (Ext006PhysicalVacuum.coefficient (V t))) (h₂ : V t ∈ momentDomain (L := L) 2) :
    Prop021RemainderInputR131.lowOrders B N (u t) (V t) hx h₂ =
      constantTermAt N B u t • V t + linearTermAt N B u V t + quadraticTermAt B u V t := by
  unfold Prop021RemainderInputR131.lowOrders constantTermAt linearTermAt quadraticTermAt
  rw [dif_pos hx, dif_pos h₂]

end Terms

/-- **PROP-024 step (1): the identification input of the scaffold, with the PROP-021 terms.**
This is exactly `hStepOneIdentificationInput` of `Prop024AssemblyR58.prop024_intermediate_scaffold`
for `constantTerm = constantTermAt`, `linearTerm = linearTermAt`, `quadraticTerm = quadraticTermAt`,
`remainderTerm = remainderTermAt`; by `lowOrders_eq_terms` the first three terms are the three summands of
`Prop021RemainderInputR131.lowOrders` (`stepOne_lowOrders`).  The hypothesis `hMoments` is the printed
`Q7B:eq:mgf` (`NumberMoments`), supplied by luna's `Prop021RemainderInputR131.actual_moments`. -/
theorem stepOneIdentification_lowOrders
    (N : ℕ) (K : ∀ n, HN L (n+1) →L[ℂ] HN L (n+1)) (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A)
    (hK : ∀ n, ‖K n‖ ≤ M * A ^ (n+1) / Real.sqrt ((2*(n+1)).factorial : ℝ))
    (hsK : ∀ n, (K n).adjoint = K n) (u₀ : Prop001.Sphere (L2T L)) (T Q : ℝ) (hQ : 1 ≤ Q)
    (hNQ : ∀ t : ℝ, |t| ≤ T → 256 * Real.exp 1 * A * Q ≤ N)
    (hMoments :
      let B := Prop022PositiveDataR126.positiveExtension K
      let hB := Prop022PositiveDataR126.positiveExtension_bound K M A hK
      let hsa := Prop022PositiveDataR126.positiveExtension_selfAdjoint K hsK
      let u := Prop022ActualProfileR117.profile B M A hA.le hB hsa u₀
      let V := fun t s : ℝ => Prop022FockPropagatorR122.propagator B M A
        (by linarith) hA.le hB hsa u₀ s t
      ∀ t : ℝ, |t| ≤ T → Prop021RemainderInputR131.NumberMoments Q (V t 0 vac))
    (hTranslatedDomainInput :
      let B := Prop022PositiveDataR126.positiveExtension K
      let hB := Prop022PositiveDataR126.positiveExtension_bound K M A hK
      let hsa := Prop022PositiveDataR126.positiveExtension_selfAdjoint K hsK
      let u := Prop022ActualProfileR117.profile B M A hA.le hB hsa u₀
      let V := fun t s : ℝ => Prop022FockPropagatorR122.propagator B M A
        (by linarith) hA.le hB hsa u₀ s t
      ∀ t : ℝ, |t| ≤ T → physicalWeyl N (u t) (V t 0 vac) ∈ (interaction N B).domain) :
    let B := Prop022PositiveDataR126.positiveExtension K
    let hB := Prop022PositiveDataR126.positiveExtension_bound K M A hK
    let hsa := Prop022PositiveDataR126.positiveExtension_selfAdjoint K hsK
    let u := Prop022ActualProfileR117.profile B M A hA.le hB hsa u₀
    let V := fun t s : ℝ => Prop022FockPropagatorR122.propagator B M A
      (by linarith) hA.le hB hsa u₀ s t
    ∀ t : ℝ, ∀ ht : |t| ≤ T,
      pulledInteraction N (u t) B (V t 0 vac) (hTranslatedDomainInput t ht) =
        constantTermAt N B u t • (V t 0 vac) + linearTermAt N B u (fun t => V t 0 vac) t +
          quadraticTermAt B u (fun t => V t 0 vac) t + remainderTermAt N B u (fun t => V t 0 vac) t := by
  intro B hB hsa u V t ht
  have hmom : Prop021RemainderInputR131.NumberMoments Q (V t 0 vac) := hMoments t ht
  have hNQt : 256 * Real.exp 1 * A * Q ≤ N := hNQ t ht
  have hNpos : 0 < N := by
    have hQ0 : 0 < Q := by linarith
    have h0 : (0 : ℝ) < 256 * Real.exp 1 * A * Q :=
      mul_pos (mul_pos (mul_pos (by norm_num) (Real.exp_pos 1)) hA) hQ0
    exact_mod_cast h0.trans_le hNQt
  have hpoly : PolyMoments Q (V t 0 vac) := hmom.2
  have hu : ‖u t‖ = 1 := (Prop022ActualProfileR117.profile_spec B M A hA.le hB hsa u₀).2.2.1 t
  have hsm : V t 0 vac ∈ physSmooth L := mem_physSmooth_of_polyMoments Q _ hpoly
  obtain ⟨hx, h₂, hz, hid⟩ := stepOne_lowOrders N hNpos B hsa M A Q (by linarith) hA hQ hNQt hB (u t) hu
    hsm hpoly
  have h1 : pulledInteraction N (u t) B (V t 0 vac) (hTranslatedDomainInput t ht) =
      pulledInteraction N (u t) B (V t 0 vac) hz := rfl
  rw [h1, hid]
  have h3 := lowOrders_eq_terms N B u (fun t => V t 0 vac) t hx h₂
  rw [h3]
  all_goals rfl

/-! ### The printed `Q7B:lem:remainder` in the PROP-021 form -/

lemma pmap_apply_congr {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (f g : E →ₗ.[ℂ] F) (hfg : f = g) (y y' : E) (e : y = y') (hy : y ∈ f.domain)
    (hy' : y' ∈ g.domain) : f ⟨y, hy⟩ = g ⟨y', hy'⟩ := by
  subst hfg; subst e; rfl

lemma sqrt_cube_eq (Q : ℝ) (hQ : 0 ≤ Q) : (Real.sqrt Q) ^ 3 = Q ^ ((3 : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hQ]
  norm_num

lemma inv_sqrt_eq (N : ℝ) (hN : 0 ≤ N) : (Real.sqrt N)⁻¹ = N ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_neg hN]

/-- **`Q7B:lem:remainder` (PROP-024), in the form of `Prop021RemainderInputR131.Prop024RemainderInput`.**
For every `A > 0` there is a constant `C_A'` (the printed `2 S_B B³ (32e)^{3/2}`, `B = √(2A)`) such that, for
every self-adjoint factorial family, `N ≥ 256 e A Q`, unit `u` and every `x` with the printed number
moments `NumberMoments Q x`: the vector `printedWeyl (√N u) x` lies in the maximal domain of the
PROP-021 Hamiltonian, and `H_N W x = W (lowOrders + R)` with `‖R‖ ≤ C_A' M N^{-1/2} Q^{3/2}`. -/
theorem prop024RemainderInput_holds : Prop021RemainderInputR131.Prop024RemainderInput (L := L) := by
  intro A hA
  have hB0 : 0 ≤ Real.sqrt (2 * A) := Real.sqrt_nonneg _
  have hS := Prop024ScalarSeriesR52.factorialRootSeries_nonneg hB0
  refine ⟨2 * Prop024ScalarSeriesR52.factorialRootSeries (Real.sqrt (2 * A)) * (Real.sqrt (2 * A)) ^ 3 *
    (Real.sqrt (32 * Real.exp 1)) ^ 3,
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hS) (pow_nonneg hB0 3))
      (pow_nonneg (Real.sqrt_nonneg _) 3), ?_⟩
  intro B M hM hB hsB N Q hQ hNQ u hu x hx
  have hQ0 : 0 ≤ Q := by linarith
  have hNpos : 0 < N := by
    have h0 : (0 : ℝ) < 256 * Real.exp 1 * A * Q :=
      mul_pos (mul_pos (mul_pos (by norm_num) (Real.exp_pos 1)) hA) (by linarith)
    exact_mod_cast h0.trans_le hNQ
  have hxs : Smooth (Ext006PhysicalVacuum.coefficient x) :=
    Prop021RemainderInputR131.smooth_of_numberMoments Q x hx
  have hsm : x ∈ physSmooth L :=
    (mem_physSmooth_iff_moments x).2 ((Prop021DisplacementR129.common_domain x).1 hxs)
  have hpoly : PolyMoments Q x := hx.2
  obtain ⟨hx', h₂, hz, hid⟩ := stepOne_lowOrders N hNpos B hsB M A Q (by linarith) hA hQ hNQ hB u hu hsm hpoly
  have heq := Prop021RemainderInputR131.interaction_eq_hamiltonian B N
  have hW : physicalWeyl N u x = Prop022OVacuum.printedWeyl ((Real.sqrt (N : ℝ) : ℂ) • u) x :=
    Prop024WeylConventionR55.physicalWeyl_eq_printedWeyl N u x
  have hd : Prop022OVacuum.printedWeyl ((Real.sqrt (N : ℝ) : ℂ) • u) x ∈
      (Prop021ManyBodyR129.hamiltonian B N).domain := by
    rw [← heq, ← hW]; exact hz
  refine ⟨hx', h₂, hd, remVec N B u x, ?_, ?_⟩
  · have h1 : Prop021ManyBodyR129.hamiltonian B N ⟨Prop022OVacuum.printedWeyl ((Real.sqrt (N : ℝ) : ℂ) • u) x, hd⟩ =
        interaction N B ⟨physicalWeyl N u x, hz⟩ :=
      (pmap_apply_congr _ _ heq.symm _ _ hW.symm hd hz)
    rw [h1, interaction_eq_physicalWeyl_pulled, hid]
    exact Prop024WeylConventionR55.physicalWeyl_eq_printedWeyl N u _
  · have hbd := norm_remVec_le N hNpos B M A Q (by linarith) hA hQ hNQ hB u hu ⟨x, hsm⟩ hpoly
    have hbd' : ‖remVec N B u x‖ ≤ 2 * Prop024ScalarSeriesR52.factorialRootSeries (Real.sqrt (2 * A)) *
        (Real.sqrt (2 * A)) ^ 3 * (Real.sqrt (32 * Real.exp 1)) ^ 3 * M * (Real.sqrt Q) ^ 3 /
          Real.sqrt (N : ℝ) := hbd
    refine hbd'.trans (le_of_eq ?_)
    rw [sqrt_cube_eq Q hQ0, div_eq_mul_inv, inv_sqrt_eq (N : ℝ) (Nat.cast_nonneg N)]
    ring

end QuantumNLS.Prop024WIdent

#print axioms QuantumNLS.Prop024WIdent.stepOne_lowOrders
#print axioms QuantumNLS.Prop024WIdent.lowOrders_eq_terms
#print axioms QuantumNLS.Prop024WIdent.stepOneIdentification_lowOrders
#print axioms QuantumNLS.Prop024WIdent.prop024RemainderInput_holds

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop024WIdent." ||
        n.toString.startsWith "_private.QuantumNLS.Prop024WIdent." then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").any (fun s => s == "HeldGP14Tonelli" || s == "RegularCut") then
        throwError "Held identifier in dependency closure: {n}"
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
  Lean.logInfo m!"Prop024WIdent aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard axioms only."
