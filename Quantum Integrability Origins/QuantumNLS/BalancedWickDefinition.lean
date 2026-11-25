import QuantumNLS.BetheOccupationGauge
import QuantumNLS.WickBounds
import QuantumNLS.KernelDefinition
import QuantumNLS.SymplecticBracket

/-! DEF-032, DEFINITIONS_LEDGER.md:687–705; definitions.tex:193.
Finite symbols and the literal normal-ordered auxiliary Wick operator, pulled
back through the gauged Bethe coefficient unitary. Coordinate maps are supplied
parameters. No symbol limit, product correction, or gauge-selection property
is asserted here. EXT-001 occurs only in the concrete Bethe instantiations.
-/
noncomputable section
open scoped BigOperators InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.BalancedWickDefinition
open WickSymbols WickBounds Occupation OccupationHilbert BetheCoefficientTransform PhysicalTensor
local instance (α : Type) : DecidableEq α := Classical.decEq α

/-- A single finite symbol, with fixed coordinate set and fixed degree bound.
Both exponent supports are restricted; balanced does not mean holomorphic. -/
structure Polynomial where
  coordinates : Finset ℤ
  degreeBound : ℕ
  symbol : Sym
  balanced : Balanced symbol
  labels : ∀ p ∈ symbol.coeff.support,
    p.1.support ⊆ coordinates ∧ p.2.support ⊆ coordinates
  degree : ∀ p ∈ symbol.coeff.support, p.1.degree ≤ degreeBound

/-- Literal finite evaluation, with the inner-product convention of DEF-015. -/
def evaluate (f : Polynomial) (w : ℤ → ℂ) : ℂ :=
  ∑ p ∈ f.symbol.coeff.support, f.symbol.coeff p *
    p.1.prod (fun n k => w n ^ k) * p.2.prod (fun n k => (starRingEnd ℂ) (w n) ^ k)

/-- The physical coordinate chart is an explicit parameter, not an identification
with the ordinary Fourier coefficients. -/
def physicalSymbol {L : ℝ} [Fact (0 < L)] (f : Polynomial)
    (w : L2T L → ℤ → ℂ) (u : L2T L) : ℂ := evaluate f (w u)

/-- The realized physical complex-bilinear bracket convention. This is a
functional definition, without a commutator or first-correction conclusion. -/
def physicalBracket {L : ℝ} [Fact (0 < L)] (f g : Polynomial)
    (w : L2T L → ℤ → ℂ) (u : L2T L) : ℂ :=
  SymplecticBracket.pbC (physicalSymbol f w) (physicalSymbol g w) u

/-- On positive sectors WHil is the proved bounded density extension of
Σ f_{αβ} N^{-|α|}(b*)^β b^α. The vacuum uses exactly the constant coefficient:
all positive-degree balanced words annihilate it. -/
def auxiliaryWick (N : ℕ) (f : Sym) : H N →L[ℂ] H N :=
  if N = 0 then f.coeff (0, 0) • 1 else WHil N f

/-- A balanced monomial lies in the fixed-number sector. -/
theorem balanced_monomial (α β : ℤ →₀ ℕ) (h : α.degree = β.degree) :
    Balanced (zm α β) := by
  intro p hp
  have hp' : p = (α, β) := by simpa [zm] using hp
  simpa [hp'] using h

/-- Positive-sector agreement with the actual creation/annihilation words,
on the dense occupation core; no operator-valued input is supplied. -/
theorem monomial_core {N : ℕ} (hN : 0 < N) (α β : ℤ →₀ ℕ)
    (h : α.degree = β.degree) (v : Sector N) (m : Arr N) :
    auxiliaryWick N (zm α β) (core N v) m = WMono N α β (emb N v) m.val := by
  rw [auxiliaryWick, ite_eq_right (Nat.ne_of_gt hN), WHil_core hN (balanced_monomial α β h),
    core_apply, WS_apply, WN_zm]

/-- The degree cutoff follows from actual annihilation, rather than being
inserted as a truncation of the coefficient carrier. -/
theorem monomial_above_sector {N : ℕ} (hN : 0 < N) (α β : ℤ →₀ ℕ)
    (h : α.degree = β.degree) (hd : N < α.degree) :
    auxiliaryWick N (zm α β) = 0 := by
  have hann (v : Sector N) : AnnMono α (emb N v) = 0 := by
    have hb := (AnnProd_bound (labels α) (inSector_emb v)).2
    have hf : fall N (labels α).length = 0 := by
      unfold fall
      apply Finset.prod_eq_zero (i := N)
      · simpa [labels_length] using hd
      · simp
    rw [hf, Nat.cast_zero, zero_mul] at hb
    exact eq_zero_of_ip_self_re (le_antisymm hb (by
      rw [ip_self_re]
      exact Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)))
  apply ext_core N
  intro v
  ext m
  rw [monomial_core hN α β h]
  simp [WMono, Module.End.mul_apply, hann v]

/-- The degree convention includes the vacuum: every balanced monomial
of degree greater than N acts by zero. -/
theorem auxiliary_above_sector (N : ℕ) (α β : ℤ →₀ ℕ)
    (h : α.degree = β.degree) (hd : N < α.degree) :
    auxiliaryWick N (zm α β) = 0 := by
  by_cases hN : N = 0
  · subst N
    have hα : α ≠ 0 := by
      intro he
      simp [he] at hd
    simp [auxiliaryWick, zm, AddMonoidAlgebra.coeff_single, hα]
    exact zero_smul ℂ (1 : H 0 →L[ℂ] H 0)
  · exact monomial_above_sector (Nat.pos_of_ne_zero hN) α β h hd

/-- The constant monomial gives identity also in the vacuum sector. -/
theorem auxiliary_constant (N : ℕ) : auxiliaryWick N (1 : Sym) = 1 := by
  by_cases hN : N = 0
  · subst N
    rw [auxiliaryWick, ite_eq_left rfl]
    change (AddMonoidAlgebra.coeff (1 : Sym)) (0 : Mon) • 1 = 1
    rw [AddMonoidAlgebra.coeff_one_zero, one_smul]
  · rw [auxiliaryWick, ite_eq_right hN, WHil_one (Nat.pos_of_ne_zero hN)]

/-- The gauged J_N into the actual auxiliary symmetric label sector. -/
def coefficientUnitary {L : ℝ} [Fact (0 < L)] {N : ℕ}
    (b : BetheBasis L N) (g : BetheOccupationGauge.Gauge) :
    HN L N ≃ₗᵢ[ℂ] OccupationUnitary.Boson N :=
  fockTransform (BetheOccupationGauge.gaugedBasis b g)

/-- J_N* (Σ f_{αβ} N^{-|α|}(b*)^β b^α) J_N, expressed in
normalized occupation coordinates by the realized unitary U4. -/
def quantization {L : ℝ} [Fact (0 < L)] {N : ℕ}
    (b : BetheBasis L N) (g : BetheOccupationGauge.Gauge) (f : Sym) :
    HN L N →L[ℂ] HN L N :=
  let J := occupationCoefficient (BetheOccupationGauge.gaugedBasis b g)
  J.symm.toContinuousLinearEquiv.toContinuousLinearMap |>.comp
    ((auxiliaryWick N f).comp J.toContinuousLinearEquiv.toContinuousLinearMap)

/-- DEF-032 for a fixed balanced finite polynomial. -/
def wick {L : ℝ} [Fact (0 < L)] {N : ℕ}
    (b : BetheBasis L N) (g : BetheOccupationGauge.Gauge) (f : Polynomial) :
    HN L N →L[ℂ] HN L N := quantization b g f.symbol

theorem quantization_constant {L : ℝ} [Fact (0 < L)] {N : ℕ}
    (b : BetheBasis L N) (g : BetheOccupationGauge.Gauge) :
    quantization b g (1 : Sym) = 1 := by
  ext ψ
  simp [quantization, auxiliary_constant]

theorem quantization_above_sector {L : ℝ} [Fact (0 < L)] {N : ℕ}
    (b : BetheBasis L N) (g : BetheOccupationGauge.Gauge)
    (α β : ℤ →₀ ℕ) (h : α.degree = β.degree) (hd : N < α.degree) :
    quantization b g (zm α β) = 0 := by
  simp [quantization, auxiliary_above_sector N α β h hd]

/-- Homogeneous-kernel convention: (N)_p N^{-p} times normalized
placement ON THE AUXILIARY LABEL SECTOR, pulled back by the same J_N.
The kernel A is an explicit argument; no unconstructed physical kernel
or identification of A with a coordinate polynomial is assumed. -/
def kernelQuantization {L : ℝ} [Fact (0 < L)] {N p : ℕ}
    (b : BetheBasis L N) (g : BetheOccupationGauge.Gauge) (hp : p ≤ N)
    (A : KernelDefinition.BoundedSymmetricKernel OccupationUnitary.OneParticle p) :
    HN L N →L[ℂ] HN L N :=
  let J := coefficientUnitary b g
  J.symm.toContinuousLinearEquiv.toContinuousLinearMap |>.comp
    ((((N.descFactorial p : ℂ) * (N : ℂ)⁻¹ ^ p) •
      KernelDefinition.genericU_N_r N p hp A).comp
        J.toContinuousLinearEquiv.toContinuousLinearMap)

/-- Concrete fixed-c Bethe instantiation. The sole scientific premise is
passed to frozen BOG1/BCB1; it is never constructed here. -/
def betheWick (hcont : BetheConditionalBasis.AbstractContinuity)
    (s : BetheOccupationGauge.UniversalSelection) (L : ℝ) [Fact (0 < L)]
    (c : ℝ) (hc : 0 < c) (N : ℕ) (f : Polynomial) : HN L N →L[ℂ] HN L N :=
  wick (BetheOccupationGauge.sectorBasis hcont L c hc N) (s L Fact.out c hc) f

/-- At mean-field coupling, the same gauge selected at L,kappa is used
for every N. No target property or symbol limit is included. -/
def meanFieldWick (hcont : BetheConditionalBasis.AbstractContinuity)
    (s : BetheOccupationGauge.UniversalSelection) (L : ℝ) [Fact (0 < L)]
    (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 1 ≤ N) (f : Polynomial) :
    HN L N →L[ℂ] HN L N :=
  quantization (BetheOccupationGauge.selectedMeanFieldBasis hcont s L κ hκ N hN)
    BetheOccupationGauge.identityGauge f.symbol

end QuantumNLS.BalancedWickDefinition

#print axioms QuantumNLS.BalancedWickDefinition.Polynomial
#print axioms QuantumNLS.BalancedWickDefinition.evaluate
#print axioms QuantumNLS.BalancedWickDefinition.physicalSymbol
#print axioms QuantumNLS.BalancedWickDefinition.physicalBracket
#print axioms QuantumNLS.BalancedWickDefinition.auxiliaryWick
#print axioms QuantumNLS.BalancedWickDefinition.balanced_monomial
#print axioms QuantumNLS.BalancedWickDefinition.monomial_core
#print axioms QuantumNLS.BalancedWickDefinition.monomial_above_sector
#print axioms QuantumNLS.BalancedWickDefinition.auxiliary_above_sector
#print axioms QuantumNLS.BalancedWickDefinition.auxiliary_constant
#print axioms QuantumNLS.BalancedWickDefinition.coefficientUnitary
#print axioms QuantumNLS.BalancedWickDefinition.quantization
#print axioms QuantumNLS.BalancedWickDefinition.wick
#print axioms QuantumNLS.BalancedWickDefinition.quantization_constant
#print axioms QuantumNLS.BalancedWickDefinition.quantization_above_sector
#print axioms QuantumNLS.BalancedWickDefinition.kernelQuantization
#print axioms QuantumNLS.BalancedWickDefinition.betheWick
#print axioms QuantumNLS.BalancedWickDefinition.meanFieldWick

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.BalancedWickDefinition.Polynomial,
    ``QuantumNLS.BalancedWickDefinition.evaluate,
    ``QuantumNLS.BalancedWickDefinition.physicalSymbol,
    ``QuantumNLS.BalancedWickDefinition.physicalBracket,
    ``QuantumNLS.BalancedWickDefinition.auxiliaryWick,
    ``QuantumNLS.BalancedWickDefinition.balanced_monomial,
    ``QuantumNLS.BalancedWickDefinition.monomial_core,
    ``QuantumNLS.BalancedWickDefinition.monomial_above_sector,
    ``QuantumNLS.BalancedWickDefinition.auxiliary_above_sector,
    ``QuantumNLS.BalancedWickDefinition.auxiliary_constant,
    ``QuantumNLS.BalancedWickDefinition.coefficientUnitary,
    ``QuantumNLS.BalancedWickDefinition.quantization,
    ``QuantumNLS.BalancedWickDefinition.wick,
    ``QuantumNLS.BalancedWickDefinition.quantization_constant,
    ``QuantumNLS.BalancedWickDefinition.quantization_above_sector,
    ``QuantumNLS.BalancedWickDefinition.kernelQuantization,
    ``QuantumNLS.BalancedWickDefinition.betheWick,
    ``QuantumNLS.BalancedWickDefinition.meanFieldWick]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.BalancedWickDefinition." then
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
            throwError "Definition nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  let mut todo := #[``QuantumNLS.BalancedWickDefinition.Polynomial,
    ``QuantumNLS.BalancedWickDefinition.evaluate,
    ``QuantumNLS.BalancedWickDefinition.physicalSymbol,
    ``QuantumNLS.BalancedWickDefinition.physicalBracket,
    ``QuantumNLS.BalancedWickDefinition.auxiliaryWick,
    ``QuantumNLS.BalancedWickDefinition.balanced_monomial,
    ``QuantumNLS.BalancedWickDefinition.monomial_core,
    ``QuantumNLS.BalancedWickDefinition.monomial_above_sector,
    ``QuantumNLS.BalancedWickDefinition.auxiliary_above_sector,
    ``QuantumNLS.BalancedWickDefinition.auxiliary_constant,
    ``QuantumNLS.BalancedWickDefinition.coefficientUnitary,
    ``QuantumNLS.BalancedWickDefinition.quantization,
    ``QuantumNLS.BalancedWickDefinition.wick,
    ``QuantumNLS.BalancedWickDefinition.quantization_constant,
    ``QuantumNLS.BalancedWickDefinition.quantization_above_sector,
    ``QuantumNLS.BalancedWickDefinition.kernelQuantization]
  let mut checked : Std.HashSet Lean.Name := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    unless checked.contains n do
      checked := checked.insert n
      if n == ``QuantumNLS.BetheConditionalBasis.AbstractContinuity then
        throwError "Generic definition reached EXT-001 premise: {n}"
      if let some ci := env.find? n then
        todo := todo ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          todo := todo ++ v.getUsedConstants
  Lean.logInfo m!"Definition aggregate audit PASS: {seen.size} transitive constants; {checked.size} generic constants independent of EXT-001. Concrete instantiations require its explicit Prop hypothesis only."
