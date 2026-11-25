import QuantumNLS.Def021ChartR41b
import QuantumNLS.UnconditionalBetheBasis
import QuantumNLS.HighMomentsOps
import QuantumNLS.FiniteCellGauge
import QuantumNLS.ExactShiftResidual
import QuantumNLS.StrongSymbolDef

/-! R-D2F4CE8F, uniform static symbols for the same full gauge.
The positive sector indexed by `n` has particle number `n + 1`.
The two witnesses are carried through from the named retargeting input. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

noncomputable section
open Filter Topology
open scoped ComplexConjugate Classical

namespace QuantumNLS.UniformStaticR31m

open PhysicalTensor BetheCoefficientTransform Sobolev
open Occupation OccupationHilbert FullOccupationAffinity FiniteCellSupport FiniteCellGauge

variable {L κ : ℝ} [Fact (0 < L)]

def unitBall (R : ℝ) : Set (L2T L) :=
  {u | ‖u‖ = 1 ∧ ∃ v : H02 L 1, v.val = u ∧ ‖v‖ ≤ R}

abbrev FullGauge := ∀ n : ℕ, Arr (n + 1) → Phase

def labels (j : ℕ) : Finset ℤ := Finset.Icc (-(j : ℤ)) j

def pairs (j : ℕ) : Finset (ℤ × ℤ) := (labels j).product (labels j)

def coordinate (hκ : 0 < κ) (u : L2T L) (a : ℤ) : ℂ :=
  (Def021ChartR41b.chart L κ hκ).Φ u a

def action (hκ : 0 < κ) (u : L2T L) (a : ℤ) : ℝ := ‖coordinate hκ u a‖ ^ 2

def symbol (hκ : 0 < κ) (u : L2T L) (p : ℤ × ℤ) : ℂ :=
  coordinate hκ u p.1 * conj (coordinate hκ u p.2)

def phase (hκ : 0 < κ) (u : L2T L) (p : ℤ × ℤ) : Phase :=
  phaseMul (completePhase (coordinate hκ u p.1))
    ⟨conj (completePhase (coordinate hκ u p.2)).1, by
      rw [Complex.norm_conj, (completePhase _).2]⟩

theorem phase_value (hκ : 0 < κ) (u : L2T L) (p : ℤ × ℤ)
    (ha : 0 < action hκ u p.1) (hb : 0 < action hκ u p.2) :
    (phase hκ u p).1 = symbol hκ u p /
      (‖coordinate hκ u p.1 * coordinate hκ u p.2‖ : ℂ) := by
  have hz : coordinate hκ u p.1 ≠ 0 := by
    intro hz
    simp [action, hz] at ha
  have hw : coordinate hκ u p.2 ≠ 0 := by
    intro hw
    simp [action, hw] at hb
  change (completePhase (coordinate hκ u p.1)).1 *
    conj (completePhase (coordinate hκ u p.2)).1 = _
  simp only [completePhase_nonzero _ hz, completePhase_nonzero _ hw, map_div₀,
    Complex.conj_ofReal, div_mul_div_comm, ← Complex.ofReal_mul, ← norm_mul, symbol]

def eligible (hκ : 0 < κ) (j : ℕ) (α : ℝ) (u : L2T L) : Finset (ℤ × ℤ) :=
  (pairs j).filter fun p => p.1 ≠ p.2 ∧ α ≤ action hκ u p.1 ∧ α ≤ action hκ u p.2

abbrev product (n : ℕ) (u : L2T L) : HN L (n + 1) := HighMomentsOps.wvec (n + 1) u

abbrev coefficientMap (hκ : 0 < κ) (n : ℕ) : HN L (n + 1) ≃ₗᵢ[ℂ] H (n + 1) :=
  occupationCoefficient (UnconditionalBetheBasis.meanField_physicalBasis L (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n)) hκ)

abbrev coefficients (hκ : 0 < κ) (n : ℕ) (u : L2T L) : H (n + 1) :=
  coefficientMap hκ n (product n u)

/-- The actual gauged intensive transfer, including its intensive diagonal. -/
def cartesian (q : FullGauge) (n : ℕ) (p : ℤ × ℤ) : H (n + 1) →L[ℂ] H (n + 1) :=
  sectorEq (n + 1) (fun m => (q n m).1)
    (fun m => by rw [Complex.normSq_eq_norm_sq, (q n m).2]; norm_num) p.1 p.2

def E (hκ : 0 < κ) (q : FullGauge) (n : ℕ) (p : ℤ × ℤ) : HN L (n + 1) →L[ℂ] HN L (n + 1) :=
  (coefficientMap hκ n).conjStarAlgEquiv.symm (cartesian q n p)

def W (hκ : 0 < κ) (q : FullGauge) (n : ℕ) (p : ℤ × ℤ) : HN L (n + 1) →L[ℂ] HN L (n + 1) :=
  (coefficientMap hκ n).conjStarAlgEquiv.symm (FiniteCellGauge.W (q n) p.1 p.2)

/-- The norm in DEF-028, also used for each member of a moving active window. -/
def residual {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (A : V →L[ℂ] V) (z : ℂ) (v : V) : ℝ :=
  ‖(A - z • ContinuousLinearMap.id ℂ V) v‖

theorem residual_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (A : V →L[ℂ] V) (z : ℂ) (v : V) : residual A z v = ‖A v - z • v‖ := rfl

def cartesianError (hκ : 0 < κ) (q : FullGauge) (n : ℕ) (u : L2T L) (p : ℤ × ℤ) : ℝ :=
  residual (E hκ q n p) (symbol hκ u p) (product n u) +
    residual (E hκ q n p).adjoint (conj (symbol hκ u p)) (product n u)

def phaseError (hκ : 0 < κ) (q : FullGauge) (n : ℕ) (u : L2T L) (p : ℤ × ℤ) : ℝ :=
  residual (W hκ q n p) (phase hκ u p).1 (product n u) +
    residual (W hκ q n p).adjoint (conj (phase hκ u p).1) (product n u)

def missingInitial (hκ : 0 < κ) (n : ℕ) (u : L2T L) (p : ℤ × ℤ) : ℝ :=
  ExactShiftResidual.missing p.1 (coefficients hκ n u)

def missingFinal (hκ : 0 < κ) (n : ℕ) (u : L2T L) (p : ℤ × ℤ) : ℝ :=
  ExactShiftResidual.missing p.2 (coefficients hκ n u)

def affinityError (hκ : 0 < κ) (n : ℕ) (u : L2T L) (p : ℤ × ℤ) : ℝ :=
  |affinity p.1 p.2 (coefficients hκ n u) - 1|

def defectError (hκ : 0 < κ) (q : FullGauge) (n : ℕ) (u : L2T L) (p : ℤ × ℤ) : ℝ :=
  |defect p.1 p.2 (edgePhase (q n) p.1 p.2) (phase hκ u p) (coefficients hκ n u)|

/-- Preservation of each occupation outside the transferred labels for every allowed edge. -/
def ExteriorExact : Prop :=
  ∀ (n : ℕ) (a b i : ℤ), i ≠ a → i ≠ b →
    ∀ m : Donor (n + 1) a, (destination (n + 1) a b m).1 i = m.1.1 i

def UniformError (S : Set (L2T L)) (test : ℕ → L2T L → Finset (ℤ × ℤ))
    (error : ℕ → L2T L → ℤ × ℤ → ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ n in atTop, ∀ u ∈ S, ∀ p ∈ test n u, error n u p ≤ ε

/-- R-D51987CA, GAUGE_RETARGETING.tex:239–271. The full printed statement
supplies one gauge on all arrays and one monotone, divergent schedule before
any radius, cutoff, profile or pair. The operators are the prescribed gauge
ratios and intensive weights. The positive-region residual sums and the
three types of support/affinity/defect convergence are uniform Q06 limits. -/
def GaugeRetargetingRD51987CAInput (hκ : 0 < κ) : Prop :=
  ∃ (j : ℕ → ℕ) (q : FullGauge),
    Monotone j ∧ Tendsto j atTop atTop ∧
    (∀ R > 0, UniformError (unitBall (L := L) R)
      (fun n _ => pairs (j n)) (cartesianError hκ q)) ∧
    (∀ R > 0, ∀ α > 0, ∀ ε > 0, ∀ᶠ n in atTop,
      ∀ u ∈ unitBall (L := L) R, ∀ p ∈ eligible hκ (j n) α u,
        phaseError hκ q n u p ≤ ε ∧ missingInitial hκ n u p ≤ ε ∧
          missingFinal hκ n u p ≤ ε ∧ affinityError hκ n u p ≤ ε ∧
          defectError hκ q n u p ≤ ε) ∧
    ExteriorExact

section Suprema

variable {X P : Type*}

/-- The finite maximum has value zero on the empty active set. -/
def maxWithZero (s : Finset P) (f : P → ℝ) : ℝ :=
  (insert 0 (s.image f)).sup' ⟨0, Finset.mem_insert_self 0 _⟩ id

theorem maxWithZero_empty (f : P → ℝ) : maxWithZero ∅ f = 0 := by
  simp [maxWithZero]

theorem maxWithZero_nonneg (s : Finset P) (f : P → ℝ) : 0 ≤ maxWithZero s f :=
  Finset.le_sup' id (Finset.mem_insert_self 0 (s.image f))

theorem maxWithZero_le (s : Finset P) (f : P → ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) (h : ∀ p ∈ s, f p ≤ ε) : maxWithZero s f ≤ ε := by
  apply Finset.sup'_le
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact hε
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    exact h p hp

/-- The supremum over profiles of the maximum over their eligible pairs.
The error functions in this theorem are nonnegative. -/
def supMax (S : Set X) (test : X → Finset P) (error : X → P → ℝ) : ℝ :=
  sSup (insert 0 ((fun u => maxWithZero (test u) (error u)) '' S))

theorem supMax_empty (test : X → Finset P) (error : X → P → ℝ) :
    supMax ∅ test error = 0 := by
  simp [supMax, csSup_singleton]

theorem supMax_tendsto (S : Set X) (test : ℕ → X → Finset P) (error : ℕ → X → P → ℝ)
    (h : ∀ ε > 0, ∀ᶠ n in atTop, ∀ u ∈ S, ∀ p ∈ test n u, error n u p ≤ ε) :
    Tendsto (fun n => supMax S (test n) (error n)) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  filter_upwards [h (ε / 2) hhalf] with n hn
  let M := insert 0 ((fun u => maxWithZero (test n u) (error n u)) '' S)
  have h0 : (0 : ℝ) ∈ M := Set.mem_insert _ _
  have hub : ∀ x ∈ M, x ≤ ε / 2 := by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact hhalf.le
    · obtain ⟨u, hu, rfl⟩ := hx
      exact maxWithZero_le _ _ hhalf.le (hn u hu)
  have hlo : 0 ≤ sSup M := le_csSup ⟨ε / 2, hub⟩ h0
  change dist (sSup M) 0 < ε
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hlo]
  exact (csSup_le ⟨0, h0⟩ hub).trans_lt (half_lt_self hε)

end Suprema

private theorem coefficient_residual (hκ : 0 < κ) (n : ℕ) (u : L2T L)
    (A : H (n + 1) →L[ℂ] H (n + 1)) (z : ℂ) :
    residual ((coefficientMap hκ n).conjStarAlgEquiv.symm A) z (product n u) =
      ‖A (coefficients hκ n u) - z • coefficients hκ n u‖ := by
  rw [residual_apply, LinearIsometryEquiv.symm_conjStarAlgEquiv_apply_apply,
    ← (coefficientMap hκ n).symm_apply_apply (product n u), ← map_smul, ← map_sub,
    LinearIsometryEquiv.norm_map]
  rw [LinearIsometryEquiv.apply_symm_apply]

private theorem coefficient_adjoint (hκ : 0 < κ) (n : ℕ) (A : H (n + 1) →L[ℂ] H (n + 1)) :
    ((coefficientMap (L := L) hκ n).conjStarAlgEquiv.symm A).adjoint =
      (coefficientMap (L := L) hκ n).conjStarAlgEquiv.symm A.adjoint := by
  simpa only [ContinuousLinearMap.star_eq_adjoint] using
    (map_star (coefficientMap (L := L) hκ n).conjStarAlgEquiv.symm A).symm

/-- R-284267AA bounds the four full-array errors by the squared phase residual sum. -/
theorem fullErrors_le (hκ : 0 < κ) (q : FullGauge) (n : ℕ) (u : L2T L)
    (hu : ‖u‖ = 1) (p : ℤ × ℤ) (hp : p.1 ≠ p.2) :
    missingInitial hκ n u p ≤ (phaseError hκ q n u p)^2 ∧
    missingFinal hκ n u p ≤ (phaseError hκ q n u p)^2 ∧
    affinityError hκ n u p ≤ (phaseError hκ q n u p)^2 / 2 ∧
    defectError hκ q n u p ≤ (phaseError hκ q n u p)^2 / 2 := by
  have hg : ‖coefficients hκ n u‖ = 1 := by
    rw [LinearIsometryEquiv.norm_map]
    change ‖TensorCarrier.htpow (n + 1) u‖ = 1
    simp [TensorCarrier.norm_htpow, hu]
  have hW : phaseError hκ q n u p =
      ‖transfer p.1 p.2 (edgePhase (q n) p.1 p.2) (coefficients hκ n u) -
        (phase hκ u p).1 • coefficients hκ n u‖ +
      ‖(transfer p.1 p.2 (edgePhase (q n) p.1 p.2)).adjoint (coefficients hκ n u) -
        conj (phase hκ u p).1 • coefficients hκ n u‖ := by
    simp only [phaseError, W, coefficient_adjoint, coefficient_residual, FiniteCellGauge.W]
  apply ExactShiftResidual.all_errors_le p.1 p.2 hp (edgePhase (q n) p.1 p.2)
    (phase hκ u p) ⟨coefficients hκ n u, hg⟩
  rw [hW]
  nlinarith only [mul_nonneg
    (norm_nonneg (transfer p.1 p.2 (edgePhase (q n) p.1 p.2) (coefficients hκ n u) -
      (phase hκ u p).1 • coefficients hκ n u))
    (norm_nonneg ((transfer p.1 p.2 (edgePhase (q n) p.1 p.2)).adjoint (coefficients hκ n u) -
      conj (phase hκ u p).1 • coefficients hκ n u))]

/-- All the printed static limits for the supplied gauge and active window. -/
def UniformStatic (hκ : 0 < κ) (j : ℕ → ℕ) (q : FullGauge) : Prop :=
  Monotone j ∧ Tendsto j atTop atTop ∧ ExteriorExact ∧
  (∀ R > 0, Tendsto (fun n => supMax (unitBall (L := L) R)
    (fun _ => pairs (j n)) (cartesianError hκ q n)) atTop (𝓝 0)) ∧
  (∀ R > 0, ∀ α > 0,
    let M := fun (error : ℕ → L2T L → ℤ × ℤ → ℝ) (n : ℕ) =>
      supMax (unitBall (L := L) R) (eligible hκ (j n) α) (error n)
    Tendsto (M (phaseError hκ q)) atTop (𝓝 0) ∧
    Tendsto (M (missingInitial hκ)) atTop (𝓝 0) ∧
    Tendsto (M (missingFinal hκ)) atTop (𝓝 0) ∧
    Tendsto (M (affinityError hκ)) atTop (𝓝 0) ∧
    Tendsto (M (defectError hκ q)) atTop (𝓝 0))

/-- Source lines 2–32. The two existential witnesses are returned verbatim. -/
theorem uniform_static_intermediate (hκ : 0 < κ)
    (PredecessorInput : GaugeRetargetingRD51987CAInput (L := L) hκ) :
    ∃ (j : ℕ → ℕ) (q : FullGauge), UniformStatic (L := L) hκ j q := by
  obtain ⟨j, q, hj, hjlim, hcart, hphase, hext⟩ := PredecessorInput
  refine ⟨j, q, hj, hjlim, hext, fun R hR => supMax_tendsto _ _ _ (hcart R hR), ?_⟩
  intro R hR α hα
  have hp ε (hε : 0 < ε) :
      ∀ᶠ n in atTop, ∀ u ∈ unitBall (L := L) R, ∀ p ∈ eligible hκ (j n) α u,
        phaseError hκ q n u p ≤ ε := by
    filter_upwards [hphase R hR α hα ε hε] with n hn
    exact fun u hu p hp => (hn u hu p hp).1
  have hmetrics ε (hε : 0 < ε) :
      ∀ᶠ n in atTop, ∀ u ∈ unitBall (L := L) R, ∀ p ∈ eligible hκ (j n) α u,
        missingInitial hκ n u p ≤ ε ∧ missingFinal hκ n u p ≤ ε ∧
          affinityError hκ n u p ≤ ε ∧ defectError hκ q n u p ≤ ε := by
    let d := min ε 1
    have hd : 0 < d := lt_min hε one_pos
    filter_upwards [hp d hd] with n hn
    intro u hu p hmem
    have hpair := (Finset.mem_filter.mp hmem).2.1
    have hpos : 0 ≤ phaseError hκ q n u p := add_nonneg (norm_nonneg _) (norm_nonneg _)
    have hsq := pow_le_pow_left₀ hpos (hn u hu p hmem) 2
    have hdε : d ≤ ε := min_le_left _ _
    have hd1 : d ≤ 1 := min_le_right _ _
    have hb : (phaseError hκ q n u p)^2 ≤ ε := by
      exact hsq.trans ((by nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hd1)] : d^2 ≤ d).trans hdε)
    have hhalf : (phaseError hκ q n u p)^2 / 2 ≤ ε := by
      linarith [sq_nonneg (phaseError hκ q n u p)]
    obtain ⟨ha, hb', hh, hD⟩ := fullErrors_le hκ q n u hu.1 p hpair
    exact ⟨ha.trans hb, hb'.trans hb, hh.trans hhalf, hD.trans hhalf⟩
  refine ⟨supMax_tendsto _ _ _ hp, supMax_tendsto _ _ _ ?_, supMax_tendsto _ _ _ ?_,
    supMax_tendsto _ _ _ ?_, supMax_tendsto _ _ _ ?_⟩ <;>
    intro ε hε <;>
    filter_upwards [hmetrics ε hε] with n hn <;>
    intro u hu p hmem
  · exact (hn u hu p hmem).1
  · exact (hn u hu p hmem).2.1
  · exact (hn u hu p hmem).2.2.1
  · exact (hn u hu p hmem).2.2.2

end QuantumNLS.UniformStaticR31m

#print axioms QuantumNLS.UniformStaticR31m.GaugeRetargetingRD51987CAInput
#print axioms QuantumNLS.UniformStaticR31m.fullErrors_le
#print axioms QuantumNLS.UniformStaticR31m.uniform_static_intermediate

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "QuantumNLS.UniformStaticR31m." ||
        name.toString.startsWith "_private.QuantumNLS.UniformStaticR31m." then
      pending := pending.push name
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    unless seen.contains name do
      seen := seen.insert name
      if (name.toString.splitOn "HeldGP14Tonelli").length > 1 then
        throwError "Rejected dependency: {name}"
      let some info := env.find? name | throwError "Missing dependency: {name}"
      if let .axiomInfo _ := info then
        unless name == ``propext || name == ``Classical.choice || name == ``Quot.sound do
          throwError "Nonstandard dependency: {name}"
      pending := pending ++ info.type.getUsedConstants
      if let some value := info.value? (allowOpaque := true) then
        pending := pending ++ value.getUsedConstants
  Lean.logInfo m!"R31m aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only."
