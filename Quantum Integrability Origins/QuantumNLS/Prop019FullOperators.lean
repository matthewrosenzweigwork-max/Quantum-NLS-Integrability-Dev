import QuantumNLS.Prop019Discharge

/-! Source-facing event projection and operator binding for Q7A:lem:linearization.
The window packet projection is not the fixed-probe projection P^I_N: they have different
label events. Both use the same frozen Prop017Physical.event_projection construction. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSectionVars false
noncomputable section
open Classical
open MeasureTheory Filter Topology Set
open scoped InnerProductSpace ComplexConjugate
namespace QuantumNLS.Prop019FullOperators
open QuantumNLS.PhysicalTensor (L2T physSector)
open QuantumNLS.BetheLabels (MArr)
open QuantumNLS.UnconditionalBetheBasis (meanField_physicalBasis)
open QuantumNLS.MPContour (ThetaSpace nu zθ uθ rectPieces)
open QuantumNLS.MPFamily (BgFam gθ dθ good)
open QuantumNLS.Prop019Linearization (pw continuous_pw rect_im_ne)
open QuantumNLS.MPOps (C0op Lop)
open QuantumNLS.MixedQuadratures (reOp)
open QuantumNLS.NormalizedTransfer (normalizedTransfer)
open QuantumNLS.FunctionalLinearization (evol)
variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-- The actual packet's diagonal orthogonal projection, including an exact range criterion. -/
theorem projection (hκ : 0 < κ) {N : ℕ} (hN : 1 ≤ N) (u : L2T L) (hu : ‖u‖ = 1)
    (E : Set (MArr N)) :
    ∃ P : QuantumNLS.KernelDefinition.BoundedSymmetricKernel (L2T L) N,
      (∀ m, P (meanField_physicalBasis L N hN hκ m) =
        (if m ∈ E then (1 : ℂ) else 0) • meanField_physicalBasis L N hN hκ m) ∧
      P * P = P ∧ ContinuousLinearMap.adjoint P = P ∧
      ‖(1 - P) (QuantumNLS.HighMomentsOps.wvec N u)‖ ^ 2 =
        (QuantumNLS.EmpiricalRapidity.bornMeasure (QuantumNLS.BulkResponseActual.physBasis L hκ N) u hu).real Eᶜ ∧
      ∀ φ : physSector L N, φ ∈ Set.range P ↔
        ∀ m ∉ E, ⟪meanField_physicalBasis L N hN hκ m, φ⟫_ℂ = 0 := by
  classical
  obtain ⟨P, he, hi, ha, hm⟩ := QuantumNLS.Prop017Physical.event_projection hκ hN u hu E
  refine ⟨P, he, hi, ha, hm, ?_⟩
  let b := meanField_physicalBasis L N hN hκ
  have hc := QuantumNLS.HilbertDiagOp.eig_coeff b P (fun m => if m ∈ E then (1 : ℂ) else 0) he
  intro φ
  constructor
  · rintro ⟨v, rfl⟩ m hm
    rw [hc]; simp [hm]
  · intro hs
    refine ⟨φ, ?_⟩
    apply b.repr.injective
    apply lp.ext
    funext m
    simp only [HilbertBasis.repr_apply_apply]
    rw [hc]
    by_cases hm : m ∈ E
    · simp [hm]
    · simp only [ite_eq_right hm, zero_mul]
      exact (hs m hm).symm

abbrev pieces (a h : ℝ) (d : ℕ) (t : ℝ) (p : ℕ → ℝ) :=
  rectPieces a h (pw d t p) (continuous_pw d t p)

lemma curve_weight (a h : ℝ) (ω ω' : ℂ → ℂ) (hω : Continuous ω) (hω' : Continuous ω')
    (i : Fin 6) (τ : ℝ) :
    (rectPieces a h ω hω i).γ τ = (rectPieces a h ω' hω' i).γ τ := by
  apply Complex.ext
  · exact (QuantumNLS.Prop019Linearization.rect_re_im a h ω hω i τ).1.trans
      (QuantumNLS.Prop019Linearization.rect_re_im a h ω' hω' i τ).1.symm
  · exact (QuantumNLS.Prop019Linearization.rect_re_im a h ω hω i τ).2.trans
      (QuantumNLS.Prop019Linearization.rect_re_im a h ω' hω' i τ).2.symm

lemma point_time (a h : ℝ) (d : ℕ) (t : ℝ) (p : ℕ → ℝ) :
    zθ (pieces a h d t p) = zθ (pieces a h d 1 p) := by
  funext θ
  exact curve_weight a h _ _ _ _ θ.1 θ.2

lemma weight_time (a h : ℝ) (d : ℕ) (t : ℝ) (p : ℕ → ℝ) (θ : ThetaSpace 6) :
    uθ κ (pieces a h d t p) θ = (t : ℂ) * uθ κ (pieces a h d 1 p) θ := by
  have hp : ∀ z, pw d t p z = (t : ℂ) * pw d 1 p z := by
    intro z
    simp only [pw, one_mul, Finset.mul_sum, Complex.ofReal_mul]
    apply Finset.sum_congr rfl
    intro r _hr
    ring
  have hω := QuantumNLS.Prop019Linearization.rect_ω
  have hd : ∀ (i : Fin 6) (τ : ℝ), (pieces a h d t p i).γ' τ = (pieces a h d 1 p i).γ' τ := by
    intro i τ
    simp only [pieces, QuantumNLS.Prop019Linearization.rect_γ']
    rw [curve_weight a h (pw d t p) (pw d 1 p) (continuous_pw d t p) (continuous_pw d 1 p) i 1,
      curve_weight a h (pw d t p) (pw d 1 p) (continuous_pw d t p) (continuous_pw d 1 p) i 0]
  unfold uθ
  rw [hd, point_time a h d t p]
  simp only [pieces, hω, hp]
  ring

-- Generic version used on every particle sector.
lemma reOp_real_smul {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (t : ℝ) (X : H →L[ℂ] H) : reOp ((t : ℂ) • X) = (t : ℂ) • reOp X := by
  simp only [reOp, map_smulₛₗ, Complex.conj_ofReal, smul_add, smul_smul]
  module

section Weight
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Θ : Type*} [MeasurableSpace Θ]
lemma C0op_weight (ν : Measure Θ) (S : Θ → H →L[ℂ] H) (u : Θ → ℂ) (g : Θ → ℂ → ℂ) (t : ℝ) :
    C0op ν S (fun θ => (t : ℂ) * u θ) g = (t : ℂ) • C0op ν S u g := by
  unfold C0op
  simp only [mul_smul]
  rw [integral_smul, reOp_real_smul]
lemma Lop_weight (ν : Measure Θ) (S : Θ → H →L[ℂ] H) (u d : Θ → ℂ) (t : ℝ) :
    Lop ν S (fun θ => (t : ℂ) * u θ) d = (t : ℂ) • Lop ν S u d := by
  unfold Lop
  simp only [mul_assoc, mul_smul]
  rw [integral_smul, reOp_real_smul]
end Weight

variable {Z : Set ℂ} {d₀ s₁ a₀ c₁ : ℝ}

/-- The printed nonlinear contour operator C_{0,N,p}. -/
def C0 (N : ℕ) (a h : ℝ) (d : ℕ) (p : ℕ → ℝ) (B : BgFam Z d₀ s₁ a₀ c₁) :=
  C0op (nu 6) (fun θ => normalizedTransfer L κ N (zθ (pieces a h d 1 p) θ))
    (uθ κ (pieces a h d 1 p)) (gθ (pieces a h d 1 p) B)

/-- The literal linear operator -Re ∮ p(z) S_N(z)/D(z) dz /(2πκ).
The contour integral is parametrized by its six printed oriented affine pieces. -/
def Linear (N : ℕ) (a h : ℝ) (d : ℕ) (p : ℕ → ℝ) (D : ℂ → ℂ) :=
  reOp (∫ θ : ThetaSpace 6, (uθ κ (pieces a h d 1 p) θ * (D (zθ (pieces a h d 1 p) θ))⁻¹) •
    normalizedTransfer L κ N (zθ (pieces a h d 1 p) θ) ∂(nu 6))

lemma good_ae (a h : ℝ) (hh : 0 < h) (d : ℕ) (t : ℝ) (p : ℕ → ℝ) :
    ∀ᵐ θ ∂(nu 6), good (pieces a h d t p) θ := by
  have he : ∀ᵐ τ : unitInterval, τ ≠ 0 ∧ τ ≠ 1 := ((volume : Measure unitInterval).ae_ne 0).and ((volume : Measure unitInterval).ae_ne 1)
  have ht : ∀ᵐ θ ∂(nu 6), θ.2 ≠ (0 : unitInterval) ∧ θ.2 ≠ 1 := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
    exact ae_of_all _ fun _ => he
  filter_upwards [ht] with θ hθ
  apply rect_im_ne hh _ _ θ.1
  exact ⟨lt_of_le_of_ne θ.2.2.1 (fun he => hθ.1 (Subtype.ext he.symm)),
    lt_of_le_of_ne θ.2.2.2 (fun he => hθ.2 (Subtype.ext he))⟩

/-- Endpoints on the real axis have zero measure, so the chart's masked derivative
is exactly the printed full D^{-1} in the operator integral. -/
lemma linear_eq_Lop (N : ℕ) (a h : ℝ) (hh : 0 < h) (d : ℕ) (p : ℕ → ℝ)
    (B : BgFam Z d₀ s₁ a₀ c₁) :
    Linear (L := L) (κ := κ) N a h d p B.D =
      Lop (nu 6) (fun θ => normalizedTransfer L κ N (zθ (pieces a h d 1 p) θ))
        (uθ κ (pieces a h d 1 p)) (dθ (pieces a h d 1 p) B) := by
  unfold Linear Lop
  congr 1
  apply integral_congr_ae
  filter_upwards [good_ae a h hh d 1 p] with θ hθ
  simp only [dθ, ite_eq_left hθ]

lemma operators_time (N : ℕ) (a h : ℝ) (hh : 0 < h) (d : ℕ) (t : ℝ) (p : ℕ → ℝ)
    (B : BgFam Z d₀ s₁ a₀ c₁) :
    C0op (nu 6) (fun θ => normalizedTransfer L κ N (zθ (pieces a h d t p) θ))
      (uθ κ (pieces a h d t p)) (gθ (pieces a h d t p) B) = (t : ℂ) • C0 (L := L) (κ := κ) N a h d p B ∧
    Lop (nu 6) (fun θ => normalizedTransfer L κ N (zθ (pieces a h d t p) θ))
      (uθ κ (pieces a h d t p)) (dθ (pieces a h d t p) B) = (t : ℂ) • Linear (L := L) (κ := κ) N a h d p B.D := by
  have hg : gθ (pieces a h d t p) B = gθ (pieces a h d 1 p) B := by
    unfold gθ good; rw [point_time]
  have hd : dθ (pieces a h d t p) B = dθ (pieces a h d 1 p) B := by
    unfold dθ good; rw [point_time]
  have hu : uθ κ (pieces a h d t p) = fun θ => (t : ℂ) * uθ κ (pieces a h d 1 p) θ :=
    funext (weight_time a h d t p)
  constructor
  · simp only [hg, hu, point_time a h d t p]
    exact C0op_weight _ _ _ _ t
  · rw [linear_eq_Lop (L := L) (κ := κ) N a h hh d p B]
    simp only [hd, hu, point_time a h d t p]
    exact Lop_weight _ _ _ _ t

lemma evol_time {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : ℕ) (t : ℝ) (A : H →L[ℂ] H) :
    evol ((N : ℂ) • ((t : ℂ) • A)) 1 = evol ((N : ℂ) • A) t := by
  simp only [evol, neg_smul, one_smul]
  congr 1
  rw [← Complex.coe_smul]
  module

end QuantumNLS.Prop019FullOperators
set_option pp.fullNames true
#print axioms QuantumNLS.Prop019FullOperators.projection
#print axioms QuantumNLS.Prop019FullOperators.linear_eq_Lop
#print axioms QuantumNLS.Prop019FullOperators.operators_time
#print axioms QuantumNLS.Prop019FullOperators.evol_time

namespace QuantumNLS.Prop019FullOperators
open QuantumNLS.PhysicalTensor (L2T physSector)
open QuantumNLS.BetheLabels (MArr)
open QuantumNLS.UnconditionalBetheBasis (meanField_physicalBasis)
variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}
/-- Named source projection; all fields are proved by the frozen diagonal construction. -/
structure EventProjection (hκ : 0 < κ) {N : ℕ} (hN : 1 ≤ N) (u : L2T L) (hu : ‖u‖ = 1)
    (E : Set (MArr N)) where
  op : QuantumNLS.KernelDefinition.BoundedSymmetricKernel (L2T L) N
  eigen : ∀ m, op (meanField_physicalBasis L N hN hκ m) =
    (if m ∈ E then (1 : ℂ) else 0) • meanField_physicalBasis L N hN hκ m
  idempotent : op * op = op
  selfadjoint : ContinuousLinearMap.adjoint op = op
  mass : ‖(1 - op) (QuantumNLS.HighMomentsOps.wvec N u)‖ ^ 2 =
    (QuantumNLS.EmpiricalRapidity.bornMeasure (QuantumNLS.BulkResponseActual.physBasis L hκ N) u hu).real Eᶜ
  range_iff : ∀ φ : physSector L N, φ ∈ Set.range op ↔
    ∀ m ∉ E, ⟪meanField_physicalBasis L N hN hκ m, φ⟫_ℂ = 0

noncomputable def eventProjection (hκ : 0 < κ) {N : ℕ} (hN : 1 ≤ N) (u : L2T L) (hu : ‖u‖ = 1)
    (E : Set (MArr N)) : EventProjection hκ hN u hu E :=
  let ex := projection hκ hN u hu E
  ⟨ex.choose, ex.choose_spec.1, ex.choose_spec.2.1, ex.choose_spec.2.2.1,
    ex.choose_spec.2.2.2.1, ex.choose_spec.2.2.2.2⟩
end QuantumNLS.Prop019FullOperators
#print axioms QuantumNLS.Prop019FullOperators.eventProjection

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop019FullOperators." then
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
