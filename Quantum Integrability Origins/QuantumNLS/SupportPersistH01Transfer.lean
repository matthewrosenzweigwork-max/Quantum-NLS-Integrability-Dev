import QuantumNLS.SupportPersistH01Born

/-! SupportPersistH01Transfer: persistence of the support conclusions of thm:uniform-static
(missing initial and final support probabilities vanish uniformly on the positively
restricted set) under uniformly norm-close normalized preparations
(principal_correspondence.tex line 31, gap G2).

Hypothesis (sup form, printed "uniformly norm-close"): the supremum over the unit ball U_R of
‖ψ_N(u) − u^{⊗N}‖ tends to zero. Normalization: ‖ψ_N(u)‖ = 1 for u in U_R (eventually).
Conclusion: the supremum over u in U_R and over eligible pairs (a, b) with a ≠ b and
α ≤ a_a(u), a_b(u) of the Born support probabilities of ψ_N(u) tends to zero, exactly as the
product-law clause of UniformStaticR49b.UniformStatic does for u^{⊗N}.
The affinity and complex defect are NOT claimed here: principal_correspondence.tex line 31
states that they refer to the original product law. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
open Set Filter Topology
open scoped ComplexConjugate InnerProductSpace

namespace QuantumNLS.SupportPersistH01Transfer
open PhysicalTensor BetheLabels BetheCoefficientTransform
open QuantumNLS.SupportPersistH01Born
variable {L κ : ℝ} [Fact (0 < L)]

/-- Sup form of uniform norm-closeness: sup over U_R of ‖ψ_N(u) − u^{⊗N}‖ → 0,
with the supremum taken as in the printed convention (zero for an empty class). -/
def UniformlyClose (R : ℝ) (ψ : ∀ n : ℕ, L2T L → HN L (n+1)) : Prop :=
  Tendsto (fun n => sSup (insert 0 ((fun u => ‖ψ n u - UniformStaticR49b.product n u‖) ''
    RetargetRoughR48b.unitBall (L := L) R))) atTop (𝓝 0)

/-- Every preparation over U_R is normalized, for all large N. -/
def NormalizedOn (R : ℝ) (ψ : ∀ n : ℕ, L2T L → HN L (n+1)) : Prop :=
  ∀ᶠ n in atTop, ∀ u ∈ RetargetRoughR48b.unitBall (L := L) R, ‖ψ n u‖ = 1

theorem tendsto_zero_of_bounds {f : ℕ → ℝ} (h0 : ∀ n, 0 ≤ f n)
    (h : ∀ ε > 0, ∀ᶠ n in atTop, f n ≤ ε) : Tendsto f atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [h (ε / 2) (half_pos hε)] with n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (h0 n)]
  linarith

theorem maxWithZero_nonneg {P : Type*} (s : Finset P) (f : P → ℝ) :
    0 ≤ UniformStaticR49b.maxWithZero s f :=
  Finset.le_sup' id (Finset.mem_insert_self (0 : ℝ) _)

theorem le_maxWithZero {P : Type*} (s : Finset P) (f : P → ℝ) {p : P} (hp : p ∈ s) :
    f p ≤ UniformStaticR49b.maxWithZero s f :=
  Finset.le_sup' id (Finset.mem_insert_of_mem (Finset.mem_image_of_mem f hp))

/-- From a uniform (in u ∈ S) eventual bound and a sup-tendsto, the pointwise values are
eventually uniformly small. -/
theorem eventually_le_of_sup {X : Type*} (S : Set X) (F : ℕ → X → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ᶠ n in atTop, ∀ u ∈ S, F n u ≤ C)
    (h : Tendsto (fun n => sSup (insert 0 (F n '' S))) atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ u ∈ S, F n u ≤ ε := by
  intro ε hε
  filter_upwards [hF, Metric.tendsto_nhds.mp h ε hε] with n hFn hn u hu
  have hbdd : BddAbove (insert 0 (F n '' S)) := by
    refine ⟨C, ?_⟩
    rintro x (rfl | ⟨v, hv, rfl⟩)
    · exact hC
    · exact hFn v hv
  have hle : F n u ≤ sSup (insert 0 (F n '' S)) :=
    le_csSup hbdd (Set.mem_insert_of_mem _ ⟨u, hu, rfl⟩)
  rw [Real.dist_eq, sub_zero] at hn
  exact hle.trans (abs_lt.mp hn).2.le

/-- Product-law sup-tendsto gives pointwise eventual smallness of each eligible error. -/
theorem product_pointwise {X P : Type*} (S : Set X) (test : ℕ → X → Finset P)
    (err : ℕ → X → P → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hbd : ∀ n, ∀ u ∈ S, ∀ p ∈ test n u, err n u p ≤ C)
    (htend : Tendsto (fun n => UniformStaticR49b.supMax S (test n) (err n)) atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ u ∈ S, ∀ p ∈ test n u, err n u p ≤ ε := by
  intro ε hε
  have hF : ∀ᶠ n in atTop, ∀ u ∈ S, UniformStaticR49b.maxWithZero (test n u) (err n u) ≤ C :=
    Filter.Eventually.of_forall fun n u hu =>
      UniformStaticR49b.maxWithZero_le _ _ hC (fun p hp => hbd n u hu p hp)
  filter_upwards [eventually_le_of_sup S (fun n u => UniformStaticR49b.maxWithZero (test n u) (err n u))
    hC hF htend ε hε] with n hn
  intro u hu p hp
  exact (le_maxWithZero _ _ hp).trans (hn u hu)

/-- Core transfer: an eligible product-law bound on the label `ℓ p`, plus uniform norm-closeness
and normalization, gives the same bound for the general preparation. -/
theorem persist_label (hκ : 0 < κ) (j : ℕ → ℕ) (α R : ℝ)
    (ψ : ∀ n : ℕ, L2T L → HN L (n+1))
    (hnorm : NormalizedOn (L := L) R ψ) (hclose : UniformlyClose (L := L) R ψ)
    (ℓ : ℤ × ℤ → ℤ)
    (hprod : ∀ ε > 0, ∀ᶠ n in atTop, ∀ u ∈ RetargetRoughR48b.unitBall (L := L) R,
      ∀ p ∈ UniformStaticR49b.eligible hκ (j (n+1)) α u,
        bornEmpty (Def044D1SpectralR51a.basis (L := L) hκ n) (ℓ p) (UniformStaticR49b.product n u) ≤ ε) :
    Tendsto (fun n => UniformStaticR49b.supMax (RetargetRoughR48b.unitBall (L := L) R)
      (UniformStaticR49b.eligible hκ (j (n+1)) α)
      (fun u p => bornEmpty (Def044D1SpectralR51a.basis (L := L) hκ n) (ℓ p) (ψ n u)))
      atTop (𝓝 0) := by
  have hF2 : ∀ᶠ n in atTop, ∀ u ∈ RetargetRoughR48b.unitBall (L := L) R,
      ‖ψ n u - UniformStaticR49b.product n u‖ ≤ 2 := by
    filter_upwards [hnorm] with n hn u hu
    calc ‖ψ n u - UniformStaticR49b.product n u‖ ≤ ‖ψ n u‖ + ‖UniformStaticR49b.product n u‖ :=
          norm_sub_le _ _
      _ = 2 := by rw [hn u hu, product_norm_eq_one hκ n u hu.1]; norm_num
  apply tendsto_zero_of_bounds
  · intro n
    unfold UniformStaticR49b.supMax
    apply Real.sSup_nonneg
    rintro x (rfl | ⟨u, _, rfl⟩)
    · exact le_rfl
    · exact maxWithZero_nonneg _ _
  · intro ε hε
    have hp := hprod (ε / 4) (div_pos hε (by norm_num))
    have hd := eventually_le_of_sup (RetargetRoughR48b.unitBall (L := L) R)
      (fun n u => ‖ψ n u - UniformStaticR49b.product n u‖) (C := 2) (by norm_num) hF2 hclose
      (ε / 8) (div_pos hε (by norm_num))
    filter_upwards [hp, hd, hnorm] with n hpn hdn hnn
    unfold UniformStaticR49b.supMax
    apply csSup_le (Set.insert_nonempty _ _)
    rintro x (rfl | ⟨u, hu, rfl⟩)
    · exact hε.le
    · apply UniformStaticR49b.maxWithZero_le _ _ hε.le
      intro p hp
      show bornEmpty (Def044D1SpectralR51a.basis (L := L) hκ n) (ℓ p) (ψ n u) ≤ ε
      have hL := bornEmpty_lipschitz (Def044D1SpectralR51a.basis (L := L) hκ n) (ℓ p)
        (ψ n u) (UniformStaticR49b.product n u) (hnn u hu).le
        (product_norm_eq_one hκ n u hu.1).le
      have h2 := hpn u hu p hp
      have h3 := hdn u hu
      have h5 := le_abs_self (bornEmpty (Def044D1SpectralR51a.basis (L := L) hκ n) (ℓ p) (ψ n u) -
        bornEmpty (Def044D1SpectralR51a.basis (L := L) hκ n) (ℓ p) (UniformStaticR49b.product n u))
      linarith

/-- **Persistence of the support conclusions of thm:uniform-static** (principal_correspondence.tex
line 31) under uniformly norm-close normalized preparations. Input: any object `hS` of the printed
static statement `UniformStatic` (its product-law support clauses are used), a sup-form uniform
norm-closeness hypothesis, and normalization on U_R. Output: the missing initial (label a = p.1)
and missing final (label b = p.2) Born probabilities of `ψ_N(u)` vanish uniformly on the eligible
pairs. -/
theorem support_persistence (hκ : 0 < κ) (j : ℕ → ℕ) (q : UniformStaticR49b.SectorGauge)
    (hS : UniformStaticR49b.UniformStatic (L := L) hκ j q)
    (ψ : ∀ n : ℕ, L2T L → HN L (n+1)) {R : ℝ} (hR : 0 < R) {α : ℝ} (hα : 0 < α)
    (hnorm : NormalizedOn (L := L) R ψ) (hclose : UniformlyClose (L := L) R ψ) :
    Tendsto (fun n => UniformStaticR49b.supMax (RetargetRoughR48b.unitBall (L := L) R)
        (UniformStaticR49b.eligible hκ (j (n+1)) α)
        (fun u p => bornEmpty (Def044D1SpectralR51a.basis (L := L) hκ n) p.1 (ψ n u)))
        atTop (𝓝 0) ∧
    Tendsto (fun n => UniformStaticR49b.supMax (RetargetRoughR48b.unitBall (L := L) R)
        (UniformStaticR49b.eligible hκ (j (n+1)) α)
        (fun u p => bornEmpty (Def044D1SpectralR51a.basis (L := L) hκ n) p.2 (ψ n u)))
        atTop (𝓝 0) := by
  unfold UniformStaticR49b.UniformStatic at hS
  obtain ⟨-, -, -, -, hL⟩ := hS
  have h := hL R hR α hα
  have hI : Tendsto (fun n => UniformStaticR49b.supMax (RetargetRoughR48b.unitBall (L := L) R)
      (UniformStaticR49b.eligible hκ (j (n+1)) α) (UniformStaticR49b.missingInitial hκ n))
      atTop (𝓝 0) := h.2.1
  have hF : Tendsto (fun n => UniformStaticR49b.supMax (RetargetRoughR48b.unitBall (L := L) R)
      (UniformStaticR49b.eligible hκ (j (n+1)) α) (UniformStaticR49b.missingFinal hκ n))
      atTop (𝓝 0) := h.2.2.1
  have hbdI : ∀ n, ∀ u ∈ RetargetRoughR48b.unitBall (L := L) R,
      ∀ p ∈ UniformStaticR49b.eligible hκ (j (n+1)) α u,
        UniformStaticR49b.missingInitial hκ n u p ≤ 1 :=
    fun n u hu p _ => missingInitial_le_one hκ n u hu.1 p
  have hbdF : ∀ n, ∀ u ∈ RetargetRoughR48b.unitBall (L := L) R,
      ∀ p ∈ UniformStaticR49b.eligible hκ (j (n+1)) α u,
        UniformStaticR49b.missingFinal hκ n u p ≤ 1 :=
    fun n u hu p _ => missingFinal_le_one hκ n u hu.1 p
  have hpI := product_pointwise (RetargetRoughR48b.unitBall (L := L) R)
    (fun n => UniformStaticR49b.eligible hκ (j (n+1)) α) (fun n => UniformStaticR49b.missingInitial hκ n)
    zero_le_one hbdI hI
  have hpF := product_pointwise (RetargetRoughR48b.unitBall (L := L) R)
    (fun n => UniformStaticR49b.eligible hκ (j (n+1)) α) (fun n => UniformStaticR49b.missingFinal hκ n)
    zero_le_one hbdF hF
  have hprodI : ∀ ε > 0, ∀ᶠ n in atTop, ∀ u ∈ RetargetRoughR48b.unitBall (L := L) R,
      ∀ p ∈ UniformStaticR49b.eligible hκ (j (n+1)) α u,
        bornEmpty (Def044D1SpectralR51a.basis (L := L) hκ n) (Prod.fst p)
          (UniformStaticR49b.product n u) ≤ ε := by
    intro ε hε
    filter_upwards [hpI ε hε] with n hn u hu p hp
    rw [← missingInitial_eq_bornEmpty]
    exact hn u hu p hp
  have hprodF : ∀ ε > 0, ∀ᶠ n in atTop, ∀ u ∈ RetargetRoughR48b.unitBall (L := L) R,
      ∀ p ∈ UniformStaticR49b.eligible hκ (j (n+1)) α u,
        bornEmpty (Def044D1SpectralR51a.basis (L := L) hκ n) (Prod.snd p)
          (UniformStaticR49b.product n u) ≤ ε := by
    intro ε hε
    filter_upwards [hpF ε hε] with n hn u hu p hp
    rw [← missingFinal_eq_bornEmpty]
    exact hn u hu p hp
  exact ⟨persist_label hκ j α R ψ hnorm hclose Prod.fst hprodI,
    persist_label hκ j α R ψ hnorm hclose Prod.snd hprodF⟩

/-- The same persistence statement at the Q06-selected static object
(`UniformStaticR49b.selected_uniform_static`, schedule `particleStage`, gauge `sectorGauge`). -/
theorem selected_support_persistence (hκ : 0 < κ) (ψ : ∀ n : ℕ, L2T L → HN L (n+1))
    {R : ℝ} (hR : 0 < R) {α : ℝ} (hα : 0 < α)
    (hnorm : NormalizedOn (L := L) R ψ) (hclose : UniformlyClose (L := L) R ψ) :
    Tendsto (fun n => UniformStaticR49b.supMax (RetargetRoughR48b.unitBall (L := L) R)
        (UniformStaticR49b.eligible hκ (RetargetSelectionR49b.particleStage (L := L) hκ (n+1)) α)
        (fun u p => bornEmpty (Def044D1SpectralR51a.basis (L := L) hκ n) p.1 (ψ n u)))
        atTop (𝓝 0) ∧
    Tendsto (fun n => UniformStaticR49b.supMax (RetargetRoughR48b.unitBall (L := L) R)
        (UniformStaticR49b.eligible hκ (RetargetSelectionR49b.particleStage (L := L) hκ (n+1)) α)
        (fun u p => bornEmpty (Def044D1SpectralR51a.basis (L := L) hκ n) p.2 (ψ n u)))
        atTop (𝓝 0) :=
  support_persistence hκ _ _ (UniformStaticR49b.selected_uniform_static (L := L) hκ) ψ hR hα hnorm hclose

end QuantumNLS.SupportPersistH01Transfer

#print axioms QuantumNLS.SupportPersistH01Transfer.tendsto_zero_of_bounds
#print axioms QuantumNLS.SupportPersistH01Transfer.product_pointwise
#print axioms QuantumNLS.SupportPersistH01Transfer.persist_label
#print axioms QuantumNLS.SupportPersistH01Transfer.support_persistence
#print axioms QuantumNLS.SupportPersistH01Transfer.selected_support_persistence

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "QuantumNLS.SupportPersistH01" ||
        name.toString.startsWith "_private.QuantumNLS.SupportPersistH01" then
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
      if (name.toString.splitOn "RegularCut").length > 1 then
        throwError "Rejected dependency: {name}"
      if let some info := env.find? name then
        match info with
        | .axiomInfo _ =>
          unless name == ``propext || name == ``Classical.choice || name == ``Quot.sound do
            throwError "Nonstandard dependency: {name}"
        | _ => pure ()
        pending := pending ++ info.type.getUsedConstants
        if let some value := info.value? (allowOpaque := true) then
          pending := pending ++ value.getUsedConstants
      else
        throwError "Missing dependency: {name}"
  Lean.logInfo m!"SupportPersistH01 aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only; no HeldGP14Tonelli or RegularCut."
