import QuantumNLS.RetargetBallR49b

/-! R-D2F4CE8F for the named rebuilt Q06 schedule and gauge. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
open Set Filter Topology
open scoped ComplexConjugate Classical

namespace QuantumNLS.UniformStaticR49b
open PhysicalTensor BetheCoefficientTransform Occupation OccupationHilbert FullOccupationAffinity FiniteCellGauge
open RetargetAnglesR48b RetargetStageR48b RetargetWeightsR48b RetargetCellR48b
open RetargetRoughR48b RetargetSelectionR49b RetargetPhysicalR48b RetargetBallR49b
variable {L κ : ℝ} [Fact (0 < L)]

abbrev SectorGauge := ∀ n : ℕ, Arr (n+1) → Phase

def pairs (j : ℕ) : Finset (ℤ × ℤ) := (labels j).product (labels j)

def action (hκ : 0 < κ) (u : L2T L) (a : ℤ) : ℝ := ‖coordinate hκ u a‖^2

def symbol (hκ : 0 < κ) (u : L2T L) (p : ℤ × ℤ) : ℂ :=
  coordinate hκ u p.1 * conj (coordinate hκ u p.2)

def phase (hκ : 0 < κ) (u : L2T L) (p : ℤ × ℤ) : Phase :=
  phaseMul (FiniteCellSupport.completePhase (coordinate hκ u p.1))
    ⟨conj (FiniteCellSupport.completePhase (coordinate hκ u p.2)).1, by
      rw [Complex.norm_conj, (FiniteCellSupport.completePhase _).2]⟩

theorem phase_eq_pairPhase (hκ : 0 < κ) (u : L2T L) (p : ℤ × ℤ) :
    phase hκ u p = pairPhase (coordinate hκ u p.1) (coordinate hκ u p.2) := by
  apply Subtype.ext
  rfl

/-- The finite-cell target is the literal phase of the printed Cartesian symbol
on every positively tested edge. -/
theorem phase_value (hκ : 0 < κ) (u : L2T L) (p : ℤ × ℤ)
    (ha : 0 < action hκ u p.1) (hb : 0 < action hκ u p.2) :
    (phase hκ u p).1 = symbol hκ u p /
      (‖coordinate hκ u p.1 * coordinate hκ u p.2‖ : ℂ) := by
  have nonzero (a : ℤ) (h : 0 < action hκ u a) : coordinate hκ u a ≠ 0 := by
    intro hz
    simp [action, hz] at h
  rw [phase_eq_pairPhase]
  exact FiniteCellFinal.completePhase_symbol _ _ (nonzero _ ha) (nonzero _ hb)

def eligible (hκ : 0 < κ) (j : ℕ) (α : ℝ) (u : L2T L) : Finset (ℤ × ℤ) :=
  (pairs j).filter fun p => p.1 ≠ p.2 ∧ α ≤ action hκ u p.1 ∧ α ≤ action hκ u p.2

theorem mem_pairs {j : ℕ} {p : ℤ × ℤ} :
    p ∈ pairs j ↔ p.1 ∈ labels j ∧ p.2 ∈ labels j :=
  Finset.mem_product

abbrev product (n : ℕ) (u : L2T L) : HN L (n+1) := HighMomentsOps.wvec (n+1) u

def E (hκ : 0 < κ) (q : SectorGauge) (n : ℕ) (p : ℤ × ℤ) : HN L (n+1) →L[ℂ] HN L (n+1) :=
  physical (Def044D1SpectralR51a.basis hκ n) (cartesian (q n) p.1 p.2)

def W (hκ : 0 < κ) (q : SectorGauge) (n : ℕ) (p : ℤ × ℤ) : HN L (n+1) →L[ℂ] HN L (n+1) :=
  physical (Def044D1SpectralR51a.basis hκ n) (FiniteCellGauge.W (q n) p.1 p.2)

open BetheLabels BetheCoefficientTransform in
/-- The physical gauge is the frozen Q06 cell-path scalar on every corrected
array of the selected sector. The cell width is fixed for the whole stage. -/
theorem selected_particle_gauge (hκ : 0 < κ) (n : ℕ)
    (hn : 0 < particleStage (L := L) hκ (n+1)) :
    let j := particleStage (L := L) hκ (n+1)
    ∃ c : SelectedSeeds (labels j) (n+1), ∀ m : MArr (n+1),
      particleGauge (L := L) hκ (n+1) m =
        q_N (labels j) (stageWidth (L := L) hκ j) c (marrArr (n+1) m) := by
  obtain ⟨c, hc⟩ := (sector_gauge_stage (L := L) hκ n hn).2.2.2
  exact ⟨c, fun m => congrFun hc (marrArr (n+1) m)⟩

open BetheLabels in
/-- The physical operator uses the very same complete-array gauge that was
selected at the largest eligible stage, including the empty-donor case. -/
theorem selected_W_basis (hκ : 0 < κ) (n : ℕ) (p : ℤ × ℤ) (m : MArr (n+1)) :
    let B := Def044D1SpectralR51a.basis (L := L) hκ n
    W hκ (sectorGauge (L := L) hκ) n p (B m) =
      if hd : DonorOK p.1 m.val then
        let d := DynSeedGradingR47b.transfer p.1 p.2 m hd
        ((particleGauge (L := L) hκ (n+1) m).1 *
          conj (particleGauge (L := L) hκ (n+1) d).1) • B d
      else 0 :=
  physical_phase_ratio (L := L) hκ n (sectorGauge (L := L) hκ) p.1 p.2 m

def cartesianError (hκ : 0 < κ) (q : SectorGauge) (n : ℕ) (u : L2T L) (p : ℤ × ℤ) : ℝ :=
  ‖E hκ q n p (product n u) - symbol hκ u p • product n u‖ +
    ‖(E hκ q n p).adjoint (product n u) - conj (symbol hκ u p) • product n u‖

def phaseError (hκ : 0 < κ) (q : SectorGauge) (n : ℕ) (u : L2T L) (p : ℤ × ℤ) : ℝ :=
  ‖W hκ q n p (product n u) - (phase hκ u p).1 • product n u‖ +
    ‖(W hκ q n p).adjoint (product n u) - conj (phase hκ u p).1 • product n u‖

def missingInitial (hκ : 0 < κ) (n : ℕ) (u : L2T L) (p : ℤ × ℤ) : ℝ :=
  ExactShiftResidual.missing p.1 (coefficients hκ n u)

def missingFinal (hκ : 0 < κ) (n : ℕ) (u : L2T L) (p : ℤ × ℤ) : ℝ :=
  ExactShiftResidual.missing p.2 (coefficients hκ n u)

def affinityError (hκ : 0 < κ) (n : ℕ) (u : L2T L) (p : ℤ × ℤ) : ℝ :=
  |affinity p.1 p.2 (coefficients hκ n u) - 1|

def defectError (hκ : 0 < κ) (q : SectorGauge) (n : ℕ) (u : L2T L) (p : ℤ × ℤ) : ℝ :=
  |defect p.1 p.2 (edgePhase (q n) p.1 p.2) (phase hκ u p) (coefficients hκ n u)|

/-- Every allowed donor-to-receiver edge preserves the entire exterior array. -/
def ExteriorExact : Prop :=
  ∀ (N : ℕ) (a b i : ℤ), i ≠ a → i ≠ b →
    ∀ m : Donor N a, (destination N a b m).1 i = m.1.1 i

theorem exterior_exact : ExteriorExact := by
  intro N a b i hia hib m
  exact FiniteCellSupport.destination_exterior a b i hia hib m

section Suprema

variable {X P : Type*}

/-- Finite maximum of a nonnegative error, including zero on the empty set. -/
def maxWithZero (s : Finset P) (f : P → ℝ) : ℝ :=
  (insert 0 (s.image f)).sup' ⟨0, Finset.mem_insert_self 0 _⟩ id

theorem maxWithZero_empty (f : P → ℝ) : maxWithZero ∅ f = 0 := by
  simp [maxWithZero]

theorem maxWithZero_le (s : Finset P) (f : P → ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) (h : ∀ p ∈ s, f p ≤ ε) : maxWithZero s f ≤ ε := by
  apply Finset.sup'_le
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact hε
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    exact h p hp

/-- The supremum over profiles of their eligible maximum, with empty value zero. -/
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

/-- The printed static assertion. Its gauge is converted to every physical
sector by the frozen corrected-occupation identification. -/
def UniformStatic (hκ : 0 < κ) (j : ℕ → ℕ) (q : SectorGauge) : Prop :=
  Monotone j ∧ Tendsto j atTop atTop ∧ ExteriorExact ∧
  (∀ R > 0, Tendsto (fun n => supMax (unitBall (L := L) R)
    (fun _ => pairs (j (n+1))) (cartesianError hκ q n)) atTop (𝓝 0)) ∧
  (∀ R > 0, ∀ α > 0,
    let M := fun (error : ℕ → L2T L → ℤ × ℤ → ℝ) (n : ℕ) =>
      supMax (unitBall (L := L) R) (eligible hκ (j (n+1)) α) (error n)
    Tendsto (M (phaseError hκ q)) atTop (𝓝 0) ∧
    Tendsto (M (missingInitial hκ)) atTop (𝓝 0) ∧
    Tendsto (M (missingFinal hκ)) atTop (𝓝 0) ∧
    Tendsto (M (affinityError hκ)) atTop (𝓝 0) ∧
    Tendsto (M (defectError hκ q)) atTop (𝓝 0))

private theorem cartesian_bound (hκ : 0 < κ) (R ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ u ∈ unitBall (L := L) R, ∀ p ∈ pairs (particleStage (L := L) hκ (n+1)),
      cartesianError hκ (sectorGauge (L := L) hκ) n u p ≤ ε := by
  have h := physical_cartesian_limit hκ _ _ (selected_gauge_conclusion (L := L) hκ) R ε hε
  filter_upwards [h] with n hn
  intro u hu p hp
  obtain ⟨ha, hb⟩ := mem_pairs.mp hp
  exact hn u hu ⟨p.1, ha⟩ ⟨p.2, hb⟩

private theorem phase_bounds (hκ : 0 < κ) (R α ε : ℝ) (hα : 0 < α) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ u ∈ unitBall (L := L) R,
      ∀ p ∈ eligible hκ (particleStage (L := L) hκ (n+1)) α u,
        phaseError hκ (sectorGauge (L := L) hκ) n u p ≤ ε ∧
        missingInitial hκ n u p ≤ ε ∧ missingFinal hκ n u p ≤ ε ∧ affinityError hκ n u p ≤ ε ∧
        defectError hκ (sectorGauge (L := L) hκ) n u p ≤ ε := by
  let s := sectorStage (L := L) hκ
  let q := sectorGauge (L := L) hκ
  have h := selected_gauge_conclusion (L := L) hκ
  filter_upwards [physical_phase_limit hκ s q h R α (ε/2) hα (half_pos hε),
    h.2.2.2 R α ε hα hε] with n hphys hcoeff
  intro u hu p hp
  obtain ⟨hp, hab, hαa, hαb⟩ := Finset.mem_filter.mp hp
  obtain ⟨ha, hb⟩ := mem_pairs.mp hp
  let a : ↥(labels (s n)) := ⟨p.1, ha⟩
  let b : ↥(labels (s n)) := ⟨p.2, hb⟩
  obtain ⟨hf, hr⟩ := hphys u hu a b hab hαa hαb
  obtain ⟨_, _, hi, hj, hA, hd, _⟩ := hcoeff u hu a b hab hαa hαb
  refine ⟨?_, hi, hj, hA, ?_⟩
  · unfold phaseError W
    rw [phase_eq_pairPhase]
    exact (add_le_add hf hr).trans (show ε / 2 + ε / 2 ≤ ε by linarith)
  · unfold defectError
    rw [phase_eq_pairPhase]
    exact hd

/-- Static limits for the gauge that also carries the full retargeting result. -/
theorem selected_uniform_static (hκ : 0 < κ) :
    UniformStatic (L := L) hκ (particleStage (L := L) hκ) (sectorGauge (L := L) hκ) := by
  obtain ⟨hs, hlim, _⟩ := select_family_explicit (L := L) hκ
  refine ⟨physicalSchedule_monotone hs, physicalSchedule_tendsto hlim, exterior_exact,
    fun R _ => supMax_tendsto _ _ _ (cartesian_bound (L := L) hκ R), ?_⟩
  intro R _ α hα
  refine ⟨supMax_tendsto _ _ _ ?_, supMax_tendsto _ _ _ ?_,
    supMax_tendsto _ _ _ ?_, supMax_tendsto _ _ _ ?_, supMax_tendsto _ _ _ ?_⟩ <;>
    intro ε hε <;> filter_upwards [phase_bounds (L := L) hκ R α ε hα hε] with n hn <;>
    intro u hu p hp
  · exact (hn u hu p hp).1
  · exact (hn u hu p hp).2.1
  · exact (hn u hu p hp).2.2.1
  · exact (hn u hu p hp).2.2.2.1
  · exact (hn u hu p hp).2.2.2.2

section Predecessor

open ActualModelTargetR53a Def033HierarchyR24m DynSeedClassicalR47b DynSeedInputR47b

/-- The conditional R-D51987CA and R-D2F4CE8F bindings share literal schedule
and gauge functions. The seed uses the exact inherited R-B2E70586 input. -/
theorem retarget_and_uniform_static_intermediate (hκ : 0 < κ) (F : HigherFlows L κ)
    (u : Smooth L) (hu : ‖Def033HierarchyR24m.physical u‖ = 1)
    (R : Finset ℕ) (lo hi : ℕ → ℝ) (a b : ℤ) (hab : a ≠ b)
    (flow_actions : ∀ t : TimeBox R lo hi,
      classicalOrbit hκ F u R t.val ∈ torus hκ (Def033HierarchyR24m.physical u))
    (mixed : MixedFinite hκ F u R)
    (PredecessorInput : DynftFullTorusInput hκ F u R) :
    DynSeedR47b.SeedStatement hκ F u R lo hi a b ∧
      RetargetFinalProofR48b.GaugeConclusion (L := L) hκ (sectorStage (L := L) hκ)
        (sectorGauge (L := L) hκ) ∧
      UniformStatic (L := L) hκ (particleStage (L := L) hκ) (sectorGauge (L := L) hκ) :=
  ⟨(retarget_with_seed_intermediate hκ F u hu R lo hi a b hab flow_actions mixed PredecessorInput).1,
    selected_gauge_conclusion hκ, selected_uniform_static hκ⟩

/-- The printed conclusion with explicit identities for both witnesses. -/
theorem uniform_static_intermediate (hκ : 0 < κ) (F : HigherFlows L κ)
    (u : Smooth L) (hu : ‖Def033HierarchyR24m.physical u‖ = 1)
    (R : Finset ℕ) (lo hi : ℕ → ℝ) (a b : ℤ) (hab : a ≠ b)
    (flow_actions : ∀ t : TimeBox R lo hi,
      classicalOrbit hκ F u R t.val ∈ torus hκ (Def033HierarchyR24m.physical u))
    (mixed : MixedFinite hκ F u R)
    (PredecessorInput : DynftFullTorusInput hκ F u R) :
    ∃ (j : ℕ → ℕ) (q : SectorGauge),
      j = particleStage (L := L) hκ ∧ q = sectorGauge (L := L) hκ ∧
      (∀ N, IsGreatest {k | particleThreshold (L := L) hκ k ≤ N} (j N)) ∧
      UniformStatic (L := L) hκ j q :=
  ⟨_, _, rfl, rfl, printed_selection hκ,
    (retarget_and_uniform_static_intermediate hκ F u hu R lo hi a b hab
      flow_actions mixed PredecessorInput).2.2⟩

end Predecessor

end QuantumNLS.UniformStaticR49b

#print axioms QuantumNLS.UniformStaticR49b.phase_value

#print axioms QuantumNLS.UniformStaticR49b.exterior_exact
#print axioms QuantumNLS.UniformStaticR49b.selected_particle_gauge

#print axioms QuantumNLS.UniformStaticR49b.selected_uniform_static

#print axioms QuantumNLS.UniformStaticR49b.retarget_and_uniform_static_intermediate
#print axioms QuantumNLS.UniformStaticR49b.uniform_static_intermediate

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "QuantumNLS.UniformStaticR49b." ||
        name.toString.startsWith "_private.QuantumNLS.UniformStaticR49b." then
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
  Lean.logInfo m!"R49b aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only."
