import QuantumNLS.AuditGapsS01Level
import QuantumNLS.ReconstructionInputsR33m

/-!
# AuditGapsS01Core: R-10EE6421 `lem:audit-gaps` from the named input `RD8362E5EBInput`

PRINTED SOURCE: `source-text/chapters/core/weighted_actions_and_same_gauge_dynamics.tex`, lines 261-294
(`\begin{lemma}[Actual adjacent differences from these dynamic symbols]`, `\ReportID{R-10EE6421}`,
`\label{lem:audit-gaps}`; the proof is lines 270-294).

PRINTED STATEMENT: "For each fixed positive-action donor-receiver pair and every fixed charge order, the
rebuilt-gauge dynamical symbols imply the master's receiver-minus-donor adjacent-difference convergence in
probability under the original product law. Finite families converge jointly. No moment convergence follows
from this argument."

NAMED INPUT (the only dynamical hypothesis): `ReconstructionR33m.RD8362E5EBInput hκ F g`, the frozen
formalization (`ReconstructionInputsR33m`, round 33) of the EXACT printed statement of R-8362E5EB
`prop:audit-dynamic-gauge` (same file, lines 155-164, UNACCEPTED, being authored by sol_multi r34 and NOT
duplicated here): for the supplied rebuilt gauge `g`, fixed smooth unit profile, fixed finite charge family,
fixed compact time box and norm-close preparations, the strong Cartesian symbols (diagonals and collapsed
actions included) and the positive-action phase symbols hold, both orientations, uniformly on the box.

SCOPE PREDECESSORS: R-09DDF6D2 is accepted. R-09DDF6D2 `lem:multiplier` is NOT used here: the printed proof
of R-10EE6421 uses "the exact diagonal multiplier" (an identity), which is here the frozen
`DiagonalMultiplier.key_identity`/`norm_T_sq` (the accepted module's lemmas for the exact multiplier), not the
conclusion of `lem:multiplier`. DEF-033 enters ONLY through its reviewed definitions
(`Def033CoreR24m.target`, `ActiveFrequency`, `phase`, `originalBorn`, `withMissing`, `DifferenceLimit`,
`Def033AdjacentR24m.limit_change_missing`); the active-frequency datum `ω` of DEF-033 enters as the
hypothesis `ActiveFrequency ... (ω a)` (the printed clause "`w_n(Φ_t^{(r)}u) = e^{-itω_{r,n}(u)} w_n(u)` when
`a_n(u) > 0`" of DEF-033, discharged by `Bind7BDEF033H02.DEF033Package.active` in `AuditGapsS01Headline`).

THE PRINTED PROOF, step by step:
1. "Fix one charge and write `δ = ν_b - ν_a`. Its Cartesian and phase targets evolve by `e^{itδ}`":
   `phase_symbol`, `hp` below: the phase symbol at joint time `t_r = s` is `rot(sδ)` times the static one.
2. "The dynamic and static phase residuals and unitarity imply
   `‖(U*W U - e^{itδ} W) u^{⊗N}‖ → 0` uniformly on each compact time interval", here `[-1, 1]`:
   `AuditGapsS01Level.level_gap_mass` (via `eps_apply_bound`).
3. "The exact diagonal multiplier makes its square `E[1_{m_a ≥ 1} |e^{it(Λ(m-e_a+e_b)-Λ(m)-δ)} - 1|²]`":
   `AuditGapsS01Analytic.norm_eps_sq`, `norm_sq_shift_defect`.
4. "The omitted donor boundary has probability tending to zero by action concentration": `hmissing`
   (from the Cartesian symbol at `a = b`, `AuditGapsS01Level.level_conc`).
5. "Integrating for `-1 ≤ t ≤ 1` gives the nonnegative function `k(x) = 4(1 - sin x / x)` ... `inf_{|x| ≥ ε}
   k > 0`. The integrated expectation tends to zero, which proves the probability claim":
   `AuditGapsS01Analytic.kk_eq`, `kk_lower`, `avg_bound`, `bad_mass`; `hbad` below.
6. "The union bound proves every fixed finite joint claim": `AuditGapsS01Headline.audit_gaps_joint`.
7. "No moment convergence follows": nothing is claimed beyond convergence in probability.

No acceptance claim.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
noncomputable section
open Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace ENNReal Classical

namespace QuantumNLS.AuditGapsS01Core
open QuantumNLS.BetheLabels QuantumNLS.BetheCoefficientTransform QuantumNLS.BetheOccupationGauge
open QuantumNLS.BetheSpectralCharges QuantumNLS.HierarchyFlow
open QuantumNLS.TerraMultiRound12Definitions QuantumNLS.Def033CoreR24m
open QuantumNLS.Occupation (DonorOK)
open QuantumNLS.ActualModelTargetR53a (HigherFlows hamFlows)
open QuantumNLS.Def033HierarchyR24m (Smooth physical)
open QuantumNLS.AuditGapsS01Level (tv)

variable {L κ : ℝ} [Fact (0 < L)]

/-! ### Elementary lemmas -/

theorem tendsto_zero_of_real {f : ℕ → ℝ≥0∞}
    (h : ∀ e : ℝ, 0 < e → ∀ᶠ N in atTop, f N ≤ ENNReal.ofReal e) : Tendsto f atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hne
  · exact Eventually.of_forall fun _ => le_top
  · have hpos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hne
    filter_upwards [h _ hpos] with N hN
    rwa [ENNReal.ofReal_toReal hne] at hN

theorem norm_phase' (t ω : ℝ) : ‖Def033CoreR24m.phase t ω‖ = 1 := by
  have : -((t * ω : ℝ) : ℂ) * Complex.I = (((-(t * ω)) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [Def033CoreR24m.phase, this, Complex.norm_exp_ofReal_mul_I]

theorem phase_mul_conj (s ωa ωb : ℝ) (wa wb : ℂ) :
    (Def033CoreR24m.phase s ωa * wa) * conj (Def033CoreR24m.phase s ωb * wb) =
      DiagonalMultiplier.rot (s * (ωb - ωa)) * (wa * conj wb) := by
  have hc : conj (Def033CoreR24m.phase s ωb) = Complex.exp (((s * ωb : ℝ) : ℂ) * Complex.I) := by
    rw [Def033CoreR24m.phase, ← Complex.exp_conj]
    congr 1
    simp [map_mul]
  have he : Def033CoreR24m.phase s ωa * Complex.exp (((s * ωb : ℝ) : ℂ) * Complex.I) =
      DiagonalMultiplier.rot (s * (ωb - ωa)) := by
    rw [Def033CoreR24m.phase, DiagonalMultiplier.rot, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [map_mul, hc]
  calc _ = (Def033CoreR24m.phase s ωa * Complex.exp (((s * ωb : ℝ) : ℂ) * Complex.I)) *
        (wa * conj wb) := by ring
    _ = _ := by rw [he]

theorem phase_symbol (s ωa ωb : ℝ) (wa wb : ℂ) :
    ((Def033CoreR24m.phase s ωa * wa) * conj (Def033CoreR24m.phase s ωb * wb)) /
        (Real.sqrt (‖Def033CoreR24m.phase s ωa * wa‖ ^ 2 *
          ‖Def033CoreR24m.phase s ωb * wb‖ ^ 2) : ℂ) =
      DiagonalMultiplier.rot (s * (ωb - ωa)) *
        ((wa * conj wb) / (Real.sqrt (‖wa‖ ^ 2 * ‖wb‖ ^ 2) : ℂ)) := by
  rw [phase_mul_conj, norm_mul, norm_mul, norm_phase', norm_phase', one_mul, one_mul, mul_div_assoc]

/-! ### Level residuals as functions of the particle number -/

/-- Dynamic residual at joint time `t_r = s`, particle number `M`. -/
def GapDyn (hκ : 0 < κ) (g : Gauge) (u : QuantumNLS.PhysicalTensor.L2T L) (r : ℕ) (a c : ℤ)
    (τ : ℂ) (δ s : ℝ) (M : ℕ) (hM : 1 ≤ M) : ℝ :=
  ‖UnitPhaseTransfer.physical
      (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L M hM hκ) g a c
      (quantumFlow (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L M hM hκ) κ {r}
        (tv r s) (productVec L M u)) -
    (DiagonalMultiplier.rot (s * δ) * τ) •
      quantumFlow (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L M hM hκ) κ {r}
        (tv r s) (productVec L M u)‖

/-- Static residual, particle number `M`. -/
def GapStat (hκ : 0 < κ) (g : Gauge) (u : QuantumNLS.PhysicalTensor.L2T L) (a c : ℤ) (τ : ℂ)
    (M : ℕ) (hM : 1 ≤ M) : ℝ :=
  ‖UnitPhaseTransfer.physical
      (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L M hM hκ) g a c
      (productVec L M u) - τ • productVec L M u‖

/-- Cartesian residual at `a = b`, particle number `M`. -/
def ConcRes (hκ : 0 < κ) (g : Gauge) (u : QuantumNLS.PhysicalTensor.L2T L) (a : ℤ) (c₀ : ℂ)
    (M : ℕ) (hM : 1 ≤ M) : ℝ :=
  ‖CartesianOccupationTransfer.physical
      (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L M hM hκ) g a a
      (productVec L M u) - c₀ • productVec L M u‖

theorem GapDyn_congr (hκ : 0 < κ) (g : Gauge) (u : QuantumNLS.PhysicalTensor.L2T L) (r : ℕ)
    (a c : ℤ) (τ : ℂ) (δ s : ℝ) {M M' : ℕ} (h : M = M') (hM : 1 ≤ M) (hM' : 1 ≤ M') :
    GapDyn hκ g u r a c τ δ s M hM = GapDyn hκ g u r a c τ δ s M' hM' := by
  subst h; rfl

theorem GapStat_congr (hκ : 0 < κ) (g : Gauge) (u : QuantumNLS.PhysicalTensor.L2T L) (a c : ℤ)
    (τ : ℂ) {M M' : ℕ} (h : M = M') (hM : 1 ≤ M) (hM' : 1 ≤ M') :
    GapStat hκ g u a c τ M hM = GapStat hκ g u a c τ M' hM' := by
  subst h; rfl

theorem ConcRes_congr (hκ : 0 < κ) (g : Gauge) (u : QuantumNLS.PhysicalTensor.L2T L) (a : ℤ)
    (c₀ : ℂ) {M M' : ℕ} (h : M = M') (hM : 1 ≤ M) (hM' : 1 ≤ M') :
    ConcRes hκ g u a c₀ M hM = ConcRes hκ g u a c₀ M' hM' := by
  subst h; rfl

/-- The physical product preparation of the printed statement is the bosonic product of `physical u`. -/
theorem product_eq (u : Smooth L) (n : ℕ) :
    ReconstructionR33m.product u n = productVec L (1 + n) (physical u) := by
  rfl

theorem norm_product (u : Smooth L) (hu : ‖physical u‖ = 1) (n : ℕ) :
    ‖ReconstructionR33m.product u n‖ = 1 := by
  rw [product_eq, norm_productVec, hu, one_pow]

theorem hprep (u : Smooth L) (hu : ‖physical u‖ = 1) :
    ReconstructionR33m.Preparation u (fun n => ReconstructionR33m.product u n) :=
  ⟨norm_product u hu, by simp only [sub_self, norm_zero]; exact tendsto_const_nhds⟩

theorem hbox (r : ℕ) (s : ℝ) (hs : s ∈ Set.Icc (-1 : ℝ) 1) :
    tv r s ∈ ReconstructionR33m.TimeBox ({r} : Finset ℕ) (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)) := by
  simp only [ReconstructionR33m.TimeBox, Set.mem_setOf_eq]
  intro i
  have hir : (i : ℕ) = r := Finset.mem_singleton.1 i.2
  rw [hir]
  simpa [tv] using hs

/-! ### The core theorem -/

/-- **R-10EE6421 `lem:audit-gaps`, core form.** Given the named input `RD8362E5EBInput hκ F g`
(the exact printed statement of R-8362E5EB, for the rebuilt gauge `g`) and a real active frequency `ω` for
the chart coordinates `a`, `b` along the order-`r` flow (DEF-033: `w_n(Φ_t^{(r)} u) = e^{-itω_n} w_n(u)`
with a nonzero coordinate, which is the positive-action condition), the receiver-minus-donor adjacent
difference converges in probability to `ω_b - ω_a` under the ORIGINAL physical product Born law, with an
arbitrary missing-donor convention. -/
theorem audit_gaps_core (hκ : 0 < κ) (F : HigherFlows L κ) (g : Gauge)
    (hD : ReconstructionR33m.RD8362E5EBInput hκ F g)
    (u : Smooth L) (hu : ‖physical u‖ = 1) (r : ℕ) (a b : ℤ) (ω : ℤ → ℝ)
    (hωa : ActiveFrequency (fun s : ℝ => (ReconstructionR33m.w hκ F u {r} (tv r s)) a)
      (((Def021ChartR41b.chart L κ hκ).Φ (physical u)) a) (ω a))
    (hωb : ActiveFrequency (fun s : ℝ => (ReconstructionR33m.w hκ F u {r} (tv r s)) b)
      (((Def021ChartR41b.chart L κ hκ).Φ (physical u)) b) (ω b))
    (missing : ∀ N, MArr (N + 1) → ℝ) :
    DifferenceLimit hκ (physical u) hu r a b ω missing := by
  have hbox' := hbox
  -- the Cartesian symbol at (a, a): action concentration
  obtain ⟨hEa, -⟩ := hD u hu {r} (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ))
    (fun n => ReconstructionR33m.product u n) (hprep u hu) a a
  set z0a : ℂ := (ReconstructionR33m.w hκ F u {r} (tv r 0)) a with hz0a
  set c₀ : ℂ := z0a * conj z0a with hc₀
  have hz0a_eq : z0a = ((Def021ChartR41b.chart L κ hκ).Φ (physical u)) a := by
    have := hωa.2 0
    simpa [Def033CoreR24m.phase] using this
  have hc₀ne : c₀ ≠ 0 := by
    have : z0a ≠ 0 := by rw [hz0a_eq]; exact hωa.1
    simp [hc₀, this]
  have hc₀pos : 0 < ‖c₀‖ := norm_pos_iff.2 hc₀ne
  have hmissing : Tendsto (fun N => originalBorn hκ (physical u) hu N
      {m | ¬ DonorOK a (marrArr (N + 1) m).1}) atTop (𝓝 0) := by
    apply tendsto_zero_of_real
    intro e he
    have hε₁ : 0 < ‖c₀‖ * Real.sqrt e := by positivity
    filter_upwards [hEa _ hε₁] with N hN
    have h1 := (hN (tv r 0) (hbox' r 0 (by norm_num))).1
    have h2 : ConcRes hκ g (physical u) a c₀ (1 + N) (by omega) ≤ ‖c₀‖ * Real.sqrt e := by
      have h3 : ‖CartesianOccupationTransfer.physical
          (ReconstructionR33m.basis (L := L) hκ N) g a a (ReconstructionR33m.product u N) -
          c₀ • ReconstructionR33m.product u N‖ ≤ ‖c₀‖ * Real.sqrt e := by
        have h4 : ‖CartesianOccupationTransfer.physical
            (ReconstructionR33m.basis (L := L) hκ N) g a a
            (quantumFlow (ReconstructionR33m.basis (L := L) hκ N) κ {r} (tv r 0)
              (ReconstructionR33m.product u N)) -
            c₀ • quantumFlow (ReconstructionR33m.basis (L := L) hκ N) κ {r} (tv r 0)
              (ReconstructionR33m.product u N)‖ ≤ ‖c₀‖ * Real.sqrt e := h1
        rwa [AuditGapsS01Level.flow_zero _ g κ r] at h4
      rw [ConcRes, ← product_eq]
      exact h3
    have h5 : ConcRes hκ g (physical u) a c₀ (N + 1) (by omega) ≤ ‖c₀‖ * Real.sqrt e := by
      rw [← ConcRes_congr hκ g (physical u) a c₀ (Nat.add_comm 1 N) (by omega) (by omega)]
      exact h2
    calc originalBorn hκ (physical u) hu N {m | ¬ DonorOK a (marrArr (N + 1) m).1}
        ≤ ENNReal.ofReal ((‖c₀‖ * Real.sqrt e) ^ 2 / ‖c₀‖ ^ 2) :=
          AuditGapsS01Level.born_conc_le g N a (physical u) hu c₀ hc₀ne _ h5
      _ = ENNReal.ofReal e := by
          congr 1
          have hne : ‖c₀‖ ≠ 0 := hc₀pos.ne'
          rw [mul_pow, Real.sq_sqrt he.le]
          field_simp
  intro ε hε
  by_cases hab : a = b
  · -- coinciding endpoints: the difference vanishes on occupied donors
    subst hab
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmissing
      (fun _ => bot_le) (fun N => measure_mono ?_)
    intro m hm
    by_contra hd
    have hd' : DonorOK a (marrArr (N + 1) m).1 := by
      by_contra hn
      exact hd hn
    have hz : withMissing L κ (N + 1) r a a (missing N) m = 0 := by
      rw [withMissing_occupied L κ (N + 1) r a a (missing N) m hd']
      exact Def033AdjacentR24m.difference_self L κ (N + 1) r a m hd'
    have : ε < |withMissing L κ (N + 1) r a a (missing N) m - target ω a a| := hm
    rw [hz, target_self] at this
    simp at this
    linarith
  · -- distinct positive-action endpoints
    set δ : ℝ := ω b - ω a with hδ
    set w0a : ℂ := ((Def021ChartR41b.chart L κ hκ).Φ (physical u)) a with hw0a
    set w0b : ℂ := ((Def021ChartR41b.chart L κ hκ).Φ (physical u)) b with hw0b
    set q : ℂ := (w0a * conj w0b) / (Real.sqrt (‖w0a‖ ^ 2 * ‖w0b‖ ^ 2) : ℂ) with hq
    have hp : ∀ s : ℝ, ((ReconstructionR33m.w hκ F u {r} (tv r s)) a *
        conj ((ReconstructionR33m.w hκ F u {r} (tv r s)) b)) /
        (Real.sqrt (‖(ReconstructionR33m.w hκ F u {r} (tv r s)) a‖ ^ 2 *
          ‖(ReconstructionR33m.w hκ F u {r} (tv r s)) b‖ ^ 2) : ℂ) =
        DiagonalMultiplier.rot (s * δ) * q := by
      intro s
      have e1 : (ReconstructionR33m.w hκ F u {r} (tv r s)) a =
          Def033CoreR24m.phase s (ω a) * w0a := hωa.2 s
      have e2 : (ReconstructionR33m.w hκ F u {r} (tv r s)) b =
          Def033CoreR24m.phase s (ω b) * w0b := hωb.2 s
      rw [e1, e2]
      exact phase_symbol s (ω a) (ω b) w0a w0b
    have hpa : 0 < ‖((Def021ChartR41b.chart L κ hκ).Φ (physical u)) a‖ ^ 2 :=
      pow_pos (norm_pos_iff.2 hωa.1) 2
    have hpb : 0 < ‖((Def021ChartR41b.chart L κ hκ).Φ (physical u)) b‖ ^ 2 :=
      pow_pos (norm_pos_iff.2 hωb.1) 2
    obtain ⟨-, hWsym⟩ := hD u hu {r} (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ))
      (fun n => ReconstructionR33m.product u n) (hprep u hu) a b
    have hWs := hWsym hab hpa hpb
    -- residuals at the level N + 1
    have hres : ∀ ε₀ : ℝ, 0 < ε₀ → ∀ᶠ N in atTop,
        (∀ s ∈ Set.Icc (-1 : ℝ) 1, GapDyn hκ g (physical u) r a b q δ s (N + 1) (by omega) ≤ ε₀) ∧
          GapStat hκ g (physical u) a b q (N + 1) (by omega) ≤ ε₀ := by
      intro ε₀ hε₀
      filter_upwards [hWs ε₀ hε₀] with N hN
      have hdyn1 : ∀ s ∈ Set.Icc (-1 : ℝ) 1,
          GapDyn hκ g (physical u) r a b q δ s (1 + N) (by omega) ≤ ε₀ := by
        intro s hs
        have h1 := (hN (tv r s) (hbox' r s hs)).1
        rw [hp s] at h1
        rw [GapDyn, ← product_eq]
        exact h1
      have hstat1 : GapStat hκ g (physical u) a b q (1 + N) (by omega) ≤ ε₀ := by
        have h1 := (hN (tv r 0) (hbox' r 0 (by norm_num))).1
        rw [hp 0] at h1
        have h2 : ‖UnitPhaseTransfer.physical (ReconstructionR33m.basis (L := L) hκ N) g a b
            (quantumFlow (ReconstructionR33m.basis (L := L) hκ N) κ {r} (tv r 0)
              (ReconstructionR33m.product u N)) -
            (DiagonalMultiplier.rot (0 * δ) * q) •
              quantumFlow (ReconstructionR33m.basis (L := L) hκ N) κ {r} (tv r 0)
                (ReconstructionR33m.product u N)‖ ≤ ε₀ := h1
        rw [AuditGapsS01Level.flow_zero _ g κ r] at h2
        have h3 : DiagonalMultiplier.rot (0 * δ) = 1 := by simp [DiagonalMultiplier.rot]
        rw [h3, one_mul] at h2
        rw [GapStat, ← product_eq]
        exact h2
      refine ⟨fun s hs => ?_, ?_⟩
      · rw [← GapDyn_congr hκ g (physical u) r a b q δ s (Nat.add_comm 1 N) (by omega) (by omega)]
        exact hdyn1 s hs
      · rw [← GapStat_congr hκ g (physical u) a b q (Nat.add_comm 1 N) (by omega) (by omega)]
        exact hstat1
    -- the bad set
    have hbad : ∀ η : ℝ, 0 < η → Tendsto (fun N => originalBorn hκ (physical u) hu N
        {m | ∃ h : DonorOK a (marrArr (N + 1) m).1,
          η ≤ |adjacentDifference L κ (N + 1) r a b m h - δ|}) atTop (𝓝 0) := by
      intro η hη
      obtain ⟨k₀, hk₀, hk⟩ := AuditGapsS01Analytic.kk_lower η hη
      apply tendsto_zero_of_real
      intro e he
      have hpos : 0 < e * k₀ / 8 := by positivity
      set ε₀ : ℝ := Real.sqrt (e * k₀ / 8) with hε₀def
      have hε₀ : 0 < ε₀ := Real.sqrt_pos.2 hpos
      have h8 : 8 * ε₀ ^ 2 / k₀ = e := by
        rw [hε₀def, Real.sq_sqrt hpos.le]
        field_simp
      filter_upwards [hres ε₀ hε₀] with N hN
      calc _ ≤ ENNReal.ofReal (8 * ε₀ ^ 2 / k₀) :=
            AuditGapsS01Level.born_gap_le g N r a b (physical u) hu q δ ε₀ η k₀ hk₀ hk hN.1 hN.2
        _ = ENNReal.ofReal e := by rw [h8]
    refine Def033AdjacentR24m.limit_change_missing hκ (physical u) hu r a b ω missing
      (fun _ _ => target ω a b) ?_ hmissing ε hε
    intro ε' hε'
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hbad ε' hε')
      (fun _ => bot_le) (fun N => measure_mono ?_)
    intro m hm
    by_cases hd : DonorOK a (marrArr (N + 1) m).1
    · refine ⟨hd, ?_⟩
      have hm' : ε' < |withMissing L κ (N + 1) r a b (fun _ => target ω a b) m - target ω a b| := hm
      rw [withMissing_occupied L κ (N + 1) r a b _ m hd] at hm'
      exact le_of_lt hm'
    · exfalso
      have hm' : ε' < |withMissing L κ (N + 1) r a b (fun _ => target ω a b) m - target ω a b| := hm
      rw [withMissing_empty L κ (N + 1) r a b _ m hd] at hm'
      simp at hm'
      linarith

end QuantumNLS.AuditGapsS01Core

#print axioms QuantumNLS.AuditGapsS01Core.phase_symbol
#print axioms QuantumNLS.AuditGapsS01Core.audit_gaps_core
