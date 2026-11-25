import Mathlib
import QuantumNLS.Prop010SingleContourR17
import QuantumNLS.Prop009FixedProjection

/-! PROP-025 (thm:MP-mixed, mixed_propagation.tex sha256 24ab083b...), stage O3c:
the count part of eq:MP-reconstruction on the fixed action contours, at the eigenvalue level.

Source (mixed_propagation.tex:196-218, 327-345): "For each `n ∈ I`, fix a contour `Γ_n` enclosing the
physical gap with label `n`, with its two real intersections in the neighboring open bands.  Collapsed
gaps are permitted.  The count reconstruction in Theorem thm:B3-period-reconstruction uses these same
contours. ... the count reconstruction in Theorem thm:B3-period-reconstruction give[s], uniformly on
the stated boxes, [eq:MP-reconstruction] ... These inequalities are obtained by summing the
corresponding uniform eigenvalue inequalities ... On a fixed action contour the weight is exactly one,
so these derivative terms vanish."

Contours: the accepted PROP-010 rectangles `Γ_n = ∂([b_{n-1}, b_n] × [-h, h])` at the physical
separators `b_j = RootScalarPeriodR8.cut hκ u j` (in the open bands, brackets `2π(n-1) < F(b_{n-1}) <
2πn < F(b_n) < 2π(n+1)`, as in the frozen R52CFCount; D1 route recorded SETTLED: the probe set and
two-term scalar reconstruction come from the accepted `cutoff_probes` on the concrete band carrier
`Prop026Bound.scalarCuts`, and no cut-set notion enters any statement).

* **`count_event`**: for finitely many labels `n_i` and bounded Lipschitz extensions `f_i, g_i` with the
  printed tube agreement (`localLog`, `localCorrection`, the hypotheses of PROP-010's scalar lemma), there
  are events `E_N` (intersection of the finitely many PROP-010 probe events) with `P_{N,u}(E_Nᶜ) → 0` and ONE
  constant `C` such that eventually, for every label `m ∈ E_N` and every `i`, the actual count
  eigenvalue `m_{n_i}` (`M_{N,n}Ψ_m = m_nΨ_m`) satisfies
  `|m_{n_i} − N c^{(0)}_i(m) − c^{(1)}_i(m)| ≤ C/N`, with `c^{(0)}_i(m) = −(2πκ)⁻¹ Re ∮_{Γ_i} f_i(z, s_N(z))dz`
  and `c^{(1)}_i(m) = Re (i/2π) ∮_{Γ_i} g_i(z, s_N(z), s_N'(z)) dz` (the PROP-010 eigenvalues `c0`, `c1`).
  This is the two-term period of thm:B3-period-reconstruction multiplied by `N`.

Imports read-only: `Prop010SingleContourR17` (accepted PROP-010 closure: `cutoff_probes`,
`scalar_cutoff_error`, `configuration*`, `c0`, `c1`), `Prop009FixedProjection` (accepted: probe events,
`event_compl_tendsto`). -/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section

open Set Filter Topology Complex MeasureTheory
open scoped InnerProductSpace BigOperators

namespace QuantumNLS.Prop025OCount

open QuantumNLS.Prop010ContourBindingR11
open IndexedScalarMeasure IndexedScalarMeasureCuts
open PhysicalTensor (L2T)
open BetheLabels (MArr)
open EmpiricalRapidity (bornMeasure)
open BulkResponseActual (physBasis IsLimitingRapidityMeasure)
open Prop017Quantum (qAct)
open PeriodReconstructionCore PeriodReconstruction PeriodTwoTerm
open LabelJointLimit LabelJointWeak LabelBlock
open Prop009ProbeBorn (probeEvent event_compl_tendsto)

variable (L : ℝ) [Fact (0<L)] {κ : ℝ}

/-- The physical separators lie in the open bands, with the PROP-006 force brackets. -/
theorem separator_brackets (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (n : ℤ) :
    RootScalarPeriodR8.cut hκ u (n-1) ∈ (Prop026Bound.scalarCuts hκ u hu).cuts ∧
    RootScalarPeriodR8.cut hκ u n ∈ (Prop026Bound.scalarCuts hκ u hu).cuts ∧
    RootScalarPeriodR8.cut hκ u (n-1) < RootScalarPeriodR8.cut hκ u n ∧
    2*Real.pi*(n-1) < exteriorForce L κ (Prop026Bound.scalarCuts hκ u hu).μ (RootScalarPeriodR8.cut hκ u (n-1)) ∧
    exteriorForce L κ (Prop026Bound.scalarCuts hκ u hu).μ (RootScalarPeriodR8.cut hκ u (n-1)) < 2*Real.pi*n ∧
    2*Real.pi*n < exteriorForce L κ (Prop026Bound.scalarCuts hκ u hu).μ (RootScalarPeriodR8.cut hκ u n) ∧
    exteriorForce L κ (Prop026Bound.scalarCuts hκ u hu).μ (RootScalarPeriodR8.cut hκ u n) < 2*Real.pi*(n+1) := by
  let S := Prop026Bound.scalarCuts hκ u hu
  have hne : u≠0 := by intro he; rw [he,norm_zero] at hu; norm_num at hu
  have hcut (k : ℤ) : RootScalarPeriodR8.cut hκ u k ∈ S.cuts :=
    (DEF014Phase.facts ((⟨κ,hκ⟩,u):DEF014Phase.Param L)).separator_in_band k
  have hforce (k : ℤ) : exteriorForce L κ S.μ (RootScalarPeriodR8.cut hκ u k)=
      2*((k:ℝ)+1/2)*Real.pi := by
    change exteriorForce L κ (Prop026Bound.M hκ u) _ = _
    rw [Prop026Bound.force_eq hκ hne (hcut k)]
    have hp := (PhysicalSourceFinal.sourceFacts hκ u).phase.separator_spec k
    change Prop026Bound.theta hκ u (RootScalarPeriodR8.cut hκ u k)=((k:ℝ)+1/2)*Real.pi at hp
    rw [hp]
    ring
  have hab : RootScalarPeriodR8.cut hκ u (n-1) < RootScalarPeriodR8.cut hκ u n :=
    (DEF014Phase.facts ((⟨κ,hκ⟩,u):DEF014Phase.Param L)).phase.separator_strictMono (by omega)
  refine ⟨hcut _, hcut _, hab, ?_, ?_, ?_, ?_⟩
  · rw [hforce]; push_cast; nlinarith [Real.pi_pos]
  · rw [hforce]; push_cast; nlinarith [Real.pi_pos]
  · rw [hforce]; nlinarith [Real.pi_pos]
  · rw [hforce]; nlinarith [Real.pi_pos]

/-- **Count reconstruction on the fixed action contours, eigenvalue level.** -/
theorem count_event (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {r : ℕ} (n : Fin r → ℤ) {h rr : ℝ} (hh : 0 < h)
    (hrr : 0 < rr) (f : Fin r → Extension (ℂ × ℂ)) (g : Fin r → Extension (ℂ × (ℂ × ℂ)))
    (hf : ∀ i, ∀ z ∈ Gam (RootScalarPeriodR8.cut hκ u (n i - 1)) (RootScalarPeriodR8.cut hκ u (n i)) h,
      ∀ w, ‖w - sf L κ (EmpiricalRapidity.cauchyTransform (PhysicalQuantumMeasure.measure hκ u)) z‖ < rr →
      (f i).value (z, w) = localLog L κ (EmpiricalRapidity.cauchyTransform (PhysicalQuantumMeasure.measure hκ u)) z w)
    (hg : ∀ i, ∀ z ∈ Gam (RootScalarPeriodR8.cut hκ u (n i - 1)) (RootScalarPeriodR8.cut hκ u (n i)) h,
      ∀ w v, ‖w - sf L κ (EmpiricalRapidity.cauchyTransform (PhysicalQuantumMeasure.measure hκ u)) z‖ < rr →
      ‖v‖ ≤ MixedQuadratures.Rbd L κ (h + 1) →
      (g i).value (z, (w, v)) =
        localCorrection L κ (EmpiricalRapidity.cauchyTransform (PhysicalQuantumMeasure.measure hκ u)) z w v) :
    ∃ (E : ∀ N : ℕ, Set (MArr N)) (C : ℝ), 0 ≤ C ∧
      Tendsto (fun N : ℕ => (bornMeasure (physBasis L hκ N) u hu).real (E N)ᶜ) atTop (𝓝 0) ∧
      ∀ᶠ N : ℕ in atTop, ∀ (hN : 0 < N), ∀ m ∈ E N, ∀ i,
        |((m.1 (n i) : ℕ) : ℝ) - (N : ℝ) * c0 L hκ hN (f i) (RootScalarPeriodR8.cut hκ u (n i - 1))
            (RootScalarPeriodR8.cut hκ u (n i)) h m -
          c1 L hκ hN (g i) (RootScalarPeriodR8.cut hκ u (n i - 1)) (RootScalarPeriodR8.cut hκ u (n i)) h m| ≤
          C / N := by
  have hL : 0 < L := Fact.out
  let S := Prop026Bound.scalarCuts hκ u hu
  have hS : (μ : Measure ℝ) = S.μ := (Prop026Bound.physical_eq_limit hκ u hu hμ).symm
  set G := EmpiricalRapidity.cauchyTransform (PhysicalQuantumMeasure.measure hκ u) with hG
  have hprobe_i : ∀ i, ∃ m : ℕ, ∃ z : Fin m → ℂ, (∀ j, RootMeasureComplex.HighHalf L κ (z j)) ∧
      ∃ ε > 0, ∃ N₀ : ℕ, ∃ C ≥ 0, ∀ (N : ℕ) (_hN : 0 < N), N₀ ≤ N → ∀ B : OnShellBethe L κ N,
        (∀ j, ‖sNf L (κ/N) B.q (z j) - sf L κ (EmpiricalRapidity.cauchyTransform S.μ) (z j)‖ < ε) →
        (∀ w ∈ Gam (RootScalarPeriodR8.cut hκ u (n i - 1)) (RootScalarPeriodR8.cut hκ u (n i)) h,
          LocalGood L κ (EmpiricalRapidity.cauchyTransform S.μ) rr B w) ∧
        ‖twoTermErr L κ (EmpiricalRapidity.cauchyTransform S.μ) B (n i)
          (RootScalarPeriodR8.cut hκ u (n i - 1)) (RootScalarPeriodR8.cut hκ u (n i)) h‖ ≤ C * ((N : ℝ)⁻¹) ^ 2 := by
    intro i
    obtain ⟨ha, hb, hab, h1, h2, h3, h4⟩ := separator_brackets L hκ u hu (n i)
    exact cutoff_probes S ha hb hab hh hrr h1 h2 h3 h4
  choose mm z hz ε hε N0 Cs hCs hpr using hprobe_i
  -- the event: all finitely many probe sets
  let E : ∀ N : ℕ, Set (MArr N) := fun N => ⋂ i, probeEvent (L := L) (κ := κ) S.μ (z i) (ε i) N
  have hEc : ∀ N, (bornMeasure (physBasis L hκ N) u hu).real (E N)ᶜ ≤
      ∑ i, (bornMeasure (physBasis L hκ N) u hu).real (probeEvent (L := L) (κ := κ) S.μ (z i) (ε i) N)ᶜ := by
    intro N
    have e : (E N)ᶜ = ⋃ i, (probeEvent (L := L) (κ := κ) S.μ (z i) (ε i) N)ᶜ := by
      simp only [E, Set.compl_iInter]
    rw [e]
    exact measureReal_iUnion_fintype_le _
  have hsum : Tendsto (fun N : ℕ => ∑ i, (bornMeasure (physBasis L hκ N) u hu).real
      (probeEvent (L := L) (κ := κ) S.μ (z i) (ε i) N)ᶜ) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset (Fin r)) (fun i _ => by
      have h' := event_compl_tendsto hκ u hu hμ (hz i) (hε i)
      rw [hS] at h'
      exact h')
    simpa using this
  have hmass : Tendsto (fun N : ℕ => (bornMeasure (physBasis L hκ N) u hu).real (E N)ᶜ) atTop (𝓝 0) :=
    squeeze_zero (fun N => measureReal_nonneg) hEc hsum
  let C : ℝ := ∑ i, Cs i
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun i _ => hCs i
  refine ⟨E, C, hC0, hmass, ?_⟩
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ i, N0 i ≤ N₀ :=
    ⟨∑ i, N0 i, fun i => Finset.single_le_sum (fun j _ => Nat.zero_le (N0 j)) (Finset.mem_univ i)⟩
  filter_upwards [eventually_ge_atTop N₀] with N hNN hN m hm i
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  set a := RootScalarPeriodR8.cut hκ u (n i - 1) with ha
  set b := RootScalarPeriodR8.cut hκ u (n i) with hb
  have hab : a < b := (separator_brackets L hκ u hu (n i)).2.2.1
  let Bc := configuration L hκ hN m
  have hq : Bc.q = qAct L κ N m := configuration_q L hκ hN m
  have hprobe : ∀ j, ‖sNf L (κ/N) Bc.q (z i j) - sf L κ (EmpiricalRapidity.cauchyTransform S.μ) (z i j)‖ < ε i := by
    intro j
    rw [hq]
    exact (Set.mem_iInter.1 hm i) j
  obtain ⟨hl, herr⟩ := hpr i N hN ((hN₀ i).trans hNN) Bc hprobe
  have hroot (w : ℂ) (hw : w ∈ Gam a b h) : ∀ k, w ≠ (Bc.q k : ℂ) := by
    intro k he
    have hn := (hl w hw).2.2.2.1 k
    rw [he, sub_self, norm_zero] at hn
    linarith [abs_nonneg (κ/(N:ℝ))]
  have hv' : ∀ w ∈ Gam a b h, ‖deriv (sNf L (κ/N) Bc.q) w‖ ≤ MixedQuadratures.Rbd L κ (h+1) := by
    intro w hw
    rw [← dev_configuration L hκ hN m w (hroot w hw)]
    exact derivative_cutoff_bound L hκ hN m w (Gam_abs_im hh hw)
  have hs := scalar_cutoff_error G Bc (n i) hab.le hh.le (f i) (g i) (hf i) (hg i) hl hv'
  have hef := LabelExactPeriod.rectIntegral_congr
    (f := fun w => (f i).value (w, sNf L (κ/N) Bc.q w)) (g := fun w => (f i).value (w, ev L hκ hN w m))
    (fun w hw => by rw [ev_configuration L hκ hN m _ (hroot _ (bot_mem hab.le hw))])
    (fun w hw => by rw [ev_configuration L hκ hN m _ (hroot _ (top_mem hab.le hw))])
    (fun w hw => by rw [ev_configuration L hκ hN m _ (hroot _ (right_mem hh.le hw))])
    (fun w hw => by rw [ev_configuration L hκ hN m _ (hroot _ (left_mem hh.le hw))])
  have heg := LabelExactPeriod.rectIntegral_congr
    (f := fun w => (g i).value (w, (sNf L (κ/N) Bc.q w, deriv (sNf L (κ/N) Bc.q) w)))
    (g := fun w => (g i).value (w, (ev L hκ hN w m, dev L hκ hN w m)))
    (fun w hw => by rw [ev_configuration L hκ hN m _ (hroot _ (bot_mem hab.le hw)),
      dev_configuration L hκ hN m _ (hroot _ (bot_mem hab.le hw))])
    (fun w hw => by rw [ev_configuration L hκ hN m _ (hroot _ (top_mem hab.le hw)),
      dev_configuration L hκ hN m _ (hroot _ (top_mem hab.le hw))])
    (fun w hw => by rw [ev_configuration L hκ hN m _ (hroot _ (right_mem hh.le hw)),
      dev_configuration L hκ hN m _ (hroot _ (right_mem hh.le hw))])
    (fun w hw => by rw [ev_configuration L hκ hN m _ (hroot _ (left_mem hh.le hw)),
      dev_configuration L hκ hN m _ (hroot _ (left_mem hh.le hw))])
  rw [hef, heg, configuration_count] at hs
  have hs' : |((m.1 (n i) : ℕ) : ℝ) / N - (c0 L hκ hN (f i) a b h m + (N : ℝ)⁻¹ * c1 L hκ hN (g i) a b h m)| ≤
      Cs i * ((N : ℝ)⁻¹) ^ 2 := hs.trans herr
  have hCi : Cs i ≤ C := Finset.single_le_sum (fun j _ => hCs j) (Finset.mem_univ i)
  have e : ((m.1 (n i) : ℕ) : ℝ) - (N : ℝ) * c0 L hκ hN (f i) a b h m - c1 L hκ hN (g i) a b h m =
      (N : ℝ) * (((m.1 (n i) : ℕ) : ℝ) / N - (c0 L hκ hN (f i) a b h m + (N : ℝ)⁻¹ * c1 L hκ hN (g i) a b h m)) := by
    field_simp
    ring
  rw [e, abs_mul, abs_of_pos hNr]
  calc (N : ℝ) * |((m.1 (n i) : ℕ) : ℝ) / N - (c0 L hκ hN (f i) a b h m + (N : ℝ)⁻¹ * c1 L hκ hN (g i) a b h m)|
      ≤ (N : ℝ) * (Cs i * ((N : ℝ)⁻¹) ^ 2) := mul_le_mul_of_nonneg_left hs' hNr.le
    _ = Cs i / N := by field_simp
    _ ≤ C / N := div_le_div_of_nonneg_right hCi hNr.le

end QuantumNLS.Prop025OCount

#print axioms QuantumNLS.Prop025OCount.separator_brackets
#print axioms QuantumNLS.Prop025OCount.count_event

-- Recursive type/value audit of every own declaration: standard axioms only, and no held
-- identifier (HeldGP14Tonelli, the superseded pre-D1 `RegularCut`) in the transitive closure.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop025OCount." then
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
  Lean.logInfo m!"Prop025OCount aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only, no held identifiers."
