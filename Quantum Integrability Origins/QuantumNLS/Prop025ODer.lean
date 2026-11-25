import Mathlib
import QuantumNLS.Prop009FixedProjection
import QuantumNLS.Prop009Branch

/-! PROP-025 (thm:MP-mixed, mixed_propagation.tex sha256 24ab083b...), stage O3a:
the fixed-action derivative event `EI_der` of eq:MP-fixed-deviation (mixed_propagation.tex:196-218).

Source: "For each integer `j ≥ 1`, apply Lemma lem:B4-finite-probes to all selected contours and
choose a finite set of probes whose good event forces the required root-free neighborhoods and
transfer/derivative deviations below `1/j`. ... Choose increasing thresholds `N_j` ... and use the
`j`th collection when `N_j ≤ N < N_{j+1}`. ... The deviations can be required on slightly larger
contour neighborhoods, by the same finite-probe contradiction proof and Cauchy's formula."

* `deriv_dev_le` (Cauchy's formula): a deviation `≤ τ` on the closed disc of radius `r` bounds the
  derivative deviation at the centre by `τ/r`.
* `probes_nb`: the finite-probe contradiction proof (`Prop009ProbeDev.probes_generic`, uniform
  transfer convergence `Prop009ProbeDev.unif_sdev`) on the slightly larger compact neighbourhoods
  `nb(Γ_i, r)` of the fixed contours: one radius `r > 0` (chosen before the probes, from the
  accepted uniform label blocks and the support distance), and for every `τ > 0` finitely many
  probes forcing roots at a common positive distance from `nb(Γ_i, r)` and `|s_N − s| ≤ τ` there.
* `der_projection`: the diagonal schedule (as in the accepted `Prop009FixedProjection.fixed_projection`):
  events `E_N` with `P_{N,u}(E_Nᶜ) → 0` and `ρ_N → 0` such that, eventually, every label `m ∈ E_N`
  satisfies on every fixed contour `Γ_i`: roots at distance `> 2κ/N`, `|s_N − s| ≤ ρ_N` and
  `|s_N' − s'| ≤ ρ_N` (eq:MP-fixed-deviation, both terms).

Imports read-only: `Prop009FixedProjection` (accepted PROP-026 item (2) closure: probe events,
`event_compl_tendsto`, `diag_schedule`, `onShell_of_arr`), `Prop009Branch` (`nb`, `isCompact_nb`). -/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped InnerProductSpace ComplexConjugate

namespace QuantumNLS.Prop025ODer

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheLabels (MArr)
open QuantumNLS.EmpiricalRapidity (bornMeasure)
open QuantumNLS.BulkResponseActual (physBasis IsLimitingRapidityMeasure)
open QuantumNLS.Prop017Quantum (qAct)
open QuantumNLS.PeriodReconstructionCore
open QuantumNLS.PeriodReconstruction (Gam isCompact_Gam Gam_dist differentiableAt_cauchy)
open QuantumNLS.IndexedScalarMeasure QuantumNLS.IndexedScalarMeasureCuts
open QuantumNLS.LabelJointLimit QuantumNLS.LabelJointWeak QuantumNLS.LabelBlock
open QuantumNLS.Prop009Branch (nb isCompact_nb)
open QuantumNLS.Prop009ProbeBorn (probeEvent event_compl_tendsto diag_schedule)
open QuantumNLS.Prop009ProbeDev (probes_generic unif_sdev onShell_of_arr gam_supp_dist
  exists_pos_le_all Gam_im_le)

/-! ### 1. Cauchy's formula for the derivative deviation -/

/-- **Cauchy's formula**: `|f − g| ≤ τ` on the closed disc of radius `r` around `z`, both
holomorphic there, gives `|f'(z) − g'(z)| ≤ τ/r`. -/
theorem deriv_dev_le {f g : ℂ → ℂ} {z : ℂ} {r τ : ℝ} (hr : 0 < r)
    (hf : ∀ w ∈ closedBall z r, DifferentiableAt ℂ f w)
    (hg : ∀ w ∈ closedBall z r, DifferentiableAt ℂ g w)
    (hb : ∀ w ∈ closedBall z r, ‖f w - g w‖ ≤ τ) :
    ‖deriv f z - deriv g z‖ ≤ τ / r := by
  have hd : DiffContOnCl ℂ (fun w => f w - g w) (ball z r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z hr.ne']
    intro w hw
    exact ((hf w hw).sub (hg w hw)).differentiableWithinAt
  have hz : z ∈ closedBall z r := mem_closedBall_self hr.le
  have hder : deriv (fun w => f w - g w) z = deriv f z - deriv g z :=
    deriv_sub (hf z hz) (hg z hz)
  rw [← hder]
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hd
    (fun w hw => hb w (sphere_subset_closedBall hw))

/-- The background transfer `s = A + e/A` is holomorphic wherever `G` is. -/
theorem differentiableAt_sf {L κ : ℝ} {G : ℂ → ℂ} {z : ℂ} (hG : DifferentiableAt ℂ G z) :
    DifferentiableAt ℂ (sf L κ G) z := by
  have hA : DifferentiableAt ℂ (Af κ G) z := by
    unfold Af
    exact ((differentiableAt_const _).mul hG).cexp
  have he : DifferentiableAt ℂ (ef L) z := by
    unfold ef
    exact ((differentiableAt_const _).mul differentiableAt_id).cexp
  have hA0 : Af κ G z ≠ 0 := Complex.exp_ne_zero _
  exact hA.add (he.div hA hA0)

/-! ### 2. Finite probes on slightly larger contour neighbourhoods -/

/-- **lem:B4-finite-probes on `nb(Γ_i, r)`.** -/
theorem probes_nb {L κ : ℝ} (S : IndexedScalarMeasureCuts L κ) {r : ℕ} {n : Fin r → ℤ}
    {xm xp h : Fin r → ℝ}
    (hxm : ∀ i, xm i ∈ S.cuts) (hxp : ∀ i, xp i ∈ S.cuts) (hlt : ∀ i, xm i < xp i) (hh : ∀ i, 0 < h i)
    (h1 : ∀ i, 2 * Real.pi * (n i - 1) < exteriorForce L κ S.μ (xm i))
    (h2 : ∀ i, exteriorForce L κ S.μ (xm i) < 2 * Real.pi * n i)
    (h3 : ∀ i, 2 * Real.pi * n i < exteriorForce L κ S.μ (xp i))
    (h4 : ∀ i, exteriorForce L κ S.μ (xp i) < 2 * Real.pi * (n i + 1)) :
    ∃ rr > 0, (∀ i, ∀ w ∈ nb (Gam (xm i) (xp i) (h i)) rr, ∀ t ∈ S.μ.support, rr ≤ ‖w - t‖) ∧
      ∀ τ > 0, ∃ m : ℕ, ∃ z : Fin m → ℂ, (∀ j, RootMeasureComplex.HighHalf L κ (z j)) ∧
        ∃ ε > 0, ∃ N₀ : ℕ, ∃ t : ℕ,
        ∀ (N : ℕ) (_ : 0 < N), N₀ ≤ N → ∀ B : OnShellBethe L κ N,
          (∀ j, ‖sNf L (κ / N) B.q (z j) - sf L κ (EmpiricalRapidity.cauchyTransform S.μ) (z j)‖ < ε) →
          ∀ i, (∀ w ∈ nb (Gam (xm i) (xp i) (h i)) rr, ∀ j, 1 / ((t : ℝ) + 1) ≤ ‖w - ((B.q j : ℝ) : ℂ)‖) ∧
            ∀ w ∈ nb (Gam (xm i) (xp i) (h i)) rr,
              ‖sNf L (κ / N) B.q w - sf L κ (EmpiricalRapidity.cauchyTransform S.μ) w‖ ≤ τ := by
  have hL := S.hL
  have hκ := S.hκ
  have : IsProbabilityMeasure S.μ := S.isProb
  set μ0 : ProbabilityMeasure ℝ := ⟨S.μ, S.isProb⟩ with hμ0
  -- uniform label blocks and support distances fix the radius before the probes
  have hblock : ∀ i, ∃ δ > 0, ∃ U ∈ 𝓝 μ0, ∃ N₀ : ℕ,
      ∀ (N : ℕ) (hN : 0 < N), N₀ ≤ N → ∀ B : OnShellBethe L κ N, rootP B hN ∈ U →
        BlockConclusion B (n i) (xm i) (xp i) δ := fun i =>
    label_block_uniform S rfl (hxm i) (hxp i) (hlt i) (h1 i) (h2 i) (h3 i) (h4 i)
  choose δ hδ U hU NB hNB using hblock
  have hsd : ∀ i, ∃ d0 > 0, ∀ z ∈ Gam (xm i) (xp i) (h i), ∀ t ∈ S.μ.support, d0 ≤ ‖z - t‖ :=
    fun i => gam_supp_dist S (hxm i) (hxp i) (hh i)
  choose d0 hd0 hd0s using hsd
  obtain ⟨rr, hrr, hrrD⟩ := exists_pos_le_all (fun i => min (min (δ i) (h i)) (d0 i) / 2)
    (fun i => by have := lt_min (lt_min (hδ i) (hh i)) (hd0 i); positivity)
  have hrr_le : ∀ i, 2 * rr ≤ min (δ i) (h i) ∧ 2 * rr ≤ d0 i := fun i => by
    have := hrrD i
    have a1 := min_le_left (min (δ i) (h i)) (d0 i)
    have a2 := min_le_right (min (δ i) (h i)) (d0 i)
    constructor <;> linarith
  -- support distance on the neighbourhoods
  have hsupp : ∀ i, ∀ w ∈ nb (Gam (xm i) (xp i) (h i)) rr, ∀ t ∈ S.μ.support, rr ≤ ‖w - t‖ := by
    intro i w hw t ht
    obtain ⟨w0, hw0, hww0⟩ := hw
    have a := hd0s i w0 hw0 t ht
    have b := norm_sub_norm_le (w0 - (t : ℂ)) (w0 - w)
    have e : w0 - (t : ℂ) - (w0 - w) = w - t := by ring
    rw [e, norm_sub_rev w0 w] at b
    linarith [(hrr_le i).2]
  refine ⟨rr, hrr, hsupp, fun τ hτ => ?_⟩
  let P : ℕ → ∀ N : ℕ, OnShellBethe L κ N → Prop := fun t N B =>
    ∀ i, (∀ w ∈ nb (Gam (xm i) (xp i) (h i)) rr, ∀ j, 1 / ((t : ℝ) + 1) ≤ ‖w - ((B.q j : ℝ) : ℂ)‖) ∧
      ∀ w ∈ nb (Gam (xm i) (xp i) (h i)) rr,
        ‖sNf L (κ / N) B.q w - sf L κ (EmpiricalRapidity.cauchyTransform S.μ) w‖ ≤ τ
  have hmono : ∀ t t' N (B : OnShellBethe L κ N), t ≤ t' → P t N B → P t' N B := by
    intro t t' N B htt hP i
    refine ⟨fun w hw j => ?_, (hP i).2⟩
    refine le_trans ?_ ((hP i).1 w hw j)
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ htt)
  have hseq : ∀ (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (B : ∀ k, OnShellBethe L κ (N k)),
      Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 (⟨S.μ, S.isProb⟩ : ProbabilityMeasure ℝ)) →
      Tendsto N atTop atTop → ∃ t, ∀ᶠ k in atTop, P t (N k) (B k) := by
    intro N hN B hconv hNtop
    change Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ0) at hconv
    -- roots at distance `≥ rr` from every neighbourhood, eventually
    have hroot : ∀ i, ∀ᶠ k in atTop, ∀ w ∈ nb (Gam (xm i) (xp i) (h i)) rr, ∀ j,
        rr ≤ ‖w - (((B k).q j : ℝ) : ℂ)‖ := by
      intro i
      filter_upwards [hconv.eventually (hU i), hNtop.eventually (eventually_ge_atTop (NB i))] with k hk1 hk2
      have hbl := hNB i (N k) (hN k) hk2 (B k) hk1
      intro w hw j
      obtain ⟨w0, hw0, hww0⟩ := hw
      have a := Gam_dist (hh i) (hbl j).2.1 (hbl j).2.2 hw0
      have b := norm_sub_norm_le (w0 - (((B k).q j : ℝ) : ℂ)) (w0 - w)
      have e : w0 - (((B k).q j : ℝ) : ℂ) - (w0 - w) = w - (((B k).q j : ℝ) : ℂ) := by ring
      rw [e, norm_sub_rev w0 w] at b
      linarith [(hrr_le i).1]
    have hdev : ∀ i, ∀ᶠ k in atTop, ∀ w ∈ nb (Gam (xm i) (xp i) (h i)) rr,
        ‖sNf L (κ / N k) (B k).q w - sf L κ (EmpiricalRapidity.cauchyTransform S.μ) w‖ < τ := fun i =>
      unif_sdev (μ := μ0) hL hκ hconv hNtop (isCompact_nb (isCompact_Gam _ _ _) rr) hrr
        (h := h i + rr)
        (fun w hw => by
          obtain ⟨w0, hw0, hww0⟩ := hw
          have a := Gam_im_le (hh i).le hw0
          have b : |w.im - w0.im| ≤ ‖w - w0‖ := by
            rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
          have c := abs_sub_abs_le_abs_sub w.im w0.im
          linarith)
        (hsupp i) ((hroot i).mono fun k hk w hw j => hk w hw j) hτ
    refine ⟨⌈1 / rr⌉₊, ?_⟩
    have hdt : 1 / (((⌈1 / rr⌉₊ : ℕ) : ℝ) + 1) ≤ rr := by
      rw [div_le_iff₀ (by positivity)]
      have h5 : 1 / rr ≤ (⌈1 / rr⌉₊ : ℝ) := Nat.le_ceil _
      rw [div_le_iff₀ hrr] at h5
      nlinarith
    filter_upwards [eventually_all.2 hroot, eventually_all.2 hdev] with k hk1 hk2 i
    exact ⟨fun w hw j => hdt.trans (hk1 i w hw j), fun w hw => (hk2 i w hw).le⟩
  obtain ⟨m, z, hz, ε, hε, N₀, t, ht⟩ := probes_generic S P hmono hseq
  exact ⟨m, z, hz, ε, hε, N₀, t, fun N hN hN0 B hB i => ht N hN hN0 B hB i⟩

/-! ### 3. The diagonal schedule: the event `EI_der` -/

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-- **eq:MP-fixed-mass / eq:MP-fixed-deviation, derivative form.** -/
theorem der_projection (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) (S : IndexedScalarMeasureCuts L κ)
    (hS : (μ : Measure ℝ) = S.μ) {r : ℕ} {n : Fin r → ℤ} {xm xp h : Fin r → ℝ}
    (hxm : ∀ i, xm i ∈ S.cuts) (hxp : ∀ i, xp i ∈ S.cuts) (hlt : ∀ i, xm i < xp i) (hh : ∀ i, 0 < h i)
    (h1 : ∀ i, 2 * Real.pi * (n i - 1) < exteriorForce L κ S.μ (xm i))
    (h2 : ∀ i, exteriorForce L κ S.μ (xm i) < 2 * Real.pi * n i)
    (h3 : ∀ i, 2 * Real.pi * n i < exteriorForce L κ S.μ (xp i))
    (h4 : ∀ i, exteriorForce L κ S.μ (xp i) < 2 * Real.pi * (n i + 1)) :
    ∃ (E : ∀ N : ℕ, Set (MArr N)) (ρ : ℕ → ℝ), (∀ N, 0 ≤ ρ N) ∧ Tendsto ρ atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => (bornMeasure (physBasis L hκ N) u hu).real (E N)ᶜ) atTop (𝓝 0) ∧
      ∀ᶠ N : ℕ in atTop, ∀ m ∈ E N, ∀ i, ∀ w ∈ Gam (xm i) (xp i) (h i),
        (∀ j, 2 * |κ / (N : ℝ)| < ‖w - ((qAct L κ N m j : ℝ) : ℂ)‖) ∧
        ‖sNf L (κ / N) (qAct L κ N m) w - sf L κ (EmpiricalRapidity.cauchyTransform S.μ) w‖ ≤ ρ N ∧
        ‖deriv (sNf L (κ / N) (qAct L κ N m)) w -
          deriv (sf L κ (EmpiricalRapidity.cauchyTransform S.μ)) w‖ ≤ ρ N := by
  have hL : 0 < L := Fact.out
  have : IsProbabilityMeasure S.μ := S.isProb
  set G := EmpiricalRapidity.cauchyTransform S.μ with hG
  obtain ⟨rr, hrr, hsupp, hpr⟩ := probes_nb S hxm hxp hlt hh h1 h2 h3 h4
  choose m z hz ε hε N0 t H using fun j : ℕ => hpr (1 / ((j : ℝ) + 1)) (by positivity)
  -- thresholds: probes active and `2κ/N` below the root distance
  let N1 : ℕ → ℕ := fun j => max (N0 j) (⌈2 * κ * ((t j : ℝ) + 1)⌉₊ + 1)
  have hEc : ∀ j : ℕ, Tendsto (fun N : ℕ => (bornMeasure (physBasis L hκ N) u hu).real
      (probeEvent (L := L) (κ := κ) S.μ (z j) (ε j) N)ᶜ) atTop (𝓝 0) := by
    intro j
    have := event_compl_tendsto hκ u hu hμ (hz j) (hε j)
    rwa [hS] at this
  have hev : ∀ j : ℕ, ∀ᶠ N : ℕ in atTop, N1 j ≤ N ∧
      (bornMeasure (physBasis L hκ N) u hu).real
        (probeEvent (L := L) (κ := κ) S.μ (z j) (ε j) N)ᶜ ≤ 1 / ((j : ℝ) + 1) := by
    intro j
    refine (eventually_ge_atTop (N1 j)).and ?_
    exact (hEc j).eventually (Iic_mem_nhds (by positivity))
  obtain ⟨J, hJ, hPJ⟩ := diag_schedule _ hev
  set E : ∀ N : ℕ, Set (MArr N) := fun N => probeEvent (L := L) (κ := κ) S.μ (z (J N)) (ε (J N)) N
    with hE
  set ρ : ℕ → ℝ := fun N => (1 + 1 / rr) * (1 / ((J N : ℝ) + 1)) with hρ
  have hρ0 : ∀ N, 0 ≤ ρ N := fun N => by positivity
  have hρlim : Tendsto ρ atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat.comp hJ).const_mul (1 + 1 / rr)
    simpa [hρ] using this
  have hmass : Tendsto (fun N : ℕ => (bornMeasure (physBasis L hκ N) u hu).real (E N)ᶜ) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun N => measureReal_nonneg) ?_
      (tendsto_one_div_add_atTop_nhds_zero_nat.comp hJ)
    filter_upwards [hPJ] with N hN using hN.2
  refine ⟨E, ρ, hρ0, hρlim, hmass, ?_⟩
  filter_upwards [hPJ, eventually_ge_atTop 1] with N hN hN1
  intro a ha i w hw
  obtain ⟨hN0, -⟩ := hN
  have hNpos : 0 < N := hN1
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hNpos
  obtain ⟨B, hB⟩ := onShell_of_arr hL hκ hNpos a
  have hprobe : ∀ j, ‖sNf L (κ / N) B.q (z (J N) j) - sf L κ G (z (J N) j)‖ < ε (J N) := by
    intro j; rw [hB]; exact ha j
  have hN0' : N0 (J N) ≤ N := (le_max_left _ _).trans hN0
  obtain ⟨hroot, hdevb⟩ := H (J N) N hNpos hN0' B hprobe i
  rw [hB] at hroot hdevb
  set T : ℝ := (t (J N) : ℝ) + 1 with hT
  have hT0 : 0 < T := by positivity
  -- `2κ/N < 1/T`
  have hsmall : 2 * |κ / (N : ℝ)| < 1 / T := by
    have hc' : ⌈2 * κ * T⌉₊ + 1 ≤ N := (le_max_right _ _).trans hN0
    have hc : (⌈2 * κ * T⌉₊ : ℝ) + 1 ≤ N := by exact_mod_cast hc'
    have hc2 : 2 * κ * T ≤ ⌈2 * κ * T⌉₊ := Nat.le_ceil _
    rw [abs_of_pos (div_pos hκ hNr), lt_div_iff₀ hT0]
    have : 2 * (κ / N) * T = 2 * κ * T / N := by ring
    rw [this, div_lt_one hNr]
    linarith
  have hw_nb : ∀ v ∈ closedBall w rr, v ∈ nb (Gam (xm i) (xp i) (h i)) rr := fun v hv =>
    ⟨w, hw, by rw [mem_closedBall, dist_eq_norm] at hv; exact hv⟩
  have hwn : w ∈ nb (Gam (xm i) (xp i) (h i)) rr := ⟨w, hw, by simp [hrr.le]⟩
  have hroots : ∀ v ∈ nb (Gam (xm i) (xp i) (h i)) rr, ∀ j,
      2 * |κ / (N : ℝ)| < ‖v - ((qAct L κ N a j : ℝ) : ℂ)‖ := fun v hv j =>
    lt_of_lt_of_le hsmall (hroot v hv j)
  have hdev' : ∀ v ∈ nb (Gam (xm i) (xp i) (h i)) rr,
      ‖sNf L (κ / N) (qAct L κ N a) v - sf L κ G v‖ ≤ 1 / ((J N : ℝ) + 1) := fun v hv => hdevb v hv
  have hdiffN : ∀ v ∈ closedBall w rr, DifferentiableAt ℂ (sNf L (κ / N) (qAct L κ N a)) v :=
    fun v hv => (hasDerivAt_sN L (hroots v (hw_nb v hv))).differentiableAt
  have hdiffs : ∀ v ∈ closedBall w rr, DifferentiableAt ℂ (sf L κ G) v :=
    fun v hv => differentiableAt_sf (differentiableAt_cauchy S.μ hrr (hsupp i v (hw_nb v hv)))
  have hcau := deriv_dev_le hrr hdiffN hdiffs (fun v hv => hdev' v (hw_nb v hv))
  have hx0 : 0 ≤ 1 / ((J N : ℝ) + 1) := by positivity
  have hx1 : 0 ≤ 1 / ((J N : ℝ) + 1) / rr := by positivity
  have hρe : ρ N = 1 / ((J N : ℝ) + 1) + 1 / ((J N : ℝ) + 1) / rr := by rw [hρ]; ring
  refine ⟨fun j => hroots w hwn j, ?_, ?_⟩
  · linarith [hdev' w hwn]
  · linarith

end QuantumNLS.Prop025ODer

#print axioms QuantumNLS.Prop025ODer.deriv_dev_le
#print axioms QuantumNLS.Prop025ODer.probes_nb
#print axioms QuantumNLS.Prop025ODer.der_projection

-- Recursive type/value audit of every own declaration: standard axioms only, and no held
-- identifier (HeldGP14Tonelli, the superseded pre-D1 `RegularCut`) in the transitive closure.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop025ODer." then
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
  Lean.logInfo m!"Prop025ODer aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only, no held identifiers."
