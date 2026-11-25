import LiebLiniger.FixedPeriod.Atomic.ALLS.TransCPrepK0

/-! # Trunk C PREPARATORY lemmas, package K6 (NOT approved, NOT admitted, NOT rooted)

Author: Claude Opus 5.5 (preparatory author P2, trunk C).  Not self-reviewed, not accepted.
Namespace `NlsGge.ALLS.TransCPrep`; every declaration carries the non-approved prefix `prep_`.
Decoupled C-PERSIST route: it uses only K0 (all-data action preservation), Track A
(`allS_actualBirkhoff_seq`, `allS_mem_iff`, `bridge_T`) and Track B (`continuous_l2Flow`);
it does NOT use the frequencies of C-MAIN.

TYPE COINCIDENCE NOTE: `prep_flow_persistence` has exactly the type of the pending (NOT yet
owner-approved) trunk C command C-PERSIST `allS_flow_persistence` in `STATEMENTS_TRUNK_C.md`
(same binders `s hs`, same existential and continuity conclusion).  Intended for later re-labelling.

Binders and conclusions (one line each):
* `prep_carrierCoe38_sub (s x y n)`: in the carrier `h^s`, coordinate `n` of `x - y` is `x_n - y_n`.
* `prep_mem_iff_of_norm_eq (s) {x y} (h)`: if `‖y_n‖ = ‖x_n‖` for every `n`, then `x ∈ h^s ↔ y ∈ h^s` (any real `s`).
* `prep_l2Flow_mem (s hs u t hu)`: for real `s ≥ 0`, `u ∈ L²` with `𝓕u ∈ h^s` and any time `t`, `𝓕(l2Flow t u) ∈ h^s`.
* `prep_l2Flow_mem_physInv (s hs)`: for real `s ≥ 0`, every `t`, every `x ∈ h⁰` with `x ∈ h^s`,
  `𝓕(l2Flow t (𝓕⁻¹ x)) ∈ h^s` (this is the `hS` witness of C-PERSIST).
* `prep_tendsto_weighted_of_coord_of_tsum (w hw f g hf hg hcoord hnorm)`: along any filter `F` on any type `α`,
  for nonnegative weights `w` and sequences `f a, g` with summable `w‖·‖²`, coordinatewise convergence
  `f a n → g n` (every `n`) plus convergence of `Σ w‖f a‖²` to `Σ w‖g‖²` give `Σ w‖f a - g‖² → 0`.
* `prep_carrier_tendsto_of_coord_of_norm (s X Y hcoord hnorm)`: along any filter, carrier elements `X a ∈ h^s`
  converging coordinatewise to `Y` with `‖X a‖ → ‖Y‖` converge to `Y` in `h^s`.
* `prep_physInv_eq_carrierToPhys (s h0 y hy)`: for `y ∈ h^s` (`0 ≤ s`), `𝓕⁻¹ y` equals the `h⁰ → L²`
  isometry applied to the inclusion of `y` into `h⁰`.
* `prep_flow_persistence (s) (hs : 0 ≤ s)`: there is a witness `hS` (for every `t`, every `x ∈ h⁰ ∩ h^s`,
  `𝓕(l2Flow t (𝓕⁻¹x)) ∈ h^s`) such that `(t, x) ↦ 𝓕(l2Flow t (𝓕⁻¹ x))` is jointly continuous
  `ℝ × h^s → h^s`.  `hS` is a proved property, not an assumption.

Route: membership from action invariance (K0) and `allS_mem_iff`.  Continuity: write the map as
`Tinv_s ∘ G` with `G(t, x) = Φ(l2Flow t (𝓕⁻¹x)) ∈ h^s`; `G` converges coordinatewise (continuity of
`l2Flow`, `Φ`, the `h^s ⊆ h⁰ ≅ L²` maps) and `‖G(t,x)‖_{h^s} = ‖T_s x‖_{h^s}` (action invariance), which is
continuous; hence `G` is continuous (weighted Radon–Riesz step); `Tinv_s` is continuous (analytic, Track A).
-/

set_option autoImplicit false
noncomputable section

open Filter Topology
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common NlsGge.GK38
open NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.PDE NlsGge.ThirdConsultation.Common
open LiebLiniger.FixedPeriod.ALLS.PdeB NlsGge.ALLS.TransA

namespace NlsGge.ALLS.TransCPrep

theorem prep_carrierCoe38_sub (s : ℝ) (x y : SobolevCarrier38 s) (n : ℤ) :
    carrierCoe38 s (x - y) n = carrierCoe38 s x n - carrierCoe38 s y n := rfl

theorem prep_mem_iff_of_norm_eq (s : ℝ) {x y : ℤ → ℂ} (h : ∀ n, ‖y n‖ = ‖x n‖) :
    x ∈ seqSobolev38 s ↔ y ∈ seqSobolev38 s := by
  rw [mem_seqSobolev38_iff, mem_seqSobolev38_iff]
  unfold SobolevSquareSummable
  simp only [h]

theorem prep_l2Flow_mem (s : ℝ) (hs : 0 ≤ s) (u : PhysicalL2) (t : ℝ)
    (hu : fourierSeq38 u ∈ seqSobolev38 s) : fourierSeq38 (l2Flow t u) ∈ seqSobolev38 s := by
  rw [allS_mem_iff s hs] at hu ⊢
  exact (prep_mem_iff_of_norm_eq s (fun n => prep_action_invariant u t n)).1 hu

theorem prep_l2Flow_mem_physInv (s : ℝ) (hs : 0 ≤ s) :
    ∀ (t : ℝ) (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 0), x ∈ seqSobolev38 s →
      fourierSeq38 (l2Flow t (physInv38 x hx)) ∈ seqSobolev38 s := by
  intro t x hx hxs
  exact prep_l2Flow_mem s hs _ t (by rw [fourierSeq38_physInv38]; exact hxs)

/-- Weighted Radon–Riesz step: coordinatewise convergence plus convergence of the weighted
square sums gives convergence of the weighted square sum of the differences. -/
theorem prep_tendsto_weighted_of_coord_of_tsum {α : Type*} {F : Filter α}
    (w : ℤ → ℝ) (hw : ∀ n, 0 ≤ w n) (f : α → ℤ → ℂ) (g : ℤ → ℂ)
    (hf : ∀ a, Summable fun n => w n * ‖f a n‖ ^ 2) (hg : Summable fun n => w n * ‖g n‖ ^ 2)
    (hcoord : ∀ n, Tendsto (fun a => f a n) F (𝓝 (g n)))
    (hnorm : Tendsto (fun a => ∑' n, w n * ‖f a n‖ ^ 2) F (𝓝 (∑' n, w n * ‖g n‖ ^ 2))) :
    Tendsto (fun a => ∑' n, w n * ‖f a n - g n‖ ^ 2) F (𝓝 0) := by
  have hpt : ∀ a n, w n * ‖f a n - g n‖ ^ 2 ≤
      2 * (w n * ‖f a n‖ ^ 2) + 2 * (w n * ‖g n‖ ^ 2) := by
    intro a n
    have h1 : ‖f a n - g n‖ ≤ ‖f a n‖ + ‖g n‖ := norm_sub_le _ _
    have h2 : ‖f a n - g n‖ ^ 2 ≤ 2 * ‖f a n‖ ^ 2 + 2 * ‖g n‖ ^ 2 := by
      nlinarith [norm_nonneg (f a n - g n), norm_nonneg (f a n), norm_nonneg (g n),
        sq_nonneg (‖f a n‖ - ‖g n‖)]
    have h3 := mul_le_mul_of_nonneg_left h2 (hw n)
    linarith
  have hDnn : ∀ a n, 0 ≤ w n * ‖f a n - g n‖ ^ 2 := fun a n => mul_nonneg (hw n) (sq_nonneg _)
  have hD : ∀ a, Summable fun n => w n * ‖f a n - g n‖ ^ 2 := fun a =>
    Summable.of_nonneg_of_le (hDnn a) (hpt a) (((hf a).mul_left 2).add (hg.mul_left 2))
  rw [Metric.tendsto_nhds]
  intro ε hε
  set δ := ε / 10 with hδdef
  have hδ : 0 < δ := by positivity
  -- a finite set `S` carrying all but `δ` of the limit mass
  have hgt : Tendsto (fun S : Finset ℤ => ∑ n ∈ S, w n * ‖g n‖ ^ 2) atTop
      (𝓝 (∑' n, w n * ‖g n‖ ^ 2)) := hg.hasSum
  obtain ⟨S, hS⟩ := (hgt.eventually (Metric.ball_mem_nhds _ hδ)).exists
  simp only [Real.dist_eq] at hS
  -- the three eventual estimates
  have hA := hnorm.eventually (Metric.ball_mem_nhds _ hδ)
  have hBt : Tendsto (fun a => ∑ n ∈ S, w n * ‖f a n‖ ^ 2) F
      (𝓝 (∑ n ∈ S, w n * ‖g n‖ ^ 2)) :=
    tendsto_finsetSum S fun n _ =>
      ((continuous_const.mul (continuous_norm.pow 2)).tendsto (g n)).comp (hcoord n)
  have hB := hBt.eventually (Metric.ball_mem_nhds _ hδ)
  have hCn : ∀ n, Tendsto (fun a => w n * ‖f a n - g n‖ ^ 2) F (𝓝 0) := by
    intro n
    have hc : Continuous fun x : ℂ => w n * ‖x - g n‖ ^ 2 :=
      continuous_const.mul ((continuous_id.sub continuous_const).norm.pow 2)
    have h := (hc.tendsto (g n)).comp (hcoord n)
    simpa [Function.comp_def] using h
  have hCt : Tendsto (fun a => ∑ n ∈ S, w n * ‖f a n - g n‖ ^ 2) F (𝓝 0) := by
    simpa using tendsto_finsetSum S fun n _ => hCn n
  have hC := hCt.eventually (Metric.ball_mem_nhds _ hδ)
  filter_upwards [hA, hB, hC] with a ha hb hc
  simp only [Real.dist_eq, sub_zero] at ha hb hc
  -- pointwise domination by a head term plus two tails
  have hite : ∀ (h : ℤ → ℝ), HasSum (fun n => if n ∈ S then h n else 0) (∑ n ∈ S, h n) := by
    intro h
    have e : HasSum (fun n => if n ∈ S then h n else 0)
        (∑ n ∈ S, (if n ∈ S then h n else 0)) :=
      hasSum_sum_of_ne_finset_zero (fun n hn => by simp [hn])
    have e2 : ∑ n ∈ S, (if n ∈ S then h n else 0) = ∑ n ∈ S, h n :=
      Finset.sum_congr rfl fun n hn => by simp [hn]
    rwa [e2] at e
  have hR : HasSum (fun n => (if n ∈ S then w n * ‖f a n - g n‖ ^ 2 else 0) +
      2 * (w n * ‖f a n‖ ^ 2 - (if n ∈ S then w n * ‖f a n‖ ^ 2 else 0)) +
      2 * (w n * ‖g n‖ ^ 2 - (if n ∈ S then w n * ‖g n‖ ^ 2 else 0)))
      ((∑ n ∈ S, w n * ‖f a n - g n‖ ^ 2) +
        2 * ((∑' n, w n * ‖f a n‖ ^ 2) - ∑ n ∈ S, w n * ‖f a n‖ ^ 2) +
        2 * ((∑' n, w n * ‖g n‖ ^ 2) - ∑ n ∈ S, w n * ‖g n‖ ^ 2)) :=
    ((hite _).add (((hf a).hasSum.sub (hite _)).mul_left 2)).add
      ((hg.hasSum.sub (hite _)).mul_left 2)
  have hle := hasSum_le (fun n => by
      by_cases hn : n ∈ S
      · simp only [hn, ite_true, sub_self, mul_zero, add_zero, le_refl]
      · simp only [hn, ite_false, sub_zero, zero_add]
        exact hpt a n) (hD a).hasSum hR
  have hnn : 0 ≤ ∑' n, w n * ‖f a n - g n‖ ^ 2 := tsum_nonneg (hDnn a)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  have hS' := (abs_lt.mp hS)
  have ha' := (abs_lt.mp ha)
  have hb' := (abs_lt.mp hb)
  have hc' := (abs_lt.mp hc)
  linarith [hS'.1, hS'.2, ha'.1, ha'.2, hb'.1, hb'.2, hc'.1, hc'.2]

/-- Carrier form of the weighted Radon–Riesz step. -/
theorem prep_carrier_tendsto_of_coord_of_norm {α : Type*} {F : Filter α} (s : ℝ)
    (X : α → SobolevCarrier38 s) (Y : SobolevCarrier38 s)
    (hcoord : ∀ n, Tendsto (fun a => carrierCoe38 s (X a) n) F (𝓝 (carrierCoe38 s Y n)))
    (hnorm : Tendsto (fun a => ‖X a‖) F (𝓝 ‖Y‖)) : Tendsto X F (𝓝 Y) := by
  have hw : ∀ n, 0 ≤ sobolevModeWeight s n := fun n => (sobolevModeWeight_pos s n).le
  have hsq : Tendsto (fun a => ∑' n, sobolevModeWeight s n * ‖carrierCoe38 s (X a) n‖ ^ 2) F
      (𝓝 (∑' n, sobolevModeWeight s n * ‖carrierCoe38 s Y n‖ ^ 2)) := by
    have e : ∀ Z : SobolevCarrier38 s,
        ∑' n, sobolevModeWeight s n * ‖carrierCoe38 s Z n‖ ^ 2 = ‖Z‖ ^ 2 :=
      fun Z => (carrier_hasSum_norm_sq38 s Z).tsum_eq
    simp only [e]
    exact hnorm.pow 2
  have h := prep_tendsto_weighted_of_coord_of_tsum (sobolevModeWeight s) hw
    (fun a => carrierCoe38 s (X a)) (carrierCoe38 s Y)
    (fun a => (carrier_hasSum_norm_sq38 s (X a)).summable)
    (carrier_hasSum_norm_sq38 s Y).summable hcoord hsq
  have e : ∀ a, ‖X a - Y‖ =
      Real.sqrt (∑' n, sobolevModeWeight s n * ‖carrierCoe38 s (X a) n - carrierCoe38 s Y n‖ ^ 2) := by
    intro a
    have h2 := (carrier_hasSum_norm_sq38 s (X a - Y)).tsum_eq
    simp only [prep_carrierCoe38_sub] at h2
    rw [h2, Real.sqrt_sq (norm_nonneg _)]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [e]
  have h3 := (Real.continuous_sqrt.tendsto 0).comp h
  rwa [Real.sqrt_zero] at h3

theorem prep_physInv_eq_carrierToPhys (s : ℝ) (h0 : ((0 : ℕ) : ℝ) ≤ s) (y : SobolevCarrier38 s)
    (hy : carrierCoe38 s y ∈ seqSobolev38 0) :
    physInv38 (carrierCoe38 s y) hy = carrierToPhys38 (carrierIncl38 h0 y) := by
  apply fourierSeq38_injective
  rw [fourierSeq38_physInv38]
  unfold carrierToPhys38
  rw [fourierSeq38_physInv38, carrierCoe38_incl38]

/-- Persistence and joint continuity on every `h^s` (type coincides with the pending C-PERSIST). -/
theorem prep_flow_persistence (s : ℝ) (hs : 0 ≤ s) :
    ∃ hS : (∀ (t : ℝ) (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 0), x ∈ seqSobolev38 s →
        fourierSeq38 (l2Flow t (physInv38 x hx)) ∈ seqSobolev38 s),
      Continuous fun p : ℝ × SobolevCarrier38 s =>
        carrierMk38 s (fourierSeq38 (l2Flow p.1 (physInv38 (carrierCoe38 s p.2)
          (seqSobolev38_mono hs (carrierCoe38_mem s p.2)))))
          (hS p.1 _ _ (carrierCoe38_mem s p.2)) := by
  refine ⟨prep_l2Flow_mem_physInv s hs, ?_⟩
  obtain ⟨hT, hTinv, hanT, hanTinv, -, -⟩ := allS_actualBirkhoff_seq s hs
  have hTc : Continuous (carrierMap38 s s actualBirkhoffTop38.T hT) :=
    continuousOn_univ.mp hanT.continuousOn
  have hTinvc : Continuous (carrierMap38 s s actualBirkhoffTop38.Tinv hTinv) :=
    continuousOn_univ.mp hanTinv.continuousOn
  obtain ⟨-, -, hA, -⟩ := actual_birkhoff_bindings
  have hΦ : Continuous physicalBirkhoff := continuousOn_univ.mp hA.continuousOn
  have h0 : ((0 : ℕ) : ℝ) ≤ s := by rw [Nat.cast_zero]; exact hs
  have hmemG : ∀ p : ℝ × SobolevCarrier38 s,
      (physicalBirkhoff (l2Flow p.1 (physInv38 (carrierCoe38 s p.2)
        (seqSobolev38_mono hs (carrierCoe38_mem s p.2)))) : ℤ → ℂ) ∈ seqSobolev38 s :=
    fun p => (allS_mem_iff s hs _).1 (prep_l2Flow_mem_physInv s hs p.1 _ _ (carrierCoe38_mem s p.2))
  let G : ℝ × SobolevCarrier38 s → SobolevCarrier38 s := fun p => carrierMk38 s _ (hmemG p)
  have hv : Continuous fun p : ℝ × SobolevCarrier38 s => l2Flow p.1 (physInv38 (carrierCoe38 s p.2)
      (seqSobolev38_mono hs (carrierCoe38_mem s p.2))) := by
    refine (continuous_l2Flow.comp (continuous_fst.prodMk (continuous_carrierToPhys38.comp
      ((carrierIncl38 h0).continuous.comp continuous_snd)))).congr fun p => ?_
    simp only [Function.comp_apply]
    rw [prep_physInv_eq_carrierToPhys s h0]
  have hGnorm : ∀ p, ‖G p‖ = ‖carrierMap38 s s actualBirkhoffTop38.T hT p.2‖ := by
    intro p
    have h1 := carrier_hasSum_norm_sq38 s (G p)
    have h2 := carrier_hasSum_norm_sq38 s (carrierMap38 s s actualBirkhoffTop38.T hT p.2)
    have e : ∀ n, sobolevModeWeight s n * ‖carrierCoe38 s (G p) n‖ ^ 2 =
        sobolevModeWeight s n *
          ‖carrierCoe38 s (carrierMap38 s s actualBirkhoffTop38.T hT p.2) n‖ ^ 2 := by
      intro n
      rw [carrierMap38_coe, bridge_T _ (seqSobolev38_mono hs (carrierCoe38_mem s p.2))]
      show sobolevModeWeight s n * ‖(physicalBirkhoff (l2Flow p.1 (physInv38 (carrierCoe38 s p.2)
        (seqSobolev38_mono hs (carrierCoe38_mem s p.2)))) : ℤ → ℂ) n‖ ^ 2 = _
      rw [prep_action_invariant]
    have h1' : HasSum (fun n => sobolevModeWeight s n *
        ‖carrierCoe38 s (carrierMap38 s s actualBirkhoffTop38.T hT p.2) n‖ ^ 2) (‖G p‖ ^ 2) := by
      convert h1 using 1
      funext n
      exact (e n).symm
    rw [← Real.sqrt_sq (norm_nonneg (G p)), h1'.unique h2, Real.sqrt_sq (norm_nonneg _)]
  have hGc : Continuous G := by
    rw [continuous_iff_continuousAt]
    intro p₀
    refine prep_carrier_tendsto_of_coord_of_norm s G (G p₀) (fun n => ?_) ?_
    · exact ((prep_continuous_coord n).comp (hΦ.comp hv)).tendsto p₀
    · rw [show (fun p => ‖G p‖) = fun p => ‖carrierMap38 s s actualBirkhoffTop38.T hT p.2‖ from
        funext hGnorm, hGnorm p₀]
      exact ((hTc.comp continuous_snd).norm).tendsto p₀
  refine (hTinvc.comp hGc).congr fun p => ?_
  apply carrierExt38
  rw [Function.comp_apply, carrierMap38_coe, carrierCoe38_mk, carrierCoe38_mk]
  show actualBirkhoffTop38.Tinv (physicalBirkhoff (l2Flow p.1 (physInv38 (carrierCoe38 s p.2)
      (seqSobolev38_mono hs (carrierCoe38_mem s p.2)))) : ℤ → ℂ) = _
  rw [physicalBirkhoff_coe_eq_T]
  exact actualBirkhoffTop38.left_inv _ (fourierSeq38_mem_zero _)

end NlsGge.ALLS.TransCPrep
