import Mathlib
import QuantumNLS.L2Flow
import QuantumNLS.RA634Main
import QuantumNLS.D05TotalVariation

/-!
# R-AEE17FD6 `thm:root-L2-flow` (ROOT_L2_extension.tex:74-100, proof :101-161)

"For `κ ≥ 0` and every `f ∈ L²(𝕋_L)` there is a unique global Duhamel solution of
`i∂ₜu = −∂ₓ²u + 2κ|u|²u`, `u(0) = f`, in `C(ℝ;L²) ∩ L⁴_loc(ℝ × 𝕋_L)`. The flow preserves the `L²`
norm, agrees with the `H¹` flow of Theorem F04:thm-global, and depends Lipschitz continuously on the
initial datum on each bounded `L²` ball over each fixed finite time interval, in both `C_tL²_x` and
`L⁴_{t,x}`. Each time map is a homeomorphism with inverse the map at the negative time.
For `κ > 0`, the full quantum-derived spectral measure, discriminant, and every indexed mass are
constant along this flow. If `f_j → f` in `L²`, their spectral measures and indexed mass sequences
converge along the corresponding solutions, uniformly on each compact time interval, respectively
in total variation and in `ℓ¹`."

First paragraph: the reviewed EXT-003 Route Y flow `L2Flow.thm_root_L2_flow` (DEF-023 realization),
restated verbatim. Second paragraph (new): conservation through the smooth approximations
`H1Bridge.trunc f N` (Fourier truncation, `emb (trunc f N) → f` in `L²`), whose flows are the `H¹`
flows (`flowMap_H1`) and conserve the data by F04:cor-spectral (`RA634Main.F04_cor_spectral`); the
`L²` Lipschitz dependence gives convergence at each time, and the continuity of the discriminant in
`L²` (R-0C33082D) passes the equality to the limit; the measure and masses are functions of the
discriminant (R-7E0532E7 density formula, R-950BFB30 separators; `RootNlsInvariance.data_eq_of_disc`).
The uniform convergence then follows from conservation and the total-variation continuity of D05
(R-0C33082D) and the `ℓ¹` continuity of the masses (R-950BFB30) at time zero.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal
open QuantumNLS.Fourier QuantumNLS.L4Strichartz QuantumNLS.L4StrichartzL2 QuantumNLS.DuhamelDuality
  QuantumNLS.LocalL4Contraction QuantumNLS.L4Gluing QuantumNLS.L2Flow QuantumNLS.H1Bridge
  QuantumNLS.Sobolev QuantumNLS.F04Regularity QuantumNLS.RootEnergyVariation

namespace QuantumNLS.RAEEMain
open QuantumNLS.PhysicalTensor (L2T)

variable {L : ℝ} [Fact (0 < L)]

/-- The `H¹ → L²` embedding of the flow is the physical `L²` vector of R-63A99F0E. -/
lemma emb_eq (a : h04 L 1) : emb a = physical (m10 a) :=
  Lp.ext ((emb_coeFn a).trans (physical_rep a).symm)

lemma continuous_disc (κ : ℝ) (z : ℂ) :
    Continuous (fun v : L2T L => L2SpatialTransfer.discriminant κ v z) := by
  have hc := DiscParamContinuity.continuous_discriminant_param (L := L) z
  have hp : Continuous (fun v : L2T L => ((κ, v) : ℝ × L2T L)) :=
    (continuous_const (y := κ)).prodMk continuous_id
  exact hc.comp (f := fun v : L2T L => ((κ, v) : ℝ × L2T L)) hp

/-- `L²` convergence of data gives uniform convergence of the flows on `[-T,T]`. -/
theorem flow_unif {κ : ℝ} (hκ : 0 ≤ κ) {fs : ℕ → HL L} {f : HL L}
    (h : Tendsto fs atTop (𝓝 f)) (T : ℝ) :
    ∀ ε > 0, ∀ᶠ j in atTop, ∀ t ∈ Icc (-T) T,
      ‖flowMap hκ (fs j) t - flowMap hκ f t‖ < ε := by
  intro ε hε
  set R : ℝ := ‖f‖ + 1 with hR
  obtain ⟨K, hK0, hK⟩ := flow_lipschitz (L := L) hκ R (max T 0) (by positivity) (le_max_right _ _)
  have hδ : 0 < min 1 (ε / (K + 1)) := lt_min one_pos (div_pos hε (by linarith))
  have hev : ∀ᶠ j in atTop, ‖fs j - f‖ < min 1 (ε / (K + 1)) := by
    have := (Metric.tendsto_nhds.1 h) _ hδ
    filter_upwards [this] with j hj
    rwa [dist_eq_norm] at hj
  filter_upwards [hev] with j hj t ht
  have h1 : ‖fs j - f‖ < 1 := lt_of_lt_of_le hj (min_le_left _ _)
  have h2 : ‖fs j - f‖ < ε / (K + 1) := lt_of_lt_of_le hj (min_le_right _ _)
  have hfj : ‖fs j‖ ≤ R := by
    have := norm_sub_norm_le (fs j) f
    rw [hR]; linarith
  have hf : ‖f‖ ≤ R := by rw [hR]; linarith
  have ht' : t ∈ Icc (-(max T 0)) (max T 0) :=
    ⟨le_trans (neg_le_neg (le_max_left T 0)) ht.1, le_trans ht.2 (le_max_left T 0)⟩
  calc ‖flowMap hκ (fs j) t - flowMap hκ f t‖ ≤ K * ‖fs j - f‖ := hK _ _ hfj hf t ht'
    _ ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left h2.le hK0
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
        nlinarith

/-- **Conservation of the discriminant along the `L²` flow.** -/
theorem disc_const_flow {κ : ℝ} (hκ : 0 < κ) (f : HL L) (z : ℂ) (t s : ℝ) :
    L2SpatialTransfer.discriminant κ (flowMap hκ.le f t) z =
      L2SpatialTransfer.discriminant κ (flowMap hκ.le f s) z := by
  have hU := flow_unif hκ.le (tendsto_trunc f) (|t| + |s|)
  have ht : t ∈ Icc (-(|t| + |s|)) (|t| + |s|) :=
    ⟨by linarith [neg_abs_le t, abs_nonneg s], by linarith [le_abs_self t, abs_nonneg s]⟩
  have hs : s ∈ Icc (-(|t| + |s|)) (|t| + |s|) :=
    ⟨by linarith [neg_abs_le s, abs_nonneg t], by linarith [le_abs_self s, abs_nonneg t]⟩
  have hconv : ∀ r ∈ Icc (-(|t| + |s|)) (|t| + |s|),
      Tendsto (fun N => flowMap hκ.le (emb (trunc f N)) r) atTop (𝓝 (flowMap hκ.le f r)) := by
    intro r hr
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hU ε hε] with N hN
    rw [dist_eq_norm]
    exact hN r hr
  have hc := continuous_disc (L := L) κ z
  have lt := (hc.tendsto _).comp (hconv t ht)
  have ls := (hc.tendsto _).comp (hconv s hs)
  have heq : (fun N => L2SpatialTransfer.discriminant κ (flowMap hκ.le (emb (trunc f N)) t) z) =
      fun N => L2SpatialTransfer.discriminant κ (flowMap hκ.le (emb (trunc f N)) s) z := by
    funext N
    rw [flowMap_H1, flowMap_H1, emb_eq, emb_eq]
    exact (RA634Main.F04_cor_spectral hκ (trunc f N) t s).1 z
  have lt' : Tendsto (fun N => L2SpatialTransfer.discriminant κ (flowMap hκ.le (emb (trunc f N)) t) z)
      atTop (𝓝 (L2SpatialTransfer.discriminant κ (flowMap hκ.le f t) z)) := lt
  have ls' : Tendsto (fun N => L2SpatialTransfer.discriminant κ (flowMap hκ.le (emb (trunc f N)) s) z)
      atTop (𝓝 (L2SpatialTransfer.discriminant κ (flowMap hκ.le f s) z)) := ls
  rw [heq] at lt'
  exact tendsto_nhds_unique lt' ls'

lemma Mmeas_flow {κ : ℝ} (hκ : 0 < κ) (f : HL L) (t : ℝ) :
    FullMass.Mmeas κ (flowMap hκ.le f t) = FullMass.Mmeas κ f := by
  have h := (RootNlsInvariance.data_eq_of_disc hκ (fun z => disc_const_flow hκ f z t 0)).2.1
  rwa [(flowMap_spec hκ.le f).2.1] at h

lemma masses_flow {κ : ℝ} (hκ : 0 < κ) (f : HL L) (t : ℝ) :
    RootIndexedMasses.masses hκ (flowMap hκ.le f t) = RootIndexedMasses.masses hκ f := by
  have h := RootIndexedMasses.masses_eq_of_measure_eq hκ
    (RootNlsInvariance.measure_eq_of_disc hκ (fun z => disc_const_flow hκ f z t 0))
  rwa [(flowMap_spec hκ.le f).2.1] at h

lemma tvNorm_congr {μ ν μ' ν' : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure μ'] [IsFiniteMeasure ν'] (h1 : μ = μ') (h2 : ν = ν') :
    TotalVariation.tvNorm μ ν = TotalVariation.tvNorm μ' ν' := by
  subst h1; subst h2; rfl

/-- **R-AEE17FD6 `thm:root-L2-flow`.** -/
theorem root_L2_flow {κ : ℝ} (hκ : 0 ≤ κ) :
    ((∀ f : HL L, IsFlow κ (flowMap hκ f) ∧ flowMap hκ f 0 = f) ∧
    (∀ f : HL L, ∀ w : ℝ → HL L, IsFlow κ w → w 0 = f → w = flowMap hκ f) ∧
    (∀ f : HL L, ∀ t, ‖flowMap hκ f t‖ = ‖f‖) ∧
    (∀ (g : QuantumNLS.Sobolev.h04 L 1) (t : ℝ), flowMap hκ (emb g) t =
      emb (QuantumNLS.LocalWellPosednessFull.umax (le_refl (1 : ℝ)) κ g t)) ∧
    (∀ R T : ℝ, 0 ≤ R → 0 ≤ T → ∃ K : ℝ, 0 ≤ K ∧ ∀ f g : HL L, ‖f‖ ≤ R → ‖g‖ ≤ R →
      ∀ t ∈ Set.Icc (-T) T, ‖flowMap hκ f t - flowMap hκ g t‖ ≤ K * ‖f - g‖) ∧
    (∀ R T : ℝ, 0 ≤ R → 0 ≤ T → ∃ K : ℝ, 0 ≤ K ∧ ∀ f g : HL L, ‖f‖ ≤ R → ‖g‖ ≤ R →
      ∀ (α β : ℝ) (hαβ : α ≤ β) (hlen : β ≤ α + TL L), -T ≤ α → β ≤ T →
        ∀ u v : Lp ℂ 4 (μJ (L := L) α β), Sol hαβ hlen (cNLS κ) u (flowMap hκ f) →
          Sol hαβ hlen (cNLS κ) v (flowMap hκ g) → ‖u - v‖ ≤ K * ‖f - g‖) ∧
    (∀ s t : ℝ, ∀ f : HL L, flowMap hκ (flowMap hκ f t) s = flowMap hκ f (s + t)) ∧
    (∀ t : ℝ, ∃ e : HL L ≃ₜ HL L, (∀ f, e f = flowMap hκ f t) ∧ ∀ f, e.symm f = flowMap hκ f (-t))) ∧
    (∀ hκ' : 0 < κ,
      (∀ f : HL L, ∀ t s : ℝ,
        FullMass.Mmeas κ (flowMap hκ f t) = FullMass.Mmeas κ (flowMap hκ f s) ∧
        (∀ z : ℂ, L2SpatialTransfer.discriminant κ (flowMap hκ f t) z =
          L2SpatialTransfer.discriminant κ (flowMap hκ f s) z) ∧
        (∀ z : ℂ, NormalizedTransfer.productSymbol L κ (flowMap hκ f t) z =
          NormalizedTransfer.productSymbol L κ (flowMap hκ f s) z) ∧
        ∀ n : ℤ, (RootIndexedMasses.masses hκ' (flowMap hκ f t)).1 n =
          (RootIndexedMasses.masses hκ' (flowMap hκ f s)).1 n) ∧
      (∀ (fs : ℕ → HL L) (f : HL L), Tendsto fs atTop (𝓝 f) → ∀ T : ℝ,
        (∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ t ∈ Icc (-T) T,
          TotalVariation.tvNorm (FullMass.Mmeas κ (flowMap hκ (fs j) t))
            (FullMass.Mmeas κ (flowMap hκ f t)) < ENNReal.ofReal ε) ∧
        TendstoUniformlyOn (fun j t => RootIndexedMasses.masses hκ' (flowMap hκ (fs j) t))
          (fun t => RootIndexedMasses.masses hκ' (flowMap hκ f t)) atTop (Icc (-T) T))) := by
  refine ⟨thm_root_L2_flow hκ, fun hκ' => ⟨fun f t s => ?_, fun fs f hf T => ⟨?_, ?_⟩⟩⟩
  · have hz : ∀ z : ℂ, L2SpatialTransfer.discriminant κ (flowMap hκ f t) z =
        L2SpatialTransfer.discriminant κ (flowMap hκ f s) z := fun z => disc_const_flow hκ' f z t s
    obtain ⟨hp, hm, hn⟩ := RootNlsInvariance.data_eq_of_disc hκ' hz
    exact ⟨hm, hz, hp, hn⟩
  · intro ε hε
    have hD := (QuantumNLS.D05TotalVariation.prop_D05_total_variation (L := L)).1 κ hκ' f
    have hpair : Tendsto (fun j => ((κ, fs j) : ℝ × L2T L)) atTop (𝓝 (κ, f)) :=
      tendsto_const_nhds.prodMk_nhds hf
    have h0 := (tendsto_order.1 (hD.comp hpair)).2 (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
    filter_upwards [h0] with j hj t _
    rw [tvNorm_congr (Mmeas_flow hκ' (fs j) t) (Mmeas_flow hκ' f t)]
    exact hj
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨-, -, -, -, hcont, -⟩ := RootIndexedMasses.root_indexed_masses_proved_clauses hκ' f
    have hpair : Tendsto (fun j => ((⟨κ, hκ'⟩, fs j) : DEF014Phase.Param L)) atTop
        (𝓝 (⟨κ, hκ'⟩, f)) := tendsto_const_nhds.prodMk_nhds hf
    have hm := (hcont.tendsto _).comp hpair
    have h0 := (Metric.tendsto_nhds.1 hm) ε hε
    filter_upwards [h0] with j hj t _
    rw [masses_flow hκ' (fs j) t, masses_flow hκ' f t, dist_comm]
    exact hj

end QuantumNLS.RAEEMain

#print axioms QuantumNLS.RAEEMain.disc_const_flow
#print axioms QuantumNLS.RAEEMain.root_L2_flow
