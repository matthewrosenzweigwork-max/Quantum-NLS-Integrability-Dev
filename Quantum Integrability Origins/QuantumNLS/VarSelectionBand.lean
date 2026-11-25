import Mathlib
import QuantumNLS.SelectionBand
import QuantumNLS.VarCoupling

/-!
# CC:F04:variable-coupling (R-C88B5D59), step 2: the whole-band cluster comparison at contact `c_N = κ_N/N`

Source: `F04.tex` line 412 (proof): "In the external-force argument the cluster error is bounded by `4√(κ_+ K_N/(LN))`, the arctangent replacement error is `O(N(κ_N/N)³) = O(N⁻²)`, and its remaining coefficient `N c_N = κ_N` tends to `κ`. Therefore (CC:F04:external-limit), Lemma CC:F04:local-height and Proposition CC:F04:selection hold with the same limiting phase."

`selection_coreV` is `SelectionBand.selection_core` (read-only; its proof is followed step by step) for the real-label equations at contact `κs N/(N+1)`, `κs → κ > 0`, `κs N > 0`: the same hypotheses (`hloc`, `hlab`, `xs` with `θ_κ(xs) = πλ`) give `q_{i_N,N} → xs`.
The single-`N` estimates (`force_approx_band`, `cluster_bound`, `extForce_slope`, `H_surjective`, `cluster_frac`, `theta_mono`, `M_tendsto`) are reused unchanged; the only changes are that the coupling inside the finite-`N` estimates is `κs N`, which is `≤ 2κ` eventually (the printed `κ_+`), and that the external-limit coefficient `N c_N = κs N → κ` (`main_convV`).
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section
open scoped BigOperators Topology BoundedContinuousFunction
open Finset Filter MeasureTheory

namespace QuantumNLS.VarSelectionBand

open QuantumNLS.LocalHeight QuantumNLS.SelectionBand QuantumNLS.VarCoupling

lemma main_convV {μ : Measure ℝ} [IsProbabilityMeasure μ] {q : (N : ℕ) → Fin (N + 1) → ℝ}
    (hw : EmpiricalWeakConv q μ) {L κ x ε : ℝ} {κs : ℕ → ℝ} (hκs : Tendsto κs atTop (𝓝 κ))
    (hε : 0 < ε) (hnull : μ (Set.Icc (x - 4 * ε) (x + 4 * ε)) = 0) :
    Tendsto (fun N : ℕ => L * x - 2 * κs N * ((1 / ((N : ℝ) + 1)) * ∑ j, gK x ε (q N j))) atTop
      (𝓝 (2 * theta L κ μ x)) := by
  have hae : ∀ᵐ y ∂μ, 4 * ε < |y - x| := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with y hy
    by_contra h
    push Not at h
    exact hy ⟨by linarith [(abs_le.mp h).1], by linarith [(abs_le.mp h).2]⟩
  have hgint : ∫ y, (gBCF x ε hε) y ∂μ = ∫ y, 1 / (x - y) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with y hy
    show gK x ε y = 1 / (x - y)
    exact gK_eq hε (by rw [abs_sub_comm]; linarith)
  have hA : Tendsto (fun N : ℕ => (1 / ((N : ℝ) + 1)) * ∑ j, gK x ε (q N j)) atTop
      (𝓝 (∫ y, 1 / (x - y) ∂μ)) := by
    rw [← hgint]; exact hw (gBCF x ε hε)
  have := (tendsto_const_nhds (x := L * x)).sub ((hκs.const_mul 2).mul hA)
  unfold theta
  convert this using 2
  ring

/-- **`selection_core` at contact `κs N/(N+1)`**: `q_{i_N,N} → x(λ)`. -/
theorem selection_coreV {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ) {κs : ℕ → ℝ}
    (hκs : Tendsto κs atTop (𝓝 κ)) (hpos : ∀ N, 0 < κs N) {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hna : ∀ y, μ {y} = 0) {r l : ℝ} (hrl : r < l)
    (hband : μ (Set.Ioo r l) = 0)
    {q ν : (N : ℕ) → Fin (N + 1) → ℝ} (hB : ∀ N, RealBetheV L κs N (q N) (ν N))
    (hw : EmpiricalWeakConv q μ) (i : (N : ℕ) → Fin (N + 1)) {lam : ℝ}
    (hloc : ∀ h : ℝ, 0 < h → ∀ᶠ N : ℕ in atTop, q N (i N) ∈ Set.Ioo (r - h) (l + h))
    (hlab : Tendsto (fun N => ν N (i N)) atTop (𝓝 lam))
    {xs : ℝ} (hxs : xs ∈ Set.Ioo r l) (hθ : theta L κ μ xs = Real.pi * lam) :
    Tendsto (fun N => q N (i N)) atTop (𝓝 xs) := by
  have hIcc : μ (Set.Icc r l) = 0 := by
    have hsub : Set.Icc r l ⊆ Set.Ioo r l ∪ {r} ∪ {l} := by
      intro y hy
      rcases eq_or_lt_of_le hy.1 with h | h
      · simp [← h]
      · rcases eq_or_lt_of_le hy.2 with h' | h'
        · simp [h']
        · exact Or.inl (Or.inl ⟨h, h'⟩)
    exact measure_mono_null hsub (measure_union_null (measure_union_null hband (hna r)) (hna l))
  -- the printed `κ_+`: eventually `κs N ≤ 2 κ`
  set K2 : ℝ := 2 * κ with hK2
  have hK2pos : 0 < K2 := by rw [hK2]; positivity
  have hκle : ∀ᶠ N : ℕ in atTop, κs N < K2 :=
    hκs.eventually (gt_mem_nhds (by rw [hK2]; linarith))
  rw [Metric.tendsto_nhds]
  intro δ hδ
  -- (1) the points `x_- < xs < x_+` with `θ(x_-) < πλ < θ(x_+)`
  have hm1 : 0 < min (xs - r) (l - xs) := lt_min (sub_pos.2 hxs.1) (sub_pos.2 hxs.2)
  set δ' : ℝ := min (δ / 4) (min (xs - r) (l - xs) / 2) with hδ'
  have hδ'pos : 0 < δ' := lt_min (by linarith) (by linarith)
  have hδ'1 : δ' ≤ δ / 4 := min_le_left _ _
  have hδ'2 : δ' ≤ min (xs - r) (l - xs) / 2 := min_le_right _ _
  have hmr : min (xs - r) (l - xs) ≤ xs - r := min_le_left _ _
  have hml : min (xs - r) (l - xs) ≤ l - xs := min_le_right _ _
  set xm : ℝ := xs - δ' with hxm
  set xp : ℝ := xs + δ' with hxp
  have hxm_mem : xm ∈ Set.Ioo r l := ⟨by linarith, by linarith [hxs.2]⟩
  have hxp_mem : xp ∈ Set.Ioo r l := ⟨by linarith [hxs.1], by linarith⟩
  have hθm : theta L κ μ xm ≤ theta L κ μ xs - L * δ' / 2 := by
    have := theta_mono (L := L) (κ := κ) hband hxm_mem hxs (by linarith) hκ.le
    have e : xs - xm = δ' := by rw [hxm]; ring
    rw [e] at this
    linarith
  have hθp : theta L κ μ xs + L * δ' / 2 ≤ theta L κ μ xp := by
    have := theta_mono (L := L) (κ := κ) hband hxs hxp_mem (by linarith) hκ.le
    have e : xp - xs = δ' := by rw [hxp]; ring
    rw [e] at this
    linarith
  -- (2) the scale `ε`
  set d : ℝ := min (xm - r) (l - xp) with hd
  have hd0 : 0 < d := lt_min (by linarith [hxm_mem.1]) (by linarith [hxp_mem.2])
  have hdm : d ≤ xm - r := min_le_left _ _
  have hdp : d ≤ l - xp := min_le_right _ _
  set ε : ℝ := d / 4 with hεdef
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hnullm : μ (Set.Icc (xm - 4 * ε) (xm + 4 * ε)) = 0 :=
    measure_mono_null (Set.Icc_subset_Icc (by rw [hεdef]; linarith) (by rw [hεdef]; linarith)) hIcc
  have hnullp : μ (Set.Icc (xp - 4 * ε) (xp + 4 * ε)) = 0 :=
    measure_mono_null (Set.Icc_subset_Icc (by rw [hεdef]; linarith) (by rw [hεdef]; linarith)) hIcc
  have hmainm := main_convV (L := L) hw hκs hε hnullm
  have hmainp := main_convV (L := L) hw hκs hε hnullp
  -- (3) the tolerances
  set ρ : ℝ := L * δ' / 4 with hρ
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  set τ0 : ℝ := min (ρ * ε / (4 * K2)) (L * δ ^ 2 / (64 * K2)) with hτ0
  have hτ0pos : 0 < τ0 := lt_min (by positivity) (by positivity)
  have hτ1 : 2 * K2 * τ0 / ε ≤ ρ / 2 := by
    have : τ0 ≤ ρ * ε / (4 * K2) := min_le_left _ _
    rw [div_le_iff₀ hε]
    have h4 : 4 * K2 * τ0 ≤ ρ * ε := by
      have := (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * K2)).1 this
      linarith
    nlinarith
  have hτ2 : K2 * τ0 / L ≤ (δ / 8) ^ 2 := by
    have : τ0 ≤ L * δ ^ 2 / (64 * K2) := min_le_right _ _
    rw [div_le_iff₀ hL]
    have h4 := (le_div_iff₀ (by positivity : (0 : ℝ) < 64 * K2)).1 this
    nlinarith
  -- (4) the cluster interval `[r - h, l + h]` with small mass
  obtain ⟨h', hh'0, hh'⟩ : ∃ h' : ℝ, 0 < h' ∧ μ.real (Set.Icc (r - h') (l + h')) < τ0 := by
    have hM := (M_tendsto hna hband).eventually (eventually_lt_nhds hτ0pos)
    obtain ⟨h', h1, h2⟩ := (hM.and self_mem_nhdsWithin).exists
    exact ⟨h', h2, h1⟩
  set h : ℝ := h' / 2 with hhdef
  have hh0 : 0 < h := by rw [hhdef]; positivity
  have hh2 : μ.real (Set.Icc (r - 2 * h) (l + 2 * h)) < τ0 := by
    have : 2 * h = h' := by rw [hhdef]; ring
    rw [this]; exact hh'
  have hab : r - h ≤ l + h := by linarith
  have hKfrac := cluster_frac hw hh0 hrl.le hh2
  -- (5) eventual inequalities
  have hcN : ∀ N : ℕ, 0 < κs N / ((N : ℝ) + 1) := fun N => div_pos (hpos N) (by positivity)
  have h1N : Tendsto (fun N : ℕ => (κs N ^ 3 / ε ^ 3) * (1 / ((N : ℝ) + 1)) ^ 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => (1 / ((N : ℝ) + 1)) ^ 2) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
      simpa using this
    have := ((hκs.pow 3).div_const (ε ^ 3)).mul h1
    simpa using this
  have hev1 : ∀ᶠ N : ℕ in atTop, (κs N ^ 3 / ε ^ 3) * (1 / ((N : ℝ) + 1)) ^ 2 < ρ / 4 :=
    h1N.eventually (gt_mem_nhds (by positivity))
  have hevm : ∀ᶠ N : ℕ in atTop,
      L * xm - 2 * κs N * ((1 / ((N : ℝ) + 1)) * ∑ j, gK xm ε (q N j)) < 2 * theta L κ μ xm + ρ :=
    hmainm.eventually (gt_mem_nhds (by linarith))
  have hevp : ∀ᶠ N : ℕ in atTop,
      2 * theta L κ μ xp - ρ < L * xp - 2 * κs N * ((1 / ((N : ℝ) + 1)) * ∑ j, gK xp ε (q N j)) :=
    hmainp.eventually (lt_mem_nhds (by linarith))
  have hevlab : ∀ᶠ N : ℕ in atTop, |2 * Real.pi * ν N (i N) - 2 * Real.pi * lam| < ρ := by
    have hl := (hlab.const_mul (2 * Real.pi))
    have := (Metric.tendsto_nhds.mp hl) ρ hρ0
    filter_upwards [this] with N hN
    rwa [Real.dist_eq] at hN
  have hevloc := hloc h hh0
  -- (6) assemble
  filter_upwards [hKfrac, hev1, hevm, hevp, hevlab, hevloc, hκle] with N hK he1 hem hep hel hloc' hκN
  set c : ℝ := κs N / ((N : ℝ) + 1) with hcdef
  have hc : 0 < c := hcN N
  set a : ℝ := r - h
  set b : ℝ := l + h
  have hxmab : xm ∈ Set.Icc a b := ⟨by linarith [hxm_mem.1], by linarith [hxm_mem.2]⟩
  have hxpab : xp ∈ Set.Icc a b := ⟨by linarith [hxp_mem.1], by linarith [hxp_mem.2]⟩
  set Kc : ℝ := ((cluster a b (q N)).card : ℝ) with hKc
  have hKfracN : Kc / ((N : ℝ) + 1) < τ0 := hK
  have hKnn : 0 ≤ Kc := by positivity
  have hKN0 : 0 ≤ Kc / ((N : ℝ) + 1) := by positivity
  have hκN' : κs N ≤ K2 := hκN.le
  have hκpos : 0 < κs N := hpos N
  have hK2nn : 0 ≤ K2 := hK2pos.le
  have hKfracN' : Kc / ((N : ℝ) + 1) ≤ τ0 := hKfracN.le
  have hτ0nn : 0 ≤ τ0 := hτ0pos.le
  -- the force estimate at `x_±`
  have hbound : ∀ x : ℝ, a ≤ x - 2 * ε → x + 2 * ε ≤ b →
      |force L c a b (q N) x - (L * x - 2 * c * ∑ j, gK x ε (q N j))| ≤ ρ := by
    intro x hxa hxb
    have := force_approx_band (L := L) (c := c) hc.le hε hxa hxb (q N)
    refine this.trans ?_
    have e1 : ((N + 1 : ℕ) : ℝ) * (c / ε) ^ 3 = (κs N ^ 3 / ε ^ 3) * (1 / ((N : ℝ) + 1)) ^ 2 := by
      rw [hcdef]; push_cast; field_simp
    have e2 : c * (Kc * (1 / ε)) = κs N * (Kc / ((N : ℝ) + 1)) / ε := by
      rw [hcdef]; field_simp
    have hcard : ((Fintype.card (Fin (N + 1)) : ℕ) : ℝ) = ((N + 1 : ℕ) : ℝ) := by simp
    calc 2 * (((N + 1 : ℕ) : ℝ) * (c / ε) ^ 3 + c * ((cluster a b (q N)).card * (1 / ε)))
        = 2 * ((κs N ^ 3 / ε ^ 3) * (1 / ((N : ℝ) + 1)) ^ 2 + κs N * (Kc / ((N : ℝ) + 1)) / ε) := by
          rw [e1]; congr 2
      _ ≤ ρ := by
          have h3 : κs N * (Kc / ((N : ℝ) + 1)) / ε ≤ K2 * τ0 / ε := by
            gcongr
          have h4 : K2 * τ0 / ε ≤ ρ / 4 := by
            have := hτ1
            have e : 2 * K2 * τ0 / ε = 2 * (K2 * τ0 / ε) := by ring
            linarith
          linarith
  have hfm : force L c a b (q N) xm ≤ 2 * Real.pi * lam - 2 * ρ := by
    have hb1 := hbound xm (by linarith [hdm]) (by linarith [hdm, hdp, hxm_mem.2, hxp_mem.2])
    rw [abs_le] at hb1
    have e : 2 * κs N * ((1 / ((N : ℝ) + 1)) * ∑ j, gK xm ε (q N j)) =
        2 * c * ∑ j, gK xm ε (q N j) := by rw [hcdef]; field_simp
    rw [e] at hem
    have : 2 * theta L κ μ xm ≤ 2 * Real.pi * lam - 4 * ρ := by
      have : theta L κ μ xm ≤ Real.pi * lam - L * δ' / 2 := by rw [← hθ]; exact hθm
      rw [hρ]; linarith
    linarith [hb1.2]
  have hfp : 2 * Real.pi * lam + 2 * ρ ≤ force L c a b (q N) xp := by
    have hb1 := hbound xp (by linarith [hdm, hdp, hxm_mem.1, hxp_mem.1]) (by linarith [hdp])
    rw [abs_le] at hb1
    have e : 2 * κs N * ((1 / ((N : ℝ) + 1)) * ∑ j, gK xp ε (q N j)) =
        2 * c * ∑ j, gK xp ε (q N j) := by rw [hcdef]; field_simp
    rw [e] at hep
    have : 2 * Real.pi * lam + 4 * ρ ≤ 2 * theta L κ μ xp := by
      have : Real.pi * lam + L * δ' / 2 ≤ theta L κ μ xp := by rw [← hθ]; exact hθp
      rw [hρ]; linarith
    linarith [hb1.1]
  have hlabs := abs_lt.1 hel
  -- the inverse `p` of the extended external force
  have hsurj : Function.Surjective (extForce L c a b (q N)) :=
    ExternalConfinement.H_surjective hL (extForce_continuous hab _) (extForce_slope hc.le hab _)
  set p : ℝ := Function.surjInv hsurj (2 * Real.pi * ν N (i N)) with hpdef
  have hp : extForce L c a b (q N) p = 2 * Real.pi * ν N (i N) := Function.surjInv_eq hsurj _
  have hxmf : extForce L c a b (q N) xm = force L c a b (q N) xm := extForce_of_mem hxmab
  have hxpf : extForce L c a b (q N) xp = force L c a b (q N) xp := extForce_of_mem hxpab
  have hpm : xm < p := by
    by_contra hle
    push Not at hle
    have := extForce_slope (L := L) hc.le hab (q N) p xm hle
    nlinarith [hlabs.1, hlabs.2]
  have hpp : p < xp := by
    by_contra hle
    push Not at hle
    have := extForce_slope (L := L) hc.le hab (q N) xp p hle
    nlinarith [hlabs.1, hlabs.2]
  have hi : i N ∈ cluster a b (q N) :=
    Finset.mem_filter.mpr ⟨mem_univ _, ⟨hloc'.1.le, hloc'.2.le⟩⟩
  have hcb := cluster_bound hL hc hab (hB N).sorted (hB N).labels (hB N).eqn hi hp
  have hsq : 4 * Real.sqrt (c * (cluster a b (q N)).card / L) ≤ δ / 2 := by
    have h1 : c * (cluster a b (q N)).card / L ≤ (δ / 8) ^ 2 := by
      have e : c * (cluster a b (q N)).card / L = (κs N / L) * (Kc / ((N : ℝ) + 1)) := by
        rw [hcdef, hKc]; field_simp
      rw [e]
      calc (κs N / L) * (Kc / ((N : ℝ) + 1)) ≤ (K2 / L) * τ0 := by
            gcongr
        _ = K2 * τ0 / L := by ring
        _ ≤ (δ / 8) ^ 2 := hτ2
    have h2 : Real.sqrt (c * (cluster a b (q N)).card / L) ≤ δ / 8 := by
      calc Real.sqrt (c * (cluster a b (q N)).card / L) ≤ Real.sqrt ((δ / 8) ^ 2) :=
            Real.sqrt_le_sqrt h1
        _ = δ / 8 := Real.sqrt_sq (by positivity)
    linarith
  rw [Real.dist_eq]
  have h3 : |q N (i N) - p| ≤ δ / 2 := hcb.trans hsq
  have h4 : |p - xs| < δ' := by
    rw [abs_lt]; constructor <;> linarith
  calc |q N (i N) - xs| = |(q N (i N) - p) + (p - xs)| := by ring_nf
    _ ≤ |q N (i N) - p| + |p - xs| := abs_add_le _ _
    _ < δ := by linarith

end QuantumNLS.VarSelectionBand

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.VarSelectionBand.main_convV
#print axioms QuantumNLS.VarSelectionBand.selection_coreV
