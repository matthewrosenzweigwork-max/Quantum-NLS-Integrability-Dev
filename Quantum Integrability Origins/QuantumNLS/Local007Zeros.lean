import Mathlib
import QuantumNLS.Local007Factor
import QuantumNLS.DEF014DiscriminantAnalytic
import QuantumNLS.PhysicalUpperTraceIdentity
import QuantumNLS.L2DiscriminantRegularity
import QuantumNLS.PhysicalVacuumSourceFacts

/-! LOCAL-007 stage Z: the zero cluster of `Δ_v² - 4` near the free double zero (route (iii)-free: no argument
principle).

All statements are at index `0` for the actual discriminant `Dl κ v = L2SpatialTransfer.discriminant κ v`;
index `n` follows by the accepted gauge `Local007Gauge.sq_disc_shift`.

* `close_free` : `Δ_v → 2cos(L z/2)` uniformly on `|z| ≤ R` as `v → 0` (compactness, `ContinuousMap.curry`);
* `real_below` : for small `v`, `Re Δ_v(x) < 2` on `δ ≤ |x| ≤ r`;
* `deriv_zero_of_unique` : a unique real point with `Δ = 2` in `(-r,r)` has `Δ' = 0` (intermediate value
  theorem; this is where a second simple zero would be forced otherwise);
* `phys_factor` : if the points of `|w|<r` with `Δ_v(w) = 2` are exactly `α ± t`, then they are localized, are
  zeros (double if `t = 0`), and `Δ_v² - 4 = ((z-α)² - t²) H` with `H` entire, real on `ℝ`,
  `|H + L²| ≤ L²/4` on `|z| ≤ 3d`, `d = 1/(16 L)`. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Metric Set Filter Topology
namespace QuantumNLS.Local007Zeros
open QuantumNLS.PhysicalTensor (L2T)
variable {L : ℝ} [Fact (0 < L)]

abbrev Dl (κ : ℝ) (v : L2T L) : ℂ → ℂ := L2SpatialTransfer.discriminant κ v

theorem close_free (κ R ε : ℝ) (hε : 0 < ε) :
    ∃ ρ > 0, ∀ v : L2T L, ‖v‖ < ρ → ∀ z : ℂ, ‖z‖ ≤ R →
      ‖Dl κ v z - 2 * Complex.cos ((L : ℂ) * z / 2)‖ ≤ ε := by
  have hc : Continuous (fun p : L2T L × ℂ => Dl κ p.1 p.2) :=
    continuous_iff_continuousAt.2 fun p =>
      (DEF014DiscriminantAnalytic.analyticAt_discriminant_joint κ p).continuousAt
  haveI : CompactSpace (closedBall (0 : ℂ) R) := isCompact_iff_compactSpace.1 (isCompact_closedBall 0 R)
  have hmap : Continuous (fun p : L2T L × closedBall (0 : ℂ) R => ((p.1, (p.2 : ℂ)) : L2T L × ℂ)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hcF := hc.comp hmap
  let F : C(L2T L × closedBall (0 : ℂ) R, ℂ) := ContinuousMap.mk _ hcF
  have h0 := (ContinuousMap.curry F).continuous.continuousAt (x := (0 : L2T L))
  obtain ⟨ρ, hρ, H⟩ := Metric.continuousAt_iff.1 h0 ε hε
  refine ⟨ρ, hρ, fun v hv z hz => ?_⟩
  have h1 := H (by simpa using hv)
  have h2 := ContinuousMap.dist_apply_le_dist (f := ContinuousMap.curry F v) (g := ContinuousMap.curry F 0)
    ⟨z, by simpa using hz⟩
  have h3 : (ContinuousMap.curry F 0) ⟨z, by simpa using hz⟩ = 2 * Complex.cos ((L : ℂ) * z / 2) :=
    QuantumNLS.PhysicalVacuumSourceFacts.discriminant_zero κ z
  have h4 : (ContinuousMap.curry F v) ⟨z, by simpa using hz⟩ = Dl κ v z := rfl
  rw [h3, h4] at h2
  rw [← dist_eq_norm]
  exact h2.trans h1.le

theorem real_of_re {κ : ℝ} (v : L2T L) (x : ℝ) : Dl κ v (x : ℂ) = (((Dl κ v (x : ℂ)).re : ℝ) : ℂ) := by
  apply Complex.ext
  · simp
  · simpa using QuantumNLS.L2DiscriminantRegularity.discriminant_real κ v x

theorem real_below (κ : ℝ) {r δ : ℝ} (hr0 : 0 < r) (hr : r < 2 * Real.pi / L) (hδ : 0 < δ) (hδr : δ ≤ r) :
    ∃ ρ > 0, ∀ v : L2T L, ‖v‖ < ρ → ∀ x : ℝ, δ ≤ |x| → |x| ≤ r → (Dl κ v (x : ℂ)).re < 2 := by
  have hL : 0 < L := Fact.out
  set K : Set ℝ := closedBall 0 r ∩ {x | δ ≤ |x|} with hK
  have hKc : IsCompact K :=
    (isCompact_closedBall 0 r).inter_right (isClosed_le continuous_const continuous_abs)
  have hKne : K.Nonempty := ⟨δ, by simp [hK, abs_of_pos hδ, hδr]⟩
  have hg : Continuous fun x : ℝ => |Real.sin (L * x / 4)| := by fun_prop
  obtain ⟨x0, hx0, hmin⟩ := hKc.exists_isMinOn hKne hg.continuousOn
  set c0 := |Real.sin (L * x0 / 4)| with hc0
  have hx0abs : δ ≤ |x0| ∧ |x0| ≤ r := by
    simp only [hK, mem_inter_iff, mem_closedBall, dist_zero_right, Real.norm_eq_abs, mem_setOf_eq] at hx0
    exact ⟨hx0.2, hx0.1⟩
  have hc0pos : 0 < c0 := by
    rw [hc0, abs_pos]
    intro h
    have hb : |L * x0 / 4| < Real.pi := by
      have : L * |x0| ≤ L * r := by gcongr; exact hx0abs.2
      have h2 : L * r < 2 * Real.pi := by
        have := (lt_div_iff₀ hL).1 hr
        linarith
      rw [abs_div, abs_mul, abs_of_pos hL, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      nlinarith [Real.pi_pos]
    have := (Real.sin_eq_zero_iff_of_lt_of_lt (abs_lt.1 hb).1 (abs_lt.1 hb).2).1 h
    have h' : x0 = 0 := by
      have h0 : L * x0 = 0 := by linarith
      exact (mul_eq_zero.1 h0).resolve_left hL.ne'
    rw [h', abs_zero] at hx0abs
    linarith [hx0abs.1]
  obtain ⟨ρ, hρ, hclose⟩ := close_free (L := L) κ r (2 * c0 ^ 2) (by positivity)
  refine ⟨ρ, hρ, fun v hv x hx1 hx2 => ?_⟩
  have hxK : x ∈ K := by simp [hK, hx1, hx2]
  have hmn : c0 ≤ |Real.sin (L * x / 4)| := hmin hxK
  have hcl := hclose v hv x (by simpa [Real.norm_eq_abs] using hx2)
  have hre : |(Dl κ v (x : ℂ)).re - 2 * Real.cos (L * x / 2)| ≤ 2 * c0 ^ 2 := by
    have h1 : (Dl κ v (x : ℂ)).re - 2 * Real.cos (L * x / 2) =
        (Dl κ v (x : ℂ) - 2 * Complex.cos ((L : ℂ) * (x : ℂ) / 2)).re := by
      have : (2 * Complex.cos ((L : ℂ) * (x : ℂ) / 2)).re = 2 * Real.cos (L * x / 2) := by
        have e : (L : ℂ) * (x : ℂ) / 2 = ((L * x / 2 : ℝ) : ℂ) := by push_cast; ring
        rw [e]
        have : (2 : ℂ) * Complex.cos ((L * x / 2 : ℝ) : ℂ) = ((2 * Real.cos (L * x / 2) : ℝ) : ℂ) := by
          push_cast; ring
        rw [this, Complex.ofReal_re]
      rw [Complex.sub_re, this]
    rw [h1]
    exact (Complex.abs_re_le_norm _).trans hcl
  have hcos : Real.cos (L * x / 2) = 1 - 2 * Real.sin (L * x / 4) ^ 2 := by
    have : L * x / 2 = 2 * (L * x / 4) := by ring
    rw [this, Real.cos_two_mul, Real.cos_sq']
    ring
  have hs2 : c0 ^ 2 ≤ Real.sin (L * x / 4) ^ 2 := by
    rw [← sq_abs (Real.sin (L * x / 4))]
    exact pow_le_pow_left₀ hc0pos.le hmn 2
  have := (abs_le.1 hre).2
  rw [hcos] at this
  nlinarith

theorem deriv_zero_of_unique (κ : ℝ) (v : L2T L) {α δ r : ℝ} (hδr : δ < r) (hα : |α| < δ)
    (hb : ∀ x : ℝ, δ ≤ |x| → |x| ≤ r → (Dl κ v (x : ℂ)).re < 2)
    (h2 : Dl κ v (α : ℂ) = 2) (huniq : ∀ x : ℝ, |x| < r → Dl κ v (x : ℂ) = 2 → x = α) :
    deriv (Dl κ v) (α : ℂ) = 0 := by
  have hD := QuantumNLS.PhysicalUpperTraceIdentity.entire_discriminant κ v
  have hda : HasDerivAt (Dl κ v) (deriv (Dl κ v) (α : ℂ)) (α : ℂ) := (hD (α : ℂ)).hasDerivAt
  set c := deriv (Dl κ v) (α : ℂ) with hc
  have hreal : ∀ y : ℝ, (Dl κ v (y : ℂ)).im = 0 := fun y =>
    QuantumNLS.L2DiscriminantRegularity.discriminant_real κ v y
  have hR : HasDerivAt (fun y : ℝ => Dl κ v (y : ℂ)) c α := hda.comp_ofReal
  have him : c.im = 0 := by
    have h1 : HasDerivAt (fun y : ℝ => (Dl κ v (y : ℂ)).im) c.im α :=
      (Complex.imCLM.hasFDerivAt.comp_hasDerivAt (α : ℝ) hR)
    have h0 : HasDerivAt (fun y : ℝ => (Dl κ v (y : ℂ)).im) 0 α := by
      simpa [hreal] using hasDerivAt_const α (0 : ℝ)
    exact h1.unique h0
  set φ : ℝ → ℝ := fun y => (Dl κ v (y : ℂ)).re with hφ
  have hφd : HasDerivAt φ c.re α := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (α : ℝ) hR
  have hφc : Continuous φ := Complex.continuous_re.comp (hD.continuous.comp Complex.continuous_ofReal)
  have hφα : φ α = 2 := by
    have := congrArg Complex.re h2
    simpa [hφ] using this
  have hφeq : ∀ x : ℝ, φ x = 2 → |x| < r → x = α := fun x hx hxr => huniq x hxr (by
    rw [real_of_re v x]; rw [show (Dl κ v (x : ℂ)).re = 2 from hx]; simp)
  have hre : c.re = 0 := by
    by_contra hne
    obtain ⟨hαδ2, hαδ1⟩ := abs_lt.1 hα
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · -- derivative negative: φ(α - s) > 2, φ(-δ) < 2
      have hs := hφd.tendsto_slope_zero_left
      have hev : ∀ᶠ s in 𝓝[<] (0 : ℝ), s⁻¹ • (φ (α + s) - φ α) < 0 :=
        hs.eventually (gt_mem_nhds hneg)
      have hev2 : ∀ᶠ s in 𝓝[<] (0 : ℝ), s ∈ Ioo (-(α + δ)) 0 :=
        Ioo_mem_nhdsLT (by linarith)
      obtain ⟨s, hs1, hs2⟩ := (hev.and hev2).exists
      obtain ⟨hsa, hsb⟩ := hs2
      have hspos : φ (α + s) > 2 := by
        have h3 : s⁻¹ * (φ (α + s) - φ α) < 0 := by simpa using hs1
        have hsneg : s < 0 := hsb
        have : φ (α + s) - φ α > 0 := by
          by_contra hle
          push Not at hle
          have : 0 ≤ s⁻¹ * (φ (α + s) - φ α) := mul_nonneg_of_nonpos_of_nonpos (inv_nonpos.2 hsneg.le) hle
          linarith
        linarith
      have hm : φ (-δ) < 2 := by
        have := hb (-δ) (by simp [abs_of_pos (show 0 < δ by linarith [abs_nonneg α])]) (by
          simp [abs_of_pos (show 0 < δ by linarith [abs_nonneg α])]; linarith)
        simpa [hφ] using this
      have hle : -δ ≤ α + s := by linarith [hsa]
      obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc hle hφc.continuousOn
        (show (2 : ℝ) ∈ Icc (φ (-δ)) (φ (α + s)) from ⟨hm.le, hspos.le⟩)
      have hxr : |x| < r := by
        have : -δ ≤ x ∧ x ≤ α + s := hx
        rw [abs_lt]; constructor <;> linarith
      have := hφeq x hx0 hxr
      linarith [hx.2, hsb]
    · have hs := hφd.tendsto_slope_zero_right
      have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), s⁻¹ • (φ (α + s) - φ α) > 0 :=
        hs.eventually (lt_mem_nhds hpos)
      have hev2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo 0 (δ - α) := Ioo_mem_nhdsGT (by linarith)
      obtain ⟨s, hs1, hs2⟩ := (hev.and hev2).exists
      obtain ⟨hsa, hsb⟩ := hs2
      have hspos : φ (α + s) > 2 := by
        have h3 : s⁻¹ * (φ (α + s) - φ α) > 0 := by simpa using hs1
        have hsp : 0 < s := hsa
        have : φ (α + s) - φ α > 0 := by
          by_contra hle
          push Not at hle
          have : s⁻¹ * (φ (α + s) - φ α) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 hsp.le) hle
          linarith
        linarith
      have hm : φ δ < 2 := by
        have hδ0 : 0 < δ := by linarith [abs_nonneg α]
        have := hb δ (by simp [abs_of_pos hδ0]) (by simp [abs_of_pos hδ0]; linarith)
        simpa [hφ] using this
      have hle : α + s ≤ δ := by linarith [hsb]
      obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc' hle hφc.continuousOn
        (show (2 : ℝ) ∈ Icc (φ δ) (φ (α + s)) from ⟨hm.le, hspos.le⟩)
      have hxr : |x| < r := by
        have : α + s ≤ x ∧ x ≤ δ := hx
        rw [abs_lt]; constructor <;> linarith
      have := hφeq x hx0 hxr
      linarith [hx.1, hsa]
  exact Complex.ext (by simpa using hre) (by simpa using him)


theorem norm_two_cos_le {w : ℂ} (hw : ‖w‖ ≤ 1 / 8) : ‖2 * Complex.cos w‖ ≤ 5 / 2 := by
  have h := Complex.cos_bound (hw.trans (by norm_num))
  have h1 : ‖Complex.cos w‖ ≤ ‖1 - w ^ 2 / 2‖ + ‖w‖ ^ 4 * (5 / 96) := by
    calc ‖Complex.cos w‖ = ‖(Complex.cos w - (1 - w ^ 2 / 2)) + (1 - w ^ 2 / 2)‖ := by ring_nf
      _ ≤ ‖Complex.cos w - (1 - w ^ 2 / 2)‖ + ‖1 - w ^ 2 / 2‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have h2 : ‖1 - w ^ 2 / 2‖ ≤ 1 + ‖w‖ ^ 2 / 2 := by
    calc ‖1 - w ^ 2 / 2‖ ≤ ‖(1 : ℂ)‖ + ‖w ^ 2 / 2‖ := norm_sub_le _ _
      _ = 1 + ‖w‖ ^ 2 / 2 := by rw [norm_one, norm_div, norm_pow, Complex.norm_two]
  have hn : ‖w‖ ^ 2 ≤ 1 / 64 := by nlinarith [norm_nonneg w]
  have hn4 : ‖w‖ ^ 4 ≤ 1 / 64 := by nlinarith [norm_nonneg w, sq_nonneg (‖w‖ ^ 2)]
  rw [norm_mul, Complex.norm_two]
  nlinarith

theorem sq_sub_le {a b : ℂ} {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hab : ‖a - b‖ ≤ ε)
    (hb : ‖b‖ ≤ 5 / 2) : ‖a ^ 2 - b ^ 2‖ ≤ 6 * ε := by
  have e : a ^ 2 - b ^ 2 = (a - b) * ((a - b) + 2 * b) := by ring
  rw [e, norm_mul]
  have h2 : ‖(a - b) + 2 * b‖ ≤ 6 := by
    calc ‖(a - b) + 2 * b‖ ≤ ‖a - b‖ + ‖2 * b‖ := norm_add_le _ _
      _ ≤ ε + 2 * (5 / 2) := by rw [norm_mul, Complex.norm_two]; linarith
      _ ≤ 6 := by linarith
  nlinarith [norm_nonneg (a - b)]

theorem phys_factor (κ : ℝ) {r : ℝ} (hr0 : 0 < r) (hr : r < 2 * Real.pi / L) :
    ∃ ρ > 0, ∀ v : L2T L, ‖v‖ < ρ → ∀ α t : ℝ, 0 ≤ t → |α| + t < r →
      (∀ w : ℂ, ‖w‖ < r → (Dl κ v w = 2 ↔ (w = (α : ℂ) + t ∨ w = (α : ℂ) - t))) →
      |α| + t < (1 / (16 * L)) / 40 ∧ Dl κ v ((α : ℂ) + t) = 2 ∧ Dl κ v ((α : ℂ) - t) = 2 ∧
      (t = 0 → deriv (Dl κ v) (α : ℂ) = 0) ∧
      ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ (∀ z, Dl κ v z ^ 2 - 4 = ((z - α) ^ 2 - (t : ℂ) ^ 2) * H z) ∧
        (∀ x : ℝ, (H (x : ℂ)).im = 0) ∧
        (∀ z : ℂ, ‖z‖ ≤ 3 * (1 / (16 * L)) → ‖H z + (L : ℂ) ^ 2‖ ≤ L ^ 2 / 4) := by
  have hL : 0 < L := Fact.out
  set d : ℝ := 1 / (16 * L) with hd
  have hd0 : 0 < d := by rw [hd]; positivity
  set δ1 : ℝ := min (d / 40) (r / 2) with hδ1
  have hδ10 : 0 < δ1 := lt_min (by positivity) (by positivity)
  have hδ1r : δ1 < r := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hδ1d : δ1 ≤ d / 40 := min_le_left _ _
  obtain ⟨ρ1, hρ1, hbelow⟩ := real_below (L := L) κ hr0 hr hδ10 hδ1r.le
  obtain ⟨ρ2, hρ2, hcl⟩ := close_free (L := L) κ (2 * Real.pi / L) (1 / 30720) (by norm_num)
  refine ⟨min ρ1 ρ2, lt_min hρ1 hρ2, fun v hv α t ht hαt hhyp => ?_⟩
  have hv1 : ‖v‖ < ρ1 := lt_of_lt_of_le hv (min_le_left _ _)
  have hv2 : ‖v‖ < ρ2 := lt_of_lt_of_le hv (min_le_right _ _)
  have hb := hbelow v hv1
  have hD := QuantumNLS.PhysicalUpperTraceIdentity.entire_discriminant κ v
  have hpn : ((α + t : ℝ) : ℂ) = (α : ℂ) + t := by push_cast; ring
  have hmn : ((α - t : ℝ) : ℂ) = (α : ℂ) - t := by push_cast; ring
  have hp1 : |α + t| < r := lt_of_le_of_lt (by
    calc |α + t| ≤ |α| + |t| := abs_add_le _ _
      _ = |α| + t := by rw [abs_of_nonneg ht]) hαt
  have hp2 : |α - t| < r := lt_of_le_of_lt (by
    calc |α - t| ≤ |α| + |t| := abs_sub _ _
      _ = |α| + t := by rw [abs_of_nonneg ht]) hαt
  have hz1 : Dl κ v ((α : ℂ) + t) = 2 :=
    (hhyp ((α : ℂ) + t) (by rw [← hpn, Complex.norm_real, Real.norm_eq_abs]; exact hp1)).2 (Or.inl rfl)
  have hz2 : Dl κ v ((α : ℂ) - t) = 2 :=
    (hhyp ((α : ℂ) - t) (by rw [← hmn, Complex.norm_real, Real.norm_eq_abs]; exact hp2)).2 (Or.inr rfl)
  -- localization
  have hloc : ∀ x : ℝ, |x| < r → Dl κ v (x : ℂ) = 2 → |x| < δ1 := by
    intro x hx hx2
    by_contra hge
    push Not at hge
    have := hb x hge hx.le
    rw [hx2] at this
    simp at this
  have hl1 := hloc (α + t) hp1 (by rw [hpn]; exact hz1)
  have hl2 := hloc (α - t) hp2 (by rw [hmn]; exact hz2)
  have hαt1 : |α| + t < δ1 := by
    rcases le_total 0 α with h | h
    · rw [abs_of_nonneg h]; rw [abs_of_nonneg (by linarith)] at hl1; exact hl1
    · rw [abs_of_nonpos h]
      have : |α - t| = t - α := by rw [abs_of_nonpos (by linarith)]; ring
      rw [this] at hl2; linarith
  have hαδ : |α| < δ1 := by linarith
  have hderiv : t = 0 → deriv (Dl κ v) (α : ℂ) = 0 := by
    intro ht0
    subst ht0
    refine deriv_zero_of_unique κ v hδ1r hαδ hb (by simpa using hz1) ?_
    intro x hx hx2
    have := (hhyp (x : ℂ) (by simpa [Real.norm_eq_abs] using hx)).1 hx2
    rcases this with h | h <;> (have := Complex.ofReal_injective (by simpa using h); linarith)
  -- the factorization
  set f : ℂ → ℂ := fun z => Dl κ v z ^ 2 - 4 with hf
  have hfd : Differentiable ℂ f := (hD.pow 2).sub_const 4
  have hf1 : f ((α : ℂ) + t) = 0 := by simp [hf, hz1]; norm_num
  have hf2 : f ((α : ℂ) - t) = 0 := by simp [hf, hz2]; norm_num
  have hf3 : t = 0 → deriv f (α : ℂ) = 0 := by
    intro ht0
    have hdd := (hD (α : ℂ)).hasDerivAt
    have : HasDerivAt f (2 * Dl κ v (α : ℂ) * deriv (Dl κ v) (α : ℂ)) (α : ℂ) := by
      simpa [hf] using (hdd.pow 2).sub_const 4
    rw [this.deriv, hderiv ht0]; simp
  obtain ⟨H, hHd, hfH⟩ := Local007Factor.factor_exists hfd α t ht hf1 hf2 hf3
  refine ⟨?_, hz1, hz2, hderiv, H, hHd, hfH, ?_, ?_⟩
  · exact lt_of_lt_of_le hαt1 hδ1d
  · refine Local007Factor.H_real hHd α t hfH (fun x => ?_)
    have := QuantumNLS.L2DiscriminantRegularity.discriminant_real κ v x
    simp [hf, pow_two, Complex.mul_im, this]
  · apply Local007Factor.H_close hL hd hHd ht (by linarith [hδ1d]) hfH
    intro ξ hξ
    have hw : ‖(L : ℂ) * ξ / 2‖ ≤ 1 / 8 := by
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hL.le, Complex.norm_two, hξ, hd]
      have : L * (3 * (1 / (16 * L))) = 3 / 16 := by field_simp
      rw [this]; norm_num
    have hR : ‖ξ‖ ≤ 2 * Real.pi / L := by
      rw [hξ, hd, show 3 * (1 / (16 * L)) = 3 / (16 * L) by ring]
      rw [div_le_div_iff₀ (by positivity) hL]
      nlinarith [Real.pi_gt_three]
    have h1 := hcl v hv2 ξ hR
    have h2 := sq_sub_le (by norm_num) (by norm_num) h1 (norm_two_cos_le hw)
    have e : f ξ - (2 * Complex.cos ((L : ℂ) * ξ / 2)) ^ 2 + 4 =
        Dl κ v ξ ^ 2 - (2 * Complex.cos ((L : ℂ) * ξ / 2)) ^ 2 := by simp [hf]; ring
    rw [e]
    refine h2.trans ?_
    have hL2d2 : L ^ 2 * d ^ 2 = 1 / 256 := by
      have : L * d = 1 / 16 := by rw [hd]; field_simp
      calc L ^ 2 * d ^ 2 = (L * d) ^ 2 := by ring
        _ = 1 / 256 := by rw [this]; norm_num
    rw [hL2d2]; norm_num

end QuantumNLS.Local007Zeros
#print axioms QuantumNLS.Local007Zeros.close_free
#print axioms QuantumNLS.Local007Zeros.real_below
#print axioms QuantumNLS.Local007Zeros.deriv_zero_of_unique
#print axioms QuantumNLS.Local007Zeros.phys_factor
