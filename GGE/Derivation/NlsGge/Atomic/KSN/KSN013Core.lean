import Mathlib
import NlsGge.Atomic.KSN.KSN013Host
import NlsGge.Atomic.KSN.KSN011
import NlsGge.GK38.TauGamma
import NlsGge.GK38.StdRootBranchesScalar
import NlsGge.GK38.IsolatingTopology
import NlsGge.GK38.IsolatingDistance
import NlsGge.GK38.XiSqKernel

/- KSN013 CORE PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/KSN/KSN013Core.lean.
   Supporting (non-packet) core for the round-15 corrected KSN-013 head (PRO_DEFINITION_RESPONSE_FP80_15.md, Q1).
   Route = Pro Q1 "Why this fixes the quantifiers", for ONE common isolating geometry (C,R,c,J):
   * separation: z in the closed nth disc and any point of the open kth disc (k ≠ n) are at distance ≥ c⁻¹|k-n|
     (ballDistance38 lower bound + closure of the open disc);
   * standard-root formula: with τ=(λ⁺+λ⁻)/2, g=(λ⁺-λ⁻)², S=stdRoot38 τ g z, w=τ-z: S²=(λ⁺-z)(λ⁻-z) (so |S|≥d),
     |w+S| ≥ |w| (principal root has Re ≥ 0), (w-S)(w+S)=g/4, λ̇-z=w+g·a; hence
     |factor-1| ≤ |g|(1/(4d²)+|a|/d)  (Pro: C(|a_k||γ_k|²/|k-n| + |γ_k|²/|k-n|²));
   * convolution: KSN-011 with the ℓ² vector b_k = 1/⟨k⟩ gives Σ_{k≠n} ⟨k⟩⁻²/|k-n| ≤ C/⟨n⟩;
   * product error: ‖∏(1+a)-1‖ ≤ exp(Σ‖a‖)-1 ≤ s·exp(s) (Mathlib Finset.norm_prod_one_add_sub_one_le, passed to
     the unconditional limit), with multipliability from Mathlib multipliable_one_add_of_summable.
   Deviation (recorded in KSN013_ROUTE.md): Pro splits large/small k and exceptional n; the single estimate above holds
   for every k ≠ n and every n, so no split is needed. Same mathematical argument otherwise. -/
set_option autoImplicit false

open Set Filter Topology Metric
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.KSN
noncomputable section

/-- Infinite product error from absolute summability (unconditional product). -/
theorem ksn013_tprod_error {ι : Type*} (a : ι → ℂ) (ha : Summable fun i => ‖a i‖) :
    Multipliable (fun i => 1 + a i) ∧
      ‖(∏' i, (1 + a i)) - 1‖ ≤ Real.exp (∑' i, ‖a i‖) - 1 := by
  have hm : Multipliable (fun i => 1 + a i) := multipliable_one_add_of_summable ha
  refine ⟨hm, ?_⟩
  have h1 : Tendsto (fun s : Finset ι => ∏ i ∈ s, (1 + a i)) atTop (𝓝 (∏' i, (1 + a i))) :=
    hm.hasProd
  have h2 : Tendsto (fun s : Finset ι => ‖∏ i ∈ s, (1 + a i) - 1‖) atTop
      (𝓝 ‖(∏' i, (1 + a i)) - 1‖) := (h1.sub_const 1).norm
  refine le_of_tendsto' h2 (fun s => ?_)
  refine (s.norm_prod_one_add_sub_one_le a).trans ?_
  have hs : ∑ i ∈ s, ‖a i‖ ≤ ∑' i, ‖a i‖ := ha.sum_le_tsum s (fun i _ => norm_nonneg _)
  linarith [Real.exp_le_exp.mpr hs]

theorem ksn013_exp_sub_one_le (s : ℝ) : Real.exp s - 1 ≤ s * Real.exp s := by
  have h := Real.add_one_le_exp (-s)
  have he : Real.exp (-s) * Real.exp s = 1 := by rw [← Real.exp_add]; simp
  have h2 := mul_le_mul_of_nonneg_right h (Real.exp_pos s).le
  nlinarith

/-- The standard-root factor estimate (scalar). -/
theorem ksn013_factor_bound (lp lm ld z a : ℂ) (d : ℝ) (hd : 0 < d)
    (hp : d ≤ ‖lp - z‖) (hm : d ≤ ‖lm - z‖) (ht : d ≤ ‖(lp + lm) / 2 - z‖)
    (hld : ld - (lp + lm) / 2 = (lp - lm) ^ 2 * a) :
    stdRoot38 ((lp + lm) / 2) ((lp - lm) ^ 2) z ≠ 0 ∧
    ‖(ld - z) / stdRoot38 ((lp + lm) / 2) ((lp - lm) ^ 2) z - 1‖ ≤
      ‖(lp - lm) ^ 2‖ * (1 / (4 * d ^ 2) + ‖a‖ / d) := by
  have hw0 : (lp + lm) / 2 - z ≠ 0 := by
    intro h; rw [h, norm_zero] at ht; linarith
  have hsq := stdRoot_sq_of_ne38 (g2 := (lp - lm) ^ 2) hw0
  have hSre : stdRoot38 ((lp + lm) / 2) ((lp - lm) ^ 2) z =
      ((lp + lm) / 2 - z) * Complex.sqrt (1 - ((lp - lm) ^ 2 / 4) / ((lp + lm) / 2 - z) ^ 2) := rfl
  have hq : 0 ≤ (Complex.sqrt (1 - ((lp - lm) ^ 2 / 4) / ((lp + lm) / 2 - z) ^ 2)).re :=
    Lib.re_sqrt_nonneg _
  set S := stdRoot38 ((lp + lm) / 2) ((lp - lm) ^ 2) z with hSdef
  set q := Complex.sqrt (1 - ((lp - lm) ^ 2 / 4) / ((lp + lm) / 2 - z) ^ 2) with hqdef
  set w := (lp + lm) / 2 - z with hwdef
  set g := (lp - lm) ^ 2 with hgdef
  have hSS : S ^ 2 = (lp - z) * (lm - z) := by rw [hsq, hwdef, hgdef]; ring
  have h1q : 1 ≤ ‖1 + q‖ := by
    have hr : (1 + q).re = 1 + q.re := by simp
    have := Complex.re_le_norm (1 + q)
    linarith
  have hwS : ‖w‖ ≤ ‖w + S‖ := by
    rw [hSre, show w + w * q = w * (1 + q) by ring, norm_mul]
    exact le_mul_of_one_le_right (norm_nonneg _) h1q
  have hdiff : (w - S) * (w + S) = g / 4 := by
    have h : (w - S) * (w + S) = w ^ 2 - S ^ 2 := by ring
    rw [h, hsq]; ring
  have hSd : d ≤ ‖S‖ := by
    have h2 : ‖S‖ ^ 2 = ‖lp - z‖ * ‖lm - z‖ := by rw [← norm_pow, hSS, norm_mul]
    have h3 : d * d ≤ ‖lp - z‖ * ‖lm - z‖ := mul_le_mul hp hm hd.le (norm_nonneg _)
    by_contra hcon
    push_neg at hcon
    have h4 : ‖S‖ * ‖S‖ < d * d := mul_self_lt_mul_self (norm_nonneg _) hcon
    nlinarith
  have hS0 : S ≠ 0 := by
    intro h; rw [h, norm_zero] at hSd; linarith
  refine ⟨hS0, ?_⟩
  have hwSpos : d ≤ ‖w + S‖ := ht.trans hwS
  have hwmS : ‖w - S‖ ≤ ‖g‖ / (4 * d) := by
    have hne : w + S ≠ 0 := by
      intro h; rw [h, norm_zero] at hwSpos; linarith
    have he : w - S = (g / 4) / (w + S) := by rw [eq_div_iff hne, hdiff]
    have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
    rw [he, norm_div, norm_div, h4, div_div]
    gcongr
  have hld' : ld - z = w + g * a := by
    rw [hwdef, hgdef]; linear_combination hld
  rw [div_sub_one hS0, hld', show w + g * a - S = (w - S) + g * a by ring, norm_div]
  have hnum : ‖(w - S) + g * a‖ ≤ ‖g‖ / (4 * d) + ‖g‖ * ‖a‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    linarith
  calc ‖(w - S) + g * a‖ / ‖S‖ ≤ (‖g‖ / (4 * d) + ‖g‖ * ‖a‖) / d := by
        gcongr
    _ = ‖g‖ * (1 / (4 * d ^ 2) + ‖a‖ / d) := by field_simp

/-- Separation of the closed nth disc from the open kth disc of one common geometry. -/
theorem ksn013_sep (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (J : ℕ) (hg : IsolatingGeometry38 C R c J)
    {k n : ℤ} (hkn : k ≠ n) {p z : ℂ} (hp : p ∈ ball (C k) (R k))
    (hz : z ∈ closedBall (C n) (R n)) :
    c⁻¹ * |((k - n : ℤ) : ℝ)| ≤ ‖p - z‖ := by
  have hRn : 0 < R n := (hg.1 n).1
  have hlow := (hg.2.2.2.1 k n hkn).1
  have hcl : closedBall (C n) (R n) ⊆ {w | c⁻¹ * |((k - n : ℤ) : ℝ)| ≤ dist p w} := by
    rw [← closure_ball (C n) hRn.ne']
    apply closure_minimal
    · intro w hw
      exact hlow.trans (ballDistance38_le_pair _ _ _ _ hp hw)
    · exact isClosed_le continuous_const (continuous_const.dist continuous_id)
  have h := hcl hz
  simpa only [mem_setOf_eq, dist_eq_norm] using h

theorem ksn013_one_le_abs {k n : ℤ} (hkn : k ≠ n) : (1 : ℝ) ≤ |((k - n : ℤ) : ℝ)| := by
  rw [← Int.cast_abs]
  exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hkn)

/-- The ℓ² vector `k ↦ 1/⟨k⟩` used with KSN-011. -/
theorem ksn013_invBracket_mem :
    Memℓp (fun k : ℤ => (((japaneseBracket k)⁻¹ : ℝ) : ℂ)) 2 := by
  have hp : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  rw [memℓp_gen_iff hp]
  refine NlsGge.Atomic.KSN011.summable_inv_br_sq.congr (fun k => ?_)
  have hb := NlsGge.Atomic.KSN011.br_pos k
  rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hb.le)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, inv_pow, one_div]

def ksn013InvBracket : lp (fun _ : ℤ => ℂ) 2 :=
  ⟨fun k : ℤ => (((japaneseBracket k)⁻¹ : ℝ) : ℂ), ksn013_invBracket_mem⟩

theorem ksn013_invBracket_apply (k : ℤ) :
    ‖ksn013InvBracket k‖ = (japaneseBracket k)⁻¹ := by
  change ‖(((japaneseBracket k)⁻¹ : ℝ) : ℂ)‖ = _
  rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (NlsGge.Atomic.KSN011.br_pos k).le)]

/-- One term of the omitted product, for one common geometry. -/
theorem ksn013_term_bound (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (J : ℕ) (hg : IsolatingGeometry38 C R c J)
    (Aa Γ : ℝ) (φ : PotPair) (hφ : φ ∈ gkW) (hsp : IsolatingSpectral38 φ C R)
    (ha : ∀ k, ‖a5CriticalA38 k φ‖ ≤ Aa) (hΓ : ∀ k, japaneseBracket k ^ 2 * ‖gamma2 φ k‖ ≤ Γ)
    (n : ℤ) (z : ℂ) (hz : z ∈ closedBall (C n) (R n)) (k : ℤ) (hkn : k ≠ n) :
    stdRoot38 (tauN φ k) (gamma2 φ k) z ≠ 0 ∧
    ‖criticalOmittedFactor n k φ z - 1‖ ≤
      Γ * (c ^ 2 / 4 + Aa * c) *
        (‖ksn013InvBracket k‖ / (japaneseBracket k * |(k : ℝ) - (n : ℝ)|)) := by
  have hc : 1 ≤ c := hg.2.2.1
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc
  have hD := ksn013_one_le_abs hkn
  set D := |((k - n : ℤ) : ℝ)| with hDdef
  have hd : 0 < c⁻¹ * D := mul_pos (inv_pos.mpr hc0) (by linarith)
  have hD0 : D ≠ 0 := (lt_of_lt_of_le one_pos hD).ne'
  have hc0' : c ≠ 0 := hc0.ne'
  have hseg := (hsp.1 k).1
  have hlp : lamPlus φ k ∈ ball (C k) (R k) := hseg (right_mem_segment ℝ _ _)
  have hlm : lamMinus φ k ∈ ball (C k) (R k) := hseg (left_mem_segment ℝ _ _)
  have hmid : (lamPlus φ k + lamMinus φ k) / 2 ∈ ball (C k) (R k) := by
    apply hseg
    rw [add_comm]
    exact stdRoot_midpoint_mem38 _ _
  have hτ := tauN_value38 φ hφ k
  have hγ := gamma2_value38 φ hφ k
  have hid := a5CriticalA_identity38 k φ hφ
  rw [hτ, hγ] at hid
  obtain ⟨hne, hb⟩ := ksn013_factor_bound (lamPlus φ k) (lamMinus φ k) (lamDot φ k) z
    (a5CriticalA38 k φ) (c⁻¹ * D) hd (ksn013_sep C R c J hg hkn hlp hz)
    (ksn013_sep C R c J hg hkn hlm hz) (ksn013_sep C R c J hg hkn hmid hz) hid
  rw [hτ, hγ]
  refine ⟨hne, ?_⟩
  have hfac : criticalOmittedFactor n k φ z =
      (lamDot φ k - z) / stdRoot38 ((lamPlus φ k + lamMinus φ k) / 2)
        ((lamPlus φ k - lamMinus φ k) ^ 2) z := by
    rw [criticalOmittedFactor, if_neg hkn, hτ, hγ]
  rw [hfac]
  refine hb.trans ?_
  have hjb := NlsGge.Atomic.KSN011.br_pos k
  have hkn' : |(k : ℝ) - (n : ℝ)| = D := by rw [hDdef]; push_cast; rfl
  rw [ksn013_invBracket_apply, hkn']
  have hg0 : ‖(lamPlus φ k - lamMinus φ k) ^ 2‖ ≤ Γ / japaneseBracket k ^ 2 := by
    rw [le_div_iff₀ (by positivity), mul_comm]
    have := hΓ k
    rwa [hγ] at this
  have hA : ‖a5CriticalA38 k φ‖ ≤ Aa := ha k
  have hAa : 0 ≤ Aa := (norm_nonneg _).trans hA
  have hinner : 1 / (4 * (c⁻¹ * D) ^ 2) + ‖a5CriticalA38 k φ‖ / (c⁻¹ * D) ≤
      (c ^ 2 / 4 + Aa * c) / D := by
    have e1 : 1 / (4 * (c⁻¹ * D) ^ 2) = c ^ 2 / 4 / D ^ 2 := by field_simp
    have e2 : ‖a5CriticalA38 k φ‖ / (c⁻¹ * D) = ‖a5CriticalA38 k φ‖ * c / D := by field_simp
    rw [e1, e2]
    have h1 : c ^ 2 / 4 / D ^ 2 ≤ c ^ 2 / 4 / D := by
      apply div_le_div_of_nonneg_left (by positivity) (by linarith)
      nlinarith
    have h2 : ‖a5CriticalA38 k φ‖ * c / D ≤ Aa * c / D := by gcongr
    rw [add_div]
    linarith
  have hin0 : 0 ≤ 1 / (4 * (c⁻¹ * D) ^ 2) + ‖a5CriticalA38 k φ‖ / (c⁻¹ * D) := by positivity
  have hΓ0 : 0 ≤ Γ := le_trans (by positivity) (hΓ k)
  calc ‖(lamPlus φ k - lamMinus φ k) ^ 2‖ *
        (1 / (4 * (c⁻¹ * D) ^ 2) + ‖a5CriticalA38 k φ‖ / (c⁻¹ * D))
      ≤ Γ / japaneseBracket k ^ 2 * ((c ^ 2 / 4 + Aa * c) / D) :=
        mul_le_mul hg0 hinner hin0 (by positivity)
    _ = Γ * (c ^ 2 / 4 + Aa * c) * ((japaneseBracket k)⁻¹ / (japaneseBracket k * D)) := by
        field_simp

/-- The corrected KSN-013 disc estimate for one common geometry (PotPair level). -/
theorem ksn013_disc_estimate (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (J : ℕ)
    (hg : IsolatingGeometry38 C R c J) (Aa Γ : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ φ : PotPair, φ ∈ gkW → IsolatingSpectral38 φ C R →
      (∀ k, ‖a5CriticalA38 k φ‖ ≤ Aa) → (∀ k, japaneseBracket k ^ 2 * ‖gamma2 φ k‖ ≤ Γ) →
      ∀ n : ℤ, ∀ z ∈ closedBall (C n) (R n),
        Multipliable (fun k : ℤ => criticalOmittedFactor n k φ z) ∧
        (∀ k : ℤ, k ≠ n → stdRoot38 (tauN φ k) (gamma2 φ k) z ≠ 0) ∧
        ‖criticalOmittedProduct n φ z - 1‖ ≤ A / japaneseBracket n := by
  obtain ⟨C0, hC0⟩ := NlsGge.Atomic.KSN011.ksn011_statement
  set K : ℝ := c ^ 2 / 4 + max Aa 0 * c with hK
  set T : ℝ := max Γ 0 * K * max (C0 * ‖ksn013InvBracket‖) 0 with hT
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hg.2.2.1
  have hK0 : 0 ≤ K := by positivity
  have hT0 : 0 ≤ T := by positivity
  refine ⟨T * Real.exp T, by positivity, ?_⟩
  intro φ hφ hsp ha hΓ n z hz
  have ha' : ∀ k, ‖a5CriticalA38 k φ‖ ≤ max Aa 0 := fun k => (ha k).trans (le_max_left _ _)
  have hΓ' : ∀ k, japaneseBracket k ^ 2 * ‖gamma2 φ k‖ ≤ max Γ 0 :=
    fun k => (hΓ k).trans (le_max_left _ _)
  set u : ℤ → ℝ := fun k => if k = n then (0 : ℝ) else
    ‖ksn013InvBracket k‖ / (japaneseBracket k * |(k : ℝ) - (n : ℝ)|) with hu
  obtain ⟨hus, hutsum⟩ := hC0 ksn013InvBracket n
  set f : ℤ → ℂ := fun k => criticalOmittedFactor n k φ z - 1 with hf
  have hfu : ∀ k, ‖f k‖ ≤ max Γ 0 * K * u k := by
    intro k
    by_cases hkn : k = n
    · simp [hf, hu, hkn, criticalOmittedFactor]
    · have := (ksn013_term_bound C R c J hg (max Aa 0) (max Γ 0) φ hφ hsp ha' hΓ' n z hz k hkn).2
      simpa [hf, hu, hkn, hK] using this
  have hfs : Summable (fun k => ‖f k‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hfu (hus.mul_left _)
  have hnv : ∀ k : ℤ, k ≠ n → stdRoot38 (tauN φ k) (gamma2 φ k) z ≠ 0 := fun k hkn =>
    (ksn013_term_bound C R c J hg (max Aa 0) (max Γ 0) φ hφ hsp ha' hΓ' n z hz k hkn).1
  obtain ⟨hmul, hprod⟩ := ksn013_tprod_error f hfs
  have hfun : (fun k : ℤ => 1 + f k) = fun k => criticalOmittedFactor n k φ z := by
    funext k; simp [hf]
  rw [hfun] at hmul hprod
  refine ⟨hmul, hnv, ?_⟩
  have hjn := NlsGge.Atomic.KSN011.br_pos n
  have hjn1 : 1 ≤ japaneseBracket n := by
    unfold japaneseBracket
    have h1 : (1 : ℝ) ≤ 1 + (n : ℝ) ^ 2 := by nlinarith [sq_nonneg (n : ℝ)]
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (1 + (n : ℝ) ^ 2) := Real.sqrt_le_sqrt h1
  have hsum_le : ∑' k, ‖f k‖ ≤ T / japaneseBracket n := by
    have h1 : ∑' k, ‖f k‖ ≤ ∑' k, max Γ 0 * K * u k :=
      hfs.tsum_le_tsum hfu (hus.mul_left _)
    rw [tsum_mul_left] at h1
    have h2 : ∑' k, u k ≤ max (C0 * ‖ksn013InvBracket‖) 0 / japaneseBracket n := by
      rw [le_div_iff₀ hjn, mul_comm]
      exact hutsum.trans (le_max_left _ _)
    calc ∑' k, ‖f k‖ ≤ max Γ 0 * K * ∑' k, u k := h1
      _ ≤ max Γ 0 * K * (max (C0 * ‖ksn013InvBracket‖) 0 / japaneseBracket n) := by gcongr
      _ = T / japaneseBracket n := by rw [hT]; ring
  have hs0 : 0 ≤ ∑' k, ‖f k‖ := tsum_nonneg (fun k => norm_nonneg _)
  have hsT : ∑' k, ‖f k‖ ≤ T := hsum_le.trans (div_le_self hT0 hjn1)
  calc ‖criticalOmittedProduct n φ z - 1‖ = ‖(∏' k, criticalOmittedFactor n k φ z) - 1‖ := rfl
    _ ≤ Real.exp (∑' k, ‖f k‖) - 1 := hprod
    _ ≤ (∑' k, ‖f k‖) * Real.exp (∑' k, ‖f k‖) := ksn013_exp_sub_one_le _
    _ ≤ (T / japaneseBracket n) * Real.exp T := by
        gcongr
    _ = T * Real.exp T / japaneseBracket n := by ring

end
end NlsGge.ThirdConsultation.KSN
