import Mathlib
import NlsGge.Atomic.G1.G1062
import NlsGge.ThirdConsultation.G1.NormCalculus
import NlsGge.ThirdConsultation.G1.IBP038Support
import NlsGge.Atomic.G2.G2045SupB1

/- G2-045 support kit G2045SupB2 (proof development, AUTHOR; not reviewed).
   Target NlsGge/Atomic/G2/G2045SupB2.lean, namespace NlsGge.GKDefinitionDesign.
   Sobolev side of the identity theorem: the pair H^N is a complex submodule of PotPair; pairSobolevNorm
   is homogeneous, subadditive, potConj-invariant; Sobolev balls about a potConj-fixed centre are convex,
   potConj-stable and line-open; so g2045b_identity applies to them (g2045b_ball_identity). -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38

namespace NlsGge.GKDefinitionDesign
attribute [local instance] Classical.propDecidable

theorem g2045b_jb_neg (n : ℤ) : japaneseBracket (-n) = japaneseBracket n := by
  simp [japaneseBracket]

theorem g2045b_refl_star (u : PhysicalL2) (n : ℤ) :
    ‖reflectedFourierL2 (star u) n‖ = ‖reflectedFourierL2 u (-n)‖ := by
  have h1 : reflectedFourierL2 (star u) n = fourierSeq38 (star u) n := rfl
  have h2 : reflectedFourierL2 u (-n) = fourierSeq38 u (-n) := rfl
  rw [h1, h2, fourierSeq38_apply, fourierSeq38_apply, norm_neg, norm_neg, physicalFourier_star,
    neg_neg]
  simp

theorem g2045b_psob_star (r : ℝ) (u : PhysicalL2) (hu : physicalSobolev r u) :
    physicalSobolev r (star u) := by
  unfold physicalSobolev SobolevSquareSummable at hu ⊢
  refine ((Equiv.neg ℤ).summable_iff.2 hu).congr (fun n => ?_)
  show Real.rpow (japaneseBracket (-n)) (2 * r) * ‖reflectedFourierL2 u (-n)‖ ^ 2 =
    Real.rpow (japaneseBracket n) (2 * r) * ‖reflectedFourierL2 (star u) n‖ ^ 2
  rw [g2045b_refl_star, g2045b_jb_neg]

theorem g2045b_psn_star (r : ℝ) (u : PhysicalL2) :
    physicalSobolevNorm r (star u) = physicalSobolevNorm r u := by
  unfold physicalSobolevNorm
  congr 1
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr (fun n => ?_)
  simp only [Equiv.neg_apply]
  rw [g2045b_refl_star, g2045b_jb_neg, neg_neg]

theorem g2045b_refl_smul (c : ℂ) (u : PhysicalL2) (n : ℤ) :
    reflectedFourierL2 (c • u) n = c * reflectedFourierL2 u n := by
  rw [map_smul]
  simp

theorem g2045b_psob_smul (r : ℝ) (c : ℂ) (u : PhysicalL2) (hu : physicalSobolev r u) :
    physicalSobolev r (c • u) := by
  unfold physicalSobolev SobolevSquareSummable at hu ⊢
  refine (hu.mul_left (‖c‖ ^ 2)).congr (fun n => ?_)
  rw [g2045b_refl_smul, norm_mul, mul_pow]
  ring

theorem g2045b_psn_smul (r : ℝ) (c : ℂ) (u : PhysicalL2) :
    physicalSobolevNorm r (c • u) = ‖c‖ * physicalSobolevNorm r u := by
  unfold physicalSobolevNorm
  have h : (∑' n : ℤ, Real.rpow (japaneseBracket n) (2 * r) * ‖reflectedFourierL2 (c • u) n‖ ^ 2) =
      ‖c‖ ^ 2 * ∑' n : ℤ, Real.rpow (japaneseBracket n) (2 * r) * ‖reflectedFourierL2 u n‖ ^ 2 := by
    rw [← tsum_mul_left]
    refine tsum_congr (fun n => ?_)
    rw [g2045b_refl_smul, norm_mul, mul_pow]
    ring
  rw [h, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem g2045b_psob_zero (r : ℝ) : physicalSobolev r (0 : PhysicalL2) := by
  unfold physicalSobolev SobolevSquareSummable
  simp

/-- The pair Sobolev space `H^N × H^N` as a complex submodule of `PotPair`. -/
def pairSobolevSub (N : ℕ) : Submodule ℂ PotPair where
  carrier := {φ | pairSobolev (N : ℝ) φ}
  add_mem' := fun {a b} ha hb => ⟨(psn_add N ha.1 hb.1).1, (psn_add N ha.2 hb.2).1⟩
  zero_mem' := ⟨g2045b_psob_zero _, g2045b_psob_zero _⟩
  smul_mem' := fun c φ h => ⟨g2045b_psob_smul _ c _ h.1, g2045b_psob_smul _ c _ h.2⟩

theorem mem_pairSobolevSub (N : ℕ) (φ : PotPair) :
    φ ∈ pairSobolevSub N ↔ pairSobolev (N : ℝ) φ := Iff.rfl

theorem g2045b_pn_nonneg (r : ℝ) (φ : PotPair) : 0 ≤ pairSobolevNorm r φ :=
  Real.sqrt_nonneg _

theorem g2045b_pn_smul (r : ℝ) (c : ℂ) (φ : PotPair) :
    pairSobolevNorm r (c • φ) = ‖c‖ * pairSobolevNorm r φ := by
  unfold pairSobolevNorm
  show Real.sqrt (physicalSobolevNorm r (c • φ.1) ^ 2 + physicalSobolevNorm r (c • φ.2) ^ 2) = _
  rw [g2045b_psn_smul, g2045b_psn_smul]
  have : (‖c‖ * physicalSobolevNorm r φ.1) ^ 2 + (‖c‖ * physicalSobolevNorm r φ.2) ^ 2 =
      ‖c‖ ^ 2 * (physicalSobolevNorm r φ.1 ^ 2 + physicalSobolevNorm r φ.2 ^ 2) := by ring
  rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem g2045b_pn_conj (r : ℝ) (φ : PotPair) :
    pairSobolevNorm r (potConj φ) = pairSobolevNorm r φ := by
  unfold pairSobolevNorm
  show Real.sqrt (physicalSobolevNorm r (star φ.2) ^ 2 + physicalSobolevNorm r (star φ.1) ^ 2) = _
  rw [g2045b_psn_star, g2045b_psn_star, add_comm]

theorem g2045b_pn_add (N : ℕ) {φ ψ : PotPair} (hφ : pairSobolev (N : ℝ) φ)
    (hψ : pairSobolev (N : ℝ) ψ) :
    pairSobolevNorm (N : ℝ) (φ + ψ) ≤ pairSobolevNorm (N : ℝ) φ + pairSobolevNorm (N : ℝ) ψ := by
  obtain ⟨-, h1⟩ := psn_add N hφ.1 hψ.1
  obtain ⟨-, h2⟩ := psn_add N hφ.2 hψ.2
  set a1 := physicalSobolevNorm (N : ℝ) φ.1
  set b1 := physicalSobolevNorm (N : ℝ) φ.2
  set a2 := physicalSobolevNorm (N : ℝ) ψ.1
  set b2 := physicalSobolevNorm (N : ℝ) ψ.2
  have ha1 : 0 ≤ a1 := psn_nonneg N _
  have hb1 : 0 ≤ b1 := psn_nonneg N _
  have ha2 : 0 ≤ a2 := psn_nonneg N _
  have hb2 : 0 ≤ b2 := psn_nonneg N _
  have hp1 : 0 ≤ physicalSobolevNorm (N : ℝ) (φ + ψ).1 := psn_nonneg N _
  have hp2 : 0 ≤ physicalSobolevNorm (N : ℝ) (φ + ψ).2 := psn_nonneg N _
  unfold pairSobolevNorm
  have hX := Real.sq_sqrt (show 0 ≤ a1 ^ 2 + b1 ^ 2 by positivity)
  have hY := Real.sq_sqrt (show 0 ≤ a2 ^ 2 + b2 ^ 2 by positivity)
  set X := Real.sqrt (a1 ^ 2 + b1 ^ 2)
  set Y := Real.sqrt (a2 ^ 2 + b2 ^ 2)
  have hXY : a1 * a2 + b1 * b2 ≤ X * Y := by
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg (a1 * b2 - a2 * b1)]
  have e1 : physicalSobolevNorm (N : ℝ) (φ + ψ).1 ^ 2 ≤ (a1 + a2) ^ 2 :=
    pow_le_pow_left₀ hp1 h1 2
  have e2 : physicalSobolevNorm (N : ℝ) (φ + ψ).2 ^ 2 ≤ (b1 + b2) ^ 2 :=
    pow_le_pow_left₀ hp2 h2 2
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.sqrt_nonneg (a1 ^ 2 + b1 ^ 2), Real.sqrt_nonneg (a2 ^ 2 + b2 ^ 2)]

theorem g2045b_pn_sub (N : ℕ) {φ ψ : PotPair} (hφ : pairSobolev (N : ℝ) φ)
    (hψ : pairSobolev (N : ℝ) ψ) :
    pairSobolevNorm (N : ℝ) (φ - ψ) ≤ pairSobolevNorm (N : ℝ) φ + pairSobolevNorm (N : ℝ) ψ := by
  have h := g2045b_pn_add N hφ ((pairSobolevSub N).smul_mem (-1 : ℂ) hψ)
  have e : φ + (-1 : ℂ) • ψ = φ - ψ := by module
  rw [e, g2045b_pn_smul] at h
  simpa using h

/-- Sobolev ball in `H^N × H^N` about `c`. -/
def g2045bBall (N : ℕ) (c : PotPair) (ρ : ℝ) : Set PotPair :=
  {φ | pairSobolev (N : ℝ) φ ∧ pairSobolevNorm (N : ℝ) (φ - c) < ρ}

theorem g2045bBall_sub (N : ℕ) (c : PotPair) (ρ : ℝ) : g2045bBall N c ρ ⊆ (pairSobolevSub N : Set PotPair) :=
  fun _ h => h.1

theorem g2045bBall_convex (N : ℕ) (c : PotPair) (hc : pairSobolev (N : ℝ) c) (ρ : ℝ) :
    Convex ℝ (g2045bBall N c ρ) := by
  intro x hx y hy θ η hθ hη hθη
  have hη' : η = 1 - θ := by linarith
  subst hη'
  have hxc : x - c ∈ pairSobolevSub N := (pairSobolevSub N).sub_mem hx.1 hc
  have hyc : y - c ∈ pairSobolevSub N := (pairSobolevSub N).sub_mem hy.1 hc
  have e : θ • x + (1 - θ) • y - c = (θ : ℂ) • (x - c) + ((1 - θ : ℝ) : ℂ) • (y - c) := by
    rw [Complex.coe_smul, Complex.coe_smul]
    module
  refine ⟨?_, ?_⟩
  · have := (pairSobolevSub N).add_mem ((pairSobolevSub N).smul_mem (θ : ℂ) hx.1)
      ((pairSobolevSub N).smul_mem ((1 - θ : ℝ) : ℂ) hy.1)
    rw [Complex.coe_smul, Complex.coe_smul] at this
    exact this
  · rw [e]
    have h := g2045b_pn_add N ((pairSobolevSub N).smul_mem (θ : ℂ) hxc)
      ((pairSobolevSub N).smul_mem ((1 - θ : ℝ) : ℂ) hyc)
    rw [g2045b_pn_smul, g2045b_pn_smul] at h
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hθ, abs_of_nonneg hη] at h
    have hx2 := hx.2
    have hy2 := hy.2
    have hpos : 0 < θ * (ρ - pairSobolevNorm (N : ℝ) (x - c)) +
        (1 - θ) * (ρ - pairSobolevNorm (N : ℝ) (y - c)) := by
      rcases hθ.eq_or_lt with h0 | hp
      · subst h0
        simp only [zero_mul, zero_add, sub_zero, one_mul]
        linarith
      · exact add_pos_of_pos_of_nonneg (mul_pos hp (sub_pos.2 hx2))
          (mul_nonneg hη (sub_pos.2 hy2).le)
    nlinarith

theorem g2045bBall_conj (N : ℕ) (c : PotPair) (hcc : potConj c = c) (ρ : ℝ) :
    ∀ φ ∈ g2045bBall N c ρ, potConj φ ∈ g2045bBall N c ρ := by
  intro φ hφ
  refine ⟨⟨g2045b_psob_star _ _ hφ.1.2, g2045b_psob_star _ _ hφ.1.1⟩, ?_⟩
  have e : potConj φ - c = potConj (φ - c) := by
    have h : φ - c = φ + (-1 : ℂ) • c := by module
    rw [h, potConj_add, potConj_smul, hcc]
    simp only [map_neg, map_one]
    module
  rw [e, g2045b_pn_conj]
  exact hφ.2

theorem g2045bBall_open (N : ℕ) (c : PotPair) (hc : pairSobolev (N : ℝ) c) (ρ : ℝ) :
    ∀ x ∈ pairSobolevSub N, ∀ A ∈ pairSobolevSub N,
      IsOpen {s : ℂ | x + s • A ∈ g2045bBall N c ρ} := by
  intro x hx A hA
  set y := x - c with hy
  have hyV : y ∈ pairSobolevSub N := (pairSobolevSub N).sub_mem hx hc
  have hnn := g2045b_pn_nonneg (N : ℝ) A
  have hlip : LipschitzWith ⟨pairSobolevNorm (N : ℝ) A, hnn⟩
      (fun s : ℂ => pairSobolevNorm (N : ℝ) (y + s • A)) := by
    refine LipschitzWith.of_dist_le_mul (fun s s' => ?_)
    rw [Real.dist_eq, dist_eq_norm]
    show |pairSobolevNorm (N : ℝ) (y + s • A) - pairSobolevNorm (N : ℝ) (y + s' • A)| ≤
      pairSobolevNorm (N : ℝ) A * ‖s - s'‖
    have hs : y + s • A ∈ pairSobolevSub N :=
      (pairSobolevSub N).add_mem hyV ((pairSobolevSub N).smul_mem s hA)
    have hs' : y + s' • A ∈ pairSobolevSub N :=
      (pairSobolevSub N).add_mem hyV ((pairSobolevSub N).smul_mem s' hA)
    have h1 := g2045b_pn_sub N hs hs'
    have key : ∀ t t' : ℂ, pairSobolevNorm (N : ℝ) (y + t • A) ≤
        pairSobolevNorm (N : ℝ) (y + t' • A) + ‖t - t'‖ * pairSobolevNorm (N : ℝ) A := by
      intro t t'
      have ht' : y + t' • A ∈ pairSobolevSub N :=
        (pairSobolevSub N).add_mem hyV ((pairSobolevSub N).smul_mem t' hA)
      have h := g2045b_pn_add N ht' ((pairSobolevSub N).smul_mem (t - t') hA)
      rw [g2045b_pn_smul] at h
      have e : y + t' • A + (t - t') • A = y + t • A := by module
      rw [e] at h
      linarith
    have k1 := key s s'
    have k2 := key s' s
    rw [norm_sub_rev] at k2
    rw [abs_le]
    constructor <;> nlinarith
  have hcont : Continuous (fun s : ℂ => pairSobolevNorm (N : ℝ) (y + s • A)) := hlip.continuous
  have hset : {s : ℂ | x + s • A ∈ g2045bBall N c ρ} =
      {s : ℂ | pairSobolevNorm (N : ℝ) (y + s • A) < ρ} := by
    ext s
    have hmem : x + s • A ∈ pairSobolevSub N :=
      (pairSobolevSub N).add_mem hx ((pairSobolevSub N).smul_mem s hA)
    have e : x + s • A - c = y + s • A := by rw [hy]; module
    show (pairSobolev (N : ℝ) (x + s • A) ∧ pairSobolevNorm (N : ℝ) (x + s • A - c) < ρ) ↔ _
    rw [e]
    exact ⟨fun h => h.2, fun h => ⟨hmem, h⟩⟩
  rw [hset]
  exact isOpen_lt hcont continuous_const

/-- Identity theorem on a Sobolev ball about a `potConj`-fixed centre. -/
theorem g2045b_ball_identity (N : ℕ) (c : PotPair) (hc : pairSobolev (N : ℝ) c)
    (hcc : potConj c = c) (ρ : ℝ) (f : PotPair → ℂ)
    (hf : ∀ x ∈ pairSobolevSub N, ∀ A ∈ pairSobolevSub N,
      AnalyticOnNhd ℂ (fun s : ℂ => f (x + s • A)) {s : ℂ | x + s • A ∈ g2045bBall N c ρ})
    (hr : ∀ u : PhysicalL2, realSlice u ∈ g2045bBall N c ρ → f (realSlice u) = 0) :
    ∀ φ ∈ g2045bBall N c ρ, f φ = 0 :=
  g2045b_identity (pairSobolevSub N) (g2045bBall N c ρ) (g2045bBall_convex N c hc ρ)
    (g2045bBall_sub N c ρ) (g2045bBall_conj N c hcc ρ) (g2045bBall_open N c hc ρ) f hf hr

end NlsGge.GKDefinitionDesign
end
