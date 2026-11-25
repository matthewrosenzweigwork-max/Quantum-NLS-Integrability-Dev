import Mathlib
import NlsGge.ThirdConsultation.G3.G3026Host
import NlsGge.ThirdConsultation.G3.G3028Host
import NlsGge.Atomic.G3.G3011
import Armstrong.Work.RawBetaSum
import Armstrong.Work.RawBetaSumSpectralMass

/- G3-026 / G3-027 SUPPORT (proof development, AUTHOR; not semantically reviewed by its author).
   Target NlsGge/ThirdConsultation/G3/G3026Support.lean, namespace NlsGge.GKDefinitionDesign.
   Shared lemmas for G3_026 and G3_027 (no design head is stated here):
   * `hasSum_offDiagonalBeta_betaSum`: the bridge between the subtype sum over {m // m ≠ n} that defines `betaSum`
     (`actualPhysicalLocalFamily.beta_spec`) and HasSum over ℤ of `offDiagonalBeta n · φ` (diagonal value 0, gk151BetaAmbient_diag38;
     off-diagonal values gk151BetaAmbient_eq_source38).  Summability is proved from beta_spec before any tsum identity is used.
   * `betaLocalData`: neighbourhood U = Winverse ∩ sourceBetaW with Winverse from the landed G3_011, local ℓ² bound from
     `gk151BetaMass_local_l2_38` (Armstrong.Work.RawBetaSumSpectralMass, X-006 closure line 86).
   * Cauchy-Schwarz row bounds (`Lib.c3_cs`, `Lib.cs_tsum`), the tail version, tail-to-zero, and the identity
     `a - betaPartialSum n R φ = ∑' m, if R < |m| then offDiagonalBeta n m φ else 0` for HasSum.
   Imports: G3026Host (fixedIndexReciprocalTail, betaPartialSum), G3028Host (proof development's host of spectralNorm), landed G3011, X-006-closure Armstrong.Work modules.
   No Armstrong.Frozen/REVIEW_ONLY/DRAFT module is imported directly (decisions 8/8a/8c). -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem offDiagonalBeta_diag (n : ℤ) (φ : PotPair) : offDiagonalBeta n n φ = 0 :=
  congrFun (gk151BetaAmbient_diag38 sourceW sourceFamily.W_open
    sourceFamily.W_real sourceFamily.W_gk sourceF sourceFamily.F_analytic
    sourceFamily.F_zero sourceFamily.F_period n) φ

theorem hasSum_offDiagonalBeta_betaSum (n : ℤ) (φ : PotPair) (hφ : φ ∈ sourceBetaW) :
    HasSum (fun m : ℤ => offDiagonalBeta n m φ) (betaSum n φ) := by
  have hφW : φ ∈ sourceW := sourceFamily.V_W hφ
  obtain ⟨hsum, hbeta⟩ := sourceFamily.beta_spec n ⟨φ, hφW⟩ hφ
  have hs := hsum.of_norm
  have e : (fun m : P2Index38 n => offDiagonalBeta n m.1 φ) =
      fun m : P2Index38 n =>
        gkSourceBeta38 sourceFamily.W sourceFamily.W_open sourceFamily.W_real
          sourceFamily.W_gk sourceFamily.F sourceFamily.F_analytic sourceFamily.F_zero
          sourceFamily.F_period n m.1 m.2 ⟨φ, hφW⟩ :=
    funext fun m =>
      gk151BetaAmbient_eq_source38 sourceW sourceFamily.W_open sourceFamily.W_real
        sourceFamily.W_gk sourceF sourceFamily.F_analytic sourceFamily.F_zero
        sourceFamily.F_period n m.1 m.2 ⟨φ, hφW⟩
  have key : HasSum (fun m : P2Index38 n => offDiagonalBeta n m.1 φ) (betaSum n φ) := by
    rw [e]
    have hb : betaSum n φ = ∑' m : P2Index38 n,
        gkSourceBeta38 sourceFamily.W sourceFamily.W_open sourceFamily.W_real
          sourceFamily.W_gk sourceFamily.F sourceFamily.F_analytic sourceFamily.F_zero
          sourceFamily.F_period n m.1 m.2 ⟨φ, hφW⟩ := hbeta
    rw [hb]
    exact hs.hasSum
  have hzero : ∀ x : ℤ, x ∉ Set.range (Subtype.val : P2Index38 n → ℤ) →
      offDiagonalBeta n x φ = 0 := by
    intro x hx
    have hxn : x = n := by
      by_contra h
      exact hx ⟨⟨x, h⟩, rfl⟩
    rw [hxn]
    exact offDiagonalBeta_diag n φ
  exact (Subtype.val_injective.hasSum_iff hzero).mp key

theorem betaLocalData :
    ∃ U : Set PotPair, IsOpen U ∧ range realSlice ⊆ U ∧ U ⊆ sourceBetaW ∧
      ∀ φ0 ∈ U, ∃ V : Set PotPair, ∃ C M : ℝ,
        IsOpen V ∧ φ0 ∈ V ∧ V ⊆ U ∧ 0 < C ∧ 0 ≤ M ∧
        ∀ φ ∈ V,
          Summable (fun m : ℤ => ‖gk151BetaMass38 φ m‖^2) ∧ spectralNorm φ ≤ M ∧
          ∀ n m : ℤ,
            ‖offDiagonalBeta n m φ‖ ≤ C*‖gk151BetaMass38 φ m‖*Lib.c3w n m := by
  obtain ⟨Wi, hWiO, hWiR, hWiW, hloc⟩ := G3_011
  refine ⟨Wi ∩ sourceBetaW, hWiO.inter sourceFamily.V_open,
    fun x hx => ⟨hWiR hx, sourceFamily.V_real hx⟩, inter_subset_right, ?_⟩
  intro φ0 hφ0
  obtain ⟨V1, C, hV1o, hφ0V1, hV1Wi, hC, hb⟩ := hloc φ0 hφ0.1
  obtain ⟨U2, hU2, _hU2gk, M0, hM0, hmass⟩ :=
    gk151BetaMass_local_l2_38 φ0 (sourceFamily.W_gk (hWiW hφ0.1))
  refine ⟨V1 ∩ interior U2 ∩ sourceBetaW, C, Real.sqrt M0,
    (hV1o.inter isOpen_interior).inter sourceFamily.V_open,
    ⟨⟨hφ0V1, mem_interior_iff_mem_nhds.mpr hU2⟩, hφ0.2⟩,
    fun x hx => ⟨hV1Wi hx.1.1, hx.2⟩, hC, Real.sqrt_nonneg _, ?_⟩
  intro φ hφ
  obtain ⟨hsm, hle⟩ := hmass φ (interior_subset hφ.1.2)
  refine ⟨hsm, ?_, fun n m => hb φ hφ.1.1 n m⟩
  exact Real.sqrt_le_sqrt hle

theorem row_bounds {C M : ℝ} (hC : 0 < C) (φ : PotPair)
    (hs : Summable (fun m : ℤ => ‖gk151BetaMass38 φ m‖^2)) (hM : spectralNorm φ ≤ M)
    (hb : ∀ n m : ℤ, ‖offDiagonalBeta n m φ‖ ≤ C*‖gk151BetaMass38 φ m‖*Lib.c3w n m)
    (n : ℤ) :
    Summable (fun m : ℤ => ‖offDiagonalBeta n m φ‖) ∧
    (∑' m : ℤ, ‖offDiagonalBeta n m φ‖) ≤ C*Real.sqrt Lib.invSqSum*spectralNorm φ ∧
    (∑' m : ℤ, ‖offDiagonalBeta n m φ‖) ≤ C*Real.sqrt Lib.invSqSum*M := by
  obtain ⟨h1, h2⟩ := Lib.c3_cs (a := gk151BetaMass38 φ) hs n
  have hb' : ∀ m : ℤ, ‖offDiagonalBeta n m φ‖ ≤
      C * (‖gk151BetaMass38 φ m‖ * Lib.c3w n m) := fun m => by
    have := hb n m
    rwa [mul_assoc] at this
  have hsum : Summable (fun m : ℤ => ‖offDiagonalBeta n m φ‖) :=
    (h1.mul_left C).of_nonneg_of_le (fun _ => norm_nonneg _) hb'
  have htsum : (∑' m : ℤ, ‖offDiagonalBeta n m φ‖) ≤
      C * Real.sqrt Lib.invSqSum * spectralNorm φ := by
    calc (∑' m : ℤ, ‖offDiagonalBeta n m φ‖)
        ≤ ∑' m : ℤ, C * (‖gk151BetaMass38 φ m‖ * Lib.c3w n m) :=
          hsum.tsum_le_tsum hb' (h1.mul_left C)
      _ = C * ∑' m : ℤ, ‖gk151BetaMass38 φ m‖ * Lib.c3w n m := tsum_mul_left
      _ ≤ C * (Real.sqrt (∑' m : ℤ, ‖gk151BetaMass38 φ m‖ ^ 2) * Real.sqrt Lib.invSqSum) :=
          mul_le_mul_of_nonneg_left h2 hC.le
      _ = C * Real.sqrt Lib.invSqSum * spectralNorm φ := by
          unfold spectralNorm
          ring
  refine ⟨hsum, htsum, htsum.trans ?_⟩
  exact mul_le_mul_of_nonneg_left hM (mul_nonneg hC.le (Real.sqrt_nonneg _))

theorem tail_bounds {C M : ℝ} (hC : 0 < C) (n : ℤ) (R : ℕ) (φ : PotPair)
    (hs : Summable (fun m : ℤ => ‖gk151BetaMass38 φ m‖^2)) (hM : spectralNorm φ ≤ M)
    (hb : ∀ m : ℤ, ‖offDiagonalBeta n m φ‖ ≤ C*‖gk151BetaMass38 φ m‖*Lib.c3w n m) :
    Summable (fun m : ℤ => if (R : ℝ) < |(m : ℝ)| then ‖offDiagonalBeta n m φ‖ else 0) ∧
    (∑' m : ℤ, if (R : ℝ) < |(m : ℝ)| then ‖offDiagonalBeta n m φ‖ else 0) ≤
      C*M*fixedIndexReciprocalTail n R := by
  set w : ℤ → ℝ := fun m => if (R : ℝ) < |(m : ℝ)| then Lib.c3w n m else 0 with hw
  have hw0 : ∀ m, 0 ≤ w m := fun m => by
    simp only [hw]
    split_ifs
    · exact Lib.c3w_nonneg n m
    · exact le_rfl
  have hw2e : ∀ m, w m ^ 2 = if (R : ℝ) < |(m : ℝ)| then Lib.c3w n m ^ 2 else 0 := fun m => by
    simp only [hw]
    split_ifs <;> simp
  have hw2 : Summable (fun m => w m ^ 2) := by
    refine (Lib.summable_c3w_sq n).of_nonneg_of_le (fun m => sq_nonneg _) (fun m => ?_)
    rw [hw2e]
    split_ifs
    · exact le_rfl
    · positivity
  obtain ⟨h1, h2⟩ := Lib.cs_tsum (f := fun m => ‖gk151BetaMass38 φ m‖) (g := w)
    (fun _ => norm_nonneg _) hw0 hs hw2
  have hb' : ∀ m : ℤ, (if (R : ℝ) < |(m : ℝ)| then ‖offDiagonalBeta n m φ‖ else 0) ≤
      C * (‖gk151BetaMass38 φ m‖ * w m) := fun m => by
    simp only [hw]
    split_ifs
    · have := hb m
      rwa [mul_assoc] at this
    · simp
  have hnn : ∀ m : ℤ, 0 ≤ (if (R : ℝ) < |(m : ℝ)| then ‖offDiagonalBeta n m φ‖ else 0) :=
    fun m => by
      split_ifs
      · exact norm_nonneg _
      · exact le_rfl
  have hsum : Summable (fun m : ℤ => if (R : ℝ) < |(m : ℝ)| then ‖offDiagonalBeta n m φ‖ else 0) :=
    (h1.mul_left C).of_nonneg_of_le hnn hb'
  refine ⟨hsum, ?_⟩
  have hT : Real.sqrt (∑' m, w m ^ 2) = fixedIndexReciprocalTail n R := by
    unfold fixedIndexReciprocalTail
    congr 1
    exact tsum_congr hw2e
  calc (∑' m : ℤ, if (R : ℝ) < |(m : ℝ)| then ‖offDiagonalBeta n m φ‖ else 0)
      ≤ ∑' m : ℤ, C * (‖gk151BetaMass38 φ m‖ * w m) := hsum.tsum_le_tsum hb' (h1.mul_left C)
    _ = C * ∑' m : ℤ, ‖gk151BetaMass38 φ m‖ * w m := tsum_mul_left
    _ ≤ C * (Real.sqrt (∑' m : ℤ, ‖gk151BetaMass38 φ m‖ ^ 2) * Real.sqrt (∑' m, w m ^ 2)) :=
        mul_le_mul_of_nonneg_left h2 hC.le
    _ ≤ C * (M * fixedIndexReciprocalTail n R) := by
        rw [hT]
        refine mul_le_mul_of_nonneg_left ?_ hC.le
        exact mul_le_mul_of_nonneg_right hM (by rw [← hT]; exact Real.sqrt_nonneg _)
    _ = C * M * fixedIndexReciprocalTail n R := by ring

theorem not_mem_Icc_iff (R : ℕ) (m : ℤ) :
    m ∉ Finset.Icc (-(R : ℤ)) (R : ℤ) ↔ (R : ℝ) < |(m : ℝ)| := by
  rw [Finset.mem_Icc, ← not_le, abs_le]
  constructor
  · intro h hle
    apply h
    exact ⟨by exact_mod_cast hle.1, by exact_mod_cast hle.2⟩
  · intro h hle
    apply h
    exact ⟨by exact_mod_cast hle.1, by exact_mod_cast hle.2⟩

theorem tendsto_fixedIndexReciprocalTail (n : ℤ) :
    Tendsto (fixedIndexReciprocalTail n) atTop (𝓝 0) := by
  have h1 := tendsto_tsum_compl_atTop_zero (fun m : ℤ => Lib.c3w n m ^ 2)
  have h2 : Tendsto (fun R : ℕ => Finset.Icc (-(R : ℤ)) (R : ℤ)) atTop atTop := by
    refine tendsto_atTop_finset_of_monotone (fun a b hab => ?_) (fun m => ?_)
    · exact Finset.Icc_subset_Icc (neg_le_neg (by exact_mod_cast hab)) (by exact_mod_cast hab)
    · refine ⟨m.natAbs, ?_⟩
      rw [Finset.mem_Icc]
      constructor <;> omega
  have h3 := h1.comp h2
  have h4 : Tendsto (fun R : ℕ => ∑' m : ℤ,
      if (R : ℝ) < |(m : ℝ)| then Lib.c3w n m ^ 2 else 0) atTop (𝓝 0) := by
    refine h3.congr (fun R => ?_)
    show (∑' b : {x : ℤ // x ∉ Finset.Icc (-(R : ℤ)) (R : ℤ)}, Lib.c3w n b ^ 2) = _
    refine (tsum_subtype {x : ℤ | x ∉ Finset.Icc (-(R : ℤ)) (R : ℤ)}
      (fun m : ℤ => Lib.c3w n m ^ 2)).trans (tsum_congr (fun m => ?_))
    by_cases hm : m ∈ Finset.Icc (-(R : ℤ)) (R : ℤ)
    · have : ¬ ((R : ℝ) < |(m : ℝ)|) := fun h => (not_mem_Icc_iff R m).mpr h hm
      rw [Set.indicator_of_notMem (show m ∉ {x : ℤ | x ∉ Finset.Icc (-(R : ℤ)) (R : ℤ)} from
        fun h => h hm)]
      simp only [this, ↓reduceIte]
    · have := (not_mem_Icc_iff R m).mp hm
      rw [Set.indicator_of_mem (show m ∈ {x : ℤ | x ∉ Finset.Icc (-(R : ℤ)) (R : ℤ)} from hm)]
      simp only [this, ↓reduceIte]
  have h5 := (Real.continuous_sqrt.tendsto 0).comp h4
  rw [Real.sqrt_zero] at h5
  exact h5

theorem sub_betaPartialSum_eq (n : ℤ) (R : ℕ) (φ : PotPair) {a : ℂ}
    (h : HasSum (fun m : ℤ => offDiagonalBeta n m φ) a) :
    a - betaPartialSum n R φ =
      ∑' m : ℤ, if (R : ℝ) < |(m : ℝ)| then offDiagonalBeta n m φ else 0 := by
  have h1 := h.summable.sum_add_tsum_compl (s := Finset.Icc (-(R : ℤ)) (R : ℤ))
  rw [h.tsum_eq] at h1
  have h2 : (∑' x : ↑((Finset.Icc (-(R : ℤ)) (R : ℤ) : Finset ℤ) : Set ℤ)ᶜ,
      offDiagonalBeta n x φ) =
      ∑' m : ℤ, if (R : ℝ) < |(m : ℝ)| then offDiagonalBeta n m φ else 0 := by
    refine (tsum_subtype (((Finset.Icc (-(R : ℤ)) (R : ℤ) : Finset ℤ) : Set ℤ)ᶜ)
      (fun x : ℤ => offDiagonalBeta n x φ)).trans (tsum_congr (fun m => ?_))
    by_cases hm : m ∈ Finset.Icc (-(R : ℤ)) (R : ℤ)
    · have : ¬ ((R : ℝ) < |(m : ℝ)|) := fun h => (not_mem_Icc_iff R m).mpr h hm
      rw [Set.indicator_of_notMem (show m ∉ (((Finset.Icc (-(R : ℤ)) (R : ℤ) : Finset ℤ) : Set ℤ)ᶜ) from
        fun h => h (Finset.mem_coe.mpr hm))]
      simp only [this, ↓reduceIte]
    · have := (not_mem_Icc_iff R m).mp hm
      rw [Set.indicator_of_mem (show m ∈ (((Finset.Icc (-(R : ℤ)) (R : ℤ) : Finset ℤ) : Set ℤ)ᶜ) from
        fun h => hm (Finset.mem_coe.mp h))]
      simp only [this, ↓reduceIte]
  rw [h2] at h1
  unfold betaPartialSum
  rw [← h1]
  ring

end
end NlsGge.GKDefinitionDesign
