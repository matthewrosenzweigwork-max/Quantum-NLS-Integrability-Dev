import NlsGge.Spectral.ActualGapActionAllNE02_38
import NlsGge.Spectral.ActualQuasimomentumContinuityE02_38
import NlsGge.Spectral.ActualPhysicalMonodromyCouplingContinuity36V2
import NlsGge.Spectral.ActualCouplingSobolevUniformBox38
import NlsGge.Spectral.ActualQuasimomentumMonotoneE02_38
import NlsGge.Batch37.ActualPhysicalVacuumInteractionHalfTrace37V2

/-!
# Mo2 (part A): from zeros of `Δh² - 1` to the labelled gap

Piece Mo2 of the E01 plan (`campaign/E01_PLAN.md` §6.12): Molnár, arXiv:1403.1369, Theorem 5.

Molnár's last step of the proof of Theorem 5 ("a standard counting argument": the two roots of
`det S_n` in `D_n` are the periodic eigenvalues `λ_n^±`) is replaced here by a homotopy argument
in the coupling `τ ∈ [0,1]` (`u ↦ τ u`), which uses only facts already in the repository:

* the labelled gap `g_n = {p = nπ}` is the level set of the nondecreasing boundary real part
  `p = Re k(· + i0)` (`actualGapLevelSet_eq_Icc_E02_38`) with `Δh(λ_n^±) = cos nπ`
  (`actualGapEndpoint_halfTrace_all_E02_38`);
* `τ ↦ Δh(τu)(x)` is continuous on `[0,1]` (`actualPhysicalUnitHalfTrace_coupling_continuousOn36V2`);
* `τ ↦ p_{τu}(x)` is continuous at every `τ` with `Δh(τu)(x)² ≠ 1`
  (`actualQuasimomentumBoundary_holder_in_u_E02_38`).

**Input** (`MolnarZeroLoc38`, Molnár Lemmas 5-10, proved in part B/C): for every potential `v` with
Molnár norm `‖φ(v)‖₁² ≤ R2` and `⟨n⟩ ≥ 8 R2`, every real zero `x` of `Δh(v)² - 1` with
`|x - nπ| ≤ π/2` lies in `|x - nπ| ≤ R2/⟨n⟩ + √2 √R2/⟨2n⟩`.

**Output** (`gap_localization_of_zeroLoc38`): the whole closed gap `[λ_n^-, λ_n^+]` lies in that
interval.  Argument: the radius is `< π/2`, so the strip boundary points `b_n = (n+½)π`,
`b_{n-1} = (n-½)π` are never zeros along the path `τu`; hence `|Δh(τu)(b)| < 1` for all `τ`
(intermediate value theorem from `Δh(0)(b) = cos b = 0`), so `b` is in a band, `p_{τu}(b) ∉ πℤ`,
and `p_{τu}(b)` (continuous, equal to `b` at `τ = 0`) stays in `(nπ, (n+1)π)`, resp.
`((n-1)π, nπ)`.  By monotonicity of `p` the whole gap `{p = nπ}` is between `b_{n-1}` and `b_n`;
its endpoints are zeros of `Δh² - 1`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set
open scoped Topology

namespace NlsGge.GK38

open NlsGge.SpectralFoundations NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

noncomputable section

/-- Molnár's bracket `⟨x⟩ = 1 + |x|` (arXiv:1403.1369, §1, after (1)). -/
def molnarBracket38 (n : ℤ) : ℝ := 1 + |(n : ℝ)|

/-- The radius of Molnár's Theorem 5: `‖φ‖₁²/⟨n⟩ + √2 ‖φ‖₁/⟨2n⟩` with `R2 = ‖φ‖₁²`. -/
def molnarRadius38 (R2 : ℝ) (n : ℤ) : ℝ :=
  R2 / molnarBracket38 n + Real.sqrt 2 * Real.sqrt R2 / molnarBracket38 (2 * n)

/-- Molnár Lemmas 5-10 for the actual half trace of `v`: real zeros of `Δh(v)² - 1` in the strip
`|x - nπ| ≤ π/2`, `⟨n⟩ ≥ 8 R2`, lie in the disc of radius `molnarRadius38 R2 n` around `nπ`. -/
def MolnarZeroLoc38 (v : PhysicalL2) (R2 : ℝ) : Prop :=
  ∀ n : ℤ, 8 * R2 ≤ molnarBracket38 n → ∀ x : ℝ, |x - n * Real.pi| ≤ Real.pi / 2 →
    actualPhysicalUnitHalfTrace32 v (x : ℂ) ^ 2 = 1 → |x - n * Real.pi| ≤ molnarRadius38 R2 n

theorem molnarBracket_pos38 (n : ℤ) : 0 < molnarBracket38 n := by
  unfold molnarBracket38; positivity

theorem one_le_molnarBracket38 (n : ℤ) : 1 ≤ molnarBracket38 n := by
  unfold molnarBracket38; linarith [abs_nonneg (n : ℝ)]

theorem molnarBracket_le_two_mul38 (n : ℤ) : molnarBracket38 n ≤ molnarBracket38 (2 * n) := by
  unfold molnarBracket38
  push_cast
  rw [abs_mul]
  norm_num
  linarith [abs_nonneg (n : ℝ)]

/-- The radius is smaller than `π/2` in the range `⟨n⟩ ≥ 8 R2`. -/
theorem molnarRadius38_lt (R2 : ℝ) (hR : 0 ≤ R2) (n : ℤ) (hn : 8 * R2 ≤ molnarBracket38 n) :
    molnarRadius38 R2 n < Real.pi / 2 := by
  set N := molnarBracket38 n with hN
  have hN1 : 1 ≤ N := one_le_molnarBracket38 n
  have hN2 : N ≤ molnarBracket38 (2 * n) := molnarBracket_le_two_mul38 n
  have h1 : R2 / N ≤ 1 / 8 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have h2 : Real.sqrt 2 * Real.sqrt R2 / molnarBracket38 (2 * n) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by linarith)]
    have : Real.sqrt 2 * Real.sqrt R2 = Real.sqrt (2 * R2) := by
      rw [Real.sqrt_mul (by norm_num)]
    rw [this]
    have h3 : 2 * R2 ≤ N / 4 := by linarith
    have h4 : Real.sqrt (2 * R2) ≤ Real.sqrt (N / 4) := Real.sqrt_le_sqrt h3
    have h5 : Real.sqrt (N / 4) ≤ N / 2 := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    nlinarith
  have := Real.pi_gt_three
  unfold molnarRadius38
  linarith

/-! ### Zero potential -/

theorem halfTrace_zero38 (x : ℂ) : actualPhysicalUnitHalfTrace32 (0 : PhysicalL2) x = Complex.cos x :=
  actualPhysicalUnitHalfTrace_zeroPotential37V2 x

/-- The quasimomentum of the zero potential is the identity on the upper half plane. -/
theorem quasimomentum_zero_eqOn38 :
    EqOn (actualQuasimomentumE02_38 (0 : PhysicalL2)) id {z : ℂ | 0 < z.im} := by
  have hk := isActualQuasimomentumBranch_actualQuasimomentumE02_38 (0 : PhysicalL2)
  have hid : IsActualQuasimomentumBranchE02_38 (0 : PhysicalL2) id := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact analyticOnNhd_id
    · intro z _; simp [halfTrace_zero38]
    · intro z hz; simpa using hz
    · intro ε hε
      refine ⟨1, one_pos, fun Y _ x => ?_⟩
      simpa using hε
  exact hk.eqOn hid

theorem quasimomentumBoundary_zero38 (x : ℝ) :
    actualQuasimomentumBoundaryE02_38 (0 : PhysicalL2) x = (x : ℂ) := by
  have h1 := tendsto_actualQuasimomentumBoundaryE02_38 (0 : PhysicalL2) x
  have hne : (𝓝[{z : ℂ | 0 < z.im}] (x:ℂ)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (mem_closure_upperHalfPlane_E02_38 (by simp))
  have h2 : Tendsto (actualQuasimomentumE02_38 (0 : PhysicalL2))
      (𝓝[{z : ℂ | 0 < z.im}] (x:ℂ)) (𝓝 (x:ℂ)) := by
    have : Tendsto (id : ℂ → ℂ) (𝓝[{z : ℂ | 0 < z.im}] (x:ℂ)) (𝓝 (x:ℂ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    exact this.congr' (eventually_nhdsWithin_of_forall fun z hz => (quasimomentum_zero_eqOn38 hz).symm)
  exact tendsto_nhds_unique h1 h2

theorem quasimomentumRealPart_zero38 (x : ℝ) :
    actualQuasimomentumRealPartE02_38 (0 : PhysicalL2) x = x := by
  unfold actualQuasimomentumRealPartE02_38
  rw [quasimomentumBoundary_zero38]; simp

/-! ### The coupling path -/

section Path

variable (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u))

theorem coupling_halfTrace_im38 (τ : ℝ) (x : ℝ) :
    (actualPhysicalUnitHalfTrace32 ((τ : ℂ) • u) (x : ℂ)).im = 0 :=
  actualPhysicalUnitHalfTrace32_ofReal_im_E02_38 _ x

theorem sq_eq_one_of_norm_eq_one38 (c : ℂ) (hc : c.im = 0) (h : ‖c‖ = 1) : c ^ 2 = 1 := by
  have hc' : c = (c.re : ℂ) := Complex.ext (by simp) (by simp [hc])
  rw [hc', Complex.norm_real, Real.norm_eq_abs] at h
  rw [hc', ← Complex.ofReal_pow]
  have : c.re ^ 2 = 1 := by rw [← sq_abs, h]; norm_num
  rw [this]; simp

/-- No zero of `Δh(τu)² - 1` at `x` along the path, and `|Δh(0)(x)| < 1`, give a band for all `τ`. -/
theorem band_along_path38 (x : ℝ) (h0 : ‖Complex.cos (x : ℂ)‖ < 1)
    (hnz : ∀ τ ∈ Icc (0:ℝ) 1, actualPhysicalUnitHalfTrace32 ((τ : ℂ) • u) (x : ℂ) ^ 2 ≠ 1) :
    ∀ τ ∈ Icc (0:ℝ) 1, ‖actualPhysicalUnitHalfTrace32 ((τ : ℂ) • u) (x : ℂ)‖ < 1 := by
  have hc : ContinuousOn (fun τ : ℝ => ‖actualPhysicalUnitHalfTrace32 ((τ : ℂ) • u) (x : ℂ)‖)
      (Icc (0:ℝ) 1) :=
    (actualPhysicalUnitHalfTrace_coupling_continuousOn36V2 u (x:ℂ) 0 le_rfl (by simp) (by simp)).norm
  intro τ₁ hτ₁
  by_contra hcon
  replace hcon := not_lt.mp hcon
  have hsub : Icc (0:ℝ) τ₁ ⊆ Icc (0:ℝ) 1 := Icc_subset_Icc_right hτ₁.2
  have h00 : ‖actualPhysicalUnitHalfTrace32 (((0:ℝ) : ℂ) • u) (x : ℂ)‖ < 1 := by
    simpa [halfTrace_zero38] using h0
  obtain ⟨τ, hτ, hτe⟩ := intermediate_value_Icc hτ₁.1 (hc.mono hsub)
    (show (1:ℝ) ∈ Icc _ _ from ⟨h00.le, hcon⟩)
  exact hnz τ (hsub hτ) (sq_eq_one_of_norm_eq_one38 _ (coupling_halfTrace_im38 u τ x) hτe)

/-- On a band point the boundary quasimomentum is real and not in `πℤ`. -/
theorem realPart_not_int38 (v : PhysicalL2) (x : ℝ)
    (h : ‖actualPhysicalUnitHalfTrace32 v (x : ℂ)‖ < 1) (j : ℤ) :
    actualQuasimomentumRealPartE02_38 v x ≠ (j : ℝ) * Real.pi := by
  intro hj
  have hcos := actualQuasimomentumBoundaryE02_38_cos v x
  have him := boundaryLimit_im_E02_38 v x _ (tendsto_actualQuasimomentumBoundaryE02_38 v x)
  have hv : actualGapHeightE02_38 v x = 0 :=
    (actualGapHeightE02_38_eq_zero_iff v x).2 h.le
  have hk : actualQuasimomentumBoundaryE02_38 v x = (((j : ℝ) * Real.pi : ℝ) : ℂ) := by
    apply Complex.ext
    · simpa [actualQuasimomentumRealPartE02_38] using hj
    · simp [him, hv]
  rw [hk, ← Complex.ofReal_cos] at hcos
  have hs := Real.sin_int_mul_pi j
  have hc2 : Real.cos ((j : ℝ) * Real.pi) ^ 2 = 1 := by
    have := Real.sin_sq_add_cos_sq ((j : ℝ) * Real.pi)
    rw [hs] at this; linarith
  have hc1 : |Real.cos ((j : ℝ) * Real.pi)| = 1 := by
    have : |Real.cos ((j : ℝ) * Real.pi)| ^ 2 = 1 := by rw [sq_abs]; exact hc2
    nlinarith [abs_nonneg (Real.cos ((j : ℝ) * Real.pi))]
  rw [← hcos, Complex.norm_real, Real.norm_eq_abs, hc1] at h
  exact lt_irrefl _ h

variable {u}
include hu

theorem realPart_continuousOn38 (x : ℝ)
    (hband : ∀ τ ∈ Icc (0:ℝ) 1, ‖actualPhysicalUnitHalfTrace32 ((τ : ℂ) • u) (x : ℂ)‖ < 1) :
    ContinuousOn (fun τ : ℝ => actualQuasimomentumRealPartE02_38 ((τ : ℂ) • u) x) (Icc 0 1) := by
  intro τ₀ hτ₀
  set B : ℝ := max 1 ‖physicalSobolevL2 1 u hu‖ with hB
  have hB1 : 1 ≤ B := le_max_left _ _
  have hu₀ := sobolevSquareSummable_smul38 (τ₀ : ℂ) u hu
  have hnorm : ∀ τ ∈ Icc (0:ℝ) 1, ∀ hτ : SobolevSquareSummable 1
      (physicalFourier (((τ : ℂ) • u : PhysicalL2) : PhysicalCircle → ℂ)),
      ‖physicalSobolevL2 1 ((τ : ℂ) • u) hτ‖ ≤ B := by
    intro τ hτ hτ'
    rw [physicalSobolevL2_smul_norm38 (τ : ℂ) u hu hτ', Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hτ.1]
    have := le_max_right 1 ‖physicalSobolevL2 1 u hu‖
    nlinarith [norm_nonneg (physicalSobolevL2 1 u hu), hτ.2]
  have hx : actualPhysicalUnitHalfTrace32 ((τ₀ : ℂ) • u) (x : ℂ) ^ 2 ≠ 1 := by
    intro h1
    have h2 := hband τ₀ hτ₀
    have : ‖actualPhysicalUnitHalfTrace32 ((τ₀ : ℂ) • u) (x : ℂ)‖ ^ 2 = 1 := by
      rw [← norm_pow, h1]; simp
    nlinarith [norm_nonneg (actualPhysicalUnitHalfTrace32 ((τ₀ : ℂ) • u) (x : ℂ))]
  obtain ⟨C, hC, δ, hδ, hH⟩ := actualQuasimomentumBoundary_holder_in_u_E02_38 ((τ₀ : ℂ) • u) hu₀ B
    hB1 (hnorm τ₀ hτ₀ hu₀) x hx
  have hdist : ∀ τ : ℝ, ‖(τ : ℂ) • u - (τ₀ : ℂ) • u‖ = |τ - τ₀| * ‖u‖ := by
    intro τ
    rw [← sub_smul, norm_smul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hg : Tendsto (fun τ : ℝ => 6 * Real.sqrt (C * (|τ - τ₀| * ‖u‖))) (𝓝 τ₀) (𝓝 0) := by
    have hc : Continuous (fun τ : ℝ => 6 * Real.sqrt (C * (|τ - τ₀| * ‖u‖))) := by fun_prop
    simpa using hc.tendsto τ₀
  have hnear : ∀ᶠ τ in 𝓝 τ₀, |τ - τ₀| * ‖u‖ < δ := by
    have hc : Continuous (fun τ : ℝ => |τ - τ₀| * ‖u‖) := by fun_prop
    exact hc.continuousAt.eventually (gt_mem_nhds (by simpa using hδ))
  unfold ContinuousWithinAt
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ (hg.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds hnear] with τ hτ hτδ
  have hτs := sobolevSquareSummable_smul38 (τ : ℂ) u hu
  have h1 := hH ((τ : ℂ) • u) hτs (hnorm τ hτ hτs) (by rw [hdist]; exact hτδ.le)
  rw [hdist] at h1
  rw [Real.dist_eq]
  have h2 := Complex.abs_re_le_norm (actualQuasimomentumBoundaryE02_38 ((τ : ℂ) • u) x -
    actualQuasimomentumBoundaryE02_38 ((τ₀ : ℂ) • u) x)
  simp only [Complex.sub_re] at h2
  exact le_trans h2 h1

theorem label_of_band38 (x : ℝ)
    (hband : ∀ τ ∈ Icc (0:ℝ) 1, ‖actualPhysicalUnitHalfTrace32 ((τ : ℂ) • u) (x : ℂ)‖ < 1)
    (j : ℤ) (h1 : (j : ℝ) * Real.pi < x) (h2 : x < ((j : ℝ) + 1) * Real.pi) :
    (j : ℝ) * Real.pi < actualQuasimomentumRealPartE02_38 ((((1:ℝ)) : ℂ) • u) x ∧
    actualQuasimomentumRealPartE02_38 ((((1:ℝ)) : ℂ) • u) x < ((j : ℝ) + 1) * Real.pi := by
  have hc := realPart_continuousOn38 hu x hband
  have h0 : actualQuasimomentumRealPartE02_38 ((((0:ℝ)) : ℂ) • u) x = x := by
    simpa using quasimomentumRealPart_zero38 x
  constructor
  · by_contra hcon
    replace hcon := not_lt.mp hcon
    obtain ⟨τ, hτ, hτe⟩ := intermediate_value_Icc' (zero_le_one' ℝ) hc
      (show (j : ℝ) * Real.pi ∈ Icc _ _ from ⟨hcon, by rw [h0]; exact h1.le⟩)
    exact realPart_not_int38 _ x (hband τ hτ) j hτe
  · by_contra hcon
    replace hcon := not_lt.mp hcon
    obtain ⟨τ, hτ, hτe⟩ := intermediate_value_Icc (zero_le_one' ℝ) hc
      (show ((j : ℝ) + 1) * Real.pi ∈ Icc _ _ from ⟨by rw [h0]; exact h2.le, hcon⟩)
    exact realPart_not_int38 _ x (hband τ hτ) (j + 1) (by push_cast; exact hτe)


end Path

theorem cos_half_integer38 (n : ℤ) (sgn : ℝ) (hs : sgn = 1 ∨ sgn = -1) :
    ‖Complex.cos ((((n : ℝ) + sgn / 2) * Real.pi : ℝ) : ℂ)‖ < 1 := by
  rw [← Complex.ofReal_cos, Complex.norm_real, Real.norm_eq_abs]
  have : Real.cos (((n : ℝ) + sgn / 2) * Real.pi) = 0 := by
    rw [Real.cos_eq_zero_iff]
    rcases hs with rfl | rfl
    · exact ⟨n, by ring⟩
    · exact ⟨n - 1, by push_cast; ring⟩
  rw [this]; simp

/-- **Mo2, part A.**  Zero localization along the coupling path gives the localization of the
whole labelled gap. -/
theorem gap_localization_of_zeroLoc38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (R2 : ℝ) (hR : 0 ≤ R2)
    (hz : ∀ τ ∈ Icc (0:ℝ) 1, MolnarZeroLoc38 ((τ : ℂ) • u) R2)
    (n : ℤ) (hn : 8 * R2 ≤ molnarBracket38 n) (l : ℝ)
    (hl : l ∈ Set.Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n)) :
    |l - n * Real.pi| ≤ molnarRadius38 R2 n := by
  have hρ := molnarRadius38_lt R2 hR n hn
  have hpi := Real.pi_pos
  -- the two strip boundaries are bands along the whole path
  have hbd : ∀ sgn : ℝ, (sgn = 1 ∨ sgn = -1) →
      ∀ τ ∈ Icc (0:ℝ) 1, ‖actualPhysicalUnitHalfTrace32 ((τ : ℂ) • u)
        ((((n : ℝ) + sgn / 2) * Real.pi : ℝ) : ℂ)‖ < 1 := by
    intro sgn hs
    refine band_along_path38 u _ (cos_half_integer38 n sgn hs) ?_
    intro τ hτ hτ1
    have habs : |((n : ℝ) + sgn / 2) * Real.pi - n * Real.pi| = Real.pi / 2 := by
      have : ((n : ℝ) + sgn / 2) * Real.pi - n * Real.pi = sgn * (Real.pi / 2) := by ring
      rw [this, abs_mul, abs_of_pos (by positivity : 0 < Real.pi / 2)]
      rcases hs with rfl | rfl <;> simp
    have := hz τ hτ n hn _ habs.le hτ1
    rw [habs] at this
    linarith
  have hup := label_of_band38 hu _ (hbd 1 (Or.inl rfl)) n
    (by nlinarith) (by nlinarith)
  have hlo := label_of_band38 hu _ (hbd (-1) (Or.inr rfl)) (n - 1)
    (by push_cast; nlinarith) (by push_cast; nlinarith)
  have h1 : ((((1:ℝ)) : ℂ) • u) = u := by simp
  rw [h1] at hup hlo
  have hmono := monotone_actualQuasimomentumRealPartE02_38 u
  -- every point of the gap is strictly inside the strip
  have hin : ∀ y ∈ Set.Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n),
      |y - n * Real.pi| < Real.pi / 2 := by
    intro y hy
    have hy' : actualQuasimomentumRealPartE02_38 u y = (n : ℝ) * Real.pi := by
      have := (actualGapLevelSet_eq_Icc_E02_38 u n).2
      have hy2 : y ∈ actualGapLevelSetE02_38 u n := by rw [this]; exact hy
      exact hy2
    rw [abs_lt]
    constructor
    · by_contra hcon
      replace hcon := not_lt.mp hcon
      have := hmono (show y ≤ ((n : ℝ) + (-1) / 2) * Real.pi by linarith)
      have h2 := hlo.2
      push_cast at h2
      nlinarith
    · by_contra hcon
      replace hcon := not_lt.mp hcon
      have := hmono (show ((n : ℝ) + 1 / 2) * Real.pi ≤ y by linarith)
      have h2 := hup.1
      nlinarith
  obtain ⟨hne, hIcc⟩ := actualGapLevelSet_eq_Icc_E02_38 u n
  have hle : actualGapLowerAllE02_38 u n ≤ actualGapUpperAllE02_38 u n := by
    obtain ⟨y, hy⟩ := hne
    rw [hIcc] at hy
    exact hy.1.trans hy.2
  obtain ⟨hlow, hupp⟩ := actualGapEndpoint_halfTrace_all_E02_38 u n
  have hcos2 : (((Real.cos ((n : ℝ) * Real.pi) : ℝ) : ℂ)) ^ 2 = 1 := by
    have hs := Real.sin_int_mul_pi n
    have := Real.sin_sq_add_cos_sq ((n : ℝ) * Real.pi)
    rw [hs] at this
    rw [← Complex.ofReal_pow]
    have h2 : Real.cos ((n : ℝ) * Real.pi) ^ 2 = 1 := by linarith
    rw [h2]; simp
  have hz1 := hz 1 ⟨zero_le_one, le_rfl⟩
  rw [h1] at hz1
  have hlow' := hz1 n hn _ (hin _ ⟨le_rfl, hle⟩).le (by rw [hlow]; exact hcos2)
  have hupp' := hz1 n hn _ (hin _ ⟨hle, le_rfl⟩).le (by rw [hupp]; exact hcos2)
  rw [abs_le] at hlow' hupp' ⊢
  obtain ⟨hl1, hl2⟩ := hl
  constructor <;> linarith [hlow'.1, hlow'.2, hupp'.1, hupp'.2]

end

end NlsGge.GK38
