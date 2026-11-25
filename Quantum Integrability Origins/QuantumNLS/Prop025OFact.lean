import QuantumNLS.Prop025OKer

/-! PROP-025 (thm:MP-mixed, mixed_propagation.tex sha256 24ab083b...), stage O4b:
**the factorial kernel bound eq:MP-factorial-M, `M ≤ C W_a`** (source lines 436-444).

"By the discriminant bounds and eq:MP-kernel, there is a constant `C` independent of `a, N, t, θ` on the fixed
boxes such that `‖B_{j,a,t,θ}‖ ≤ C W_a (κL)^j/√((2j)!)`.  The fixed action contours contribute only a fixed
constant to this bound.  In the notation of Theorem Q7B:thm:main, one can therefore choose `M ≤ CW_a` and a fixed
`A_* = κL`."

At the PROP-020/026 window cut `a = cutN L α N` (`α = 1/(56(d+1))`, the cut of the frozen stage O3f) and the
physical separators of the fixed rectangles, eventually in `N` and uniformly on the boxes:
* `weight_bounds`: the frozen weight `D(z_θ)⁻¹` is continuous, `‖u_θ D(z_θ)⁻¹‖ ≤ C W_a` (`|p_t| ≤ ΣT (1+a+h)^d`,
  side lengths `≤ 2(a+h)`, `|D| ≥ η` on the window contour from the accepted moving-contour bundle, `|D| ≥ η_f`
  on the fixed rectangles from the accepted `gam_family_background`), and every contour point has `|Im z| ≤ h`;
* **`factorial_bound`**: `‖B_{j+1}‖ ≤ (C' W_a) (κL)^{j+1}/√((2(j+1))!)` (accepted `kernel_bound` through
  `R52CFBudget.kerA_le_bseq`), with ONE `C'`.
No hypothesis is added; all inherited modules are read-only.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open scoped ComplexConjugate Topology NNReal ENNReal InnerProductSpace
open MeasureTheory Filter Set

namespace QuantumNLS.Prop025OFact
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheCoefficientTransform (HN)
open QuantumNLS.Extrapolation (Gfull)
open QuantumNLS.PeriodReconstructionCore
open QuantumNLS.PeriodReconstruction (Gam)
open QuantumNLS.MPContour (Piece ThetaSpace nu zθ uθ rectPieces polyT continuous_polyT continuous_zθ continuous_uθ)
open QuantumNLS.MPContour (norm_polyT_le)
open QuantumNLS.Prop026Uniform (rectFamily rectFamily_props)
open QuantumNLS.Prop025OPhase (mixedPieces xmS xpS)
open QuantumNLS.Prop025OKer (mixD mixK)
open QuantumNLS.Prop025OFinal (W)
open QuantumNLS.Prop025OParams (alpha alpha_pos)
open QuantumNLS.PROP018Probability (cutN regime_eventually)
open QuantumNLS.Prop018BundleFull (moving_contour_bundle_full)
open QuantumNLS.Prop017Physical (RootSpectralInputs)
open QuantumNLS.Prop017Quantum (eta0 Gfull_eq qAct)
open QuantumNLS.BulkResponseActual (physBasis IsLimitingRapidityMeasure)
open QuantumNLS.EmpiricalRapidity (bornMeasure)
open QuantumNLS.RootEvent (EN)
open QuantumNLS.ResolventNeighborhood (NbhdN)
open QuantumNLS.Prop026Mixed (gam_family_background)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-! ### Piece geometry -/

theorem rectGen_γ' (xm xp h : ℝ) (ω : ℂ → ℂ) (hω : Continuous ω) (i : Fin 6) (τ : ℝ) :
    (MPFixedContour.rectGen xm xp h ω hω i).γ' τ =
      (MPFixedContour.rectGen xm xp h ω hω i).γ 1 - (MPFixedContour.rectGen xm xp h ω hω i).γ 0 := by
  fin_cases i <;> simp [MPFixedContour.rectGen, MPContour.affinePiece]

theorem rectGen_ω (xm xp h : ℝ) (ω : ℂ → ℂ) (hω : Continuous ω) (i : Fin 6) :
    (MPFixedContour.rectGen xm xp h ω hω i).ω = ω := by
  fin_cases i <;> rfl

theorem norm_le_of_Gam {a b h : ℝ} (hab : a ≤ b) (hh : 0 ≤ h) {z : ℂ} (hz : z ∈ Gam a b h) :
    ‖z‖ ≤ |a| + |b| + h := by
  have h1 := Complex.norm_le_abs_re_add_abs_im z
  have hre : |z.re| ≤ |a| + |b| := by
    rcases hz with ⟨⟨h1, h2⟩, _⟩ | ⟨_, h3 | h3⟩
    · rw [abs_le]; constructor <;> cases abs_cases a <;> cases abs_cases b <;> linarith
    · rw [h3]; linarith [abs_nonneg b]
    · rw [h3]; linarith [abs_nonneg a]
  have him : |z.im| ≤ h := QuantumNLS.R52CFCoh.Gam_abs_im_le hh hz
  linarith

/-! ### The weight bounds -/

set_option maxHeartbeats 32000000 in
theorem weight_bounds (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {h δ d0 : ℝ} {l0 : ℕ} (hηh : eta0 L κ < h)
    (hδ : 0 < δ) (hd0 : 0 < d0) (hin : RootSpectralInputs L κ (μ : Measure ℝ) h δ d0 l0)
    (d : ℕ) (hd : 2 ≤ d) (ords : Finset ℕ) (hords : ords ⊆ Finset.range (d + 1)) (T : ℕ → ℝ)
    {nI : ℕ} (n : Fin nI → ℤ) (Θ : Fin nI → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, ∀ t : ℕ → ℝ, (∀ r ∈ ords, |t r| ≤ T r) →
      ∀ θf : Fin nI → ℝ, (∀ i, |θf i| ≤ Θ i) →
        Continuous (mixD (L := L) hκ u (μ : Measure ℝ) h (cutN L (alpha d) N) ords t n θf) ∧
        (∀ θ, ‖uθ κ (mixedPieces hκ u h (cutN L (alpha d) N) ords t n θf) θ *
            mixD (L := L) hκ u (μ : Measure ℝ) h (cutN L (alpha d) N) ords t n θf θ‖ ≤
          C * W d (cutN L (alpha d) N)) ∧
        (∀ θ, |(zθ (mixedPieces hκ u h (cutN L (alpha d) N) ords t n θf) θ).im| ≤ h) := by
  have hL : 0 < L := Fact.out
  -- the printed parameters (eq:MP-parameters), as in stage O3f
  set α : ℝ := alpha d with hαdef
  have hα : 0 < α := alpha_pos d
  have hα56 : α ≤ 1 / 56 := by
    rw [hαdef]; unfold alpha
    have : (56 : ℝ) ≤ 56 * ((d : ℝ) + 1) := by have := (Nat.cast_nonneg d : (0 : ℝ) ≤ d); nlinarith
    exact one_div_le_one_div_of_le (by norm_num) this
  have hsum : 3 * (1 / 8 : ℝ) + α < 1 := by linarith
  have hγ0 : (0 : ℝ) < 1 / 8 := by norm_num
  set b : ℕ := d + 2 with hbdef
  have hb1 : 1 ≤ b := by omega
  set p0 : ℕ := 28 * (d + 1) + 1 with hp0def
  have hp0 : 1 < 2 * (p0 : ℝ) * α := by
    rw [hαdef, hp0def]; unfold alpha
    have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
    have e : 2 * (((28 * (d + 1) + 1 : ℕ)) : ℝ) * (1 / (56 * ((d : ℝ) + 1))) = 1 + 1 / (28 * ((d : ℝ) + 1)) := by
      push_cast; field_simp; ring
    rw [e]
    have : 0 < 1 / (28 * ((d : ℝ) + 1)) := by positivity
    linarith
  obtain ⟨ρ, hρ0, h2ρ, hbadT, -, C0, M, η, rd, K, Kd, hM1, hη, hrd, hK0, hev⟩ :=
    moving_contour_bundle_full hκ u hu hμ hηh hδ hd0 hin b b hb1 (by omega) α (1 / 8) hα hγ0 hsum p0 hp0
  have hh : 0 < h := by linarith
  -- the fixed rectangles and their background
  set S := QuantumNLS.Prop026Bound.scalarCuts hκ u hu with hSdef
  have hS : (μ : Measure ℝ) = S.μ := (QuantumNLS.Prop026Bound.physical_eq_limit hκ u hu hμ).symm
  have hGeq : Gfull (μ : Measure ℝ) = EmpiricalRapidity.cauchyTransform S.μ := by
    funext z; rw [Gfull_eq, hS]; rfl
  set xm : Fin nI → ℝ := xmS hκ u n with hxmdef
  set xp : Fin nI → ℝ := xpS hκ u n with hxpdef
  have hsep := fun i => QuantumNLS.Prop025OCount.separator_brackets L hκ u hu (n i)
  have hxm : ∀ i, xm i ∈ S.cuts := fun i => (hsep i).1
  have hxp : ∀ i, xp i ∈ S.cuts := fun i => (hsep i).2.1
  have hlt : ∀ i, xm i < xp i := fun i => (hsep i).2.2.1
  obtain ⟨ηf, Mf, Gbf, hηf, hMf, hGbf, hbf⟩ :=
    gam_family_background S (h := fun _ => h) hxm hxp hlt (fun _ => hh)
      (fun i => (hsep i).2.2.2.1) (fun i => (hsep i).2.2.2.2.1) (fun i => (hsep i).2.2.2.2.2.1)
      (fun i => (hsep i).2.2.2.2.2.2)
  -- the constant
  set Bf : ℝ := ∑ i, (|xm i| + |xp i|) + h with hBfdef
  have hBf0 : 0 ≤ Bf := by
    rw [hBfdef]; have : 0 ≤ ∑ i, (|xm i| + |xp i|) := Finset.sum_nonneg fun i _ => by positivity
    linarith
  set ST : ℝ := ∑ r ∈ ords, |T r| with hSTdef
  have hST0 : 0 ≤ ST := Finset.sum_nonneg fun r _ => abs_nonneg _
  set SΘ : ℝ := ∑ i, |Θ i| with hSΘdef
  have hSΘ0 : 0 ≤ SΘ := Finset.sum_nonneg fun i _ => abs_nonneg _
  set c2 : ℝ := (2 * Real.pi * κ)⁻¹ with hc2def
  have hc20 : 0 < c2 := by rw [hc2def]; positivity
  set Dm : ℝ := (min η ηf)⁻¹ with hDmdef
  have hDm0 : 0 < Dm := by rw [hDmdef]; exact inv_pos.mpr (lt_min hη hηf)
  set C : ℝ := c2 * Dm * (ST * 2 * (1 + h) ^ (d + 1) + SΘ * 2 * Bf) with hCdef
  refine ⟨C, by rw [hCdef]; positivity, ?_⟩
  -- the event is eventually nonempty
  have hne : ∀ᶠ N : ℕ in atTop, ∃ m, m ∈ EN (μ : Measure ℝ) (qAct L κ N) ((N : ℝ) ^ α) (cutN L α N) ρ h
      (eta0 L κ) ((N : ℝ) ^ (-(1 / 8 : ℝ))) b := by
    filter_upwards [hbadT.eventually (gt_mem_nhds one_pos)] with N hN
    by_contra hcon
    push Not at hcon
    have he : EN (μ : Measure ℝ) (qAct L κ N) ((N : ℝ) ^ α) (cutN L α N) ρ h (eta0 L κ)
        ((N : ℝ) ^ (-(1 / 8 : ℝ))) b = ∅ := Set.eq_empty_iff_forall_notMem.mpr hcon
    rw [he, Set.compl_empty, probReal_univ] at hN
    exact lt_irrefl _ hN
  filter_upwards [hev, hne, regime_eventually hL hα hγ0 1 0] with N hevN hneN hreg
  obtain ⟨m0, hm0⟩ := hneN
  intro t ht θf hθf
  set a : ℝ := cutN L α N with hadef
  have ha2 : 2 ≤ a := by linarith [hreg.1, hreg.2.2.1]
  have ha0 : 0 ≤ a := by linarith
  set P := mixedPieces hκ u h a ords t n θf with hPdef
  -- the background facts at every contour point
  have hwin : ∀ z ∈ NbhdN a h (ρ / 8), DifferentiableAt ℂ (Gfull (μ : Measure ℝ)) z ∧
      η ≤ ‖Df L κ (Gfull (μ : Measure ℝ)) z‖ := by
    intro z hz
    obtain ⟨-, -, -, -, hdz, hηz, -⟩ := hevN m0 hm0 z hz
    exact ⟨hdz, hηz⟩
  have hfix : ∀ i, ∀ z ∈ Gam (xm i) (xp i) h, DifferentiableAt ℂ (Gfull (μ : Measure ℝ)) z ∧
      ηf ≤ ‖Df L κ (Gfull (μ : Measure ℝ)) z‖ := by
    intro i z hz
    rw [hGeq]
    exact ⟨(hbf i z hz).1, (hbf i z hz).2.1⟩
  have hfam := rectFamily_props xm xp (fun _ => h) θf Θ hlt (fun _ => hh) hθf
  -- every contour point: membership, `|Im| ≤ h`, weight bound
  have hpt : ∀ θ : ThetaSpace (6 + nI * 6),
      (DifferentiableAt ℂ (Gfull (μ : Measure ℝ)) (zθ P θ) ∧ min η ηf ≤ ‖Df L κ (Gfull (μ : Measure ℝ)) (zθ P θ)‖) ∧
      |(zθ P θ).im| ≤ h ∧ ‖uθ κ P θ‖ ≤ c2 * (ST * 2 * (1 + h) ^ (d + 1) + SΘ * 2 * Bf) * W d a := by
    rintro ⟨i, τ⟩
    have hτ : (τ : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨τ.2.1, τ.2.2⟩
    have hW1 : 1 ≤ W d a := by unfold W; exact one_le_pow₀ (by linarith)
    simp only [zθ, uθ]
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simp only [hPdef, mixedPieces, Fin.append_left]
      set Wp := rectPieces a h (polyT ords t) (continuous_polyT ords t)
      have hz : (Wp i).γ τ ∈ NbhdN a h (ρ / 8) :=
        QuantumNLS.Prop020Link.rect_nbhd ha0 hh.le (by positivity) _ _ i τ hτ
      obtain ⟨hdz, hηz⟩ := hwin _ hz
      refine ⟨⟨hdz, (min_le_left _ _).trans hηz⟩,
        QuantumNLS.Prop020Link.rect_im_le ha0 hh.le _ _ i τ hτ, ?_⟩
      have hzG := QuantumNLS.Prop019Linearization.rect_mem ha0 hh.le (polyT ords t) (continuous_polyT ords t) i hτ
      have hzn := QuantumNLS.Prop019Linearization.norm_le_of_gammaN ha0 hh.le hzG
      set B : ℝ := (1 + a) * (1 + h) with hB
      have hB1 : 1 ≤ B := by rw [hB]; nlinarith
      have hzB : ‖(Wp i).γ τ‖ ≤ B := hzn.trans (by rw [hB]; nlinarith)
      have hω : ‖(Wp i).ω ((Wp i).γ τ)‖ ≤ ST * B ^ d := by
        rw [QuantumNLS.Prop019Linearization.rect_ω]
        have hT' : ∀ r ∈ ords, |t r| ≤ |T r| := fun r hr => (ht r hr).trans (le_abs_self _)
        have := norm_polyT_le ords t (fun r => |T r|)
          (fun r hr => Nat.lt_succ_iff.mp (Finset.mem_range.mp (hords hr))) hT' hzB hB1
        exact this
      have hγ' : ‖(Wp i).γ' τ‖ ≤ 2 * B := by
        rw [QuantumNLS.Prop019Linearization.rect_γ']
        have h1 := QuantumNLS.Prop019Linearization.norm_le_of_gammaN ha0 hh.le
          (QuantumNLS.Prop019Linearization.rect_mem ha0 hh.le (polyT ords t) (continuous_polyT ords t) i
            (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩))
        have h0 := QuantumNLS.Prop019Linearization.norm_le_of_gammaN ha0 hh.le
          (QuantumNLS.Prop019Linearization.rect_mem ha0 hh.le (polyT ords t) (continuous_polyT ords t) i
            (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩))
        have := norm_sub_le ((Wp i).γ 1) ((Wp i).γ 0)
        have hB' : a + h ≤ B := by rw [hB]; nlinarith
        linarith
      have hBd : B ^ d * B = W d a * (1 + h) ^ (d + 1) := by
        rw [hB]; unfold W; rw [← pow_succ, mul_pow]
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hc20.le]
      calc c2 * ‖(Wp i).ω ((Wp i).γ τ)‖ * ‖(Wp i).γ' τ‖ ≤ c2 * (ST * B ^ d) * (2 * B) := by
            gcongr
        _ = c2 * (ST * 2) * (B ^ d * B) := by ring
        _ = c2 * (ST * 2 * (1 + h) ^ (d + 1)) * W d a := by rw [hBd]; ring
        _ ≤ c2 * (ST * 2 * (1 + h) ^ (d + 1) + SΘ * 2 * Bf) * W d a := by
            gcongr; nlinarith
    · simp only [hPdef, mixedPieces, Fin.append_right]
      obtain ⟨i0, hi0⟩ := hfam.2.1 j τ hτ
      obtain ⟨hdz, hηz⟩ := hfix i0 _ hi0
      refine ⟨⟨hdz, (min_le_right _ _).trans hηz⟩,
        QuantumNLS.R52CFCoh.Gam_abs_im_le hh.le hi0, ?_⟩
      have hBi : ∀ i', |xm i'| + |xp i'| + h ≤ Bf := by
        intro i'
        rw [hBfdef]
        have := Finset.single_le_sum (f := fun i => |xm i| + |xp i|) (fun i _ => by positivity)
          (Finset.mem_univ i')
        linarith
      have hγ' : ‖(rectFamily xm xp (fun _ => h) θf j).γ' τ‖ ≤ 2 * Bf := by
        have hg : (rectFamily xm xp (fun _ => h) θf j).γ' τ =
            (rectFamily xm xp (fun _ => h) θf j).γ 1 - (rectFamily xm xp (fun _ => h) θf j).γ 0 := by
          unfold rectFamily; exact rectGen_γ' _ _ _ _ _ _ _
        rw [hg]
        obtain ⟨i1, hi1⟩ := hfam.2.1 j 1 ⟨zero_le_one, le_rfl⟩
        obtain ⟨i2, hi2⟩ := hfam.2.1 j 0 ⟨le_rfl, zero_le_one⟩
        have e1 := (norm_le_of_Gam (hlt i1).le hh.le hi1).trans (hBi i1)
        have e2 := (norm_le_of_Gam (hlt i2).le hh.le hi2).trans (hBi i2)
        have := norm_sub_le ((rectFamily xm xp (fun _ => h) θf j).γ 1)
          ((rectFamily xm xp (fun _ => h) θf j).γ 0)
        linarith
      have hω : ‖(rectFamily xm xp (fun _ => h) θf j).ω ((rectFamily xm xp (fun _ => h) θf j).γ τ)‖ ≤ SΘ := by
        have hωe : (rectFamily xm xp (fun _ => h) θf j).ω =
            fun _ => ((θf (finProdFinEquiv.symm j).1 : ℝ) : ℂ) := by
          unfold rectFamily; exact rectGen_ω _ _ _ _ _ _
        rw [hωe, Complex.norm_real, Real.norm_eq_abs]
        have h1 := (hθf (finProdFinEquiv.symm j).1).trans (le_abs_self _)
        have h2 := Finset.single_le_sum (f := fun i => |Θ i|) (fun i _ => abs_nonneg _)
          (Finset.mem_univ (finProdFinEquiv.symm j).1)
        linarith
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hc20.le]
      calc c2 * ‖(rectFamily xm xp (fun _ => h) θf j).ω ((rectFamily xm xp (fun _ => h) θf j).γ τ)‖ *
            ‖(rectFamily xm xp (fun _ => h) θf j).γ' τ‖ ≤ c2 * SΘ * (2 * Bf) := by gcongr
        _ = c2 * (SΘ * 2 * Bf) * 1 := by ring
        _ ≤ c2 * (ST * 2 * (1 + h) ^ (d + 1) + SΘ * 2 * Bf) * W d a := by
            gcongr
            · have : 0 ≤ ST * 2 * (1 + h) ^ (d + 1) := by positivity
              linarith
  refine ⟨?_, fun θ => ?_, fun θ => (hpt θ).2.1⟩
  · -- continuity of the frozen weight
    refine continuous_iff_continuousAt.mpr fun θ => ?_
    obtain ⟨⟨hdz, hηz⟩, -, -⟩ := hpt θ
    have hG : ContinuousAt (Gfull (μ : Measure ℝ)) (zθ P θ) := hdz.continuousAt
    have hA : ContinuousAt (Af κ (Gfull (μ : Measure ℝ))) (zθ P θ) := by
      unfold Af
      exact Complex.continuous_exp.continuousAt.comp (continuousAt_const.mul hG)
    have he : ContinuousAt (ef L) (zθ P θ) := by
      unfold ef; exact (by fun_prop : Continuous fun z : ℂ => Complex.exp (Complex.I * L * z)).continuousAt
    have hD : ContinuousAt (Df L κ (Gfull (μ : Measure ℝ))) (zθ P θ) := by
      unfold Df
      exact hA.sub (he.div hA (by unfold Af; exact Complex.exp_ne_zero _))
    have hne : Df L κ (Gfull (μ : Measure ℝ)) (zθ P θ) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hηz
      exact absurd hηz (not_le.mpr (lt_min hη hηf))
    exact (ContinuousAt.comp (g := Df L κ (Gfull (μ : Measure ℝ))) hD
      (continuous_zθ P).continuousAt).inv₀ hne
  · obtain ⟨⟨-, hηz⟩, -, hu'⟩ := hpt θ
    have hmin : 0 < min η ηf := lt_min hη hηf
    have hD : ‖mixD (L := L) hκ u (μ : Measure ℝ) h a ords t n θf θ‖ ≤ Dm := by
      unfold mixD
      rw [norm_inv, hDmdef]
      exact inv_anti₀ hmin hηz
    rw [norm_mul]
    calc ‖uθ κ P θ‖ * ‖mixD (L := L) hκ u (μ : Measure ℝ) h a ords t n θf θ‖
        ≤ (c2 * (ST * 2 * (1 + h) ^ (d + 1) + SΘ * 2 * Bf) * W d a) * Dm :=
          mul_le_mul hu' hD (norm_nonneg _) (by unfold W; positivity)
      _ = C * W d a := by rw [hCdef]; ring

/-- **eq:MP-factorial-M**: `‖B_{j+1}‖ ≤ (C' W_a) (κL)^{j+1}/√((2(j+1))!)`, eventually, uniformly on the boxes. -/
theorem factorial_bound (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {h δ d0 : ℝ} {l0 : ℕ} (hηh : eta0 L κ < h)
    (hδ : 0 < δ) (hd0 : 0 < d0) (hin : RootSpectralInputs L κ (μ : Measure ℝ) h δ d0 l0)
    (d : ℕ) (hd : 2 ≤ d) (ords : Finset ℕ) (hords : ords ⊆ Finset.range (d + 1)) (T : ℕ → ℝ)
    {nI : ℕ} (n : Fin nI → ℤ) (Θ : Fin nI → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, ∀ t : ℕ → ℝ, (∀ r ∈ ords, |t r| ≤ T r) →
      ∀ θf : Fin nI → ℝ, (∀ i, |θf i| ≤ Θ i) →
        Continuous (mixD (L := L) hκ u (μ : Measure ℝ) h (cutN L (alpha d) N) ords t n θf) ∧
        (∀ θ, ‖uθ κ (mixedPieces hκ u h (cutN L (alpha d) N) ords t n θf) θ *
            mixD (L := L) hκ u (μ : Measure ℝ) h (cutN L (alpha d) N) ords t n θf θ‖ ≤
          C * W d (cutN L (alpha d) N)) ∧
        (∀ θ, |(zθ (mixedPieces hκ u h (cutN L (alpha d) N) ords t n θf) θ).im| ≤ h) ∧
        ∀ j : ℕ, ‖mixK (L := L) hκ u (μ : Measure ℝ) h (cutN L (alpha d) N) ords t n θf j‖ ≤
          ((nu (6 + nI * 6)).real univ * C * 2 * Real.exp (L * h) * W d (cutN L (alpha d) N)) * (κ * L) ^ (j + 1) /
            Real.sqrt ((2 * (j + 1)).factorial : ℝ) := by
  obtain ⟨C, hC0, hev⟩ := weight_bounds hκ u hu hμ hηh hδ hd0 hin d hd ords hords T n Θ
  refine ⟨C, hC0, ?_⟩
  filter_upwards [hev] with N hN t ht θf hθf
  obtain ⟨hcont, hw, him⟩ := hN t ht θf hθf
  refine ⟨hcont, hw, him, fun j => ?_⟩
  have hW0 : 0 ≤ C * W d (cutN L (alpha d) N) := by
    have := hw (⟨0, by omega⟩, 0); exact (norm_nonneg _).trans this
  have hk := QuantumNLS.R52CFBudget.kerA_le_bseq (L := L) (nu (6 + nI * 6)) κ _ _ him hw hW0 j
  unfold QuantumNLS.R52CFBudget.bseq QuantumNLS.R52CFBudget.beta at hk
  rw [abs_of_pos hκ] at hk
  unfold mixK
  refine hk.trans (le_of_eq ?_)
  ring

end QuantumNLS.Prop025OFact

#print axioms QuantumNLS.Prop025OFact.weight_bounds
#print axioms QuantumNLS.Prop025OFact.factorial_bound

-- Recursive type/value audit of every own declaration: standard axioms only, and no held
-- identifier (HeldGP14Tonelli, the superseded pre-D1 `RegularCut`) in the transitive closure.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop025OFact." then
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
  Lean.logInfo m!"Prop025OFact aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only, no held identifiers."
