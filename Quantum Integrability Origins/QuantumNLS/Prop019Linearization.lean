import QuantumNLS.Prop019Deviation
import QuantumNLS.Prop018Scalar
import QuantumNLS.MPFamily
import QuantumNLS.MPOps

/-!
# PROP-019 (`Q7A:lem:linearization`): quantitative spectral linearization on the moving window contour

Source: `window_reconstruction.tex:220`, `Q7A:eq:linear`, `Q7A:eq:lincompare` and the proof of `Q7A:lem:linearization`:
on `ran P_N`, uniformly for normalized `Φ` and `|t| ≤ T`,
`‖γ^{(k)}_{e^{−itNC_{0,N,p}}Φ} − γ^{(k)}_{e^{−itNL_{N,p}}Φ}‖₁ ≤ C_{p,k,T}(1+a)^{d+1}(ε+R^{−b}+N^{−1})`.

The printed proof is the PROP-026 argument (`lem:A4-functional-linearization` applied at every contour point to the quadratures
of `S_N(z)`, the commutator estimate, trace-norm duality) on the window contour `Γ_N`, with the deviation
`Δ = C_b(ε+R^{−b}+N^{−1})` and the weighted length `∮_{Γ_N}|p||dz| ≤ C_p(1+a)^{d+1}`.

## The named hypothesis (integrator ruling): `MPLinearizationStatement`
The PROP-026 actual-contour theorem is sonnet_fourier's target `MPLinearization.mp_linearization` (not frozen at the time of
writing; its open obligations are owned by sonnet_fourier and are NOT re-proved here). Its statement is carried **verbatim** as the
explicit hypothesis `MPLinearizationStatement` (only the weighted length `wlen` of the unfrozen `MPContourBound` is written out
as its defining integral). Once frozen, `fun d₀ s₁ a₀ c₁ h1 h2 h3 h4 => mp_linearization L κ hκ h k d₀ s₁ a₀ c₁ h1 h2 h3 h4`
discharges it. The operators are the printed ones (`MPOps`, frozen `d123401d`):
`C_{0,N,p_t} = C0op = Re ∫ u_θ f_{z_θ}(S_N(z_θ)) dν` with `u_θ = −(2πκ)^{−1}p_t(z_θ)γ'` (`Q7A:eq:C0` along `Γ_N`) and
`L_{N,p_t} = Lop = Re ∫ u_θ D(z_θ)^{−1}S_N(z_θ) dν` (`Q7A:eq:linear`); the time is absorbed into `p_t = t p`.

## Proved here
* the window contour `Γ_N = rectPieces a_N h p_t` (frozen `MPContour`): its points lie on `Γ_N`, `|Im| ≤ h`, interiors off the
  real axis; the weighted-length bound `∑_i ∫|p_t(γ_i)||γ_i'| ≤ 12|t| Σ|p_r| ((1+a)(1+h))^{d+1}` (own proof);
* the background family `BgFam` on the `ρ/8`-neighbourhood of `Γ_N` with `c₀ = iκG_μ`, `D`, `s`, `A` and the uniform bounds
  `d₀ = η`, `s₁ = M + M²`, `a₀ = 1/M`, `c₁ = κ(2K + 1/r)` from the PROP-018 bundle (`Prop018Bundle`);
* the deviation `ε = max(K_d,0)(ε_N + R_N^{−b} + N^{−1})` on `ran P_N` (W1 `deviation_of_bundle`);
* **`prop019_linearization`**: `eq:lincompare` for the actual model on the PROP-018 event, with `RootSpectralInputs` and
  `MPLinearizationStatement` as explicit hypotheses.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology Set
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace QuantumNLS.Prop019Linearization

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheLabels (MArr)
open QuantumNLS.EmpiricalRapidity (bornMeasure)
open QuantumNLS.BulkResponseActual (physBasis IsLimitingRapidityMeasure)
open QuantumNLS.Extrapolation (Gfull GN)
open QuantumNLS.RootEvent (EN)
open QuantumNLS.ResolventNeighborhood (GammaN NbhdN)
open QuantumNLS.PROP018Probability (cutN regime_eventually)
open QuantumNLS.Prop017Quantum (qAct eta0)
open QuantumNLS.Prop017Physical (RootSpectralInputs)
open QuantumNLS.PeriodReconstructionCore
open QuantumNLS.Prop018Bundle (moving_contour_bundle)
open QuantumNLS.Prop018Scalar (A_eq_half norm_sf_le)
open QuantumNLS.Prop019Deviation (deviation_of_bundle)
open QuantumNLS.MPContour (Piece ThetaSpace nu zθ uθ affinePiece rectPieces)
open QuantumNLS.MPFamily (BgFam gθ dθ)
open QuantumNLS.MPChartSmooth (Bg)
open QuantumNLS.MPOps (C0op Lop)
open QuantumNLS.FunctionalLinearization (evol)
open QuantumNLS.TensorCarrier (SymSector HilbertTensorPower reducedDensityPower)
open QuantumNLS.NormalizedTransfer (normalizedTransfer)
open QuantumNLS.UnconditionalBetheBasis (meanField_physicalBasis)

/-! ## 1. The named hypothesis -/

/-- The statement of sonnet_fourier's PROP-026 actual-contour theorem `MPLinearization.mp_linearization` (verbatim; `wlen P`
written out as `∫ τ, ‖P.ω (P.γ τ)‖ * ‖P.γ' τ‖`). -/
def MPLinearizationStatement (L : ℝ) [Fact (0 < L)] (κ : ℝ) (h : ℝ) (k : ℕ) (d₀ s₁ a₀ c₁ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (q : ℕ) (_hN : 1 ≤ k + q) {m : ℕ} (Z : Set ℂ) (P : Fin m → Piece)
      (_hZ : ∀ i, ∀ τ ∈ Icc (0 : ℝ) 1, (P i).γ τ ∈ Z)
      (_hIm : ∀ i, ∀ τ ∈ Icc (0 : ℝ) 1, |((P i).γ τ).im| ≤ h)
      (_hreal : ∀ i, ∀ τ ∈ Ioo (0 : ℝ) 1, ((P i).γ τ).im ≠ 0)
      (B : BgFam Z d₀ s₁ a₀ c₁)
      (phi : SymSector ℂ (L2T L) (k + q)) (_hphi : ‖phi‖ = 1) (ε : Fin m → ℝ) (_hε : ∀ i, 0 ≤ ε i)
      (_hdev : ∀ i, ∀ τ ∈ Icc (0 : ℝ) 1,
        ‖(normalizedTransfer L κ (k + q) ((P i).γ τ) - B.s ((P i).γ τ) •
          (1 : SymSector ℂ (L2T L) (k + q) →L[ℂ] SymSector ℂ (L2T L) (k + q))) phi‖ ≤ ε i),
      QuantumNLS.TraceClass.traceNorm
        (reducedDensityPower k q
            ((evol (((((k + q : ℕ) : ℝ) : ℂ)) •
              C0op (nu m) (fun θ => normalizedTransfer L κ (k + q) (zθ P θ)) (uθ κ P) (gθ P B)) 1 phi :
              SymSector ℂ (L2T L) (k + q)) : HilbertTensorPower ℂ (L2T L) (k + q)) -
          reducedDensityPower k q
            ((evol (((((k + q : ℕ) : ℝ) : ℂ)) •
              Lop (nu m) (fun θ => normalizedTransfer L κ (k + q) (zθ P θ)) (uθ κ P) (dθ P B)) 1 phi :
              SymSector ℂ (L2T L) (k + q)) : HilbertTensorPower ℂ (L2T L) (k + q))) ≤
        ENNReal.ofReal (C * ((2 * Real.pi * κ)⁻¹ *
          ∑ i : Fin m, ε i * ∫ τ : unitInterval, ‖(P i).ω ((P i).γ τ)‖ * ‖(P i).γ' τ‖))

/-! ## 2. The window contour -/

/-- The time-scaled polynomial weight `p_t(z) = Σ_{r ≤ d} t p_r z^r`. -/
def pw (d : ℕ) (t : ℝ) (p : ℕ → ℝ) (z : ℂ) : ℂ := ∑ r ∈ Finset.range (d + 1), ((t * p r : ℝ) : ℂ) * z ^ r

lemma continuous_pw (d : ℕ) (t : ℝ) (p : ℕ → ℝ) : Continuous (pw d t p) := by
  unfold pw; fun_prop

lemma rect_re_im (a h : ℝ) (ω : ℂ → ℂ) (hω : Continuous ω) (i : Fin 6) (τ : ℝ) :
    ((rectPieces a h ω hω i).γ τ).re = ![-a + 2 * a * τ, a, a, a - 2 * a * τ, -a, -a] i ∧
    ((rectPieces a h ω hω i).γ τ).im = ![-h, -h + h * τ, h * τ, h, h - h * τ, -(h * τ)] i := by
  fin_cases i <;> simp [rectPieces, affinePiece] <;> ring_nf

lemma rect_mem {a h : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) (ω : ℂ → ℂ) (hω : Continuous ω) (i : Fin 6) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) 1) : (rectPieces a h ω hω i).γ τ ∈ GammaN a h := by
  obtain ⟨h0, h1⟩ := hτ
  obtain ⟨hre, him⟩ := rect_re_im a h ω hω i τ
  generalize (rectPieces a h ω hω i).γ τ = z at hre him ⊢
  simp only [GammaN, mem_union, Set.mem_ofPred_eq]
  fin_cases i <;> simp at hre him <;> rw [hre, him]
  · exact Or.inr ⟨Or.inr rfl, abs_le.2 ⟨by nlinarith, by nlinarith⟩⟩
  · exact Or.inl ⟨Or.inl rfl, abs_le.2 ⟨by nlinarith, by nlinarith⟩⟩
  · exact Or.inl ⟨Or.inl rfl, abs_le.2 ⟨by nlinarith, by nlinarith⟩⟩
  · exact Or.inr ⟨Or.inl rfl, abs_le.2 ⟨by nlinarith, by nlinarith⟩⟩
  · exact Or.inl ⟨Or.inr rfl, abs_le.2 ⟨by nlinarith, by nlinarith⟩⟩
  · exact Or.inl ⟨Or.inr rfl, abs_le.2 ⟨by nlinarith, by nlinarith⟩⟩

lemma rect_im_ne {a h : ℝ} (hh : 0 < h) (ω : ℂ → ℂ) (hω : Continuous ω) (i : Fin 6) {τ : ℝ}
    (hτ : τ ∈ Ioo (0 : ℝ) 1) : ((rectPieces a h ω hω i).γ τ).im ≠ 0 := by
  obtain ⟨h0, h1⟩ := hτ
  rw [(rect_re_im a h ω hω i τ).2]
  intro hc
  fin_cases i <;> simp at hc <;> (try rcases hc with hc | hc) <;> nlinarith

lemma gammaN_abs {a h : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) {z : ℂ} (hz : z ∈ GammaN a h) :
    |z.re| ≤ a ∧ |z.im| ≤ h := by
  rcases hz with ⟨h1 | h1, h2⟩ | ⟨h1 | h1, h2⟩
  · exact ⟨by rw [h1, abs_of_nonneg ha], h2⟩
  · exact ⟨by rw [h1, abs_neg, abs_of_nonneg ha], h2⟩
  · exact ⟨h2, by rw [h1, abs_of_nonneg hh]⟩
  · exact ⟨h2, by rw [h1, abs_neg, abs_of_nonneg hh]⟩

lemma norm_le_of_gammaN {a h : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) {z : ℂ} (hz : z ∈ GammaN a h) : ‖z‖ ≤ a + h := by
  have := Complex.norm_le_abs_re_add_abs_im z
  have h2 := gammaN_abs ha hh hz
  linarith [h2.1, h2.2]

lemma rect_ω (a h : ℝ) (ω : ℂ → ℂ) (hω : Continuous ω) (i : Fin 6) : (rectPieces a h ω hω i).ω = ω := by
  fin_cases i <;> rfl

lemma rect_γ' (a h : ℝ) (ω : ℂ → ℂ) (hω : Continuous ω) (i : Fin 6) (τ : ℝ) :
    (rectPieces a h ω hω i).γ' τ = (rectPieces a h ω hω i).γ 1 - (rectPieces a h ω hω i).γ 0 := by
  fin_cases i <;> simp [rectPieces, affinePiece]

lemma integral_I_le (f : unitInterval → ℝ) (C : ℝ) (hf : ∀ τ, ‖f τ‖ ≤ C) : ∫ τ : unitInterval, f τ ≤ C := by
  have h := norm_integral_le_of_norm_le_const (μ := (volume : Measure unitInterval)) (f := f) (C := C)
    (Filter.Eventually.of_forall hf)
  have h1 : ∫ τ : unitInterval, f τ ≤ |∫ τ : unitInterval, f τ| := le_abs_self _
  simp at h
  linarith

/-- **Weighted length of the window contour**: `∑_i ∫ |p_t(γ_i)||γ_i'| ≤ 12 |t| Σ|p_r| ((1+a)(1+h))^{d+1}`. -/
lemma rect_wlen_le {a h : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) (d : ℕ) (t : ℝ) (p : ℕ → ℝ) :
    ∑ i : Fin 6, ∫ τ : unitInterval, ‖(rectPieces a h (pw d t p) (continuous_pw d t p) i).ω
        ((rectPieces a h (pw d t p) (continuous_pw d t p) i).γ τ)‖ *
        ‖(rectPieces a h (pw d t p) (continuous_pw d t p) i).γ' τ‖ ≤
      12 * (|t| * ∑ r ∈ Finset.range (d + 1), |p r|) * ((1 + a) * (1 + h)) ^ (d + 1) := by
  set B : ℝ := (1 + a) * (1 + h) with hB
  have hB1 : 1 ≤ B := by rw [hB]; nlinarith
  set S : ℝ := |t| * ∑ r ∈ Finset.range (d + 1), |p r| with hS
  have hS0 : 0 ≤ S := mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun r _ => abs_nonneg _)
  have hpw : ∀ z ∈ GammaN a h, ‖pw d t p z‖ ≤ S * B ^ d := by
    intro z hz
    have hz1 : ‖z‖ ≤ B := (norm_le_of_gammaN ha hh hz).trans (by rw [hB]; nlinarith)
    unfold pw
    rw [hS, mul_assoc, Finset.sum_mul, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r hr => ?_)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    have hr' : r ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
    have h1 : ‖z‖ ^ r ≤ B ^ d :=
      (pow_le_pow_left₀ (norm_nonneg _) hz1 r).trans (pow_le_pow_right₀ hB1 hr')
    calc |t| * |p r| * ‖z‖ ^ r ≤ |t| * |p r| * B ^ d :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = |t| * (|p r| * B ^ d) := by ring
  have hpiece : ∀ i : Fin 6, ∫ τ : unitInterval, ‖(rectPieces a h (pw d t p) (continuous_pw d t p) i).ω
        ((rectPieces a h (pw d t p) (continuous_pw d t p) i).γ τ)‖ *
        ‖(rectPieces a h (pw d t p) (continuous_pw d t p) i).γ' τ‖ ≤ S * B ^ d * (2 * B) := by
    intro i
    refine integral_I_le _ _ fun τ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)), rect_ω]
    have hτ : (τ : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨τ.2.1, τ.2.2⟩
    refine mul_le_mul (hpw _ (rect_mem ha hh _ _ i hτ)) ?_ (norm_nonneg _)
      (mul_nonneg hS0 (pow_nonneg (by linarith) d))
    rw [rect_γ']
    have h1 := norm_le_of_gammaN ha hh (rect_mem ha hh (pw d t p) (continuous_pw d t p) i
      (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩))
    have h0 := norm_le_of_gammaN ha hh (rect_mem ha hh (pw d t p) (continuous_pw d t p) i
      (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩))
    have := norm_sub_le ((rectPieces a h (pw d t p) (continuous_pw d t p) i).γ 1)
      ((rectPieces a h (pw d t p) (continuous_pw d t p) i).γ 0)
    have hB' : a + h ≤ B := by rw [hB]; nlinarith
    linarith
  calc _ ≤ ∑ _i : Fin 6, S * B ^ d * (2 * B) := Finset.sum_le_sum fun i _ => hpiece i
    _ = 12 * S * B ^ (d + 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, pow_succ]; push_cast; ring

/-! ## 3. PROP-019 -/

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-- **PROP-019** (`Q7A:lem:linearization`, `eq:lincompare`), for the actual model on the PROP-018 event, with
`RootSpectralInputs` and the PROP-026 actual-contour statement `MPLinearizationStatement` as explicit hypotheses.
There are a packet radius `ρ` (`P_{N,u}(𝓔_Nᶜ) → 0`, the same event as `Prop018Scalar.prop018_reconstruct`'s construction),
background constants `d₀ s₁ a₀ c₁` and `C ≥ 0` such that, eventually in `q` (`N = k + q`), for every normalized `Φ ∈ ran P_N`
there is the background family `B` (`c₀ = iκG_μ`, `D`, `s`, `A`) on the `ρ/8`-neighbourhood of `Γ_N` for which, for every
time `t` and every polynomial `p` of degree `≤ d`,
`‖γ^{(k)}_{e^{−iN C_{0,N,p_t}}Φ} − γ^{(k)}_{e^{−iN L_{N,p_t}}Φ}‖₁ ≤ C |t| Σ|p_r| (1+a_N)^{d+1}(ε_N + R_N^{−b} + N^{−1})`,
`p_t = t p` (so `e^{−iNC_{0,N,p_t}} = e^{−itNC_{0,N,p}}`), with `C_{0,N,p_t} = C0op` and `L_{N,p_t} = Lop` along
`Γ_N = rectPieces a_N h p_t`. -/
theorem prop019_linearization (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {h δ d0 : ℝ} {l0 : ℕ} (hηh : eta0 L κ < h)
    (hδ : 0 < δ) (hd0 : 0 < d0) (hin : RootSpectralInputs L κ (μ : Measure ℝ) h δ d0 l0)
    (b pc : ℕ) (hb : 1 ≤ b) (hbpc : b ≤ 2 * pc)
    (θ γ : ℝ) (hθ : 0 < θ) (hγ : 0 < γ) (hsum : 3 * γ + θ < 1) (pt : ℕ) (hpt : 1 < 2 * (pt : ℝ) * θ)
    (d k : ℕ)
    (hMP : ∀ d₀ s₁ a₀ c₁ : ℝ, 0 < d₀ → 0 ≤ s₁ → 0 < a₀ → 0 ≤ c₁ →
      MPLinearizationStatement L κ h k d₀ s₁ a₀ c₁) :
    ∃ ρ : ℝ, 0 < ρ ∧
      Tendsto (fun N : ℕ => (bornMeasure (physBasis L hκ N) u hu).real
        (EN (μ : Measure ℝ) (qAct L κ N) ((N : ℝ) ^ θ) (cutN L θ N) ρ h (eta0 L κ) ((N : ℝ) ^ (-γ)) b)ᶜ)
        atTop (𝓝 0) ∧
      ∃ d₀ s₁ a₀ c₁ C : ℝ, 0 < d₀ ∧ 0 ≤ s₁ ∧ 0 < a₀ ∧ 0 ≤ c₁ ∧ 0 ≤ C ∧
        ∀ᶠ q : ℕ in atTop, ∀ (hN : 1 ≤ k + q) (φ : SymSector ℂ (L2T L) (k + q)), ‖φ‖ = 1 →
          (∀ m ∉ EN (μ : Measure ℝ) (qAct L κ (k + q)) (((k + q : ℕ) : ℝ) ^ θ) (cutN L θ (k + q)) ρ h (eta0 L κ)
              (((k + q : ℕ) : ℝ) ^ (-γ)) b, ⟪meanField_physicalBasis L (k + q) hN hκ m, φ⟫_ℂ = 0) →
          ∃ B : BgFam (NbhdN (cutN L θ (k + q)) h (ρ / 8)) d₀ s₁ a₀ c₁,
            B.c0 = (fun z => Complex.I * κ * Gfull (μ : Measure ℝ) z) ∧ B.D = Df L κ (Gfull (μ : Measure ℝ)) ∧
            B.s = sf L κ (Gfull (μ : Measure ℝ)) ∧ B.A = Af κ (Gfull (μ : Measure ℝ)) ∧
            ∀ (t : ℝ) (p : ℕ → ℝ),
              QuantumNLS.TraceClass.traceNorm
                (reducedDensityPower k q
                    ((evol (((((k + q : ℕ) : ℝ) : ℂ)) •
                      C0op (nu 6) (fun θ' => normalizedTransfer L κ (k + q)
                        (zθ (rectPieces (cutN L θ (k + q)) h (pw d t p) (continuous_pw d t p)) θ'))
                        (uθ κ (rectPieces (cutN L θ (k + q)) h (pw d t p) (continuous_pw d t p)))
                        (gθ (rectPieces (cutN L θ (k + q)) h (pw d t p) (continuous_pw d t p)) B)) 1 φ :
                      SymSector ℂ (L2T L) (k + q)) : HilbertTensorPower ℂ (L2T L) (k + q)) -
                  reducedDensityPower k q
                    ((evol (((((k + q : ℕ) : ℝ) : ℂ)) •
                      Lop (nu 6) (fun θ' => normalizedTransfer L κ (k + q)
                        (zθ (rectPieces (cutN L θ (k + q)) h (pw d t p) (continuous_pw d t p)) θ'))
                        (uθ κ (rectPieces (cutN L θ (k + q)) h (pw d t p) (continuous_pw d t p)))
                        (dθ (rectPieces (cutN L θ (k + q)) h (pw d t p) (continuous_pw d t p)) B)) 1 φ :
                      SymSector ℂ (L2T L) (k + q)) : HilbertTensorPower ℂ (L2T L) (k + q))) ≤
                ENNReal.ofReal (C * (|t| * ∑ r ∈ Finset.range (d + 1), |p r|) *
                  (1 + cutN L θ (k + q)) ^ (d + 1) *
                  ((((k + q : ℕ) : ℝ)) ^ (-γ) + 1 / ((((k + q : ℕ) : ℝ)) ^ θ) ^ b + 1 / ((k + q : ℕ) : ℝ))) := by
  have hL : 0 < L := Fact.out
  obtain ⟨ρ, hρ0, h2ρ, hprob, C0, M, η, r, K, Kd, hM1, hη, hr0, hK0, hev⟩ :=
    moving_contour_bundle hκ u hu hμ hηh hδ hd0 hin b pc hb hbpc θ γ hθ hγ hsum pt hpt
  have hh : 0 < h := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hM0 : 0 < M := by linarith
  obtain ⟨C, hC0, hCb⟩ := hMP η (M + M * M) (1 / M) (κ * (2 * K + 1 / r)) hη (by positivity) (by positivity)
    (by positivity)
  refine ⟨ρ, hρ0, hprob, η, M + M * M, 1 / M, κ * (2 * K + 1 / r),
    C * (2 * Real.pi * κ)⁻¹ * max Kd 0 * (12 * (1 + h) ^ (d + 1)), hη, by positivity, by positivity,
    by positivity, by positivity, ?_⟩
  set E : (N : ℕ) → Set (MArr N) := fun N =>
    EN (μ : Measure ℝ) (qAct L κ N) ((N : ℝ) ^ θ) (cutN L θ N) ρ h (eta0 L κ) ((N : ℝ) ^ (-γ)) b with hE
  have hdev := deviation_of_bundle hκ (μ : Measure ℝ) (h := h) (ρ := ρ) (Kd := Kd) (θ := θ) (γ := γ) (b := b) E
    (hev.mono fun N hN m hm z hz => ⟨(hN m hm z hz).1.1, (hN m hm z hz).2.2.2.2.2.2.2.2.2 0⟩)
  have hkq : Tendsto (fun q : ℕ => k + q) atTop atTop := by
    simpa [Nat.add_comm] using tendsto_add_atTop_nat k
  filter_upwards [hkq.eventually (hev.and (hdev.and (regime_eventually hL hθ hγ 1 0)))]
    with q ⟨hevN, hdevN, hreg⟩
  intro hN φ hφ hsupp
  have hNr : (0 : ℝ) < ((k + q : ℕ) : ℝ) := by exact_mod_cast hN
  set a := cutN L θ (k + q) with ha
  have ha2 : 2 ≤ a := by linarith [hreg.1, hreg.2.2.1]
  -- a label of the event (the event is nonempty since `Φ ≠ 0`)
  obtain ⟨m0, hm0⟩ : ∃ m, m ∈ E (k + q) := by
    by_contra hne
    push Not at hne
    have hs := QuantumNLS.RootMeasureTransfer.hasSum_norm_sq (meanField_physicalBasis L (k + q) hN hκ) φ
    have h0 : (fun m => ‖⟪meanField_physicalBasis L (k + q) hN hκ m, φ⟫_ℂ‖ ^ 2) = fun _ => (0 : ℝ) := by
      funext m; rw [hsupp m (hne m), norm_zero]; ring
    rw [h0] at hs
    have := hs.unique hasSum_zero
    rw [hφ] at this; norm_num at this
  -- the background family
  have hP := fun z (hz : z ∈ NbhdN a h (ρ / 8)) => hevN m0 hm0 z hz
  have hGc : ∀ z ∈ NbhdN a h (ρ / 8), ContinuousAt (Gfull (μ : Measure ℝ)) z := fun z hz =>
    (hP z hz).2.2.2.2.1.continuousAt
  have hAc : ∀ z ∈ NbhdN a h (ρ / 8), ContinuousAt (Af κ (Gfull (μ : Measure ℝ))) z := fun z hz =>
    ((hGc z hz).const_mul (Complex.I * κ)).cexp
  have hec : ∀ z, ContinuousAt (ef L) z := fun z => (hasDerivAt_ef L z).continuousAt
  have hAlow : ∀ z ∈ NbhdN a h (ρ / 8), 1 / M ≤ ‖Af κ (Gfull (μ : Measure ℝ)) z‖ := fun z hz => by
    have hAi := (hP z hz).2.2.2.2.2.2.2.1
    have hAn : 0 < ‖Af κ (Gfull (μ : Measure ℝ)) z‖ := norm_pos_iff.2 (Complex.exp_ne_zero _)
    rw [norm_inv] at hAi
    exact (one_div_le hM0 hAn).2 (by rw [one_div]; exact hAi)
  have hGle : ∀ z ∈ NbhdN a h (ρ / 8), ‖Gfull (μ : Measure ℝ) z‖ ≤ 2 * K + 1 / r := fun z hz => by
    have hPz := hP z hz
    have hG1 := hPz.2.2.1
    have hN1 : 1 ≤ ((k + q : ℕ) : ℝ) ^ θ := hreg.1
    have hRb : 1 / (((k + q : ℕ) : ℝ) ^ θ) ^ b ≤ 1 := by
      rw [div_le_one (by positivity)]; exact one_le_pow₀ hN1
    have hGN : ‖GN (qAct L κ (k + q) m0) z‖ ≤ 1 / r := by
      unfold GN
      rw [norm_mul]
      have hs : ‖∑ j, 1 / (z - (qAct L κ (k + q) m0 j : ℂ))‖ ≤ ∑ _j : Fin (k + q), 1 / r := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [norm_div, norm_one]
        exact one_div_le_one_div_of_le hr0 (hPz.2.2.2.1 j)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
      calc ‖1 / ((k + q : ℕ) : ℂ)‖ * ‖∑ j, 1 / (z - (qAct L κ (k + q) m0 j : ℂ))‖ ≤ (1 / ((k + q : ℕ) : ℝ)) * (((k + q : ℕ) : ℝ) * (1 / r)) := by
            refine mul_le_mul (le_of_eq ?_) hs (norm_nonneg _) (by positivity)
            rw [norm_div, norm_one, Complex.norm_natCast]
        _ = 1 / r := by field_simp
    have := norm_sub_le (Gfull (μ : Measure ℝ) z - GN (qAct L κ (k + q) m0) z) (-GN (qAct L κ (k + q) m0) z)
    rw [sub_neg_eq_add, sub_add_cancel, norm_neg] at this
    have hKb : K * (((k + q : ℕ) : ℝ) ^ (-γ) + 1 / (((k + q : ℕ) : ℝ) ^ θ) ^ b) ≤ K * 2 :=
      mul_le_mul_of_nonneg_left (by linarith [hreg.2.2.2.2]) hK0
    linarith
  let B : BgFam (NbhdN a h (ρ / 8)) η (M + M * M) (1 / M) (κ * (2 * K + 1 / r)) :=
    { c0 := fun z => Complex.I * κ * Gfull (μ : Measure ℝ) z
      D := Df L κ (Gfull (μ : Measure ℝ))
      s := sf L κ (Gfull (μ : Measure ℝ))
      A := Af κ (Gfull (μ : Measure ℝ))
      hc0 := fun z hz => (continuousAt_const.mul (hGc z hz.1)).continuousWithinAt
      hD := fun z hz => ((hAc z hz.1).sub ((hec z).div (hAc z hz.1) (Complex.exp_ne_zero _))).continuousWithinAt
      hs := fun z hz => ((hAc z hz.1).add ((hec z).div (hAc z hz.1) (Complex.exp_ne_zero _))).continuousWithinAt
      hA := fun z hz => (hAc z hz.1).continuousWithinAt
      bg := fun z hz _ => ⟨hη, by positivity, by positivity, (hP z hz).2.2.2.2.2.1,
        norm_sf_le (hP z hz).2.2.2.2.2.2.1 (hP z hz).2.2.2.2.2.2.2.1 (hP z hz).2.2.2.2.2.2.2.2.1, hAlow z hz,
        A_eq_half L κ _ z⟩
      c0le := fun z hz _ => by
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hκ.le]
        exact mul_le_mul_of_nonneg_left (hGle z hz) hκ.le
      s_le := fun z hz =>
        norm_sf_le (hP z hz).2.2.2.2.2.2.1 (hP z hz).2.2.2.2.2.2.2.1 (hP z hz).2.2.2.2.2.2.2.2.1 }
  refine ⟨B, rfl, rfl, rfl, rfl, fun t p => ?_⟩
  -- apply the PROP-026 actual-contour statement on `Γ_N`
  set δN : ℝ := ((k + q : ℕ) : ℝ) ^ (-γ) + 1 / (((k + q : ℕ) : ℝ) ^ θ) ^ b + 1 / ((k + q : ℕ) : ℝ) with hδNdef
  have hδN0 : 0 ≤ δN := by
    have : 0 < ((k + q : ℕ) : ℝ) ^ θ := Real.rpow_pos_of_pos hNr θ
    have : 0 < ((k + q : ℕ) : ℝ) ^ (-γ) := Real.rpow_pos_of_pos hNr _
    rw [hδNdef]; positivity
  have hZ : ∀ i, ∀ τ ∈ Icc (0 : ℝ) 1,
      (rectPieces a h (pw d t p) (continuous_pw d t p) i).γ τ ∈ NbhdN a h (ρ / 8) := fun i τ hτ =>
    ⟨_, rect_mem (by linarith) hh.le _ _ i hτ, by rw [sub_self, norm_zero]; positivity⟩
  have hmain := hCb q hN (NbhdN a h (ρ / 8)) (rectPieces a h (pw d t p) (continuous_pw d t p)) hZ
    (fun i τ hτ => (gammaN_abs (by linarith) hh.le (rect_mem (by linarith) hh.le _ _ i hτ)).2)
    (fun i τ hτ => rect_im_ne hh _ _ i hτ) B φ hφ (fun _ => max Kd 0 * δN)
    (fun _ => mul_nonneg (le_max_right _ _) hδN0)
    (fun i τ hτ => by
      have := hdevN hN φ hsupp _ (hZ i τ hτ)
      rw [hφ, mul_one] at this
      exact this)
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  have hw := rect_wlen_le (by linarith : (0 : ℝ) ≤ a) hh.le d t p
  rw [← Finset.mul_sum]
  have hk0 : 0 ≤ C * (2 * Real.pi * κ)⁻¹ * max Kd 0 := by positivity
  calc C * ((2 * Real.pi * κ)⁻¹ * (max Kd 0 * δN * ∑ i : Fin 6, ∫ τ : unitInterval,
        ‖(rectPieces a h (pw d t p) (continuous_pw d t p) i).ω
          ((rectPieces a h (pw d t p) (continuous_pw d t p) i).γ τ)‖ *
        ‖(rectPieces a h (pw d t p) (continuous_pw d t p) i).γ' τ‖))
      = C * (2 * Real.pi * κ)⁻¹ * max Kd 0 * δN * ∑ i : Fin 6, ∫ τ : unitInterval,
        ‖(rectPieces a h (pw d t p) (continuous_pw d t p) i).ω
          ((rectPieces a h (pw d t p) (continuous_pw d t p) i).γ τ)‖ *
        ‖(rectPieces a h (pw d t p) (continuous_pw d t p) i).γ' τ‖ := by ring
    _ ≤ C * (2 * Real.pi * κ)⁻¹ * max Kd 0 * δN *
        (12 * (|t| * ∑ r ∈ Finset.range (d + 1), |p r|) * ((1 + a) * (1 + h)) ^ (d + 1)) :=
        mul_le_mul_of_nonneg_left hw (mul_nonneg hk0 hδN0)
    _ = C * (2 * Real.pi * κ)⁻¹ * max Kd 0 * (12 * (1 + h) ^ (d + 1)) *
        (|t| * ∑ r ∈ Finset.range (d + 1), |p r|) * (1 + a) ^ (d + 1) * δN := by
        rw [mul_pow]; ring

end QuantumNLS.Prop019Linearization

#print axioms QuantumNLS.Prop019Linearization.rect_mem
#print axioms QuantumNLS.Prop019Linearization.rect_wlen_le
#print axioms QuantumNLS.Prop019Linearization.prop019_linearization
