import QuantumNLS.Prop018Bundle
import QuantumNLS.Prop018Period
import QuantumNLS.BetheSpectralCharges
import QuantumNLS.RootMeasureTransfer

/-!
# PROP-018 (`Q7A:prop:reconstruct`), `eq:phase`: the unscaled error of the two-term reconstruction

Source: `window_reconstruction.tex`, `Q7A:eq:chart`–`Q7A:eq:C1` and `Q7A:prop:reconstruct`, `eq:phase`:
`‖(Σ_r p_r Q_{N,r} − N C_{0,N,p} − C_{1,N,p}) P_N‖ ≤ C_p (1+a)^{d+1}/N` for all large `N`.

All operators involved are diagonal in the actual Bethe basis `Ψ_{N,m}` (the transfer `S_N(z)` has eigenvalue
`s_N(z; q(m))`, the charge `Q_{N,r}` has eigenvalue `Σ_j q_j(m)^r`), so the operator norm on `ran P_N` is the supremum over
`m ∈ 𝓔_N` of the eigenvalue errors.  This module proves the eigenvalue statement for every label of the event, uniformly:
* `lam`, `qch`: the charts `λ(z,w)` and `q(z,w,v)` of `Q7A:eq:chart`, `Q7A:eq:qchart` (Taylor = principal branches);
* `C0ev f`, `C1ev qt`: the eigenvalues of `C_{0,N,p}`, `C_{1,N,p}` on `Ψ_{N,m}` for **arbitrary** extensions `f_z(w)`,
  `q̃_z(w,v)` agreeing with `λ`, `q` on disks of a fixed radius `r₀ > 0` around the background `(s(z), s'(z))`;
* `charge_symbol`: `Σ_r p_r ⋅ eigenvalue(Q_{N,r})(m) = Σ_j p(q_j(m))` for the actual full charges;
* `corrf_eq_qch`: the two-term correction is exactly `q(z, s_N, s_N')` (`a_N' = (a_N s_N' − iLe)/d(z,s_N)`);
* `phase_det`: the deterministic estimate (exact polynomial period + integrated `O(N^{−2})` remainder);
* **`prop018_phase`**: `eq:phase` on `𝓔_N` for the actual model, with `C_p = Cp ⋅ Σ_r |p_r|` (uniform for coefficients in a
  compact set) and the `N`-threshold independent of `p` and of the label.
`RootSpectralInputs` is carried as an explicit hypothesis (assigned to R-7E0532E7).
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology Complex Set
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace QuantumNLS.Prop018Phase

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheLabels (MArr arrRoots)
open QuantumNLS.EmpiricalRapidity (bornMeasure)
open QuantumNLS.BulkResponseActual (physBasis IsLimitingRapidityMeasure)
open QuantumNLS.Extrapolation (Gfull GN)
open QuantumNLS.RootEvent (EN)
open QuantumNLS.ResolventNeighborhood (GammaN NbhdN sNsrc sLimsrc)
open QuantumNLS.PROP018Probability (cutN regime_eventually)
open QuantumNLS.Prop017Quantum (qAct eta0)
open QuantumNLS.Prop017Physical (RootSpectralInputs)
open QuantumNLS.PeriodReconstructionCore QuantumNLS.PeriodTwoTerm
open QuantumNLS.PeriodReconstruction (Gam)
open QuantumNLS.LabelExactPeriod (rectIntegral rectIntegral_sum)
open QuantumNLS.Prop018Period (poly prim root_period_poly period_err continuous_poly)
open QuantumNLS.Prop018Bundle (moving_contour_bundle)
open QuantumNLS.HaarSummableReconstruction (contAt_gen)
open QuantumNLS.BetheSpectralCharges (eigenvalue)

/-! ## 1. The charts -/

section Charts

variable (L κ : ℝ) (G : ℂ → ℂ)

/-- `d(z,w) = D(z)(1 + (w² − s(z)²)/D(z)²)^{1/2}` (`Q7A:eq:chart`). -/
def dch (z w : ℂ) : ℂ := Df L κ G z * (1 + (w ^ 2 - sf L κ G z ^ 2) / Df L κ G z ^ 2) ^ ((2 : ℂ)⁻¹)

/-- `a(z,w) = (w + d(z,w))/2` (`Q7A:eq:chart`). -/
def ach (z w : ℂ) : ℂ := (w + dch L κ G z w) / 2

/-- `λ(z,w) = iκG(z) + log(a(z,w)/A(z))` (`Q7A:eq:chart`). -/
def lam (z w : ℂ) : ℂ := I * κ * G z + log (ach L κ G z w / Af κ G z)

/-- `q(z,w,v) = e(z)(a(z,w)v − iLe(z))/(a(z,w)² d(z,w)²)` (`Q7A:eq:qchart`). -/
def qch (z w v : ℂ) : ℂ :=
  ef L z * (ach L κ G z w * v - I * L * ef L z) / (ach L κ G z w ^ 2 * dch L κ G z w ^ 2)

end Charts

/-- `log a_N = λ(z, s_N)`. -/
lemma logaNf_eq_lam (L κ c : ℝ) (G : ℂ → ℂ) {N : ℕ} (q : Fin N → ℝ) (z : ℂ) :
    logaNf L κ c G q z = lam L κ G z (sNf L c q z) := rfl

/-- The two-term correction is exactly `q(z, s_N, s_N')`. -/
lemma corrf_eq_qch {L κ c : ℝ} {G : ℂ → ℂ} {N : ℕ} {q : Fin N → ℝ} {z : ℂ}
    (hG : DifferentiableAt ℂ G z) (hGc : ∀ᶠ w in 𝓝 z, Df L κ G w ≠ 0)
    (hz : ∀ j, 2 * |c| < ‖z - q j‖) (hW : 1 + Wf L κ c G q z ∈ slitPlane)
    (ha : aNf L κ c G q z ≠ 0) (hDN : DNf L κ c G q z ≠ 0) :
    corrf L κ c G q z = qch L κ G z (sNf L c q z) (deriv (sNf L c q) z) := by
  have h1 := deriv_aN_mul_DN L κ c hG hGc hz hW
  have hq := quad L κ c G q hGc.self_of_nhds
  rw [(hasDerivAt_sN L hz).deriv]
  have hach : ach L κ G z (sNf L c q z) = aNf L κ c G q z := rfl
  have hdch : dch L κ G z (sNf L c q z) = DNf L κ c G q z := rfl
  unfold qch corrf
  rw [hach, hdch]
  have hDNe : DNf L κ c G q z = 2 * aNf L κ c G q z - sNf L c q z := by unfold aNf; ring
  have hae : aNf L κ c G q z ^ 2 - ef L z = aNf L κ c G q z * DNf L κ c G q z := by
    rw [hDNe]; linear_combination -hq
  rw [hae, div_eq_div_iff (mul_ne_zero ha (mul_ne_zero ha hDN))
    (mul_ne_zero (pow_ne_zero 2 ha) (pow_ne_zero 2 hDN))]
  linear_combination (ef L z * aNf L κ c G q z ^ 2 * DNf L κ c G q z) * h1

/-- The source transfer symbol is `sNf`. -/
lemma sNsrc_eq (κ L : ℝ) {N : ℕ} (q : Fin N → ℝ) : sNsrc κ L q = sNf L (κ / N) q := by
  funext z
  simp only [sNsrc, sNf, ANf, ef]
  push_cast
  ring_nf

lemma sLimsrc_eq (κ L : ℝ) (μ : Measure ℝ) : sLimsrc κ L μ = sf L κ (Gfull μ) := rfl

/-! ## 2. The actual charges -/

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-- The eigenvalue of the actual full charge `Q_{N,r}` on `Ψ_{N,m}` is `Σ_j q_j(m)^r`. -/
lemma eigenvalue_eq (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (m : MArr N) (r : ℕ) :
    eigenvalue L N (κ / N) r m = ∑ j, qAct L κ N m j ^ r := by
  have hL : 0 < L := Fact.out
  have hc : 0 < κ / (N : ℝ) := div_pos hκ (Nat.cast_pos.2 hN)
  unfold eigenvalue QuantumNLS.BetheSpectralCharges.rapidity
  have hroot : ∀ i, QuantumNLS.BetheSmooth.sourceRoots L
      ((QuantumNLS.BetheConditionalBasis.labelArr N).symm m).val (κ / N) i =
      arrRoots L (κ / N) m (Fin.rev i) := by
    intro i
    have := QuantumNLS.RootMeasureTransfer.label_val m
    rw [show ((QuantumNLS.BetheConditionalBasis.labelArr N).symm m).val =
      (QuantumNLS.NormalityBridge.label m).1 from rfl, this]
    exact QuantumNLS.BetheLabels.sourceRoots_eq_roots_rev hL hc _ i
  simp only [hroot]
  have := Equiv.sum_comp Fin.revPerm (fun j => arrRoots L (κ / N) m j ^ r)
  simp only [Fin.revPerm_apply] at this
  exact this

/-- `Σ_r p_r Q_{N,r}` acts on `Ψ_{N,m}` by `Σ_j p(q_j(m))`. -/
lemma charge_symbol (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (m : MArr N) (p : ℕ → ℝ) (d : ℕ) :
    ∑ r ∈ Finset.range (d + 1), p r * eigenvalue L N (κ / N) r m =
      ∑ j, (poly p d (qAct L κ N m j : ℂ)).re := by
  simp only [eigenvalue_eq hκ hN, poly, Finset.mul_sum, re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun r _ => ?_
  rw [← ofReal_pow, ← ofReal_mul, ofReal_re]

/-! ## 3. The eigenvalues of `C₀`, `C₁` and the scalar -/

/-- Eigenvalue of `C_{0,N,p} = −(2πκ)^{−1} Re ∮_{Γ_N} p(z) f_z(S_N(z)) dz` on `Ψ_{N,m}` (`Q7A:eq:C0`). -/
def C0ev (L κ : ℝ) (f : ℂ → ℂ → ℂ) (θ h : ℝ) (p : ℕ → ℝ) (d N : ℕ) (m : MArr N) : ℝ :=
  -(1 / (2 * Real.pi * κ)) *
    (rectIntegral (fun z => poly p d z * f z (sNf L (κ / N) (qAct L κ N m) z)) (-cutN L θ N) (cutN L θ N) h).re

/-- Eigenvalue of `C_{1,N,p} = Re (i/2π) ∮_{Γ_N} p(z) q̃_z(S_N(z), S_N'(z)) dz` on `Ψ_{N,m}` (`Q7A:eq:C1`). -/
def C1ev (L κ : ℝ) (qt : ℂ → ℂ → ℂ → ℂ) (θ h : ℝ) (p : ℕ → ℝ) (d N : ℕ) (m : MArr N) : ℝ :=
  ((I / (2 * Real.pi)) * rectIntegral (fun z => poly p d z * qt z (sNf L (κ / N) (qAct L κ N m) z)
    (deriv (sNf L (κ / N) (qAct L κ N m)) z)) (-cutN L θ N) (cutN L θ N) h).re

/-! ## 4. Geometry of `Γ_N` -/

lemma gam_sub_GammaN {a h : ℝ} {z : ℂ} (hz : z ∈ Gam (-a) a h) : z ∈ GammaN a h := by
  rcases hz with ⟨⟨h1, h2⟩, h3 | h3⟩ | ⟨⟨h1, h2⟩, h3 | h3⟩
  · exact Or.inr ⟨Or.inr h3, abs_le.2 ⟨h1, h2⟩⟩
  · exact Or.inr ⟨Or.inl h3, abs_le.2 ⟨h1, h2⟩⟩
  · exact Or.inl ⟨Or.inr h3, abs_le.2 ⟨h1, h2⟩⟩
  · exact Or.inl ⟨Or.inl h3, abs_le.2 ⟨h1, h2⟩⟩

lemma gam_sub_nbhd {a h ρ : ℝ} {z w : ℂ} (hz : z ∈ Gam (-a) a h) (hw : ‖w - z‖ ≤ ρ) :
    w ∈ NbhdN a h ρ :=
  ⟨z, gam_sub_GammaN hz, hw⟩

lemma norm_le_of_gam {a h : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) {z : ℂ} (hz : z ∈ Gam (-a) a h) :
    ‖z‖ ≤ a + h := by
  have h0 := Complex.norm_le_abs_re_add_abs_im z
  have : |z.re| ≤ a ∧ |z.im| ≤ h := by
    rcases hz with ⟨⟨h1, h2⟩, h3 | h3⟩ | ⟨⟨h1, h2⟩, h3 | h3⟩
    · exact ⟨abs_le.2 ⟨h1, h2⟩, by rw [h3, abs_neg, abs_of_nonneg hh]⟩
    · exact ⟨abs_le.2 ⟨h1, h2⟩, by rw [h3, abs_of_nonneg hh]⟩
    · exact ⟨by rw [h3, abs_neg, abs_of_nonneg ha], abs_le.2 ⟨h1, h2⟩⟩
    · exact ⟨by rw [h3, abs_of_nonneg ha], abs_le.2 ⟨h1, h2⟩⟩
  linarith [this.1, this.2]

lemma norm_poly_le (p : ℕ → ℝ) (d : ℕ) {z : ℂ} {B : ℝ} (hB : 1 ≤ B) (hz : ‖z‖ ≤ B) :
    ‖poly p d z‖ ≤ (∑ r ∈ Finset.range (d + 1), |p r|) * B ^ d := by
  unfold poly
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r hr => ?_)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hr' : r ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc ‖z‖ ^ r ≤ B ^ r := pow_le_pow_left₀ (norm_nonneg _) hz r
    _ ≤ B ^ d := pow_le_pow_right₀ hB hr'

/-! ## 5. The deterministic estimate -/

/-- **Deterministic `eq:phase`**: on a rectangle `Γ = ∂([−a,a] × [−h,h])` containing every root and every shifted root, with
the two-term remainder `≤ C/N²` on `Γ`, the eigenvalue error is at most
`(κ² + 4C(1+h)^{d+1}/(2πκ)) Σ_r|p_r| (1+a)^{d+1}/N`. -/
theorem phase_det {L κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) {G : ℂ → ℂ} {q : Fin N → ℝ}
    {a h C : ℝ} (ha : 2 ≤ a) (hh : 0 < h) (hC : 0 ≤ C)
    (hq : ∀ j, |q j| ≤ a / 2) (hch : 2 * (κ / N) < h) (hc1 : 2 * (κ / N) < 1)
    (hdist : ∀ z ∈ Gam (-a) a h, ∀ j, 2 * |κ / (N : ℝ)| < ‖z - (q j : ℂ)‖)
    (hcont : ∀ z ∈ Gam (-a) a h, ContinuousAt (logaNf L κ (κ / N) G q) z ∧
      ContinuousAt (corrf L κ (κ / N) G q) z ∧ ContinuousAt (ellf (κ / N) q) z)
    (hrem : ∀ z ∈ Gam (-a) a h, ‖ellf (κ / N) q z - logaNf L κ (κ / N) G q z +
      I * κ / (N : ℂ) * corrf L κ (κ / N) G q z‖ ≤ C / (N : ℝ) ^ 2)
    (p : ℕ → ℝ) (d : ℕ) :
    |∑ j, (poly p d (q j : ℂ)).re
      - (N : ℝ) * (-(1 / (2 * Real.pi * κ)) *
          (rectIntegral (fun z => poly p d z * logaNf L κ (κ / N) G q z) (-a) a h).re)
      - ((I / (2 * Real.pi)) * rectIntegral (fun z => poly p d z * corrf L κ (κ / N) G q z) (-a) a h).re| ≤
      (κ ^ 2 + 4 * C * (1 + h) ^ (d + 1) / (2 * Real.pi * κ)) *
        (∑ r ∈ Finset.range (d + 1), |p r|) * (1 + a) ^ (d + 1) / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hc0 : 0 < κ / (N : ℝ) := div_pos hκ hNr
  have hab : -a ≤ a := by linarith
  have hh0 : 0 ≤ h := hh.le
  have hpi : 0 < Real.pi := Real.pi_pos
  set c : ℝ := κ / N with hcdef
  set S : ℝ := ∑ r ∈ Finset.range (d + 1), |p r| with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun r _ => abs_nonneg _
  set rem : ℂ → ℂ := fun z => ellf c q z - logaNf L κ c G q z + I * κ / (N : ℂ) * corrf L κ c G q z
    with hremdef
  have hPc : Continuous (poly p d) := continuous_poly p d
  have hcL : ∀ z ∈ Gam (-a) a h, ContinuousAt (fun z => poly p d z * logaNf L κ c G q z) z :=
    fun z hz => hPc.continuousAt.mul (hcont z hz).1
  have hcC : ∀ z ∈ Gam (-a) a h, ContinuousAt (fun z => poly p d z * corrf L κ c G q z) z :=
    fun z hz => hPc.continuousAt.mul (hcont z hz).2.1
  have hcR : ∀ z ∈ Gam (-a) a h, ContinuousAt (fun z => poly p d z * rem z) z := fun z hz =>
    hPc.continuousAt.mul ((((hcont z hz).2.2).sub (hcont z hz).1).add
      (continuousAt_const.mul (hcont z hz).2.1))
  -- the integrated two-term identity
  have e3 : rectIntegral (fun z => poly p d z * ellf c q z) (-a) a h =
      rectIntegral (fun z => poly p d z * logaNf L κ c G q z) (-a) a h +
        (-(I * κ / (N : ℂ))) * rectIntegral (fun z => poly p d z * corrf L κ c G q z) (-a) a h +
        rectIntegral (fun z => poly p d z * rem z) (-a) a h := by
    have pt : (fun z => poly p d z * ellf c q z) = fun z =>
        (poly p d z * logaNf L κ c G q z + (-(I * κ / (N : ℂ))) * (poly p d z * corrf L κ c G q z)) +
          poly p d z * rem z := by
      funext z; simp only [hremdef]; ring
    rw [pt, rectIntegral_add (f := fun z => poly p d z * logaNf L κ c G q z +
        (-(I * κ / (N : ℂ))) * (poly p d z * corrf L κ c G q z)) (g := fun z => poly p d z * rem z) hab hh0
        (fun z hz => (hcL z hz).add (continuousAt_const.mul (hcC z hz))) hcR,
      rectIntegral_add (f := fun z => poly p d z * logaNf L κ c G q z)
        (g := fun z => (-(I * κ / (N : ℂ))) * (poly p d z * corrf L κ c G q z)) hab hh0 hcL
        (fun z hz => continuousAt_const.mul (hcC z hz)), rectIntegral_const_mul]
  -- the exact polynomial period of `ℓ_N`
  have e4 : rectIntegral (fun z => poly p d z * ellf c q z) (-a) a h =
      ∑ j, 2 * Real.pi * I * (prim p d (q j : ℂ) - prim p d ((q j : ℂ) - I * c)) := by
    have pt : (fun z => poly p d z * ellf c q z) = fun z => ∑ j, poly p d z * log (1 + I * c / (z - q j)) := by
      funext z; unfold ellf; rw [Finset.mul_sum]
    have hct : ∀ j, ∀ z ∈ Gam (-a) a h, ContinuousAt (fun z => poly p d z * log (1 + I * c / (z - q j))) z :=
      fun j z hz => hPc.continuousAt.mul (hasDerivAt_log_term (hdist z hz j)).continuousAt
    rw [pt, rectIntegral_sum Finset.univ (fun j _ x hx => hct j _ (bot_mem hab hx))
      (fun j _ x hx => hct j _ (top_mem hab hx)) (fun j _ y hy => hct j _ (right_mem hh0 hy))
      (fun j _ y hy => hct j _ (left_mem hh0 hy))]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hqj := abs_le.1 (hq j)
    exact root_period_poly hc0 (by linarith) (by rw [abs_of_pos (by linarith)]; linarith)
      (by rw [abs_of_neg (by linarith)]; linarith) (by linarith) (by linarith) (by linarith) p d
  -- the complex identity
  set k : ℝ := (N : ℝ) / (2 * Real.pi * κ) with hkdef
  have hk0 : 0 ≤ k := by rw [hkdef]; positivity
  set Y : Fin N → ℂ := fun j => prim p d (q j : ℂ) - prim p d ((q j : ℂ) - I * c) with hYdef
  have hid : (k : ℂ) * rectIntegral (fun z => poly p d z * logaNf L κ c G q z) (-a) a h -
      (I / (2 * Real.pi)) * rectIntegral (fun z => poly p d z * corrf L κ c G q z) (-a) a h =
      (∑ j, ((1 / c : ℝ) : ℂ) * (I * Y j)) - (k : ℂ) * rectIntegral (fun z => poly p d z * rem z) (-a) a h := by
    have hT0 : rectIntegral (fun z => poly p d z * logaNf L κ c G q z) (-a) a h =
        rectIntegral (fun z => poly p d z * ellf c q z) (-a) a h +
          (I * κ / (N : ℂ)) * rectIntegral (fun z => poly p d z * corrf L κ c G q z) (-a) a h -
          rectIntegral (fun z => poly p d z * rem z) (-a) a h := by
      rw [e3]; ring
    have hsum : (∑ j, ((1 / c : ℝ) : ℂ) * (I * Y j)) =
        (k : ℂ) * ∑ j, 2 * Real.pi * I * (prim p d (q j : ℂ) - prim p d ((q j : ℂ) - I * c)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hκc : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
      have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hNr.ne'
      have hpic : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
      simp only [hYdef, hcdef, hkdef]
      push_cast
      field_simp
    rw [hsum, hT0, e4]
    have hκc : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
    have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hNr.ne'
    have hpic : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
    simp only [hkdef]
    push_cast
    field_simp
    ring
  have hre := congrArg Complex.re hid
  rw [sub_re, sub_re, re_ofReal_mul, re_ofReal_mul, re_sum] at hre
  simp only [re_ofReal_mul] at hre
  -- rewrite the error
  have hE : ∑ j, (poly p d (q j : ℂ)).re
      - (N : ℝ) * (-(1 / (2 * Real.pi * κ)) *
          (rectIntegral (fun z => poly p d z * logaNf L κ c G q z) (-a) a h).re)
      - ((I / (2 * Real.pi)) * rectIntegral (fun z => poly p d z * corrf L κ c G q z) (-a) a h).re =
      (∑ j, ((poly p d (q j : ℂ)).re - (-(1 / c) * (I * Y j).re))) -
        k * (rectIntegral (fun z => poly p d z * rem z) (-a) a h).re := by
    have h1 : (N : ℝ) * (-(1 / (2 * Real.pi * κ)) *
        (rectIntegral (fun z => poly p d z * logaNf L κ c G q z) (-a) a h).re) =
        -(k * (rectIntegral (fun z => poly p d z * logaNf L κ c G q z) (-a) a h).re) := by
      rw [hkdef]; ring
    have h2 : (∑ j, ((poly p d (q j : ℂ)).re - (-(1 / c) * (I * Y j).re))) =
        (∑ j, (poly p d (q j : ℂ)).re) + ∑ j, 1 / c * (I * Y j).re := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h1, h2]
    linarith [hre]
  -- the bound
  set B : ℝ := (1 + a) * (1 + h) with hBdef
  have hB1 : 1 ≤ B := by rw [hBdef]; nlinarith
  have hperiod : ∀ j, |(poly p d (q j : ℂ)).re - (-(1 / c) * (I * Y j).re)| ≤ c ^ 2 * (S * (1 + a) ^ (d + 1)) := by
    intro j
    rw [abs_sub_comm]
    refine (period_err p d (q j) c hc0 (by linarith)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    rw [hSdef, Finset.sum_mul]
    refine Finset.sum_le_sum fun r hr => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have hr' : r ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
    have hqa : 1 + |q j| ≤ 1 + a := by linarith [hq j]
    calc (1 + |q j|) ^ (r + 1) ≤ (1 + a) ^ (r + 1) := pow_le_pow_left₀ (by positivity) hqa _
      _ ≤ (1 + a) ^ (d + 1) := pow_le_pow_right₀ (by linarith) (by omega)
  have hremI : ‖rectIntegral (fun z => poly p d z * rem z) (-a) a h‖ ≤
      (2 * (a - -a) + 4 * h) * (S * B ^ d * (C / (N : ℝ) ^ 2)) := by
    refine norm_rectIntegral_le hab hh0 fun z hz => ?_
    rw [norm_mul]
    have hz1 : ‖z‖ ≤ B := (norm_le_of_gam (by linarith) hh0 hz).trans (by rw [hBdef]; nlinarith)
    exact mul_le_mul (norm_poly_le p d hB1 hz1) (hrem z hz) (norm_nonneg _)
      (mul_nonneg hS0 (pow_nonneg (by linarith) d))
  have hlen : 2 * (a - -a) + 4 * h ≤ 4 * B := by rw [hBdef]; nlinarith
  rw [hE]
  calc |(∑ j, ((poly p d (q j : ℂ)).re - (-(1 / c) * (I * Y j).re))) -
        k * (rectIntegral (fun z => poly p d z * rem z) (-a) a h).re|
      ≤ |∑ j, ((poly p d (q j : ℂ)).re - (-(1 / c) * (I * Y j).re))| +
          |k * (rectIntegral (fun z => poly p d z * rem z) (-a) a h).re| := abs_sub _ _
    _ ≤ (∑ j, |(poly p d (q j : ℂ)).re - (-(1 / c) * (I * Y j).re)|) +
          k * ‖rectIntegral (fun z => poly p d z * rem z) (-a) a h‖ := by
        refine add_le_add (Finset.abs_sum_le_sum_abs _ _) ?_
        rw [abs_mul, abs_of_nonneg hk0]
        exact mul_le_mul_of_nonneg_left (abs_re_le_norm _) hk0
    _ ≤ (∑ _j : Fin N, c ^ 2 * (S * (1 + a) ^ (d + 1))) +
          k * ((4 * B) * (S * B ^ d * (C / (N : ℝ) ^ 2))) := by
        refine add_le_add (Finset.sum_le_sum fun j _ => hperiod j) (mul_le_mul_of_nonneg_left ?_ hk0)
        exact hremI.trans (mul_le_mul_of_nonneg_right hlen
          (mul_nonneg (mul_nonneg hS0 (pow_nonneg (by linarith) d)) (div_nonneg hC (by positivity))))
    _ = (κ ^ 2 + 4 * C * (1 + h) ^ (d + 1) / (2 * Real.pi * κ)) * S * (1 + a) ^ (d + 1) / N := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hkdef, hcdef, hBdef, mul_pow,
          pow_succ (1 + a) d, pow_succ (1 + h) d]
        field_simp

/-! ## 6. `eq:phase` for the actual model -/

/-- **`eq:phase` from the moving-contour bundle**, for an abstract family of label events `E N` on which the conclusions of
`Prop018Bundle.moving_contour_bundle` hold (eventually in `N`, on the `ρ/8`-neighbourhood of `Γ_N`). -/
theorem phase_of_bundle (hκ : 0 < κ) (μ : Measure ℝ) {h ρ C M η r K Kd θ γ : ℝ} {b : ℕ} (hh : 0 < h)
    (hρ0 : 0 < ρ) (hM1 : 1 ≤ M) (hη : 0 < η) (hθ : 0 < θ) (hγ : 0 < γ) (hb : 1 ≤ b)
    (E : (N : ℕ) → Set (MArr N))
    (hev : ∀ᶠ N : ℕ in atTop, ∀ m ∈ E N, ∀ z ∈ NbhdN (cutN L θ N) h (ρ / 8),
          ((∀ j, 2 * |κ / (N : ℝ)| < ‖z - (qAct L κ N m j : ℂ)‖) ∧
          ‖Wf L κ (κ / N) (Gfull μ) (qAct L κ N m) z‖ ≤ 1 / 2 ∧
          1 / (2 * M) ≤ ‖aNf L κ (κ / N) (Gfull μ) (qAct L κ N m) z‖ ∧
          3 * η / 4 ≤ ‖DNf L κ (κ / N) (Gfull μ) (qAct L κ N m) z‖ ∧
          ‖aNf L κ (κ / N) (Gfull μ) (qAct L κ N m) z - Af κ (Gfull μ) z‖ ≤ 1 / (2 * M) ∧
          ‖ellf (κ / N) (qAct L κ N m) z - logaNf L κ (κ / N) (Gfull μ) (qAct L κ N m) z +
              I * κ / (N : ℂ) * corrf L κ (κ / N) (Gfull μ) (qAct L κ N m) z‖ ≤ C / (N : ℝ) ^ 2) ∧
          (∀ j, |qAct L κ N m j| ≤ (N : ℝ) ^ θ) ∧
          ‖Gfull μ z - GN (qAct L κ N m) z‖ ≤ K * ((N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ θ) ^ b) ∧
          (∀ j, r ≤ ‖z - (qAct L κ N m j : ℂ)‖) ∧
          DifferentiableAt ℂ (Gfull μ) z ∧
          η ≤ ‖Df L κ (Gfull μ) z‖ ∧
          ‖Af κ (Gfull μ) z‖ ≤ M ∧ ‖(Af κ (Gfull μ) z)⁻¹‖ ≤ M ∧ ‖ef L z‖ ≤ M ∧
          ∀ n : ℕ, ‖iteratedDeriv n (fun w => sNsrc κ L (qAct L κ N m) w - sLimsrc κ L μ w) z‖ ≤
            n.factorial * (Kd * ((N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ θ) ^ b + 1 / (N : ℝ))) / (ρ / 2) ^ n)
    (d : ℕ) (r0 : ℝ) (hr0' : 0 < r0) (f : ℂ → ℂ → ℂ) (qt : ℂ → ℂ → ℂ → ℂ)
    (hf : ∀ z w, ‖w - sf L κ (Gfull μ) z‖ < r0 → f z w = lam L κ (Gfull μ) z w)
    (hqt : ∀ z w v, ‖w - sf L κ (Gfull μ) z‖ < r0 →
      ‖v - deriv (sf L κ (Gfull μ)) z‖ < r0 → qt z w v = qch L κ (Gfull μ) z w v) :
    ∀ᶠ N : ℕ in atTop, ∀ p : ℕ → ℝ, ∀ m ∈ E N,
      |∑ r ∈ Finset.range (d + 1), p r * eigenvalue L N (κ / N) r m
        - (N : ℝ) * C0ev L κ f θ h p d N m - C1ev L κ qt θ h p d N m| ≤
        (κ ^ 2 + 4 * max C 0 * (1 + h) ^ (d + 1) / (2 * Real.pi * κ)) *
          (∑ r ∈ Finset.range (d + 1), |p r|) * (1 + cutN L θ N) ^ (d + 1) / N := by
  have hL : 0 < L := Fact.out
  have hpi : 0 < Real.pi := Real.pi_pos
  -- `δ_N → 0`
  have hδN : Tendsto (fun N : ℕ => Kd * ((N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ θ) ^ b + 1 / (N : ℝ))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-γ)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hγ).comp tendsto_natCast_atTop_atTop
    have hR' : Tendsto (fun N : ℕ => (N : ℝ) ^ θ) atTop atTop :=
      (tendsto_rpow_atTop hθ).comp tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun N : ℕ => 1 / ((N : ℝ) ^ θ) ^ b) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by omega)).comp hR')
    have h3 : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa using ((h1.add h2).add h3).const_mul Kd
  have hsm : ∀ᶠ N : ℕ in atTop,
      Kd * ((N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ θ) ^ b + 1 / (N : ℝ)) < r0 ∧
      Kd * ((N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ θ) ^ b + 1 / (N : ℝ)) / (ρ / 2) < r0 := by
    have h2 : Tendsto (fun N : ℕ => Kd * ((N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ θ) ^ b + 1 / (N : ℝ)) / (ρ / 2))
        atTop (𝓝 0) := by simpa using hδN.div_const (ρ / 2)
    exact (hδN.eventually (gt_mem_nhds hr0')).and (h2.eventually (gt_mem_nhds hr0'))
  have hcN : ∀ᶠ N : ℕ in atTop, 2 * (κ / (N : ℝ)) < h ∧ 2 * (κ / (N : ℝ)) < 1 := by
    have : Tendsto (fun N : ℕ => 2 * (κ / (N : ℝ))) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop).const_mul (2 : ℝ)
    exact (this.eventually (gt_mem_nhds hh)).and (this.eventually (gt_mem_nhds one_pos))
  filter_upwards [hev, hsm, hcN, regime_eventually hL hθ hγ 1 0, eventually_ge_atTop 1]
    with N hevN hsmN hcN' hreg hN1
  intro p m hm
  have hN : 0 < N := hN1
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ha2 : 2 ≤ (cutN L θ N) := by linarith [hreg.1, hreg.2.2.1]
  have hρ8 : 0 < ρ / 8 := by positivity
  have hzN : ∀ z ∈ Gam (-(cutN L θ N)) (cutN L θ N) h, z ∈ NbhdN (cutN L θ N) h (ρ / 8) := fun z hz =>
    gam_sub_nbhd hz (by rw [sub_self, norm_zero]; exact hρ8.le)
  have hball : ∀ z ∈ Gam (-(cutN L θ N)) (cutN L θ N) h, ∀ᶠ w in 𝓝 z, w ∈ NbhdN (cutN L θ N) h (ρ / 8) := fun z hz => by
    filter_upwards [Metric.ball_mem_nhds z hρ8] with w hw
    exact gam_sub_nbhd hz (by rw [Metric.mem_ball, dist_eq_norm] at hw; exact hw.le)
  -- the roots lie in the window
  have hroots : ∀ j, |(qAct L κ N m) j| ≤ (cutN L θ N) / 2 := by
    have hz0 : (((cutN L θ N) : ℝ) : ℂ) ∈ Gam (-(cutN L θ N)) (cutN L θ N) h := Or.inr ⟨by simp only [ofReal_im, Set.mem_Icc]; constructor <;> linarith,
      Or.inr (by simp only [ofReal_re])⟩
    intro j
    have := ((hevN m hm _ (hzN _ hz0)).2.1) j
    linarith [hreg.2.2.1]
  -- the background is differentiable near `Γ_N`
  have hsfd : ∀ z ∈ NbhdN (cutN L θ N) h (ρ / 8), DifferentiableAt ℂ (sf L κ (Gfull μ)) z := fun z hz => by
    have hG := (hevN m hm z hz).2.2.2.2.1
    have hA : DifferentiableAt ℂ (Af κ (Gfull μ)) z := (hG.const_mul (I * κ)).cexp
    have he : DifferentiableAt ℂ (ef L) z := (hasDerivAt_ef L z).differentiableAt
    exact hA.add (he.div hA (exp_ne_zero _))
  -- `s_N` and `s_N'` are within `r₀` of the background on `Γ_N`
  have hsN : ∀ z ∈ Gam (-(cutN L θ N)) (cutN L θ N) h, ‖sNf L (κ / N) (qAct L κ N m) z - sf L κ (Gfull μ) z‖ < r0 ∧
      ‖deriv (sNf L (κ / N) (qAct L κ N m)) z - deriv (sf L κ (Gfull μ)) z‖ < r0 := fun z hz => by
    have hP := hevN m hm z (hzN z hz)
    have hder := hP.2.2.2.2.2.2.2.2.2
    rw [sNsrc_eq, sLimsrc_eq] at hder
    have hroot : ∀ j, 2 * |κ / (N : ℝ)| < ‖z - ((qAct L κ N m) j : ℂ)‖ := hP.1.1
    have hd1 : DifferentiableAt ℂ (sNf L (κ / N) (qAct L κ N m)) z := (hasDerivAt_sN L hroot).differentiableAt
    constructor
    · have h0 := hder 0
      simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, pow_zero, div_one, one_mul] at h0
      exact lt_of_le_of_lt h0 hsmN.1
    · have h1 := hder 1
      rw [iteratedDeriv_one, deriv_fun_sub hd1 (hsfd z (hzN z hz))] at h1
      simp only [Nat.factorial_one, Nat.cast_one, pow_one, one_mul] at h1
      exact lt_of_le_of_lt h1 hsmN.2
  -- pointwise identification of the extensions on `Γ_N`
  have hfz : ∀ z ∈ Gam (-(cutN L θ N)) (cutN L θ N) h, f z (sNf L (κ / N) (qAct L κ N m) z) = logaNf L κ (κ / N) (Gfull μ) (qAct L κ N m) z := fun z hz =>
    (hf z _ (hsN z hz).1).trans (logaNf_eq_lam L κ (κ / N) (Gfull μ) (qAct L κ N m) z).symm
  have hqz : ∀ z ∈ Gam (-(cutN L θ N)) (cutN L θ N) h, qt z (sNf L (κ / N) (qAct L κ N m) z) (deriv (sNf L (κ / N) (qAct L κ N m)) z) =
      corrf L κ (κ / N) (Gfull μ) (qAct L κ N m) z := fun z hz => by
    rw [hqt z _ _ (hsN z hz).1 (hsN z hz).2]
    have hP := hevN m hm z (hzN z hz)
    have hGc : ∀ᶠ w in 𝓝 z, Df L κ (Gfull μ) w ≠ 0 := by
      filter_upwards [hball z hz] with w hw
      have := (hevN m hm w hw).2.2.2.2.2.1
      intro h0; rw [h0, norm_zero] at this; linarith
    have hW : 1 + Wf L κ (κ / N) (Gfull μ) (qAct L κ N m) z ∈ slitPlane := by
      refine Or.inl ?_
      have h1 := Complex.abs_re_le_norm (Wf L κ (κ / N) (Gfull μ) (qAct L κ N m) z)
      have h2 := hP.1.2.1
      simp only [add_re, one_re]
      linarith [neg_abs_le (Wf L κ (κ / N) (Gfull μ) (qAct L κ N m) z).re]
    have hM0 : 0 < 1 / (2 * M) := by positivity
    have ha0 : aNf L κ (κ / N) (Gfull μ) (qAct L κ N m) z ≠ 0 := fun h0 => by
      have := hP.1.2.2.1; rw [h0, norm_zero] at this; linarith
    have hDN0 : DNf L κ (κ / N) (Gfull μ) (qAct L κ N m) z ≠ 0 := fun h0 => by
      have := hP.1.2.2.2.1; rw [h0, norm_zero] at this; linarith
    exact (corrf_eq_qch hP.2.2.2.2.1 hGc hP.1.1 hW ha0 hDN0).symm
  -- continuity on `Γ_N`
  have hcont : ∀ z ∈ Gam (-(cutN L θ N)) (cutN L θ N) h, ContinuousAt (logaNf L κ (κ / N) (Gfull μ) (qAct L κ N m)) z ∧
      ContinuousAt (corrf L κ (κ / N) (Gfull μ) (qAct L κ N m)) z ∧ ContinuousAt (ellf (κ / N) (qAct L κ N m)) z := fun z hz => by
    have hP := hevN m hm z (hzN z hz)
    have hGnear : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (Gfull μ) w := by
      filter_upwards [hball z hz] with w hw
      exact (hevN m hm w hw).2.2.2.2.1
    have hDz : Df L κ (Gfull μ) z ≠ 0 := fun h0 => by
      have := hP.2.2.2.2.2.1; rw [h0, norm_zero] at this; linarith
    have hc := contAt_gen (by linarith : (0 : ℝ) < M) hη hGnear hP.1.1 hDz hP.1.2.1 hP.1.2.2.1 hP.1.2.2.2.1
      hP.1.2.2.2.2.1 hP.2.2.2.2.2.2.2.1
    exact ⟨hc.1, hc.2.1, hc.2.2.1⟩
  have hremz : ∀ z ∈ Gam (-(cutN L θ N)) (cutN L θ N) h, ‖ellf (κ / N) (qAct L κ N m) z - logaNf L κ (κ / N) (Gfull μ) (qAct L κ N m) z +
      I * κ / (N : ℂ) * corrf L κ (κ / N) (Gfull μ) (qAct L κ N m) z‖ ≤ max C 0 / (N : ℝ) ^ 2 := fun z hz =>
    ((hevN m hm z (hzN z hz)).1.2.2.2.2.2).trans
      (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
  -- assemble
  have hC0 : C0ev L κ f θ h p d N m = -(1 / (2 * Real.pi * κ)) *
      (rectIntegral (fun z => poly p d z * logaNf L κ (κ / N) (Gfull μ) (qAct L κ N m) z) (-(cutN L θ N)) (cutN L θ N) h).re := by
    unfold C0ev
    rw [QuantumNLS.HaarNonlinearAbstract.rect_congr_Gam (by linarith) hh.le fun z hz => by rw [hfz z hz]]
  have hC1 : C1ev L κ qt θ h p d N m =
      ((I / (2 * Real.pi)) * rectIntegral (fun z => poly p d z * corrf L κ (κ / N) (Gfull μ) (qAct L κ N m) z) (-(cutN L θ N)) (cutN L θ N) h).re := by
    unfold C1ev
    rw [QuantumNLS.HaarNonlinearAbstract.rect_congr_Gam (by linarith) hh.le fun z hz => by rw [hqz z hz]]
  rw [charge_symbol hκ hN m p d, hC0, hC1]
  exact phase_det hκ hN ha2 hh (le_max_right _ _) hroots hcN'.1 hcN'.2 (fun z hz => (hevN m hm z (hzN z hz)).1.1)
    hcont hremz p d


/-- **PROP-018, `eq:phase`** (`Q7A:prop:reconstruct`). For the actual model in the diagonal regime `R_N = N^θ`,
`ε_N = N^{−γ}`, `a_N = cutN L θ N` (as in `moving_contour_uniform`), there is a packet radius `ρ` with
`P_{N,u}(𝓔_Nᶜ) → 0` and a constant `Cp` such that, for every chart radius `r₀ > 0` and all extensions `f`, `q̃` agreeing with
`λ`, `q` on the `r₀`-disks around `(s(z), s'(z))`, eventually in `N`, for **every** real polynomial `p` of degree `≤ d` and
every label `m ∈ 𝓔_N`:
`|Σ_r p_r Q_{N,r}(m) − N C_{0,N,p}(m) − C_{1,N,p}(m)| ≤ Cp Σ_r|p_r| (1+a_N)^{d+1}/N`. -/
theorem prop018_phase (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {h δ d0 : ℝ} {l0 : ℕ} (hηh : eta0 L κ < h)
    (hδ : 0 < δ) (hd0 : 0 < d0) (hin : RootSpectralInputs L κ (μ : Measure ℝ) h δ d0 l0)
    (b pc : ℕ) (hb : 1 ≤ b) (hbpc : b ≤ 2 * pc)
    (θ γ : ℝ) (hθ : 0 < θ) (hγ : 0 < γ) (hsum : 3 * γ + θ < 1) (pt : ℕ) (hpt : 1 < 2 * (pt : ℝ) * θ)
    (d : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧
      Tendsto (fun N : ℕ => (bornMeasure (physBasis L hκ N) u hu).real
        (EN (μ : Measure ℝ) (qAct L κ N) ((N : ℝ) ^ θ) (cutN L θ N) ρ h (eta0 L κ) ((N : ℝ) ^ (-γ)) b)ᶜ)
        atTop (𝓝 0) ∧
      ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ r0 : ℝ, 0 < r0 → ∀ (f : ℂ → ℂ → ℂ) (qt : ℂ → ℂ → ℂ → ℂ),
        (∀ z w, ‖w - sf L κ (Gfull (μ : Measure ℝ)) z‖ < r0 → f z w = lam L κ (Gfull (μ : Measure ℝ)) z w) →
        (∀ z w v, ‖w - sf L κ (Gfull (μ : Measure ℝ)) z‖ < r0 →
          ‖v - deriv (sf L κ (Gfull (μ : Measure ℝ))) z‖ < r0 → qt z w v = qch L κ (Gfull (μ : Measure ℝ)) z w v) →
        ∀ᶠ N : ℕ in atTop, ∀ p : ℕ → ℝ, ∀ m ∈ EN (μ : Measure ℝ) (qAct L κ N) ((N : ℝ) ^ θ) (cutN L θ N) ρ h
          (eta0 L κ) ((N : ℝ) ^ (-γ)) b,
          |∑ r ∈ Finset.range (d + 1), p r * eigenvalue L N (κ / N) r m
            - (N : ℝ) * C0ev L κ f θ h p d N m - C1ev L κ qt θ h p d N m| ≤
            Cp * (∑ r ∈ Finset.range (d + 1), |p r|) * (1 + cutN L θ N) ^ (d + 1) / N := by
  obtain ⟨ρ, hρ0, h2ρ, hprob, C, M, η, r, K, Kd, hM1, hη, hr0, hK0, hev⟩ :=
    moving_contour_bundle hκ u hu hμ hηh hδ hd0 hin b pc hb hbpc θ γ hθ hγ hsum pt hpt
  have hh : 0 < h := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  refine ⟨ρ, hρ0, hprob, κ ^ 2 + 4 * max C 0 * (1 + h) ^ (d + 1) / (2 * Real.pi * κ), by positivity,
    fun r0 hr0' f qt hf hqt => ?_⟩
  exact phase_of_bundle hκ (μ : Measure ℝ) hh hρ0 hM1 hη hθ hγ hb
    (fun N => EN (μ : Measure ℝ) (qAct L κ N) ((N : ℝ) ^ θ) (cutN L θ N) ρ h (eta0 L κ) ((N : ℝ) ^ (-γ)) b)
    hev d r0 hr0' f qt hf hqt

end QuantumNLS.Prop018Phase

#print axioms QuantumNLS.Prop018Phase.corrf_eq_qch
#print axioms QuantumNLS.Prop018Phase.eigenvalue_eq
#print axioms QuantumNLS.Prop018Phase.charge_symbol
#print axioms QuantumNLS.Prop018Phase.phase_det
#print axioms QuantumNLS.Prop018Phase.phase_of_bundle
#print axioms QuantumNLS.Prop018Phase.prop018_phase
