import Mathlib
import QuantumNLS.MPFamilyMeas
import QuantumNLS.MPOps
import QuantumNLS.MPContourBound

/-!
# PROP-026 `lem:MP-linearization` (`mixed_propagation.tex:354`): the combined linearization, actual contour family

New module.  Binds the contour pieces (`Γ_a` and the fixed contours), the weights `ω_i` (`p_t` on `Γ_a`, `θ_n` on `Γ_n`), the smooth
extensions `f_z` (`gfun`, built from the multiplier chart `eq:MP-chart`), the background `A, G, D, s` (`BgFam`, only the
uniform bounds of the source's contour setup and continuity off the real axis), and the physical transfer
`S_N = normalizedTransfer` on the realized `Sym^N` to the proved trace-norm theorem `prop026_traceNorm_physical`:

**`mp_linearization`**: there is `C` (depending on `L, κ, h, k` and the background bounds `d₀, s₁, a₀, c₁` only) such that for every
`q`, `N = k + q`, every contour family `P` and background `B`, every normalized `φ` with `‖(S_N(z) - s(z)) φ‖ ≤ ε_i` on piece `i`:

`‖γ^{(k)}_{e^{-iN C_{0,N}} φ} - γ^{(k)}_{e^{-iN L_N} φ}‖₁ ≤ C · (2πκ)⁻¹ · ∑_i ε_i · wlen(P_i)`,

with `C_{0,N} = C0op = Re ∫ u_θ f_{z_θ}(S_θ) dν` (`eq:MP-C0`) and `L_N = Lop = Re ∫ u_θ D(z_θ)⁻¹ S_θ dν` (`eq:MP-L`) the
printed operators, and `wlen(P_i)` the weighted length `∫_{piece i} |ω_i| |dz|` (`MPContour`).  The right side is the
`∫ w δ dν` of PROP-014 evaluated exactly (`MPContourBound.integral_w_delta`): the fixed-contour deviation enters only through its own
weighted length, unamplified by the growth of `Γ_a`.
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

open MeasureTheory Set Filter Metric Topology
open scoped InnerProductSpace ENNReal

namespace QuantumNLS.MPLinearization

open QuantumNLS.MPContour QuantumNLS.MPChartBounds QuantumNLS.MPChartSmooth QuantumNLS.MPChartDeriv
  QuantumNLS.MPFamily QuantumNLS.MPFamilyMeas QuantumNLS.MPOps
open QuantumNLS.MixedQuadratures
open QuantumNLS.FunctionalLinearization
open QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor QuantumNLS.NormalizedTransfer

/-- The piece family with the weights multiplied by `-i` (for the imaginary-part quadrature of `C_{0,N}`). -/
def twist {m : ℕ} (P : Fin m → Piece) : Fin m → Piece := fun i =>
  ⟨(P i).γ, (P i).γ', fun z => -Complex.I * (P i).ω z, (P i).hγ, (P i).hγ',
    continuous_const.mul (P i).hω⟩

theorem uθ_twist {m : ℕ} (κ : ℝ) (P : Fin m → Piece) (θ : ThetaSpace m) :
    uθ κ (twist P) θ = -Complex.I * uθ κ P θ := by
  unfold uθ twist zθ
  simp only
  ring

theorem zθ_twist {m : ℕ} (P : Fin m → Piece) : zθ (twist P) = zθ P := rfl

theorem gθ_twist {m : ℕ} {Z : Set ℂ} {d₀ s₁ a₀ c₁ : ℝ} (P : Fin m → Piece) (B : BgFam Z d₀ s₁ a₀ c₁) :
    gθ (twist P) B = gθ P B := rfl

section GenericAux

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Θ : Type*} [TopologicalSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ] [SecondCountableTopology Θ]
  (ν : MeasureTheory.Measure Θ) [IsFiniteMeasure ν]

/-- Integrability of a scalar-weighted continuous operator family (generic `H`; instantiated at `Sym^N`). -/
theorem integrable_smul_family (S : Θ → H →L[ℂ] H) (hS : Continuous S) (c : Θ → ℂ)
    (hc : AEStronglyMeasurable c ν) {C R : ℝ} (hC0 : 0 ≤ C) (hC : ∀ θ, ‖c θ‖ ≤ C) (hR : ∀ θ, ‖S θ‖ ≤ R) :
    Integrable (fun θ => c θ • S θ) ν :=
  (integrable_const (C * R)).mono' (hc.smul hS.aestronglyMeasurable)
    (ae_of_all _ fun θ => by
      rw [norm_smul]
      exact mul_le_mul (hC θ) (hR θ) (norm_nonneg _) hC0)

end GenericAux

section Bounds

variable {m : ℕ} {Z : Set ℂ} {d₀ s₁ a₀ c₁ : ℝ} (P : Fin m → Piece) (B : BgFam Z d₀ s₁ a₀ c₁)
  (hZ : ∀ i, ∀ τ ∈ Icc (0 : ℝ) 1, (P i).γ τ ∈ Z)

include hZ in
theorem norm_gθ_le (hc1 : 0 ≤ c₁) (θ : ThetaSpace m) (w : ℂ) : ‖gθ P B θ w‖ ≤ c₁ + 1 := by
  unfold gθ
  by_cases h : good P θ
  · rw [if_pos h]
    have hbg : Bg d₀ s₁ a₀ (B.D (zθ P θ)) (B.s (zθ P θ)) (B.A (zθ P θ)) := B.bg _ (hZ θ.1 θ.2 θ.2.2) h
    have h1 := norm_gfun_le hbg (B.c0 (zθ P θ)) w
    have h2 : ‖B.c0 (zθ P θ)‖ ≤ c₁ := B.c0le _ (hZ θ.1 θ.2 θ.2.2) h
    linarith
  · rw [if_neg h]; simp; linarith

omit hZ in
theorem norm_resKd_Fθ_le (hc1 : 0 ≤ c₁) (u : ℂ) (R : ℝ) (g : ℂ → ℂ) (hg : Continuous g)
    (hgb : ∀ w, ‖g w‖ ≤ c₁ + 1) : ‖resKd (Kdisc R) (quadF u g)‖ ≤ ‖u‖ * (c₁ + 1) := by
  refine (ContinuousMap.norm_le _ (by positivity)).2 (fun x => ?_)
  rw [resKd_apply (continuous_quadF u hg).continuousOn x, Complex.norm_real, Real.norm_eq_abs]
  unfold quadF
  calc |(u * g (isoR2.symm x)).re| ≤ ‖u * g (isoR2.symm x)‖ := Complex.abs_re_le_norm _
    _ = ‖u‖ * ‖g (isoR2.symm x)‖ := norm_mul _ _
    _ ≤ ‖u‖ * (c₁ + 1) := mul_le_mul_of_nonneg_left (hgb _) (norm_nonneg _)

include hZ in
theorem norm_dθ_le (hd0 : 0 < d₀) (θ : ThetaSpace m) : ‖dθ P B θ‖ ≤ d₀⁻¹ := by
  unfold dθ
  by_cases h : good P θ
  · rw [if_pos h]
    have hbg : Bg d₀ s₁ a₀ (B.D (zθ P θ)) (B.s (zθ P θ)) (B.A (zθ P θ)) := B.bg _ (hZ θ.1 θ.2 θ.2.2) h
    rw [norm_inv]
    exact inv_anti₀ hbg.hd0 hbg.hD
  · rw [if_neg h]; simpa using inv_nonneg.2 hd0.le

end Bounds

/-- **PROP-026 `lem:MP-linearization`: the combined linearization for the actual contour family.** -/
theorem mp_linearization (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (h : ℝ) (k : ℕ)
    (d₀ s₁ a₀ c₁ : ℝ) (hd0 : 0 < d₀) (hs0 : 0 ≤ s₁) (ha0 : 0 < a₀) (hc1 : 0 ≤ c₁) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (q : ℕ) (hN : 1 ≤ k + q) {m : ℕ} (Z : Set ℂ) (P : Fin m → Piece)
        (hZ : ∀ i, ∀ τ ∈ Icc (0 : ℝ) 1, (P i).γ τ ∈ Z)
        (hIm : ∀ i, ∀ τ ∈ Icc (0 : ℝ) 1, |((P i).γ τ).im| ≤ h)
        (hreal : ∀ i, ∀ τ ∈ Ioo (0 : ℝ) 1, ((P i).γ τ).im ≠ 0)
        (B : BgFam Z d₀ s₁ a₀ c₁)
        (phi : SymSector ℂ (L2T L) (k + q)) (hphi : ‖phi‖ = 1) (ε : Fin m → ℝ) (hε : ∀ i, 0 ≤ ε i)
        (hdev : ∀ i, ∀ τ ∈ Icc (0 : ℝ) 1,
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
          ENNReal.ofReal (C * ((2 * Real.pi * κ)⁻¹ * ∑ i : Fin m, ε i * wlen (P i))) := by
  classical
  obtain ⟨mder, C0, hm, hC0, hmain⟩ := prop026_traceNorm_physical
  have hρ := rho_pos hd0 hs0 ha0
  have hr : 0 < rad d₀ s₁ a₀ := by unfold rad; positivity
  set Rs : ℝ := max (Rbd L κ h) s₁ with hRs
  have hU : IsOpen (ball (0 : EuclideanSpace ℝ (Fin 2)) (Rs + 1)) := isOpen_ball
  have hQ : IsCompact (closedBall (0 : EuclideanSpace ℝ (Fin 2)) Rs) := isCompact_closedBall _ _
  have hQU : closedBall (0 : EuclideanSpace ℝ (Fin 2)) Rs ⊆ ball 0 (Rs + 1) :=
    closedBall_subset_ball (by linarith)
  obtain ⟨C1, hC1, hC1b⟩ := hmain hU hQ hQU
  obtain ⟨Cψ, hCψ0, hCψ⟩ := exists_cutoff_bound hr mder
  set M0 : ℝ := ∑ i ∈ Finset.range (mder + 1), Bder Cψ (rad d₀ s₁ a₀) c₁ i with hM0def
  have hM0 : 0 ≤ M0 := Finset.sum_nonneg (fun i _ => Bder_nonneg hCψ0 hr hc1 i)
  have hY : 0 ≤ Real.exp (L * h) * (2 * k * (2 * Real.exp (L * h) *
      ((|κ| * L) * Real.exp (|κ| * L)))) := by
    have := (Fact.out : 0 < L)
    positivity
  refine ⟨C0 * (C1 * M0) * (Real.exp (L * h) * (2 * k * (2 * Real.exp (L * h) *
    ((|κ| * L) * Real.exp (|κ| * L))))), mul_nonneg (mul_nonneg hC0 (mul_nonneg hC1 hM0)) hY, ?_⟩
  intro q hN m Z P hZ hIm hreal B phi hphi ε hε hdev
  have hz : Continuous (zθ P) := continuous_zθ P
  have hzh : ∀ θ : ThetaSpace m, |(zθ P θ).im| ≤ h := fun θ => hIm θ.1 θ.2 θ.2.2
  have hKQ : Kdisc (Rbd L κ h) ⊆ closedBall (0 : EuclideanSpace ℝ (Fin 2)) Rs :=
    closedBall_subset_closedBall (le_max_left _ _)
  have hsQ : ∀ θ : ThetaSpace m, isoR2 (B.s (zθ P θ)) ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) Rs := by
    intro θ
    rw [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
    exact (B.s_le _ (hZ θ.1 θ.2 θ.2.2)).trans (le_max_right _ _)
  have hF := fun θ => (contDiff_Fθ κ P B hZ θ).contDiffOn (s := ball (0 : EuclideanSpace ℝ (Fin 2)) (Rs + 1))
  have hFm := aesm_resKd κ P B hZ (Rbd L κ h)
  have hdF := fun j => aesm_fderiv κ P B hZ j
  have hδ : ∀ θ : ThetaSpace m, 0 ≤ ε θ.1 := fun θ => hε _
  have hsδ : ∀ θ : ThetaSpace m, ‖(normalizedTransfer L κ (k + q) (zθ P θ) - B.s (zθ P θ) •
      (1 : SymSector ℂ (L2T L) (k + q) →L[ℂ] SymSector ℂ (L2T L) (k + q))) phi‖ ≤ ε θ.1 :=
    fun θ => hdev θ.1 θ.2 θ.2.2
  have hw0 : ∀ θ, 0 ≤ wθ κ P θ := fun θ => norm_nonneg _
  have hw : Integrable (wθ κ P) (nu m) := integrable_of_continuous (continuous_wθ κ P)
  have hwδ : Integrable (fun θ : ThetaSpace m => wθ κ P θ * ε θ.1) (nu m) :=
    integrable_of_continuous ((continuous_wθ κ P).mul (continuous_of_discreteTopology.comp continuous_fst))
  have hFb : ∀ θ, ∀ i ≤ mder, ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (Rs + 1),
      ‖iteratedFDeriv ℝ i (Fθ κ P B θ) x‖ ≤ wθ κ P θ * M0 := by
    intro θ i hi x _
    refine (norm_iteratedFDeriv_Fθ_le κ P B hZ hc1 hCψ hCψ0 hr hi θ x).trans ?_
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (f := fun i => Bder Cψ (rad d₀ s₁ a₀) c₁ i)
        (fun i _ => Bder_nonneg hCψ0 hr hc1 i) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))) (hw0 θ)
  have key := hC1b (nu m) L κ hκ k q hN (zθ P) hz h hzh hKQ (fun θ => B.s (zθ P θ)) hsQ (Fθ κ P B) hF
    hFm hdF phi hphi (fun θ => ε θ.1) hδ hsδ (wθ κ P) hw0 hw hwδ hM0 hFb
  beta_reduce at key
  rw [integral_w_delta hκ P ε hε] at key
  -- operator identification
  have hS : ∀ θ : ThetaSpace m, IsStarNormal (normalizedTransfer L κ (k + q) (zθ P θ)) :=
    fun θ => SN_isStarNormal L κ hκ (k + q) hN (zθ P θ)
  have hR : ∀ θ : ThetaSpace m, ‖normalizedTransfer L κ (k + q) (zθ P θ)‖ ≤ Rbd L κ h :=
    fun θ => norm_normalizedTransfer_le L κ (k + q) (zθ P θ) h (hzh θ)
  obtain ⟨U₁, hU₁⟩ := isCompact_univ.exists_bound_of_continuousOn (continuous_uθ κ P).continuousOn
  set U₀ : ℝ := max U₁ 0 with hU₀def
  have hU₀' : ∀ θ, ‖uθ κ P θ‖ ≤ U₀ := fun θ => (hU₁ θ (mem_univ _)).trans (le_max_left _ _)
  have hU₀0 : 0 ≤ U₀ := le_max_right _ _
  have hgc : ∀ θ, Continuous (gθ P B θ) := fun θ => (contDiff_gθ P B hZ θ).continuous
  have hgb : ∀ θ w, ‖gθ P B θ w‖ ≤ c₁ + 1 := norm_gθ_le P B hZ hc1
  have hBm : ∀ j, AEStronglyMeasurable (fun θ => quadHom (normalizedTransfer L κ (k + q) (zθ P θ)) (hS θ)
      (Rbd L κ h) (hR θ) (coordC (d := 2) (K := Kdisc (Rbd L κ h)) j)) (nu m) :=
    fun j => PhiFam_hB hκ hN (nu m) (zθ P) hz (Rbd L κ h) hR j
  have hF1 : AEStronglyMeasurable (fun θ => resKd (Kdisc (Rbd L κ h)) (quadF (uθ κ P θ) (gθ P B θ))) (nu m) := hFm
  have hF2 : AEStronglyMeasurable
      (fun θ => resKd (Kdisc (Rbd L κ h)) (quadF ((-Complex.I) * uθ κ P θ) (gθ P B θ))) (nu m) := by
    have := aesm_resKd κ (twist P) B (fun i τ hτ => hZ i τ hτ) (Rbd L κ h)
    have e : (fun θ => resKd (Kdisc (Rbd L κ h)) (quadF ((-Complex.I) * uθ κ P θ) (gθ P B θ))) =
        fun θ => resKd (Kdisc (Rbd L κ h)) (Fθ κ (twist P) B θ) := by
      funext θ; unfold Fθ; rw [uθ_twist, gθ_twist]
    rw [e]; exact this
  have hC1' : ∀ θ, ‖resKd (Kdisc (Rbd L κ h)) (quadF (uθ κ P θ) (gθ P B θ))‖ ≤ U₀ * (c₁ + 1) := fun θ =>
    (norm_resKd_Fθ_le hc1 (uθ κ P θ) (Rbd L κ h) (gθ P B θ) (hgc θ) (hgb θ)).trans
      (mul_le_mul_of_nonneg_right (hU₀' θ) (by linarith))
  have hC2' : ∀ θ, ‖resKd (Kdisc (Rbd L κ h)) (quadF ((-Complex.I) * uθ κ P θ) (gθ P B θ))‖ ≤ U₀ * (c₁ + 1) :=
    fun θ => (norm_resKd_Fθ_le hc1 ((-Complex.I) * uθ κ P θ) (Rbd L κ h) (gθ P B θ) (hgc θ) (hgb θ)).trans
      (by rw [norm_mul, norm_neg, Complex.norm_I, one_mul]; exact mul_le_mul_of_nonneg_right (hU₀' θ) (by linarith))
  have hCop : C0N (nu m) (PhiFam' L κ hκ (k + q) hN (zθ P) h hzh) (Fθ κ P B) =
      C0op (nu m) (fun θ => normalizedTransfer L κ (k + q) (zθ P θ)) (uθ κ P) (gθ P B) :=
    C0N_eq_C0op (nu m) (Rbd L κ h) (fun θ => normalizedTransfer L κ (k + q) (zθ P θ)) hS hR (uθ κ P)
      (gθ P B) hgc hBm hF1 hF2 hC1' hC2'
  have hSc : Continuous fun θ : ThetaSpace m => normalizedTransfer L κ (k + q) (zθ P θ) :=
    ((QuantumNLS.NormalityBridge.differentiable_normalizedTransfer (L := L) (κ := κ) (N := k + q)).continuous).comp hz
  have hcud : AEStronglyMeasurable (fun θ => uθ κ P θ * dθ P B θ) (nu m) :=
    (continuous_uθ κ P).aestronglyMeasurable.mul (aesm_dθ P B hZ)
  have hint := integrable_smul_family (nu m) (fun θ => normalizedTransfer L κ (k + q) (zθ P θ)) hSc
    (fun θ => uθ κ P θ * dθ P B θ) hcud (C := U₀ * d₀⁻¹) (R := Rbd L κ h) (mul_nonneg hU₀0 (inv_nonneg.2 hd0.le))
    (fun θ => by
      rw [norm_mul]
      exact mul_le_mul (hU₀' θ) (norm_dθ_le P B hZ hd0 θ) (norm_nonneg _) hU₀0) hR
  have hLop : LN (nu m) (PhiFam' L κ hκ (k + q) hN (zθ P) h hzh) (Fθ κ P B)
      (fun θ => isoR2 (B.s (zθ P θ))) =
      Lop (nu m) (fun θ => normalizedTransfer L κ (k + q) (zθ P θ)) (uθ κ P) (dθ P B) :=
    LN_eq_Lop (nu m) (Rbd L κ h) (fun θ => normalizedTransfer L κ (k + q) (zθ P θ)) hS hR (uθ κ P)
      (gθ P B) (dθ P B) (fun θ => B.s (zθ P θ)) (hasDerivAt_gθ P B hZ) hint
  rw [hCop, hLop] at key
  refine key.trans (le_of_eq ?_)
  congr 1
  ring

end QuantumNLS.MPLinearization

#print axioms QuantumNLS.MPLinearization.mp_linearization
