import QuantumNLS.HaarSpectralTail

/-!
# R-9C3CC17D `QG:lem:haar-nonlinear-tail` (QUANTUM_GAUGE_COMPONENTS.tex:699-731, proof 732-795)

Fix `E > 0` and the marginal rank `k ≥ 1`. On the actual physical Bethe basis at coupling `κ/N`
(`HaarSpectralTail.bas`), with the energy projection `P_{N,E}` (the diagonal mask `1_{E_m ≤ NE}`,
`HaarSpectralTail.energyProjection_phys`) and `X_{N,n}(w) = S_N(ωn + w) − (1 + e^{iwL})·1`
(`HaarSpectralTail.Xop`):

* (free expansion) `HaarFreeTaylor.free_taylor`: `F_w(X) = X/(1 − e^{iwL}) + Σ_{d≥2} f_d(w) X^d`, `|f_d(w)| ≤ Mσ^{-d}`,
  uniformly in `w ∈ Γ_0`;
* (small spectral tail) `‖X_{N,n}(w) P_{N,E}‖ ≤ C_E/|n|`;
* (the remainder) for `R ≥ R₀`, finite `I ⊂ {|n| > R}`, real `|t_n| ≤ 1`, the operator `R_{N,I}` defined by its
  joint spectral calculus, i.e. diagonal in the common eigenbasis with eigenvalue
  `rEig m = 1_{E_m ≤ NE} · (−N/(2πκ)) Re ∮_{Γ_0} Σ_{n∈I} t_n (F_w(x_{n,m}(w)) − x_{n,m}(w)/(1 − e^{iwL})) dw`
  (`x_{n,m}(w)` the joint eigenvalue of `X_{N,n}(w)`; `∮_{Γ_0}` the positively oriented boundary integral,
  `rect0_eq_boundary`), exists (`RN_exists`) and satisfies, for every unit `ψ ∈ ran P_{N,E}` and every bounded
  `J` on the symmetric `k`-particle space, with `J_N = U_{N,k}(J)`:
  `|⟨ψ, [R_{N,I}, J_N] ψ⟩| ≤ C_{E,k} R^{-1/2} ‖J‖`, the same with `J_N` compressed by `P_{N,E}`, and the same after
  conjugating that compression by any unitary commuting with all the transfers and `P_{N,E}`
  (**`haar_nonlinear_tail`**).

Route (the source's): the square-sum commutator bounds of R-F9AB39A7 (`OffgridCommutator.haar_commutator_bessel`
and its adjoint version) for `J_N` and `J_N^* = U_{N,k}(J^*)` (`BasisAdjoint.placement_adjoint'`) are transported to
the compressions and unitary conjugates (`BesselOp.sandwich`); the abstract argument
`HaarNonlinearAbstract.abstract_tail` (Cauchy–Schwarz in the label for the quadratic term, individual commutator
norms for `d ≥ 3`, the adjoint for the real part) gives the bound with
`Σ_{|n|>R} (C_E/|n|)² ≤ 4C_E²/R` (`HaarSummableReconstruction.finite_tail`).
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section

open Complex Filter Topology Set
open scoped InnerProductSpace ComplexConjugate

namespace QuantumNLS.HaarNonlinearTail

open QuantumNLS.HaarFreeTaylor QuantumNLS.HaarNonlinearAbstract QuantumNLS.HaarSpectralTail
  QuantumNLS.OffgridBessel QuantumNLS.HaarKernelFactorizationSym QuantumNLS.PeriodReconstruction
  QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor QuantumNLS.NormalizedTransfer
  QuantumNLS.KernelDefinition QuantumNLS.PeriodTwoTerm

instance (N : ℕ) : Countable (BetheLabels.MArr N) := by unfold BetheLabels.MArr; infer_instance

/-! ## 1. Generic operator facts -/

section Generic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

lemma comm_sub_smul (S J : E →L[ℂ] E) (c : ℂ) :
    (S - c • (1 : E →L[ℂ] E)) * J - J * (S - c • (1 : E →L[ℂ] E)) = S * J - J * S := by
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]; abel

lemma adjoint_sub_smul (S : E →L[ℂ] E) (c : ℂ) :
    ContinuousLinearMap.adjoint (S - c • (1 : E →L[ℂ] E)) =
      ContinuousLinearMap.adjoint S - conj c • (1 : E →L[ℂ] E) := by
  rw [map_sub, map_smulₛₗ, ContinuousLinearMap.adjoint_one]

lemma comm_sandwich (S A J B : E →L[ℂ] E) (hA : S * A = A * S) (hB : B * S = S * B) :
    S * (A * J * B) - A * J * B * S = A * (S * J - J * S) * B := by
  rw [show S * (A * J * B) = S * A * J * B by noncomm_ring,
    show A * J * B * S = A * J * (B * S) by noncomm_ring, hA, hB]
  noncomm_ring

lemma norm_isometry_le {V : E →L[ℂ] E} (hV : ContinuousLinearMap.adjoint V * V = 1) (x : E) :
    ‖V x‖ ≤ ‖x‖ := by
  have h : ⟪V x, V x⟫_ℂ = ⟪x, x⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← mul_ap, hV, one_ap]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖V x‖ ^ 2 = ‖x‖ ^ 2 := by exact_mod_cast h
  nlinarith [norm_nonneg (V x), norm_nonneg x]

lemma adjoint_comm_of_unitary {V S : E →L[ℂ] E} (hV'V : ContinuousLinearMap.adjoint V * V = 1)
    (hVV' : V * ContinuousLinearMap.adjoint V = 1) (hc : V * S = S * V) :
    ContinuousLinearMap.adjoint V * S = S * ContinuousLinearMap.adjoint V := by
  calc ContinuousLinearMap.adjoint V * S =
        ContinuousLinearMap.adjoint V * S * (V * ContinuousLinearMap.adjoint V) := by
        rw [hVV', mul_one]
    _ = ContinuousLinearMap.adjoint V * (S * V) * ContinuousLinearMap.adjoint V := by
        simp only [mul_assoc]
    _ = ContinuousLinearMap.adjoint V * (V * S) * ContinuousLinearMap.adjoint V := by rw [hc]
    _ = ContinuousLinearMap.adjoint V * V * S * ContinuousLinearMap.adjoint V := by
        simp only [mul_assoc]
    _ = S * ContinuousLinearMap.adjoint V := by rw [hV'V, one_mul]

lemma comm_smul_of_comm (c : ℂ) {V S : E →L[ℂ] E} (h : V * S = S * V) :
    (c • S) * V = V * (c • S) := by
  ext x
  have h' := congrArg (fun T => T x) h
  simp only [mul_ap] at h' ⊢
  rw [smul_apply, smul_apply, map_smul, h']

variable {ι : Type*} {b : HilbertBasis ι ℂ E}

lemma IsDiagC.commute {S T : E →L[ℂ] E} {μ ν : ι → ℂ} (hS : IsDiagC b S μ) (hT : IsDiagC b T ν) :
    S * T = T * S := by
  ext v
  refine ext_coeff (b := b) fun i => ?_
  rw [(hS.mul hT) i v, (hT.mul hS) i v]
  beta_reduce
  ring

end Generic

/-! ## 2. Square-sum commutator bounds as a closed class -/

section Bessel

variable (L : ℝ) [Fact (0 < L)]

/-- `S_n = S_N(ωn + w)`. -/
abbrev Sn (κ : ℝ) (N : ℕ) (w : ℂ) (n : ℤ) : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N :=
  normalizedTransfer L κ N (OffgridCommutator.zpt L w n)

/-- The square-sum commutator bounds, for `S_N(ωn+w)` and for its adjoint, uniformly on `Γ_0`. -/
def BesselOp (κ : ℝ) (N : ℕ) (β : ℝ) (J' : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N) :
    Prop :=
  ∀ w ∈ Gamma0 L, ∀ (I : Finset ℤ) (φ : SymSector ℂ (L2T L) N),
    ∑ n ∈ I, ‖(Sn L κ N w n * J' - J' * Sn L κ N w n) φ‖ ^ 2 ≤ β ^ 2 * ‖φ‖ ^ 2 ∧
    ∑ n ∈ I, ‖(ContinuousLinearMap.adjoint (Sn L κ N w n) * J' -
      J' * ContinuousLinearMap.adjoint (Sn L κ N w n)) φ‖ ^ 2 ≤ β ^ 2 * ‖φ‖ ^ 2

lemma finite_of_tsum {f : ℤ → ℝ} {N : ℕ} (hN : 0 < N) {X : ℝ}
    (hs : Summable (fun j : ℤ => ((N : ℝ) * f j) ^ 2))
    (hb : Real.sqrt (∑' j : ℤ, ((N : ℝ) * f j) ^ 2) ≤ X) (I : Finset ℤ) :
    ∑ n ∈ I, f n ^ 2 ≤ (X / N) ^ 2 := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have h1 := hs.sum_le_tsum I (fun _ _ => sq_nonneg _)
  have h0 : 0 ≤ ∑' j : ℤ, ((N : ℝ) * f j) ^ 2 := tsum_nonneg fun _ => sq_nonneg _
  have h2 : ∑' j : ℤ, ((N : ℝ) * f j) ^ 2 ≤ X ^ 2 := by
    rw [← Real.sq_sqrt h0]; exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hb 2
  have e : ∑ n ∈ I, ((N : ℝ) * f n) ^ 2 = (N : ℝ) ^ 2 * ∑ n ∈ I, f n ^ 2 := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun n _ => by ring
  rw [div_pow, le_div_iff₀ (pow_pos hNr 2)]
  linarith

lemma besselOp_U {κ : ℝ} (hκ : 0 ≤ κ) {N k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N)
    (J : BoundedSymmetricKernel (L2T L) k) :
    BesselOp L κ N (OffgridCommutator.Bk L κ k * ‖J‖ / N) (genericU_N_r N k hkN J) := by
  intro w hw I φ
  have hN : 0 < N := by omega
  obtain ⟨hs1, hb1⟩ := OffgridCommutator.haar_commutator_bessel L hw hκ hk1 hkN J φ
  obtain ⟨hs2, hb2⟩ := OffgridCommutator.haar_commutator_bessel_adjoint L hw hκ hk1 hkN J φ
  have e : (OffgridCommutator.Bk L κ k * ‖J‖ * ‖φ‖ / N) ^ 2 =
      (OffgridCommutator.Bk L κ k * ‖J‖ / N) ^ 2 * ‖φ‖ ^ 2 := by ring
  refine ⟨?_, ?_⟩
  · have := finite_of_tsum (f := fun j => ‖(normalizedTransfer L κ N (OffgridCommutator.zpt L w j) *
      genericU_N_r N k hkN J - genericU_N_r N k hkN J *
        normalizedTransfer L κ N (OffgridCommutator.zpt L w j)) φ‖) hN hs1 hb1 I
    rw [e] at this; exact this
  · have := finite_of_tsum (f := fun j => ‖(ContinuousLinearMap.adjoint
      (normalizedTransfer L κ N (OffgridCommutator.zpt L w j)) * genericU_N_r N k hkN J -
        genericU_N_r N k hkN J * ContinuousLinearMap.adjoint
          (normalizedTransfer L κ N (OffgridCommutator.zpt L w j))) φ‖) hN hs2 hb2 I
    rw [e] at this; exact this

lemma besselOp_U_adj {κ : ℝ} (hκ : 0 ≤ κ) {N k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N)
    (J : BoundedSymmetricKernel (L2T L) k) :
    BesselOp L κ N (OffgridCommutator.Bk L κ k * ‖J‖ / N)
      (ContinuousLinearMap.adjoint (genericU_N_r N k hkN J)) := by
  rw [BasisAdjoint.placement_adjoint' L N k hkN J]
  have := besselOp_U L hκ hk1 hkN (ContinuousLinearMap.adjoint J)
  rwa [LinearIsometryEquiv.norm_map] at this

/-- Square-sum bounds survive `J' ↦ A J' B` for contractions `A, B` commuting with all `S_n` and `S_n^*`. -/
lemma BesselOp.sandwich {κ : ℝ} {N : ℕ} {β : ℝ} {J' A B : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N}
    (h : BesselOp L κ N β J')
    (hA : ∀ z, normalizedTransfer L κ N z * A = A * normalizedTransfer L κ N z ∧
      ContinuousLinearMap.adjoint (normalizedTransfer L κ N z) * A =
        A * ContinuousLinearMap.adjoint (normalizedTransfer L κ N z))
    (hB : ∀ z, B * normalizedTransfer L κ N z = normalizedTransfer L κ N z * B ∧
      B * ContinuousLinearMap.adjoint (normalizedTransfer L κ N z) =
        ContinuousLinearMap.adjoint (normalizedTransfer L κ N z) * B)
    (hAn : ∀ x, ‖A x‖ ≤ ‖x‖) (hBn : ∀ x, ‖B x‖ ≤ ‖x‖) :
    BesselOp L κ N β (A * J' * B) := by
  intro w hw I φ
  obtain ⟨h1, h2⟩ := h w hw I (B φ)
  have hBφ : ‖B φ‖ ^ 2 ≤ ‖φ‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hBn φ) 2
  have hβ : 0 ≤ β ^ 2 := sq_nonneg β
  refine ⟨?_, ?_⟩
  · refine le_trans (Finset.sum_le_sum fun n _ => ?_) (h1.trans (mul_le_mul_of_nonneg_left hBφ hβ))
    rw [comm_sandwich _ _ _ _ (hA _).1 (hB _).1, mul_ap, mul_ap]
    exact pow_le_pow_left₀ (norm_nonneg _) (hAn _) 2
  · refine le_trans (Finset.sum_le_sum fun n _ => ?_) (h2.trans (mul_le_mul_of_nonneg_left hBφ hβ))
    rw [comm_sandwich _ _ _ _ (hA _).2 (hB _).2, mul_ap, mul_ap]
    exact pow_le_pow_left₀ (norm_nonneg _) (hAn _) 2

/-- From the square-sum bounds for `J'` and `J'^*` to the hypotheses of the abstract argument. -/
lemma commBd_of_bessel {κ : ℝ} {N : ℕ} {β : ℝ} (hβ : 0 ≤ β)
    {J' : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N}
    (h1 : BesselOp L κ N β J') (h2 : BesselOp L κ N β (ContinuousLinearMap.adjoint J'))
    (I : Finset ℤ) (ψ : SymSector ℂ (L2T L) N) (hψ1 : ‖ψ‖ = 1) :
    CommBd (fun n w => Xop L κ N w n) I (Gam (-(omegaL L / 4)) (omegaL L / 4) (omegaL L / 4)) ψ β J' := by
  intro w hw
  beta_reduce
  rw [Gam0_eq] at hw
  have hXc : ∀ n, Xop L κ N w n * J' - J' * Xop L κ N w n = Sn L κ N w n * J' - J' * Sn L κ N w n :=
    fun n => comm_sub_smul _ _ _
  have hXa : ∀ n, ContinuousLinearMap.adjoint (Xop L κ N w n) * ContinuousLinearMap.adjoint J' -
      ContinuousLinearMap.adjoint J' * ContinuousLinearMap.adjoint (Xop L κ N w n) =
      ContinuousLinearMap.adjoint (Sn L κ N w n) * ContinuousLinearMap.adjoint J' -
        ContinuousLinearMap.adjoint J' * ContinuousLinearMap.adjoint (Sn L κ N w n) := fun n => by
    unfold Xop; rw [adjoint_sub_smul]; exact comm_sub_smul _ _ _
  refine ⟨fun n _ => ?_, ?_, ?_⟩
  · rw [hXc]
    refine ContinuousLinearMap.opNorm_le_bound _ hβ fun φ => ?_
    have := (h1 w hw {n} φ).1
    rw [Finset.sum_singleton] at this
    have h3 := Real.sqrt_le_sqrt this
    rw [Real.sqrt_sq (norm_nonneg _), show β ^ 2 * ‖φ‖ ^ 2 = (β * ‖φ‖) ^ 2 by ring,
      Real.sqrt_sq (by positivity)] at h3
    exact h3
  · have := (h1 w hw I ψ).1
    rw [hψ1, one_pow, mul_one] at this
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun n _ => by rw [hXc])) this
  · have := (h2 w hw I ψ).2
    rw [hψ1, one_pow, mul_one] at this
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun n _ => by rw [hXa])) this

end Bessel

/-! ## 3. The nonlinear remainder operator -/

section Remainder

variable (L : ℝ) [Fact (0 < L)]

/-- `G_w(y) = F_w(y) − y/(1 − e^{iwL})`, the nonlinear part of the free expansion. -/
def Gfun (w y : ℂ) : ℂ := FW L w y - y / (1 - ew L w)

/-- The joint eigenvalue `x_{n,m}(w)` of `X_{N,n}(w)` on the Bethe vector `m`. -/
def xEig {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (n : ℤ) (w : ℂ) (m : BetheLabels.MArr N) : ℂ :=
  NormalityBridge.eigen (L := L) κ hκ hN m (OffgridCommutator.zpt L w n) - (1 + ew L w)

open Classical in
/-- The joint-spectral-calculus eigenvalue of `R_{N,I}`:
`1_{E_m ≤ NE} · (−N/(2πκ)) Re ∮_{Γ_0} Σ_{n∈I} t_n (F_w(x) − x/(1−e^{iwL})) dw`. -/
def rEig {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (E : ℝ) (I : Finset ℤ) (t : ℤ → ℝ)
    (m : BetheLabels.MArr N) : ℂ :=
  if m ∈ adm L κ N E then
    ((-(N / (2 * Real.pi * κ)) * (LabelExactPeriod.rectIntegral
      (fun w => ∑ n ∈ I, (t n : ℂ) * Gfun L w (xEig L hκ hN n w m))
        (-(omegaL L / 4)) (omegaL L / 4) (omegaL L / 4)).re : ℝ) : ℂ)
  else 0

/-- The contour integral used is the positively oriented boundary integral over `Γ_0`. -/
lemma rect0_eq_boundary (f : ℂ → ℂ) :
    LabelExactPeriod.rectIntegral f (-(omegaL L / 4)) (omegaL L / 4) (omegaL L / 4) =
      HighContours.boundaryIntegral L 0 f := by
  rw [← HaarSummableReconstruction.rect_eq_boundary]
  simp only [HaarSummableReconstruction.lo, HaarSummableReconstruction.hi,
    HaarSummableReconstruction.ht, Int.cast_zero, mul_zero, zero_sub, zero_add, ← omegaL_eq_om]

variable {L}

lemma norm_Gfun_le {w : ℂ} (hw : w ∈ Gamma0 L) {y : ℂ} (hy : ‖y‖ ≤ sig) : ‖Gfun L w y‖ ≤ 2 := by
  unfold Gfun
  refine (norm_sub_le _ _).trans ?_
  have h1 := norm_FW_le hw hy
  have hη := one_sub_ew_lower hw
  have hη0 := etaL_pos
  have hη1 := etaL_lt_one
  have hM := M1_ge
  have hs : sig ≤ etaL := by
    unfold sig
    rw [div_le_iff₀ (by positivity)]
    calc etaL ^ 2 = etaL * etaL := sq etaL
      _ ≤ etaL * 1 := mul_le_mul_of_nonneg_left hη1.le hη0.le
      _ ≤ etaL * (8 * M1 ^ 2) := mul_le_mul_of_nonneg_left (by nlinarith) hη0.le
  have h2 : ‖y / (1 - ew L w)‖ ≤ 1 := by
    rw [norm_div, div_le_one (lt_of_lt_of_le hη0 hη)]; linarith
  linarith

lemma contAt_G {X : ℂ → ℂ} {w0 : ℂ} (hw0 : w0 ∈ Gamma0 L) (hX : ContinuousAt X w0)
    (hX0 : ‖X w0‖ ≤ sig) : ContinuousAt (fun w => Gfun L w (X w)) w0 := by
  have he : Continuous (ew L) := by unfold ew; fun_prop
  have hec := he.continuousAt (x := w0)
  have hD : 1 - ew L w0 ≠ 0 := by
    intro h0; have := one_sub_ew_lower hw0; rw [h0, norm_zero] at this; linarith [etaL_pos]
  have hu : ContinuousAt (fun w => 1 + uF L w (X w)) w0 := by
    unfold uF
    exact continuousAt_const.add ((((continuousAt_const.mul (continuousAt_const.add hec)).mul hX).add
      (hX.pow 2)).div ((continuousAt_const.sub hec).pow 2) (pow_ne_zero 2 hD))
  have hcp : ContinuousAt (fun w => (1 + uF L w (X w)) ^ ((2 : ℂ)⁻¹)) w0 :=
    hu.cpow continuousAt_const (uF_slit hw0 hX0)
  have ha : ContinuousAt (fun w => aF L w (X w)) w0 := by
    unfold aF
    exact (((continuousAt_const.add hec).add hX).add ((continuousAt_const.sub hec).mul hcp)).div_const 2
  have hlog := ha.clog (aF_slit hw0 hX0)
  unfold Gfun FW
  exact hlog.sub (hX.div (continuousAt_const.sub hec) hD)

end Remainder

/-! ## 4. The lemma -/

set_option maxHeartbeats 40000000 in
/-- **R-9C3CC17D `QG:lem:haar-nonlinear-tail`.** -/
theorem haar_nonlinear_tail (L : ℝ) [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) {E : ℝ} (hE : 0 < E)
    {k : ℕ} (hk : 1 ≤ k) :
    -- the free expansion `QG:eq:haar-free-taylor`
    (∃ σ M : ℝ, 0 < σ ∧ 0 ≤ M ∧ ∀ w ∈ Gamma0 L,
      DifferentiableOn ℂ (FW L w) (Metric.closedBall 0 σ) ∧
      ∃ f : ℕ → ℂ, f 0 = 0 ∧ f 1 = 1 / (1 - ew L w) ∧ (∀ d, ‖f d‖ ≤ M * σ⁻¹ ^ d) ∧
        ∀ X, ‖X‖ < σ → HasSum (fun d => f d * X ^ d) (FW L w X)) ∧
    ∃ R₀ CE : ℝ, 2 ≤ R₀ ∧ 0 ≤ CE ∧ ∀ (N : ℕ) (hkN : k ≤ N)
      (P : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N),
      (∀ m, P (bas L hκ (hk.trans hkN) m) = mask L κ N E m • bas L hκ (hk.trans hkN) m) →
      -- `QG:eq:haar-small-spectral-tail`
      (∀ n : ℤ, R₀ < |(n : ℝ)| → ∀ w ∈ Gamma0 L, ∀ φ,
        ‖(Xop L κ N w n * P) φ‖ ≤ CE / |(n : ℝ)| * ‖φ‖) ∧
      ∀ R : ℝ, R₀ ≤ R → ∀ I : Finset ℤ, (∀ n ∈ I, R < |(n : ℝ)|) → ∀ t : ℤ → ℝ,
        (∀ n, |t n| ≤ 1) →
        -- `R_{N,I}` exists by its joint spectral calculus
        (∃ RN : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N,
          ∀ m, RN (bas L hκ (hk.trans hkN) m) =
            rEig L hκ (hk.trans hkN) E I t m • bas L hκ (hk.trans hkN) m) ∧
        ∀ RN : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N,
          (∀ m, RN (bas L hκ (hk.trans hkN) m) =
            rEig L hκ (hk.trans hkN) E I t m • bas L hκ (hk.trans hkN) m) →
        ∀ (J : BoundedSymmetricKernel (L2T L) k) (ψ : SymSector ℂ (L2T L) N), P ψ = ψ → ‖ψ‖ = 1 →
          -- `QG:eq:haar-nonlinear-commutator`
          ‖⟪ψ, (RN * genericU_N_r N k hkN J - genericU_N_r N k hkN J * RN) ψ⟫_ℂ‖ ≤
            CE * ‖J‖ / Real.sqrt R ∧
          -- with `J_N` compressed by `P_{N,E}`
          ‖⟪ψ, (RN * (P * genericU_N_r N k hkN J * P) -
            (P * genericU_N_r N k hkN J * P) * RN) ψ⟫_ℂ‖ ≤ CE * ‖J‖ / Real.sqrt R ∧
          -- after conjugating the compression by a unitary commuting with the transfers and `P_{N,E}`
          ∀ V : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N,
            ContinuousLinearMap.adjoint V * V = 1 → V * ContinuousLinearMap.adjoint V = 1 →
            (∀ z, V * normalizedTransfer L κ N z = normalizedTransfer L κ N z * V) → V * P = P * V →
            ‖⟪ψ, (RN * (V * (P * genericU_N_r N k hkN J * P) * ContinuousLinearMap.adjoint V) -
              (V * (P * genericU_N_r N k hkN J * P) * ContinuousLinearMap.adjoint V) * RN) ψ⟫_ℂ‖ ≤
              CE * ‖J‖ / Real.sqrt R := by
  have hL : 0 < L := Fact.out
  obtain ⟨σ0, M0, hσ0, hM0, hσeq, hft⟩ := free_taylor L
  refine ⟨⟨σ0, M0, hσ0, hM0, fun w hw => ⟨(hft w hw).2.1, (hft w hw).2.2.2⟩⟩, ?_⟩
  choose! f hf using fun w (hw : w ∈ Gamma0 L) => (hft w hw).2.2.2
  obtain ⟨R₁, C, hR₁, hC, htail⟩ := eig_tail hL hκ hE
  set ω := omegaL L with hωdef
  have hω : 0 < ω := omegaL_pos
  set σ := σ0 with hσdef
  set Kin : ℝ := 4 * M0 * σ⁻¹ ^ 2 * C + 64 * M0 * σ⁻¹ ^ 3 * C ^ 2 with hKin
  have hσi : 0 ≤ σ⁻¹ := inv_nonneg.2 hσ0.le
  have hKin0 : 0 ≤ Kin :=
    add_nonneg (mul_nonneg (mul_nonneg (by linarith) (pow_nonneg hσi 2)) hC)
      (mul_nonneg (mul_nonneg (by linarith) (pow_nonneg hσi 3)) (sq_nonneg C))
  set Kc : ℝ := OffgridCommutator.Bk L κ k / (2 * Real.pi * κ) * (2 * ω) * Kin with hKc
  have hBk := OffgridCommutator.Bk_nonneg L hκ.le k
  have h2πκ : 0 < 2 * Real.pi * κ := mul_pos (mul_pos two_pos Real.pi_pos) hκ
  have hKc0 : 0 ≤ Kc :=
    mul_nonneg (mul_nonneg (div_nonneg hBk h2πκ.le) (by linarith)) hKin0
  set R₀ : ℝ := max R₁ (max 2 (2 * C / σ)) with hR₀
  have h2R₀' : 2 ≤ R₀ := (le_max_left 2 _).trans (le_max_right _ _)
  refine ⟨R₀, C + Kc, h2R₀', add_nonneg hC hKc0, ?_⟩
  intro N hkN P hP
  have hN : 0 < N := hk.trans hkN
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hR₁₀ : R₁ ≤ R₀ := le_max_left _ _
  have h2R₀ : 2 ≤ R₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hCR₀ : 2 * C / σ ≤ R₀ := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨fun n hn w hw φ => ?_, ?_⟩
  · -- the small spectral tail
    have hn0 : 0 < |(n : ℝ)| := by linarith
    show ‖Xop L κ N w n (P φ)‖ ≤ _
    refine ((diagC_X L hκ hN w n).norm_le (div_nonneg hC (abs_nonneg _))
      (fun m hm => (htail N hN m hm n (lt_of_le_of_lt hR₁₀ hn) w hw).1) (supp_P hκ hN hP φ)).trans ?_
    calc C / |(n : ℝ)| * ‖P φ‖ ≤ C / |(n : ℝ)| * ‖φ‖ :=
          mul_le_mul_of_nonneg_left (norm_P_le hκ hN hP φ) (div_nonneg hC (abs_nonneg _))
      _ ≤ (C + Kc) / |(n : ℝ)| * ‖φ‖ :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by linarith) (abs_nonneg _))
            (norm_nonneg _)
  intro R hR I hI t ht
  have hR2 : 2 ≤ R := h2R₀.trans hR
  have hRpos : 0 < R := by linarith
  set A := adm L κ N E
  set b := bas L hκ hN
  set κ' : ℝ := -(N / (2 * Real.pi * κ)) with hκ'
  -- the contour
  have hGam : ∀ w ∈ Gam (-(ω / 4)) (ω / 4) (ω / 4), w ∈ Gamma0 L := fun w hw => by
    rw [← Gam0_eq]; exact hw
  -- the label weights
  set ρ : ℤ → ℝ := fun n => C / |(n : ℝ)| with hρdef
  have hρ0 : ∀ n, 0 ≤ ρ n := fun n => div_nonneg hC (abs_nonneg _)
  have hρσ : ∀ n ∈ I, ρ n ≤ σ / 2 := fun n hn => by
    have h1 := hI n hn
    have h2 : 2 * C / σ < |(n : ℝ)| := lt_of_le_of_lt (hCR₀.trans hR) h1
    have hn0 : 0 < |(n : ℝ)| := by linarith
    simp only [hρdef]
    rw [div_le_iff₀ hn0]
    rw [div_lt_iff₀ hσ0] at h2
    linarith
  set Q : ℝ := 4 * C ^ 2 / R with hQdef
  have hQ : ∑ n ∈ I, ρ n ^ 2 ≤ Q := by
    have h1 := HaarSummableReconstruction.finite_tail hR2 I hI
    have e : ∑ n ∈ I, ρ n ^ 2 = C ^ 2 * ∑ n ∈ I, 1 / (n : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      simp only [hρdef, div_pow, sq_abs]; ring
    rw [e, hQdef]
    calc C ^ 2 * ∑ n ∈ I, 1 / (n : ℝ) ^ 2 ≤ C ^ 2 * (4 / R) := mul_le_mul_of_nonneg_left h1 (sq_nonneg C)
      _ = 4 * C ^ 2 / R := by ring
  -- the free expansion data
  set g : ℂ → ℕ → ℂ := fun w d => if d ≤ 1 then 0 else f w d with hgdef
  have hg0 : ∀ w ∈ Gam (-(ω / 4)) (ω / 4) (ω / 4), g w 0 = 0 := fun w _ => by simp [hgdef]
  have hg1 : ∀ w ∈ Gam (-(ω / 4)) (ω / 4) (ω / 4), g w 1 = 0 := fun w _ => by simp [hgdef]
  have hgM : ∀ w ∈ Gam (-(ω / 4)) (ω / 4) (ω / 4), ∀ d, ‖g w d‖ ≤ M0 * σ⁻¹ ^ d := fun w hw d => by
    simp only [hgdef]
    split_ifs
    · rw [norm_zero]; exact mul_nonneg hM0 (pow_nonneg hσi d)
    · exact (hf w (hGam w hw)).2.2.1 d
  have hG : ∀ w ∈ Gam (-(ω / 4)) (ω / 4) (ω / 4), ∀ y, ‖y‖ ≤ σ / 2 →
      HasSum (fun d => g w d * y ^ d) (Gfun L w y) := fun w hw y hy => by
    obtain ⟨hf0, hf1, -, hfs⟩ := hf w (hGam w hw)
    have h1 := hfs y (by linarith)
    have h2 := h1.sub (hasSum_ite_eq 1 (y / (1 - ew L w)))
    refine h2.congr_fun fun d => ?_
    match d with
    | 0 => simp [hgdef, hf0]
    | 1 =>
      have e1 : (if (1 : ℕ) = 1 then y / (1 - ew L w) else 0) = y / (1 - ew L w) := by simp
      have e2 : g w 1 = 0 := by simp [hgdef]
      rw [e1, e2, hf1]; ring
    | d + 2 =>
      have e3 : (if d + 2 = 1 then y / (1 - ew L w) else 0) = 0 := by
        rw [ite_eq_right_iff]; intro h; omega
      have e4 : g w (d + 2) = f w (d + 2) := by
        simp only [hgdef]; rw [ite_eq_right_iff]; intro h; omega
      rw [e3, e4, sub_zero]
  have hx : ∀ n ∈ I, ∀ w ∈ Gam (-(ω / 4)) (ω / 4) (ω / 4), ∀ m ∈ A, ‖xEig L hκ hN n w m‖ ≤ ρ n :=
    fun n hn w hw m hm => (htail N hN m hm n (lt_of_le_of_lt hR₁₀ (lt_of_le_of_lt hR (hI n hn)))
      w (hGam w hw)).1
  have hGc : ∀ m ∈ A, ∀ n ∈ I, ∀ w ∈ Gam (-(ω / 4)) (ω / 4) (ω / 4),
      ContinuousAt (fun w => Gfun L w (xEig L hκ hN n w m)) w := fun m hm n hn w hw => by
    refine contAt_G (hGam w hw) ?_ ((hx n hn w hw m hm).trans ((hρσ n hn).trans (by linarith)))
    have h1 : Continuous fun w : ℂ => OffgridCommutator.zpt L w n := by
      unfold OffgridCommutator.zpt; fun_prop
    have h2 : Continuous (ew L) := by unfold ew; fun_prop
    exact (((NormalityBridge.eigen_differentiable (L := L) κ hκ hN m).continuous.comp h1).sub
      (continuous_const.add h2)).continuousAt
  -- the remainder operator
  have hrb0 : 0 ≤ N / (2 * Real.pi * κ) * ((2 * ω) * (I.card * 2)) :=
    mul_nonneg (div_pos hNr h2πκ).le (mul_nonneg (by linarith) (by positivity))
  have hrb : ∀ m, ‖rEig L hκ hN E I t m‖ ≤ N / (2 * Real.pi * κ) * ((2 * ω) * (I.card * 2)) := by
    intro m
    unfold rEig
    split_ifs with hm
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_neg,
        abs_of_pos (div_pos hNr h2πκ)]
      refine mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans ?_) (div_pos hNr h2πκ).le
      have := norm_rectIntegral_le (f := fun w => ∑ n ∈ I, (t n : ℂ) * Gfun L w (xEig L hκ hN n w m))
        (a := -(ω / 4)) (b := ω / 4) (h := ω / 4)
        (K := I.card * 2) (by linarith) (by linarith) fun w hw => by
          refine (norm_sum_le _ _).trans ?_
          calc ∑ n ∈ I, ‖(t n : ℂ) * Gfun L w (xEig L hκ hN n w m)‖ ≤ ∑ _n ∈ I, (2 : ℝ) :=
                Finset.sum_le_sum fun n hn => by
                  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
                  calc |t n| * ‖Gfun L w (xEig L hκ hN n w m)‖ ≤ 1 * 2 :=
                        mul_le_mul (ht n) (norm_Gfun_le (hGam w hw)
                          ((hx n hn w hw m hm).trans ((hρσ n hn).trans (by linarith))))
                          (norm_nonneg _) zero_le_one
                    _ = 2 := one_mul _
            _ = I.card * 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      have e : 2 * (ω / 4 - -(ω / 4)) + 4 * (ω / 4) = 2 * ω := by ring
      rw [e] at this
      exact this
    · rw [norm_zero]; exact hrb0
  refine ⟨?_, ?_⟩
  · obtain ⟨RN, hRN, -⟩ := QuantumNLS.HilbertDiagOp.diag_exists b (rEig L hκ hN E I t) _ hrb hrb0
    exact ⟨RN, fun m => (show IsDiagC b RN _ from hRN).apply_basis m⟩
  intro RN hRN J ψ hψP hψ1
  have hRd : IsDiagC b RN (rEig L hκ hN E I t) := diagC_of_apply hRN
  have hψs : Supp b A ψ := by have := supp_P hκ hN hP ψ; rwa [hψP] at this
  set β : ℝ := OffgridCommutator.Bk L κ k * ‖J‖ / N with hβdef
  have hβ : 0 ≤ β := div_nonneg (mul_nonneg hBk (ContinuousLinearMap.opNorm_nonneg J)) hNr.le
  have hr : ∀ m ∈ A, rEig L hκ hN E I t m = ((κ' * (LabelExactPeriod.rectIntegral
      (fun w => ∑ n ∈ I, (t n : ℂ) * Gfun L w (xEig L hκ hN n w m))
        (-(ω / 4)) (ω / 4) (ω / 4)).re : ℝ) : ℂ) := fun m hm => by
    have hm' : m ∈ adm L κ N E := hm
    unfold rEig; simp only [hm', ↓reduceIte]; rfl
  -- the key estimate for any `J'` with square-sum bounds for `J'` and `J'^*`
  have key : ∀ J' : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N,
      BesselOp L κ N β J' → BesselOp L κ N β (ContinuousLinearMap.adjoint J') →
      ‖⟪ψ, (RN * J' - J' * RN) ψ⟫_ℂ‖ ≤ (C + Kc) * ‖J‖ / Real.sqrt R := by
    intro J' hJ1 hJ2
    have hK1 := commBd_of_bessel L hβ hJ1 hJ2 I ψ hψ1
    have hK2 := commBd_of_bessel L hβ hJ2 (by rwa [ContinuousLinearMap.adjoint_adjoint]) I ψ hψ1
    have hmain := abstract_tail (b := b) (X := fun n w => Xop L κ N w n)
      (x := fun n w m => xEig L hκ hN n w m) (fun n w => diagC_X L hκ hN w n) hψs hψ1 ht hρ0
      hσ0 hM0 hβ hρσ hQ (G := Gfun L) (g := g) (by linarith) (by linarith) hg0 hg1 hgM hG hx hGc
      hK1 hK2 hRd κ' hr
    refine hmain.trans ?_
    -- the arithmetic
    have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hRpos
    have hsq : Real.sqrt Q = 2 * C / Real.sqrt R := by
      rw [hQdef, show 4 * C ^ 2 / R = (2 * C / Real.sqrt R) ^ 2 by
        rw [div_pow, Real.sq_sqrt hRpos.le]; ring]
      exact Real.sqrt_sq (div_nonneg (by linarith) hsR.le)
    have hQle : Q ≤ 4 * C ^ 2 / Real.sqrt R := by
      rw [hQdef]
      apply div_le_div_of_nonneg_left (by positivity) hsR
      have h1 : 1 ≤ Real.sqrt R := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
      calc Real.sqrt R = Real.sqrt R * 1 := (mul_one _).symm
        _ ≤ Real.sqrt R * Real.sqrt R := mul_le_mul_of_nonneg_left h1 hsR.le
        _ = R := Real.mul_self_sqrt hRpos.le
    have hκabs : |κ'| = N / (2 * Real.pi * κ) := by
      rw [hκ', abs_neg, abs_of_pos (div_pos hNr h2πκ)]
    have hper : 2 * (ω / 4 - -(ω / 4)) + 4 * (ω / 4) = 2 * ω := by ring
    rw [hκabs, hper, hsq]
    have hT : 2 * M0 * σ⁻¹ ^ 2 * (2 * C / Real.sqrt R) * β + 16 * M0 * σ⁻¹ ^ 3 * Q * β ≤
        β / Real.sqrt R * Kin := by
      have h16 : 0 ≤ 16 * M0 * σ⁻¹ ^ 3 * β := by
        have := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 16 * M0) (pow_nonneg hσi 3)) hβ
        exact this
      have := mul_le_mul_of_nonneg_left hQle h16
      have e1 : β / Real.sqrt R * Kin = 2 * M0 * σ⁻¹ ^ 2 * (2 * C / Real.sqrt R) * β +
          16 * M0 * σ⁻¹ ^ 3 * β * (4 * C ^ 2 / Real.sqrt R) := by
        have := hsR.ne'
        simp only [hKin]; field_simp; ring
      rw [e1]
      nlinarith
    calc N / (2 * Real.pi * κ) * (2 * ω * (2 * M0 * σ⁻¹ ^ 2 * (2 * C / Real.sqrt R) * β +
          16 * M0 * σ⁻¹ ^ 3 * Q * β))
        ≤ N / (2 * Real.pi * κ) * (2 * ω * (β / Real.sqrt R * Kin)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hT (by linarith))
            (div_pos hNr h2πκ).le
      _ = Kc * ‖J‖ / Real.sqrt R := by
          have h1 := hsR.ne'
          have h2 := hNr.ne'
          have h3 := hκ.ne'
          have h4 := Real.pi_pos.ne'
          simp only [hKc, hβdef]; field_simp
      _ ≤ (C + Kc) * ‖J‖ / Real.sqrt R :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by linarith) (ContinuousLinearMap.opNorm_nonneg J)) hsR.le
  -- the three operators
  have hU := besselOp_U L hκ.le hk hkN J
  have hUa := besselOp_U_adj L hκ.le hk hkN J
  have hPd := diagC_P hκ hN hP
  have hPsa : ContinuousLinearMap.adjoint P = P := by
    refine ContinuousLinearMap.ext fun v => ext_coeff (b := b) fun m => ?_
    rw [IsDiagC.adjoint hPd m v, hPd m v]
    beta_reduce
    by_cases hm : m ∈ A
    · rw [mask_of_mem L hm, map_one]
    · rw [mask_of_not_mem L hm, map_zero]
  have hPS : ∀ z, normalizedTransfer L κ N z * P = P * normalizedTransfer L κ N z ∧
      ContinuousLinearMap.adjoint (normalizedTransfer L κ N z) * P =
        P * ContinuousLinearMap.adjoint (normalizedTransfer L κ N z) := fun z =>
    ⟨IsDiagC.commute (diagC_transfer L hκ hN z) hPd,
      IsDiagC.commute (IsDiagC.adjoint (diagC_transfer L hκ hN z)) hPd⟩
  have hSP : ∀ z, P * normalizedTransfer L κ N z = normalizedTransfer L κ N z * P ∧
      P * ContinuousLinearMap.adjoint (normalizedTransfer L κ N z) =
        ContinuousLinearMap.adjoint (normalizedTransfer L κ N z) * P := fun z =>
    ⟨((hPS z).1).symm, ((hPS z).2).symm⟩
  have hPn : ∀ x, ‖P x‖ ≤ ‖x‖ := norm_P_le hκ hN hP
  have hPJ : BesselOp L κ N β (P * genericU_N_r N k hkN J * P) :=
    BesselOp.sandwich L hU hPS hSP hPn hPn
  have hPJa : BesselOp L κ N β (ContinuousLinearMap.adjoint (P * genericU_N_r N k hkN J * P)) := by
    have e : ContinuousLinearMap.adjoint (P * genericU_N_r N k hkN J * P) =
        P * ContinuousLinearMap.adjoint (genericU_N_r N k hkN J) * P := by
      simp only [← ContinuousLinearMap.star_eq_adjoint, star_mul] at hPsa ⊢
      rw [hPsa, mul_assoc]
    rw [e]; exact BesselOp.sandwich L hUa hPS hSP hPn hPn
  refine ⟨key _ hU hUa, key _ hPJ hPJa, ?_⟩
  intro V hV'V hVV' hVS hVP
  have hVS' : ∀ z, normalizedTransfer L κ N z * V = V * normalizedTransfer L κ N z ∧
      ContinuousLinearMap.adjoint (normalizedTransfer L κ N z) * V =
        V * ContinuousLinearMap.adjoint (normalizedTransfer L κ N z) := fun z => by
    refine ⟨(hVS z).symm, ?_⟩
    rw [normalizedTransfer_adjoint]
    exact comm_smul_of_comm _ (hVS (conj z))
  have hV'S : ∀ z, ContinuousLinearMap.adjoint V * normalizedTransfer L κ N z =
      normalizedTransfer L κ N z * ContinuousLinearMap.adjoint V ∧
      ContinuousLinearMap.adjoint V * ContinuousLinearMap.adjoint (normalizedTransfer L κ N z) =
        ContinuousLinearMap.adjoint (normalizedTransfer L κ N z) * ContinuousLinearMap.adjoint V :=
    fun z => ⟨adjoint_comm_of_unitary hV'V hVV' (hVS z),
      adjoint_comm_of_unitary hV'V hVV' (hVS' z).2.symm⟩
  have hVn : ∀ x, ‖V x‖ ≤ ‖x‖ := fun x => norm_isometry_le hV'V x
  have hVV'' : ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint V) *
      ContinuousLinearMap.adjoint V = 1 := by
    rw [ContinuousLinearMap.adjoint_adjoint]; exact hVV'
  have hV'n : ∀ x, ‖ContinuousLinearMap.adjoint V x‖ ≤ ‖x‖ := fun x =>
    norm_isometry_le (V := ContinuousLinearMap.adjoint V) hVV'' x
  have hVJ := BesselOp.sandwich L hPJ hVS' hV'S hVn hV'n
  have hVJa : BesselOp L κ N β (ContinuousLinearMap.adjoint
      (V * (P * genericU_N_r N k hkN J * P) * ContinuousLinearMap.adjoint V)) := by
    have e : ContinuousLinearMap.adjoint
        (V * (P * genericU_N_r N k hkN J * P) * ContinuousLinearMap.adjoint V) =
        V * ContinuousLinearMap.adjoint (P * genericU_N_r N k hkN J * P) *
          ContinuousLinearMap.adjoint V := by
      simp only [← ContinuousLinearMap.star_eq_adjoint, star_mul, star_star, mul_assoc]
    rw [e]; exact BesselOp.sandwich L hPJa hVS' hV'S hVn hV'n
  exact key _ hVJ hVJa

end QuantumNLS.HaarNonlinearTail

#print axioms QuantumNLS.HaarNonlinearTail.besselOp_U
#print axioms QuantumNLS.HaarNonlinearTail.contAt_G
#print axioms QuantumNLS.HaarNonlinearTail.haar_nonlinear_tail
