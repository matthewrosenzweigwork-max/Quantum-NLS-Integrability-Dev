import QuantumNLS.HaarFreeTaylor
import QuantumNLS.HaarNonlinearAbstract
import QuantumNLS.HaarSummableReconstruction
import QuantumNLS.UnconditionalBetheBasis
import QuantumNLS.EnergyProjection
import QuantumNLS.TransferSeparation
import QuantumNLS.OffgridCommutator

/-!
# R-9C3CC17D `QG:lem:haar-nonlinear-tail`, part 3: the small spectral tail `QG:eq:haar-small-spectral-tail`

Source: `source-text/chapters/core/QUANTUM_GAUGE_COMPONENTS.tex:745-753`: "The proof of
Proposition `QG:prop:haar-summable-reconstruction` gives `‖X_{N,n}(w) P_{N,E}‖ ≤ C_E/|n|`, uniformly in the contour
parameter and `N ≥ N_E`. The transfers are normal and share the actual Bethe basis, so they commute with
`P_{N,E}`, with each other, and with their adjoints."

* `sourceRoots_actual`: the source roots of an antitone label (the actual Bethe basis vectors) are, after
  reversing the order, an actual configuration `RootContraction.IsActualConfig` (the configurations of
  HighContours R-93DEB242);
* `Gam0_eq`: the four edges `Gam (−ω/4) (ω/4) (ω/4)` are exactly `Γ_0 = OffgridBessel.Gamma0 L`; `zpt_mem`:
  `ωn + w` lies on `Γ_n` for `w ∈ Γ_0`;
* `norm_prod_sub_one_le`: `|∏(1 + a_j) − 1| ≤ exp(Σ|a_j|) − 1`;
* **`eig_tail`**: there are `R₁ ≥ 2` and `C ≥ 0` (depending on `L, κ, E`) such that for every `N`, every Bethe basis
  label `m` of energy `≤ NE` and every `|n| > R₁`, `w ∈ Γ_0`:
  `|Λ_m(ωn + w) − (1 + e^{iwL})| ≤ C/|n|` (`Λ_m` the actual transfer eigenvalue `NormalityBridge.eigen`);
* `diagC_transfer`, `diagC_X`: `S_N(z)` and `X_{N,n}(w) = S_N(ωn+w) − (1+e^{iwL})·1` are diagonal in the
  actual physical Bethe basis; `diagC_P`, `energyProjection_exists`, `energyProjection_phys`: the energy
  projection `P_{N,E}` is the diagonal mask `1_{E_m ≤ NE}` in that basis; it is the transport of the
  `EnergyProjection.energy_projection` operator of `1_{[0,NE]}(H_N)` through `symmetricPosition`;
* **`small_spectral_tail`**: `‖X_{N,n}(w) P_{N,E} φ‖ ≤ (C/|n|) ‖φ‖`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
noncomputable section

open Complex Filter Topology Set
open scoped InnerProductSpace ComplexConjugate

namespace QuantumNLS.HaarSpectralTail

open QuantumNLS.HaarFreeTaylor QuantumNLS.HaarNonlinearAbstract QuantumNLS.OffgridBessel
  QuantumNLS.HaarKernelFactorizationSym QuantumNLS.PeriodReconstruction
  QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor QuantumNLS.NormalizedTransfer

/-! ## 1. The actual Bethe roots are actual configurations -/

lemma logMap_rev {N : ℕ} (L c : ℝ) (q : Fin N → ℝ) (i : Fin N) :
    BetheAdmission.logMap L c (q ∘ Fin.rev) i = BetheAdmission.logMap L c q (Fin.rev i) := by
  unfold BetheAdmission.logMap
  simp only [Function.comp]
  rw [Fintype.sum_equiv Fin.revPerm (fun j => Real.arctan ((q (Fin.rev i) - q (Fin.rev j)) / c))
    (fun j => Real.arctan ((q (Fin.rev i) - q j) / c)) (fun j => rfl)]

/-- The source roots of an antitone label, in increasing order, form an actual configuration. -/
theorem sourceRoots_actual {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c) {n : Fin N → ℤ}
    (hn : Antitone n) :
    RootContraction.IsActualConfig L c (n ∘ Fin.rev) (BetheSmooth.sourceRoots L n c ∘ Fin.rev) := by
  have hmono : Monotone (n ∘ Fin.rev) := fun i j hij => hn (Fin.rev_le_rev.2 hij)
  rw [RootContraction.isActual_iff_solves hc hmono _ hL]
  intro i
  rw [logMap_rev, congrFun (BetheSmooth.sourceRoots_solves hL hc n) (Fin.rev i)]
  unfold BetheSmooth.sourceNumbers BetheAdmission.quantumNumbers
  simp only [Function.comp, Fin.val_rev]
  rw [Nat.cast_sub (by omega : i.val + 1 ≤ N)]
  push_cast
  ring

lemma sum_rev {N : ℕ} (f : Fin N → ℝ) : ∑ j, f (Fin.rev j) = ∑ j, f j :=
  Fintype.sum_equiv Fin.revPerm _ _ (fun _ => rfl)

lemma sum_rev_c {N : ℕ} (f : Fin N → ℂ) : ∑ j, f (Fin.rev j) = ∑ j, f j :=
  Fintype.sum_equiv Fin.revPerm _ _ (fun _ => rfl)

/-! ## 2. The contour `Γ_0` and its translates -/

section Geometry

variable {L : ℝ} [Fact (0 < L)]

lemma omegaL_eq_om : omegaL L = HighContours.om L := by unfold omegaL HighContours.om; rfl

lemma omegaL_pos : 0 < omegaL L := by
  have : 0 < L := Fact.out; unfold omegaL; have := Real.pi_pos; positivity

/-- The four edges are `Γ_0`. -/
theorem Gam0_eq : Gam (-(omegaL L / 4)) (omegaL L / 4) (omegaL L / 4) = Gamma0 L := by
  have hω := omegaL_pos (L := L)
  ext w
  constructor
  · intro hw
    show max |w.re| |w.im| = omegaL L / 4
    rcases hw with ⟨⟨h1, h2⟩, h3 | h3⟩ | ⟨⟨h1, h2⟩, h3 | h3⟩
    · rw [h3, abs_neg, abs_of_pos (show 0 < omegaL L / 4 by linarith),
        max_eq_right (abs_le.2 ⟨h1, h2⟩)]
    · rw [h3, abs_of_pos (show 0 < omegaL L / 4 by linarith), max_eq_right (abs_le.2 ⟨h1, h2⟩)]
    · rw [h3, abs_neg, abs_of_pos (show 0 < omegaL L / 4 by linarith),
        max_eq_left (abs_le.2 ⟨h1, h2⟩)]
    · rw [h3, abs_of_pos (show 0 < omegaL L / 4 by linarith), max_eq_left (abs_le.2 ⟨h1, h2⟩)]
  · intro hw
    obtain ⟨h1, h2, h3⟩ := mem_Gamma0 hw
    rw [abs_le] at h1 h2
    rcases h3 with h3 | h3
    · refine Or.inr ⟨⟨h2.1, h2.2⟩, ?_⟩
      rcases (abs_eq (by linarith)).1 h3 with h | h
      · exact Or.inr h
      · exact Or.inl h
    · refine Or.inl ⟨⟨h1.1, h1.2⟩, ?_⟩
      rcases (abs_eq (by linarith)).1 h3 with h | h
      · exact Or.inr h
      · exact Or.inl h

/-- `ωn + w ∈ Γ_n` for `w ∈ Γ_0`. -/
lemma zpt_mem {w : ℂ} (hw : w ∈ Gamma0 L) (n : ℤ) :
    OffgridCommutator.zpt L w n ∈
      Gam (HaarSummableReconstruction.lo L n) (HaarSummableReconstruction.hi L n)
        (HaarSummableReconstruction.ht L) := by
  rw [← Gam0_eq] at hw
  rw [OffgridCommutator.zpt_eq]
  simp only [HaarSummableReconstruction.lo, HaarSummableReconstruction.hi,
    HaarSummableReconstruction.ht, ← omegaL_eq_om]
  rcases hw with ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩
  · refine Or.inl ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [add_re, ofReal_re]; linarith
    · simp only [add_re, ofReal_re]; linarith
    · simpa only [add_im, ofReal_im, zero_add] using h3
  · refine Or.inr ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [add_im, ofReal_im, zero_add]; linarith
    · simp only [add_im, ofReal_im, zero_add]; linarith
    · rcases h3 with h3 | h3
      · left; simp only [add_re, ofReal_re, h3]; try ring
      · right; simp only [add_re, ofReal_re, h3]; try ring

lemma ew_zpt (w : ℂ) (n : ℤ) : exp (I * L * OffgridCommutator.zpt L w n) = ew L w := by
  have hL : (L : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : 0 < L).ne'
  rw [OffgridCommutator.zpt_eq, ew]
  have e : I * L * (((omegaL L * n : ℝ) : ℂ) + w) = n * (2 * Real.pi * I) + I * L * w := by
    unfold omegaL; push_cast; field_simp
  rw [e, exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]

end Geometry

/-! ## 3. Products near one -/

lemma norm_prod_sub_one_le {ι : Type*} (s : Finset ι) (a : ι → ℂ) :
    ‖∏ i ∈ s, (1 + a i) - 1‖ ≤ Real.exp (∑ i ∈ s, ‖a i‖) - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Real.exp_add]
    have e : (1 + a i) * ∏ j ∈ s, (1 + a j) - 1 = (1 + a i) * (∏ j ∈ s, (1 + a j) - 1) + a i := by
      ring
    rw [e]
    set S := ∑ j ∈ s, ‖a j‖
    have h1 := norm_add_le ((1 + a i) * (∏ j ∈ s, (1 + a j) - 1)) (a i)
    rw [norm_mul] at h1
    have h2 : ‖1 + a i‖ ≤ 1 + ‖a i‖ := (norm_add_le _ _).trans (by rw [norm_one])
    have h3 := Real.add_one_le_exp ‖a i‖
    have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => norm_nonneg (a j)
    have h4 : 0 ≤ Real.exp S - 1 := by have := Real.add_one_le_exp S; linarith
    have h5 : ‖1 + a i‖ * ‖∏ j ∈ s, (1 + a j) - 1‖ ≤ (1 + ‖a i‖) * (Real.exp S - 1) :=
      mul_le_mul h2 ih (norm_nonneg _) (by positivity)
    have h6 : (1 + ‖a i‖) * Real.exp S ≤ Real.exp ‖a i‖ * Real.exp S :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    nlinarith

lemma exp_sub_one_le (S : ℝ) : Real.exp S - 1 ≤ S * Real.exp S := by
  have h1 := Real.add_one_le_exp (-S)
  have h2 : Real.exp (-S) * Real.exp S = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h3 := Real.exp_pos S
  nlinarith

/-! ## 4. The eigenvalue tail -/

section Eigen

variable {L : ℝ} [Fact (0 < L)]

/-- `|∏(1 ± ic/(z − q_j)) − 1| ≤ exp S − 1` with `S = |c| Σ |z − q_j|^{-1}`. -/
lemma sFun_dev {N : ℕ} (c : ℝ) (q : Fin N → ℝ) (z : ℂ) (w : ℂ) (hew : exp (I * L * z) = ew L w) :
    ‖TransferSeparation.sFun L c q z - (1 + ew L w)‖ ≤
      (1 + ‖ew L w‖) * (Real.exp (∑ j, ‖I * c / (z - q j)‖) - 1) := by
  unfold TransferSeparation.sFun
  rw [hew]
  have e : (∏ j, (1 + I * c / (z - q j))) + ew L w * ∏ j, (1 - I * c / (z - q j)) - (1 + ew L w) =
      (∏ j, (1 + I * c / (z - q j)) - 1) + ew L w * (∏ j, (1 + -(I * c / (z - q j))) - 1) := by
    simp only [← sub_eq_add_neg]; ring
  rw [e]
  have h1 := norm_prod_sub_one_le Finset.univ (fun j => I * c / (z - q j))
  have h2 := norm_prod_sub_one_le Finset.univ (fun j => -(I * c / (z - q j)))
  simp only [norm_neg] at h2
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  have h3 : 0 ≤ Real.exp (∑ j, ‖I * c / (z - q j)‖) - 1 := by
    have := Real.add_one_le_exp (∑ j, ‖I * c / (z - q j)‖)
    have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => norm_nonneg (I * c / (z - q j))
    linarith
  have h4 := mul_le_mul_of_nonneg_left h2 (norm_nonneg (ew L w))
  nlinarith

/-- **The eigenvalue tail.** -/
theorem eig_tail (hL : 0 < L) {κ : ℝ} (hκ : 0 < κ) {E : ℝ} (hE : 0 < E) :
    ∃ R₁ C : ℝ, 2 ≤ R₁ ∧ 0 ≤ C ∧ ∀ (N : ℕ) (hN : 0 < N) (m : BetheLabels.MArr N),
      EnergyProjection.energyEig L κ N (NormalityBridge.label m) ≤ N * E →
      ∀ n : ℤ, R₁ < |(n : ℝ)| → ∀ w ∈ Gamma0 L,
        ‖NormalityBridge.eigen (L := L) κ hκ hN m (OffgridCommutator.zpt L w n) - (1 + ew L w)‖ ≤
          C / |(n : ℝ)| ∧
        ∀ j, omegaL L / 8 ≤
          ‖OffgridCommutator.zpt L w n -
            (BetheSmooth.sourceRoots L (NormalityBridge.label m).val (κ / N) j : ℂ)‖ := by
  obtain ⟨R, -, hHC⟩ := HighContours.high_contours hL hκ E hE
  set ω := HighContours.om L with hωdef
  have hω : 0 < ω := HighContours.om_pos hL
  set K1 : ℝ := (4 / ω) ^ 1 + 4 * E / ((ω / 8) ^ 1 * ω ^ 2) with hK1
  have hK10 : 0 ≤ K1 := by positivity
  set C : ℝ := M1 * (κ * K1 * Real.exp (κ * K1)) with hC
  have hM1 : 0 ≤ M1 := by have := M1_ge; linarith
  refine ⟨max R 2, C, le_max_right _ _, by positivity, ?_⟩
  intro N hN m hEm n hn w hw
  have hRn : R < |(n : ℝ)| := lt_of_le_of_lt (le_max_left _ _) hn
  have hn1 : 1 ≤ |(n : ℝ)| := by linarith [le_max_right R 2]
  have hn0 : 0 < |(n : ℝ)| := by linarith
  set c : ℝ := κ / N with hc
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hc0 : 0 < c := div_pos hκ hNr
  set lab := NormalityBridge.label m
  set q := BetheSmooth.sourceRoots L lab.val c with hq
  have hact := sourceRoots_actual hL hc0 lab.2
  have hEn : (N : ℝ)⁻¹ * ∑ j, (q ∘ Fin.rev) j ^ 2 ≤ E := by
    have e1 : ∑ j, (q ∘ Fin.rev) j ^ 2 = EnergyProjection.energyEig L κ N lab := by
      unfold EnergyProjection.energyEig
      exact sum_rev (fun j => q j ^ 2)
    rw [e1, inv_mul_le_iff₀ hNr]; linarith
  obtain ⟨hdist, -, hmom⟩ := hHC N (lab.val ∘ Fin.rev) (q ∘ Fin.rev) hact hEn n hRn
  set z := OffgridCommutator.zpt L w n with hz
  have hznb : z ∈ HighContours.nbhd L n := HaarSummableReconstruction.Gam_subset_nbhd hL n (zpt_mem hw n)
  have hd : ∀ j, ω / 8 ≤ ‖z - (q j : ℂ)‖ := fun j => by
    have := hdist z hznb (Fin.rev j)
    simpa [Function.comp, Fin.rev_rev] using this
  refine ⟨?_, fun j => by rw [omegaL_eq_om]; exact hd j⟩
  -- the eigenvalue is the transfer formula off the roots
  have hoff : ∀ k, z ≠ (q k : ℂ) := fun k h0 => by
    have := hd k; rw [h0, sub_self, norm_zero] at this; linarith
  have heig : NormalityBridge.eigen (L := L) κ hκ hN m z = TransferSeparation.sFun L c q z :=
    (BetheSpectralContinuity.basis_eigenvalue L (NormalityBridge.cpos hκ hN) lab.2).2.1 z hoff
  rw [heig]
  refine (sFun_dev c q z w (ew_zpt w n)).trans ?_
  -- the sum `S`
  set S := ∑ j, ‖I * c / (z - q j)‖ with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => norm_nonneg _
  have hSb : S ≤ κ * K1 * |(n : ℝ)|⁻¹ := by
    have hm1 := hmom 1 le_rfl z hznb
    have e1 : (N : ℝ)⁻¹ * ∑ j, (‖z - ((q ∘ Fin.rev) j : ℂ)‖ ^ 1)⁻¹ =
        (N : ℝ)⁻¹ * ∑ j, ‖z - (q j : ℂ)‖⁻¹ := by
      congr 1
      simp only [pow_one, Function.comp]
      exact sum_rev (fun j => ‖z - (q j : ℂ)‖⁻¹)
    rw [e1] at hm1
    have hm2 := hm1.trans (HaarSummableReconstruction.mom_le hL hE.le (s := 1) (r := 1) le_rfl
      (by norm_num) hn1)
    have e2 : S = κ * ((N : ℝ)⁻¹ * ∑ j, ‖z - (q j : ℂ)‖⁻¹) := by
      simp only [hSdef, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [HaarSummableCore.norm_u_eq, abs_of_pos hc0, hc]; ring
    rw [e2]
    have := mul_le_mul_of_nonneg_left hm2 hκ.le
    simp only [pow_one] at this
    simpa only [hK1, pow_one, mul_assoc] using this
  have hSb' : S ≤ κ * K1 := by
    have : |(n : ℝ)|⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn1
    calc S ≤ κ * K1 * |(n : ℝ)|⁻¹ := hSb
      _ ≤ κ * K1 * 1 := mul_le_mul_of_nonneg_left this (by positivity)
      _ = κ * K1 := mul_one _
  have h1 := exp_sub_one_le S
  have h2 : Real.exp S ≤ Real.exp (κ * K1) := Real.exp_le_exp.2 hSb'
  have h3 : 1 + ‖ew L w‖ ≤ M1 := by unfold M1; linarith [norm_ew_le hw]
  have h4 : Real.exp S - 1 ≤ κ * K1 * |(n : ℝ)|⁻¹ * Real.exp (κ * K1) :=
    h1.trans (mul_le_mul hSb h2 (Real.exp_pos _).le (by positivity))
  have h5 : 0 ≤ Real.exp S - 1 := by have := Real.add_one_le_exp S; linarith
  calc (1 + ‖ew L w‖) * (Real.exp S - 1) ≤ M1 * (κ * K1 * |(n : ℝ)|⁻¹ * Real.exp (κ * K1)) :=
        mul_le_mul h3 h4 h5 hM1
    _ = C / |(n : ℝ)| := by simp only [hC]; field_simp

end Eigen

/-! ## 5. The transfers and the energy projection in the actual Bethe basis -/

section Basis

/-- The actual physical Bethe basis at coupling `κ/N`. -/
abbrev bas (L : ℝ) [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) :
    HilbertBasis (BetheLabels.MArr N) ℂ (SymSector ℂ (L2T L) N) :=
  UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ

lemma diagC_of_apply {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {b : HilbertBasis ι ℂ E} {T : E →L[ℂ] E} {μ : ι → ℂ} (h : ∀ i, T (b i) = μ i • b i) :
    IsDiagC b T μ := by
  intro i v
  rw [← ContinuousLinearMap.adjoint_inner_left, TransferNormality.adjoint_diag b T μ h i,
    inner_smul_left, Complex.conj_conj]

variable (L : ℝ) [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N)

/-- `S_N(z)` is diagonal in the actual Bethe basis with the transfer eigenvalues. -/
lemma diagC_transfer (z : ℂ) :
    IsDiagC (bas L hκ hN) (normalizedTransfer L κ N z)
      (fun m => NormalityBridge.eigen (L := L) κ hκ hN m z) :=
  diagC_of_apply fun m => UnconditionalBetheBasis.transfer_physicalBasis hκ hN z m

/-- `X_{N,n}(w) = S_N(ωn + w) − (1 + e^{iwL})·1`. -/
def Xop (κ : ℝ) (N : ℕ) (w : ℂ) (n : ℤ) : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N :=
  normalizedTransfer L κ N (OffgridCommutator.zpt L w n) -
    (1 + ew L w) • (1 : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N)

lemma diagC_X (w : ℂ) (n : ℤ) :
    IsDiagC (bas L hκ hN) (Xop L κ N w n)
      (fun m => NormalityBridge.eigen (L := L) κ hκ hN m (OffgridCommutator.zpt L w n) -
        (1 + ew L w)) :=
  (diagC_transfer L hκ hN _).sub_smul_one _

/-- The energy-admissible labels `E_m ≤ NE`. -/
def adm (κ : ℝ) (N : ℕ) (E : ℝ) : Set (BetheLabels.MArr N) :=
  {m | EnergyProjection.energyEig L κ N (NormalityBridge.label m) ≤ N * E}

/-- The energy mask `1_{E_m ≤ NE}`. -/
def mask (κ : ℝ) (N : ℕ) (E : ℝ) (m : BetheLabels.MArr N) : ℂ :=
  by classical exact if m ∈ adm L κ N E then 1 else 0

lemma mask_of_mem {E : ℝ} {m : BetheLabels.MArr N} (hm : m ∈ adm L κ N E) : mask L κ N E m = 1 := by
  unfold mask; simp [hm]

lemma mask_of_not_mem {E : ℝ} {m : BetheLabels.MArr N} (hm : m ∉ adm L κ N E) :
    mask L κ N E m = 0 := by
  unfold mask; simp [hm]

lemma norm_mask_le (E : ℝ) (m : BetheLabels.MArr N) : ‖mask L κ N E m‖ ≤ 1 := by
  by_cases hm : m ∈ adm L κ N E
  · rw [mask_of_mem L hm, norm_one]
  · rw [mask_of_not_mem L hm, norm_zero]; exact zero_le_one

/-- `P_{N,E}` in the actual Bethe basis exists (a bounded diagonal projection). -/
theorem energyProjection_exists (E : ℝ) :
    ∃ P : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N,
      ∀ m, P (bas L hκ hN m) = mask L κ N E m • bas L hκ hN m := by
  obtain ⟨P, hP, -⟩ := QuantumNLS.HilbertDiagOp.diag_exists (bas L hκ hN)
    (mask L κ N E) 1 (norm_mask_le L E) zero_le_one
  exact ⟨P, fun m => (show IsDiagC (bas L hκ hN) P _ from hP).apply_basis m⟩

/-- The diagonal mask projection is the transport of `EnergyProjection.energy_projection` (the basis form of
`1_{[0,NE]}(H_N)` on the position carrier) through `symmetricPosition`. -/
theorem energyProjection_phys (E : ℝ) (s : Finset ℤ) (t : ℤ → ℝ) :
    ∃ P₀ : ContactOperator.SymL2 L N →L[ℂ] ContactOperator.SymL2 L N,
      (∀ n : BetheFreeFamily.Label N,
        P₀ (BetheConditionalBasis.normalizedWave L N
          ⟨κ / (N : ℝ), (div_pos hκ (by exact_mod_cast hN)).le⟩ n) =
          ((if EnergyProjection.energyEig L κ N n ≤ (N : ℝ) * E then (1 : ℝ) else 0 : ℝ) : ℂ) •
            BetheConditionalBasis.normalizedWave L N
              ⟨κ / (N : ℝ), (div_pos hκ (by exact_mod_cast hN)).le⟩ n) ∧
      P₀ * P₀ = P₀ ∧ ContinuousLinearMap.adjoint P₀ = P₀ ∧
      ∀ m, ((BethePhysicalTransfer.symmetricPosition L N).symm
          (P₀ (BethePhysicalTransfer.symmetricPosition L N (bas L hκ hN m)))) =
        mask L κ N E m • bas L hκ hN m := by
  obtain ⟨P₀, hP₀, hidem, hsa, -, -⟩ :=
    EnergyProjection.energy_projection L κ hκ N (by omega) E s t
  refine ⟨P₀, hP₀, hidem, hsa, fun m => ?_⟩
  have hpos := UnconditionalBetheBasis.physicalBasis_position L N (by omega) (κ / N)
    (div_pos hκ (by exact_mod_cast hN)) m
  have hb : bas L hκ hN m = UnconditionalBetheBasis.physicalBasis L N (by omega) (κ / N)
      (div_pos hκ (by exact_mod_cast hN)) m := rfl
  rw [hb, hpos, hP₀, map_smul, ← hpos, LinearIsometryEquiv.symm_apply_apply]
  by_cases hm : m ∈ adm L κ N E
  · rw [mask_of_mem L hm]
    have : EnergyProjection.energyEig L κ N ((BetheConditionalBasis.labelArr N).symm m) ≤ N * E := hm
    simp [this]
  · rw [mask_of_not_mem L hm]
    have : ¬ EnergyProjection.energyEig L κ N ((BetheConditionalBasis.labelArr N).symm m) ≤ N * E :=
      hm
    simp [this]

variable {L}

lemma diagC_P {E : ℝ} {P : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N}
    (hP : ∀ m, P (bas L hκ hN m) = mask L κ N E m • bas L hκ hN m) :
    IsDiagC (bas L hκ hN) P (mask L κ N E) := diagC_of_apply hP

lemma supp_P {E : ℝ} {P : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N}
    (hP : ∀ m, P (bas L hκ hN m) = mask L κ N E m • bas L hκ hN m)
    (φ : SymSector ℂ (L2T L) N) :
    Supp (bas L hκ hN) (adm L κ N E) (P φ) := fun m hm => by
  rw [diagC_P hκ hN hP m φ, mask_of_not_mem L hm, zero_mul]

lemma norm_P_le {E : ℝ} {P : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N}
    (hP : ∀ m, P (bas L hκ hN m) = mask L κ N E m • bas L hκ hN m)
    (φ : SymSector ℂ (L2T L) N) : ‖P φ‖ ≤ ‖φ‖ := by
  have := (diagC_P hκ hN hP).norm_le (A := univ) zero_le_one (fun m _ => norm_mask_le L E m)
    (v := φ) (fun m hm => absurd (mem_univ m) hm)
  linarith

end Basis

/-! ## 6. `QG:eq:haar-small-spectral-tail` -/

/-- **`‖X_{N,n}(w) P_{N,E}‖ ≤ C_E/|n|`**, uniformly in `w ∈ Γ_0`, `N ≥ 1` and `|n| > R₁`. -/
theorem small_spectral_tail {L : ℝ} [Fact (0 < L)] (hL : 0 < L) {κ : ℝ} (hκ : 0 < κ) {E : ℝ}
    (hE : 0 < E) :
    ∃ R₁ C : ℝ, 2 ≤ R₁ ∧ 0 ≤ C ∧ ∀ (N : ℕ) (hN : 0 < N)
      (P : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N),
      (∀ m, P (bas L hκ hN m) = mask L κ N E m • bas L hκ hN m) →
      ∀ n : ℤ, R₁ < |(n : ℝ)| → ∀ w ∈ Gamma0 L, ∀ φ,
        ‖(Xop L κ N w n * P) φ‖ ≤ C / |(n : ℝ)| * ‖φ‖ := by
  obtain ⟨R₁, C, hR, hC, htail⟩ := eig_tail hL hκ hE
  refine ⟨R₁, C, hR, hC, fun N hN P hP n hn w hw φ => ?_⟩
  have hn0 : 0 < |(n : ℝ)| := by linarith
  show ‖Xop L κ N w n (P φ)‖ ≤ _
  refine ((diagC_X L hκ hN w n).norm_le (by positivity) (fun m hm => (htail N hN m hm n hn w hw).1)
    (supp_P hκ hN hP φ)).trans ?_
  exact mul_le_mul_of_nonneg_left (norm_P_le hκ hN hP φ) (by positivity)

end QuantumNLS.HaarSpectralTail

#print axioms QuantumNLS.HaarSpectralTail.sourceRoots_actual
#print axioms QuantumNLS.HaarSpectralTail.Gam0_eq
#print axioms QuantumNLS.HaarSpectralTail.eig_tail
#print axioms QuantumNLS.HaarSpectralTail.energyProjection_phys
#print axioms QuantumNLS.HaarSpectralTail.small_spectral_tail
