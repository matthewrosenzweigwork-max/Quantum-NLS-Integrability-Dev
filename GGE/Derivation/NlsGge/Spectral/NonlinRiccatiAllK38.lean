import NlsGge.Spectral.RTreeExpansion38
import NlsGge.Spectral.RTreeBornTruncation38
import NlsGge.Spectral.RTreeCoeffIdent38
import NlsGge.Spectral.R3cIdentification38
import NlsGge.Spectral.R3cExpansionK1_38
import NlsGge.Spectral.NonlinearRemainderDensity38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis NlsGge.HierarchyRiccati.Core

/-! # R3c piece T10: `NonlinRiccatiSmoothBound38 k` for every `k ≥ 1`

Chain: P4a (`r3c_im_eq_pair38` at `|B|`) and P4b (`quadRiccati38_eq_pair38`) give
`n_η = Re ⟪U, Γ - G₀⟫`; T8 (`pair_born_truncation38`, `L = k`) replaces `Γ` by
`Σ_{ℓ ≤ k} G_ℓ`; T7 writes each `⟪U, G_ℓ⟫` as a sum of tree terms; T6 (`RTerm38.expOK_main`)
expands each tree term with a uniform remainder; T9 (`nonlin_coeff_ident38`) identifies the
coefficients. -/

/-! ## Born pairings as sums of tree terms -/

theorem pair_bornG38_eq {η : ℝ} (hη : 0 < η) (N : ℕ) (z : FourierPlane N) (ℓ : ℕ) :
    pair38 (planeReal N z) (bornG38 η N z ℓ) =
      ((bornTrees38 ℓ).map (fun T => (⟨(-1 : ℂ) ^ ℓ, 0, 0, T⟩ : RTerm38).val η N z)).sum := by
  have h1 : bornG38 η N z ℓ = fun x => (-1 : ℂ) ^ ℓ *
      ((bornTrees38 ℓ).map (fun T => T.eval η N z x)).sum := rfl
  rw [h1]
  have h2 : pair38 (planeReal N z) (fun x => (-1 : ℂ) ^ ℓ *
      ((bornTrees38 ℓ).map (fun T => T.eval η N z x)).sum) =
      (-1 : ℂ) ^ ℓ * pair38 (planeReal N z)
        (fun x => ((bornTrees38 ℓ).map (fun T => T.eval η N z x)).sum) := by
    unfold pair38
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    ring
  rw [h2]
  have h3 := pair38_list_sum_right (planeReal N z) (planeReal_smooth38 N z).continuous
    (bornTrees38 ℓ) (fun T x => T.eval η N z x)
    (fun T _ => (RTree38.eval_cont_per hη N z T).1)
  rw [h3, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left (fun T _ => ?_))
  simp [RTerm38.val, leafU38_zero_eq]

theorem expOK_born38 (k : ℕ) (hk : 1 ≤ k) (B : ℝ) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ k) :
    ExpOK38 k B 3 (fun N z η => pair38 (planeReal N z) (bornG38 η N z ℓ)) := by
  have hL : ExpOK38 k B 3 (fun N z η => ((bornTrees38 ℓ).map
      (fun T => (⟨(-1 : ℂ) ^ ℓ, 0, 0, T⟩ : RTerm38).val η N z)).sum) := by
    refine ExpOK38.list_sum (bornTrees38 ℓ)
      (fun T N z η => (⟨(-1 : ℂ) ^ ℓ, 0, 0, T⟩ : RTerm38).val η N z) (fun T hT => ?_)
    obtain ⟨a, b, _⟩ := bornTrees38_nodes ℓ T hT
    have hmain := RTerm38.expOK_main k hk B _ (⟨(-1 : ℂ) ^ ℓ, 0, 0, T⟩ : RTerm38)
      (by simp only [RTerm38.weight]; omega) (by simp only; omega)
      (by simp only; omega) rfl
    refine ExpOK38.mono ?_ hmain
    simp only [RTerm38.weight]; omega
  exact hL.congr (fun N z η hη => (pair_bornG38_eq hη N z ℓ).symm)

theorem expOK_born_sum38 (k : ℕ) (hk : 1 ≤ k) (B : ℝ) :
    ∀ n : ℕ, n ≤ k → ExpOK38 k B 3 (fun N z η =>
      ∑ ℓ ∈ Finset.range n, pair38 (planeReal N z) (bornG38 η N z (ℓ + 1))) := by
  intro n
  induction n with
  | zero => intro _; simpa using ExpOK38.zero k B 3
  | succ n ih =>
    intro hn
    have := (ih (by omega)).add (expOK_born38 k hk B (n + 1) (by omega) (by omega))
    simpa only [Finset.sum_range_succ] using this

/-! ## Linearity of the pairing over the Born sums -/

theorem pair38_range_sum_right {η : ℝ} (hη : 0 < η) (N : ℕ) (z : FourierPlane N) (n : ℕ) :
    pair38 (planeReal N z) (fun x => ∑ ℓ ∈ Finset.range n, bornG38 η N z (ℓ + 1) x) =
      ∑ ℓ ∈ Finset.range n, pair38 (planeReal N z) (bornG38 η N z (ℓ + 1)) := by
  have h := pair38_list_sum_right (planeReal N z) (planeReal_smooth38 N z).continuous
    (List.range n) (fun ℓ x => bornG38 η N z (ℓ + 1) x)
    (fun ℓ _ => (bornG38_cont_per hη N z (ℓ + 1)).1)
  rw [list_range_sum38] at h
  simp only [list_range_sum38] at h
  exact h

theorem pair38_sub_sum38 {η : ℝ} (hη : 0 < η) (N : ℕ) (z : FourierPlane N) {Γ : ℝ → ℂ}
    (hΓc : Continuous Γ) (k : ℕ) :
    pair38 (planeReal N z) (fun x => Γ x - ∑ ℓ ∈ Finset.range (k + 1), bornG38 η N z ℓ x) =
      pair38 (planeReal N z) Γ - pair38 (planeReal N z) (bornG38 η N z 0) -
        ∑ ℓ ∈ Finset.range k, pair38 (planeReal N z) (bornG38 η N z (ℓ + 1)) := by
  have hUc : Continuous (planeReal N z) := (planeReal_smooth38 N z).continuous
  have hGc : ∀ ℓ, Continuous (bornG38 η N z ℓ) := fun ℓ => (bornG38_cont_per hη N z ℓ).1
  have hsc : Continuous (fun x => ∑ ℓ ∈ Finset.range k, bornG38 η N z (ℓ + 1) x) :=
    continuous_finsetSum _ fun ℓ _ => hGc (ℓ + 1)
  have e1 : (fun x => Γ x - ∑ ℓ ∈ Finset.range (k + 1), bornG38 η N z ℓ x) =
      fun x => Γ x - (bornG38 η N z 0 x + ∑ ℓ ∈ Finset.range k, bornG38 η N z (ℓ + 1) x) := by
    funext x
    rw [Finset.sum_range_succ']
    ring
  rw [e1]
  have hrest := pair38_range_sum_right hη N z k
  unfold pair38 at hrest ⊢
  have i1 : IntervalIntegrable (fun x => planeReal N z x * Γ x) volume 0 1 :=
    (hUc.mul hΓc).intervalIntegrable 0 1
  have i2 : IntervalIntegrable (fun x => planeReal N z x * bornG38 η N z 0 x) volume 0 1 :=
    (hUc.mul (hGc 0)).intervalIntegrable 0 1
  have i3 : IntervalIntegrable (fun x => planeReal N z x *
      ∑ ℓ ∈ Finset.range k, bornG38 η N z (ℓ + 1) x) volume 0 1 :=
    (hUc.mul hsc).intervalIntegrable 0 1
  have e2 : (fun x => planeReal N z x * (Γ x - (bornG38 η N z 0 x +
      ∑ ℓ ∈ Finset.range k, bornG38 η N z (ℓ + 1) x))) =
      fun x => (planeReal N z x * Γ x - planeReal N z x * bornG38 η N z 0 x) -
        planeReal N z x * ∑ ℓ ∈ Finset.range k, bornG38 η N z (ℓ + 1) x := by
    funext x; ring
  rw [e2, intervalIntegral.integral_sub (i1.sub i2) i3, intervalIntegral.integral_sub i1 i2, hrest]

/-! ## The sum of the coefficients -/

/-- the target sum over `j ≤ k` equals the sum over `w ∈ [3, 2k+1]` of the real parts of `c w`,
once `c` is identified with the charges. -/
theorem target_sum_eq38 (k N : ℕ) (z : FourierPlane N) (c : ℕ → ℂ) (η : ℝ) (hη : 0 < η)
    (hc0 : ∀ w < 3, c w = 0)
    (hid : ∀ w ∈ Finset.Icc 3 (2 * k + 1), (c w).re =
      if Even w then 0 else (-1 : ℝ) ^ ((w - 1) / 2) / (2 * 4 ^ ((w - 1) / 2)) *
        (localCharge38 (planeReal N z) ((w - 1) / 2) -
          ∑ i : Fin (2 * N + 1), (2 * Real.pi * (modeIndex N i : ℤ)) ^ (w - 1) * ‖z i‖ ^ 2)) :
    ∑ j ∈ Finset.range (k + 1), (-1 : ℝ) ^ j / (2 * 4 ^ j * η ^ (2 * j + 1)) *
        (localCharge38 (planeReal N z) j -
          ∑ i : Fin (2 * N + 1), (2 * Real.pi * (modeIndex N i : ℤ)) ^ (2 * j) * ‖z i‖ ^ 2) =
      ∑ w ∈ Finset.Icc 3 (2 * k + 1), (c w).re * η⁻¹ ^ w := by
  set g : ℕ → ℝ := fun m => if m < 2 * k + 2 then (c m).re * η⁻¹ ^ m else 0 with hg
  have hsub : ∑ w ∈ Finset.Icc 3 (2 * k + 1), (c w).re * η⁻¹ ^ w =
      ∑ m ∈ Finset.range (2 * k + 2), g m := by
    have h1 : ∑ w ∈ Finset.Icc 3 (2 * k + 1), (c w).re * η⁻¹ ^ w =
        ∑ m ∈ Finset.range (2 * k + 2), (c m).re * η⁻¹ ^ m := by
      apply Finset.sum_subset
      · intro x hx
        simp only [Finset.mem_Icc] at hx
        simp only [Finset.mem_range]; omega
      · intro x hx hx'
        simp only [Finset.mem_range] at hx
        simp only [Finset.mem_Icc, not_and, not_le] at hx'
        have : x < 3 := by
          by_contra hcon
          have := hx' (not_lt.mp hcon); omega
        simp [hc0 x this]
    rw [h1]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    have hm' : m < 2 * k + 2 := Finset.mem_range.mp hm
    simp [hg, hm']
  have hg0 : ∀ j, g (2 * j) = 0 := by
    intro j
    simp only [hg]
    split_ifs with h
    · by_cases h3 : 2 * j < 3
      · simp [hc0 _ h3]
      · have := hid (2 * j) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        simp only [even_two_mul, ite_true] at this
        simp [this]
    · rfl
  rw [hsub, sum_range_odd38 g hg0 k]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' : j < k + 1 := Finset.mem_range.mp hj
  have hlt : 2 * j + 1 < 2 * k + 2 := by omega
  have hgj : g (2 * j + 1) = (c (2 * j + 1)).re * η⁻¹ ^ (2 * j + 1) := by simp [hg, hlt]
  rw [hgj]
  by_cases hj0 : j = 0
  · subst hj0
    have h0 := nonlinCharge_zero_r3c N z
    simp only [mul_zero] at h0
    simp only [mul_zero, zero_add, pow_zero]
    have h0' : localCharge38 (planeReal N z) 0 - ∑ x : Fin (2 * N + 1), ‖z x‖ ^ 2 = 0 := by
      simpa using h0
    rw [hc0 1 (by norm_num)]
    simp [h0']
  · have := hid (2 * j + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    simp only [Nat.not_even_two_mul_add_one, ite_false] at this
    have e1 : (2 * j + 1 - 1) / 2 = j := by omega
    have e2 : 2 * j + 1 - 1 = 2 * j := by omega
    rw [e1, e2] at this
    rw [this, inv_pow]
    have hη' : η ≠ 0 := hη.ne'
    field_simp

/-! ## The main theorem -/

theorem nonlinRiccatiSmoothBound38_all (k : ℕ) (hk : 1 ≤ k) : NonlinRiccatiSmoothBound38 k := by
  intro B
  obtain ⟨ηP, hηP, hP⟩ := r3c_im_eq_pair38 |B| (abs_nonneg B)
  set A : ℝ := Real.sqrt bracketSumE02_38 * |B| with hAdef
  have hA0 : 0 ≤ A := mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
  obtain ⟨CT, hCT0, hCT⟩ := pair_born_truncation38 k A hA0
  obtain ⟨η₃, C₃, hη₃, hC₃, hE⟩ := expOK_born_sum38 k hk B k le_rfl
  set η₀ : ℝ := max (max ηP η₃) (max (4 * A) 1) with hη₀
  have hη₀1 : 1 ≤ η₀ := (le_max_right _ _).trans' (le_max_right _ _)
  refine ⟨η₀, A * CT + C₃, lt_of_lt_of_le one_pos hη₀1, by positivity, ?_⟩
  intro N z hS η hη
  have hηP' : ηP ≤ η := ((le_max_left _ _).trans (le_max_left _ _)).trans hη
  have hη₃' : η₃ ≤ η := ((le_max_right _ _).trans (le_max_left _ _)).trans hη
  have hηA : max (4 * A) 1 ≤ η := (le_max_right _ _).trans hη
  have hη1 : 1 ≤ η := hη₀1.trans hη
  have hηpos : 0 < η := by linarith
  -- `S_1 ≤ S_k ≤ B²`
  have hS1 : ∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ 1 * ‖z i‖ ^ 2 ≤
      |B| ^ 2 := by
    rw [sq_abs]
    refine le_trans (Finset.sum_le_sum fun i _ => ?_) hS
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact pow_le_pow_right₀ (by nlinarith [sq_nonneg ((modeIndex N i : ℤ) : ℝ)]) hk
  have hUb : ∀ x, ‖planeReal N z x‖ ≤ A := by
    intro x
    refine (plane_sup_le_r3c N z x).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    calc Real.sqrt (∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ 1 * ‖z i‖ ^ 2)
        ≤ Real.sqrt (|B| ^ 2) := Real.sqrt_le_sqrt hS1
      _ = |B| := Real.sqrt_sq (abs_nonneg _)
  obtain ⟨c, hc0, hb⟩ := hE N z hS
  set Cc : ℝ := A * CT + C₃ with hCc
  have hrepl : ∀ η' : ℝ, ∑ w ∈ Finset.Icc 3 (2 * k + 1), (c w).re * η'⁻¹ ^ w =
      (∑ w ∈ Finset.range (2 * k + 2), c w * (η' : ℂ)⁻¹ ^ w).re := by
    intro η'
    have hsub : ∑ w ∈ Finset.Icc 3 (2 * k + 1), (c w).re * η'⁻¹ ^ w =
        ∑ w ∈ Finset.range (2 * k + 2), (c w).re * η'⁻¹ ^ w := by
      apply Finset.sum_subset
      · intro x hx
        simp only [Finset.mem_Icc] at hx
        simp only [Finset.mem_range]; omega
      · intro x hx hx'
        simp only [Finset.mem_range] at hx
        simp only [Finset.mem_Icc, not_and, not_le] at hx'
        have : x < 3 := by
          by_contra hcon
          have := hx' (not_lt.mp hcon); omega
        simp [hc0 x this]
    rw [hsub, Complex.re_sum]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    have : (η' : ℂ)⁻¹ ^ w = ((η'⁻¹ ^ w : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.re_mul_ofReal]
  have hkey : ∀ η' : ℝ, η₀ ≤ η' →
      |nonlinPart38 N z η' - ∑ w ∈ Finset.Icc 3 (2 * k + 1), (c w).re * η'⁻¹ ^ w| ≤
        Cc * η'⁻¹ ^ (2 * k + 2) := by
    intro η' hη'
    have hηP'' : ηP ≤ η' := ((le_max_left _ _).trans (le_max_left _ _)).trans hη'
    have hη₃'' : η₃ ≤ η' := ((le_max_right _ _).trans (le_max_left _ _)).trans hη'
    have hηA' : max (4 * A) 1 ≤ η' := (le_max_right _ _).trans hη'
    have hη1' : 1 ≤ η' := hη₀1.trans hη'
    have hηpos' : 0 < η' := by linarith
    obtain ⟨Γ', hΓc', hΓp', hΓd', hΓb', hΓk'⟩ := hP N z hS1 η' hηP''
    have hqu' := quadRiccati38_eq_pair38 N z hηpos'
    have hnl' : nonlinPart38 N z η' =
        (pair38 (planeReal N z)
          (fun x => Γ' x - ∑ ℓ ∈ Finset.range (k + 1), bornG38 η' N z ℓ x)).re +
          (∑ ℓ ∈ Finset.range k, pair38 (planeReal N z) (bornG38 η' N z (ℓ + 1))).re := by
      unfold nonlinPart38
      rw [hΓk', hqu', pair38_sub_sum38 hηpos' N z hΓc' k, ← bornG38_zero]
      simp only [Complex.sub_re]
      ring
    have hD' := hCT N z Γ' hUb hηA' hΓc' hΓp' (fun x => hΓd' x) (fun x => hΓb' x)
    have hb'' := hb η' hη₃''
    rw [hnl', hrepl η']
    set D := pair38 (planeReal N z)
      (fun x => Γ' x - ∑ ℓ ∈ Finset.range (k + 1), bornG38 η' N z ℓ x) with hDdef
    set S := ∑ ℓ ∈ Finset.range k, pair38 (planeReal N z) (bornG38 η' N z (ℓ + 1)) with hSdef
    set P := ∑ w ∈ Finset.range (2 * k + 2), c w * (η' : ℂ)⁻¹ ^ w with hPdef
    have e : D.re + S.re - P.re = (D + (S - P)).re := by simp [Complex.add_re, Complex.sub_re]; ring
    rw [e]
    have hnorm : ‖D + (S - P)‖ ≤ A * CT / η' ^ (2 * k + 3) + C₃ * η'⁻¹ ^ (2 * k + 2) :=
      (norm_add_le _ _).trans (add_le_add hD' hb'')
    have hinv : η'⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hη1'
    have hinv0 : 0 ≤ η'⁻¹ := by positivity
    have e3 : A * CT / η' ^ (2 * k + 3) = A * CT * η'⁻¹ ^ (2 * k + 3) := by
      rw [inv_pow]; field_simp
    have h4 : η'⁻¹ ^ (2 * k + 3) ≤ η'⁻¹ ^ (2 * k + 2) :=
      pow_le_pow_of_le_one hinv0 hinv (by omega)
    calc |(D + (S - P)).re| ≤ ‖D + (S - P)‖ := Complex.abs_re_le_norm _
      _ ≤ A * CT * η'⁻¹ ^ (2 * k + 3) + C₃ * η'⁻¹ ^ (2 * k + 2) := by rw [← e3]; exact hnorm
      _ ≤ A * CT * η'⁻¹ ^ (2 * k + 2) + C₃ * η'⁻¹ ^ (2 * k + 2) := by
          have := mul_le_mul_of_nonneg_left h4 (mul_nonneg hA0 hCT0)
          linarith
      _ = Cc * η'⁻¹ ^ (2 * k + 2) := by rw [hCc]; ring
  have hid := nonlin_coeff_ident38 k N z c Cc η₀ hkey
  have hc0' : ∀ w < 3, c w = 0 := hc0
  have htgt := target_sum_eq38 k N z c η hηpos hc0' hid
  have hk' := hkey η hη
  show |η ^ (2 * k + 1) * (nonlinPart38 N z η -
    ∑ j ∈ Finset.range (k + 1), (-1 : ℝ) ^ j / (2 * 4 ^ j * η ^ (2 * j + 1)) *
        (localCharge38 (planeReal N z) j -
          ∑ i : Fin (2 * N + 1), (2 * Real.pi * (modeIndex N i : ℤ)) ^ (2 * j) * ‖z i‖ ^ 2))| ≤ _
  rw [htgt, abs_mul, abs_of_pos (by positivity : 0 < η ^ (2 * k + 1))]
  calc η ^ (2 * k + 1) * |nonlinPart38 N z η - ∑ w ∈ Finset.Icc 3 (2 * k + 1), (c w).re * η⁻¹ ^ w|
      ≤ η ^ (2 * k + 1) * (Cc * η⁻¹ ^ (2 * k + 2)) :=
        mul_le_mul_of_nonneg_left hk' (by positivity)
    _ = Cc / η := by
        rw [inv_pow]; field_simp; ring

end NlsGge.SpectralFoundations
end
