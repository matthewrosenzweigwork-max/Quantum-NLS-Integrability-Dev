import NlsGge.GK38.AbelianJacobianDiagonalEquiv
import NlsGge.GK38.AbelianInputDiscPlacement
import NlsGge.GK38.AbelianJacobianCommonRows
import NlsGge.GK38.IsolatingPersistence

/-! Original-family neighborhoods and locally uniform actual Jacobian rows.
Draft pending independent target/source review and default native elaboration.
All original sigma placements and every signed omitted index are retained. -/
set_option autoImplicit false
open Set Filter Topology Metric
namespace NlsGge.GK38.P3JacobianColumns
noncomputable section

 theorem original_family_neighborhoods (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW)
    (s₀ : Lib.L2Seq) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam₀ : IsolatingFamily38 φ₀ C R)
    (hσ₀ : ∀ k : ℤ, Lib.sigmaOf s₀ k ∈ ball (C k) (R k)) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ U ⊆ gkW ∧
    ∃ V : Set Lib.L2Seq, V ∈ 𝓝 s₀ ∧
    ∃ (c : ℝ) (N : ℕ), IsolatingGeometry38 C R c N ∧
      (∀ φ ∈ U, IsolatingFamily38 φ C R) ∧
      ∀ s ∈ V, ∀ k : ℤ, Lib.sigmaOf s k ∈ ball (C k) (R k) := by
  obtain ⟨ρ,hρ,c,N,hg,hsp⟩ := fixed_family_persistence38 φ₀ C R hfam₀
  obtain ⟨V,hV,hVσ⟩ := p3Input_all_own_disc38 s₀ C R c N hg hσ₀
  refine ⟨ball φ₀ ρ ∩ gkW,inter_mem (ball_mem_nhds _ hρ) (isOpen_gkW.mem_nhds hφ₀),
    inter_subset_right,V,hV,c,N,hg,?_,hVσ⟩
  intro φ hφ
  exact ⟨c,N,hg,hsp φ hφ.1⟩

 theorem original_family_uniform_complex_rows (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW)
    (s₀ : Lib.L2Seq) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam₀ : IsolatingFamily38 φ₀ C R)
    (hσ₀ : ∀ k : ℤ, Lib.sigmaOf s₀ k ∈ ball (C k) (R k)) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ U ⊆ gkW ∧
    ∃ V : Set Lib.L2Seq, V ∈ 𝓝 s₀ ∧
    ∃ (c : ℝ) (N : ℕ) (B : ℝ), IsolatingGeometry38 C R c N ∧
      (∀ φ ∈ U, IsolatingFamily38 φ C R) ∧
      (∀ s ∈ V, ∀ k : ℤ, Lib.sigmaOf s k ∈ ball (C k) (R k)) ∧ 0 ≤ B ∧
      ∀ φ ∈ U, ∀ s ∈ V, ∃ a e : ℤ → ℝ,
        (∀ m, 0 ≤ a m) ∧ (∀ m, 0 ≤ e m) ∧
        Summable (fun m : ℤ => a m^2) ∧ Summable (fun m : ℤ => e m^2) ∧
        (∑' m : ℤ, a m^2) ≤ B ∧ (∑' m : ℤ, e m^2) ≤ B ∧
        (∀ (n : ℤ) (m : P2Index38 n),
          ‖(fderiv ℂ (fun t : P2Space38 n => p2Fn38 n (φ,t)) (p2Restrict38 n s))
            (lp.single 2 m (1 : ℂ)) m-2‖ ≤ a m.1) ∧
        (∀ (n : ℤ) (m r : P2Index38 n), r ≠ m →
          ‖(fderiv ℂ (fun t : P2Space38 n => p2Fn38 n (φ,t)) (p2Restrict38 n s))
            (lp.single 2 r (1 : ℂ)) m‖ ≤ e m.1*Lib.c3w m.1 r.1) := by
  obtain ⟨Ug,hUg,hUgW,Vg,hVg,c,N,hgeom,hfamily,hσg⟩ :=
    original_family_neighborhoods φ₀ hφ₀ s₀ C R hfam₀ hσ₀
  obtain ⟨Ur,hUr,_hUrW,Vr,hVr,Br,H,hBr,hH,hr⟩ :=
    p3OmittedRatio_all_cut_error38 φ₀ hφ₀ s₀
  obtain ⟨Ue,hUe,_hUeW,Ve,hVe,Be,hBe,he⟩ :=
    p2RowEnvelope_common_l2_bound38 φ₀ hφ₀ s₀
  obtain ⟨Vf,hVf,Bf,hBf,hf⟩ := p3InputRowEnvelope_common_bound38 s₀
  let U := Ug ∩ (Ur ∩ Ue)
  let V := Vg ∩ (Vr ∩ (Ve ∩ Vf))
  let α : ℝ := 2*c*H
  let β : ℝ := 2*Real.pi*c^2*H
  let Bd : ℝ := 3*α^2*Be+3*α^2*Bf+12*Br
  let Bo : ℝ := β^2*Be
  have hc : 0 ≤ c := (by norm_num : (0 : ℝ) ≤ 1).trans hgeom.2.2.1
  have hα : 0 ≤ α := mul_nonneg (mul_nonneg (by norm_num) hc) hH
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hBd : 0 ≤ Bd := by dsimp [Bd]; positivity
  have hBo : 0 ≤ Bo := mul_nonneg (sq_nonneg β) hBe
  refine ⟨U,inter_mem hUg (inter_mem hUr hUe),fun φ hφ => hUgW hφ.1,
    V,inter_mem hVg (inter_mem hVr (inter_mem hVe hVf)),c,N,Bd+Bo,hgeom,
    (fun φ hφ => hfamily φ hφ.1),(fun s hs => hσg s hs.1),add_nonneg hBd hBo,?_⟩
  intro φ hφ s hs
  have hφW : φ ∈ gkW := hUgW hφ.1
  have hfam := hfamily φ hφ.1
  have hσ (k : ℤ) : Lib.sigmaOf s k ∈ closedBall (C k) (R k) :=
    ball_subset_closedBall (hσg s hs.1 k)
  obtain ⟨b,hb0,hbs,hbB,hb⟩ := hr φ hφ.2.1 s hs.2.1
  obtain ⟨hEs,hEB⟩ := he φ hφ.2.2 s hs.2.2.1
  obtain ⟨hFs,hFB⟩ := hf s hs.2.2.2
  let a : ℤ → ℝ := fun m => α*p2RowEnvelope38 φ s m+α*p3InputRowEnvelope38 s m+2*b m
  let e : ℤ → ℝ := fun m => β*p2RowEnvelope38 φ s m
  have ha0 (m : ℤ) : 0 ≤ a m := by
    exact add_nonneg
      (add_nonneg (mul_nonneg hα (p2RowEnvelope_nonneg38 φ s m))
        (mul_nonneg hα (Real.sqrt_nonneg _))) (mul_nonneg (by norm_num) (hb0 m))
  have he0 (m : ℤ) : 0 ≤ e m := mul_nonneg hβ (p2RowEnvelope_nonneg38 φ s m)
  have hdom : Summable (fun m : ℤ => 3*α^2*p2RowEnvelope38 φ s m^2+
      3*α^2*p3InputRowEnvelope38 s m^2+12*b m^2) :=
    ((hEs.mul_left (3*α^2)).add (hFs.mul_left (3*α^2))).add (hbs.mul_left 12)
  have hsq (m : ℤ) : a m^2 ≤ 3*α^2*p2RowEnvelope38 φ s m^2+
      3*α^2*p3InputRowEnvelope38 s m^2+12*b m^2 := by
    dsimp [a]
    nlinarith [sq_nonneg (α*p2RowEnvelope38 φ s m-α*p3InputRowEnvelope38 s m),
      sq_nonneg (α*p2RowEnvelope38 φ s m-2*b m),
      sq_nonneg (α*p3InputRowEnvelope38 s m-2*b m)]
  have has : Summable (fun m : ℤ => a m^2) :=
    hdom.of_nonneg_of_le (fun _ => sq_nonneg _) hsq
  have haB : (∑' m : ℤ, a m^2) ≤ Bd := by
    apply (has.tsum_le_tsum hsq hdom).trans
    rw [((hEs.mul_left (3*α^2)).add (hFs.mul_left (3*α^2))).tsum_add (hbs.mul_left 12),
      (hEs.mul_left (3*α^2)).tsum_add (hFs.mul_left (3*α^2)),
      tsum_mul_left,tsum_mul_left,tsum_mul_left]
    exact add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left hEB (by positivity))
        (mul_le_mul_of_nonneg_left hFB (by positivity)))
      (mul_le_mul_of_nonneg_left hbB (by norm_num))
  have hes : Summable (fun m : ℤ => e m^2) := by
    simpa only [e,mul_pow] using hEs.mul_left (β^2)
  have heB : (∑' m : ℤ, e m^2) ≤ Bo := by
    simp only [e,mul_pow,tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hEB (sq_nonneg β)
  refine ⟨a,e,ha0,he0,has,hes,haB.trans (le_add_of_nonneg_right hBo),
    heB.trans (le_add_of_nonneg_left hBd),?_,?_⟩
  · intro n m
    have hp := diagonal_period_sub_two_bound φ hφW C R c N hgeom hfam
      s n m.1 m.2.symm (hσ n) H (b m.1) hH (hb0 m.1)
      (fun z hz => (hb m.1 z hz).2) (fun z hz => (hb m.1 z hz).1)
    rw [matrix_coordinate n m m φ hφW]
    have hcol : p3NumeratorColumn38 n m.1 (p2Extend38 n (p2Restrict38 n s)) =
        p3NumeratorColumn38 n m.1 s := funext (column_extend_restrict n m.1 s)
    rw [hcol]
    apply hp.trans_eq
    dsimp [a,α]
    field_simp [Real.pi_ne_zero]
  · intro n m r hrm
    have hrm' : r.1 ≠ m.1 := fun h => hrm (Subtype.ext h)
    rw [matrix_coordinate n m r φ hφW]
    have hcol : p3NumeratorColumn38 n r.1 (p2Extend38 n (p2Restrict38 n s)) =
        p3NumeratorColumn38 n r.1 s := funext (column_extend_restrict n r.1 s)
    rw [hcol]
    exact offDiagonal_period_bound φ hφW C R c N hgeom hfam s n m.1 r.1
      m.2.symm r.2 hrm' (hσ n) (hσ r.1) H hH (fun z hz => (hb m.1 z hz).2)

end
end NlsGge.GK38.P3JacobianColumns
