                                                                                                                                                               
-- removed (see dedup log); #check/#print lines stripped; no proof text changed.
import Mathlib
import NlsGge.Atomic.G1.G1004
import NlsGge.Atomic.G1.G1008
import NlsGge.Atomic.G1.G1015
import NlsGge.Atomic.Volterra
import NlsGge.GK38.PairPotential
import NlsGge.GK38.PairVolterra
import NlsGge.GK38.PairVolterraDefs
import NlsGge.Atomic.G1.G1020

                                                                                                                   
                                                                                                                        
                                                                                                                      
                                                                                                                                       
                                                                                                           

set_option autoImplicit false

                                                                             


                                                                                
                                                                           
                                                                                                                                        
                                                                                                                                              
                                                                                                                                         
                             
                                                                               

namespace NlsGge.Atomic.G1029S3

open Filter Topology Set NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Pilot

noncomputable section

open scoped Matrix.Norms.L2Operator in
/-- The trace as a continuous linear functional. -/
def trL : Matrix (Fin 2) (Fin 2) ℂ →L[ℂ] ℂ :=
  { toLinearMap := Matrix.traceLinearMap (Fin 2) ℂ ℂ
    cont := LinearMap.continuous_of_finiteDimensional _ }

theorem trL_apply (X : Matrix (Fin 2) (Fin 2) ℂ) : trL X = Matrix.trace X := rfl

open scoped Matrix.Norms.L2Operator in
/-- `X ↦ X 0 1 + X 1 0` as a continuous linear functional. -/
def offL : Matrix (Fin 2) (Fin 2) ℂ →L[ℂ] ℂ :=
  { toLinearMap := Matrix.entryLinearMap ℂ ℂ 0 1 + Matrix.entryLinearMap ℂ ℂ 1 0
    cont := LinearMap.continuous_of_finiteDimensional _ }

theorem offL_apply (X : Matrix (Fin 2) (Fin 2) ℂ) : offL X = X 0 1 + X 1 0 := rfl

theorem bridge (φ : PotPair) (z : ℂ) :
    (∑' m : ℕ, potentialVolterraTerm38 φ z m 1) = monodromyPair φ z :=
  NlsGge.Atomic.G1004GenT.tsum_terms_eq_fundContT φ z zero_le_one ⟨zero_le_one, le_rfl⟩

open scoped Matrix.Norms.L2Operator in
theorem entry_le_l2 (A : Matrix (Fin 2) (Fin 2) ℂ) (i k : Fin 2) : ‖A i k‖ ≤ ‖A‖ := by
  have h := Matrix.l2_opNorm_mulVec A (EuclideanSpace.single k (1:ℂ))
  have h1 : ‖(EuclideanSpace.single k (1:ℂ))‖ = 1 := by simp
  rw [h1, mul_one] at h
  refine le_trans ?_ h
  have h2 := PiLp.norm_apply_le
    ((EuclideanSpace.equiv (Fin 2) ℂ).symm (A.mulVec (EuclideanSpace.single k (1:ℂ)))) i
  simpa [Matrix.mulVec, dotProduct, EuclideanSpace.single_apply] using h2

open scoped Matrix.Norms.L2Operator in
theorem entry_facts (M E : Matrix (Fin 2) (Fin 2) ℂ) (h01 : E 0 1 = 0) (h10 : E 1 0 = 0)
    (e : ℝ) (h00 : ‖E 0 0‖ ≤ e) (h11 : ‖E 1 1‖ ≤ e) :
    ‖M 0 1‖ ≤ ‖M - E‖ ∧ ‖M 1 0‖ ≤ ‖M - E‖ ∧ ‖M 0 0‖ ≤ e + ‖M - E‖ ∧ ‖M 1 1‖ ≤ e + ‖M - E‖ := by
  have k : ∀ i j, ‖(M - E) i j‖ ≤ ‖M - E‖ := fun i j => entry_le_l2 _ i j
  have s : ∀ i j, M i j = E i j + (M - E) i j := fun i j => by simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := k 0 1
    simpa [Matrix.sub_apply, h01] using this
  · have := k 1 0
    simpa [Matrix.sub_apply, h10] using this
  · calc ‖M 0 0‖ = ‖E 0 0 + (M - E) 0 0‖ := by rw [← s]
      _ ≤ ‖E 0 0‖ + ‖(M - E) 0 0‖ := norm_add_le _ _
      _ ≤ e + ‖M - E‖ := add_le_add h00 (k 0 0)
  · calc ‖M 1 1‖ = ‖E 1 1 + (M - E) 1 1‖ := by rw [← s]
      _ ≤ ‖E 1 1‖ + ‖(M - E) 1 1‖ := norm_add_le _ _
      _ ≤ e + ‖M - E‖ := add_le_add h11 (k 1 1)

theorem freeE_facts (z : ℂ) (R : ℝ) (hz : |z.im| ≤ R) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    freeZsFundamentalComplex z t 0 1 = 0 ∧ freeZsFundamentalComplex z t 1 0 = 0 ∧
    ‖freeZsFundamentalComplex z t 0 0‖ ≤ Real.exp R ∧ ‖freeZsFundamentalComplex z t 1 1‖ ≤ Real.exp R ∧
    freeZsFundamentalComplex z t 0 0 = Complex.exp (-(Complex.I * z * (t : ℂ))) ∧
    freeZsFundamentalComplex z t 1 1 = Complex.exp (Complex.I * z * (t : ℂ)) := by
  rw [freeZsFundamentalComplex_entries]
  have h1 : (-(Complex.I * z * (t : ℂ))).re = t * z.im := by
    simp [Complex.mul_re]; ring
  have h2 : (Complex.I * z * (t : ℂ)).re = -(t * z.im) := by
    simp [Complex.mul_re]; ring
  have hb : |t * z.im| ≤ R := by
    rw [abs_mul, abs_of_nonneg ht0]
    calc t * |z.im| ≤ 1 * |z.im| := mul_le_mul_of_nonneg_right ht1 (abs_nonneg _)
      _ ≤ R := by linarith
  refine ⟨by simp, by simp, ?_, ?_, by simp, by simp⟩
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Complex.norm_exp, h1]
    exact Real.exp_le_exp.2 (le_trans (le_abs_self _) hb)
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Complex.norm_exp, h2]
    exact Real.exp_le_exp.2 (le_trans (neg_le_abs _) hb)

end

end NlsGge.Atomic.G1029S3

namespace NlsGge.Atomic.G1029S3

open Filter Topology Set NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Pilot

noncomputable section

theorem n3 (x y z : ℂ) (a b c : ℝ) (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ b) (hz : ‖z‖ ≤ c) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖x * (y * z)‖ ≤ a * (b * c) := by
  rw [norm_mul, norm_mul]
  exact mul_le_mul hx (mul_le_mul hy hz (norm_nonneg _) hb) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ha

theorem bGD (a b c d m1 m2 m3 m4 : ℂ) (B ε ee : ℝ) (hB : 0 ≤ B) (hε : 0 ≤ ε) (he : 0 ≤ ee)
    (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ B) (hd : ‖d‖ ≤ B) (hm1 : ‖m1‖ ≤ B) (hm4 : ‖m4‖ ≤ B)
    (hbε : ‖b‖ ≤ ε) (hcε : ‖c‖ ≤ ε) (hm2 : ‖m2‖ ≤ ee) (hm3 : ‖m3‖ ≤ ee) :
    ‖m2 * (c * c) + (m4 - m1) * (c * d) - m3 * (d * d)‖ ≤ 2 * B ^ 2 * (ee + ε) ∧
    ‖m2 * (a * a) + (m4 - m1) * (a * b) - m3 * (b * b)‖ ≤ 2 * B ^ 2 * (ee + ε) := by
  have hdiff : ‖m4 - m1‖ ≤ 2 * B := by
    refine (norm_sub_le _ _).trans ?_; linarith
  constructor
  · have t1 := n3 m2 c c ee B B hm2 hc hc he hB
    have t2 := n3 (m4 - m1) c d (2 * B) ε B hdiff hcε hd (by linarith) hε
    have t3 := n3 m3 d d ee B B hm3 hd hd he hB
    calc ‖m2 * (c * c) + (m4 - m1) * (c * d) - m3 * (d * d)‖
        ≤ ‖m2 * (c * c)‖ + ‖(m4 - m1) * (c * d)‖ + ‖m3 * (d * d)‖ :=
          (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ ee * (B * B) + 2 * B * (ε * B) + ee * (B * B) := by gcongr
      _ = 2 * B ^ 2 * (ee + ε) := by ring
  · have t1 := n3 m2 a a ee B B hm2 ha ha he hB
    have t2 := n3 (m4 - m1) a b (2 * B) B ε hdiff ha hbε (by linarith) hB
    have t3 := n3 m3 b b ee B B hm3 hb hb he hB
    calc ‖m2 * (a * a) + (m4 - m1) * (a * b) - m3 * (b * b)‖
        ≤ ‖m2 * (a * a)‖ + ‖(m4 - m1) * (a * b)‖ + ‖m3 * (b * b)‖ :=
          (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ ee * (B * B) + 2 * B * (B * ε) + ee * (B * B) := by gcongr
      _ = 2 * B ^ 2 * (ee + ε) := by ring


theorem bLead0 (c d m1 m2 m3 m4 e1 e2 : ℂ) (B ε ee E : ℝ) (hB : 0 ≤ B) (hε : 0 ≤ ε) (he : 0 ≤ ee) (hE : 0 ≤ E)
    (hc : ‖c‖ ≤ B) (hd : ‖d‖ ≤ B) (hm4 : ‖m4‖ ≤ B) (hcε : ‖c‖ ≤ ε) (hm2 : ‖m2‖ ≤ ee) (hm3 : ‖m3‖ ≤ ee)
    (h1 : ‖m1 - e1‖ ≤ ee) (h2 : ‖d - e2‖ ≤ ε) (he1 : ‖e1‖ ≤ E) (he2 : ‖e2‖ ≤ E) :
    ‖(m4 * (c * c) + (m2 - m3) * (c * d) - m1 * (d * d)) - (-(e1 * (e2 * e2)))‖ ≤
      (3 * B ^ 2 + E * (B + E)) * (ee + ε) := by
  have hdiff : ‖m2 - m3‖ ≤ 2 * ee := by refine (norm_sub_le _ _).trans ?_; linarith
  have t1 := n3 m4 c c B ε B hm4 hcε hc hB hε
  have t2 := n3 (m2 - m3) c d (2 * ee) B B hdiff hc hd (by linarith) hB
  have t3 := n3 (m1 - e1) d d ee B B h1 hd hd he hB
  have hdd : ‖e2 + d‖ ≤ E + B := (norm_add_le _ _).trans (by linarith)
  have t4 : ‖e1 * ((d - e2) * (d + e2))‖ ≤ E * (ε * (B + E)) := by
    refine n3 e1 (d - e2) (d + e2) E ε (B + E) he1 h2 ?_ hE hε
    refine (norm_add_le _ _).trans ?_; linarith
  have hid : (m4 * (c * c) + (m2 - m3) * (c * d) - m1 * (d * d)) - (-(e1 * (e2 * e2))) =
      m4 * (c * c) + (m2 - m3) * (c * d) - (m1 - e1) * (d * d) - e1 * ((d - e2) * (d + e2)) := by ring
  rw [hid]
  calc ‖m4 * (c * c) + (m2 - m3) * (c * d) - (m1 - e1) * (d * d) - e1 * ((d - e2) * (d + e2))‖
      ≤ ‖m4 * (c * c)‖ + ‖(m2 - m3) * (c * d)‖ + ‖(m1 - e1) * (d * d)‖ + ‖e1 * ((d - e2) * (d + e2))‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ B * (ε * B) + 2 * ee * (B * B) + ee * (B * B) + E * (ε * (B + E)) := by gcongr
    _ ≤ (3 * B ^ 2 + E * (B + E)) * (ee + ε) := by nlinarith [mul_nonneg hB hB, mul_nonneg hE hB, mul_nonneg hE hE, mul_nonneg (mul_nonneg hB hB) hε, mul_nonneg (mul_nonneg hB hB) he, mul_nonneg hE (mul_nonneg hε hB), mul_nonneg hE (mul_nonneg hε hE), mul_nonneg hE (mul_nonneg he hB), mul_nonneg hE (mul_nonneg he hE)]

theorem bLead1 (a b m1 m2 m3 m4 e3 e4 : ℂ) (B ε ee E : ℝ) (hB : 0 ≤ B) (hε : 0 ≤ ε) (he : 0 ≤ ee) (hE : 0 ≤ E)
    (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) (hm1 : ‖m1‖ ≤ B) (hbε : ‖b‖ ≤ ε) (hm2 : ‖m2‖ ≤ ee) (hm3 : ‖m3‖ ≤ ee)
    (h4 : ‖m4 - e4‖ ≤ ee) (h3 : ‖a - e3‖ ≤ ε) (he3 : ‖e3‖ ≤ E) (he4 : ‖e4‖ ≤ E) :
    ‖(m4 * (a * a) + (m2 - m3) * (a * b) - m1 * (b * b)) - (e4 * (e3 * e3))‖ ≤
      (3 * B ^ 2 + E * (B + E)) * (ee + ε) := by
  have hdiff : ‖m2 - m3‖ ≤ 2 * ee := by refine (norm_sub_le _ _).trans ?_; linarith
  have t1 := n3 (m4 - e4) a a ee B B h4 ha ha he hB
  have t2 := n3 (m2 - m3) a b (2 * ee) B B hdiff ha hb (by linarith) hB
  have t3 := n3 m1 b b B ε B hm1 hbε hb hB hε
  have t4 : ‖e4 * ((a - e3) * (a + e3))‖ ≤ E * (ε * (B + E)) := by
    refine n3 e4 (a - e3) (a + e3) E ε (B + E) he4 h3 ?_ hE hε
    refine (norm_add_le _ _).trans ?_; linarith
  have hid : (m4 * (a * a) + (m2 - m3) * (a * b) - m1 * (b * b)) - (e4 * (e3 * e3)) =
      (m4 - e4) * (a * a) + (m2 - m3) * (a * b) - m1 * (b * b) + e4 * ((a - e3) * (a + e3)) := by ring
  rw [hid]
  calc ‖(m4 - e4) * (a * a) + (m2 - m3) * (a * b) - m1 * (b * b) + e4 * ((a - e3) * (a + e3))‖
      ≤ ‖(m4 - e4) * (a * a)‖ + ‖(m2 - m3) * (a * b)‖ + ‖m1 * (b * b)‖ + ‖e4 * ((a - e3) * (a + e3))‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ ee * (B * B) + 2 * ee * (B * B) + B * (ε * B) + E * (ε * (B + E)) := by gcongr
    _ ≤ (3 * B ^ 2 + E * (B + E)) * (ee + ε) := by nlinarith [mul_nonneg hB hB, mul_nonneg hE hB, mul_nonneg hE hE, mul_nonneg (mul_nonneg hB hB) hε, mul_nonneg (mul_nonneg hB hB) he, mul_nonneg hE (mul_nonneg hε hB), mul_nonneg hE (mul_nonneg hε hE), mul_nonneg hE (mul_nonneg he hB), mul_nonneg hE (mul_nonneg he hE)]

end

end NlsGge.Atomic.G1029S3


namespace NlsGge.Atomic.G1029S3

open Filter Topology Set NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Pilot

noncomputable section

theorem sumsq_dom (x : ℤ → ℂ) (K : ℝ) (u v : ℤ → ℝ) (C1 C2 : ℝ) (hK : 0 ≤ K)
    (hu : Summable (fun n => u n ^ 2)) (hv : Summable (fun n => v n ^ 2))
    (hu1 : ∑' n, u n ^ 2 ≤ C1) (hv1 : ∑' n, v n ^ 2 ≤ C2)
    (hu0 : ∀ n, 0 ≤ u n) (hv0 : ∀ n, 0 ≤ v n)
    (hx : ∀ n, ‖x n‖ ≤ K * (u n + v n)) :
    Summable (fun n => ‖x n‖ ^ 2) ∧ ∑' n, ‖x n‖ ^ 2 ≤ 2 * K ^ 2 * (C1 + C2) := by
  have hpt : ∀ n, ‖x n‖ ^ 2 ≤ 2 * K ^ 2 * (u n ^ 2 + v n ^ 2) := by
    intro n
    have h0 : 0 ≤ ‖x n‖ := norm_nonneg _
    have h1 : ‖x n‖ ^ 2 ≤ (K * (u n + v n)) ^ 2 := pow_le_pow_left₀ h0 (hx n) 2
    nlinarith [sq_nonneg (u n - v n), sq_nonneg K, mul_nonneg (sq_nonneg K) (sq_nonneg (u n - v n))]
  have hs : Summable (fun n => 2 * K ^ 2 * (u n ^ 2 + v n ^ 2)) := (hu.add hv).mul_left _
  refine ⟨Summable.of_nonneg_of_le (fun n => sq_nonneg _) hpt hs, ?_⟩
  calc ∑' n, ‖x n‖ ^ 2 ≤ ∑' n, 2 * K ^ 2 * (u n ^ 2 + v n ^ 2) :=
        (Summable.of_nonneg_of_le (fun n => sq_nonneg _) hpt hs).tsum_le_tsum hpt hs
    _ = 2 * K ^ 2 * (∑' n, u n ^ 2 + ∑' n, v n ^ 2) := by
        rw [tsum_mul_left, hu.tsum_add hv]
    _ ≤ 2 * K ^ 2 * (C1 + C2) := by gcongr


theorem sumsq_dom' (x : ℤ → ℂ) (K : ℝ) (u v : ℤ → ℝ) (C1 C2 C : ℝ) (hK : 0 ≤ K)
    (hu : Summable (fun n => u n ^ 2)) (hv : Summable (fun n => v n ^ 2))
    (hu1 : ∑' n, u n ^ 2 ≤ C1) (hv1 : ∑' n, v n ^ 2 ≤ C2)
    (hu0 : ∀ n, 0 ≤ u n) (hv0 : ∀ n, 0 ≤ v n) (hC : 2 * K ^ 2 * (C1 + C2) ≤ C)
    (hx : ∀ n, ‖x n‖ ≤ K * (u n + v n)) :
    Summable (fun n => ‖x n‖ ^ 2) ∧ ∑' n, ‖x n‖ ^ 2 ≤ C := by
  obtain ⟨h1, h2⟩ := sumsq_dom x K u v C1 C2 hK hu hv hu1 hv1 hu0 hv0 hx
  exact ⟨h1, h2.trans hC⟩

open scoped Matrix.Norms.L2Operator in
theorem fact_n (M : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) (R t C ε : ℝ) (hz : |z.im| ≤ R) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hε : ε = ‖M - freeZsFundamentalComplex z t‖) (hC : ε ^ 2 ≤ C) :
    ‖M 0 1‖ ≤ ε ∧ ‖M 1 0‖ ≤ ε ∧ ‖M 0 0‖ ≤ Real.exp R + 1 + C ∧ ‖M 1 1‖ ≤ Real.exp R + 1 + C ∧
    ‖M 0 1‖ ≤ Real.exp R + 1 + C ∧ ‖M 1 0‖ ≤ Real.exp R + 1 + C ∧
    ‖M 0 0 - Complex.exp (-(Complex.I * z * (t : ℂ)))‖ ≤ ε ∧
    ‖M 1 1 - Complex.exp (Complex.I * z * (t : ℂ))‖ ≤ ε ∧
    ‖Complex.exp (-(Complex.I * z * (t : ℂ)))‖ ≤ Real.exp R ∧ ‖Complex.exp (Complex.I * z * (t : ℂ))‖ ≤ Real.exp R := by
  obtain ⟨f01, f10, f00, f11, e00, e11⟩ := freeE_facts z R hz t ht0 ht1
  obtain ⟨a1, a2, a3, a4⟩ := entry_facts M _ f01 f10 (Real.exp R) f00 f11
  rw [← hε] at a1 a2 a3 a4
  have hε1 : ε ≤ 1 + C := by nlinarith [sq_nonneg (ε - 1), norm_nonneg (M - freeZsFundamentalComplex z t), hε ▸ norm_nonneg (M - freeZsFundamentalComplex z t)]
  have hE0 : 0 ≤ Real.exp R := (Real.exp_pos _).le
  have k : ∀ i j, ‖(M - freeZsFundamentalComplex z t) i j‖ ≤ ε := fun i j => hε ▸ entry_le_l2 _ i j
  refine ⟨a1, a2, by linarith, by linarith, by linarith, by linarith, ?_, ?_, ?_, ?_⟩
  · have := k 0 0
    simpa [Matrix.sub_apply, e00] using this
  · have := k 1 1
    simpa [Matrix.sub_apply, e11] using this
  · rw [← e00]; exact f00
  · rw [← e11]; exact f11

open scoped Matrix.Norms.L2Operator in
theorem G1029_main :
((
  ∀ R0 R1 : ℝ, ∃ C : ℝ, ∀ (φ : PotPair) (ξ : ℤ → ℂ),
    Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2) ≤ R0 →
    (∀ n : ℤ, ‖ξ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ R1) →
    let Dl : ℂ → ℂ := fun w => Matrix.trace (monodromyPair φ w)
    let dl : ℂ → ℂ := fun w => monodromyPair φ w 0 1 + monodromyPair φ w 1 0
    (∀ n : ℤ, DifferentiableAt ℂ Dl (ξ n) ∧ DifferentiableAt ℂ dl (ξ n)) ∧
    (Summable (fun n : ℤ => ‖deriv Dl (ξ n) - (-2 * Complex.sin (ξ n))‖ ^ 2) ∧
      (∑' n : ℤ, ‖deriv Dl (ξ n) - (-2 * Complex.sin (ξ n))‖ ^ 2) ≤ C) ∧
    (Summable (fun n : ℤ => ‖deriv dl (ξ n)‖ ^ 2) ∧
      (∑' n : ℤ, ‖deriv dl (ξ n)‖ ^ 2) ≤ C) ∧
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ k : Fin 2,
      let Mf : ℤ → ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun n u => ∑' m : ℕ, potentialVolterraTerm38 φ (ξ n) m u
      let Ml : ℤ → Matrix (Fin 2) (Fin 2) ℂ := fun n => monodromyPair φ (ξ n)
      let mc1 : ℤ → Fin 2 → ℂ := fun n => ![Mf n t 0 0, Mf n t 1 0]
      let mc2 : ℤ → Fin 2 → ℂ := fun n => ![Mf n t 0 1, Mf n t 1 1]
      let star : (Fin 2 → ℂ) → (Fin 2 → ℂ) → (Fin 2 → ℂ) := fun g k => ![g 1 * k 1, g 0 * k 0]
      let GD : ℤ → ℂ := fun n =>
        Ml n 0 1 * star (mc1 n) (mc1 n) k + (Ml n 1 1 - Ml n 0 0) * star (mc1 n) (mc2 n) k
          - Ml n 1 0 * star (mc2 n) (mc2 n) k
      let Gd : ℤ → ℂ := fun n =>
        Ml n 1 1 * star (mc1 n) (mc1 n) k + (Ml n 0 1 - Ml n 1 0) * star (mc1 n) (mc2 n) k
          - Ml n 0 0 * star (mc2 n) (mc2 n) k
      let lead : ℤ → ℂ := fun n =>
        (![-Complex.exp (-(Complex.I * ξ n * (1 - 2 * (t : ℂ)))),
           Complex.exp (Complex.I * ξ n * (1 - 2 * (t : ℂ)))] : Fin 2 → ℂ) k
      (Summable (fun n : ℤ => ‖GD n‖ ^ 2) ∧ (∑' n : ℤ, ‖GD n‖ ^ 2) ≤ C) ∧
      (Summable (fun n : ℤ => ‖Gd n - lead n‖ ^ 2) ∧ (∑' n : ℤ, ‖Gd n - lead n‖ ^ 2) ≤ C))
  : Prop)) := by
  intro R0 R1
  obtain ⟨C19, h19⟩ := NlsGge.Atomic.G1020S1.K19.G1019_whole R0 R1
  obtain ⟨C20, h20⟩ := NlsGge.Atomic.G1020S1.G1020_whole R0 R1
  set R1' : ℝ := max R1 0 with hR1'
  set E : ℝ := Real.exp R1' with hE
  set C19' : ℝ := max C19 0 with hC19'
  set C20' : ℝ := max C20 0 with hC20'
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hC19'0 : 0 ≤ C19' := le_max_right _ _
  have hC20'0 : 0 ≤ C20' := le_max_right _ _
  have hC19le : C19 ≤ C19' := le_max_left _ _
  have hC20le : C20 ≤ C20' := le_max_left _ _
  set B : ℝ := E + 1 + C19' with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; linarith
  set K1 : ℝ := 2 * B ^ 2 with hK1
  set K2 : ℝ := 3 * B ^ 2 + E * (B + E) with hK2
  have hK10 : 0 ≤ K1 := by rw [hK1]; positivity
  have hK20 : 0 ≤ K2 := by rw [hK2]; positivity
  set TD : ℝ := 2 * 2 ^ 2 * (C20' + 0) with hTD
  set TG : ℝ := 2 * K1 ^ 2 * (C19' + C19') with hTG
  set TL : ℝ := 2 * K2 ^ 2 * (C19' + C19') with hTL
  have hTD0 : 0 ≤ TD := by rw [hTD]; positivity
  have hTG0 : 0 ≤ TG := by rw [hTG]; positivity
  have hTL0 : 0 ≤ TL := by rw [hTL]; positivity
  refine ⟨TD + TD + TG + TL, ?_⟩
  intro φ ξ hφ hξ Dl dl
  have hξim : ∀ n : ℤ, |(ξ n).im| ≤ R1' := by
    intro n
    have h1 : (ξ n - (n : ℂ) * (Real.pi : ℂ)).im = (ξ n).im := by simp
    have h2 := Complex.abs_im_le_norm (ξ n - (n : ℂ) * (Real.pi : ℂ))
    rw [h1] at h2
    exact h2.trans ((hξ n).trans (le_max_left _ _))
  obtain ⟨hDiff, hS20, hT20⟩ := h20 φ ξ hφ hξ 1 zero_le_one le_rfl
  have hone := h19 φ ξ hφ hξ 1 zero_le_one le_rfl
  -- the maps and their derivatives
  let M1 : ℂ → Matrix (Fin 2) (Fin 2) ℂ := fun w => ∑' m : ℕ, potentialVolterraTerm38 φ w m 1
  let Ed : ℂ → Matrix (Fin 2) (Fin 2) ℂ := fun w => freeZsFundamentalComplex w 1
  let A : ℤ → Matrix (Fin 2) (Fin 2) ℂ := fun n => deriv M1 (ξ n) - deriv Ed (ξ n)
  have hDiff' : ∀ n : ℤ, DifferentiableAt ℂ M1 (ξ n) := hDiff
  have hEd : ∀ n : ℤ, HasDerivAt Ed (deriv Ed (ξ n)) (ξ n) := fun n =>
    (NlsGge.Atomic.G1020S1.differentiable_E 1 (ξ n)).hasDerivAt
  have hAs : Summable (fun n : ℤ => ‖A n‖ ^ 2) := hS20
  have hAt : ∑' n : ℤ, ‖A n‖ ^ 2 ≤ C20 := hT20
  have e1 : (fun w : ℂ => Matrix.trace (monodromyPair φ w)) = fun w => trL (M1 w) :=
    funext fun w => by
      show _ = trL (∑' m : ℕ, potentialVolterraTerm38 φ w m 1)
      rw [bridge, trL_apply]
  have e2 : (fun w : ℂ => monodromyPair φ w 0 1 + monodromyPair φ w 1 0) = fun w => offL (M1 w) :=
    funext fun w => by
      show _ = offL (∑' m : ℕ, potentialVolterraTerm38 φ w m 1)
      rw [bridge, offL_apply]
  have hdT : ∀ n : ℤ, deriv (fun w : ℂ => Matrix.trace (monodromyPair φ w)) (ξ n) =
      trL (deriv M1 (ξ n)) := fun n => by
    rw [e1]
    exact (trL.hasFDerivAt.comp_hasDerivAt (ξ n) (hDiff' n).hasDerivAt).deriv
  have hdO : ∀ n : ℤ, deriv (fun w : ℂ => monodromyPair φ w 0 1 + monodromyPair φ w 1 0) (ξ n) =
      offL (deriv M1 (ξ n)) := fun n => by
    rw [e2]
    exact (offL.hasFDerivAt.comp_hasDerivAt (ξ n) (hDiff' n).hasDerivAt).deriv
  have hTE : ∀ n : ℤ, trL (deriv Ed (ξ n)) = -2 * Complex.sin (ξ n) := by
    intro n
    have hT := trL.hasFDerivAt.comp_hasDerivAt (ξ n) (hEd n)
    have hf : (⇑trL ∘ Ed) = fun w : ℂ => 2 * Complex.cos w := by
      funext w
      show trL (freeZsFundamentalComplex w 1) = 2 * Complex.cos w
      rw [trL_apply, Matrix.trace_fin_two, freeZsFundamentalComplex_entries, Complex.two_cos]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Complex.ofReal_one, mul_one]
      rw [add_comm]; congr 2 <;> ring
    rw [hf] at hT
    have hC : HasDerivAt (fun w : ℂ => 2 * Complex.cos w) (-2 * Complex.sin (ξ n)) (ξ n) := by
      have := (Complex.hasDerivAt_cos (ξ n)).const_mul 2
      convert this using 1; ring
    exact hT.unique hC
  have hOE : ∀ n : ℤ, offL (deriv Ed (ξ n)) = 0 := by
    intro n
    have hT := offL.hasFDerivAt.comp_hasDerivAt (ξ n) (hEd n)
    have hf : (⇑offL ∘ Ed) = fun _ : ℂ => (0 : ℂ) := by
      funext w
      show offL (freeZsFundamentalComplex w 1) = 0
      rw [offL_apply, freeZsFundamentalComplex_entries]
      simp
    rw [hf] at hT
    exact hT.unique (hasDerivAt_const _ _)
  have hnT : ∀ n : ℤ, ‖trL (A n)‖ ≤ 2 * ‖A n‖ := by
    intro n
    rw [trL_apply, Matrix.trace_fin_two]
    have := entry_le_l2 (A n) 0 0
    have := entry_le_l2 (A n) 1 1
    calc ‖A n 0 0 + A n 1 1‖ ≤ ‖A n 0 0‖ + ‖A n 1 1‖ := norm_add_le _ _
      _ ≤ 2 * ‖A n‖ := by linarith
  have hnO : ∀ n : ℤ, ‖offL (A n)‖ ≤ 2 * ‖A n‖ := by
    intro n
    rw [offL_apply]
    have := entry_le_l2 (A n) 0 1
    have := entry_le_l2 (A n) 1 0
    calc ‖A n 0 1 + A n 1 0‖ ≤ ‖A n 0 1‖ + ‖A n 1 0‖ := norm_add_le _ _
      _ ≤ 2 * ‖A n‖ := by linarith
  have hzs : Summable (fun _ : ℤ => ((0 : ℝ)) ^ 2) := by simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    refine ⟨?_, ?_⟩
    · show DifferentiableAt ℂ (fun w : ℂ => Matrix.trace (monodromyPair φ w)) (ξ n)
      rw [e1]; exact trL.differentiableAt.comp (ξ n) (hDiff' n)
    · show DifferentiableAt ℂ (fun w : ℂ => monodromyPair φ w 0 1 + monodromyPair φ w 1 0) (ξ n)
      rw [e2]; exact offL.differentiableAt.comp (ξ n) (hDiff' n)
  · have hx : ∀ n : ℤ, deriv (fun w : ℂ => Matrix.trace (monodromyPair φ w)) (ξ n) - (-2 * Complex.sin (ξ n)) =
        trL (A n) := fun n => by
      rw [hdT, ← hTE n, ← map_sub]
    have key := sumsq_dom (fun n => trL (A n)) 2 (fun n => ‖A n‖) (fun _ => 0) C20 0 (by norm_num) hAs hzs hAt
      (by simp) (fun n => norm_nonneg _) (fun _ => le_rfl) (fun n => by simpa using hnT n)
    show Summable (fun n : ℤ => ‖deriv (fun w : ℂ => Matrix.trace (monodromyPair φ w)) (ξ n) -
      (-2 * Complex.sin (ξ n))‖ ^ 2) ∧ (∑' n : ℤ, ‖deriv (fun w : ℂ => Matrix.trace (monodromyPair φ w)) (ξ n) -
      (-2 * Complex.sin (ξ n))‖ ^ 2) ≤ TD + TD + TG + TL
    simp only [hx]
    refine ⟨key.1, key.2.trans ?_⟩
    have : 2 * 2 ^ 2 * (C20 + 0) ≤ TD := by rw [hTD]; nlinarith
    linarith
  · have hx : ∀ n : ℤ, deriv (fun w : ℂ => monodromyPair φ w 0 1 + monodromyPair φ w 1 0) (ξ n) =
        offL (A n) := fun n => by
      rw [hdO, show A n = deriv M1 (ξ n) - deriv Ed (ξ n) from rfl, map_sub, hOE, sub_zero]
    have key := sumsq_dom (fun n => offL (A n)) 2 (fun n => ‖A n‖) (fun _ => 0) C20 0 (by norm_num) hAs hzs hAt
      (by simp) (fun n => norm_nonneg _) (fun _ => le_rfl) (fun n => by simpa using hnO n)
    show Summable (fun n : ℤ => ‖deriv (fun w : ℂ => monodromyPair φ w 0 1 + monodromyPair φ w 1 0) (ξ n)‖ ^ 2) ∧
      (∑' n : ℤ, ‖deriv (fun w : ℂ => monodromyPair φ w 0 1 + monodromyPair φ w 1 0) (ξ n)‖ ^ 2) ≤ TD + TD + TG + TL
    simp only [hx]
    refine ⟨key.1, key.2.trans ?_⟩
    have : 2 * 2 ^ 2 * (C20 + 0) ≤ TD := by rw [hTD]; nlinarith
    linarith
  · intro t ht0 ht1 k
    obtain ⟨ε, hεd, hεs, hεsum⟩ : ∃ ε : ℤ → ℝ,
        (∀ n, ε n = ‖(∑' m : ℕ, potentialVolterraTerm38 φ (ξ n) m t) - freeZsFundamentalComplex (ξ n) t‖) ∧
        Summable (fun n => ε n ^ 2) ∧ ∑' n, ε n ^ 2 ≤ C19 := by
      obtain ⟨hs, hb⟩ := h19 φ ξ hφ hξ t ht0 ht1
      exact ⟨_, fun _ => rfl, hs, hb⟩
    obtain ⟨ee, hed, hes, heesum⟩ : ∃ ee : ℤ → ℝ,
        (∀ n, ee n = ‖(∑' m : ℕ, potentialVolterraTerm38 φ (ξ n) m 1) - freeZsFundamentalComplex (ξ n) 1‖) ∧
        Summable (fun n => ee n ^ 2) ∧ ∑' n, ee n ^ 2 ≤ C19 :=
      ⟨_, fun _ => rfl, hone.1, hone.2⟩
    have hε0 : ∀ n, 0 ≤ ε n := fun n => by rw [hεd n]; exact norm_nonneg _
    have hee0 : ∀ n, 0 ≤ ee n := fun n => by rw [hed n]; exact norm_nonneg _
    have hε2 : ∀ n, ε n ^ 2 ≤ C19' := fun n =>
      (hεs.le_tsum n (fun j _ => sq_nonneg _)).trans (hεsum.trans hC19le)
    have hee2 : ∀ n, ee n ^ 2 ≤ C19' := fun n =>
      (hes.le_tsum n (fun j _ => sq_nonneg _)).trans (heesum.trans hC19le)
    have Ft := fun n : ℤ => fact_n (∑' m : ℕ, potentialVolterraTerm38 φ (ξ n) m t) (ξ n) R1' t C19' (ε n)
      (hξim n) ht0 ht1 (hεd n) (hε2 n)
    have F1 := fun n : ℤ => fact_n (∑' m : ℕ, potentialVolterraTerm38 φ (ξ n) m 1) (ξ n) R1' 1 C19' (ee n)
      (hξim n) zero_le_one le_rfl (hed n) (hee2 n)
    have hle0 : ∀ n : ℤ, Complex.exp (-(Complex.I * ξ n * (((1 : ℝ)) : ℂ))) *
        (Complex.exp (Complex.I * ξ n * (t : ℂ)) * Complex.exp (Complex.I * ξ n * (t : ℂ))) =
        Complex.exp (-(Complex.I * ξ n * (1 - 2 * (t : ℂ)))) := fun n => by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
    have hle1 : ∀ n : ℤ, Complex.exp (Complex.I * ξ n * (((1 : ℝ)) : ℂ)) *
        (Complex.exp (-(Complex.I * ξ n * (t : ℂ))) * Complex.exp (-(Complex.I * ξ n * (t : ℂ)))) =
        Complex.exp (Complex.I * ξ n * (1 - 2 * (t : ℂ))) := fun n => by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
    have hsT : ∀ n : ℤ, TG ≤ TD + TD + TG + TL := fun n => by linarith
    fin_cases k
    · intro Mf' Ml mc1 mc2 star GD Gd lead
      simp only [GD, Gd, lead, star, mc1, mc2, Ml, Mf', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Fin.zero_eta]
      refine ⟨sumsq_dom' _ K1 ee ε C19 C19 _ hK10 hes hεs heesum hεsum hee0 hε0 ?_ (fun n => ?_),
        sumsq_dom' _ K2 ee ε C19 C19 _ hK20 hes hεs heesum hεsum hee0 hε0 ?_ (fun n => ?_)⟩
      · have h1 := mul_le_mul_of_nonneg_left (add_le_add hC19le hC19le) (by positivity : (0 : ℝ) ≤ 2 * K1 ^ 2)
        have : 2 * K1 ^ 2 * (C19' + C19') = TG := by rw [hTG]
        linarith
      · obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10⟩ := Ft n
        have F1n := F1 n
        simp only [bridge] at F1n
        obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩ := F1n
        have := (bGD _ _ _ _ _ _ _ _ B (ε n) (ee n) hB0 (hε0 n) (hee0 n) t3 t5 t6 t4 f3 f4 t1 t2 f1 f2).1
        exact this
      · have h1 := mul_le_mul_of_nonneg_left (add_le_add hC19le hC19le) (by positivity : (0 : ℝ) ≤ 2 * K2 ^ 2)
        have : 2 * K2 ^ 2 * (C19' + C19') = TL := by rw [hTL]
        linarith
      · obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10⟩ := Ft n
        have F1n := F1 n
        simp only [bridge] at F1n
        obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩ := F1n
        have := bLead0 _ _ _ _ _ _ _ _ B (ε n) (ee n) E hB0 (hε0 n) (hee0 n) hE0 t6 t4 f4 t2 f1 f2 f7 t8 f9 t10
        rw [hle0 n] at this
        exact this
    · intro Mf' Ml mc1 mc2 star GD Gd lead
      simp only [GD, Gd, lead, star, mc1, mc2, Ml, Mf', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Fin.mk_one]
      refine ⟨sumsq_dom' _ K1 ee ε C19 C19 _ hK10 hes hεs heesum hεsum hee0 hε0 ?_ (fun n => ?_),
        sumsq_dom' _ K2 ee ε C19 C19 _ hK20 hes hεs heesum hεsum hee0 hε0 ?_ (fun n => ?_)⟩
      · have h1 := mul_le_mul_of_nonneg_left (add_le_add hC19le hC19le) (by positivity : (0 : ℝ) ≤ 2 * K1 ^ 2)
        have : 2 * K1 ^ 2 * (C19' + C19') = TG := by rw [hTG]
        linarith
      · obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10⟩ := Ft n
        have F1n := F1 n
        simp only [bridge] at F1n
        obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩ := F1n
        have := (bGD _ _ _ _ _ _ _ _ B (ε n) (ee n) hB0 (hε0 n) (hee0 n) t3 t5 t6 t4 f3 f4 t1 t2 f1 f2).2
        exact this
      · have h1 := mul_le_mul_of_nonneg_left (add_le_add hC19le hC19le) (by positivity : (0 : ℝ) ≤ 2 * K2 ^ 2)
        have : 2 * K2 ^ 2 * (C19' + C19') = TL := by rw [hTL]
        linarith
      · obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10⟩ := Ft n
        have F1n := F1 n
        simp only [bridge] at F1n
        obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩ := F1n
        have := bLead1 _ _ _ _ _ _ _ _ B (ε n) (ee n) E hB0 (hε0 n) (hee0 n) hE0 t3 t5 f3 t1 f1 f2 f8 t7 t9 f10
        rw [hle1 n] at this
        exact this

end

end NlsGge.Atomic.G1029S3


