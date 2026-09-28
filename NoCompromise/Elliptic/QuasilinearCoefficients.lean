import NoCompromise.Elliptic.NondivSchauderDifference

/-! The actual averaged derivative matrix in the quasilinear difference equation.
Its increment identity is the fundamental theorem of calculus; its bounds are
inherited from the genuine first and second derivatives of the nonlinear flux. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The derivative of the flux averaged along the closed segment from p to q. -/
def quasilinearSecantCoefficient {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (p q : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ∫ t in Icc (0 : ℝ) 1, fderiv ℝ A (p + t • (q - p))

lemma quasilinearSecantCoefficient_integrable {n : ℕ}
    {A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hA : ContDiff ℝ 1 A) (p q : EuclideanSpace ℝ (Fin n)) :
    IntegrableOn (fun t : ℝ => fderiv ℝ A (p + t • (q - p))) (Icc 0 1) :=
  (((hA.continuous_fderiv one_ne_zero).comp
    (continuous_const.add (continuous_id.smul continuous_const))).continuousOn).integrableOn_compact
      isCompact_Icc

/-- The secant coefficient gives the exact nonlinear flux increment. -/
theorem quasilinearSecantCoefficient_apply_sub {n : ℕ}
    {A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hA : ContDiff ℝ 1 A) (p q : EuclideanSpace ℝ (Fin n)) :
    quasilinearSecantCoefficient A p q (q - p) = A q - A p := by
  rw [quasilinearSecantCoefficient,
    ContinuousLinearMap.integral_apply (quasilinearSecantCoefficient_integrable hA p q)]
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => A (p + s • (q - p)))
      (fderiv ℝ A (p + t • (q - p)) (q - p)) t := by
    have hp : HasDerivAt (fun s : ℝ => p + s • (q - p)) (q - p) t := by
      simpa only [one_smul, id_eq] using!
        ((hasDerivAt_id t).smul_const (q - p)).const_add p
    exact (hA.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t hp
  have hc : Continuous (fun t : ℝ => fderiv ℝ A (p + t • (q - p)) (q - p)) :=
    ((hA.continuous_fderiv one_ne_zero).comp
      (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
  have ht := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (hc.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc] at ht
  simpa only [one_smul, zero_smul, add_zero, show p + (q - p) = q by abel] using ht

lemma quasilinearSecantCoefficient_norm_le {n : ℕ}
    {A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {M cap : ℝ}
    (hb : ∀ p ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) M, ‖fderiv ℝ A p‖ ≤ cap)
    {p q : EuclideanSpace ℝ (Fin n)} (hp : p ∈ closedBall 0 M) (hq : q ∈ closedBall 0 M) :
    ‖quasilinearSecantCoefficient A p q‖ ≤ cap := by
  simpa only [quasilinearSecantCoefficient, Measure.real, Real.volume_Icc, sub_zero,
    ENNReal.ofReal_one, ENNReal.toReal_one, mul_one] using
    norm_setIntegral_le_of_norm_le_const (μ := volume) isCompact_Icc.measure_lt_top
      (fun t ht => hb _
        ((convex_closedBall (0 : EuclideanSpace ℝ (Fin n)) M).add_smul_sub_mem hp hq ht))

/-- A genuine second derivative bound makes the first derivative Lipschitz on
its closed convex gradient ball. -/
lemma quasilinear_fderiv_lipschitz_bound {n : ℕ}
    {A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hA : ContDiff ℝ 2 A) {M B : ℝ}
    (hb : ∀ p ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) M,
      ‖fderiv ℝ (fderiv ℝ A) p‖ ≤ B)
    {p q : EuclideanSpace ℝ (Fin n)} (hp : p ∈ closedBall 0 M) (hq : q ∈ closedBall 0 M) :
    ‖fderiv ℝ A p - fderiv ℝ A q‖ ≤ B * ‖p - q‖ := by
  have hd : ContDiff ℝ 1 (fderiv ℝ A) := hA.fderiv_right (by norm_num)
  have hc := convex_closedBall (0 : EuclideanSpace ℝ (Fin n)) M
  exact hc.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x _ => (hd.differentiable one_ne_zero x).hasFDerivAt.hasFDerivWithinAt) hb hq hp

/-- Uniform positive ellipticity survives averaging, without any symmetry
assumption on the derivative of the flux. -/
lemma quasilinearSecantCoefficient_elliptic {n : ℕ}
    {A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hA : ContDiff ℝ 1 A) {M lam : ℝ}
    (hell : ∀ p ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) M,
      ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (fderiv ℝ A p ξ) ξ)
    {p q : EuclideanSpace ℝ (Fin n)} (hp : p ∈ closedBall 0 M) (hq : q ∈ closedBall 0 M)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    lam * ‖ξ‖ ^ 2 ≤ inner ℝ (quasilinearSecantCoefficient A p q ξ) ξ := by
  have hi := quasilinearSecantCoefficient_integrable hA p q
  have hv : IntegrableOn (fun t : ℝ => fderiv ℝ A (p + t • (q - p)) ξ) (Icc 0 1) :=
    (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n)) ξ).integrable_comp hi
  have he : inner ℝ (quasilinearSecantCoefficient A p q ξ) ξ =
      ∫ t in Icc (0 : ℝ) 1, inner ℝ (fderiv ℝ A (p + t • (q - p)) ξ) ξ := by
    rw [quasilinearSecantCoefficient, ContinuousLinearMap.integral_apply hi]
    simpa only [real_inner_comm] using (integral_inner hv ξ).symm
  rw [he]
  have hh : (∫ _t in Icc (0 : ℝ) 1, lam * ‖ξ‖ ^ 2) ≤
      ∫ t in Icc (0 : ℝ) 1, inner ℝ (fderiv ℝ A (p + t • (q - p)) ξ) ξ := by
    apply setIntegral_mono_on (integrableOn_const (by simp))
      (hv.inner_const (𝕜 := ℝ) ξ) measurableSet_Icc
    intro t ht
    exact hell _ ((convex_closedBall (0 : EuclideanSpace ℝ (Fin n)) M).add_smul_sub_mem hp hq ht) ξ
  simpa only [integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Icc,
    sub_zero, ENNReal.ofReal_one, ENNReal.toReal_one, one_smul] using hh

/-- The averaged coefficient converges quantitatively to the derivative at
one endpoint as the two endpoints approach one another. -/
lemma quasilinearSecantCoefficient_sub_fderiv_le {n : ℕ}
    {A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hA : ContDiff ℝ 2 A) {M B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ p ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) M,
      ‖fderiv ℝ (fderiv ℝ A) p‖ ≤ B)
    {p q : EuclideanSpace ℝ (Fin n)} (hp : p ∈ closedBall 0 M) (hq : q ∈ closedBall 0 M) :
    ‖quasilinearSecantCoefficient A p q - fderiv ℝ A p‖ ≤ B * ‖q - p‖ := by
  have hic : (∫ _t in Icc (0 : ℝ) 1, fderiv ℝ A p) = fderiv ℝ A p := by simp
  rw [quasilinearSecantCoefficient, ← hic,
    ← integral_sub (quasilinearSecantCoefficient_integrable (hA.of_le (by norm_num)) p q)
      (integrableOn_const (by simp))]
  have hs (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖fderiv ℝ A (p + t • (q - p)) - fderiv ℝ A p‖ ≤ B * ‖q - p‖ := by
    apply (quasilinear_fderiv_lipschitz_bound hA hb
      ((convex_closedBall (0 : EuclideanSpace ℝ (Fin n)) M).add_smul_sub_mem hp hq ht) hp).trans
    apply mul_le_mul_of_nonneg_left _ hB
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact mul_le_of_le_one_left (norm_nonneg _) ht.2
  simpa only [Measure.real, Real.volume_Icc, sub_zero, ENNReal.ofReal_one,
    ENNReal.toReal_one, mul_one] using
    norm_setIntegral_le_of_norm_le_const (μ := volume) isCompact_Icc.measure_lt_top hs

lemma quasilinear_segment_sub_norm_le {n : ℕ} (p q p' q' : EuclideanSpace ℝ (Fin n))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖(p + t • (q - p)) - (p' + t • (q' - p'))‖ ≤ ‖p - p'‖ + ‖q - q'‖ := by
  have he : (p + t • (q - p)) - (p' + t • (q' - p')) =
      (1 - t) • (p - p') + t • (q - q') := by module
  rw [he]
  calc
    _ ≤ ‖(1 - t) • (p - p')‖ + ‖t • (q - q')‖ := norm_add_le _ _
    _ = (1 - t) * ‖p - p'‖ + t * ‖q - q'‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1,
        abs_of_nonneg (sub_nonneg.mpr ht.2)]
    _ ≤ ‖p - p'‖ + ‖q - q'‖ := by
      apply add_le_add
      · exact mul_le_of_le_one_left (norm_nonneg _) (by linarith only [ht.1])
      · exact mul_le_of_le_one_left (norm_nonneg _) ht.2

/-- Joint Lipschitz control of the two endpoints of the secant matrix. -/
lemma quasilinearSecantCoefficient_sub_le {n : ℕ}
    {A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hA : ContDiff ℝ 2 A) {M B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ p ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) M,
      ‖fderiv ℝ (fderiv ℝ A) p‖ ≤ B)
    {p q p' q' : EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ closedBall 0 M) (hq : q ∈ closedBall 0 M)
    (hp' : p' ∈ closedBall 0 M) (hq' : q' ∈ closedBall 0 M) :
    ‖quasilinearSecantCoefficient A p q - quasilinearSecantCoefficient A p' q'‖ ≤
      B * (‖p - p'‖ + ‖q - q'‖) := by
  rw [quasilinearSecantCoefficient, quasilinearSecantCoefficient,
    ← integral_sub (quasilinearSecantCoefficient_integrable (hA.of_le (by norm_num)) p q)
      (quasilinearSecantCoefficient_integrable (hA.of_le (by norm_num)) p' q')]
  have hs (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖fderiv ℝ A (p + t • (q - p)) - fderiv ℝ A (p' + t • (q' - p'))‖ ≤
        B * (‖p - p'‖ + ‖q - q'‖) := by
    apply (quasilinear_fderiv_lipschitz_bound hA hb
      ((convex_closedBall (0 : EuclideanSpace ℝ (Fin n)) M).add_smul_sub_mem hp hq ht)
      ((convex_closedBall (0 : EuclideanSpace ℝ (Fin n)) M).add_smul_sub_mem hp' hq' ht)).trans
    exact mul_le_mul_of_nonneg_left (quasilinear_segment_sub_norm_le p q p' q' ht) hB
  simpa only [Measure.real, Real.volume_Icc, sub_zero, ENNReal.ofReal_one,
    ENNReal.toReal_one, mul_one] using
    norm_setIntegral_le_of_norm_le_const (μ := volume) isCompact_Icc.measure_lt_top hs

/-- The averaged matrices have a Hölder constant independent of the displacement. -/
lemma quasilinearSecantCoefficient_holder {n : ℕ}
    {A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hA : ContDiff ℝ 2 A) {M B H a : ℝ} (hB : 0 ≤ B)
    (hb : ∀ p ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) M,
      ‖fderiv ℝ (fderiv ℝ A) p‖ ≤ B)
    {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {U V : Set (EuclideanSpace ℝ (Fin n))}
    (hF : ∀ x ∈ U, F x ∈ closedBall 0 M)
    (hH : ∀ x ∈ U, ∀ y ∈ U, ‖F x - F y‖ ≤ H * dist x y ^ a)
    (hVU : V ⊆ U) (v : EuclideanSpace ℝ (Fin n)) (hv : ∀ x ∈ V, x + v ∈ U)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ V) (hy : y ∈ V) :
    ‖quasilinearSecantCoefficient A (F x) (F (x + v)) -
      quasilinearSecantCoefficient A (F y) (F (y + v))‖ ≤
      (2 * B * H) * dist x y ^ a := by
  apply (quasilinearSecantCoefficient_sub_le hA hB hb
    (hF x (hVU hx)) (hF _ (hv x hx)) (hF y (hVU hy)) (hF _ (hv y hy))).trans
  have ht := hH (x + v) (hv x hx) (y + v) (hv y hy)
  rw [dist_add_right] at ht
  calc
    _ ≤ B * (H * dist x y ^ a + H * dist x y ^ a) :=
      mul_le_mul_of_nonneg_left (add_le_add (hH x (hVU hx) y (hVU hy)) ht) hB
    _ = _ := by ring

end LiquidDrop
