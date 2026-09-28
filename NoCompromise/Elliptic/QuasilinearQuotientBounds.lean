import NoCompromise.Elliptic.QuasilinearEquation
import NoCompromise.Elliptic.NondivSchauderQuotientBounds

/-! Uniform H¹ bounds for the genuine quasilinear difference quotients. The
constant uses the gradient bound and scalar-source norm, and is invariant under
adding constants to the solution. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma quasilinear_quotient_norm_le {n : ℕ} {a M : ℝ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hf : HasC1HolderOn a f U)
    (hM : ∀ x ∈ U, ‖gradient f x‖ ≤ M) (i : Fin n) {h : ℝ} (hh : h ≠ 0)
    (x : EuclideanSpace ℝ (Fin n))
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • (h • EuclideanSpace.single i 1) ∈ U) :
    ‖coordinateDifferenceQuotient i h f x‖ ≤ M := by
  have hd : ∀ y ∈ U, ‖fderiv ℝ f y‖ ≤ M := by
    intro y hy
    simpa only [gradient, LinearIsometryEquiv.norm_map] using hM y hy
  have hi := nondiv_norm_segment_increment_le hU hf.contDiff hd x
    (h • EuclideanSpace.single i 1) hseg
  rw [coordinateDifferenceQuotient, norm_smul]
  apply (mul_le_mul_of_nonneg_left hi (norm_nonneg _)).trans_eq
  simp only [norm_smul, PiLp.norm_single, norm_one, mul_one, norm_inv]
  rw [mul_left_comm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hh), mul_one]

/-- A uniform actual H¹ bound on B₃/₄. All constants are fixed before the nonlinear
flux, the solution, the source, the coordinate, and the signed quotient step. -/
theorem quasilinear_quotient_h1_bound {n : ℕ} {a lam cap M B N : ℝ}
    (ha : 0 < a) (hlam : 0 < lam) (hlamcap : lam ≤ cap)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hN : 0 ≤ N) :
    ∃ C > 0, ∀ (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (f g : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiff ℝ 2 A → HasC1HolderOn a f (ball 0 1) →
      HasFiniteHolderNormOn a g (ball 0 1) → holderNorm a g (ball 0 1) ≤ N →
      (∀ x ∈ ball 0 (1 : ℝ), ‖gradient f x‖ ≤ M) →
      (∀ p ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) M, ‖fderiv ℝ A p‖ ≤ cap) →
      (∀ p ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) M,
        ‖fderiv ℝ (fderiv ℝ A) p‖ ≤ B) →
      (∀ p ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) M, ∀ ξ,
        lam * ‖ξ‖ ^ 2 ≤ inner ℝ (fderiv ℝ A p ξ) ξ) →
      IsWeakQuasilinearEquationOn A f g (ball 0 1) →
      ∀ (i : Fin n) (h : ℝ), h ≠ 0 → |h| < 1 / 16 →
      HasH1GradientOn (coordinateDifferenceQuotient i h f)
        (coordinateDifferenceQuotient i h (gradient f)) (ball 0 (3 / 4)) ∧
      lpNorm (coordinateDifferenceQuotient i h f) 2 (volume.restrict (ball 0 (3 / 4))) +
        lpNorm (coordinateDifferenceQuotient i h (gradient f)) 2
          (volume.restrict (ball 0 (3 / 4))) ≤ C := by
  obtain ⟨C₀, hC₀, henergy⟩ := nondiv_caccioppoli_nested_balls (n := n) hlam hlamcap
  let V : Set (EuclideanSpace ℝ (Fin n)) := ball 0 (7 / 8)
  let W : Set (EuclideanSpace ℝ (Fin n)) := ball 0 (3 / 4)
  let m := volume.real V
  let E := 2 * C₀ * m
  let T := M + N
  have hm : 0 ≤ m := measureReal_nonneg
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hT : 0 ≤ T := add_nonneg hM hN
  have hWV : W ⊆ V := ball_subset_ball (by norm_num : (3 / 4 : ℝ) ≤ 7 / 8)
  refine ⟨(m + E + 2) * T + 1, by positivity, ?_⟩
  intro A f g hA hf hg hgN hfM hcap hb hell he i h hh hsmall
  have hseg : ∀ x ∈ V, ∀ t ∈ Icc (0 : ℝ) 1,
      x + t • (h • EuclideanSpace.single i 1) ∈ ball 0 (1 : ℝ) :=
    fun _ hx _ ht => nondiv_segment_mem_unitBall i hsmall hx ht
  have hVU : V ⊆ ball 0 (1 : ℝ) := ball_subset_ball (by norm_num)
  have hmap : ∀ x ∈ V, x + h • EuclideanSpace.single i 1 ∈ ball 0 (1 : ℝ) := by
    intro x hx
    simpa only [one_smul] using hseg x hx 1 (by simp)
  obtain ⟨hq, heq⟩ := quasilinear_quotient_equation ha hB isOpen_ball isOpen_ball
    isBounded_ball isBounded_ball hA hf hg hfM hcap hb he i hh hseg
  have hqW := hq.mono hWV
  refine ⟨hqW, ?_⟩
  let G := campanatoSegmentField g h (EuclideanSpace.single i 1)
  obtain ⟨hG₀, hG₀b⟩ := campanatoSegmentField_holder (hg.nondiv_continuousOn ha) hg
    h (EuclideanSpace.single i 1) (by simp)
  obtain ⟨hG, hGb⟩ := schauder_holder_mono hG₀ hseg
  have hGb' (x) (hx : x ∈ V) : ‖G x‖ ≤ T :=
    (hG.nondiv_norm_le hx).trans ((hGb.trans (hG₀b.trans hgN)).trans
      (le_add_of_nonneg_left hM))
  have hqb (x) (hx : x ∈ V) : ‖coordinateDifferenceQuotient i h f x‖ ≤ T :=
    (quasilinear_quotient_norm_le isOpen_ball hf hfM i hh x (hseg x hx)).trans
      (le_add_of_nonneg_right hN)
  let : IsFiniteMeasure (volume.restrict V) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact isBounded_ball.measure_lt_top⟩
  have hmG : MemLp G 2 (volume.restrict V) := by
    apply MemLp.of_bound ((hG.nondiv_continuousOn ha).aestronglyMeasurable measurableSet_ball) T
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact hGb' x hx
  have hqint : (∫ x in V, coordinateDifferenceQuotient i h f x ^ 2) ≤ m * T ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      nondiv_integral_norm_sq_le measurableSet_ball isBounded_ball hq.memLp_function hqb
  have hGint : (∫ x in V, ‖G x‖ ^ 2) ≤ m * T ^ 2 :=
    nondiv_integral_norm_sq_le measurableSet_ball isBounded_ball hmG hGb'
  have hFM : ∀ x ∈ ball 0 (1 : ℝ), gradient f x ∈ closedBall 0 M := by
    intro x hx
    simpa only [mem_closedBall, dist_zero_right] using hfM x hx
  have hhold := hf.gradient_holder.1
  have hAc := quasilinearCoefficientField_continuousOn hA hB hhold.seminorm_nonneg ha hb hFM
    (fun x hx y hy => by simpa only [dist_eq_norm] using hhold.nondiv_norm_sub_le hx hy)
    hVU i h hmap
  have hDint := henergy (quasilinearCoefficientField A (gradient f) i h)
    (coordinateDifferenceQuotient i h f) (coordinateDifferenceQuotient i h (gradient f)) G
    (hAc.aestronglyMeasurable measurableSet_ball)
    (by
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      intro ξ
      simpa only [real_inner_comm, quasilinearCoefficientField] using
        quasilinearSecantCoefficient_elliptic (hA.of_le (by norm_num)) hell
          (hFM x (hVU hx)) (hFM _ (hmap x hx)) ξ)
    (by
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      exact quasilinearSecantCoefficient_norm_le hcap (hFM x (hVU hx)) (hFM _ (hmap x hx)))
    hq hmG heq
  have hDsq : lpNorm (coordinateDifferenceQuotient i h (gradient f)) 2
      (volume.restrict W) ^ 2 ≤ E * T ^ 2 := by
    rw [lpNorm_two_sq_eq_integral_norm_sq hqW.memLp_gradient]
    apply hDint.trans
    have ht := mul_le_mul_of_nonneg_left (add_le_add hqint hGint) hC₀.le
    convert ht using 1
    dsimp [E]
    ring
  have hqsq : lpNorm (coordinateDifferenceQuotient i h f) 2 (volume.restrict W) ^ 2 ≤
      m * T ^ 2 := by
    rw [lpNorm_two_sq_eq_integral_norm_sq hqW.memLp_function]
    apply (setIntegral_mono_set (hq.memLp_function.integrable_norm_pow (by norm_num))
      (Eventually.of_forall (fun _ => sq_nonneg _)) (Eventually.of_forall hWV)).trans
    simpa only [Real.norm_eq_abs, sq_abs] using hqint
  have hqbound := nondiv_le_mul_of_sq_le
    (lpNorm_nonneg (f := coordinateDifferenceQuotient i h f) (p := 2)
      (μ := volume.restrict W)) hm hT hqsq
  have hDbound := nondiv_le_mul_of_sq_le
    (lpNorm_nonneg (f := coordinateDifferenceQuotient i h (gradient f)) (p := 2)
      (μ := volume.restrict W)) hE hT hDsq
  nlinarith only [hqbound, hDbound]

end LiquidDrop
