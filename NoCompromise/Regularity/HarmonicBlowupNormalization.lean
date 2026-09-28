import NoCompromise.Sobolev.H1Poincare
import NoCompromise.Sobolev.H1Approximation

/-!
# Actual normalization of the graph functions

Subtract the average on the half disk and divide by the positive excess scale.
The weak gradient is divided by the same number. Poincaré bounds the resulting
Hilbert-space norm uniformly from the graph Dirichlet estimate, independently
of the graph height or its additive constant.
-/

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped Topology ENNReal NNReal Gradient
namespace LiquidDrop

/-- The literal normalized graph function in blueprint `eq:blowup-normalized`. -/
def harmonicBlowupFunction (f : EuclideanSpace ℝ (Fin 2) → ℝ) (a : ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  a⁻¹ * (f x - ⨍ y in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2), f y)

/-- A Lipschitz function and its actual gradient belong to H¹ on a finite disk. -/
lemma harmonicBlowup_hasH1_lipschitz
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    HasH1GradientOn f (gradient f) (ball 0 (1 / 2)) := by
  let : IsFiniteMeasure (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2))) :=
    ⟨by simpa using (measure_ball_lt_top (μ := volume) (x := (0 : EuclideanSpace ℝ (Fin 2)))
      (r := (1 / 2 : ℝ)))⟩
  refine ⟨hasWeakGradientOn_of_lipschitz hf _, ?_, ?_⟩
  · apply MemLp.of_bound hf.continuous.measurable.aestronglyMeasurable (‖f 0‖ + (K : ℝ))
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have hx' : ‖x‖ < 1 / 2 := by simpa only [mem_ball, dist_zero_right] using hx
    have hh := hf.norm_sub_le x 0
    rw [sub_zero] at hh
    have ht' := norm_add_le (f x - f 0) (f 0)
    rw [sub_add_cancel] at ht'
    nlinarith [K.coe_nonneg]
  · exact MemLp.of_bound (measurable_gradient f).aestronglyMeasurable (K : ℝ)
      (Eventually.of_forall (norm_gradient_le_of_lipschitz hf))

/-- Normalization preserves the actual weak-gradient identity. -/
theorem harmonicBlowup_hasH1GradientOn
    {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    {G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hf : HasH1GradientOn f G (ball 0 (1 / 2))) (a : ℝ) :
    HasH1GradientOn (harmonicBlowupFunction f a) (fun x => a⁻¹ • G x)
      (ball 0 (1 / 2)) := by
  let : IsFiniteMeasure (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2))) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (measure_ball_lt_top (μ := volume) (x := (0 : EuclideanSpace ℝ (Fin 2)))
        (r := (1 / 2 : ℝ)))⟩
  let c := ⨍ y in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2), f y
  have hc : HasH1GradientOn (fun _ => c) (fun _ => 0)
      (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2)) := by
    refine ⟨?_, memLp_const c, memLp_const (0 : EuclideanSpace ℝ (Fin 2))⟩
    simpa only [gradient_fun_const'] using
      hasWeakGradientOn_of_contDiffOn isOpen_ball (contDiff_const (c := c)).contDiffOn
  simpa only [harmonicBlowupFunction, c, sub_zero] using! (hf.sub hc).const_mul a⁻¹

/-- The actual H¹ class of the normalized graph and its specified gradient. -/
def harmonicBlowupClass (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hf : HasH1GradientOn f G (ball 0 (1 / 2))) (a : ℝ) :
    H1Space (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2)) :=
  H1Space.ofFunction (harmonicBlowupFunction f a) (fun x => a⁻¹ • G x)
    (harmonicBlowup_hasH1GradientOn hf a)

lemma harmonicBlowupClass_coeFn (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hf : HasH1GradientOn f G (ball 0 (1 / 2))) (a : ℝ) :
    ⇑(harmonicBlowupClass f G hf a) =ᵐ[volume.restrict (ball 0 (1 / 2))]
      harmonicBlowupFunction f a := H1Space.coeFn_ofFunction _ _ _

lemma harmonicBlowupClass_gradient_pairing (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hf : HasH1GradientOn f G (ball 0 (1 / 2))) (a : ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) :
    (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2),
      inner ℝ ((harmonicBlowupClass f G hf a).gradientLp x) (P x)) =
      a⁻¹ * ∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2), inner ℝ (G x) (P x) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [H1Space.gradientLp_ofFunction (harmonicBlowupFunction f a)
    (fun x => a⁻¹ • G x) (harmonicBlowup_hasH1GradientOn hf a)] with x hx
  change (harmonicBlowupClass f G hf a).gradientLp x = a⁻¹ • G x at hx
  rw [hx, real_inner_smul_left]

lemma harmonicBlowupClass_mean_zero (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hf : HasH1GradientOn f G (ball 0 (1 / 2))) (a : ℝ) :
    (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2),
      harmonicBlowupClass f G hf a x) = 0 := by
  rw [integral_congr_ae (harmonicBlowupClass_coeFn f G hf a)]
  simp only [harmonicBlowupFunction, integral_const_mul,
    setAverage_sub_setAverage measure_ball_lt_top.ne, mul_zero]

/-- One constant controls the full norm of every zero-mean H¹ class on the half disk. -/
theorem harmonicBlowup_mean_zero_norm_bound :
    ∃ P > 0, ∀ u : H1Space (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2)),
      (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2), u x) = 0 →
      ‖u‖ ≤ P * ‖u.gradientLp‖ := by
  have hcompact (u : ℕ → H1Space (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2)))
      (hu : ∀ j, ‖u j‖ ≤ 2) :
      ∃ v : H1Space (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2)),
        ∃ σ : ℕ → ℕ, StrictMono σ ∧
          Tendsto (fun j => (u (σ j)).toLp) atTop (𝓝 v.toLp) := by
    obtain ⟨v, σ, hσ, _, _, ht⟩ := rellich_disk 0 (by norm_num : (0 : ℝ) < 1 / 2) u hu
    exact ⟨v, σ, hσ, ht⟩
  obtain ⟨P, hP, hp⟩ := exists_h1_poincare_mean_zero_of_compactness
    (D := ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2)) isOpen_ball
    (convex_ball _ _).isPreconnected measure_ball_lt_top hcompact
  refine ⟨P + 1, by positivity, fun u hu => ?_⟩
  have h := hp u hu
  have hb := u.norm_le_sum
  nlinarith

/-- Constants precede every graph and scale: a true Dirichlet estimate of size
`C*a²` bounds the normalized graph in H¹ independently of its height. -/
theorem harmonicBlowup_normalized_bound {C : ℝ} (hC : 0 ≤ C) :
    ∃ B > 0, ∀ (f : EuclideanSpace ℝ (Fin 2) → ℝ)
      (G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
      (hf : HasH1GradientOn f G (ball 0 (1 / 2))) (a : ℝ), 0 < a →
      (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2), ‖G x‖ ^ 2) ≤ C * a ^ 2 →
      ‖harmonicBlowupClass f G hf a‖ ≤ B := by
  obtain ⟨P, hP, hp⟩ := harmonicBlowup_mean_zero_norm_bound
  refine ⟨P * (Real.sqrt C + 1), by positivity, fun f G hf a ha he => ?_⟩
  let u := harmonicBlowupClass f G hf a
  have hgrad : ‖u.gradientLp‖ ^ 2 ≤ C := by
    change ‖(harmonicBlowup_hasH1GradientOn hf a).memLp_gradient.toLp
      (fun x => a⁻¹ • G x)‖ ^ 2 ≤ C
    rw [Lp.norm_toLp, toReal_eLpNorm]
    change lpNorm (a⁻¹ • G) 2 (volume.restrict (ball 0 (1 / 2))) ^ 2 ≤ C
    rw [lpNorm_const_smul, coe_nnnorm, Real.norm_of_nonneg (inv_nonneg.mpr ha.le),
      mul_pow, lpNorm_two_sq_eq_integral_norm_sq hf.memLp_gradient]
    have hh := mul_le_mul_of_nonneg_left he (sq_nonneg a⁻¹)
    convert hh using 1 <;> first | rfl | (field_simp [ha.ne'])
  have hb : ‖u.gradientLp‖ ≤ Real.sqrt C := by
    nlinarith [Real.sq_sqrt hC, Real.sqrt_nonneg C]
  have hp' := hp u (harmonicBlowupClass_mean_zero f G hf a)
  exact hp'.trans (mul_le_mul_of_nonneg_left (hb.trans (by linarith)) hP.le)

end LiquidDrop
