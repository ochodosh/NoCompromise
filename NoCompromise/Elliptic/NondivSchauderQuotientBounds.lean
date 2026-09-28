import NoCompromise.Elliptic.NondivSchauderQuotient
import NoCompromise.Elliptic.NondivSchauderEnergy

/-!
# Uniform bounds for the constructed interior quotients

The constants are chosen before the coefficient fields, the solution, and the
right-hand side. Small signed coordinate steps preserve every segment from
B₇/₈ to B₁. Caccioppoli then controls the genuine quotient gradient on B₃/₄.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma nondiv_segment_mem_unitBall {n : ℕ} (i : Fin n) {h : ℝ} (hh : |h| < 1 / 16)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ ball 0 (7 / 8 : ℝ))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    x + t • (h • EuclideanSpace.single i 1) ∈ ball 0 (1 : ℝ) := by
  rw [mem_ball_zero_iff] at hx ⊢
  have hv : ‖t • (h • EuclideanSpace.single i (1 : ℝ))‖ ≤ |h| := by
    simp only [norm_smul, PiLp.norm_single, norm_one, mul_one,
      Real.norm_of_nonneg ht.1, Real.norm_eq_abs]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.2 (abs_nonneg h)
  exact (norm_add_le _ _).trans_lt (by linarith)

/-- A bounded actual L² function has the expected squared integral bound. -/
lemma nondiv_integral_norm_sq_le {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : MeasurableSet U)
    (hbU : Bornology.IsBounded U) {f : EuclideanSpace ℝ (Fin n) → F}
    (hf : MemLp f 2 (volume.restrict U)) {B : ℝ}
    (hb : ∀ x ∈ U, ‖f x‖ ≤ B) :
    (∫ x in U, ‖f x‖ ^ 2) ≤ volume.real U * B ^ 2 := by
  let : IsFiniteMeasure (volume.restrict U) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hbU.measure_lt_top⟩
  have hi := hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have ht := integral_mono_ae hi (integrable_const (B ^ 2)) (by
    filter_upwards [ae_restrict_mem hU] with x hx
    exact pow_le_pow_left₀ (norm_nonneg _) (hb x hx) 2)
  simpa only [integral_const, Measure.restrict_apply_univ, smul_eq_mul, measureReal_def] using ht

/-- Uniform size of the explicit forcing in terms of one bound for the two
coefficient norms and the actual solution/source norm sum. -/
lemma nondivQuotientDatum_norm_le {n : ℕ} {α M : ℝ} (hα : 0 < α) (hM : 0 ≤ M)
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {b : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {z f : EuclideanSpace ℝ (Fin n) → ℝ}
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hA : HasC1HolderOn α A U) (hb : HasFiniteHolderNormOn α b U)
    (hz : HasC1HolderOn α z U) (hf : HasFiniteHolderNormOn α f U)
    (hbA : nondivC1HolderNorm α A U ≤ M) (hbb : holderNorm α b U ≤ M)
    (i : Fin n) {h : ℝ} (hh : h ≠ 0)
    (hseg : ∀ x ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, x + t • (h • EuclideanSpace.single i 1) ∈ U) :
    holderNorm α (nondivQuotientDatum A b z f i h) V ≤
      (1 + 3 * ((n : ℝ) + 2) * M) *
        (nondivC1HolderNorm α z U + holderNorm α f U) := by
  apply (nondivQuotientDatum_holder hα hU hA hb hz hf i hh hseg).2.trans
  have hD := hA.derivative_norm_le.trans hbA
  have hDz := hz.gradient_holder.2.trans hz.derivative_norm_le
  have hterm : 3 * holderNorm α (fderiv ℝ A) U * holderNorm α (gradient z) U ≤
      3 * M * nondivC1HolderNorm α z U :=
    mul_le_mul (mul_le_mul_of_nonneg_left hD (by norm_num)) hDz
      hz.gradient_holder.1.norm_nonneg (by positivity)
  have hcoef : (n : ℝ) * nondivC1HolderNorm α A U + holderNorm α b U ≤
      ((n : ℝ) + 1) * M := by nlinarith
  have hterm' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcoef (by norm_num : (0 : ℝ) ≤ 3)) hz.norm_nonneg
  nlinarith [hz.norm_nonneg, hf.norm_nonneg,
    mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 3 * ((n : ℝ) + 2)) hM) hf.norm_nonneg]

lemma nondiv_le_mul_of_sq_le {a B T : ℝ} (ha : 0 ≤ a) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (h : a ^ 2 ≤ B * T ^ 2) : a ≤ (B + 1) * T := by
  apply (sq_le_sq₀ ha (mul_nonneg (by positivity) hT)).mp
  apply h.trans
  have hb : B ≤ (B + 1) ^ 2 := by nlinarith only [sq_nonneg B, hB]
  simpa only [mul_pow] using mul_le_mul_of_nonneg_right hb (sq_nonneg T)

/-- Uniform actual H¹ bounds on the three-quarter ball. The coefficient-norm
bound and ellipticity constants are fixed before all solution data and signed
steps. The right side is linear in the solution/source norm sum. -/
theorem nondiv_quotient_h1_bound {n : ℕ} {α lam cap M : ℝ}
    (hα : 0 < α) (hlam : 0 < lam) (hlamcap : lam ≤ cap) (hM : 0 ≤ M) :
    ∃ C > 0, ∀ (A : EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (b : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (z f : EuclideanSpace ℝ (Fin n) → ℝ),
      HasC1HolderOn α A (ball 0 1) → HasFiniteHolderNormOn α b (ball 0 1) →
      HasC1HolderOn α z (ball 0 1) → HasFiniteHolderNormOn α f (ball 0 1) →
      nondivC1HolderNorm α A (ball 0 1) ≤ M → holderNorm α b (ball 0 1) ≤ M →
      (∀ x ∈ ball 0 (1 : ℝ), ‖A x‖ ≤ cap) →
      (∀ x ∈ ball 0 (1 : ℝ), ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v)) →
      IsWeakNondivergenceEquationOn A b z f (ball 0 1) →
      ∀ (i : Fin n) (h : ℝ), h ≠ 0 → |h| < 1 / 16 →
      HasH1GradientOn (coordinateDifferenceQuotient i h z)
        (coordinateDifferenceQuotient i h (gradient z)) (ball 0 (3 / 4)) ∧
      lpNorm (coordinateDifferenceQuotient i h z) 2 (volume.restrict (ball 0 (3 / 4))) +
        lpNorm (coordinateDifferenceQuotient i h (gradient z)) 2
          (volume.restrict (ball 0 (3 / 4))) ≤
        C * (nondivC1HolderNorm α z (ball 0 1) + holderNorm α f (ball 0 1)) := by
  obtain ⟨C₀, hC₀, henergy⟩ := nondiv_caccioppoli_nested_balls (n := n) hlam hlamcap
  let V : Set (EuclideanSpace ℝ (Fin n)) := ball 0 (7 / 8)
  let W : Set (EuclideanSpace ℝ (Fin n)) := ball 0 (3 / 4)
  let m := volume.real V
  let K := 1 + 3 * ((n : ℝ) + 2) * M
  let E := C₀ * m * (1 + K ^ 2)
  have hm : 0 ≤ m := measureReal_nonneg
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hWV : W ⊆ V := ball_subset_ball (by norm_num : (3 / 4 : ℝ) ≤ 7 / 8)
  refine ⟨m + E + 2, by positivity, ?_⟩
  intro A b z f hA hb hz hf hbA hbb hcap hell he i h hh hsmall
  let T := nondivC1HolderNorm α z (ball 0 1) + holderNorm α f (ball 0 1)
  have hT : 0 ≤ T := add_nonneg hz.norm_nonneg hf.norm_nonneg
  have hseg : ∀ x ∈ V, ∀ t ∈ Icc (0 : ℝ) 1,
      x + t • (h • EuclideanSpace.single i 1) ∈ ball 0 (1 : ℝ) :=
    fun _ hx _ ht => nondiv_segment_mem_unitBall i hsmall hx ht
  have hmap : ∀ x ∈ V, x + h • EuclideanSpace.single i 1 ∈ ball 0 (1 : ℝ) := by
    intro x hx
    simpa only [one_smul] using hseg x hx 1 (by simp)
  obtain ⟨hq, heq⟩ := nondiv_quotient_equation hα isOpen_ball isOpen_ball
    isBounded_ball isBounded_ball hA hb hz hf he i hh hseg
  have hqW := hq.mono hWV
  refine ⟨hqW, ?_⟩
  have hF := (nondivQuotientDatum_holder hα isOpen_ball hA hb hz hf i hh hseg).1
  have hFb := nondivQuotientDatum_norm_le hα hM isOpen_ball hA hb hz hf hbA hbb i hh hseg
  have hqHolder := nondiv_coordinateDifferenceQuotient_holder isOpen_ball hz i hh hseg
  have hqb (x) (hx : x ∈ V) : ‖coordinateDifferenceQuotient i h z x‖ ≤ T :=
    ((hqHolder.1.nondiv_norm_le hx).trans hqHolder.2).trans
      (hz.derivative_norm_le.trans (le_add_of_nonneg_right hf.norm_nonneg))
  have hGb (x) (hx : x ∈ V) : ‖nondivQuotientDatum A b z f i h x‖ ≤ K * T :=
    (hF.nondiv_norm_le hx).trans hFb
  let : IsFiniteMeasure (volume.restrict V) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact isBounded_ball.measure_lt_top⟩
  have hFG : MemLp (nondivQuotientDatum A b z f i h) 2 (volume.restrict V) := by
    apply MemLp.of_bound
      ((hF.nondiv_continuousOn hα).aestronglyMeasurable measurableSet_ball) (K * T)
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact hGb x hx
  have hqint : (∫ x in V, coordinateDifferenceQuotient i h z x ^ 2) ≤ m * T ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      nondiv_integral_norm_sq_le measurableSet_ball isBounded_ball hq.memLp_function hqb
  have hGint : (∫ x in V, ‖nondivQuotientDatum A b z f i h x‖ ^ 2) ≤ m * (K * T) ^ 2 :=
    nondiv_integral_norm_sq_le measurableSet_ball isBounded_ball hFG hGb
  have hAc : ContinuousOn (fun x => A (x + h • EuclideanSpace.single i 1)) V :=
    hA.contDiff.continuousOn.comp (continuous_id.add continuous_const).continuousOn hmap
  have hDint := henergy (fun x => A (x + h • EuclideanSpace.single i 1))
    (coordinateDifferenceQuotient i h z) (coordinateDifferenceQuotient i h (gradient z))
    (nondivQuotientDatum A b z f i h) (hAc.aestronglyMeasurable measurableSet_ball)
    (by
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      exact hell _ (hmap x hx))
    (by
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      exact hcap _ (hmap x hx)) hq hFG heq
  have hDsq : lpNorm (coordinateDifferenceQuotient i h (gradient z)) 2
      (volume.restrict W) ^ 2 ≤ E * T ^ 2 := by
    rw [lpNorm_two_sq_eq_integral_norm_sq hqW.memLp_gradient]
    apply hDint.trans
    have ht := mul_le_mul_of_nonneg_left (add_le_add hqint hGint) hC₀.le
    convert ht using 1
    dsimp [E]
    ring
  have hqsq : lpNorm (coordinateDifferenceQuotient i h z) 2 (volume.restrict W) ^ 2 ≤
      m * T ^ 2 := by
    rw [lpNorm_two_sq_eq_integral_norm_sq hqW.memLp_function]
    apply (setIntegral_mono_set (hq.memLp_function.integrable_norm_pow (by norm_num))
      (Eventually.of_forall (fun _ => sq_nonneg _)) (Eventually.of_forall hWV)).trans
    simpa only [Real.norm_eq_abs, sq_abs] using hqint
  have hqbound := nondiv_le_mul_of_sq_le
    (lpNorm_nonneg (f := coordinateDifferenceQuotient i h z) (p := 2)
      (μ := volume.restrict W)) hm hT hqsq
  have hDbound := nondiv_le_mul_of_sq_le
    (lpNorm_nonneg (f := coordinateDifferenceQuotient i h (gradient z)) (p := 2)
      (μ := volume.restrict W)) hE hT hDsq
  change _ ≤ (m + E + 2) * T
  nlinarith only [hqbound, hDbound]

end LiquidDrop
