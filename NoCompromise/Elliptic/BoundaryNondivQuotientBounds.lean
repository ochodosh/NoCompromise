module

public import NoCompromise.Elliptic.BoundaryNondivEnergy
public import NoCompromise.Elliptic.NondivSchauderQuotientBounds

@[expose] public section

/-!
# Uniform H¹ bounds for the actual tangential quotients

The right side is the C¹,α norm of the solution plus the C⁰,α norm of the
source. The constant is fixed before the data and signed tangential step.
Only classical continuity and zero values on the flat face are added to the
interior hypotheses; no second derivative is assumed.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

lemma boundary_nondiv_segment_mem_halfBall {r R h : ℝ} {i : Fin 3}
    (hi : i ≠ Fin.last 2) (hh : |h| ≤ R - r)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ boundaryHalfBall r)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    x + t • (h • EuclideanSpace.single i 1) ∈ boundaryHalfBall R := by
  rw [smul_smul]
  apply boundaryHalfBall_add_tangential hi _ hx
  rw [abs_mul, abs_of_nonneg ht.1]
  exact (mul_le_mul_of_nonneg_right ht.2 (abs_nonneg h)).trans (by simpa using hh)

/-- Uniform actual H¹ bounds on the three-quarter ball. The coefficient-norm
bound and ellipticity constants are fixed before all solution data and signed
steps. The right side is linear in the solution/source norm sum. -/
theorem boundary_nondiv_quotient_h1_bound {α lam cap M : ℝ}
    (hα : 0 < α) (hlam : 0 < lam) (_hlamcap : lam ≤ cap) (hM : 0 ≤ M) :
    ∃ C > 0, ∀ (A : EuclideanSpace ℝ (Fin 3) →
        EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
      (b : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (z f : EuclideanSpace ℝ (Fin 3) → ℝ),
      HasC1HolderOn α A (boundaryHalfBall 1) → HasFiniteHolderNormOn α b (boundaryHalfBall 1) →
      HasC1HolderOn α z (boundaryHalfBall 1) → HasFiniteHolderNormOn α f (boundaryHalfBall 1) →
      nondivC1HolderNorm α A (boundaryHalfBall 1) ≤ M → holderNorm α b (boundaryHalfBall 1) ≤ M →
      (∀ x ∈ boundaryHalfBall (1 : ℝ), ‖A x‖ ≤ cap) →
      (∀ x ∈ boundaryHalfBall (1 : ℝ), ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v)) →
      IsWeakNondivergenceEquationOn A b z f (boundaryHalfBall 1) →
      ContinuousOn z (closure (boundaryHalfBall 1)) →
      (∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 → z x = 0) →
      ∀ (i : Fin 3) (h : ℝ), i ≠ Fin.last 2 → h ≠ 0 → |h| < 1 / 16 →
      HasH1GradientOn (coordinateDifferenceQuotient i h z)
        (coordinateDifferenceQuotient i h (gradient z)) (boundaryHalfBall (3 / 4)) ∧
      lpNorm (coordinateDifferenceQuotient i h z) 2 (volume.restrict (boundaryHalfBall (3 / 4))) +
        lpNorm (coordinateDifferenceQuotient i h (gradient z)) 2
          (volume.restrict (boundaryHalfBall (3 / 4))) ≤
        C * (nondivC1HolderNorm α z (boundaryHalfBall 1) +
          holderNorm α f (boundaryHalfBall 1)) := by
  obtain ⟨C₀, hC₀, henergy⟩ := boundary_nondiv_caccioppoli_nested_halfBalls hlam
  let V : Set (EuclideanSpace ℝ (Fin 3)) := boundaryHalfBall (7 / 8)
  let W : Set (EuclideanSpace ℝ (Fin 3)) := boundaryHalfBall (3 / 4)
  let m := volume.real V
  let K := 1 + 3 * ((3 : ℝ) + 2) * M
  let E := C₀ * m * (1 + K ^ 2)
  have hm : 0 ≤ m := measureReal_nonneg
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hWV : W ⊆ V := boundaryHalfBall_mono (by norm_num : (3 / 4 : ℝ) ≤ 7 / 8)
  refine ⟨m + E + 2, by positivity, ?_⟩
  intro A b z f hA hb hz hf hbA hbb hcap hell he hzc hzero i h hi hh hsmall
  let T := nondivC1HolderNorm α z (boundaryHalfBall 1) + holderNorm α f (boundaryHalfBall 1)
  have hT : 0 ≤ T := add_nonneg hz.norm_nonneg hf.norm_nonneg
  have hseg : ∀ x ∈ V, ∀ t ∈ Icc (0 : ℝ) 1,
      x + t • (h • EuclideanSpace.single i 1) ∈ boundaryHalfBall (1 : ℝ) :=
    fun _ hx _ ht => boundary_nondiv_segment_mem_halfBall hi (by linarith) hx ht
  have hmap : ∀ x ∈ V, x + h • EuclideanSpace.single i 1 ∈ boundaryHalfBall (1 : ℝ) := by
    intro x hx
    simpa only [one_smul] using hseg x hx 1 (by simp)
  obtain ⟨hq, heq⟩ := nondiv_quotient_equation hα
    (isOpen_boundaryHalfBall _) (isOpen_boundaryHalfBall _)
    (isBounded_ball.subset inter_subset_left) (isBounded_ball.subset inter_subset_left)
    hA hb hz hf he i hh hseg
  have htrace := (hz.hasH1GradientOn (isOpen_boundaryHalfBall 1)
    (isBounded_ball.subset inter_subset_left)).boundary_nondiv_zero_trace hzc hzero
  have hTq := htrace.boundary_nondiv_quotient (by norm_num : (7 / 8 : ℝ) ≤ 1)
    (hz.hasH1GradientOn (isOpen_boundaryHalfBall 1) (isBounded_ball.subset inter_subset_left))
    hi (by linarith : |h| ≤ 1 - 7 / 8)
  have hqW := hq.mono hWV
  refine ⟨hqW, ?_⟩
  have hF := (nondivQuotientDatum_holder hα (isOpen_boundaryHalfBall _) hA hb hz hf i hh hseg).1
  have hFb := nondivQuotientDatum_norm_le hα hM (isOpen_boundaryHalfBall _)
    hA hb hz hf hbA hbb i hh hseg
  have hqHolder := nondiv_coordinateDifferenceQuotient_holder
    (isOpen_boundaryHalfBall _) hz i hh hseg
  have hqb (x) (hx : x ∈ V) : ‖coordinateDifferenceQuotient i h z x‖ ≤ T :=
    ((hqHolder.1.nondiv_norm_le hx).trans hqHolder.2).trans
      (hz.derivative_norm_le.trans (le_add_of_nonneg_right hf.norm_nonneg))
  have hGb (x) (hx : x ∈ V) : ‖nondivQuotientDatum A b z f i h x‖ ≤ K * T :=
    (hF.nondiv_norm_le hx).trans hFb
  let : IsFiniteMeasure (volume.restrict V) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact (isBounded_ball.subset inter_subset_left).measure_lt_top⟩
  have hFG : MemLp (nondivQuotientDatum A b z f i h) 2 (volume.restrict V) := by
    apply MemLp.of_bound
      ((hF.nondiv_continuousOn hα).aestronglyMeasurable
        (isOpen_boundaryHalfBall _).measurableSet) (K * T)
    filter_upwards [ae_restrict_mem (isOpen_boundaryHalfBall _).measurableSet] with x hx
    exact hGb x hx
  have hqint : (∫ x in V, coordinateDifferenceQuotient i h z x ^ 2) ≤ m * T ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      nondiv_integral_norm_sq_le (isOpen_boundaryHalfBall _).measurableSet
        (isBounded_ball.subset inter_subset_left) hq.memLp_function hqb
  have hGint : (∫ x in V, ‖nondivQuotientDatum A b z f i h x‖ ^ 2) ≤ m * (K * T) ^ 2 :=
    nondiv_integral_norm_sq_le (isOpen_boundaryHalfBall _).measurableSet
      (isBounded_ball.subset inter_subset_left) hFG hGb
  have hAc : ContinuousOn (fun x => A (x + h • EuclideanSpace.single i 1)) V :=
    hA.contDiff.continuousOn.comp (continuous_id.add continuous_const).continuousOn hmap
  have hDint := henergy (fun x => A (x + h • EuclideanSpace.single i 1))
    (coordinateDifferenceQuotient i h z) (coordinateDifferenceQuotient i h (gradient z))
    (nondivQuotientDatum A b z f i h)
    (hAc.aestronglyMeasurable (isOpen_boundaryHalfBall _).measurableSet)
    (by
      filter_upwards [ae_restrict_mem (isOpen_boundaryHalfBall _).measurableSet] with x hx
      exact hell _ (hmap x hx))
    (by
      filter_upwards [ae_restrict_mem (isOpen_boundaryHalfBall _).measurableSet] with x hx
      exact hcap _ (hmap x hx)) hq hTq hFG heq
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
