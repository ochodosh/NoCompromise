import NoCompromise.Elliptic.QuasilinearCoefficients
import NoCompromise.Elliptic.CampanatoHolderDatum
import NoCompromise.Elliptic.NondivSchauderDifferenceEquation
import NoCompromise.Elliptic.NondivSchauderTests

/-! The nonlinear scalar divergence equation yields a genuine linear weak
system for each nonzero coordinate quotient, with the constructed segment
average as vector source. No second derivative of the solution is assumed. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The original distributional quasilinear equation, with smooth compact tests. -/
def IsWeakQuasilinearEquationOn {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (f g : EuclideanSpace ℝ (Fin n) → ℝ) (U : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
    HasCompactSupport φ → tsupport φ ⊆ U →
    (∫ x, inner ℝ (A (gradient f x)) (gradient φ x)) = -(∫ x, φ x * g x)

/-- The actual coefficient in the coordinate difference equation. -/
def quasilinearCoefficientField {n : ℕ}
    (A F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (i : Fin n) (h : ℝ) (x : EuclideanSpace ℝ (Fin n)) :=
  quasilinearSecantCoefficient A (F x) (F (x + h • EuclideanSpace.single i 1))

lemma quasilinearCoefficientField_apply_quotient {n : ℕ}
    {A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hA : ContDiff ℝ 1 A)
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (i : Fin n) (h : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    quasilinearCoefficientField A F i h x (coordinateDifferenceQuotient i h F x) =
      coordinateDifferenceQuotient i h (fun y => A (F y)) x := by
  simp only [quasilinearCoefficientField, coordinateDifferenceQuotient, map_smul,
    quasilinearSecantCoefficient_apply_sub hA]

lemma quasilinearCoefficientField_continuousOn {n : ℕ}
    {A F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hA : ContDiff ℝ 2 A)
    {M B H a : ℝ} (hB : 0 ≤ B) (hH : 0 ≤ H) (ha : 0 < a)
    (hb : ∀ p ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) M,
      ‖fderiv ℝ (fderiv ℝ A) p‖ ≤ B)
    {U V : Set (EuclideanSpace ℝ (Fin n))}
    (hF : ∀ x ∈ U, F x ∈ closedBall 0 M)
    (hhold : ∀ x ∈ U, ∀ y ∈ U, ‖F x - F y‖ ≤ H * dist x y ^ a)
    (hVU : V ⊆ U) (i : Fin n) (h : ℝ)
    (hmap : ∀ x ∈ V, x + h • EuclideanSpace.single i 1 ∈ U) :
    ContinuousOn (quasilinearCoefficientField A F i h) V := by
  apply campanato_continuousOn_of_holder_bound (by positivity : 0 ≤ 2 * B * H) ha
  exact fun _ hx _ hy => quasilinearSecantCoefficient_holder hA hB hb hF hhold hVU
    (h • EuclideanSpace.single i 1) hmap hx hy

/-- Difference quotients of a genuine C¹,α weak solution satisfy the exact
averaged-coefficient equation, with the actual Gh source. -/
theorem quasilinear_quotient_equation {n : ℕ} {a M cap B : ℝ}
    (ha : 0 < a) (hB : 0 ≤ B)
    {A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hV : IsOpen V)
    (hbU : Bornology.IsBounded U) (hbV : Bornology.IsBounded V)
    (hA : ContDiff ℝ 2 A) (hf : HasC1HolderOn a f U) (hg : HasFiniteHolderNormOn a g U)
    (hM : ∀ x ∈ U, ‖gradient f x‖ ≤ M)
    (hcap : ∀ p ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) M, ‖fderiv ℝ A p‖ ≤ cap)
    (hb : ∀ p ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) M,
      ‖fderiv ℝ (fderiv ℝ A) p‖ ≤ B)
    (he : IsWeakQuasilinearEquationOn A f g U)
    (i : Fin n) {h : ℝ} (hh : h ≠ 0)
    (hseg : ∀ x ∈ V, ∀ t ∈ Icc (0 : ℝ) 1,
      x + t • (h • EuclideanSpace.single i 1) ∈ U) :
    HasH1GradientOn (coordinateDifferenceQuotient i h f)
      (coordinateDifferenceQuotient i h (gradient f)) V ∧
    IsWeakDivergenceEquationOn (quasilinearCoefficientField A (gradient f) i h)
      (coordinateDifferenceQuotient i h (gradient f))
      (campanatoSegmentField g h (EuclideanSpace.single i 1)) V := by
  have hVU : V ⊆ U := by
    intro x hx
    simpa only [zero_smul, add_zero] using hseg x hx 0 (by simp)
  have hmap : ∀ x ∈ V, x + h • EuclideanSpace.single i 1 ∈ U := by
    intro x hx
    simpa only [one_smul] using hseg x hx 1 (by simp)
  have hq := (hf.hasH1GradientOn hU hbU).coordinateDifferenceQuotient hU hV hVU i h hmap
  refine ⟨hq, ?_⟩
  have hgc : ContinuousOn g U := hg.nondiv_continuousOn ha
  let H := campanatoSegmentField g h (EuclideanSpace.single i 1)
  have hH : HasFiniteHolderNormOn a H V :=
    (schauder_holder_mono
      (campanatoSegmentField_holder hgc hg h (EuclideanSpace.single i 1) (by simp)).1 hseg).1
  have hFc : ContinuousOn (gradient f) U := continuousOn_gradient_of_contDiffOn hU hf.contDiff
  have hFM : ∀ x ∈ U, gradient f x ∈ closedBall 0 M := by
    intro x hx
    simpa only [mem_closedBall, dist_zero_right] using hM x hx
  have hhold := hf.gradient_holder.1
  have hAc := quasilinearCoefficientField_continuousOn hA hB hhold.seminorm_nonneg ha hb hFM
    (fun x hx y hy => by simpa only [dist_eq_norm] using hhold.nondiv_norm_sub_le hx hy)
    hVU i h hmap
  let : IsFiniteMeasure (volume.restrict V) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hbV.measure_lt_top⟩
  have hmH : MemLp H 2 (volume.restrict V) := by
    apply MemLp.of_bound ((hH.nondiv_continuousOn ha).aestronglyMeasurable hV.measurableSet)
      (holderNorm a H V)
    filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
    exact hH.nondiv_norm_le hx
  have hmP := campanato_memLp_apply_bounded
    (hAc.aestronglyMeasurable hV.measurableSet) hq.memLp_gradient (Λ := cap)
    (by
      filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
      exact quasilinearSecantCoefficient_norm_le hcap (hFM x (hVU hx)) (hFM _ (hmap x hx)))
  apply nondiv_weakDivergenceEquationOn_of_smooth_tests hV (hmP.sub hmH)
  intro φ hφ hcφ hsφ
  have heId : IsWeakScalarDivergenceEquationOn
      (fun _ => ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
      (fun x => A (gradient f x)) g U := by
    simpa only [IsWeakScalarDivergenceEquationOn, IsWeakQuasilinearEquationOn,
      ContinuousLinearMap.id_apply] using he
  have ht := heId.coordinateDifferenceQuotient hU hV continuousOn_const
    (hA.continuous.comp_continuousOn hFc) hgc hVU i h hmap φ hφ hcφ hsφ
  have hflux (x) :
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
        (coordinateDifferenceQuotient i h (fun y => A (gradient f y)) x) +
      coordinateDifferenceQuotient i h
        (fun _ => ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) x
          (A (gradient f x)) =
      coordinateDifferenceQuotient i h (fun y => A (gradient f y)) x := by
    simp [coordinateDifferenceQuotient]
  simp_rw [hflux] at ht
  have hp := campanatoSegmentField_distribution hU hgc (hφ.of_le (by simp)) hcφ hh
    (EuclideanSpace.single i 1) (hsφ.trans hseg)
  have hcδ : ContinuousOn (coordinateDifferenceQuotient i h (fun y => A (gradient f y))) V := by
    have hc := hA.continuous.comp_continuousOn hFc
    simpa only [coordinateDifferenceQuotient] using!
      ((hc.comp (continuous_id.add continuous_const).continuousOn hmap).sub
        (hc.mono hVU)).const_smul h⁻¹
  have hiδ := nondiv_integrable_flux_test hV hcδ (hφ.of_le (by simp)) hcφ hsφ
  have hiH := nondiv_integrable_flux_test hV (hH.nondiv_continuousOn ha)
    (hφ.of_le (by simp)) hcφ hsφ
  simp_rw [quasilinearCoefficientField_apply_quotient (hA.of_le (by norm_num)), inner_sub_left]
  rw [integral_sub hiδ hiH, ht, hp]
  simp only [coordinateDifferenceQuotient, smul_eq_mul, div_eq_mul_inv, mul_comm]
  ring

end LiquidDrop
