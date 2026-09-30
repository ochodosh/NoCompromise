module

public import NoCompromise.Elliptic.BoundaryHolderOdd
public import NoCompromise.Elliptic.BoundaryHolderLocalization

@[expose] public section

/-!
# Gradient-energy control for adapted odd reflection

Inside the region where the cutoff is one, the reflected energy is controlled
solely by the original gradient energy. The cutoff's derivatives and the scalar
L² norm therefore do not enter the eventual frozen boundary estimates.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma boundary_zero_gradient_energy
    {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hf : HasH1GradientOn f G (ball 0 1 ∩ {x | 0 < x (Fin.last 2)})) :
    (∫ x in ball 0 (1 / 64 : ℝ), ‖boundaryHolderZeroGradient f G x‖ ^ 2) ≤
      ∫ x in ball 0 1 ∩ {x | 0 < x (Fin.last 2)}, ‖G x‖ ^ 2 := by
  let W := ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 64 : ℝ)
  let U := {x : EuclideanSpace ℝ (Fin 3) | 0 < x (Fin.last 2)}
  have hU : MeasurableSet U := boundary_holder_open_upper.measurableSet
  have he : (∫ x in W, ‖boundaryHolderZeroGradient f G x‖ ^ 2) =
      ∫ x in W ∩ U, ‖G x‖ ^ 2 := by
    calc
      _ = ∫ x in W, U.indicator (fun y => ‖G y‖ ^ 2) x := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with x hx
        by_cases hxU : x ∈ U
        · rw [indicator_of_mem hxU, boundaryHolderZeroGradient_eq f G hx hxU]
        · rw [indicator_of_notMem hxU,
            boundaryHolderZeroGradient_eq_zero f G (le_of_not_gt hxU)]
          simp
      _ = ∫ x in U ∩ W, ‖G x‖ ^ 2 := by
        rw [integral_indicator hU, Measure.restrict_restrict hU]
      _ = _ := by rw [inter_comm U W]
  rw [he]
  exact integral_mono_measure
    (Measure.restrict_mono (inter_subset_inter_left _ (ball_subset_ball (by norm_num))) le_rfl)
    (Eventually.of_forall fun _ => sq_nonneg _) hf.memLp_gradient.norm.integrable_sq

/-- The squared L² gradient bound for adapted odd reflection on a ball whose
image lies inside the region where the cutoff is one. -/
theorem boundary_odd_gradient_energy
    {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hf : HasH1GradientOn f G (ball 0 1 ∩ {x | 0 < x (Fin.last 2)}))
    (hT : HasZeroFlatTraceOn f G (ball 0 1))
    (A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (n : EuclideanSpace ℝ (Fin 3))
    (hn : inner ℝ (frozenSymmetricPart A n) n ≠ 0)
    {r M : ℝ} (hbound : ‖boundaryFrozenReflection A n‖ ≤ M)
    (hr : r ≤ 1 / 64)
    (hmap : MapsTo (boundaryFrozenReflection A n) (ball 0 r) (ball 0 (1 / 64 : ℝ))) :
    (∫ x in ball 0 r,
      ‖boundaryHolderZeroGradient f G x - (boundaryFrozenReflection A n).adjoint
        (boundaryHolderZeroGradient f G (boundaryFrozenReflection A n x))‖ ^ 2) ≤
      (2 + 2 * M ^ 2) * (∫ x in ball 0 1 ∩ {x | 0 < x (Fin.last 2)}, ‖G x‖ ^ 2) := by
  let G₀ := boundaryHolderZeroGradient f G
  let R := boundaryFrozenReflectionEquiv A n hn
  let W := ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 64 : ℝ)
  let D := ball (0 : EuclideanSpace ℝ (Fin 3)) r
  have hm : MemLp G₀ 2 volume := by
    simpa only [Measure.restrict_univ] using (hf.boundary_zero_extension_ball hT).memLp_gradient
  have hmr := hm.comp_measurePreserving (boundaryFrozenReflection_measurePreserving A n hn)
  have hmadj := R.toContinuousLinearMap.adjoint.comp_memLp' hmr
  have hi0 : Integrable (fun x => ‖G₀ x‖ ^ 2) volume := hm.norm.integrable_sq
  have hir : Integrable (fun x => ‖G₀ (R x)‖ ^ 2) volume := hmr.norm.integrable_sq
  have hib : Integrable (fun x => ‖G₀ x - R.toContinuousLinearMap.adjoint (G₀ (R x))‖ ^ 2)
      (volume.restrict D) := (hm.sub hmadj).norm.integrable_sq.integrableOn
  have hfirst : (∫ x in D, ‖G₀ x‖ ^ 2) ≤ ∫ x in W, ‖G₀ x‖ ^ 2 :=
    integral_mono_measure (Measure.restrict_mono (ball_subset_ball hr) le_rfl)
      (Eventually.of_forall fun _ => sq_nonneg _) hi0.integrableOn
  have hsecond : (∫ x in D, ‖G₀ (R x)‖ ^ 2) ≤ ∫ x in W, ‖G₀ x‖ ^ 2 := by
    have he := ((boundaryFrozenReflection_measurePreserving A n hn).restrict_preimage
      (show MeasurableSet W from isOpen_ball.measurableSet)).integral_comp
      R.toHomeomorph.measurableEmbedding (fun x => ‖G₀ x‖ ^ 2)
    calc
      _ ≤ ∫ x in R ⁻¹' W, ‖G₀ (R x)‖ ^ 2 := integral_mono_measure
        (Measure.restrict_mono hmap le_rfl) (Eventually.of_forall fun _ => sq_nonneg _)
        hir.integrableOn
      _ = _ := he
  have hpoint (x) : ‖G₀ x - R.toContinuousLinearMap.adjoint (G₀ (R x))‖ ^ 2 ≤
      2 * ‖G₀ x‖ ^ 2 + 2 * M ^ 2 * ‖G₀ (R x)‖ ^ 2 := by
    have hadj : ‖R.toContinuousLinearMap.adjoint (G₀ (R x))‖ ≤ M * ‖G₀ (R x)‖ := by
      apply (R.toContinuousLinearMap.adjoint.le_opNorm _).trans
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact hbound
    have htri := (norm_sub_le (G₀ x) (R.toContinuousLinearMap.adjoint (G₀ (R x)))).trans
      (add_le_add le_rfl hadj)
    have hs := mul_self_le_mul_self (norm_nonneg _) htri
    nlinarith [sq_nonneg (‖G₀ x‖ - M * ‖G₀ (R x)‖)]
  calc
    _ ≤ ∫ x in D, 2 * ‖G₀ x‖ ^ 2 + 2 * M ^ 2 * ‖G₀ (R x)‖ ^ 2 :=
      integral_mono hib ((hi0.integrableOn.const_mul 2).add
        (hir.integrableOn.const_mul (2 * M ^ 2))) hpoint
    _ = 2 * (∫ x in D, ‖G₀ x‖ ^ 2) + 2 * M ^ 2 * (∫ x in D, ‖G₀ (R x)‖ ^ 2) := by
      rw [integral_add (hi0.integrableOn.const_mul 2)
        (hir.integrableOn.const_mul (2 * M ^ 2)), integral_const_mul, integral_const_mul]
    _ ≤ (2 + 2 * M ^ 2) * (∫ x in W, ‖G₀ x‖ ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hsecond (sq_nonneg M)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (boundary_zero_gradient_energy hf) (by positivity)

end LiquidDrop
