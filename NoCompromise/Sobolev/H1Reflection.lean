import NoCompromise.Sobolev.H1Mollification

/-!
# Interior mollification and reflection estimates for H¹ functions

Zero extensions may have a boundary jump. A convolution sees the original weak
gradient exactly when its translated kernel has support inside the domain.
-/

noncomputable section

open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient Convolution

namespace LiquidDrop

set_option maxSynthPendingDepth 8

/-- Interior convolution commutes with the weak gradient of an H¹ function on an
open set. Only the translated kernel, not the zero extension, must stay away from
the boundary; no finite-volume assumption is required. -/
theorem HasH1GradientOn.gradient_convolution_indicator {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f k : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G U) (hk : ContDiff ℝ 1 k) (hck : HasCompactSupport k)
    (x : EuclideanSpace ℝ (Fin n)) (hs : tsupport (fun y => k (x - y)) ⊆ U) :
    gradient (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] U.indicator f) x =
      (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] U.indicator G) x := by
  have hmf := (memLp_indicator_iff_restrict hU.measurableSet).mpr hf.memLp_function
  have hmG := (memLp_indicator_iff_restrict hU.measurableSet).mpr hf.memLp_gradient
  have hif := hmf.locallyIntegrable (by norm_num)
  have hiG := hmG.locallyIntegrable (by norm_num)
  let φ := fun y => k (x - y)
  have hφ : ContDiff ℝ 1 φ := hk.comp (contDiff_const.sub contDiff_id)
  have hcφ : HasCompactSupport φ := hck.comp_homeomorph (Homeomorph.subLeft x)
  have hcgrad : HasCompactSupport (gradient k) :=
    hck.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset k)
  have hiL := hcgrad.convolutionExists_right (μ := volume) (ContinuousLinearMap.lsmul ℝ ℝ)
    hif (continuous_gradient_of_contDiff hk) x
  have hiR := hck.convolutionExists_right (μ := volume)
    (ContinuousLinearMap.lsmul ℝ ℝ).flip hiG hk.continuous x
  change Integrable (fun y => U.indicator f y • gradient k (x - y)) at hiL
  change Integrable (fun y => k (x - y) • U.indicator G y) at hiR
  rw [gradient_convolution_left hif hk hck x, convolution_eq_swap]
  simp only [ContinuousLinearMap.lsmul_apply]
  apply PiLp.ext
  intro i
  rw [eval_integral_piLp hiL.eval_piLp, eval_integral_piLp hiR.eval_piLp]
  have h := hf.test_eq i φ hφ hcφ hs
  have hderiv (y) : fderiv ℝ φ y (EuclideanSpace.single i 1) =
      -gradient k (x - y) i := by
    rw [gradient_apply_eq_fderiv_single]
    exact fderiv_comp_const_sub hk x y _
  simp_rw [hderiv, mul_neg, integral_neg, neg_neg] at h
  simp only [PiLp.smul_apply, smul_eq_mul]
  calc
    _ = ∫ y in U, f y * gradient k (x - y) i := by
      rw [← integral_indicator hU.measurableSet]
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        by_cases hy : y ∈ U <;> simp [hy]
    _ = ∫ y in U, k (x - y) * G y i := h
    _ = _ := by
      rw [← integral_indicator hU.measurableSet]
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        by_cases hy : y ∈ U <;> simp [hy]

/-- A smooth normalized bump gives an H¹ approximation on every open region where
its translated support lies inside the original domain, with uniform L² bounds. -/
theorem HasH1GradientOn.bump_convolution_indicator {n : ℕ}
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hV : IsOpen V)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G U) (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)))
    (hs : ∀ x ∈ V, tsupport (fun y => φ.normed volume (x - y)) ⊆ U) :
    ContDiff ℝ (⊤ : ℕ∞)
        (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] U.indicator f) ∧
      (∀ x ∈ V,
        gradient (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] U.indicator f) x =
          (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] U.indicator G) x) ∧
      HasH1GradientOn (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] U.indicator f)
        (gradient (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] U.indicator f)) V ∧
      eLpNorm (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] U.indicator f) 2 volume ≤
        eLpNorm f 2 (volume.restrict U) ∧
      eLpNorm (gradient (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] U.indicator f))
        2 (volume.restrict V) ≤ eLpNorm G 2 (volume.restrict U) := by
  have hmf := (memLp_indicator_iff_restrict hU.measurableSet).mpr hf.memLp_function
  have hmG := (memLp_indicator_iff_restrict hU.measurableSet).mpr hf.memLp_gradient
  have hbf := memLp_two_convolution_probability_kernel φ.continuous_normed
    φ.hasCompactSupport_normed φ.nonneg_normed φ.integral_normed hmf
  have hbG := memLp_two_convolution_probability_kernel φ.continuous_normed
    φ.hasCompactSupport_normed φ.nonneg_normed φ.integral_normed hmG
  have hcont : ContDiff ℝ (⊤ : ℕ∞)
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] U.indicator f) :=
    φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed
      (hmf.locallyIntegrable (by norm_num))
  have hgrad : ∀ x ∈ V,
      gradient (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] U.indicator f) x =
        (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] U.indicator G) x :=
    fun x hx => hf.gradient_convolution_indicator hU φ.contDiff_normed
      φ.hasCompactSupport_normed x (hs x hx)
  have hgradAE :
      gradient (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] U.indicator f) =ᵐ[
        volume.restrict V]
        (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] U.indicator G) :=
    (ae_restrict_iff' hV.measurableSet).mpr (Eventually.of_forall hgrad)
  refine ⟨hcont, hgrad,
    ⟨hasWeakGradientOn_of_contDiffOn hV (hcont.of_le (by simp)).contDiffOn,
      hbf.1.mono_measure Measure.restrict_le_self,
      (hbG.1.mono_measure Measure.restrict_le_self).ae_eq hgradAE.symm⟩, ?_, ?_⟩
  · simpa only [eLpNorm_indicator_eq_eLpNorm_restrict hU.measurableSet] using hbf.2.1
  · rw [eLpNorm_congr_ae hgradAE]
    exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans
      (by simpa only [eLpNorm_indicator_eq_eLpNorm_restrict hU.measurableSet] using hbG.2.1)

/-- Lᵖ pullback under shifted folding costs at most the two-sheet volume factor. -/
lemma memLp_comp_shiftedCoordinateFold {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    (i : Fin n) (δ : ℝ) {U V : Set (EuclideanSpace ℝ (Fin n))}
    (hU : MeasurableSet U) (hmaps : MapsTo (shiftedCoordinateFold i δ) U V)
    {g : EuclideanSpace ℝ (Fin n) → F} {p : ℝ≥0∞} (hg : MemLp g p (volume.restrict V)) :
    MemLp (g ∘ shiftedCoordinateFold i δ) p (volume.restrict U) ∧
      eLpNorm (g ∘ shiftedCoordinateFold i δ) p (volume.restrict U) ≤
        (2 : ℝ≥0∞) ^ (1 / p).toReal * eLpNorm g p (volume.restrict V) := by
  have hmap := map_volume_restrict_shiftedCoordinateFold_le i δ hU hmaps
  have hm := hg.of_measure_le_smul (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hmap
  have hΦ := (lipschitzWith_shiftedCoordinateFold i δ).continuous.aemeasurable
    (μ := volume.restrict U)
  refine ⟨hm.comp_of_map hΦ, ?_⟩
  rw [← eLpNorm_map_measure hm.aestronglyMeasurable hΦ]
  exact eLpNorm_le_of_measure_le_smul hmap

/-- Smooth functions composed with shifted folding have H¹ norms bounded by the
square root of the two-sheet volume multiplicity, separately for each L² term. -/
theorem hasH1GradientOn_smooth_shiftedCoordinateFold {n : ℕ}
    (i : Fin n) (δ : ℝ) {U V : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hV : IsOpen V)
    (hmaps : MapsTo (shiftedCoordinateFold i δ) U V)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiffOn ℝ 1 g V)
    (hm : MemLp g 2 (volume.restrict V))
    (hmg : MemLp (gradient g) 2 (volume.restrict V)) :
    HasH1GradientOn (g ∘ shiftedCoordinateFold i δ)
      (gradient (g ∘ shiftedCoordinateFold i δ)) U ∧
      eLpNorm (g ∘ shiftedCoordinateFold i δ) 2 (volume.restrict U) ≤
        (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) * eLpNorm g 2 (volume.restrict V) ∧
      eLpNorm (gradient (g ∘ shiftedCoordinateFold i δ)) 2 (volume.restrict U) ≤
        (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) * eLpNorm (gradient g) 2 (volume.restrict V) := by
  have hmf := memLp_comp_shiftedCoordinateFold i δ hU.measurableSet hmaps hm
  have hmG := memLp_comp_shiftedCoordinateFold i δ hU.measurableSet hmaps hmg
  have hlip := (lipschitzWith_shiftedCoordinateFold i δ).lipschitzOnWith (s := U)
  have hbound := ae_norm_gradient_comp_le hU hV hg hlip hmaps
  simp only [NNReal.coe_one, one_mul] at hbound
  refine ⟨⟨hasWeakGradientOn_comp_of_contDiffOn hU hV hg hlip hmaps, hmf.1,
    hmG.1.of_le (measurable_gradient _).aestronglyMeasurable hbound⟩, ?_, ?_⟩
  · simpa only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] using hmf.2
  · exact (eLpNorm_mono_ae (measurable_gradient _).aestronglyMeasurable hbound).trans
      (by simpa only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat,
        Function.comp_def] using hmG.2)

/-- A bump translated to a point with enough coordinate clearance has its entire
support inside the upper half-cube. -/
lemma tsupport_bump_translate_subset_halfCube {n : ℕ} (i : Fin n) {R : ℝ}
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)))
    {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ coordinateCube n (R - φ.rOut)) (hxi : φ.rOut < x i) :
    tsupport (fun y => φ.normed volume (x - y)) ⊆ coordinateHalfCube i R := by
  intro y hy
  have hxy : ‖x - y‖ ≤ φ.rOut := by
    have h := tsupport_comp_subset_preimage (φ.normed volume)
      (continuous_const.sub continuous_id) hy
    simpa only [ContDiffBump.tsupport_normed_eq, mem_preimage, mem_closedBall,
      dist_zero_right, Pi.sub_apply, id_eq] using h
  have hcoord (j : Fin n) : |x j - y j| ≤ φ.rOut := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using
      (PiLp.norm_apply_le (x - y) j).trans hxy
  constructor
  · intro j
    calc
      |y j| ≤ |x j| + |x j - y j| := by
        have h := abs_add_le (y j - x j) (x j)
        rw [sub_add_cancel, abs_sub_comm] at h
        simpa only [add_comm] using h
      _ ≤ |x j| + φ.rOut := add_le_add le_rfl (hcoord j)
      _ < R := by linarith [hx j]
  · have h := (abs_le.mp (hcoord i)).2
    change 0 < y i
    linarith

/-- Smooth interior mollification followed by shifted even reflection has uniform
H¹ bounds on the smaller cube. The radius and shift assumptions explicitly keep
every convolution kernel inside the original upper half-cube. -/
theorem HasH1GradientOn.bump_convolution_shiftedCoordinateFold {n : ℕ}
    (i : Fin n) {r R δ : ℝ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G (coordinateHalfCube i R))
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)))
    (hδ : φ.rOut < δ) (hR : r + δ + φ.rOut ≤ R) :
    let g := (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ]
      (coordinateHalfCube i R).indicator f) ∘ shiftedCoordinateFold i δ
    HasH1GradientOn g (gradient g) (coordinateCube n r) ∧
      eLpNorm g 2 (volume.restrict (coordinateCube n r)) ≤
        (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) * eLpNorm f 2
          (volume.restrict (coordinateHalfCube i R)) ∧
      eLpNorm (gradient g) 2 (volume.restrict (coordinateCube n r)) ≤
        (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) * eLpNorm G 2
          (volume.restrict (coordinateHalfCube i R)) := by
  let V := coordinateCube n (R - φ.rOut) ∩ {x | φ.rOut < x i}
  have hV : IsOpen V := (isOpen_coordinateCube n _).inter
    (isOpen_lt continuous_const (EuclideanSpace.proj i).continuous)
  have hmaps : MapsTo (shiftedCoordinateFold i δ) (coordinateCube n r) V := by
    intro x hx
    refine ⟨(mapsTo_shiftedCoordinateFold_halfCube i
      (φ.rOut_pos.trans hδ) (by linarith) hx).1, ?_⟩
    simp only [mem_ofPred_eq, shiftedCoordinateFold_apply, ite_true]
    linarith [abs_nonneg (x i)]
  have hs : ∀ x ∈ V, tsupport (fun y => φ.normed volume (x - y)) ⊆
      coordinateHalfCube i R := fun x hx =>
    tsupport_bump_translate_subset_halfCube i φ hx.1 hx.2
  have hlocal := hf.bump_convolution_indicator (isOpen_coordinateHalfCube i R) hV φ hs
  have hfold := hasH1GradientOn_smooth_shiftedCoordinateFold i δ
    (isOpen_coordinateCube n r) hV hmaps (hlocal.1.of_le (by simp)).contDiffOn
    hlocal.2.2.1.memLp_function hlocal.2.2.1.memLp_gradient
  refine ⟨hfold.1, hfold.2.1.trans ?_, hfold.2.2.trans ?_⟩
  · gcongr
    exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans hlocal.2.2.2.1
  · gcongr
    exact hlocal.2.2.2.2

end LiquidDrop
