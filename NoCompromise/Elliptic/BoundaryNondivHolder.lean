import NoCompromise.Elliptic.BoundaryNondivQuotientBounds

/-!
# Closed-half-ball control of the constructed quotient datum

The extra up-to-the-face hypotheses are explicit C¹,α assumptions on the closed
half ball, including the actual first derivatives in the existing norm convention.
No Hölder bound for a second derivative of the solution is used.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

lemma boundary_nondiv_holder_on_closure {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] {U : Set E}
    {g : E → F} {α H : ℝ} (hα : 0 ≤ α) (hg : ContinuousOn g (closure U))
    (hh : ∀ x ∈ U, ∀ y ∈ U, ‖g x - g y‖ ≤ H * dist x y ^ α) :
    ∀ x ∈ closure U, ∀ y ∈ closure U, ‖g x - g y‖ ≤ H * dist x y ^ α := by
  have hleft : ContinuousOn (fun p : E × E => ‖g p.1 - g p.2‖) (closure (U ×ˢ U)) := by
    rw [closure_prod_eq]
    exact ((hg.comp continuous_fst.continuousOn (fun _ hp => hp.1)).sub
      (hg.comp continuous_snd.continuousOn (fun _ hp => hp.2))).norm
  have hright : Continuous (fun p : E × E => H * dist p.1 p.2 ^ α) :=
    continuous_const.mul ((Real.continuous_rpow_const hα).comp (continuous_fst.dist continuous_snd))
  intro x hx y hy
  exact le_on_closure (fun p hp => hh p.1 hp.1 p.2 hp.2) hleft hright.continuousOn
    (by simpa only [closure_prod_eq] using (show (x, y) ∈ closure U ×ˢ closure U from ⟨hx, hy⟩))

lemma boundary_nondiv_closed_segment {r R h : ℝ} {i : Fin 3}
    (hi : i ≠ Fin.last 2) (hh : |h| ≤ R - r)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ closure (boundaryHalfBall r))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    x + t • (h • EuclideanSpace.single i 1) ∈ closure (boundaryHalfBall R) :=
  (show MapsTo (fun x : EuclideanSpace ℝ (Fin 3) =>
      x + t • (h • EuclideanSpace.single i 1)) (boundaryHalfBall r) (boundaryHalfBall R) from
    fun _ hx => boundary_nondiv_segment_mem_halfBall hi hh hx ht).closure
      (continuous_id.add continuous_const) hx

/-- The explicit segment forcing extends continuously to the flat face under
the stated closed-half-ball C¹,α hypotheses. -/
theorem boundary_nondiv_quotientDatum_continuous {α r h : ℝ} (hα : 0 < α)
    {A : EuclideanSpace ℝ (Fin 3) →
      EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    {b : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {z f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hA : HasC1HolderOn α A (closure (boundaryHalfBall 1)))
    (hb : HasFiniteHolderNormOn α b (closure (boundaryHalfBall 1)))
    (hz : HasC1HolderOn α z (closure (boundaryHalfBall 1)))
    (hf : HasFiniteHolderNormOn α f (closure (boundaryHalfBall 1)))
    {i : Fin 3} (hi : i ≠ Fin.last 2) (hh : |h| ≤ 1 - r) :
    ContinuousOn (nondivQuotientDatum A b z f i h) (closure (boundaryHalfBall r)) := by
  have hseg : ∀ x ∈ closure (boundaryHalfBall r), ∀ t ∈ Icc (0 : ℝ) 1,
      x + t • (h • EuclideanSpace.single i 1) ∈ closure (boundaryHalfBall 1) :=
    fun _ hx _ ht => boundary_nondiv_closed_segment hi hh hx ht
  have hsub : closure (boundaryHalfBall r) ⊆ closure (boundaryHalfBall 1) := by
    intro x hx
    simpa only [zero_smul, add_zero] using hseg x hx 0 (by simp)
  have hmap : MapsTo (fun x => x + h • EuclideanSpace.single i (1 : ℝ))
      (closure (boundaryHalfBall r)) (closure (boundaryHalfBall 1)) := by
    intro x hx
    simpa only [one_smul] using hseg x hx 1 (by simp)
  have hg := (nondivDivergenceSource_holder hA hb hz hf).1
  have hH := (schauder_holder_mono
    (campanatoSegmentField_holder (hg.nondiv_continuousOn hα) hg h
      (EuclideanSpace.single i 1) (by simp)).1 hseg).1.nondiv_continuousOn hα
  have hδA : ContinuousOn (coordinateDifferenceQuotient i h A) (closure (boundaryHalfBall r)) :=
    ((hA.contDiff.continuousOn.comp (continuous_id.add continuous_const).continuousOn hmap).sub
      (hA.contDiff.continuousOn.mono hsub)).const_smul h⁻¹
  exact hH.sub (hδA.clm_apply ((hz.gradient_holder.1.nondiv_continuousOn hα).mono hsub))

/-- Uniform Hölder modulus of the actual quotient datum on the closed smaller
half ball. The norm bound uses only the original solution/source norms. -/
theorem boundary_nondiv_quotientDatum_holder_closed {α M r h : ℝ}
    (hα : 0 < α) (hM : 0 ≤ M)
    {A : EuclideanSpace ℝ (Fin 3) →
      EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    {b : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {z f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hA : HasC1HolderOn α A (closure (boundaryHalfBall 1)))
    (hb : HasFiniteHolderNormOn α b (closure (boundaryHalfBall 1)))
    (hz : HasC1HolderOn α z (closure (boundaryHalfBall 1)))
    (hf : HasFiniteHolderNormOn α f (closure (boundaryHalfBall 1)))
    (hbA : nondivC1HolderNorm α A (closure (boundaryHalfBall 1)) ≤ M)
    (hbb : holderNorm α b (closure (boundaryHalfBall 1)) ≤ M)
    {i : Fin 3} (hi : i ≠ Fin.last 2) (hh : h ≠ 0) (hsmall : |h| ≤ 1 - r) :
    ∀ x ∈ closure (boundaryHalfBall r), ∀ y ∈ closure (boundaryHalfBall r),
      ‖nondivQuotientDatum A b z f i h x - nondivQuotientDatum A b z f i h y‖ ≤
        (1 + 15 * M) * (nondivC1HolderNorm α z (closure (boundaryHalfBall 1)) +
          holderNorm α f (closure (boundaryHalfBall 1))) * dist x y ^ α := by
  obtain ⟨hAo, hbAo⟩ := hA.mono subset_closure
  obtain ⟨hbo, hbbo⟩ := schauder_holder_mono hb subset_closure
  obtain ⟨hzo, hbzo⟩ := hz.mono subset_closure
  obtain ⟨hfo, hbfo⟩ := schauder_holder_mono hf subset_closure
  have hseg : ∀ x ∈ boundaryHalfBall r, ∀ t ∈ Icc (0 : ℝ) 1,
      x + t • (h • EuclideanSpace.single i 1) ∈ boundaryHalfBall 1 :=
    fun _ hx _ ht => boundary_nondiv_segment_mem_halfBall hi hsmall hx ht
  have hreg := (nondivQuotientDatum_holder hα (isOpen_boundaryHalfBall 1)
    hAo hbo hzo hfo i hh hseg).1
  have hbound := nondivQuotientDatum_norm_le hα hM (isOpen_boundaryHalfBall 1)
    hAo hbo hzo hfo (hbAo.trans hbA) (hbbo.trans hbb) i hh hseg
  have hbound' : holderNorm α (nondivQuotientDatum A b z f i h) (boundaryHalfBall r) ≤
      (1 + 15 * M) * (nondivC1HolderNorm α z (closure (boundaryHalfBall 1)) +
        holderNorm α f (closure (boundaryHalfBall 1))) := by
    apply hbound.trans
    norm_num
    exact mul_le_mul_of_nonneg_left (add_le_add hbzo hbfo) (by positivity)
  apply boundary_nondiv_holder_on_closure hα.le
    (boundary_nondiv_quotientDatum_continuous hα hA hb hz hf hi hsmall)
  intro x hx y hy
  have ht := hreg.nondiv_norm_sub_le hx hy
  rw [dist_eq_norm]
  exact ht.trans (mul_le_mul_of_nonneg_right
    ((le_add_of_nonneg_left (holderUniformNorm_nonneg hreg.uniform_bounded)).trans hbound')
      (Real.rpow_nonneg (norm_nonneg _) _))

end LiquidDrop
