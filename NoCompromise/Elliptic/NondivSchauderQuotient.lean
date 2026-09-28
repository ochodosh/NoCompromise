import NoCompromise.Elliptic.NondivSchauderForcing
import NoCompromise.Elliptic.CampanatoHolderDatum

/-!
# Constructed equations for nondivergence difference quotients

The vector datum here is the actual segment integral of the scalar source minus
its discrete coefficient correction. All test identities and L² hypotheses are
proved from C¹,α data; no divergence primitive or second derivative is assumed.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The explicit datum for the quotient in coordinate `i`. -/
def nondivQuotientDatum {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (z f : EuclideanSpace ℝ (Fin n) → ℝ) (i : Fin n) (h : ℝ) :=
  nondivDifferenceForcing
    (campanatoSegmentField (nondivDivergenceSource A b z f) h (EuclideanSpace.single i 1))
    A (gradient z) i h

/-- Uniform Hölder control of the constructed datum, independent of the nonzero
step size. The segment hypothesis is the exact geometric requirement. -/
theorem nondivQuotientDatum_holder {n : ℕ} {α : ℝ} (hα : 0 < α)
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {b : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {z f : EuclideanSpace ℝ (Fin n) → ℝ}
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hA : HasC1HolderOn α A U) (hb : HasFiniteHolderNormOn α b U)
    (hz : HasC1HolderOn α z U) (hf : HasFiniteHolderNormOn α f U)
    (i : Fin n) {h : ℝ} (hh : h ≠ 0)
    (hseg : ∀ x ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, x + t • (h • EuclideanSpace.single i 1) ∈ U) :
    HasFiniteHolderNormOn α (nondivQuotientDatum A b z f i h) V ∧
      holderNorm α (nondivQuotientDatum A b z f i h) V ≤ holderNorm α f U +
        3 * ((n : ℝ) * nondivC1HolderNorm α A U + holderNorm α b U) *
          nondivC1HolderNorm α z U +
        3 * holderNorm α (fderiv ℝ A) U * holderNorm α (gradient z) U := by
  obtain ⟨hg, hgb⟩ := nondivDivergenceSource_holder hA hb hz hf
  obtain ⟨hH, hHb⟩ := campanatoSegmentField_holder
    (hg.nondiv_continuousOn hα) hg h (EuclideanSpace.single i 1) (by simp)
  obtain ⟨hHV, hHVb⟩ := schauder_holder_mono hH hseg
  obtain ⟨hF, hFb⟩ := nondivDifferenceForcing_holder hU hA hz.gradient_holder.1 hHV i hh hseg
  exact ⟨hF, hFb.trans (add_le_add (hHVb.trans (hHb.trans hgb)) le_rfl)⟩

/-- The constructed quotients are genuine H¹ solutions of the differentiated
weak equation. Neither a weak derivative of `Dz` nor an assumed Gh identity is
included among the hypotheses. -/
theorem nondiv_quotient_equation {n : ℕ} {α : ℝ} (hα : 0 < α)
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {b : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {z f : EuclideanSpace ℝ (Fin n) → ℝ}
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hV : IsOpen V)
    (hbU : Bornology.IsBounded U) (hbV : Bornology.IsBounded V)
    (hA : HasC1HolderOn α A U) (hb : HasFiniteHolderNormOn α b U)
    (hz : HasC1HolderOn α z U) (hf : HasFiniteHolderNormOn α f U)
    (he : IsWeakNondivergenceEquationOn A b z f U)
    (i : Fin n) {h : ℝ} (hh : h ≠ 0)
    (hseg : ∀ x ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, x + t • (h • EuclideanSpace.single i 1) ∈ U) :
    HasH1GradientOn (coordinateDifferenceQuotient i h z)
      (coordinateDifferenceQuotient i h (gradient z)) V ∧
    IsWeakDivergenceEquationOn (fun x => A (x + h • EuclideanSpace.single i 1))
      (coordinateDifferenceQuotient i h (gradient z)) (nondivQuotientDatum A b z f i h) V := by
  have hVU : V ⊆ U := by
    intro x hx
    simpa only [zero_smul, add_zero] using hseg x hx 0 (by simp)
  have hmap : ∀ x ∈ V, x + h • EuclideanSpace.single i 1 ∈ U := by
    intro x hx
    simpa only [one_smul] using hseg x hx 1 (by simp)
  have hq := (hz.hasH1GradientOn hU hbU).coordinateDifferenceQuotient
    hU hV hVU i h hmap
  refine ⟨hq, ?_⟩
  obtain ⟨hdiv, hg, -⟩ := he.divergence hα hU hA hb hz hf
  let g := nondivDivergenceSource A b z f
  let H := campanatoSegmentField g h (EuclideanSpace.single i 1)
  have hgc : ContinuousOn g U := hg.nondiv_continuousOn hα
  have hH : HasFiniteHolderNormOn α H V :=
    (schauder_holder_mono
      (campanatoSegmentField_holder hgc hg h (EuclideanSpace.single i 1) (by simp)).1 hseg).1
  have hp : IsWeakScalarDivergenceEquationOn
      (fun _ => ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) H
      (coordinateDifferenceQuotient i h g) V := by
    intro φ hφ hcφ hsφ
    have ht := campanatoSegmentField_distribution hU hgc (hφ.of_le (by simp)) hcφ hh
      (EuclideanSpace.single i 1) (hsφ.trans hseg)
    simpa only [ContinuousLinearMap.id_apply, coordinateDifferenceQuotient,
      smul_eq_mul, div_eq_mul_inv, mul_comm, H] using ht
  have hF := (nondivQuotientDatum_holder hα hU hA hb hz hf i hh hseg).1
  let : IsFiniteMeasure (volume.restrict V) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hbV.measure_lt_top⟩
  have hmF : MemLp (nondivQuotientDatum A b z f i h) 2 (volume.restrict V) := by
    apply MemLp.of_bound
      ((hF.nondiv_continuousOn hα).aestronglyMeasurable hV.measurableSet)
      (holderNorm α (nondivQuotientDatum A b z f i h) V)
    filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
    exact hF.nondiv_norm_le hx
  have hAc : ContinuousOn (fun x => A (x + h • EuclideanSpace.single i 1)) V :=
    hA.contDiff.continuousOn.comp (continuous_id.add continuous_const).continuousOn hmap
  have hmP := campanato_memLp_apply_bounded
    (hAc.aestronglyMeasurable hV.measurableSet) hq.memLp_gradient (Λ := holderNorm α A U)
    (by
      filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
      exact hA.function_holder.nondiv_norm_le (hmap x hx))
  have hm : MemLp (fun x => A (x + h • EuclideanSpace.single i 1)
      (coordinateDifferenceQuotient i h (gradient z) x) -
      nondivDifferenceForcing H A (gradient z) i h x) 2 (volume.restrict V) := by
    simpa only [nondivQuotientDatum, H, g] using! hmP.sub hmF
  exact nondiv_difference_weakDivergenceEquation hdiv hU hV hA.contDiff.continuousOn
    (continuousOn_gradient_of_contDiffOn hU hz.contDiff) hgc (hH.nondiv_continuousOn hα)
    hVU i h hmap hp hm

end LiquidDrop
