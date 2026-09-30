module

public import NoCompromise.Sobolev.H1Approximation

@[expose] public section

/-!
# Mollification of distributional Poisson equations

The source equation is defined by testing the Laplacian against compact smooth
functions. No weak first derivative of the solution is part of the hypotheses.
-/

noncomputable section

open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient Convolution

namespace LiquidDrop

/-- A classical coordinate derivative, using the standard orthonormal basis. -/
def poissonCoordinateDerivative {n : ℕ} (i : Fin n)
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  fderiv ℝ u x (EuclideanSpace.single i 1)

/-- The classical Euclidean Laplacian, as a sum of second coordinate derivatives. -/
def laplacianN {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i, poissonCoordinateDerivative i (poissonCoordinateDerivative i u) x

/-- The distributional equation `Δu = f` on `U`, without an H¹ assumption. -/
structure HasDistributionalLaplacianOn {n : ℕ}
    (u f : EuclideanSpace ℝ (Fin n) → ℝ) (U : Set (EuclideanSpace ℝ (Fin n))) : Prop where
  locallyIntegrable_function : LocallyIntegrableOn u U
  locallyIntegrable_source : LocallyIntegrableOn f U
  test_eq : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ x in U, u x * laplacianN φ x) = ∫ x in U, f x * φ x

lemma poissonCoordinateDerivative_eq_gradient {n : ℕ} (i : Fin n)
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    poissonCoordinateDerivative i u x = gradient u x i :=
  (gradient_apply_eq_fderiv_single u x i).symm

lemma ContDiff.poissonCoordinateDerivative {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {r : WithTop ℕ∞} (hu : ContDiff ℝ (r + 1) u) (i : Fin n) :
    ContDiff ℝ r (poissonCoordinateDerivative i u) := by
  exact (hu.fderiv_right le_rfl).clm_apply contDiff_const

lemma tsupport_poissonCoordinateDerivative_subset {n : ℕ} (i : Fin n)
    (u : EuclideanSpace ℝ (Fin n) → ℝ) :
    tsupport (poissonCoordinateDerivative i u) ⊆ tsupport u := by
  apply closure_minimal _ (isClosed_tsupport u)
  intro x hx
  by_contra hn
  exact hx (by simp [poissonCoordinateDerivative, fderiv_of_notMem_tsupport ℝ hn])

lemma HasCompactSupport.poissonCoordinateDerivative {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : HasCompactSupport u) (i : Fin n) :
    HasCompactSupport (poissonCoordinateDerivative i u) :=
  hu.of_isClosed_subset (isClosed_tsupport _) (tsupport_poissonCoordinateDerivative_subset i u)

lemma poissonCoordinateDerivative_convolution {n : ℕ}
    {u k : EuclideanSpace ℝ (Fin n) → ℝ} (hu : LocallyIntegrable u)
    (hk : ContDiff ℝ 1 k) (hck : HasCompactSupport k) (i : Fin n) :
    poissonCoordinateDerivative i (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] u) =
      poissonCoordinateDerivative i k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] u := by
  funext x
  rw [poissonCoordinateDerivative_eq_gradient, gradient_convolution_left hu hk hck x]
  have hcg : HasCompactSupport (gradient k) :=
    hck.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset k)
  have hi := hcg.convolutionExists_right (μ := volume)
    (ContinuousLinearMap.lsmul ℝ ℝ) hu (continuous_gradient_of_contDiff hk) x
  change Integrable (fun y => u y • gradient k (x - y)) at hi
  rw [eval_integral_piLp hi.eval_piLp, convolution_eq_swap]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    simp [poissonCoordinateDerivative_eq_gradient, mul_comm]

lemma laplacianN_convolution {n : ℕ}
    {u k : EuclideanSpace ℝ (Fin n) → ℝ} (hu : LocallyIntegrable u)
    (hk : ContDiff ℝ 2 k) (hck : HasCompactSupport k)
    (x : EuclideanSpace ℝ (Fin n)) :
    laplacianN (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] u) x =
      ∫ y, u y * laplacianN k (x - y) := by
  classical
  have hki (i : Fin n) : ContDiff ℝ 1 (poissonCoordinateDerivative i k) :=
    ContDiff.poissonCoordinateDerivative (r := 1) hk i
  have hki0 (i : Fin n) :
      Continuous (poissonCoordinateDerivative i (poissonCoordinateDerivative i k)) :=
    (ContDiff.poissonCoordinateDerivative (r := 0) (hki i) i).continuous
  have hi (i : Fin n) : Integrable
      (fun y => u y * poissonCoordinateDerivative i (poissonCoordinateDerivative i k) (x - y)) := by
    have hckii := HasCompactSupport.poissonCoordinateDerivative
      (HasCompactSupport.poissonCoordinateDerivative hck i) i
    have h := hckii.convolutionExists_right
      (μ := volume) (ContinuousLinearMap.lsmul ℝ ℝ) hu (hki0 i) x
    exact h
  simp only [laplacianN, poissonCoordinateDerivative_convolution hu (hk.of_le (by norm_num)) hck,
    poissonCoordinateDerivative_convolution hu (hki _)
      (HasCompactSupport.poissonCoordinateDerivative hck _)]
  simp_rw [convolution_eq_swap, ContinuousLinearMap.lsmul_apply, smul_eq_mul, mul_comm]
  rw [← integral_finsetSum _ (fun i _ => hi i)]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => (Finset.mul_sum _ _ _).symm

lemma poissonCoordinateDerivative_comp_const_sub {n : ℕ}
    {k : EuclideanSpace ℝ (Fin n) → ℝ} (hk : ContDiff ℝ 1 k)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    poissonCoordinateDerivative i (fun y => k (x - y)) =
      fun y => -poissonCoordinateDerivative i k (x - y) := by
  funext y
  exact fderiv_comp_const_sub hk x y _

lemma laplacianN_comp_const_sub {n : ℕ}
    {k : EuclideanSpace ℝ (Fin n) → ℝ} (hk : ContDiff ℝ 2 k)
    (x y : EuclideanSpace ℝ (Fin n)) :
    laplacianN (fun z => k (x - z)) y = laplacianN k (x - y) := by
  classical
  unfold laplacianN
  apply Finset.sum_congr rfl
  intro i _
  rw [poissonCoordinateDerivative_comp_const_sub (hk.of_le (by norm_num))]
  have hki : ContDiff ℝ 1 (poissonCoordinateDerivative i k) :=
    ContDiff.poissonCoordinateDerivative (r := 1) hk i
  change fderiv ℝ (fun z => -poissonCoordinateDerivative i k (x - z)) y _ = _
  rw [fderiv_fun_neg]
  simpa only [neg_apply, neg_neg, poissonCoordinateDerivative] using
    congrArg Neg.neg (fderiv_comp_const_sub hki x y (EuclideanSpace.single i 1))

/-- Interior mollification turns a distributional Poisson equation with L² data
into a pointwise classical equation. No H¹ premise is used. -/
theorem HasDistributionalLaplacianOn.laplacianN_convolution_indicator {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u f k : EuclideanSpace ℝ (Fin n) → ℝ}
    (h : HasDistributionalLaplacianOn u f U)
    (hu : MemLp u 2 (volume.restrict U)) (_hf : MemLp f 2 (volume.restrict U))
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hck : HasCompactSupport k)
    (x : EuclideanSpace ℝ (Fin n)) (hs : tsupport (fun y => k (x - y)) ⊆ U) :
    laplacianN (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] U.indicator u) x =
      (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] U.indicator f) x := by
  have hmu := (memLp_indicator_iff_restrict hU.measurableSet).mpr hu
  have htest := h.test_eq (fun y => k (x - y))
    (hk.comp (contDiff_const.sub contDiff_id))
    (hck.comp_homeomorph (Homeomorph.subLeft x)) hs
  simp_rw [laplacianN_comp_const_sub (hk.of_le (by simp))] at htest
  rw [laplacianN_convolution (hmu.locallyIntegrable (by norm_num))
    (hk.of_le (by simp)) hck x, convolution_eq_swap]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  calc
    _ = ∫ y in U, u y * laplacianN k (x - y) := by
      rw [← integral_indicator hU.measurableSet]
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        by_cases hy : y ∈ U <;> simp [hy]
    _ = ∫ y in U, f y * k (x - y) := htest
    _ = _ := by
      rw [← integral_indicator hU.measurableSet]
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        by_cases hy : y ∈ U <;> simp [hy, mul_comm]

/-- Smooth interior approximations of L² distributional Poisson solutions retain
uniform L² bounds for both their value and their classical Laplacian. -/
theorem HasDistributionalLaplacianOn.bump_convolution_indicator {n : ℕ}
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hV : MeasurableSet V)
    {u f : EuclideanSpace ℝ (Fin n) → ℝ}
    (h : HasDistributionalLaplacianOn u f U)
    (hu : MemLp u 2 (volume.restrict U)) (hf : MemLp f 2 (volume.restrict U))
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)))
    (hs : ∀ x ∈ V, tsupport (fun y => φ.normed volume (x - y)) ⊆ U) :
    ContDiff ℝ (⊤ : ℕ∞)
        (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] U.indicator u) ∧
      (∀ x ∈ V,
        laplacianN (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] U.indicator u) x =
          (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] U.indicator f) x) ∧
      MemLp (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] U.indicator u) 2 volume ∧
      MemLp (laplacianN
        (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] U.indicator u))
        2 (volume.restrict V) ∧
      eLpNorm (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] U.indicator u) 2 volume ≤
        eLpNorm u 2 (volume.restrict U) ∧
      eLpNorm (laplacianN
        (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] U.indicator u))
        2 (volume.restrict V) ≤ eLpNorm f 2 (volume.restrict U) := by
  have hmu := (memLp_indicator_iff_restrict hU.measurableSet).mpr hu
  have hmf := (memLp_indicator_iff_restrict hU.measurableSet).mpr hf
  have hbu := memLp_two_convolution_probability_kernel φ.continuous_normed
    φ.hasCompactSupport_normed φ.nonneg_normed φ.integral_normed hmu
  have hbf := memLp_two_convolution_probability_kernel φ.continuous_normed
    φ.hasCompactSupport_normed φ.nonneg_normed φ.integral_normed hmf
  have heq := fun x hx => h.laplacianN_convolution_indicator hU hu hf
    φ.contDiff_normed φ.hasCompactSupport_normed x (hs x hx)
  have hae : laplacianN
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] U.indicator u) =ᵐ[volume.restrict V]
        (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] U.indicator f) :=
    (ae_restrict_iff' hV).mpr (Eventually.of_forall heq)
  refine ⟨φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed
    (hmu.locallyIntegrable (by norm_num)), heq, hbu.1,
    (hbf.1.mono_measure Measure.restrict_le_self).ae_eq hae.symm, ?_, ?_⟩
  · simpa only [eLpNorm_indicator_eq_eLpNorm_restrict hU.measurableSet] using hbu.2.1
  · rw [eLpNorm_congr_ae hae]
    exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans
      (by simpa only [eLpNorm_indicator_eq_eLpNorm_restrict hU.measurableSet] using hbf.2.1)

/-- Interior smooth approximations converge strongly in L² simultaneously with
 their classical Laplacians. The original solution needs no first weak derivative. -/
theorem HasDistributionalLaplacianOn.tendsto_bump_convolution_indicator {n : ℕ}
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hV : MeasurableSet V)
    (hVU : V ⊆ U) {u f : EuclideanSpace ℝ (Fin n) → ℝ}
    (h : HasDistributionalLaplacianOn u f U)
    (hu : MemLp u 2 (volume.restrict U)) (hf : MemLp f 2 (volume.restrict U))
    (φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin n)))
    (hφ : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0))
    (hs : ∀ j x, x ∈ V → tsupport (fun y => (φ j).normed volume (x - y)) ⊆ U) :
    Tendsto (fun j => eLpNorm
      ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] U.indicator u - u)
      2 (volume.restrict V)) atTop (𝓝 0) ∧
    Tendsto (fun j => eLpNorm
      (laplacianN ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] U.indicator u) - f)
      2 (volume.restrict V)) atTop (𝓝 0) := by
  have ht (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : MemLp g 2 (volume.restrict U)) :
      Tendsto (fun j => eLpNorm
        ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] U.indicator g - g)
        2 (volume.restrict V)) atTop (𝓝 0) := by
    have hg0 := (memLp_indicator_iff_restrict hU.measurableSet).mpr hg
    have hb (j : ℕ) : eLpNorm
        ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] U.indicator g - g)
        2 (volume.restrict V) ≤ eLpNorm
        ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] U.indicator g - U.indicator g)
        2 volume := by
      calc
        _ = eLpNorm
            ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] U.indicator g - U.indicator g)
            2 (volume.restrict V) := by
          apply eLpNorm_congr_ae
          filter_upwards [ae_restrict_mem hV] with x hx
          simp only [Pi.sub_apply, indicator_of_mem (hVU hx)]
        _ ≤ _ := eLpNorm_mono_measure _ Measure.restrict_le_self
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_eLpNorm_bump_convolution_sub hg0 hφ) (fun _ => bot_le) hb
  refine ⟨ht u hu, ?_⟩
  have heq (j : ℕ) : eLpNorm
      (laplacianN ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] U.indicator u) - f)
      2 (volume.restrict V) = eLpNorm
      ((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] U.indicator f - f)
      2 (volume.restrict V) := by
    apply eLpNorm_congr_ae
    filter_upwards [ae_restrict_mem hV] with x hx
    simp only [Pi.sub_apply]
    rw [h.laplacianN_convolution_indicator hU hu hf (φ j).contDiff_normed
      (φ j).hasCompactSupport_normed x (hs j x hx)]
  simpa only [heq] using ht f hf

end LiquidDrop
