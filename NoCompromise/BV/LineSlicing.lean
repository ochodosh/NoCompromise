module

public import NoCompromise.BV.CoareaApproximation
public import NoCompromise.BV.CoareaCoordinates
public import NoCompromise.Measure.WeakDerivativeOne
public import NoCompromise.BV.Algebra

@[expose] public section

/-!
# Distributional BV on coordinate lines

Strict approximation, a common almost-everywhere L1 subsequence, lower
semicontinuity and Fatou prove the integral bound for variations of global BV
slices. Compact cutoffs then give locally BV restrictions of locally BV
functions, including Lebesgue-measurable finite-perimeter indicators.

The line variable is one-dimensional Euclidean space and the horizontal variable
has arbitrary dimension. These are distributional, almost-everywhere statements;
no jump claim is made about arbitrary pointwise representatives. The derivative
measure disintegration and the finite-jump representative are separate steps.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Split off the final coordinate as a one-dimensional Euclidean factor. -/
def lineCoordinateEquiv (n : ℕ) : EuclideanSpace ℝ (Fin (n + 1)) ≃ᵐ
    EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1) :=
  (euclideanLastEquiv n).toHomeomorph.toMeasurableEquiv.trans
    ((euclideanOneReal.symm.toHomeomorph.toMeasurableEquiv.prodCongr
      (MeasurableEquiv.refl _)).trans MeasurableEquiv.prodComm)

@[simp] lemma lineCoordinateEquiv_symm_apply {n : ℕ}
    (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1)) :
    (lineCoordinateEquiv n).symm p = graphAppendN p.1 (p.2 0) := rfl

lemma lineCoordinateEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (lineCoordinateEquiv n) volume (volume.prod volume) := by
  exact Measure.measurePreserving_swap.comp
    (((euclideanOneReal.symm.measurePreserving).prod (MeasurePreserving.id volume)).comp
      (euclideanLastEquiv_measurePreserving n))

/-- The actual restriction to a line, with almost-everywhere properties proved below. -/
def lineSlice {n : ℕ} (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin 1) → ℝ :=
  fun t => f (graphAppendN x (t 0))

lemma lintegral_lineSlice {n : ℕ} {q : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞}
    (hq : AEMeasurable q volume) :
    (∫⁻ x : EuclideanSpace ℝ (Fin n), ∫⁻ t : EuclideanSpace ℝ (Fin 1),
      q (graphAppendN x (t 0))) = ∫⁻ z, q z := by
  let e := lineCoordinateEquiv n
  have hp := (lineCoordinateEquiv_measurePreserving n).symm e
  have hm := hq.comp_quasiMeasurePreserving hp.quasiMeasurePreserving
  change (∫⁻ x, ∫⁻ t, (q ∘ e.symm) (x, t)) = _
  rw [← lintegral_prod _ hm]
  exact hp.lintegral_comp_emb e.symm.measurableEmbedding q

lemma ae_integrable_lineSlice {n : ℕ} {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hf : Integrable f volume) : ∀ᵐ x, Integrable (lineSlice f x) volume := by
  have hp := (lineCoordinateEquiv_measurePreserving n).symm (lineCoordinateEquiv n)
  have hi := (hp.integrable_comp hf.aestronglyMeasurable).mpr hf
  exact hi.prod_right_ae

lemma contDiff_lineSlice {n : ℕ} {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    {r : WithTop ℕ∞} (hf : ContDiff ℝ r f) (x : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ r (lineSlice f x) := by
  have ht : ContDiff ℝ r (fun t : EuclideanSpace ℝ (Fin 1) => t 0) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).contDiff
  exact hf.comp (contDiff_const.add (ht.smul contDiff_const))

lemma gradient_lineSlice {n : ℕ} {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hf : ContDiff ℝ 1 f) (x : EuclideanSpace ℝ (Fin n))
    (t : EuclideanSpace ℝ (Fin 1)) :
    gradient (lineSlice f x) t 0 = gradient f (graphAppendN x (t 0)) (Fin.last n) := by
  let L : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    (EuclideanSpace.proj 0).smulRight (EuclideanSpace.single (Fin.last n) 1)
  have hp : HasFDerivAt (fun t : EuclideanSpace ℝ (Fin 1) => graphAppendN x (t 0)) L t :=
    L.hasFDerivAt.const_add (graphBaseN n x)
  have hd := (hf.differentiable one_ne_zero _).hasFDerivAt.comp t hp
  rw [gradient_apply_eq_fderiv_single, gradient_apply_eq_fderiv_single]
  rw [show fderiv ℝ (lineSlice f x) t = (fderiv ℝ f (graphAppendN x (t 0))).comp L
    from hd.fderiv]
  simp [L]

lemma norm_gradient_lineSlice_le {n : ℕ} {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hf : ContDiff ℝ 1 f) (x : EuclideanSpace ℝ (Fin n))
    (t : EuclideanSpace ℝ (Fin 1)) :
    ‖gradient (lineSlice f x) t‖ ≤ ‖gradient f (graphAppendN x (t 0))‖ := by
  rw [← euclideanOneReal.norm_map (gradient (lineSlice f x) t), euclideanOneReal_apply,
    gradient_lineSlice hf]
  exact PiLp.norm_apply_le _ _

/-- One common subsequence converges in L1 on almost every coordinate line. -/
lemma exists_subseq_lineSlice_l1 {n : ℕ}
    {f : ℕ → EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    {g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hi : ∀ j, Integrable (fun z => f j z - g z) volume)
    (ht : Tendsto (fun j => ∫ z, |f j z - g z|) atTop (𝓝 0)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ᵐ x : EuclideanSpace ℝ (Fin n),
      Tendsto (fun j => ∫⁻ t : EuclideanSpace ℝ (Fin 1),
        ENNReal.ofReal |lineSlice (f (σ j)) x t - lineSlice g x t|) atTop (𝓝 0) := by
  let e := lineCoordinateEquiv n
  have hp := (lineCoordinateEquiv_measurePreserving n).symm e
  have hm (j) : AEMeasurable (fun p : EuclideanSpace ℝ (Fin n) ×
      EuclideanSpace ℝ (Fin 1) => ENNReal.ofReal
        |lineSlice (f j) p.1 p.2 - lineSlice g p.1 p.2|) (volume.prod volume) :=
    ((hi j).abs.aestronglyMeasurable.aemeasurable.ennreal_ofReal).comp_quasiMeasurePreserving
      hp.quasiMeasurePreserving
  have heq (j) : (∫⁻ x : EuclideanSpace ℝ (Fin n), ∫⁻ t : EuclideanSpace ℝ (Fin 1),
      ENNReal.ofReal |lineSlice (f j) x t - lineSlice g x t|) =
        ENNReal.ofReal (∫ z, |f j z - g z|) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hi j).abs (ae_of_all _ fun _ => abs_nonneg _)]
    exact lintegral_lineSlice ((hi j).abs.aestronglyMeasurable.aemeasurable.ennreal_ofReal)
  apply exists_subseq_ae_tendsto_zero_of_lintegral (fun j => (hm j).lintegral_prod_right')
  · intro j
    rw [heq]
    exact ENNReal.ofReal_lt_top
  · simpa only [heq, Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht

/-- Global BV functions have BV slices in the last coordinate. The integral of
slice variations is bounded by the full ambient variation. -/
theorem IsBVOn.ae_lineSlice_and_lintegral_variation_le {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsBVOn f univ) :
    (∀ᵐ x : EuclideanSpace ℝ (Fin n), IsBVOn (lineSlice f x) univ) ∧
      (∫⁻ x : EuclideanSpace ℝ (Fin n), variation (lineSlice f x) univ) ≤
        variation f univ := by
  obtain ⟨g, hg, hconv, hgrad⟩ := strict_approximation_univ hf
  have hif : Integrable f volume := integrableOn_univ.mp hf.1
  obtain ⟨σ, hσ, hlines⟩ := exists_subseq_lineSlice_l1
    (fun j => (hg j).2.2.1.sub hif) (by simpa only [Real.norm_eq_abs] using hconv)
  let e := lineCoordinateEquiv n
  have hp := (lineCoordinateEquiv_measurePreserving n).symm e
  let q : ℕ → EuclideanSpace ℝ (Fin n) → ℝ≥0∞ := fun j x =>
    ∫⁻ t : EuclideanSpace ℝ (Fin 1),
      ENNReal.ofReal ‖gradient (g (σ j)) (graphAppendN x (t 0))‖
  have hqm (j) : Measurable (q j) := by
    have hc := continuous_gradient_of_contDiff ((hg (σ j)).1.of_le (by simp))
    have hm := (hc.norm.measurable.ennreal_ofReal).comp e.symm.measurable
    exact hm.lintegral_prod_right'
  have hqint (j) : (∫⁻ x, q j x) =
      ENNReal.ofReal (∫ z, ‖gradient (g (σ j)) z‖) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hg (σ j)).2.2.2.norm
      (ae_of_all _ fun _ => norm_nonneg _)]
    exact lintegral_lineSlice
      ((hg (σ j)).2.2.2.norm.aestronglyMeasurable.aemeasurable.ennreal_ofReal)
  have hqlim : Tendsto (fun j => ∫⁻ x, q j x) atTop (𝓝 (variation f univ)) := by
    simpa only [hqint, Function.comp_def, ENNReal.ofReal_toReal hf.2.ne] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hgrad.comp hσ.tendsto_atTop)
  have hfatou : (∫⁻ x, liminf (fun j => q j x) atTop) ≤ variation f univ :=
    (lintegral_liminf_le hqm).trans_eq hqlim.liminf_eq
  have hfull (j) : ∀ᵐ x : EuclideanSpace ℝ (Fin n), Integrable
      (fun t : EuclideanSpace ℝ (Fin 1) =>
        ‖gradient (g (σ j)) (graphAppendN x (t 0))‖) volume := by
    have hi := (hp.integrable_comp (hg (σ j)).2.2.2.norm.aestronglyMeasurable).mpr
      (hg (σ j)).2.2.2.norm
    exact hi.prod_right_ae
  have hbound : ∀ᵐ x : EuclideanSpace ℝ (Fin n),
      variation (lineSlice f x) univ ≤ liminf (fun j => q j x) atTop := by
    filter_upwards [hlines, ae_integrable_lineSlice hif, ae_all_iff.mpr hfull] with x hx hxi hxg
    have hcs (j) : ContDiff ℝ 1 (lineSlice (g (σ j)) x) :=
      contDiff_lineSlice ((hg (σ j)).1.of_le (by simp)) x
    have hgi (j) : Integrable (gradient (lineSlice (g (σ j)) x)) volume := by
      apply (hxg j).mono'
        (continuous_gradient_of_contDiff (hcs j)).aestronglyMeasurable
      exact ae_of_all _ fun t => norm_gradient_lineSlice_le
        ((hg (σ j)).1.of_le (by simp)) x t
    have hqbound (j) : variation (lineSlice (g (σ j)) x) univ ≤ q j x := by
      apply (variation_le_integral_norm_gradient (hcs j) (hgi j)).trans
      dsimp only [q]
      rw [← ofReal_integral_eq_lintegral_ofReal (hxg j)
        (ae_of_all _ fun _ => norm_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      apply integral_mono (hgi j).norm (hxg j)
      exact fun t => norm_gradient_lineSlice_le ((hg (σ j)).1.of_le (by simp)) x t
    have hlocg (j) : LocallyIntegrableOn (lineSlice (g (σ j)) x) univ :=
      (hcs j).continuous.locallyIntegrable.locallyIntegrableOn _
    have hlocf := hxi.locallyIntegrable.locallyIntegrableOn univ
    apply (variation_le_liminf_of_locally_l1 isOpen_univ hlocg hlocf
      (fun K hK hKU => tendsto_integral_abs_on_compact_of_lintegral
        hlocg hlocf (by simpa only [Measure.restrict_univ] using hx) hK hKU)).trans
    exact liminf_le_liminf (Eventually.of_forall hqbound)
  have hfinite : ∀ᵐ x : EuclideanSpace ℝ (Fin n), liminf (fun j => q j x) atTop < ∞ :=
    ae_lt_top' (Measurable.liminf hqm).aemeasurable (hfatou.trans_lt hf.2).ne
  refine ⟨?_, (lintegral_mono_ae hbound).trans hfatou⟩
  filter_upwards [ae_integrable_lineSlice hif, hbound, hfinite] with x hx hb hfin
  exact ⟨hx.integrableOn, hb.trans_lt hfin⟩

/-- Locally BV functions have locally BV restrictions on almost every coordinate line. -/
theorem IsLocallyBVOn.ae_lineSlice {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsLocallyBVOn f univ) :
    ∀ᵐ x : EuclideanSpace ℝ (Fin n), IsLocallyBVOn (lineSlice f x) univ := by
  let κ (j : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin (n + 1))) :=
    ⟨(j : ℝ) + 1, (j : ℝ) + 2, by positivity, by linarith⟩
  let g (j : ℕ) (z : EuclideanSpace ℝ (Fin (n + 1))) := κ j z * f z
  have hgv (j) : IsBVOn (g j) univ := hf.isBVOn_mul_compact_factor isOpen_univ
    (κ j).contDiff (κ j).hasCompactSupport (subset_univ _)
  have hgs : ∀ᵐ x : EuclideanSpace ℝ (Fin n), ∀ j, IsBVOn (lineSlice (g j) x) univ :=
    ae_all_iff.mpr fun j => (hgv j).ae_lineSlice_and_lintegral_variation_le.1
  filter_upwards [hgs] with x hx
  have heq : ∀ K : Set (EuclideanSpace ℝ (Fin 1)), IsCompact K →
      ∃ j, EqOn (lineSlice (g j) x) (lineSlice f x) K := by
    intro K hK
    have hc : Continuous (fun t : EuclideanSpace ℝ (Fin 1) => graphAppendN x (t 0)) := by
      unfold graphAppendN
      exact continuous_const.add ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).continuous.smul
        continuous_const)
    obtain ⟨R, hR⟩ := (hK.image hc).isBounded.subset_closedBall 0
    obtain ⟨j, hj⟩ := exists_nat_gt R
    refine ⟨j, fun t ht => ?_⟩
    have hmem : graphAppendN x (t 0) ∈ closedBall 0 (κ j).rIn := by
      apply closedBall_subset_closedBall (show R ≤ (κ j).rIn by dsimp [κ]; linarith)
      exact hR (mem_image_of_mem _ ht)
    simp only [lineSlice, g, (κ j).one_of_mem_closedBall hmem, one_mul]
  have hlocal : LocallyIntegrable (lineSlice f x) volume := by
    apply locallyIntegrable_iff.mpr
    intro K hK
    obtain ⟨j, hj⟩ := heq K hK
    exact ((integrableOn_univ.mp (hx j).1).integrableOn).congr_fun hj hK.measurableSet
  refine ⟨hlocal.locallyIntegrableOn _, fun A hA hcA _ => ?_⟩
  obtain ⟨j, hj⟩ := heq (closure A) hcA
  have hv := (hx j).mono MeasurableSet.univ (subset_univ A)
  have ha : lineSlice (g j) x =ᵐ[volume.restrict A] lineSlice f x := by
    filter_upwards [ae_restrict_mem hA.measurableSet] with t ht
    exact hj (subset_closure ht)
  rw [← variation_congr_ae A ha]
  exact hv.2

/-- Lebesgue-measurable locally finite-perimeter sets have distributionally locally
BV indicator slices. No assertion concerns an arbitrary pointwise jump convention. -/
theorem HasLocallyFinitePerimeter.ae_lineSlice_indicator {n : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) :
    ∀ᵐ x : EuclideanSpace ℝ (Fin n),
      IsLocallyBVOn (lineSlice (E.indicator (fun _ => (1 : ℝ))) x) univ :=
  (hE.isLocallyBVOn_indicator hmE univ).ae_lineSlice

end LiquidDrop
