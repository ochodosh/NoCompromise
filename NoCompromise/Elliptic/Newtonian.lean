import NoCompromise.Elliptic.NewtonianKernel

/-!
# Newton's equation for bounded densities

The Newtonian potential is the actual integral against inverse distance. Compact
support and boundedness give its pointwise absolute convergence and local
integrability. The singular-kernel identity and an absolutely integrable Fubini
pairing prove `-Δv = 4πf` for arbitrary signed Lebesgue-measurable densities.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The actual Newtonian potential of a scalar density. -/
def scalarNewtonianPotential (f : E₃ → ℝ) (x : E₃) : ℝ :=
  ∫ y, f y / ‖x - y‖

lemma integrable_newtonian_pair {f g : E₃ → ℝ} {B D : ℝ}
    (hf : AEStronglyMeasurable f volume) (hcf : HasCompactSupport f)
    (hB : ∀ x, ‖f x‖ ≤ B) (hg : AEStronglyMeasurable g volume)
    (hcg : HasCompactSupport g) (hD : ∀ x, ‖g x‖ ≤ D) :
    Integrable (fun p : E₃ × E₃ => g p.1 * f p.2 * ‖p.1 - p.2‖⁻¹) := by
  have hB0 : 0 ≤ B := (norm_nonneg (f 0)).trans (hB 0)
  have hD0 : 0 ≤ D := (norm_nonneg (g 0)).trans (hD 0)
  have hs : Function.support (fun p : E₃ × E₃ => g p.1 * f p.2 * ‖p.1 - p.2‖⁻¹) ⊆
      tsupport g ×ˢ tsupport f := by
    intro p hp
    by_contra hn
    simp only [mem_prod, not_and_or] at hn
    rcases hn with hn | hn
    · exact hp (by simp [image_eq_zero_of_notMem_tsupport hn])
    · exact hp (by simp [image_eq_zero_of_notMem_tsupport hn])
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  have hm : AEStronglyMeasurable
      (fun p : E₃ × E₃ => g p.1 * f p.2 * ‖p.1 - p.2‖⁻¹) volume := by
    rw [Measure.volume_eq_prod]
    exact (hg.comp_fst.mul hf.comp_snd).mul
      ((continuous_fst.sub continuous_snd).norm.measurable.inv.aestronglyMeasurable)
  apply ((integrableOn_coulombKernel_prod (tsupport g) (tsupport f)
    hcg.measure_lt_top hcf.measure_lt_top).const_mul (D * B)).mono' hm.restrict
  filter_upwards [] with p
  simp only [norm_mul, norm_inv, norm_norm]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (hD _) (hB _) (norm_nonneg _) hD0) (inv_nonneg.mpr (norm_nonneg _))

lemma integrable_newtonianPotential_integrand {f : E₃ → ℝ} {B : ℝ}
    (hf : AEStronglyMeasurable f volume) (hcf : HasCompactSupport f)
    (hB : ∀ x, ‖f x‖ ≤ B) (x : E₃) :
    Integrable (fun y => f y / ‖x - y‖) := by
  have hs : Function.support (fun y => f y / ‖x - y‖) ⊆ tsupport f := by
    intro y hy
    by_contra hn
    exact hy (by simp [image_eq_zero_of_notMem_tsupport hn])
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  have hk : AEStronglyMeasurable (fun y : E₃ => ‖x - y‖⁻¹) volume := by
    exact ((continuous_const.sub continuous_id).norm.measurable.inv).aestronglyMeasurable
  have hm : AEStronglyMeasurable (fun y : E₃ => f y / ‖x - y‖) volume := by
    convert! hf.mul hk using 1
  apply ((integrableOn_coulombKernel (tsupport f) hcf.measure_lt_top x).const_mul B).mono'
    hm.restrict
  filter_upwards [] with y
  rw [norm_div, norm_norm, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (hB y) (inv_nonneg.mpr (norm_nonneg _))

lemma locallyIntegrable_scalarNewtonianPotential {f : E₃ → ℝ} {B : ℝ}
    (hf : AEStronglyMeasurable f volume) (hcf : HasCompactSupport f)
    (hB : ∀ x, ‖f x‖ ≤ B) : LocallyIntegrable (scalarNewtonianPotential f) := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  let g : E₃ → ℝ := K.indicator (fun _ => 1)
  have hg : AEStronglyMeasurable g volume :=
    (measurable_const.indicator hK.measurableSet).aestronglyMeasurable
  have hcg : HasCompactSupport g := by
    apply hK.of_isClosed_subset (isClosed_tsupport g)
    apply closure_minimal _ hK.isClosed
    exact support_indicator_subset
  have hD : ∀ x, ‖g x‖ ≤ 1 := by
    intro x
    by_cases hx : x ∈ K <;> simp [g, hx]
  have hp := integrable_newtonian_pair hf hcf hB hg hcg hD
  rw [Measure.volume_eq_prod] at hp
  have hi := hp.integral_prod_left
  have he : (fun x => ∫ y, g x * f y * ‖x - y‖⁻¹) =
      K.indicator (scalarNewtonianPotential f) := by
    funext x
    rw [show (fun y => g x * f y * ‖x - y‖⁻¹) =
      (fun y => g x * (f y / ‖x - y‖)) by funext y; simp [div_eq_mul_inv, mul_assoc],
      integral_const_mul]
    by_cases hx : x ∈ K <;> simp [g, hx, scalarNewtonianPotential]
  rw [he] at hi
  exact (integrable_indicator_iff hK.measurableSet).mp hi

lemma integrable_scalarDensity_of_bounded_compact {f : E₃ → ℝ} {B : ℝ}
    (hf : AEStronglyMeasurable f volume) (hcf : HasCompactSupport f)
    (hB : ∀ x, ‖f x‖ ≤ B) : Integrable f := by
  apply (integrableOn_iff_integrable_of_support_subset (subset_tsupport f)).mp
  have : IsFiniteMeasure (volume.restrict (tsupport f)) :=
    ⟨by simpa using hcf.measure_lt_top⟩
  exact (integrable_const B).mono' hf.restrict (Eventually.of_forall hB)

/-- Newton's equation for every bounded Lebesgue-measurable compactly supported
scalar density. Both the potential and the source are genuinely locally integrable. -/
theorem hasDistributionalLaplacianOn_scalarNewtonianPotential {f : E₃ → ℝ} {B : ℝ}
    (hf : AEStronglyMeasurable f volume) (hcf : HasCompactSupport f)
    (hB : ∀ x, ‖f x‖ ≤ B) :
    HasDistributionalLaplacianOn (scalarNewtonianPotential f)
      (fun x => -(4 * Real.pi) * f x) univ := by
  refine ⟨(locallyIntegrable_scalarNewtonianPotential hf hcf hB).locallyIntegrableOn _,
    ((integrable_scalarDensity_of_bounded_compact hf hcf hB).const_mul
      (-(4 * Real.pi))).locallyIntegrable.locallyIntegrableOn _, ?_⟩
  intro φ hφ hcφ _
  simp only [setIntegral_univ]
  have hΔφ := continuous_laplacianN (hφ.of_le (by simp) : ContDiff ℝ 2 φ)
  have hcΔφ : HasCompactSupport (laplacianN φ) :=
    hcφ.of_isClosed_subset (isClosed_tsupport _) (tsupport_laplacianN_subset φ)
  obtain ⟨D, hD⟩ := hcΔφ.exists_bound_of_continuous hΔφ
  have hp := integrable_newtonian_pair hf hcf hB hΔφ.aestronglyMeasurable hcΔφ hD
  rw [Measure.volume_eq_prod] at hp
  calc
    _ = ∫ x, ∫ y, laplacianN φ x * f y * ‖x - y‖⁻¹ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [show (fun y => laplacianN φ x * f y * ‖x - y‖⁻¹) =
        (fun y => (f y / ‖x - y‖) * laplacianN φ x) by funext y; simp only [div_eq_mul_inv]; ring,
        integral_mul_const]
      rfl
    _ = ∫ y, ∫ x, laplacianN φ x * f y * ‖x - y‖⁻¹ := integral_integral_swap hp
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [show (fun x => laplacianN φ x * f y * ‖x - y‖⁻¹) =
        (fun x => f y * (‖x - y‖⁻¹ * laplacianN φ x)) by funext x; ring,
        integral_const_mul, integral_newtonKernel_sub_mul_laplacianN hφ hcφ]
      ring

end LiquidDrop
