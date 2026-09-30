module

public import NoCompromise.BV.Basic
public import NoCompromise.Measure.BallDifferentiation

@[expose] public section

/-!
# Local BV from genuine distributional densities

Finite sums of locally integrable vector densities define locally BV functions
when their coordinate pairings are the distributional derivatives. No unit-norm
hypothesis is imposed on the densities. This applies to bulk and surface terms.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

/-- Pairing one compact continuous component with a locally integrable density
is integrable, regardless of the total mass of its underlying measure. -/
lemma integrable_coordinate_density_pairing {n : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin n))}
    {σ X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hσ : LocallyIntegrable σ μ) (hX : Continuous X) (hcX : HasCompactSupport X)
    (i : Fin n) : Integrable (fun x => X x i * σ x i) μ := by
  let φ := vectorComponentCC X hX hcX i
  have hi := hσ.integrable_smul_left_of_hasCompactSupport φ.continuous φ.hasCompactSupport
  have hp := (EuclideanSpace.proj (𝕜 := ℝ) i).integrable_comp hi
  simpa only [Function.comp_apply, map_smul, smul_eq_mul] using! hp

/-- Coordinate identities assemble into the divergence identity, including a
finite sum of derivative measures with different underlying measures. -/
theorem integral_divergence_eq_sum_of_coordinate_pairings {n : ℕ} {ι : Type*} [Fintype ι]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : LocallyIntegrable f)
    {μ : ι → Measure (EuclideanSpace ℝ (Fin n))}
    {σ : ι → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hσ : ∀ j, LocallyIntegrable (σ j) (μ j))
    (hpair : ∀ (i : Fin n) (φ : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin n)) ℝ),
      ContDiff ℝ 1 φ → -(∫ x, f x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∑ j, ∫ x, φ x * σ j x i ∂μ j)
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X) :
    -(∫ x, f x * divergenceN X x) = ∑ j, ∫ x, inner ℝ (X x) (σ j x) ∂μ j := by
  classical
  have hi (i : Fin n) := integrable_mul_fderiv_component
    (hf.locallyIntegrableOn univ) hX hcX (subset_univ _) i i
  have ht (i : Fin n) : -(∫ x, f x * fderiv ℝ X x (EuclideanSpace.single i 1) i) =
      ∑ j, ∫ x, X x i * σ j x i ∂μ j := by
    have hφ : ContDiff ℝ 1 (fun x => X x i) :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hX
    have hh := hpair i (vectorComponentCC X hX.continuous hcX i) hφ
    change -(∫ x, f x * fderiv ℝ (fun y => X y i) x (EuclideanSpace.single i 1)) = _ at hh
    simpa only [fderiv_vectorComponent hX] using! hh
  simp only [divergenceN, Finset.mul_sum,
    integral_finsetSum Finset.univ (fun i _ => hi i)]
  rw [← Finset.sum_neg_distrib]
  simp_rw [ht]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← integral_finsetSum Finset.univ
    (fun i _ => integrable_coordinate_density_pairing (hσ j) hX.continuous hcX i)]
  congr 1
  funext x
  simp only [PiLp.inner_apply, Real.inner_apply]

/-- A genuine finite distributional representation bounds variation by the sum
of its density norms on any region. Infinite right-hand sides are permitted. -/
theorem variation_le_sum_lintegral_of_divergence_pairing {n : ℕ} {ι : Type*} [Fintype ι]
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {μ : ι → Measure (EuclideanSpace ℝ (Fin n))}
    {σ : ι → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hpair : ∀ (X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      ContDiff ℝ 1 X → HasCompactSupport X →
      -(∫ x, f x * divergenceN X x) = ∑ j, ∫ x, inner ℝ (X x) (σ j x) ∂μ j)
    (U : Set (EuclideanSpace ℝ (Fin n))) :
    variation f U ≤ ∑ j, ∫⁻ x in U, ‖σ j x‖ₑ ∂μ j := by
  classical
  apply iSup_le
  intro X
  apply iSup_le
  intro hX
  have hl : (∫ x in U, f x * divergenceN X x) = ∫ x, f x * divergenceN X x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [divergenceN_eq_zero_of_notMem_tsupport (fun hz => hx (hX.2.2.1 hz)), mul_zero]
  have hr (j : ι) : (∫ x in U, inner ℝ (X x) (σ j x) ∂μ j) =
      ∫ x, inner ℝ (X x) (σ j x) ∂μ j := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hz => hx (hX.2.2.1 hz)), inner_zero_left]
  rw [hl]
  apply (Real.ofReal_le_enorm _).trans
  rw [← enorm_neg, hpair X hX.1 hX.2.1]
  apply (enorm_sum_le Finset.univ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [← hr j]
  apply (enorm_integral_le_lintegral_enorm _).trans
  apply lintegral_mono
  intro x
  have hb : ‖inner ℝ (X x) (σ j x)‖ ≤ ‖σ j x‖ :=
    (norm_inner_le_norm _ _).trans
      ((mul_le_mul_of_nonneg_right (hX.2.2.2 x) (norm_nonneg _)).trans_eq (one_mul _))
  simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal hb

/-- Locally integrable vector densities in a true coordinate representation
suffice for local BV. In particular, bulk and surface contributions may be
represented by distinct measures. -/
theorem isLocallyBVOn_of_sum_coordinate_pairings {n : ℕ} {ι : Type*} [Fintype ι]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : LocallyIntegrable f)
    {μ : ι → Measure (EuclideanSpace ℝ (Fin n))}
    {σ : ι → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hσ : ∀ j, LocallyIntegrable (σ j) (μ j))
    (hpair : ∀ (i : Fin n) (φ : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin n)) ℝ),
      ContDiff ℝ 1 φ → -(∫ x, f x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∑ j, ∫ x, φ x * σ j x i ∂μ j) : IsLocallyBVOn f univ := by
  classical
  refine ⟨hf.locallyIntegrableOn _, fun A _ hcA _ => ?_⟩
  apply (variation_le_sum_lintegral_of_divergence_pairing
    (fun X hX hcX =>
      integral_divergence_eq_sum_of_coordinate_pairings hf hσ hpair hX hcX) A).trans_lt
  rw [ENNReal.sum_lt_top]
  intro j _
  exact hasFiniteIntegral_iff_enorm.mp
    (((hσ j).integrableOn_isCompact hcA).mono_set subset_closure).hasFiniteIntegral

/-- Every globally locally BV scalar function has an actual ambient polar
measure with the original distributional sign and the correct variation mass. -/
theorem IsLocallyBVOn.exists_ambient_scalar_polar {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsLocallyBVOn f univ) :
    ∃ μ : Measure (EuclideanSpace ℝ (Fin n)),
      ∃ σ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        μ.Regular ∧ IsFiniteMeasureOnCompacts μ ∧ Measurable σ ∧
        (∀ᵐ x ∂μ, ‖σ x‖ = 1) ∧ LocallyIntegrable σ μ ∧
        (∀ (i : Fin n) (φ : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin n)) ℝ),
          ContDiff ℝ 1 φ → -(∫ x, f x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
            ∫ x, φ x * σ x i ∂μ) ∧
        ∀ O, IsOpen O → variation f O = μ O := by
  obtain ⟨ρ, σs, hρ, hp, hv⟩ := exists_polar_representation_with_variation isOpen_univ hf
  let e := Homeomorph.Set.univ (EuclideanSpace ℝ (Fin n))
  let μ := Measure.map e ρ
  let σ := fun x => σs (e.symm x)
  let : ρ.Regular := hρ
  let : μ.Regular := Measure.Regular.map e
  have hm : Measurable σ := hp.measurable.comp e.symm.continuous.measurable
  have hn : ∀ᵐ x ∂μ, ‖σ x‖ = 1 := by
    rw [show μ = Measure.map e ρ from rfl, e.measurableEmbedding.ae_map_iff]
    simpa only [σ, e.symm_apply_apply] using hp.norm_ae
  refine ⟨μ, σ, inferInstance, inferInstance, hm, hn,
    locallyIntegrable_of_ae_norm_le μ hm.aestronglyMeasurable (hn.mono fun _ hx => hx.le), ?_, ?_⟩
  · intro i φ hφ
    rw [show μ = Measure.map e ρ from rfl, e.measurableEmbedding.integral_map]
    simp only [σ, e.symm_apply_apply]
    simpa only [Measure.restrict_univ, e, Homeomorph.Set.univ_apply] using
      hp.test_eq i φ hφ (subset_univ _)
  · intro O hO
    rw [show μ = Measure.map e ρ from rfl,
      Measure.map_apply e.continuous.measurable hO.measurableSet]
    exact hv O hO (subset_univ _)

end LiquidDrop
