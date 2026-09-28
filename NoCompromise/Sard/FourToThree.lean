import NoCompromise.Sard.Slicing
import NoCompromise.Sard.Scalar
import NoCompromise.Measure.WeakDerivativeOne

/-!
# Sard's theorem for C² maps from four to three dimensions

Planar scalar Sard supplies the `2 → 1` base case. Straightening a regular
component and applying Fubini twice handles the nonzero-rank strata. The C²
quadratic estimate handles rank zero in `3 → 2` and `4 → 3`. The final theorem
has exactly the blueprint's C² regularity and no additional Sard premise.
-/

noncomputable section
open MeasureTheory Set Filter Function
open scoped Topology ENNReal
namespace LiquidDrop

/-- A non-surjective linear map to the Euclidean line vanishes after scalar identification. -/
lemma euclideanOneReal_comp_eq_zero_of_not_surjective {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin 1))
    (hL : ¬ Surjective L) :
    euclideanOneReal.toContinuousLinearEquiv.toContinuousLinearMap.comp L = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  change euclideanOneReal (L v) = 0
  by_contra hv
  apply hL
  intro w
  refine ⟨(euclideanOneReal w / euclideanOneReal (L v)) • v, ?_⟩
  apply euclideanOneReal.injective
  simp only [map_smul, smul_eq_mul, div_mul_cancel₀ _ hv]

/-- Planar scalar Sard in the Euclidean-line target convention used by the recursion. -/
theorem hasNullCriticalValuesC2_two_one : HasNullCriticalValuesC2 2 1 := by
  intro U hU f hf
  let g := euclideanOneReal ∘ f
  have hg : ContDiffOn ℝ 2 g U :=
    euclideanOneReal.toContinuousLinearEquiv.contDiff.comp_contDiffOn hf
  have hnull := sard_two_dimensional hU hg
  have hz : volume (euclideanOneReal '' (f '' {x | x ∈ U ∧ ¬ Surjective (fderiv ℝ f x)})) = 0 := by
    apply measure_mono_null ?_ hnull
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x, ⟨hx.1, ?_⟩, rfl⟩
    have hd := euclideanOneReal.toContinuousLinearEquiv.hasFDerivAt.comp x
      ((hf.differentiableOn (by norm_num) x hx.1).differentiableAt
        (hU.mem_nhds hx.1)).hasFDerivAt
    have hdg : HasFDerivAt g
        (euclideanOneReal.toContinuousLinearEquiv.toContinuousLinearMap.comp
          (fderiv ℝ f x)) x := hd
    rw [hdg.fderiv]
    exact euclideanOneReal_comp_eq_zero_of_not_surjective _ hx.2
  rw [← euclideanOneReal.measurePreserving.measure_preimage_emb
    euclideanOneReal.toHomeomorph.measurableEmbedding] at hz
  simpa only [Set.preimage_image_eq _ euclideanOneReal.injective] using hz

/-- The intermediate C² three-to-two critical-value theorem. -/
theorem hasNullCriticalValuesC2_three_two : HasNullCriticalValuesC2 3 2 :=
  hasNullCriticalValuesC2_two_one.succ (by norm_num)

/-- The complete C² four-to-three critical-value assertion. -/
theorem hasNullCriticalValuesC2_four_three : HasNullCriticalValuesC2 4 3 :=
  hasNullCriticalValuesC2_three_two.succ (by norm_num)

/-- Critical values of a C² map `ℝ⁴ → ℝ³` are null, in derivative-surjectivity form. -/
theorem sard_four_to_three_not_surjective
    {U : Set (EuclideanSpace ℝ (Fin 4))} (hU : IsOpen U)
    {F : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 3)}
    (hF : ContDiffOn ℝ 2 F U) :
    volume (F '' {x | x ∈ U ∧ ¬ Surjective (fderiv ℝ F x)}) = 0 :=
  hasNullCriticalValuesC2_four_three U hU F hF

/-- In a finite-dimensional Euclidean target, failure to be onto means deficient rank. -/
lemma finrank_range_lt_iff_not_surjective {n m : ℕ}
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    Module.finrank ℝ L.range < m ↔ ¬ Surjective L := by
  constructor
  · intro h hs
    have hr : L.range = ⊤ := LinearMap.range_eq_top.mpr hs
    have hd := Submodule.eq_top_iff_finrank_eq.mp hr
    rw [finrank_euclideanSpace_fin] at hd
    omega
  · intro h
    have hr : L.range ≠ ⊤ := fun he => h (LinearMap.range_eq_top.mp he)
    simpa only [finrank_euclideanSpace_fin] using Submodule.finrank_lt hr

/-- Blueprint `thm:sard-4to3`: the rank-deficient image of a C² map from an open
subset of four-space to three-space has three-dimensional Lebesgue measure zero. -/
theorem sard_four_to_three
    {U : Set (EuclideanSpace ℝ (Fin 4))} (hU : IsOpen U)
    {F : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 3)}
    (hF : ContDiffOn ℝ 2 F U) :
    volume (F '' {x | x ∈ U ∧ Module.finrank ℝ (fderiv ℝ F x).range < 3}) = 0 := by
  simpa only [finrank_range_lt_iff_not_surjective] using
    sard_four_to_three_not_surjective hU hF

/-- Almost every target value is regular for a C² four-to-three map. -/
theorem ae_regular_values_four_to_three
    {U : Set (EuclideanSpace ℝ (Fin 4))} (hU : IsOpen U)
    {F : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 3)}
    (hF : ContDiffOn ℝ 2 F U) :
    ∀ᵐ z ∂volume, ∀ x ∈ U, F x = z → Surjective (fderiv ℝ F x) := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp
    (sard_four_to_three_not_surjective hU hF)] with z hz
  intro x hx hFx
  by_contra hns
  exact hz ⟨x, ⟨hx, hns⟩, hFx⟩

end LiquidDrop
