import NoCompromise.BV.Basic
import NoCompromise.Measure.PositiveWeakStar

/-!
# Genuine relative perimeter measures and their positive weak compactness

The measure is the one supplied by the proved local distributional polar
theorem. Its open-set values are exactly the original variation supremum.
Everything takes place on the open subtype, allowing infinite mass near the
boundary and infinite global perimeter outside the domain.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology CompactlySupported
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The actual positive perimeter measure on an open domain. -/
def localPerimeterMeasure {n : ℕ} {U F : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hf : IsLocallyBVOn (F.indicator (fun _ => (1 : ℝ))) U) : Measure U :=
  (exists_distributional_polar_representation hU hf).choose

/-- Its genuine distributional polar direction, with the distributional sign. -/
def localPerimeterDirection {n : ℕ} {U F : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hf : IsLocallyBVOn (F.indicator (fun _ => (1 : ℝ))) U) :
    U → EuclideanSpace ℝ (Fin n) :=
  (exists_distributional_polar_representation hU hf).choose_spec.choose

lemma localPerimeterMeasure_data {n : ℕ} {U F : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hf : IsLocallyBVOn (F.indicator (fun _ => (1 : ℝ))) U) :
    (localPerimeterMeasure hU hf).Regular ∧
      IsFiniteMeasureOnCompacts (localPerimeterMeasure hU hf) ∧
      IsDistributionalPolarRepresentation (F.indicator (fun _ => (1 : ℝ))) U
        (localPerimeterMeasure hU hf) (localPerimeterDirection hU hf) :=
  (exists_distributional_polar_representation hU hf).choose_spec.choose_spec

lemma localPerimeterMeasure_open {n : ℕ} {U F O : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hf : IsLocallyBVOn (F.indicator (fun _ => (1 : ℝ))) U)
    (hO : IsOpen O) (hOU : O ⊆ U) :
    localPerimeterMeasure hU hf ((Subtype.val : U → EuclideanSpace ℝ (Fin n)) ⁻¹' O) =
      perimeterIn F O := by
  let : (localPerimeterMeasure hU hf).Regular := (localPerimeterMeasure_data hU hf).1
  exact ((localPerimeterMeasure_data hU hf).2.2.variation_eq_measure hU hO hOU hf.1).symm

/-- The actual local measure is uniquely determined by the open-region perimeters. -/
lemma localPerimeterMeasure_unique {n : ℕ} {U F : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hf : IsLocallyBVOn (F.indicator (fun _ => (1 : ℝ))) U)
    (ρ : Measure U) [ρ.Regular]
    (hρ : ∀ O : Set (EuclideanSpace ℝ (Fin n)), IsOpen O → O ⊆ U →
      ρ ((Subtype.val : U → EuclideanSpace ℝ (Fin n)) ⁻¹' O) = perimeterIn F O) :
    localPerimeterMeasure hU hf = ρ := by
  let : (localPerimeterMeasure hU hf).Regular := (localPerimeterMeasure_data hU hf).1
  apply Measure.OuterRegular.ext_isOpen
  intro V hV
  let O := (Subtype.val : U → EuclideanSpace ℝ (Fin n)) '' V
  have hO : IsOpen O := hU.isOpenEmbedding_subtypeVal.isOpenMap _ hV
  have hOU : O ⊆ U := by rintro _ ⟨z, _, rfl⟩; exact z.property
  have hp : (Subtype.val : U → EuclideanSpace ℝ (Fin n)) ⁻¹' O = V :=
    preimage_image_eq _ Subtype.val_injective
  rw [← hp, localPerimeterMeasure_open hU hf hO hOU, hρ O hO hOU]

/-- Uniform local bounds on the original perimeters give actual positive
weak subsequential compactness on the open domain. -/
theorem exists_subseq_local_perimeter_measure {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {E : ℕ → Set (EuclideanSpace ℝ (Fin n))}
    (hf : ∀ j, IsLocallyBVOn ((E j).indicator (fun _ => (1 : ℝ))) U)
    (hbound : ∀ A : Set (EuclideanSpace ℝ (Fin n)), IsOpen A → IsCompact (closure A) →
      closure A ⊆ U → ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ j, perimeterIn (E j) A ≤ C) :
    ∃ (ρ : Measure U) (σ : ℕ → ℕ), StrictMono σ ∧ ρ.Regular ∧
      IsFiniteMeasureOnCompacts ρ ∧ ∀ φ : C_c(U, ℝ),
        Tendsto (fun j => ∫ z : U, φ z ∂localPerimeterMeasure hU (hf (σ j)))
          atTop (𝓝 (∫ z : U, φ z ∂ρ)) := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let : ∀ j, IsFiniteMeasureOnCompacts (localPerimeterMeasure hU (hf j)) :=
    fun j => (localPerimeterMeasure_data hU (hf j)).2.1
  apply exists_subseq_positive_measure (fun j => localPerimeterMeasure hU (hf j))
  intro K hK
  have hiK : IsCompact ((Subtype.val : U → EuclideanSpace ℝ (Fin n)) '' K) :=
    hK.image continuous_subtype_val
  have hKU : (Subtype.val : U → EuclideanSpace ℝ (Fin n)) '' K ⊆ U := by
    rintro _ ⟨z, _, rfl⟩
    exact z.property
  obtain ⟨A, hA, hKA, hAU, hcA⟩ := exists_open_between_and_isCompact_closure hiK hU hKU
  obtain ⟨C, hC, hb⟩ := hbound A hA hcA hAU
  refine ⟨C.toReal, ENNReal.toReal_nonneg, fun j => ?_⟩
  apply ENNReal.toReal_mono hC.ne
  calc
    _ ≤ localPerimeterMeasure hU (hf j)
        ((Subtype.val : U → EuclideanSpace ℝ (Fin n)) ⁻¹' A) :=
      measure_mono (fun z hz => hKA (mem_image_of_mem _ hz))
    _ = perimeterIn (E j) A := localPerimeterMeasure_open hU (hf j) hA
      (subset_closure.trans hAU)
    _ ≤ C := hb j

end LiquidDrop
