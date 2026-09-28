import NoCompromise.BV.Compactness

/-!
# Indicator clause of local BV compactness on an arbitrary open domain

Blueprint `thm:bv-compactness`, indicator clause, with the approved perimeter
scope: the limit set has locally finite perimeter *in* `U`, meaning finite
perimeter on every open set with compact closure contained in `U`. The
hypotheses only control perimeter inside `U`, so nothing is asserted at its
boundary. On the whole space this is exactly `HasLocallyFinitePerimeter`, and
`bv_compactness_indicators_univ` is recovered.
-/

noncomputable section
open Set MeasureTheory Filter Metric Topology
open scoped ENNReal

namespace LiquidDrop

/-- Local finiteness of perimeter inside an open domain `U`: finite perimeter on
every open set whose closure is compact and contained in `U`. -/
def HasLocallyFinitePerimeterIn {n : ℕ} (E U : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ A : Set (EuclideanSpace ℝ (Fin n)),
    IsOpen A → IsCompact (closure A) → closure A ⊆ U → perimeterIn E A < ∞

theorem hasLocallyFinitePerimeterIn_univ_iff {n : ℕ} (E : Set (EuclideanSpace ℝ (Fin n))) :
    HasLocallyFinitePerimeterIn E univ ↔ HasLocallyFinitePerimeter E := by
  constructor
  · intro h A hA hcA
    exact h A hA hcA (subset_univ _)
  · intro h A hA hcA _
    exact h A hA hcA

theorem HasLocallyFinitePerimeter.hasLocallyFinitePerimeterIn {n : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))} (hE : HasLocallyFinitePerimeter E)
    (U : Set (EuclideanSpace ℝ (Fin n))) : HasLocallyFinitePerimeterIn E U :=
  fun A hA hcA _ => hE A hA hcA

theorem HasLocallyFinitePerimeterIn.isLocallyBVOn_indicator {n : ℕ}
    {E U : Set (EuclideanSpace ℝ (Fin n))} (hE : HasLocallyFinitePerimeterIn E U)
    (hmE : NullMeasurableSet E volume) :
    IsLocallyBVOn (E.indicator (fun _ => (1 : ℝ))) U :=
  ⟨(locallyIntegrable_indicator_one hmE).locallyIntegrableOn U,
    fun A hA hcA hAU => hE A hA hcA hAU⟩

theorem IsLocallyBVOn.hasLocallyFinitePerimeterIn {n : ℕ}
    {E U : Set (EuclideanSpace ℝ (Fin n))}
    (h : IsLocallyBVOn (E.indicator (fun _ => (1 : ℝ))) U) :
    HasLocallyFinitePerimeterIn E U :=
  fun A hA hcA hAU => h.2 A hA hcA hAU

/-- Blueprint `thm:bv-compactness`, indicator clause on an arbitrary open domain.
Indicators of sets with locally finite perimeter in `U`, with uniform L¹ and
perimeter bounds on every relatively compact open subset of `U`, have a
subsequence converging in L¹ on every compact subset of `U` to the indicator of
a Borel set with locally finite perimeter in `U`. -/
theorem bv_compactness_indicators {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (E : ℕ → Set (EuclideanSpace ℝ (Fin n)))
    (hE : ∀ j, HasLocallyFinitePerimeterIn (E j) U)
    (hmE : ∀ j, NullMeasurableSet (E j) volume)
    (hbound : ∀ A : Set (EuclideanSpace ℝ (Fin n)), IsOpen A → IsCompact (closure A) →
      closure A ⊆ U →
      ∃ C : ℝ, ∀ j, (∫ x in A, |(E j).indicator (fun _ => (1 : ℝ)) x|) +
        (perimeterIn (E j) A).toReal ≤ C) :
    ∃ F : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet F ∧ HasLocallyFinitePerimeterIn F U ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ U →
          Tendsto (fun j => ∫ x in K,
            |(E (σ j)).indicator (fun _ => (1 : ℝ)) x - F.indicator (fun _ => (1 : ℝ)) x|)
            atTop (𝓝 0) := by
  let f (j) := (E j).indicator (fun _ => (1 : ℝ))
  have hf (j) : IsLocallyBVOn (f j) U := (hE j).isLocallyBVOn_indicator (hmE j)
  obtain ⟨g, σ, hσ, hg, ht⟩ := bv_compactness hU f hf hbound
  have hval : ∀ᵐ x ∂volume.restrict U, g x = 0 ∨ g x = 1 := by
    have hc := ae_mem_closed_of_locally_l1_convergence hU
      (fun j => (hf (σ j)).1) hg.1 ht
      (isClosed_singleton.union isClosed_singleton : IsClosed ({0, 1} : Set ℝ))
      (fun j => Eventually.of_forall fun x => by
        by_cases hx : x ∈ E (σ j) <;> simp [f, hx])
    simpa only [mem_union, mem_singleton_iff] using hc
  obtain ⟨F, hmF, hF⟩ :=
    exists_measurable_indicator_of_ae_zero_or_one hg.1.aestronglyMeasurable hval
  have hBV := hg.congr_ae hF
  refine ⟨F, hmF, hBV.hasLocallyFinitePerimeterIn, σ, hσ, ?_⟩
  intro K hK hKU
  have heq := hF.filter_mono (ae_mono (Measure.restrict_mono hKU le_rfl))
  convert ht K hK hKU using 1
  ext j
  exact integral_congr_ae ((EventuallyEq.rfl.sub heq.symm).fun_comp abs)

/-- The whole-space theorem is the special case `U = univ`. -/
theorem bv_compactness_indicators_univ' {n : ℕ}
    (E : ℕ → Set (EuclideanSpace ℝ (Fin n)))
    (hE : ∀ j, HasLocallyFinitePerimeter (E j)) (hmE : ∀ j, NullMeasurableSet (E j) volume)
    (hbound : ∀ A : Set (EuclideanSpace ℝ (Fin n)), IsOpen A → IsCompact (closure A) →
      ∃ C : ℝ, ∀ j, (∫ x in A, |(E j).indicator (fun _ => (1 : ℝ)) x|) +
        (perimeterIn (E j) A).toReal ≤ C) :
    ∃ F : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet F ∧ HasLocallyFinitePerimeter F ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
          Tendsto (fun j => ∫ x in K,
            |(E (σ j)).indicator (fun _ => (1 : ℝ)) x - F.indicator (fun _ => (1 : ℝ)) x|)
            atTop (𝓝 0) := by
  obtain ⟨F, hmF, hF, σ, hσ, ht⟩ := bv_compactness_indicators isOpen_univ E
    (fun j => (hE j).hasLocallyFinitePerimeterIn univ) hmE
    (fun A hA hcA _ => hbound A hA hcA)
  exact ⟨F, hmF, (hasLocallyFinitePerimeterIn_univ_iff F).mp hF, σ, hσ,
    fun K hK => ht K hK (subset_univ _)⟩

end LiquidDrop
