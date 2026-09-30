module

public import NoCompromise.BV.FlatCut
public import NoCompromise.BV.ScalarDistribution

@[expose] public section

/-!
# The derivative measure and BV regularity of a flat cut

The actual one-sided trace is the surface density in the distributional
identity. A finite-family reconstruction theorem then proves local BV of the
cut, using the original scalar BV polar rather than assuming a cut derivative.
-/

noncomputable section
open MeasureTheory Filter Set Metric Topology
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma isClosedEmbedding_graphAppendN (n : ℕ) (a : ℝ) :
    IsClosedEmbedding (fun x : EuclideanSpace ℝ (Fin n) => graphAppendN x a) := by
  have hp : IsClosedEmbedding (fun x : EuclideanSpace ℝ (Fin n) => (x, a)) :=
    .of_isEmbedding_isClosedMap (isEmbedding_prodMkLeft a) (isClosedMap_prodMk_right a)
  exact (realLineCoordinates n).isClosedEmbedding.comp hp

/-- Euclidean area on a flat interface, in tangential coordinates. -/
def flatHyperplaneMeasure (n : ℕ) (a : ℝ) : Measure (EuclideanSpace ℝ (Fin (n + 1))) :=
  Measure.map (fun x : EuclideanSpace ℝ (Fin n) => graphAppendN x a) volume

instance flatHyperplaneMeasure_finiteOnCompacts (n : ℕ) (a : ℝ) :
    IsFiniteMeasureOnCompacts (flatHyperplaneMeasure n a) := by
  refine ⟨fun K hK => ?_⟩
  rw [flatHyperplaneMeasure, Measure.map_apply
    (isClosedEmbedding_graphAppendN n a).continuous.measurable hK.measurableSet]
  exact ((isClosedEmbedding_graphAppendN n a).isProperMap.isCompact_preimage hK).measure_lt_top

instance flatHyperplaneMeasure_regular (n : ℕ) (a : ℝ) :
    (flatHyperplaneMeasure n a).Regular := inferInstance

lemma locallyIntegrable_flatHyperplane_of_comp {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    {T : EuclideanSpace ℝ (Fin (n + 1)) → F} {a : ℝ}
    (hT : LocallyIntegrable (fun x => T (graphAppendN x a)) volume) :
    LocallyIntegrable T (flatHyperplaneMeasure n a) := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  have he := isClosedEmbedding_graphAppendN n a
  rw [flatHyperplaneMeasure, he.measurableEmbedding.integrableOn_map_iff]
  exact hT.integrableOn_isCompact (he.isProperMap.isCompact_preimage hK)

/-- The signed boundary derivative of the lower-halfspace cut. -/
def flatCutSurfaceDensity {n : ℕ} (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (a : ℝ) (z : EuclideanSpace ℝ (Fin (n + 1))) : EuclideanSpace ℝ (Fin (n + 1)) :=
  -flatBVLeftTrace f a (graphProjectionN n z) • EuclideanSpace.single (Fin.last n) 1

lemma IsLocallyBVOn.locallyIntegrable_flatCutSurfaceDensity {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsLocallyBVOn f univ) (a : ℝ) :
    LocallyIntegrable (flatCutSurfaceDensity f a) (flatHyperplaneMeasure n a) := by
  apply locallyIntegrable_flatHyperplane_of_comp
  simpa only [flatCutSurfaceDensity, graphProjectionN_append, Pi.neg_apply] using!
    (hf.locallyIntegrable_flatBVLeftTrace a).neg.smul_continuous
      (continuous_const : Continuous (fun _ : EuclideanSpace ℝ (Fin n) =>
        EuclideanSpace.single (Fin.last n) (1 : ℝ)))

lemma locallyIntegrable_scalar_component {n : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin n))}
    {σ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hσ : LocallyIntegrable σ μ) (i : Fin n) : LocallyIntegrable (fun x => σ x i) μ := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  simpa only [Function.comp_def] using!
    (EuclideanSpace.proj (𝕜 := ℝ) i).integrable_comp (hσ.integrableOn_isCompact hK)

/-- The exact bulk-plus-surface coordinate measure identity for a flat cut. -/
theorem IsLocallyBVOn.flat_cut_coordinate_measure_pairing {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsLocallyBVOn f univ)
    {μ : Measure (EuclideanSpace ℝ (Fin (n + 1)))}
    {σ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hσ : LocallyIntegrable σ μ)
    (hpair : ∀ (i : Fin (n + 1))
      (φ : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin (n + 1))) ℝ),
      ContDiff ℝ 1 φ → -(∫ z, f z * fderiv ℝ φ z (EuclideanSpace.single i 1)) =
        ∫ z, φ z * σ z i ∂μ)
    (a : ℝ) (i : Fin (n + 1))
    (φ : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin (n + 1))) ℝ)
    (hφ : ContDiff ℝ 1 φ) :
    -(∫ z, ({z | z (Fin.last n) < a}.indicator f) z *
      fderiv ℝ φ z (EuclideanSpace.single i 1)) =
      (∫ z in {z | z (Fin.last n) < a}, φ z * σ z i ∂μ) +
      ∫ z, φ z * flatCutSurfaceDensity f a z i ∂flatHyperplaneMeasure n a := by
  classical
  have hH : MeasurableSet {z : EuclideanSpace ℝ (Fin (n + 1)) | z (Fin.last n) < a} :=
    measurableSet_lt (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last n)).measurable measurable_const
  have ht := hf.flat_cut_directional_pairing (locallyIntegrable_scalar_component hσ i)
    (EuclideanSpace.single i 1)
    (fun ψ hψ hcψ => hpair i ⟨⟨ψ, hψ.continuous⟩, hcψ⟩ hψ) hφ φ.hasCompactSupport a
  have hleft : (∫ z, ({z | z (Fin.last n) < a}.indicator f) z *
      fderiv ℝ φ z (EuclideanSpace.single i 1)) =
      ∫ z in {z | z (Fin.last n) < a}, f z * fderiv ℝ φ z (EuclideanSpace.single i 1) := by
    rw [← integral_indicator hH]
    apply integral_congr_ae
    exact ae_of_all _ fun z => by by_cases hz : z (Fin.last n) < a <;> simp [hz]
  rw [hleft, ht, flatHyperplaneMeasure,
    (isClosedEmbedding_graphAppendN n a).measurableEmbedding.integral_map]
  have hs : (∫ x : EuclideanSpace ℝ (Fin n), φ (graphAppendN x a) *
      flatCutSurfaceDensity f a (graphAppendN x a) i) =
      -(EuclideanSpace.single i (1 : ℝ) (Fin.last n)) *
        ∫ x, φ (graphAppendN x a) * flatBVLeftTrace f a x := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      simp only [flatCutSurfaceDensity, graphProjectionN_append, PiLp.smul_apply, smul_eq_mul]
      have he : EuclideanSpace.single (Fin.last n) (1 : ℝ) i =
          EuclideanSpace.single i (1 : ℝ) (Fin.last n) := by
        by_cases hi : i = Fin.last n
        · subst i; rfl
        · simp [hi, Ne.symm hi]
      rw [he]
      ring
  rw [hs]
  ring

/-- Cutting on the lower side of a flat interface preserves local BV, proved
from its actual trace formula. -/
theorem IsLocallyBVOn.indicator_lowerHalfspace {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsLocallyBVOn f univ) (a : ℝ) :
    IsLocallyBVOn ({z | z (Fin.last n) < a}.indicator f) univ := by
  classical
  obtain ⟨μ, σ, _, _, _, _, hσ, hp, _⟩ := hf.exists_ambient_scalar_polar
  let μs : Bool → Measure (EuclideanSpace ℝ (Fin (n + 1))) :=
    fun b => if b then flatHyperplaneMeasure n a else μ.restrict {z | z (Fin.last n) < a}
  let σs : Bool → EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun b => if b then flatCutSurfaceDensity f a else σ
  have hH : MeasurableSet {z : EuclideanSpace ℝ (Fin (n + 1)) | z (Fin.last n) < a} :=
    measurableSet_lt (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last n)).measurable measurable_const
  apply isLocallyBVOn_of_sum_coordinate_pairings
    ((locallyIntegrableOn_univ.mp hf.1).indicator hH) (μ := μs) (σ := σs)
  · intro b
    cases b
    · exact hσ.mono_measure Measure.restrict_le_self
    · exact hf.locallyIntegrable_flatCutSurfaceDensity a
  · intro i φ hφ
    simpa only [μs, σs, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte, add_comm] using
      hf.flat_cut_coordinate_measure_pairing hσ hp a i φ hφ

/-- Local BV is closed under subtraction on the whole ambient space. -/
lemma IsLocallyBVOn.sub_univ {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : IsLocallyBVOn f univ) (hg : IsLocallyBVOn g univ) :
    IsLocallyBVOn (fun z => f z - g z) univ := by
  refine ⟨hf.1.sub hg.1, fun A hA hcA hAU => ?_⟩
  have hif : IsBVOn f A := ⟨
    (hf.1.integrableOn_compact_subset hAU hcA).mono_set subset_closure,
    hf.2 A hA hcA hAU⟩
  have hig : IsBVOn g A := ⟨
    (hg.1.integrableOn_compact_subset hAU hcA).mono_set subset_closure,
    hg.2 A hA hcA hAU⟩
  exact (hif.sub hig).2

lemma volume_flatHyperplane (n : ℕ) (a : ℝ) :
    volume {z : EuclideanSpace ℝ (Fin (n + 1)) | z (Fin.last n) = a} = 0 := by
  have hm : MeasurableSet {z : EuclideanSpace ℝ (Fin (n + 1)) | z (Fin.last n) = a} :=
    measurableSet_eq_fun (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last n)).measurable measurable_const
  have hp : realLineCoordinates n ⁻¹'
      {z : EuclideanSpace ℝ (Fin (n + 1)) | z (Fin.last n) = a} =
      univ ×ˢ ({a} : Set ℝ) := by
    ext p
    simp
  have hh := (realLineCoordinates_measurePreserving n).measure_preimage hm.nullMeasurableSet
  rw [hp] at hh
  simpa only [Measure.prod_prod, measure_singleton, mul_zero] using hh.symm

/-- The open upper halfspace cut is also locally BV. -/
theorem IsLocallyBVOn.indicator_upperHalfspace {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsLocallyBVOn f univ) (a : ℝ) :
    IsLocallyBVOn ({z | a < z (Fin.last n)}.indicator f) univ := by
  classical
  have hsub := hf.sub_univ (hf.indicator_lowerHalfspace a)
  apply hsub.congr_ae
  rw [Measure.restrict_univ]
  have hae : ∀ᵐ z : EuclideanSpace ℝ (Fin (n + 1)) ∂volume, z (Fin.last n) ≠ a := by
    rw [ae_iff]
    simpa using volume_flatHyperplane n a
  filter_upwards [hae] with z hz
  by_cases hza : z (Fin.last n) < a
  · simp [hza, not_lt.mpr hza.le]
  · have haz : a < z (Fin.last n) := lt_of_le_of_ne (not_lt.mp hza) (Ne.symm hz)
    simp [hza, haz]

/-- A single positive measure carrying the disjoint bulk and interface terms. -/
def flatCutMeasure {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin (n + 1)))) (a : ℝ) :
    Measure (EuclideanSpace ℝ (Fin (n + 1))) :=
  μ.restrict {z | z (Fin.last n) < a} + flatHyperplaneMeasure n a

/-- Density with respect to the disjoint bulk-plus-interface measure. -/
def flatCutDensity {n : ℕ}
    (σ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (a : ℝ)
    (z : EuclideanSpace ℝ (Fin (n + 1))) : EuclideanSpace ℝ (Fin (n + 1)) :=
  if z (Fin.last n) < a then σ z else flatCutSurfaceDensity f a z

lemma flatCutDensity_ae_bulk {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin (n + 1))))
    (σ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (a : ℝ) :
    flatCutDensity σ f a =ᵐ[μ.restrict {z | z (Fin.last n) < a}] σ := by
  have hH : MeasurableSet {z : EuclideanSpace ℝ (Fin (n + 1)) | z (Fin.last n) < a} :=
    measurableSet_lt (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last n)).measurable measurable_const
  filter_upwards [ae_restrict_mem hH] with z hz
  exact ite_eq_left hz

lemma flatCutDensity_ae_surface {n : ℕ}
    (σ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (a : ℝ) :
    flatCutDensity σ f a =ᵐ[flatHyperplaneMeasure n a] flatCutSurfaceDensity f a := by
  rw [Filter.EventuallyEq, flatHyperplaneMeasure,
    (isClosedEmbedding_graphAppendN n a).measurableEmbedding.ae_map_iff]
  exact ae_of_all _ fun x => by simp [flatCutDensity]

lemma IsLocallyBVOn.locallyIntegrable_flatCutDensity {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsLocallyBVOn f univ)
    {μ : Measure (EuclideanSpace ℝ (Fin (n + 1)))}
    {σ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hσ : LocallyIntegrable σ μ) (a : ℝ) :
    LocallyIntegrable (flatCutDensity σ f a) (flatCutMeasure μ a) := by
  have hb := (hσ.mono_measure (Measure.restrict_le_self (s := {z | z (Fin.last n) < a}))).congr
    (flatCutDensity_ae_bulk μ σ f a).symm
  have hs := (hf.locallyIntegrable_flatCutSurfaceDensity a).congr
    (flatCutDensity_ae_surface σ f a).symm
  apply locallyIntegrable_iff.mpr
  intro K hK
  exact (hb.integrableOn_isCompact hK).add_measure (hs.integrableOn_isCompact hK)

/-- The actual derivative of a halfspace cut as one locally integrable density.
The measure is positive but the vector density is signed; it is not required to
have unit norm. This representation is suitable for C¹ cofactor transport. -/
theorem IsLocallyBVOn.flat_cut_distributional_pairing {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsLocallyBVOn f univ)
    {μ : Measure (EuclideanSpace ℝ (Fin (n + 1)))}
    {σ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hσ : LocallyIntegrable σ μ)
    (hpair : ∀ (i : Fin (n + 1))
      (φ : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin (n + 1))) ℝ),
      ContDiff ℝ 1 φ → -(∫ z, f z * fderiv ℝ φ z (EuclideanSpace.single i 1)) =
        ∫ z, φ z * σ z i ∂μ)
    (a : ℝ) (i : Fin (n + 1))
    (φ : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin (n + 1))) ℝ)
    (hφ : ContDiff ℝ 1 φ) :
    -(∫ z, ({z | z (Fin.last n) < a}.indicator f) z *
      fderiv ℝ φ z (EuclideanSpace.single i 1)) =
      ∫ z, φ z * flatCutDensity σ f a z i ∂flatCutMeasure μ a := by
  have hi : Integrable (fun z => φ z * flatCutDensity σ f a z i) (flatCutMeasure μ a) := by
    simpa only [smul_eq_mul, mul_comm] using!
      (locallyIntegrable_scalar_component (hf.locallyIntegrable_flatCutDensity hσ a) i
        ).integrable_smul_right_of_hasCompactSupport φ.continuous φ.hasCompactSupport
  have hib : Integrable (fun z => φ z * flatCutDensity σ f a z i)
      (μ.restrict {z | z (Fin.last n) < a}) :=
    hi.mono_measure (Measure.le_add_right le_rfl)
  have his : Integrable (fun z => φ z * flatCutDensity σ f a z i)
      (flatHyperplaneMeasure n a) := hi.mono_measure (Measure.le_add_left le_rfl)
  rw [flatCutMeasure, integral_add_measure hib his,
    hf.flat_cut_coordinate_measure_pairing hσ hpair a i φ hφ]
  congr 1
  · apply integral_congr_ae
    filter_upwards [flatCutDensity_ae_bulk μ σ f a] with z hz
    rw [hz]
  · apply integral_congr_ae
    filter_upwards [flatCutDensity_ae_surface σ f a] with z hz
    rw [hz]

end LiquidDrop
