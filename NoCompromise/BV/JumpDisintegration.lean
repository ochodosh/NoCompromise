module

public import NoCompromise.BV.JointJumpDensity
public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

@[expose] public section

/-!
# Full directional disintegration of binary BV derivatives

For any Lebesgue-measurable set of locally finite perimeter and any fixed unit
direction, this module constructs a Radon directional derivative with a Borel
unit sign. Its positive total-variation measure disintegrates on every Borel set
into the actual one-dimensional slice variations. Its compatible finite signed
restrictions to compact sets disintegrate into the signed slice jump measures.
The slice measure evaluations and Borel sections are proved Lebesgue measurable;
no measurable-kernel premise is used.

Canonical left-continuous binary representatives describe the slices only up to
one-dimensional Lebesgue null sets. Their jump sets are finite on compact
subintervals, and their signed measures there are the finite sums of jumps.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology
namespace LiquidDrop

/-- Scalar directional derivative represented by a locally finite positive measure
and a Borel sign of absolute value one. -/
structure IsDirectionalBVPolar {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (v : EuclideanSpace ℝ (Fin n)) (τ : Measure (EuclideanSpace ℝ (Fin n)))
    (s : EuclideanSpace ℝ (Fin n) → ℝ) : Prop where
  regular : τ.Regular
  finiteOnCompacts : IsFiniteMeasureOnCompacts τ
  measurable : Measurable s
  norm_ae : ∀ᵐ z ∂τ, |s z| = 1
  locallyIntegrable : LocallyIntegrable f volume
  test_eq : ∀ φ, ContDiff ℝ 1 φ → HasCompactSupport φ →
    -(∫ z, f z * fderiv ℝ φ z v) = ∫ z, φ z * s z ∂τ

lemma IsDirectionalBVPolar.locallyIntegrable_density {n : ℕ}
    {f s : EuclideanSpace ℝ (Fin n) → ℝ} {v : EuclideanSpace ℝ (Fin n)}
    {τ : Measure (EuclideanSpace ℝ (Fin n))} (h : IsDirectionalBVPolar f v τ s) :
    LocallyIntegrable s τ := by
  let := h.finiteOnCompacts
  apply locallyIntegrable_iff.mpr
  intro K hK
  let : IsFiniteMeasure (τ.restrict K) := ⟨by simpa using hK.measure_lt_top (μ := τ)⟩
  exact Integrable.of_bound h.measurable.aestronglyMeasurable.restrict 1
    ((ae_restrict_of_ae h.norm_ae).mono fun z hz => by simpa only [Real.norm_eq_abs] using hz.le)

/-- The actual finite signed derivative on a compact set. -/
def directionalDerivativeRestriction {n : ℕ}
    (τ : Measure (EuclideanSpace ℝ (Fin n))) (s : EuclideanSpace ℝ (Fin n) → ℝ)
    (K : Set (EuclideanSpace ℝ (Fin n))) : SignedMeasure (EuclideanSpace ℝ (Fin n)) :=
  (τ.restrict K).withDensityᵥ s

lemma IsDirectionalBVPolar.variation_directionalDerivativeRestriction {n : ℕ}
    {f s : EuclideanSpace ℝ (Fin n) → ℝ} {v : EuclideanSpace ℝ (Fin n)}
    {τ : Measure (EuclideanSpace ℝ (Fin n))} (h : IsDirectionalBVPolar f v τ s)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) :
    (directionalDerivativeRestriction τ s K).variation = τ.restrict K := by
  rw [directionalDerivativeRestriction,
    Measure.variation_withDensityᵥ (h.locallyIntegrable_density.integrableOn_isCompact hK)]
  calc
    (τ.restrict K).withDensity (fun z => ‖s z‖ₑ) =
        (τ.restrict K).withDensity (fun _ => 1) := by
      apply withDensity_congr_ae
      filter_upwards [ae_restrict_of_ae h.norm_ae] with z hz
      simp only [Real.enorm_eq_ofReal_abs, hz, ENNReal.ofReal_one]
    _ = τ.restrict K := by simp

/-- Real line coordinates in a prescribed orthogonal frame. -/
def jumpCoordinateHomeomorph (n : ℕ)
    (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1))) :
    (EuclideanSpace ℝ (Fin n) × ℝ) ≃ₜ EuclideanSpace ℝ (Fin (n + 1)) :=
  ((Homeomorph.prodComm _ _).trans (euclideanLastEquiv n).symm.toHomeomorph).trans
    e.toHomeomorph

@[simp] lemma jumpCoordinateHomeomorph_apply {n : ℕ}
    (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (p : EuclideanSpace ℝ (Fin n) × ℝ) :
    jumpCoordinateHomeomorph n e p = e (graphAppendN p.1 p.2) := rfl

/-- A full signed and total-variation disintegration, with actual slice measures
and canonical representatives. All measurability is part of the conclusion. -/
structure IsDirectionalJumpDisintegration {n : ℕ}
    (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (τ : Measure (EuclideanSpace ℝ (Fin (n + 1))))
    (s : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (κ : EuclideanSpace ℝ (Fin n) → Measure ℝ)
    (σ : EuclideanSpace ℝ (Fin n) → ℝ → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → ℝ → ℝ → ℝ → ℝ) : Prop where
  polar : IsDirectionalBVPolar f (e (EuclideanSpace.single (Fin.last n) 1)) τ s
  slices : ∀ᵐ x, IsRealBVPolar (fun t => f (e (graphAppendN x t))) (κ x) (σ x) ∧
    ∀ a b, IsBinaryBVRepresentativeOn (fun t => f (e (graphAppendN x t))) (g x a b) a b
  measurable_evaluation : ∀ A : Set ℝ, MeasurableSet A →
    AEMeasurable (fun x => κ x A) volume
  measurable_sections : ∀ A, MeasurableSet A →
    AEMeasurable (fun x => κ x {t | e (graphAppendN x t) ∈ A}) volume
  variation_eq : ∀ A, MeasurableSet A →
    τ A = ∫⁻ x, κ x {t | e (graphAppendN x t) ∈ A}
  integral_eq : ∀ q : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
    Measurable q → Integrable (fun z => q z * s z) τ →
    Integrable (fun x => ∫ t, q (e (graphAppendN x t)) * σ x t ∂κ x) volume ∧
    (∫ z, q z * s z ∂τ) = ∫ x, ∫ t, q (e (graphAppendN x t)) * σ x t ∂κ x

/-- Construct the directional polar and both disintegrations for a Borel binary BV
function. No joint measurability of the initially chosen slice signs is assumed. -/
theorem IsLocallyBVOn.exists_directionalJumpDisintegration {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsLocallyBVOn f univ)
    (hm : Measurable f) (hb : ∀ z, f z ∈ ({0, 1} : Set ℝ))
    (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1))) :
    ∃ τ s κ σ g, IsDirectionalJumpDisintegration f e τ s κ σ g := by
  let H := jumpCoordinateHomeomorph n e
  let F : EuclideanSpace ℝ (Fin n) × ℝ → ℝ := f ∘ H
  have hF : Measurable F := hm.comp H.measurable
  have hfe := hf.comp_linearIsometryEquiv_univ e
  obtain ⟨κ, σ, g, hg, hκ⟩ := hfe.exists_measurable_binary_line_measures (fun z => hb (e z))
  have hp : ∀ᵐ x, IsRealBVPolar (fun t => F (x, t)) (κ x) (σ x) := hg.mono fun _ h => h.1
  have hrep : ∀ᵐ x, ∀ a b, ∃ g, IsBinaryBVRepresentativeOn (fun t => F (x, t)) g a b :=
    hg.mono fun x hx a b => ⟨g x a b, hx.2 a b⟩
  let μp := sliceProductMeasure volume 0 κ (hp.mono fun _ h => h.finiteOnCompacts) hκ
  let τ := μp.map H
  let S := jointJumpDensity F
  let s := S ∘ H.symm
  have hS : Measurable S := measurable_jointJumpDensity hF
  have hs : Measurable s := hS.comp H.symm.measurable
  have hn : ∀ᵐ p ∂μp, |S p| = 1 := ae_abs_jointJumpDensity_eq_one hF hp hrep hκ
  have hsn : ∀ᵐ z ∂τ, |s z| = 1 := by
    apply H.measurableEmbedding.ae_map_iff.mpr
    simpa only [s, Function.comp_def, Homeomorph.symm_apply_apply] using hn
  let : IsFiniteMeasureOnCompacts μp := hfe.isFiniteMeasureOnCompacts_sliceProductMeasure
    (hg.mono fun _ h => h.1) hκ
  let : IsFiniteMeasureOnCompacts τ := Measure.IsFiniteMeasureOnCompacts.map μp H
  have hsl : LocallyIntegrable s τ := by
    apply locallyIntegrable_iff.mpr
    intro K hK
    let : IsFiniteMeasure (τ.restrict K) := ⟨by simpa using hK.measure_lt_top (μ := τ)⟩
    exact Integrable.of_bound hs.aestronglyMeasurable.restrict 1
      ((ae_restrict_of_ae hsn).mono fun z hz => by simpa only [Real.norm_eq_abs] using hz.le)
  have hline : ∀ᵐ x, (fun t => S (x, t)) =ᵐ[κ x] σ x := by
    filter_upwards [hp, hrep] with x hx hxg
    exact jointJumpDensity_eq_polar_ae hx hxg
  have hint (q : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (hq : Measurable q)
      (hqi : Integrable (fun z => q z * s z) τ) :
      Integrable (fun x => ∫ t, q (e (graphAppendN x t)) * σ x t ∂κ x) volume ∧
      (∫ z, q z * s z ∂τ) = ∫ x, ∫ t, q (e (graphAppendN x t)) * σ x t ∂κ x := by
    have hi : Integrable (fun p => q (H p) * S p) μp := by
      have hi := (integrable_map_equiv H.toMeasurableEquiv _).mp hqi
      change Integrable (fun p => q (H p) * S (H.symm (H p))) μp at hi
      simpa only [Homeomorph.symm_apply_apply] using hi
    obtain ⟨_, hii, he⟩ := integral_sliceProductMeasure volume 0 κ
      (hp.mono fun _ h => h.finiteOnCompacts) hκ ((hq.comp H.measurable).mul hS) hi
    have heq : (fun x => ∫ t, q (H (x, t)) * S (x, t) ∂κ x) =ᵐ[volume]
        (fun x => ∫ t, q (e (graphAppendN x t)) * σ x t ∂κ x) := by
      filter_upwards [hline] with x hx
      apply integral_congr_ae
      filter_upwards [hx] with t ht
      simp only [H, jumpCoordinateHomeomorph_apply, ht]
    refine ⟨hii.congr heq, ?_⟩
    rw [show (∫ z, q z * s z ∂τ) = ∫ p, q (H p) * S p ∂μp from by
      simpa only [s, Function.comp_def, Homeomorph.symm_apply_apply] using
        (H.measurableEmbedding.integral_map (fun z => q z * s z))]
    exact he.trans (integral_congr_ae heq)
  refine ⟨τ, s, κ, σ, g, ?_⟩
  refine ⟨⟨inferInstance, inferInstance, hs, hsn, locallyIntegrableOn_univ.mp hf.1, ?_⟩,
    hg, hκ, ?_, ?_, hint⟩
  · intro φ hφ hcφ
    have hi : Integrable (fun z => φ z * s z) τ := by
      simpa only [smul_eq_mul] using hsl.integrable_smul_left_of_hasCompactSupport
        hφ.continuous hcφ
    rw [(hint φ hφ.continuous.measurable hi).2,
      frame_pairing_eq_integral_lineDerivativePairing (locallyIntegrableOn_univ.mp hf.1) hφ hcφ e]
    apply integral_congr_ae
    filter_upwards [hp] with x hx
    have hφe : ContDiff ℝ 1 (φ ∘ e) := hφ.comp e.toContinuousLinearEquiv.contDiff
    rw [lineDerivativePairing_eq_real hφe]
    exact hx.test_eq _ (contDiff_lineSlice_real hφe x)
      (hasCompactSupport_lineSlice_real (hcφ.comp_homeomorph e.toHomeomorph) x)
  · intro A hA
    exact aemeasurable_measure_prod_section 0
      (hp.mono fun _ h => h.finiteOnCompacts) hκ (H ⁻¹' A) (H.measurable hA)
  · intro A hA
    rw [show τ A = μp (H ⁻¹' A) from Measure.map_apply H.measurable hA,
      sliceProductMeasure_apply _ _ _ _ _ (H.measurable hA)]
    rfl

lemma IsDirectionalJumpDisintegration.setIntegral_eq {n : ℕ}
    {f s : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    {e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1))}
    {τ : Measure (EuclideanSpace ℝ (Fin (n + 1)))}
    {κ : EuclideanSpace ℝ (Fin n) → Measure ℝ}
    {σ : EuclideanSpace ℝ (Fin n) → ℝ → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → ℝ → ℝ → ℝ → ℝ}
    (h : IsDirectionalJumpDisintegration f e τ s κ σ g)
    {K A : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hK : IsCompact K) (hA : MeasurableSet A) (hAK : A ⊆ K) :
    Integrable (fun x => ∫ t in {t | e (graphAppendN x t) ∈ A}, σ x t ∂κ x) volume ∧
    (∫ z in A, s z ∂τ) = ∫ x, ∫ t in {t | e (graphAppendN x t) ∈ A}, σ x t ∂κ x := by
  classical
  have hi : IntegrableOn s A τ :=
    (h.polar.locallyIntegrable_density.integrableOn_isCompact hK).mono_set hAK
  have he : (fun z => A.indicator (fun _ => (1 : ℝ)) z * s z) = A.indicator s := by
    funext z
    by_cases hz : z ∈ A <;> simp [hz]
  have hir : Integrable (fun z => A.indicator (fun _ => (1 : ℝ)) z * s z) τ := by
    rw [he]
    exact hi.integrable_indicator hA
  have hr := h.integral_eq (A.indicator (fun _ => 1)) (measurable_const.indicator hA) hir
  have hinner (x : EuclideanSpace ℝ (Fin n)) :
      (∫ t, A.indicator (fun _ => (1 : ℝ)) (e (graphAppendN x t)) * σ x t ∂κ x) =
        ∫ t in {t | e (graphAppendN x t) ∈ A}, σ x t ∂κ x := by
    have ht : Measurable (fun t : ℝ => e (graphAppendN x t)) :=
      e.continuous.measurable.comp
        (continuous_const.add (continuous_id.smul continuous_const)).measurable
    have hAm : MeasurableSet {t | e (graphAppendN x t) ∈ A} := ht hA
    rw [← integral_indicator hAm]
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by
      by_cases ht : e (graphAppendN x t) ∈ A <;> simp [ht]
  simpa only [he, integral_indicator hA, hinner] using hr

lemma IsDirectionalJumpDisintegration.directionalDerivativeRestriction_apply {n : ℕ}
    {f s : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    {e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1))}
    {τ : Measure (EuclideanSpace ℝ (Fin (n + 1)))}
    {κ : EuclideanSpace ℝ (Fin n) → Measure ℝ}
    {σ : EuclideanSpace ℝ (Fin n) → ℝ → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → ℝ → ℝ → ℝ → ℝ}
    (h : IsDirectionalJumpDisintegration f e τ s κ σ g)
    {K A : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hK : IsCompact K) (hA : MeasurableSet A) :
    directionalDerivativeRestriction τ s K A =
      ∫ x, ∫ t in {t | e (graphAppendN x t) ∈ A ∩ K}, σ x t ∂κ x := by
  rw [directionalDerivativeRestriction,
    withDensityᵥ_apply (h.polar.locallyIntegrable_density.integrableOn_isCompact hK) hA,
    Measure.restrict_restrict hA]
  exact (h.setIntegral_eq hK (hA.inter hK.measurableSet) inter_subset_right).2

lemma IsDirectionalJumpDisintegration.variation_directionalDerivativeRestriction_apply {n : ℕ}
    {f s : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    {e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1))}
    {τ : Measure (EuclideanSpace ℝ (Fin (n + 1)))}
    {κ : EuclideanSpace ℝ (Fin n) → Measure ℝ}
    {σ : EuclideanSpace ℝ (Fin n) → ℝ → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → ℝ → ℝ → ℝ → ℝ}
    (h : IsDirectionalJumpDisintegration f e τ s κ σ g)
    {K A : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hK : IsCompact K) (hA : MeasurableSet A) :
    (directionalDerivativeRestriction τ s K).variation A =
      ∫⁻ x, κ x {t | e (graphAppendN x t) ∈ A ∩ K} := by
  rw [h.polar.variation_directionalDerivativeRestriction hK, Measure.restrict_apply hA]
  exact h.variation_eq _ (hA.inter hK.measurableSet)

lemma IsDirectionalBVPolar.directionalDerivativeRestriction_restrict {n : ℕ}
    {f s : EuclideanSpace ℝ (Fin n) → ℝ} {v : EuclideanSpace ℝ (Fin n)}
    {τ : Measure (EuclideanSpace ℝ (Fin n))} (h : IsDirectionalBVPolar f v τ s)
    {K L : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (hL : IsCompact L) (hKL : K ⊆ L) :
    (directionalDerivativeRestriction τ s L).restrict K =
      directionalDerivativeRestriction τ s K := by
  ext A hA
  rw [VectorMeasure.restrict_apply _ hK.measurableSet hA, directionalDerivativeRestriction,
    withDensityᵥ_apply (h.locallyIntegrable_density.integrableOn_isCompact hL)
      (hA.inter hK.measurableSet), directionalDerivativeRestriction,
    withDensityᵥ_apply (h.locallyIntegrable_density.integrableOn_isCompact hK) hA,
    Measure.restrict_restrict (hA.inter hK.measurableSet), Measure.restrict_restrict hA]
  rw [inter_assoc, inter_eq_left.mpr hKL]

lemma IsRealBVPolar.congr_ae {f k σ : ℝ → ℝ} {μ : Measure ℝ}
    (h : IsRealBVPolar f μ σ) (hfk : f =ᵐ[volume] k) : IsRealBVPolar k μ σ := by
  refine ⟨h.regular, h.finiteOnCompacts, h.measurable, h.norm_ae,
    h.locallyIntegrable.congr hfk, ?_, ?_⟩
  · intro ψ hψ hcψ
    rw [← h.test_eq ψ hψ hcψ]
    congr 1
    exact integral_congr_ae (hfk.symm.mul (EventuallyEq.refl _ _))
  · intro O hO
    rw [h.open_eq O hO]
    exact variation_congr_ae _ (ae_restrict_of_ae
      (euclideanOneReal.measurePreserving.quasiMeasurePreserving.ae_eq_comp hfk))

lemma IsBinaryBVRepresentativeOn.congr_ae {f k g : ℝ → ℝ} {a b : ℝ}
    (h : IsBinaryBVRepresentativeOn f g a b) (hfk : f =ᵐ[volume] k) :
    IsBinaryBVRepresentativeOn k g a b := by
  have he : f =ᵐ[volume.restrict (Ioo a b)] k := ae_restrict_of_ae hfk
  exact ⟨h.boundedVariation, h.leftContinuous, he.symm.trans h.ae_eq, h.binary⟩

lemma IsDirectionalBVPolar.congr_ae {n : ℕ}
    {f k s : EuclideanSpace ℝ (Fin n) → ℝ} {v : EuclideanSpace ℝ (Fin n)}
    {τ : Measure (EuclideanSpace ℝ (Fin n))} (h : IsDirectionalBVPolar f v τ s)
    (hfk : f =ᵐ[volume] k) : IsDirectionalBVPolar k v τ s := by
  refine ⟨h.regular, h.finiteOnCompacts, h.measurable, h.norm_ae,
    h.locallyIntegrable.congr hfk, ?_⟩
  intro φ hφ hcφ
  rw [← h.test_eq φ hφ hcφ]
  congr 1
  exact integral_congr_ae (hfk.symm.mul (EventuallyEq.refl _ _))

lemma IsDirectionalJumpDisintegration.congr_ae {n : ℕ}
    {f k s : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    {e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1))}
    {τ : Measure (EuclideanSpace ℝ (Fin (n + 1)))}
    {κ : EuclideanSpace ℝ (Fin n) → Measure ℝ}
    {σ : EuclideanSpace ℝ (Fin n) → ℝ → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → ℝ → ℝ → ℝ → ℝ}
    (h : IsDirectionalJumpDisintegration f e τ s κ σ g)
    (hfk : f =ᵐ[volume] k) : IsDirectionalJumpDisintegration k e τ s κ σ g := by
  refine ⟨h.polar.congr_ae hfk, ?_, h.measurable_evaluation, h.measurable_sections,
    h.variation_eq, h.integral_eq⟩
  have he := e.measurePreserving.quasiMeasurePreserving.ae_eq_comp hfk
  filter_upwards [h.slices, ae_lineSlice_congr_ae he] with x hx heq
  have hr : (fun t => f (e (graphAppendN x t))) =ᵐ[volume]
      (fun t => k (e (graphAppendN x t))) := by
    simpa only [lineSlice, Function.comp_def, euclideanOneReal_symm_apply] using
      euclideanOneReal.symm.measurePreserving.quasiMeasurePreserving.ae_eq_comp heq
  exact ⟨hx.1.congr_ae hr, fun a b => (hx.2 a b).congr_ae hr⟩

/-- Full directional BV slicing for a Lebesgue-measurable set of locally finite
perimeter, in every fixed unit direction. The derivative and variation are actual
locally finite measures, and the canonical line representatives are understood
modulo one-dimensional Lebesgue null sets. -/
theorem HasLocallyFinitePerimeter.exists_full_jump_disintegration_direction {n : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume)
    {v : EuclideanSpace ℝ (Fin (n + 1))} (hv : ‖v‖ = 1) :
    ∃ e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)),
      ∃ τ s κ σ g, e (EuclideanSpace.single (Fin.last n) 1) = v ∧
        IsDirectionalJumpDisintegration (E.indicator (fun _ => (1 : ℝ))) e τ s κ σ g := by
  classical
  let B := toMeasurable volume E
  let f := B.indicator (fun _ => (1 : ℝ))
  have hfg : f =ᵐ[volume] E.indicator (fun _ => (1 : ℝ)) :=
    indicator_ae_eq_of_ae_eq_set hmE.toMeasurable_ae_eq
  have hf : IsLocallyBVOn f univ :=
    (hE.isLocallyBVOn_indicator hmE univ).congr_ae (by simpa using hfg.symm)
  have hm : Measurable f := measurable_const.indicator (measurableSet_toMeasurable volume E)
  have hb (z) : f z ∈ ({0, 1} : Set ℝ) := by
    by_cases hz : z ∈ B <;> simp [f, hz]
  obtain ⟨e, he⟩ := exists_line_direction_frame hv
  obtain ⟨τ, s, κ, σ, g, h⟩ := hf.exists_directionalJumpDisintegration hm hb e
  exact ⟨e, τ, s, κ, σ, g, he, h.congr_ae hfg⟩

lemma IsDirectionalJumpDisintegration.ae_finite_jumps {n : ℕ}
    {f s : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    {e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1))}
    {τ : Measure (EuclideanSpace ℝ (Fin (n + 1)))}
    {κ : EuclideanSpace ℝ (Fin n) → Measure ℝ}
    {σ : EuclideanSpace ℝ (Fin n) → ℝ → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → ℝ → ℝ → ℝ → ℝ}
    (h : IsDirectionalJumpDisintegration f e τ s κ σ g) :
    ∀ᵐ x, ∀ a b, ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo a b →
      {t ∈ K | oneDimensionalJump (g x a b) t ≠ 0}.Finite :=
  h.slices.mono fun _ hx _ _ _ hK hKU => (hx.2 _ _).finite_jumps hK hKU

lemma IsDirectionalJumpDisintegration.ae_slice_integral_eq_finsum_jumps {n : ℕ}
    {f s : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    {e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1))}
    {τ : Measure (EuclideanSpace ℝ (Fin (n + 1)))}
    {κ : EuclideanSpace ℝ (Fin n) → Measure ℝ}
    {σ : EuclideanSpace ℝ (Fin n) → ℝ → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → ℝ → ℝ → ℝ → ℝ}
    (h : IsDirectionalJumpDisintegration f e τ s κ σ g) :
    ∀ᵐ x, ∀ a b, ∀ K A : Set ℝ, IsCompact K → K ⊆ Ioo a b →
      MeasurableSet A → A ⊆ K →
      (∫ t in A, σ x t ∂κ x) = ∑ᶠ t, A.indicator (oneDimensionalJump (g x a b)) t :=
  h.slices.mono fun _ hx _ _ _ _ hK hKU hA hAK =>
    (hx.2 _ _).setIntegral_eq_finsum_jumps hx.1 hK hKU hA hAK

end LiquidDrop
