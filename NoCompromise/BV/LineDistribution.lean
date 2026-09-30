module

public import NoCompromise.BV.LineSlicing
public import NoCompromise.Sobolev.Extension

@[expose] public section

/-!
# Directional BV slices and weak disintegration

Orthogonal transport gives locally BV slices in any fixed unit direction.
Fubini identifies all compact C1 directional pairings with the one-dimensional
slice pairings. Almost every slice has a genuine locally finite polar derivative
measure; a chosen family realizes these tested integrals, which are integrable
in the transverse variable. No pointwise representative or jump-measure theorem
is assumed. Identifying these measures with jumps is a separate step.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma locallyIntegrable_comp_linearIsometryEquiv {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : LocallyIntegrable f volume)
    (e : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    LocallyIntegrable (f ∘ e) volume := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  have hi := hf.integrableOn_isCompact (hK.image e.continuous)
  have ht := e.measurePreserving.integrableOn_comp_preimage e.toHomeomorph.measurableEmbedding
    (s := e '' K) (f := f)
  rw [e.injective.preimage_image] at ht
  exact ht.mpr hi

/-- The proved BV chain estimate specializes to invariance under orthogonal coordinates. -/
theorem IsLocallyBVOn.comp_linearIsometryEquiv_univ {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsLocallyBVOn f univ)
    (e : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    IsLocallyBVOn (f ∘ e) univ := by
  have hi := locallyIntegrableOn_univ.mp hf.1
  refine ⟨(locallyIntegrable_comp_linearIsometryEquiv hi e).locallyIntegrableOn _, ?_⟩
  intro A hA hcA _
  have hV : IsOpen (e '' A) := e.toHomeomorph.isOpenMap A hA
  have hcV : IsCompact (closure (e '' A)) := by
    change IsCompact (closure (e.toHomeomorph '' A))
    rw [← e.toHomeomorph.image_closure]
    exact hcA.image e.continuous
  have hfi : IsBVOn f (e '' A) := ⟨(hi.integrableOn_isCompact hcV).mono_set subset_closure,
    hf.2 _ hV hcV (subset_univ _)⟩
  have hv := variation_comp_le_of_lipschitz_leftInverse hA hV
    e.isometry.lipschitzWith.lipschitzOnWith e.symm.isometry.lipschitzWith.lipschitzOnWith
    (mapsTo_image e A) (fun x _ => e.symm_apply_apply x) hfi
  exact hv.trans_lt ENNReal.ofReal_lt_top

/-- An orthogonal frame represents any fixed unit direction. -/
lemma exists_line_direction_frame {n : ℕ} {v : EuclideanSpace ℝ (Fin (n + 1))}
    (hv : ‖v‖ = 1) :
    ∃ e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)),
      e (EuclideanSpace.single (Fin.last n) 1) = v := by
  let u := EuclideanSpace.single (Fin.last n) (1 : ℝ)
  let e := (Submodule.span ℝ {u - v})ᗮ.reflection
  exact ⟨e, Submodule.reflection_sub (by simpa [u] using hv.symm)⟩

/-- Slicing after an arbitrary orthogonal change of coordinates. -/
theorem IsLocallyBVOn.ae_lineSlice_frame {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsLocallyBVOn f univ)
    (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1))) :
    ∀ᵐ x : EuclideanSpace ℝ (Fin n),
      IsLocallyBVOn (fun t : EuclideanSpace ℝ (Fin 1) =>
        f (e (graphBaseN n x) + t 0 • e (EuclideanSpace.single (Fin.last n) 1))) univ := by
  have h := (hf.comp_linearIsometryEquiv_univ e).ae_lineSlice
  filter_upwards [h] with x hx
  change IsLocallyBVOn (fun t : EuclideanSpace ℝ (Fin 1) =>
    f (e (graphAppendN x (t 0)))) univ at hx
  simpa only [graphAppendN, map_add, map_smul] using hx

/-- Every fixed unit direction has locally BV slices, parametrized by its orthogonal frame. -/
theorem HasLocallyFinitePerimeter.ae_lineSlice_direction {n : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) {v : EuclideanSpace ℝ (Fin (n + 1))}
    (hv : ‖v‖ = 1) :
    ∃ e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)),
      e (EuclideanSpace.single (Fin.last n) 1) = v ∧
      ∀ᵐ x : EuclideanSpace ℝ (Fin n),
        IsLocallyBVOn (fun t : EuclideanSpace ℝ (Fin 1) =>
          E.indicator (fun _ => (1 : ℝ)) (e (graphBaseN n x) + t 0 • v)) univ := by
  obtain ⟨e, he⟩ := exists_line_direction_frame hv
  refine ⟨e, he, ?_⟩
  simpa only [he] using (hE.isLocallyBVOn_indicator hmE univ).ae_lineSlice_frame e

/-- Null changes in ambient representatives induce null changes on almost every line. -/
lemma ae_lineSlice_congr_ae {n : ℕ}
    {f g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hfg : f =ᵐ[volume] g) :
    ∀ᵐ x : EuclideanSpace ℝ (Fin n), lineSlice f x =ᵐ[volume] lineSlice g x := by
  have hp := (lineCoordinateEquiv_measurePreserving n).symm (lineCoordinateEquiv n)
  exact Measure.ae_ae_of_ae_prod (hp.quasiMeasurePreserving.ae_eq_comp hfg)

lemma integral_lineSlice {n : ℕ} {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hf : Integrable f volume) :
    (∫ x : EuclideanSpace ℝ (Fin n), ∫ t : EuclideanSpace ℝ (Fin 1), lineSlice f x t) =
      ∫ z, f z := by
  let e := lineCoordinateEquiv n
  have hp := (lineCoordinateEquiv_measurePreserving n).symm e
  have hi := (hp.integrable_comp hf.aestronglyMeasurable).mpr hf
  change (∫ x, ∫ t, (f ∘ e.symm) (x, t)) = _
  rw [← integral_prod _ hi]
  exact hp.integral_comp e.symm.measurableEmbedding f

/-- The line derivative pairing, defined on almost-everywhere classes of functions. -/
def lineDerivativePairing {n : ℕ} (f φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  -(∫ t : EuclideanSpace ℝ (Fin 1), lineSlice f x t * gradient (lineSlice φ x) t 0)

lemma integrable_coordinate_derivative_pairing {n : ℕ}
    {f φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : LocallyIntegrable f volume)
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) :
    Integrable (fun z => f z * gradient φ z (Fin.last n)) volume := by
  have hc : Continuous (fun z => fderiv ℝ φ z (EuclideanSpace.single (Fin.last n) 1)) :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  simpa only [smul_eq_mul, ← gradient_apply_eq_fderiv_single] using
    hf.integrable_smul_right_of_hasCompactSupport hc
      (hcφ.fderiv_apply ℝ (EuclideanSpace.single (Fin.last n) 1))

lemma integrable_lineDerivativePairing {n : ℕ}
    {f φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : LocallyIntegrable f volume)
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) :
    Integrable (lineDerivativePairing f φ) volume := by
  have hq := integrable_coordinate_derivative_pairing hf hφ hcφ
  have hp := (lineCoordinateEquiv_measurePreserving n).symm (lineCoordinateEquiv n)
  have hi := (hp.integrable_comp hq.aestronglyMeasurable).mpr hq
  have hj := hi.integral_prod_left.neg
  change Integrable (fun x => -(∫ t : EuclideanSpace ℝ (Fin 1),
    lineSlice f x t * gradient (lineSlice φ x) t 0)) volume
  simp only [gradient_lineSlice hφ]
  exact hj

/-- Fubini disintegrates the directional distribution against every compact C1 test.
This is the weak pairing identity, before identifying line measures with jump measures. -/
theorem directional_pairing_eq_integral_lineDerivativePairing {n : ℕ}
    {f φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : LocallyIntegrable f volume)
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) :
    -(∫ z, f z * gradient φ z (Fin.last n)) =
      ∫ x : EuclideanSpace ℝ (Fin n), lineDerivativePairing f φ x := by
  have hi := integrable_coordinate_derivative_pairing hf hφ hcφ
  rw [← integral_lineSlice hi, ← integral_neg]
  congr 1
  funext x
  simp only [lineDerivativePairing, gradient_lineSlice hφ, lineSlice]

lemma isometry_linePoint {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    Isometry (fun t : EuclideanSpace ℝ (Fin 1) => graphAppendN x (t 0)) := by
  apply Isometry.of_dist_eq
  intro t s
  rw [dist_eq_norm, dist_eq_norm]
  simp only [graphAppendN, add_sub_add_left_eq_sub, ← sub_smul, norm_smul,
    PiLp.norm_single, norm_one, mul_one]
  exact euclideanOneReal.norm_map (t - s)

lemma hasCompactSupport_lineSlice {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hφ : HasCompactSupport φ)
    (x : EuclideanSpace ℝ (Fin n)) : HasCompactSupport (lineSlice φ x) :=
  hφ.comp_isClosedEmbedding (isometry_linePoint x).isClosedEmbedding

lemma gradient_comp_frame_last {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (z : EuclideanSpace ℝ (Fin (n + 1))) :
    gradient (φ ∘ e) z (Fin.last n) =
      fderiv ℝ φ (e z) (e (EuclideanSpace.single (Fin.last n) 1)) := by
  have he : HasFDerivAt (fun y => e y)
      e.toContinuousLinearEquiv.toContinuousLinearMap z :=
    e.toContinuousLinearEquiv.hasFDerivAt
  have hd := (hφ.differentiable one_ne_zero _).hasFDerivAt.comp z he
  rw [gradient_apply_eq_fderiv_single]
  exact congrArg (fun L => L (EuclideanSpace.single (Fin.last n) 1)) hd.fderiv

/-- The weak directional disintegration in any fixed orthogonal frame. -/
theorem frame_pairing_eq_integral_lineDerivativePairing {n : ℕ}
    {f φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : LocallyIntegrable f volume)
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1))) :
    -(∫ z, f z * fderiv ℝ φ z (e (EuclideanSpace.single (Fin.last n) 1))) =
      ∫ x : EuclideanSpace ℝ (Fin n), lineDerivativePairing (f ∘ e) (φ ∘ e) x := by
  have hec : ContDiff ℝ 1 (fun y => e y) := e.toContinuousLinearEquiv.contDiff
  have h := directional_pairing_eq_integral_lineDerivativePairing
    (locallyIntegrable_comp_linearIsometryEquiv hf e)
    (hφ.comp hec) (hcφ.comp_homeomorph e.toHomeomorph)
  have he := e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding
    (fun z => f z * fderiv ℝ φ z (e (EuclideanSpace.single (Fin.last n) 1)))
  have hg (z : EuclideanSpace ℝ (Fin (n + 1))) :
      gradient (fun y => φ (e y)) z (Fin.last n) =
        fderiv ℝ φ (e z) (e (EuclideanSpace.single (Fin.last n) 1)) :=
    gradient_comp_frame_last hφ e z
  simp only [hg, Function.comp_def] at h
  rw [he] at h
  exact h

lemma IsDistributionalPolarRepresentation.lineDerivativePairing_eq {n : ℕ}
    {f φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    {ρ : Measure (univ : Set (EuclideanSpace ℝ (Fin 1)))}
    {σ : ↥(univ : Set (EuclideanSpace ℝ (Fin 1))) → EuclideanSpace ℝ (Fin 1)}
    (h : IsDistributionalPolarRepresentation (lineSlice f x) univ ρ σ)
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) :
    lineDerivativePairing f φ x =
      ∫ t : (univ : Set (EuclideanSpace ℝ (Fin 1))), lineSlice φ x t * σ t 0 ∂ρ := by
  let ψ : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin 1)) ℝ :=
    ⟨⟨lineSlice φ x, (contDiff_lineSlice hφ x).continuous⟩, hasCompactSupport_lineSlice hcφ x⟩
  have ht := h.test_eq 0 ψ (contDiff_lineSlice hφ x) (subset_univ _)
  change -(∫ t in univ, lineSlice f x t *
    fderiv ℝ (lineSlice φ x) t (EuclideanSpace.single 0 1)) =
      (∫ t : (univ : Set (EuclideanSpace ℝ (Fin 1))), lineSlice φ x t * σ t 0 ∂ρ) at ht
  simpa only [Measure.restrict_univ, ← gradient_apply_eq_fderiv_single,
    lineDerivativePairing] using ht

/-- A family of genuine one-dimensional derivative polar measures realizes all
compact C1 directional pairings. Its tested integrals are Lebesgue integrable.
Identifying these measures with finite jump measures is a further one-dimensional step. -/
theorem IsLocallyBVOn.exists_line_polar_disintegration {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsLocallyBVOn f univ) :
    ∃ ρ : EuclideanSpace ℝ (Fin n) → Measure (univ : Set (EuclideanSpace ℝ (Fin 1))),
    ∃ σ : EuclideanSpace ℝ (Fin n) →
        ↥(univ : Set (EuclideanSpace ℝ (Fin 1))) → EuclideanSpace ℝ (Fin 1),
      (∀ᵐ x, (ρ x).Regular ∧ IsFiniteMeasureOnCompacts (ρ x) ∧
        IsDistributionalPolarRepresentation (lineSlice f x) univ (ρ x) (σ x)) ∧
      ∀ φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
        Integrable (fun x => ∫ t : (univ : Set (EuclideanSpace ℝ (Fin 1))),
          lineSlice φ x t * σ x t 0 ∂ρ x) volume ∧
        -(∫ z, f z * gradient φ z (Fin.last n)) =
          ∫ x : EuclideanSpace ℝ (Fin n),
            ∫ t : (univ : Set (EuclideanSpace ℝ (Fin 1))), lineSlice φ x t * σ x t 0 ∂ρ x := by
  classical
  have hex (x : EuclideanSpace ℝ (Fin n)) :
      ∃ ρ : Measure (univ : Set (EuclideanSpace ℝ (Fin 1))),
      ∃ σ : ↥(univ : Set (EuclideanSpace ℝ (Fin 1))) → EuclideanSpace ℝ (Fin 1),
        IsLocallyBVOn (lineSlice f x) univ →
          ρ.Regular ∧ IsFiniteMeasureOnCompacts ρ ∧
            IsDistributionalPolarRepresentation (lineSlice f x) univ ρ σ := by
    by_cases hx : IsLocallyBVOn (lineSlice f x) univ
    · obtain ⟨ρ, σ, hρ, hfin, hpol⟩ := exists_distributional_polar_representation isOpen_univ hx
      exact ⟨ρ, σ, fun _ => ⟨hρ, hfin, hpol⟩⟩
    · exact ⟨0, fun _ => 0, fun h => (hx h).elim⟩
  choose ρ σ hρ using hex
  have hgood := hf.ae_lineSlice
  refine ⟨ρ, σ, hgood.mono fun x hx => hρ x hx, ?_⟩
  intro φ hφ hcφ
  have heq : lineDerivativePairing f φ =ᵐ[volume]
      (fun x => ∫ t : (univ : Set (EuclideanSpace ℝ (Fin 1))),
        lineSlice φ x t * σ x t 0 ∂ρ x) := by
    filter_upwards [hgood] with x hx
    exact (hρ x hx).2.2.lineDerivativePairing_eq hφ hcφ
  have hi := locallyIntegrableOn_univ.mp hf.1
  exact ⟨(integrable_lineDerivativePairing hi hφ hcφ).congr heq,
    (directional_pairing_eq_integral_lineDerivativePairing hi hφ hcφ).trans
      (integral_congr_ae heq)⟩

end LiquidDrop
