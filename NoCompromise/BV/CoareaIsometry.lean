module

public import NoCompromise.Area.C1GraphAlgebra
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section

/-!
# Coarea identities under orthogonal changes of coordinates

The shared predicate includes Lebesgue almost-everywhere measurability of the
level integral. Regular chart formulas can give Borel measurability, while the
critical set contributes an almost-everywhere zero modification.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Weighted coarea on a fixed source patch, with actual Hausdorff level integrals. -/
def HasWeightedCoareaOn {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (A : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞, Measurable g →
    AEMeasurable (fun t : ℝ => ∫⁻ x in A ∩ u ⁻¹' {t}, g x
      ∂Measure.euclideanHausdorffMeasure (n - 1)) volume ∧
    (∫⁻ x in A, g x * ENNReal.ofReal ‖gradient u x‖) =
      ∫⁻ t : ℝ, ∫⁻ x in A ∩ u ⁻¹' {t}, g x ∂Measure.euclideanHausdorffMeasure (n - 1)

lemma gradient_comp_linearIsometryEquiv {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hu : DifferentiableAt ℝ u (e x)) :
    gradient (u ∘ e) x = e.symm (gradient u (e x)) := by
  apply ext_inner_right ℝ
  intro y
  calc
    inner ℝ (gradient (u ∘ e) x) y = fderiv ℝ (u ∘ e) x y := inner_gradient_left
    _ = fderiv ℝ u (e x) (e y) := by
      rw [fderiv_comp x hu e.toContinuousLinearEquiv.differentiableAt]
      have he : fderiv ℝ e x = e.toContinuousLinearEquiv.toContinuousLinearMap :=
        e.toContinuousLinearEquiv.hasFDerivAt.fderiv
      rw [he]
      rfl
    _ = inner ℝ (gradient u (e x)) (e y) := inner_gradient_left.symm
    _ = inner ℝ (e.symm (gradient u (e x))) y := by
      simpa only [e.apply_symm_apply] using e.inner_map_map (e.symm (gradient u (e x))) y

lemma norm_gradient_comp_linearIsometryEquiv {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hu : DifferentiableAt ℝ u (e x)) :
    ‖gradient (u ∘ e) x‖ = ‖gradient u (e x)‖ := by
  rw [gradient_comp_linearIsometryEquiv e hu, e.symm.norm_map]

/-- Orthogonal changes of coordinates preserve the genuine level-set integrals. -/
lemma lintegral_coarea_level_preimage_isometry {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (A : Set (EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (t : ℝ) :
    (∫⁻ x in (e ⁻¹' A) ∩ (u ∘ e) ⁻¹' {t}, g x
      ∂Measure.euclideanHausdorffMeasure (n - 1)) =
      ∫⁻ y in A ∩ u ⁻¹' {t}, g (e.symm y)
        ∂Measure.euclideanHausdorffMeasure (n - 1) := by
  have hp := e.toIsometryEquiv.measurePreserving_euclideanHausdorffMeasure (n - 1)
  have hmp := hp.restrict_preimage_emb e.toHomeomorph.measurableEmbedding (A ∩ u ⁻¹' {t})
  change MeasurePreserving e
    ((Measure.euclideanHausdorffMeasure (n - 1)).restrict (e ⁻¹' (A ∩ u ⁻¹' {t})))
    ((Measure.euclideanHausdorffMeasure (n - 1)).restrict (A ∩ u ⁻¹' {t})) at hmp
  have h := hmp.lintegral_comp_emb e.toHomeomorph.measurableEmbedding (g ∘ e.symm)
  simpa only [Function.comp_apply, e.symm_apply_apply, preimage_inter,
    preimage_comp] using h

/-- Weighted coarea is invariant under pullback by a Euclidean linear isometry. -/
theorem HasWeightedCoareaOn.comp_linearIsometryEquiv {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {A : Set (EuclideanSpace ℝ (Fin n))}
    (h : HasWeightedCoareaOn u A) (hA : MeasurableSet A)
    (hu : ∀ x ∈ A, DifferentiableAt ℝ u x)
    (e : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    HasWeightedCoareaOn (u ∘ e) (e ⁻¹' A) := by
  intro g hg
  obtain ⟨hm, he⟩ := h (g ∘ e.symm) (hg.comp e.symm.continuous.measurable)
  simp only [Function.comp_apply] at hm he
  have hfiber := lintegral_coarea_level_preimage_isometry e u A g
  refine ⟨?_, ?_⟩
  · simpa only [hfiber] using hm
  · simp_rw [hfiber]
    rw [← he]
    have hmp := e.measurePreserving.restrict_preimage_emb e.toHomeomorph.measurableEmbedding A
    have hchange := hmp.lintegral_comp_emb e.toHomeomorph.measurableEmbedding
      (fun y => g (e.symm y) * ENNReal.ofReal ‖gradient u y‖)
    simp only [e.symm_apply_apply] at hchange
    rw [← hchange]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (hA.preimage e.continuous.measurable)] with x hx
    rw [norm_gradient_comp_linearIsometryEquiv e (hu (e x) hx)]

/-- A coarea identity in rotated coordinates gives the original identity. -/
theorem HasWeightedCoareaOn.of_comp_linearIsometryEquiv {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {A : Set (EuclideanSpace ℝ (Fin n))}
    (e : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (h : HasWeightedCoareaOn (u ∘ e) (e ⁻¹' A)) (hA : MeasurableSet A)
    (hu : ∀ x ∈ A, DifferentiableAt ℝ u x) : HasWeightedCoareaOn u A := by
  have hder (x) (hx : x ∈ e ⁻¹' A) : DifferentiableAt ℝ (u ∘ e) x :=
    (hu (e x) hx).comp x e.toContinuousLinearEquiv.differentiableAt
  have ht := h.comp_linearIsometryEquiv (hA.preimage e.continuous.measurable) hder e.symm
  have hfun : (u ∘ e) ∘ e.symm = u := by ext x; simp
  have hset : e.symm ⁻¹' (e ⁻¹' A) = A := by ext x; simp
  simpa only [hfun, hset] using ht

/-- The coordinate permutation exchanging a chosen coordinate with the last one. -/
def coareaSwap {k : ℕ} (i : Fin (k + 1)) :
    EuclideanSpace ℝ (Fin (k + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (k + 1)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i (Fin.last k))

@[simp] lemma coareaSwap_apply {k : ℕ} (i j : Fin (k + 1))
    (x : EuclideanSpace ℝ (Fin (k + 1))) :
    coareaSwap i x j = x (Equiv.swap i (Fin.last k) j) := by
  rfl

@[simp] lemma coareaSwap_symm_apply {k : ℕ} (i j : Fin (k + 1))
    (x : EuclideanSpace ℝ (Fin (k + 1))) :
    (coareaSwap i).symm x j = x (Equiv.swap i (Fin.last k) j) := by
  simp [coareaSwap, LinearIsometryEquiv.piLpCongrLeft_symm,
    LinearIsometryEquiv.piLpCongrLeft_apply]

@[simp] lemma coareaSwap_apply_last {k : ℕ} (i : Fin (k + 1))
    (x : EuclideanSpace ℝ (Fin (k + 1))) : coareaSwap i x (Fin.last k) = x i := by
  simp

/-- A chosen nonzero derivative can always be placed in the last coordinate. -/
lemma gradient_comp_coareaSwap_last {k : ℕ} (i : Fin (k + 1))
    {u : EuclideanSpace ℝ (Fin (k + 1)) → ℝ} {x : EuclideanSpace ℝ (Fin (k + 1))}
    (hu : DifferentiableAt ℝ u (coareaSwap i x)) :
    gradient (u ∘ coareaSwap i) x (Fin.last k) = gradient u (coareaSwap i x) i := by
  rw [gradient_comp_linearIsometryEquiv (coareaSwap i) hu]
  simp

lemma exists_coareaSwap_nonzero_last {k : ℕ}
    {u : EuclideanSpace ℝ (Fin (k + 1)) → ℝ} {x : EuclideanSpace ℝ (Fin (k + 1))}
    (hu : DifferentiableAt ℝ u x) (hg : gradient u x ≠ 0) :
    ∃ i : Fin (k + 1),
      gradient (u ∘ coareaSwap i) ((coareaSwap i).symm x) (Fin.last k) ≠ 0 := by
  have hi : ∃ i : Fin (k + 1), gradient u x i ≠ 0 := by
    by_contra! h
    exact hg (PiLp.ext fun i => h i)
  obtain ⟨i, hi⟩ := hi
  refine ⟨i, ?_⟩
  have hux : DifferentiableAt ℝ u (coareaSwap i ((coareaSwap i).symm x)) := by simpa
  rw [gradient_comp_coareaSwap_last i hux, (coareaSwap i).apply_symm_apply]
  exact hi

end LiquidDrop
