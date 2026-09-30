module

public import NoCompromise.Regularity.GraphSlicesPolar
public import NoCompromise.Regularity.GraphSlicesPhases

@[expose] public section

/-! # Actual reduced-boundary points on almost every oriented vertical slice -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The actual slice variation is carried by the genuine reduced boundary,
and every nonzero jump in a canonical local representative lies there. -/
theorem IsDirectionalJumpDisintegration.ae_vertical_reducedBoundary
    {E : Set AmbientSpace} (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume)
    {τ : Measure AmbientSpace} {s : AmbientSpace → ℝ}
    {κ : EuclideanSpace ℝ (Fin 2) → Measure ℝ}
    {σ : EuclideanSpace ℝ (Fin 2) → ℝ → ℝ}
    {g : EuclideanSpace ℝ (Fin 2) → ℝ → ℝ → ℝ → ℝ}
    (h : IsDirectionalJumpDisintegration (E.indicator (fun _ => (1 : ℝ)))
      (LinearIsometryEquiv.refl ℝ AmbientSpace) τ s κ σ g) :
    ∀ᵐ p : EuclideanSpace ℝ (Fin 2),
      (∀ᵐ t ∂κ p, graphAppendN p t ∈ reducedBoundary E hE hmE) ∧
      ∀ a b t, t ∈ Ioo a b → oneDimensionalJump (g p a b) t ≠ 0 →
        graphAppendN p t ∈ reducedBoundary E hE hmE := by
  have hm := (measurableSet_reducedBoundary E hE hmE).compl
  have hz := h.polar.measure_compl_reducedBoundary_eq_zero hE hmE
  rw [h.variation_eq _ hm] at hz
  have hae := (lintegral_eq_zero_iff' (h.measurable_sections _ hm)).mp hz
  filter_upwards [h.slices, hae] with p hp hpzero
  have hmem : ∀ᵐ t ∂κ p, graphAppendN p t ∈ reducedBoundary E hE hmE :=
    ae_iff.mpr hpzero
  refine ⟨hmem, ?_⟩
  intro a b t ht hj
  by_contra hn
  have hatom : κ p {t} = 0 := measure_mono_null
    (singleton_subset_iff.mpr hn) hpzero
  have he := hp.1.oneDimensionalJump_eq_atom (hp.2 a b).ae_eq
    (hp.2 a b).leftContinuous ht
  rw [Measure.real, hatom, ENNReal.toReal_zero, zero_mul] at he
  exact hj he

/-- Positive signed jump number forces an actual reduced-boundary point in the
open half-height fiber for almost every base in the genuine phase region. -/
theorem HasLocallyFinitePerimeter.ae_exists_vertical_reducedBoundary_of_phases
    {E : Set AmbientSpace} (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume)
    {B : Set (EuclideanSpace ℝ (Fin 2))} (hB : MeasurableSet B)
    (hL : E.indicator (fun _ => (1 : ℝ)) =ᵐ[volume.restrict
      {z | graphProjectionN 2 z ∈ B ∧ z 2 ∈ Ioo (-(3 / 4)) (-(1 / 4))}] fun _ => 1)
    (hU : E.indicator (fun _ => (1 : ℝ)) =ᵐ[volume.restrict
      {z | graphProjectionN 2 z ∈ B ∧ z 2 ∈ Ioo (1 / 4) (3 / 4)}] fun _ => 0) :
    ∀ᵐ p : EuclideanSpace ℝ (Fin 2), p ∈ B →
      ∃ t ∈ Ioo (-(1 / 2)) (1 / 2), graphAppendN p t ∈ reducedBoundary E hE hmE := by
  obtain ⟨τ, s, κ, σ, g, hd, hj⟩ := hE.exists_oriented_vertical_slices hmE hB hL hU
  filter_upwards [hj, hd.ae_vertical_reducedBoundary hE hmE] with p hp hpR hpB
  have hi := (hp hpB).2.2.1
  have hne : κ p (Ioo (-(1 / 2)) (1 / 2)) ≠ 0 := by
    intro hz
    rw [Measure.restrict_eq_zero.mpr hz, integral_zero_measure] at hi
    norm_num at hi
  exact Measure.exists_mem_of_measure_ne_zero_of_ae hne (ae_restrict_of_ae hpR.1)

end LiquidDrop
