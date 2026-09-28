import NoCompromise.Regularity.GraphSlicesOneDimensional

/-! # Actual phase bands and the almost-everywhere oriented vertical jump count -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Vertical real coordinates preserve the actual Euclidean volume. -/
lemma measurePreserving_graphAppendN (n : ℕ) :
    MeasurePreserving (fun p : EuclideanSpace ℝ (Fin n) × ℝ => graphAppendN p.1 p.2)
      (volume.prod volume) volume := by
  exact ((euclideanLastEquiv_measurePreserving n).symm
    (euclideanLastEquiv n).toHomeomorph.toMeasurableEquiv).comp
      Measure.measurePreserving_swap

/-- An actual AE phase on a vertical product gives the same phase on almost
every real line. No chosen pointwise representative is required. -/
lemma ae_vertical_slice_eq_const_of_phase
    {f : AmbientSpace → ℝ} {B : Set (EuclideanSpace ℝ (Fin 2))} {a b q : ℝ}
    (hB : MeasurableSet B)
    (hf : f =ᵐ[volume.restrict
      {z | graphProjectionN 2 z ∈ B ∧ z 2 ∈ Ioo a b}] fun _ => q) :
    ∀ᵐ p : EuclideanSpace ℝ (Fin 2), p ∈ B →
      (fun t : ℝ => f (graphAppendN p t)) =ᵐ[volume.restrict (Ioo a b)] fun _ => q := by
  have hQ : MeasurableSet {z : AmbientSpace |
      graphProjectionN 2 z ∈ B ∧ z 2 ∈ Ioo a b} :=
    ((graphProjectionN 2).measurable hB).inter
      ((EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).measurable measurableSet_Ioo)
  have he := (ae_restrict_iff' hQ).mp hf
  have hp := Measure.ae_ae_of_ae_prod
    ((measurePreserving_graphAppendN 2).quasiMeasurePreserving.ae he)
  filter_upwards [hp] with p hp hpB
  apply (ae_restrict_iff' measurableSet_Ioo).mpr
  filter_upwards [hp] with t ht htI
  apply ht
  change graphProjectionN 2 (graphAppendN p t) ∈ B ∧
    graphAppendN p t (Fin.last 2) ∈ Ioo a b
  simpa only [mem_ofPred_eq, graphProjectionN_append, graphAppendN_last] using
    And.intro hpB htI

/-- The full jump disintegration may be chosen in the identity frame itself,
even for a Lebesgue-measurable original set. -/
theorem HasLocallyFinitePerimeter.exists_vertical_jump_disintegration
    {E : Set AmbientSpace} (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) :
    ∃ τ s κ σ g, IsDirectionalJumpDisintegration (E.indicator (fun _ => (1 : ℝ)))
      (LinearIsometryEquiv.refl ℝ AmbientSpace) τ s κ σ g := by
  classical
  let B := toMeasurable volume E
  let f := B.indicator (fun _ => (1 : ℝ))
  have he : f =ᵐ[volume] E.indicator (fun _ => (1 : ℝ)) :=
    indicator_ae_eq_of_ae_eq_set hmE.toMeasurable_ae_eq
  have hf : IsLocallyBVOn f univ :=
    (hE.isLocallyBVOn_indicator hmE univ).congr_ae (by simpa using he.symm)
  have hm : Measurable f := measurable_const.indicator (measurableSet_toMeasurable volume E)
  have hb (z) : f z ∈ ({0, 1} : Set ℝ) := by
    by_cases hz : z ∈ B <;> simp [f, hz]
  obtain ⟨τ, s, κ, σ, g, hd⟩ :=
    hf.exists_directionalJumpDisintegration hm hb (LinearIsometryEquiv.refl ℝ AmbientSpace)
  exact ⟨τ, s, κ, σ, g, hd.congr_ae he⟩

/-- Cleared lower-one and upper-zero bands give the actual slice BV property,
finite jumps, and signed outward jump number one in the half-height interval. -/
theorem HasLocallyFinitePerimeter.exists_oriented_vertical_slices
    {E : Set AmbientSpace} (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume)
    {B : Set (EuclideanSpace ℝ (Fin 2))} (hB : MeasurableSet B)
    (hL : E.indicator (fun _ => (1 : ℝ)) =ᵐ[volume.restrict
      {z | graphProjectionN 2 z ∈ B ∧ z 2 ∈ Ioo (-(3 / 4)) (-(1 / 4))}] fun _ => 1)
    (hU : E.indicator (fun _ => (1 : ℝ)) =ᵐ[volume.restrict
      {z | graphProjectionN 2 z ∈ B ∧ z 2 ∈ Ioo (1 / 4) (3 / 4)}] fun _ => 0) :
    ∃ τ s κ σ g,
      IsDirectionalJumpDisintegration (E.indicator (fun _ => (1 : ℝ)))
        (LinearIsometryEquiv.refl ℝ AmbientSpace) τ s κ σ g ∧
      ∀ᵐ p : EuclideanSpace ℝ (Fin 2), p ∈ B →
        IsBinaryBVRepresentativeOn
          (fun t => E.indicator (fun _ => (1 : ℝ)) (graphAppendN p t))
          (g p (-(3 / 4)) (3 / 4)) (-(3 / 4)) (3 / 4) ∧
        {t ∈ Ioo (-(1 / 2)) (1 / 2) |
          oneDimensionalJump (g p (-(3 / 4)) (3 / 4)) t ≠ 0}.Finite ∧
        (∫ t in Ioo (-(1 / 2)) (1 / 2), σ p t ∂κ p) = -1 ∧
        -(∑ᶠ t : ℝ, (Ioo (-(1 / 2)) (1 / 2)).indicator
          (oneDimensionalJump (g p (-(3 / 4)) (3 / 4))) t) = 1 := by
  obtain ⟨τ, s, κ, σ, g, hd⟩ := hE.exists_vertical_jump_disintegration hmE
  refine ⟨τ, s, κ, σ, g, hd, ?_⟩
  filter_upwards [hd.slices, ae_vertical_slice_eq_const_of_phase hB hL,
    ae_vertical_slice_eq_const_of_phase hB hU] with p hp hpL hpU hpB
  have hg := hp.2 (-(3 / 4)) (3 / 4)
  refine ⟨hg, ?_⟩
  exact hg.oriented_jump_count hp.1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (hpL hpB) (hpU hpB)

end LiquidDrop
