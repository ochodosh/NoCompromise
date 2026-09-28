import NoCompromise.Elliptic.BoundaryNeumannQuotient
import NoCompromise.Elliptic.NondivSchauderScalingNorm

/-! Uniform Hölder estimates using only the original closed-half-ball C¹,α data. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- Explicit up-to-the-face data for the homogeneous conormal problem. The
normal derivative is assumed zero on the face, as in the bootstrap hypothesis.
All derivatives use the existing `HasC1HolderOn` convention. -/
structure BoundaryNeumannClosedData (α lam cap M N : ℝ)
    (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3))
    (H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (w : EuclideanSpace ℝ (Fin 3) → ℝ) : Prop where
  coefficient : HasC1HolderOn α A (closure (boundaryHalfBall 1))
  source : HasC1HolderOn α H (closure (boundaryHalfBall 1))
  solution : HasC1HolderOn α w (closure (boundaryHalfBall 1))
  coefficient_norm : nondivC1HolderNorm α A (closure (boundaryHalfBall 1)) ≤ M
  norm_bound : nondivC1HolderNorm α w (closure (boundaryHalfBall 1)) +
    nondivC1HolderNorm α H (closure (boundaryHalfBall 1)) ≤ N
  coefficient_bound : ∀ x ∈ closure (boundaryHalfBall 1), ‖A x‖ ≤ cap
  elliptic : ∀ x ∈ closure (boundaryHalfBall 1), ∀ v,
    lam * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v
  cross_zero : ∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 →
    ∀ j : Fin 3, j ≠ Fin.last 2 →
      A x (EuclideanSpace.single j 1) (Fin.last 2) = 0 ∧
      A x (EuclideanSpace.single (Fin.last 2) 1) j = 0
  source_normal_zero : ∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 →
    H x (Fin.last 2) = 0
  solution_normal_zero : ∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 →
    gradient w x (Fin.last 2) = 0
  equation : IsBoundaryNeumannEquationOn A (gradient w) H 1

lemma boundary_neumann_quotient_datum_continuous {α r s : ℝ} (hα : 0 < α)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {w : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hA : HasC1HolderOn α A (closure (boundaryHalfBall 1)))
    (hH : HasC1HolderOn α H (closure (boundaryHalfBall 1)))
    (hw : HasC1HolderOn α w (closure (boundaryHalfBall 1)))
    {i : Fin 3} (hi : i ≠ Fin.last 2) (hs : |s| ≤ 1 - r) :
    ContinuousOn (boundaryNeumannQuotientDatum A (gradient w) H i s)
      (closure (boundaryHalfBall r)) := by
  have hr : r ≤ 1 := by linarith [abs_nonneg s]
  have hsub := closure_mono (boundaryHalfBall_mono hr)
  have hm : MapsTo (fun x => x + s • EuclideanSpace.single i (1 : ℝ))
      (closure (boundaryHalfBall r)) (closure (boundaryHalfBall 1)) := by
    intro x hx
    simpa only [one_smul] using boundary_nondiv_closed_segment hi hs hx (t := 1) (by simp)
  have hcA := ((hA.contDiff.continuousOn.comp
    (continuous_id.add continuous_const).continuousOn hm).sub
      (hA.contDiff.continuousOn.mono hsub)).const_smul s⁻¹
  have hcH := ((hH.contDiff.continuousOn.comp
    (continuous_id.add continuous_const).continuousOn hm).sub
      (hH.contDiff.continuousOn.mono hsub)).const_smul s⁻¹
  exact hcH.sub (hcA.clm_apply ((hw.gradient_holder.1.nondiv_continuousOn hα).comp
    (continuous_id.add continuous_const).continuousOn hm))

/-- A quantitative open-half-ball bound for the actual, shifted-gradient datum. -/
lemma boundary_neumann_quotient_datum_norm {α M r s : ℝ}
    (hα : 0 < α) (hM : 0 ≤ M)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {w : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hA : HasC1HolderOn α A (boundaryHalfBall 1))
    (hH : HasC1HolderOn α H (boundaryHalfBall 1))
    (hw : HasC1HolderOn α w (boundaryHalfBall 1))
    (hbA : nondivC1HolderNorm α A (boundaryHalfBall 1) ≤ M)
    {i : Fin 3} (hi : i ≠ Fin.last 2) (hs0 : s ≠ 0) (hs : |s| ≤ 1 - r) :
    HasFiniteHolderNormOn α (boundaryNeumannQuotientDatum A (gradient w) H i s)
      (boundaryHalfBall r) ∧
    holderNorm α (boundaryNeumannQuotientDatum A (gradient w) H i s) (boundaryHalfBall r) ≤
      (1 + 3 * M) * (nondivC1HolderNorm α w (boundaryHalfBall 1) +
        nondivC1HolderNorm α H (boundaryHalfBall 1)) := by
  have hseg : ∀ x ∈ boundaryHalfBall r, ∀ t ∈ Icc (0 : ℝ) 1,
      x + t • (s • EuclideanSpace.single i 1) ∈ boundaryHalfBall 1 :=
    fun _ hx _ ht => boundary_nondiv_segment_mem_halfBall hi hs hx ht
  obtain ⟨hδA, hbδA⟩ := nondiv_coordinateDifferenceQuotient_holder
    (isOpen_boundaryHalfBall 1) hA i hs0 hseg
  obtain ⟨hδH, hbδH⟩ := nondiv_coordinateDifferenceQuotient_holder
    (isOpen_boundaryHalfBall 1) hH i hs0 hseg
  obtain ⟨hF, hbF⟩ := nondiv_holder_comp_contraction hα.le hw.gradient_holder.1
    (fun _ hx => boundaryHalfBall_add_tangential hi hs hx)
    (fun _ _ _ _ => by rw [add_sub_add_right_eq_sub])
  obtain ⟨hP, hbP⟩ := nondiv_holder_clm_apply hδA hF
  obtain ⟨hG, hbG⟩ := nondiv_holder_sub hδH hP
  refine ⟨hG, hbG.trans ?_⟩
  have hB : holderNorm α (coordinateDifferenceQuotient i s A) (boundaryHalfBall r) ≤ M :=
    hbδA.trans (hA.derivative_norm_le.trans hbA)
  have hW := hbF.trans (hw.gradient_holder.2.trans hw.derivative_norm_le)
  have hPbound := hbP.trans (mul_le_mul (mul_le_mul_of_nonneg_left hB (by norm_num))
    hW hF.norm_nonneg (by positivity))
  have hHbound := hbδH.trans hH.derivative_norm_le
  have htotal := add_le_add hHbound hPbound
  apply htotal.trans
  nlinarith [hw.norm_nonneg, hH.norm_nonneg]

/-- Uniform pointwise size and Hölder modulus of the quotient datum on the
closed smaller half ball. The constant is fixed before all data and steps. -/
theorem boundary_neumann_quotient_datum_holder {α M : ℝ}
    (hα : 0 < α) (hM : 0 ≤ M) :
    ∃ C > 0, ∀ (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
        EuclideanSpace ℝ (Fin 3))
      (H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (w : EuclideanSpace ℝ (Fin 3) → ℝ),
      HasC1HolderOn α A (closure (boundaryHalfBall 1)) →
      HasC1HolderOn α H (closure (boundaryHalfBall 1)) →
      HasC1HolderOn α w (closure (boundaryHalfBall 1)) →
      nondivC1HolderNorm α A (closure (boundaryHalfBall 1)) ≤ M →
      ∀ (r s : ℝ) (i : Fin 3), i ≠ Fin.last 2 → s ≠ 0 → |s| ≤ 1 - r →
      let B := C * (nondivC1HolderNorm α w (closure (boundaryHalfBall 1)) +
        nondivC1HolderNorm α H (closure (boundaryHalfBall 1)))
      (∀ x ∈ closure (boundaryHalfBall r),
        ‖boundaryNeumannQuotientDatum A (gradient w) H i s x‖ ≤ B) ∧
      ∀ x ∈ closure (boundaryHalfBall r), ∀ y ∈ closure (boundaryHalfBall r),
        ‖boundaryNeumannQuotientDatum A (gradient w) H i s x -
          boundaryNeumannQuotientDatum A (gradient w) H i s y‖ ≤ B * dist x y ^ α := by
  refine ⟨1 + 3 * M, by positivity, ?_⟩
  intro A H w hA hH hw hbA r s i hi hs0 hs
  dsimp only
  obtain ⟨hAo, hbAo⟩ := hA.mono subset_closure
  obtain ⟨hHo, hbHo⟩ := hH.mono subset_closure
  obtain ⟨hwo, hbwo⟩ := hw.mono subset_closure
  obtain ⟨hG, hbG⟩ := boundary_neumann_quotient_datum_norm hα hM hAo hHo hwo
    (hbAo.trans hbA) hi hs0 hs
  have hcG := boundary_neumann_quotient_datum_continuous hα hA hH hw hi hs
  have hb := hbG.trans (mul_le_mul_of_nonneg_left (add_le_add hbwo hbHo) (by positivity))
  constructor
  · exact le_on_closure (fun _ hx => (hG.nondiv_norm_le hx).trans hb)
      hcG.norm continuousOn_const
  · apply boundary_nondiv_holder_on_closure hα.le hcG
    intro x hx y hy
    apply (hG.nondiv_norm_sub_le hx hy).trans
    rw [dist_eq_norm]
    exact mul_le_mul_of_nonneg_right
      ((le_add_of_nonneg_left (holderUniformNorm_nonneg hG.uniform_bounded)).trans hb)
      (Real.rpow_nonneg (norm_nonneg _) _)

/-- The quotient carries its actual weak gradient on every smaller half ball. -/
lemma BoundaryNeumannClosedData.quotient_h1 {α lam cap M N r s : ℝ}
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {w : EuclideanSpace ℝ (Fin 3) → ℝ}
    (d : BoundaryNeumannClosedData α lam cap M N A H w)
    {i : Fin 3} (hi : i ≠ Fin.last 2) (hs : |s| ≤ 1 - r) :
    HasH1GradientOn (coordinateDifferenceQuotient i s w)
      (coordinateDifferenceQuotient i s (gradient w)) (boundaryHalfBall r) := by
  have hr : r ≤ 1 := by linarith [abs_nonneg s]
  exact ((d.solution.mono subset_closure).1.hasH1GradientOn (isOpen_boundaryHalfBall 1)
    (isBounded_ball.subset inter_subset_left)).coordinateDifferenceQuotient
    (isOpen_boundaryHalfBall 1) (isOpen_boundaryHalfBall r) (boundaryHalfBall_mono hr)
    i s (fun _ hx => boundaryHalfBall_add_tangential hi hs hx)

lemma BoundaryNeumannClosedData.quotient_equation {α lam cap M N r s : ℝ}
    (hα : 0 < α)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {w : EuclideanSpace ℝ (Fin 3) → ℝ}
    (d : BoundaryNeumannClosedData α lam cap M N A H w)
    {i : Fin 3} (hi : i ≠ Fin.last 2) (hs : |s| ≤ 1 - r) :
    IsBoundaryNeumannEquationOn A (coordinateDifferenceQuotient i s (gradient w))
      (boundaryNeumannQuotientDatum A (gradient w) H i s) r ∧
    ∀ x ∈ closure (boundaryHalfBall r), x (Fin.last 2) = 0 →
      boundaryNeumannQuotientDatum A (gradient w) H i s x (Fin.last 2) = 0 :=
  boundary_neumann_quotient_equation hi hs d.coefficient.contDiff.continuousOn
    (d.solution.gradient_holder.1.nondiv_continuousOn hα) d.source.contDiff.continuousOn
    d.equation (fun x hx hflat j hj => (d.cross_zero x hx hflat j hj).1)
    d.source_normal_zero d.solution_normal_zero

end LiquidDrop
