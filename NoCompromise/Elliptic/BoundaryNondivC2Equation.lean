module

public import NoCompromise.Elliptic.BoundaryNeumannC2Interior
public import NoCompromise.Elliptic.BoundaryNondivC1

@[expose] public section

/-!
# The classical nondivergence equation and interior C² for the boundary problem

A C² solution of the weak nondivergence equation satisfies it pointwise. For the
zero-trace boundary data, interior C² regularity on the open half ball follows
from the interior nondivergence Schauder theorem applied on small balls.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- A C² solution of the weak nondivergence equation satisfies it classically,
with the row-column convention `Aᵢⱼ = (A eⱼ)ᵢ` and `∂ᵢ(∂ⱼz)`. -/
theorem IsWeakNondivergenceEquationOn.pointwise_of_contDiffOn
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    {b : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {z f : EuclideanSpace ℝ (Fin 3) → ℝ} {U : Set (EuclideanSpace ℝ (Fin 3))}
    (hU : IsOpen U) (hA : ContDiffOn ℝ 1 A U) (hb : ContinuousOn b U)
    (hz : ContDiffOn ℝ 2 z U) (hf : ContinuousOn f U)
    (he : IsWeakNondivergenceEquationOn A b z f U) :
    ∀ x ∈ U,
      (∑ i, ∑ j, A x (EuclideanSpace.single j 1) i *
        fderiv ℝ (fun y => fderiv ℝ z y (EuclideanSpace.single j 1)) x
          (EuclideanSpace.single i 1)) + inner ℝ (b x) (gradient z x) = f x := by
  have hz1 : ContDiffOn ℝ 1 z U := hz.of_le (by norm_num)
  have hDz : ContDiffOn ℝ 1 (fderiv ℝ z) U := hz.fderiv_of_isOpen hU (by norm_num)
  have hGz : ContDiffOn ℝ 1 (gradient z) U :=
    (toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm.toContinuousLinearEquiv.contDiff
      |>.comp_contDiffOn hDz
  have hF : ContDiffOn ℝ 1 (fun y => A y (gradient z y)) U := hA.clm_apply hGz
  have hs := (isWeakNondivergenceEquationOn_iff_divergence hU hA hb hz1 hf).mp he
  let g := nondivDivergenceSource A b z f
  have hgc : ContinuousOn g U := by
    have hG := continuousOn_gradient_of_contDiffOn hU hz1
    have hD := continuousOn_nondivCoefficientDivergence hU hA
    exact hf.add ((hD.sub hb).inner hG)
  have hdc := boundary_neumann_c2_continuousOn_divergence hU hF
  have hdiv : EqOn (divergenceN (fun y => A y (gradient z y))) g U := by
    have hz0 : ∀ᵐ x ∂volume, x ∈ U →
        (divergenceN (fun y => A y (gradient z y)) - g) x = 0 := by
      apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        ((hdc.sub hgc).locallyIntegrableOn hU.measurableSet)
      intro φ hφ hcφ hsφ
      have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
      have hparts := boundary_neumann_c2_integral_divergence hU hF hφ1 hcφ hsφ
      have hweak := hs φ hφ hcφ hsφ
      have hi₁ := integrable_mul_compact_factor_on (hdc.locallyIntegrableOn hU.measurableSet)
        hφ.continuous hcφ hsφ
      have hi₂ := integrable_mul_compact_factor_on (hgc.locallyIntegrableOn hU.measurableSet)
        hφ.continuous hcφ hsφ
      have hsplit : (∫ x, φ x • (divergenceN (fun y => A y (gradient z y)) - g) x) =
          (∫ x, φ x * divergenceN (fun y => A y (gradient z y)) x) -
            ∫ x, φ x * g x := by
        rw [← integral_sub hi₁ hi₂]
        apply integral_congr_ae
        filter_upwards with x
        simp only [Pi.sub_apply, smul_eq_mul, mul_sub]
      rw [hsplit]
      linarith
    have hae : ∀ᵐ x ∂volume.restrict U,
        divergenceN (fun y => A y (gradient z y)) x = g x := by
      filter_upwards [(ae_restrict_iff' hU.measurableSet).mpr hz0] with x hx
      exact sub_eq_zero.mp hx
    exact Measure.eqOn_open_of_ae_eq hae hU hdc hgc
  intro x hx
  have hdG := (hGz.contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero
  have hpartial (i j : Fin 3) :
      fderiv ℝ (gradient z) x (EuclideanSpace.single i 1) j =
        fderiv ℝ (fun y => fderiv ℝ z y (EuclideanSpace.single j 1)) x
          (EuclideanSpace.single i 1) := by
    have he' : (fun y => fderiv ℝ z y (EuclideanSpace.single j 1)) =
        fun y => gradient z y j :=
      funext fun y => (gradient_apply_eq_fderiv_single z y j).symm
    rw [he']
    change _ = fderiv ℝ ((EuclideanSpace.proj j) ∘ gradient z) x _
    rw [((EuclideanSpace.proj j).hasFDerivAt.comp x hdG.hasFDerivAt).fderiv]
    rfl
  have hdA := (hA.contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero
  have hp := boundary_neumann_c2_divergence_product hdA hdG
    (differentiableAt_const (0 : EuclideanSpace ℝ (Fin 3)))
  have hzero : divergenceN (fun _ : EuclideanSpace ℝ (Fin 3) =>
      (0 : EuclideanSpace ℝ (Fin 3))) x = 0 := by
    simp [divergenceN]
  simp only [sub_zero] at hp
  rw [hzero, sub_zero, hdiv hx] at hp
  have hexp := boundary_neumann_c2_source_expansion A (fun _ => 0) z x
  simp only [boundaryNeumannC2Source] at hexp
  rw [hzero, zero_sub] at hexp
  simp only [hpartial, gradient_apply_eq_fderiv_single] at hp
  have hg : g x = f x + inner ℝ (nondivCoefficientDivergence A x) (gradient z x) -
      inner ℝ (b x) (gradient z x) := by
    simp only [g, nondivDivergenceSource, inner_sub_left]
    ring
  rw [hg] at hp
  linarith

/-- Interior C² regularity of the zero-trace boundary nondivergence solution on the
open unit half ball. -/
theorem boundary_nondiv_interior_c2 {α lam cap M N : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hlamcap : lam ≤ cap) (hM : 0 ≤ M)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    {b : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {z f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (d : BoundaryNondivClosedData α lam cap M N A b z f) :
    ContDiffOn ℝ 2 z (boundaryHalfBall 1) := by
  intro x hx
  obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.mp (isOpen_boundaryHalfBall 1) x hx
  let r := min r₀ (1 / 2 : ℝ)
  have hr : 0 < r := lt_min hr₀ (by norm_num)
  have hr1 : r ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hsub : ball x r ⊆ boundaryHalfBall 1 := (ball_subset_ball (min_le_left _ _)).trans hball
  have hclosed : ball x r ⊆ closure (boundaryHalfBall 1) := hsub.trans subset_closure
  obtain ⟨hA, hAb⟩ := d.coefficient.mono hclosed
  obtain ⟨hz, _⟩ := d.solution.mono hclosed
  obtain ⟨hb, hbb⟩ := schauder_holder_mono d.drift hclosed
  obtain ⟨hf, _⟩ := schauder_holder_mono d.source hclosed
  obtain ⟨C, _, hreg⟩ := nondiv_schauder_c1_ball (n := 3) (by norm_num) (by norm_num)
    hα hα1 hlam hlamcap hM
  have hlocal := (hreg x r hr hr1 A b z f hA hb hz hf (hAb.trans d.coefficient_norm)
    (hbb.trans d.drift_norm)
    (fun y hy => d.coefficient_bound y (hclosed hy))
    (fun y hy v => d.elliptic y (hclosed hy) v)
    (d.equation.mono hsub)).1.contDiff
  exact (hlocal.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self (half_pos hr)))).contDiffWithinAt

end LiquidDrop
