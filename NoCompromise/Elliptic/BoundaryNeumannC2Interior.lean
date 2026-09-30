module

public import NoCompromise.Elliptic.BoundaryNeumannC2Data
public import NoCompromise.Elliptic.NondivSchauderScalingBall
public import NoCompromise.Elliptic.BoundaryC2

@[expose] public section

/-!
# Interior C² regularity from the Neumann data

The vector-source weak equation is converted to the repository's distributional
nondivergence convention. The existing interior Schauder theorem then applies on
every ball compactly contained in the open half ball.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

theorem boundary_neumann_c2_weak_nondivergence {α lam cap M N : ℝ}
    (hα : 0 < α) (hM : 0 ≤ M) (hN : 0 ≤ N)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {w : EuclideanSpace ℝ (Fin 3) → ℝ}
    (d : BoundaryNeumannClosedData α lam cap M N A H w) :
    IsWeakNondivergenceEquationOn A (fun _ => 0) w (boundaryNeumannC2Source A H w)
      (boundaryHalfBall 1) := by
  have hU := isOpen_boundaryHalfBall (1 : ℝ)
  have hA := d.coefficient.contDiff.mono subset_closure
  have hw := d.solution.contDiff.mono subset_closure
  have hH := d.source.contDiff.mono subset_closure
  have hf := (boundary_neumann_c2_source_holder hM hN d).1.nondiv_continuousOn hα
    |>.mono subset_closure
  apply (isWeakNondivergenceEquationOn_iff_divergence hU hA continuousOn_const hw hf).mpr
  intro φ hφ hcφ hsφ
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  have hsource : nondivDivergenceSource A (fun _ => 0) w (boundaryNeumannC2Source A H w) =
      divergenceN H := by
    funext x
    simp only [nondivDivergenceSource, boundaryNeumannC2Source, sub_zero, sub_add_cancel]
  rw [hsource]
  have hgrad := continuousOn_gradient_of_contDiffOn hU hw
  have hcgrad : HasCompactSupport (gradient φ) :=
    hcφ.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset φ)
  have hiA : Integrable (fun x => inner ℝ (A x (gradient w x)) (gradient φ x)) := by
    simpa only [real_inner_comm] using integrable_inner_compact_factor_on
      ((hA.continuousOn.clm_apply hgrad).locallyIntegrableOn hU.measurableSet)
      (continuous_gradient_of_contDiff hφ1) hcgrad ((tsupport_gradient_subset φ).trans hsφ)
  have hiH : Integrable (fun x => inner ℝ (H x) (gradient φ x)) := by
    simpa only [real_inner_comm] using integrable_inner_compact_factor_on
      (hH.continuousOn.locallyIntegrableOn hU.measurableSet)
      (continuous_gradient_of_contDiff hφ1) hcgrad ((tsupport_gradient_subset φ).trans hsφ)
  have he : (∫ x, inner ℝ (A x (gradient w x) - H x) (gradient φ x)) = 0 := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := boundaryHalfBall 1)
      (fun x hx => by
        rw [gradient_eq_zero_of_notMem_tsupport (fun ht => hx (hsφ ht)), inner_zero_right])]
    exact d.equation φ hφ1 hcφ (hsφ.trans inter_subset_left)
  simp only [inner_sub_left] at he
  rw [integral_sub hiA hiH] at he
  have hparts := boundary_neumann_c2_integral_divergence hU hH hφ1 hcφ hsφ
  linarith

/-- The interior C² hypothesis needed in the pointwise calculation follows from
the original closed data by the existing interior nondivergence Schauder theorem. -/
theorem boundary_neumann_interior_c2 {α lam cap M N : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hM : 0 ≤ M) (hN : 0 ≤ N)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {w : EuclideanSpace ℝ (Fin 3) → ℝ}
    (d : BoundaryNeumannClosedData α lam cap M N A H w) :
    BoundaryNeumannInteriorC2 w := by
  have he := boundary_neumann_c2_weak_nondivergence hα hM hN d
  have hf := (boundary_neumann_c2_source_holder hM hN d).1
  intro x hx
  have hlamcap : lam ≤ cap := by
    have hell := elliptic_diagonal_entry_ge (d.elliptic x (subset_closure hx)) (0 : Fin 3)
    have hn : ‖A x (EuclideanSpace.single (0 : Fin 3) 1)‖ ≤ cap := by
      simpa only [PiLp.norm_single, norm_one, mul_one] using
        (A x).le_opNorm (EuclideanSpace.single (0 : Fin 3) 1) |>.trans
          (mul_le_mul_of_nonneg_right (d.coefficient_bound x (subset_closure hx)) (norm_nonneg _))
    have hi := real_inner_le_norm (A x (EuclideanSpace.single (0 : Fin 3) 1))
      (EuclideanSpace.single (0 : Fin 3) 1)
    simp only [PiLp.norm_single, norm_one, mul_one] at hi
    exact hell.trans (hi.trans hn)
  obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.mp (isOpen_boundaryHalfBall 1) x hx
  let r := min r₀ (1 / 2 : ℝ)
  have hr : 0 < r := lt_min hr₀ (by norm_num)
  have hr1 : r ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hsub : ball x r ⊆ boundaryHalfBall 1 := (ball_subset_ball (min_le_left _ _)).trans hball
  have hclosed : ball x r ⊆ closure (boundaryHalfBall 1) := hsub.trans subset_closure
  obtain ⟨hA, hAb⟩ := d.coefficient.mono hclosed
  obtain ⟨hw, _⟩ := d.solution.mono hclosed
  obtain ⟨hf', _⟩ := schauder_holder_mono hf hclosed
  have hb : HasFiniteHolderNormOn α (fun _ : EuclideanSpace ℝ (Fin 3) =>
      (0 : EuclideanSpace ℝ (Fin 3))) (ball x r) := by
    apply HasFiniteHolderNormOn.of_bounds (A := 0) (B := 0) (by norm_num) (by norm_num)
    · intro y hy
      simp
    · intro y hy z hz
      simp
  have hbb : holderNorm α (fun _ : EuclideanSpace ℝ (Fin 3) =>
      (0 : EuclideanSpace ℝ (Fin 3))) (ball x r) ≤ M := by
    apply le_trans (b := 0)
    · apply (holderNorm_le (A := 0) (B := 0) (by norm_num) (by norm_num) ?_ ?_).trans_eq
        (by norm_num)
      · intro y hy
        simp
      · intro y hy z hz
        simp
    · exact hM
  obtain ⟨C, _, hreg⟩ := nondiv_schauder_c1_ball (n := 3) (by norm_num) (by norm_num)
    hα hα1 hlam hlamcap hM
  have hlocal := (hreg x r hr hr1 A (fun _ => 0) w (boundaryNeumannC2Source A H w)
    hA hb hw hf' (hAb.trans d.coefficient_norm) hbb
    (fun y hy => d.coefficient_bound y (hclosed hy))
    (fun y hy v => by simpa only [real_inner_comm] using d.elliptic y (hclosed hy) v)
    (he.mono hsub)).1.contDiff
  exact (hlocal.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self (half_pos hr)))).contDiffWithinAt

end LiquidDrop
