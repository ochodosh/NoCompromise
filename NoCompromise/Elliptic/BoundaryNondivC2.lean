module

public import NoCompromise.Elliptic.BoundaryNondivC2Equation
public import NoCompromise.Elliptic.BoundaryNondivTangential
public import NoCompromise.Elliptic.BoundaryNeumannC2

@[expose] public section

/-!
# Boundary C²,α estimates for the zero-trace nondivergence problem

The tangential estimates of `boundary_nondiv_tangential_derivative_c1_holder` are
transported back to original coordinates, where they live on the fixed upper slab
`boundaryNondivC2Slab = (3/4) • boundaryC1UpperSlab`. Interior C² regularity gives
symmetry of the Hessian, and the pointwise equation, whose `a₃₃` is bounded below,
is solved algebraically for `∂₃₃z`. All constants are chosen before the data.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- The upper slab in original coordinates: `(3/4) • boundaryC1UpperSlab`. -/
def boundaryNondivC2Slab : Set (EuclideanSpace ℝ (Fin 3)) :=
  (fun x => (4 / 3 : ℝ) • x) ⁻¹' boundaryC1UpperSlab

lemma isOpen_boundaryNondivC2Slab : IsOpen boundaryNondivC2Slab :=
  isOpen_boundaryC1UpperSlab.preimage (continuous_const_smul _)

lemma boundaryNondivC2Slab_subset : boundaryNondivC2Slab ⊆ boundaryHalfBall 1 := by
  intro x hx
  have h := boundary_nondiv_scale_mem (boundaryC1UpperSlab_subset hx)
  rw [smul_smul] at h
  norm_num at h
  exact boundaryHalfBall_mono (by norm_num) h

/-- The closure of the slab contains the flat disk of radius `15/32`. -/
lemma boundaryNondivC2Slab_face_mem_closure {p : EuclideanSpace ℝ (Fin 2)}
    (hp : ‖p‖ < 15 / 32) : graphAppendN p 0 ∈ closure boundaryNondivC2Slab := by
  have hc : Continuous (fun t : ℝ => graphAppendN p t) := by
    change Continuous (fun t : ℝ => graphBaseN 2 p + t • EuclideanSpace.single (Fin.last 2) 1)
    exact continuous_const.add (continuous_id.smul continuous_const)
  have ht : Tendsto (fun t : ℝ => graphAppendN p t) (𝓝[>] 0) (𝓝 (graphAppendN p 0)) :=
    (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto ht
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2097152 by norm_num)] with t ht
  obtain ⟨ht0, ht1⟩ := ht
  have hlast : ((4 / 3 : ℝ) • graphAppendN p t) (Fin.last 2) = 4 / 3 * t := by
    simp only [PiLp.smul_apply, graphAppendN_last, smul_eq_mul]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · change graphProjectionN 2 ((4 / 3 : ℝ) • graphAppendN p t) ∈ ball 0 (5 / 8)
    rw [map_smul, graphProjectionN_append, mem_ball, dist_zero_right, norm_smul,
      Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 3)]
    linarith
  · change |((4 / 3 : ℝ) • graphAppendN p t) (Fin.last 2)| < 1 / 1048576
    rw [hlast, abs_of_pos (by positivity)]
    linarith
  · change 0 < ((4 / 3 : ℝ) • graphAppendN p t) (Fin.last 2)
    rw [hlast]
    positivity

/-- In original coordinates, every tangential first derivative is differentiable on
the slab, and all its first derivatives are uniformly bounded and α-Hölder. -/
theorem boundary_nondiv_tangential_second_derivatives {α lam cap M N : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hlamcap : lam ≤ cap)
    (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ C > 0, ∀ (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
        EuclideanSpace ℝ (Fin 3))
      (b : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (z f : EuclideanSpace ℝ (Fin 3) → ℝ),
      BoundaryNondivClosedData α lam cap M N A b z f →
      ∀ i : Fin 3, i ≠ Fin.last 2 →
        DifferentiableOn ℝ (fun x => fderiv ℝ z x (EuclideanSpace.single i 1))
          boundaryNondivC2Slab ∧
        ∀ j : Fin 3,
          (∀ x ∈ boundaryNondivC2Slab, |boundaryNeumannC2Entry z x j i| ≤ C) ∧
          ∀ x ∈ boundaryNondivC2Slab, ∀ y ∈ boundaryNondivC2Slab,
            |boundaryNeumannC2Entry z x j i - boundaryNeumannC2Entry z y j i| ≤
              C * dist x y ^ α := by
  obtain ⟨K, hK, ht⟩ := boundary_nondiv_tangential_derivative_c1_holder
    hα hα1 hlam hlamcap hM hN
  refine ⟨(4 / 3) * K * (1 + (4 / 3 : ℝ) ^ α), by positivity, ?_⟩
  intro A b z f d i hi
  obtain ⟨hd, hb, hh⟩ := ht A b z f d i hi
  let g := fun x => fderiv ℝ z ((3 / 4 : ℝ) • x) (EuclideanSpace.single i 1)
  have he : (fun x => g ((4 / 3 : ℝ) • x)) =
      (fun x => fderiv ℝ z x (EuclideanSpace.single i 1)) := by
    funext x
    dsimp only [g]
    rw [smul_smul]
    norm_num
  have hgd (x) (hx : x ∈ boundaryNondivC2Slab) :
      DifferentiableAt ℝ g ((4 / 3 : ℝ) • x) :=
    hd.differentiableAt (isOpen_boundaryC1UpperSlab.mem_nhds hx)
  have hgrad (x) (hx : x ∈ boundaryNondivC2Slab) :
      gradient (fun y => fderiv ℝ z y (EuclideanSpace.single i 1)) x =
        (4 / 3 : ℝ) • gradient g ((4 / 3 : ℝ) • x) := by
    rw [← he]
    exact boundary_neumann_c2_gradient_comp_smul (hgd x hx)
  have hentry (x) (hx : x ∈ boundaryNondivC2Slab) (j : Fin 3) :
      boundaryNeumannC2Entry z x j i =
        gradient (fun y => fderiv ℝ z y (EuclideanSpace.single i 1)) x j := by
    rw [gradient_apply_eq_fderiv_single]
    rfl
  have hGb (x) (hx : x ∈ boundaryNondivC2Slab) :
      ‖gradient (fun y => fderiv ℝ z y (EuclideanSpace.single i 1)) x‖ ≤
        (4 / 3) * K * (1 + (4 / 3 : ℝ) ^ α) := by
    rw [hgrad x hx, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 3)]
    apply (mul_le_mul_of_nonneg_left (hb _ hx) (by norm_num : (0 : ℝ) ≤ 4 / 3)).trans
    exact le_mul_of_one_le_right (by positivity)
      (by linarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 3) α])
  have hGh (x) (hx : x ∈ boundaryNondivC2Slab) (y) (hy : y ∈ boundaryNondivC2Slab) :
      ‖gradient (fun y => fderiv ℝ z y (EuclideanSpace.single i 1)) x -
        gradient (fun y => fderiv ℝ z y (EuclideanSpace.single i 1)) y‖ ≤
          (4 / 3) * K * (1 + (4 / 3 : ℝ) ^ α) * dist x y ^ α := by
    rw [hgrad x hx, hgrad y hy, ← smul_sub, norm_smul,
      Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 3)]
    apply (mul_le_mul_of_nonneg_left (hh _ hx _ hy)
      (by norm_num : (0 : ℝ) ≤ 4 / 3)).trans
    have hdist : dist ((4 / 3 : ℝ) • x) ((4 / 3 : ℝ) • y) =
        (4 / 3 : ℝ) * dist x y := by
      rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_nonneg (by norm_num), dist_eq_norm]
    rw [hdist, Real.mul_rpow (by norm_num) dist_nonneg]
    have hnonneg := Real.rpow_nonneg (dist_nonneg (x := x) (y := y)) α
    nlinarith [mul_nonneg hK.le hnonneg]
  refine ⟨?_, fun j => ⟨?_, ?_⟩⟩
  · intro x hx
    rw [← he]
    exact ((hgd x hx).comp x (differentiableAt_id.const_smul (4 / 3 : ℝ))).differentiableWithinAt
  · intro x hx
    rw [hentry x hx, ← Real.norm_eq_abs]
    exact (PiLp.norm_apply_le _ j).trans (hGb x hx)
  · intro x hx y hy
    rw [hentry x hx, hentry y hy, ← PiLp.sub_apply, ← Real.norm_eq_abs]
    exact (PiLp.norm_apply_le _ j).trans (hGh x hx y hy)

/-- Symmetry supplies the entries `∂ᵢ∂ⱼz` with `i` tangential from those with `j`
tangential; together, every entry except `∂₃∂₃z` is controlled on the slab. -/
theorem boundary_nondiv_c2_tangential_entries {α lam cap M N : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hlamcap : lam ≤ cap)
    (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ C > 0, ∀ (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
        EuclideanSpace ℝ (Fin 3))
      (b : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (z f : EuclideanSpace ℝ (Fin 3) → ℝ),
      BoundaryNondivClosedData α lam cap M N A b z f →
      ∀ i j : Fin 3, ¬ (i = Fin.last 2 ∧ j = Fin.last 2) →
        (∀ x ∈ boundaryNondivC2Slab, |boundaryNeumannC2Entry z x i j| ≤ C) ∧
        ∀ x ∈ boundaryNondivC2Slab, ∀ y ∈ boundaryNondivC2Slab,
          |boundaryNeumannC2Entry z x i j - boundaryNeumannC2Entry z y i j| ≤
            C * dist x y ^ α := by
  obtain ⟨C, hC, ht⟩ := boundary_nondiv_tangential_second_derivatives
    hα hα1 hlam hlamcap hM hN
  refine ⟨C, hC, ?_⟩
  intro A b z f d i j hij
  have hw : BoundaryNeumannInteriorC2 z := boundary_nondiv_interior_c2 hα hα1 hlam hlamcap hM d
  have hsub := boundaryNondivC2Slab_subset
  by_cases hi : i = Fin.last 2
  · have hj : j ≠ Fin.last 2 := fun hj => hij ⟨hi, hj⟩
    exact (ht A b z f d j hj).2 i
  · obtain ⟨hb, hh⟩ := (ht A b z f d i hi).2 j
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [boundary_neumann_c2_entry_comm hw (hsub hx) i j]
      exact hb x hx
    · intro x hx y hy
      rw [boundary_neumann_c2_entry_comm hw (hsub hx) i j,
        boundary_neumann_c2_entry_comm hw (hsub hy) i j]
      exact hh x hx y hy

/-- Blueprint `thm:boundary-nondiv` (zero trace, C²,α on a fixed boundary slab):
the zero-trace solution is C² on `boundaryNondivC2Slab`, every second derivative
`∂ᵢ∂ⱼz` is bounded and α-Hölder there with a constant chosen before the data, and
each extends continuously to the closure of the slab, which contains the flat disk
of radius `15/32` (`boundaryNondivC2Slab_face_mem_closure`). -/
theorem boundary_nondiv_c2_holder {α lam cap M N : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hlamcap : lam ≤ cap)
    (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ C > 0, ∀ (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
        EuclideanSpace ℝ (Fin 3))
      (b : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (z f : EuclideanSpace ℝ (Fin 3) → ℝ),
      BoundaryNondivClosedData α lam cap M N A b z f →
      ContDiffOn ℝ 2 z boundaryNondivC2Slab ∧
      ∀ i j : Fin 3,
        (∀ x ∈ boundaryNondivC2Slab, |boundaryNeumannC2Entry z x i j| ≤ C) ∧
        (∀ x ∈ boundaryNondivC2Slab, ∀ y ∈ boundaryNondivC2Slab,
          |boundaryNeumannC2Entry z x i j - boundaryNeumannC2Entry z y i j| ≤
            C * dist x y ^ α) ∧
        ∃ D : EuclideanSpace ℝ (Fin 3) → ℝ,
          EqOn D (fun x => boundaryNeumannC2Entry z x i j) boundaryNondivC2Slab ∧
          ContinuousOn D (closure boundaryNondivC2Slab) ∧
          (∀ x ∈ closure boundaryNondivC2Slab, |D x| ≤ C) ∧
          ∀ x ∈ closure boundaryNondivC2Slab, ∀ y ∈ closure boundaryNondivC2Slab,
            |D x - D y| ≤ C * dist x y ^ α := by
  obtain ⟨T, hT, ht⟩ := boundary_nondiv_c2_tangential_entries hα hα1 hlam hlamcap hM hN
  have hcap : 0 ≤ cap := hlam.le.trans hlamcap
  let F := (1 + 3 * M) * N
  let B := (F + 8 * cap * T) / lam
  let K := (F + 9 * M * (T + B) + 8 * cap * T) / lam
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨1 + T + B + K, by positivity, ?_⟩
  intro A b z f d
  have hw := boundary_nondiv_interior_c2 hα hα1 hlam hlamcap hM d
  let U := boundaryNondivC2Slab
  have hsub : U ⊆ boundaryHalfBall 1 := boundaryNondivC2Slab_subset
  have hclosed : U ⊆ closure (boundaryHalfBall 1) := hsub.trans subset_closure
  let a := fun x i j => A x (EuclideanSpace.single j 1) i
  have hell (x) (hx : x ∈ U) : lam ≤ a x (Fin.last 2) (Fin.last 2) := by
    simpa only [EuclideanSpace.inner_single_right, conj_trivial, one_mul] using
      elliptic_diagonal_entry_ge (fun v => by
        simpa only [real_inner_comm] using d.elliptic x (hclosed hx) v) (Fin.last 2)
  have hab (x) (hx : x ∈ U) (i j) : |a x i j| ≤ cap :=
    (boundary_neumann_c2_matrix_entry_bound _ i j).trans (d.coefficient_bound x (hclosed hx))
  have hah (x) (hx : x ∈ U) (y) (hy : y ∈ U) (i j) :
      |a x i j - a y i j| ≤ M * dist x y ^ α := by
    have hn : |a x i j - a y i j| ≤ ‖A x - A y‖ :=
      boundary_neumann_c2_matrix_entry_bound (A x - A y) i j
    apply hn.trans ((d.coefficient.function_holder.nondiv_norm_sub_le
      (hclosed hx) (hclosed hy)).trans ?_)
    rw [dist_eq_norm]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) α)
    exact (le_add_of_nonneg_left
      (holderUniformNorm_nonneg d.coefficient.function_holder.uniform_bounded)).trans
        (d.coefficient.function_norm_le.trans d.coefficient_norm)
  -- The scalar source `f - ⟪b, ∇z⟫` of the pointwise equation.
  have hzN : nondivC1HolderNorm α z (closure (boundaryHalfBall 1)) ≤ N :=
    (le_add_of_nonneg_right d.source.norm_nonneg).trans d.norm_bound
  have hfN : holderNorm α f (closure (boundaryHalfBall 1)) ≤ N :=
    (le_add_of_nonneg_left d.solution.norm_nonneg).trans d.norm_bound
  obtain ⟨hGz, hGzb⟩ := d.solution.gradient_holder
  have hGzN := hGzb.trans (d.solution.derivative_norm_le.trans hzN)
  obtain ⟨hp, hpb⟩ := nondiv_holder_inner d.drift hGz
  obtain ⟨hs, hsb⟩ := nondiv_holder_sub d.source hp
  have hsN : holderNorm α (fun x => f x - inner ℝ (b x) (gradient z x))
      (closure (boundaryHalfBall 1)) ≤ F := by
    have hpN : holderNorm α (fun x => inner ℝ (b x) (gradient z x))
        (closure (boundaryHalfBall 1)) ≤ 3 * M * N := by
      apply hpb.trans
      exact mul_le_mul (mul_le_mul_of_nonneg_left d.drift_norm (by norm_num)) hGzN
        hGz.norm_nonneg (by positivity)
    apply hsb.trans
    dsimp only [F]
    nlinarith only [hfN, hpN]
  have hsourceb (x) (hx : x ∈ U) : |f x - inner ℝ (b x) (gradient z x)| ≤ F := by
    simpa only [Real.norm_eq_abs] using (hs.nondiv_norm_le (hclosed hx)).trans hsN
  have hsourceh (x) (hx : x ∈ U) (y) (hy : y ∈ U) :
      |(f x - inner ℝ (b x) (gradient z x)) - (f y - inner ℝ (b y) (gradient z y))| ≤
        F * dist x y ^ α := by
    rw [← Real.norm_eq_abs]
    apply (hs.nondiv_norm_sub_le (hclosed hx) (hclosed hy)).trans
    rw [dist_eq_norm]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) α)
    exact (le_add_of_nonneg_left (holderUniformNorm_nonneg hs.uniform_bounded)).trans hsN
  have hpt := d.equation.pointwise_of_contDiffOn (isOpen_boundaryHalfBall 1)
    (d.coefficient.contDiff.mono subset_closure)
    ((d.drift.nondiv_continuousOn hα).mono subset_closure) hw
    ((d.source.nondiv_continuousOn hα).mono subset_closure)
  have heq (x) (hx : x ∈ U) :
      ∑ i, ∑ j, a x i j * boundaryNeumannC2Entry z x i j =
        f x - inner ℝ (b x) (gradient z x) := by
    have h := hpt x (hsub hx)
    change (∑ i, ∑ j, a x i j * boundaryNeumannC2Entry z x i j) + _ = _ at h
    linarith
  obtain ⟨hnb, hnh⟩ := normal_entry_holder_of_contraction
    (f := fun x => f x - inner ℝ (b x) (gradient z x)) hlam hcap hM hT.le hF
    hell hab hah (fun x hx i j hij => (ht A b z f d i j hij).1 x hx)
    (fun x hx y hy i j hij => (ht A b z f d i j hij).2 x hx y hy) hsourceb hsourceh heq
  refine ⟨hw.mono hsub, ?_⟩
  intro i j
  have hb : ∀ x ∈ U, |boundaryNeumannC2Entry z x i j| ≤ 1 + T + B + K := by
    intro x hx
    by_cases hij : i = Fin.last 2 ∧ j = Fin.last 2
    · rcases hij with ⟨rfl, rfl⟩
      exact (hnb x hx).trans (by dsimp only [B] at *; linarith)
    · exact ((ht A b z f d i j hij).1 x hx).trans (by linarith)
  have hh : ∀ x ∈ U, ∀ y ∈ U,
      |boundaryNeumannC2Entry z x i j - boundaryNeumannC2Entry z y i j| ≤
        (1 + T + B + K) * dist x y ^ α := by
    intro x hx y hy
    have hd := Real.rpow_nonneg (dist_nonneg (x := x) (y := y)) α
    by_cases hij : i = Fin.last 2 ∧ j = Fin.last 2
    · rcases hij with ⟨rfl, rfl⟩
      exact (hnh x hx y hy).trans (mul_le_mul_of_nonneg_right (by
        change K ≤ 1 + T + B + K
        linarith) hd)
    · exact ((ht A b z f d i j hij).2 x hx y hy).trans
        (mul_le_mul_of_nonneg_right (by linarith) hd)
  refine ⟨hb, hh, ?_⟩
  have hbn : ∀ x ∈ U, ‖boundaryNeumannC2Entry z x i j‖ ≤ 1 + T + B + K := by
    simpa only [Real.norm_eq_abs] using hb
  have hhn : ∀ x ∈ U, ∀ y ∈ U,
      ‖boundaryNeumannC2Entry z x i j - boundaryNeumannC2Entry z y i j‖ ≤
        (1 + T + B + K) * dist x y ^ α := by
    simpa only [Real.norm_eq_abs] using hh
  simpa only [Real.norm_eq_abs] using boundary_neumann_c2_holder_extension hα hbn hhn

end LiquidDrop
