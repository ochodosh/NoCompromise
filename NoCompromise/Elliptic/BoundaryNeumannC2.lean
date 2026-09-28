import NoCompromise.Elliptic.BoundaryNeumannC2Interior
import NoCompromise.Elliptic.BoundaryNeumannC2Algebra
import NoCompromise.Elliptic.BoundaryNeumannC2Extension

/-!
# Boundary C²,α estimates for the homogeneous Neumann problem

Interior C² regularity follows from the existing interior nondivergence Schauder
theorem. The boundary estimates and the continuous extensions of all second
derivatives use constants fixed before the coefficient, source, and solution.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- The actual iterated coordinate derivative `∂ᵢ(∂ⱼw)`. -/
def boundaryNeumannC2Entry (w : EuclideanSpace ℝ (Fin 3) → ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) (i j : Fin 3) : ℝ :=
  fderiv ℝ (fun y => fderiv ℝ w y (EuclideanSpace.single j 1)) x
    (EuclideanSpace.single i 1)

lemma boundary_neumann_c2_entry_comm {w : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hw : BoundaryNeumannInteriorC2 w) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ boundaryHalfBall 1) (i j : Fin 3) :
    boundaryNeumannC2Entry w x i j = boundaryNeumannC2Entry w x j i := by
  unfold boundaryNeumannC2Entry
  rw [nondiv_fderiv_coordinate_eq (isOpen_boundaryHalfBall _) hw j hx,
    nondiv_fderiv_coordinate_eq (isOpen_boundaryHalfBall _) hw i hx]
  exact ((hw.contDiffAt ((isOpen_boundaryHalfBall _).mem_nhds hx)).isSymmSndFDerivAt
    (by norm_num)).eq _ _

lemma boundary_neumann_c2_matrix_entry_bound
    (L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) (i j : Fin 3) :
    |L (EuclideanSpace.single j 1) i| ≤ ‖L‖ := by
  apply (show |L (EuclideanSpace.single j 1) i| ≤ ‖L (EuclideanSpace.single j 1)‖ from
    by simpa only [Real.norm_eq_abs] using
      PiLp.norm_apply_le (L (EuclideanSpace.single j 1)) i).trans
  simpa only [PiLp.norm_single, norm_one, mul_one] using L.le_opNorm (EuclideanSpace.single j 1)

/-- Under the named interior C² hypothesis, symmetry supplies the other mixed
derivatives from the tangential first-derivative estimates. -/
theorem boundary_neumann_c2_tangential_entries {α lam cap M N : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hcap : 0 ≤ cap)
    (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ C > 0, ∀ (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
        EuclideanSpace ℝ (Fin 3))
      (H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (w : EuclideanSpace ℝ (Fin 3) → ℝ),
      BoundaryNeumannClosedData α lam cap M N A H w → BoundaryNeumannInteriorC2 w →
      ∀ i j : Fin 3, ¬ (i = Fin.last 2 ∧ j = Fin.last 2) →
        (∀ x ∈ boundaryHalfBall (3 / 8), |boundaryNeumannC2Entry w x i j| ≤ C) ∧
        ∀ x ∈ boundaryHalfBall (3 / 8), ∀ y ∈ boundaryHalfBall (3 / 8),
          |boundaryNeumannC2Entry w x i j - boundaryNeumannC2Entry w y i j| ≤
            C * dist x y ^ α := by
  obtain ⟨C, hC, ht⟩ := boundary_neumann_tangential_second_derivatives hα hα1 hlam hcap hM hN
  refine ⟨C, hC, ?_⟩
  intro A H w d hw i j hij
  have hsub : boundaryHalfBall (3 / 8) ⊆ boundaryHalfBall 1 := boundaryHalfBall_mono (by norm_num)
  by_cases hj : j = Fin.last 2
  · have hi : i ≠ Fin.last 2 := fun hi => hij ⟨hi, hj⟩
    obtain ⟨hb, hh⟩ := (ht A H w d i hi).2 j
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [boundary_neumann_c2_entry_comm hw (hsub hx) i j]
      exact hb x hx
    · intro x hx y hy
      rw [boundary_neumann_c2_entry_comm hw (hsub hx) i j,
        boundary_neumann_c2_entry_comm hw (hsub hy) i j]
      exact hh x hx y hy
  · exact (ht A H w d j hj).2 i

/-- The pointwise algebraic formula for the remaining normal second derivative.
The ellipticity lower bound ensures that the denominator is positive. -/
theorem boundary_neumann_c2_normal_entry_eq {α lam cap M N : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hM : 0 ≤ M) (hN : 0 ≤ N)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {w : EuclideanSpace ℝ (Fin 3) → ℝ}
    (d : BoundaryNeumannClosedData α lam cap M N A H w)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ boundaryHalfBall 1) :
    boundaryNeumannC2Entry w x (Fin.last 2) (Fin.last 2) =
      (boundaryNeumannC2Source A H w x -
        ∑ p ∈ ((Finset.univ : Finset (Fin 3)) ×ˢ (Finset.univ : Finset (Fin 3))).erase
          (Fin.last 2, Fin.last 2),
          A x (EuclideanSpace.single p.2 1) p.1 * boundaryNeumannC2Entry w x p.1 p.2) /
        A x (EuclideanSpace.single (Fin.last 2) 1) (Fin.last 2) := by
  have hw := boundary_neumann_interior_c2 hα hα1 hlam hM hN d
  have hell : lam ≤ A x (EuclideanSpace.single (Fin.last 2) 1) (Fin.last 2) := by
    simpa only [EuclideanSpace.inner_single_right, conj_trivial, one_mul] using
      elliptic_diagonal_entry_ge (d.elliptic x (subset_closure hx)) (Fin.last 2)
  apply normal_entry_eq_of_contraction
    (A := fun i j => A x (EuclideanSpace.single j 1) i)
    (H := boundaryNeumannC2Entry w x) (f := boundaryNeumannC2Source A H w x) hlam hell
  rw [boundary_neumann_c2_source_expansion]
  have hp := boundary_neumann_c2_pointwise_equation d hw x hx
  change (∑ i, ∑ j, A x (EuclideanSpace.single j 1) i * boundaryNeumannC2Entry w x i j) +
    _ = _ at hp
  linarith

/-- Uniform C²,α estimates and continuous extensions of every second derivative
to the closed radius `3/8` half ball, under the original closed Neumann data. -/
theorem boundary_neumann_c2_holder {α lam cap M N : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hcap : 0 ≤ cap)
    (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ C > 0, ∀ (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
        EuclideanSpace ℝ (Fin 3))
      (H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (w : EuclideanSpace ℝ (Fin 3) → ℝ),
      BoundaryNeumannClosedData α lam cap M N A H w →
      ContDiffOn ℝ 2 w (boundaryHalfBall (3 / 8)) ∧
      ∀ i j : Fin 3,
        (∀ x ∈ boundaryHalfBall (3 / 8), |boundaryNeumannC2Entry w x i j| ≤ C) ∧
        (∀ x ∈ boundaryHalfBall (3 / 8), ∀ y ∈ boundaryHalfBall (3 / 8),
          |boundaryNeumannC2Entry w x i j - boundaryNeumannC2Entry w y i j| ≤ C * dist x y ^ α) ∧
        ∃ D : EuclideanSpace ℝ (Fin 3) → ℝ,
          EqOn D (fun x => boundaryNeumannC2Entry w x i j) (boundaryHalfBall (3 / 8)) ∧
          ContinuousOn D (closure (boundaryHalfBall (3 / 8))) ∧
          (∀ x ∈ closure (boundaryHalfBall (3 / 8)), |D x| ≤ C) ∧
          ∀ x ∈ closure (boundaryHalfBall (3 / 8)), ∀ y ∈ closure (boundaryHalfBall (3 / 8)),
            |D x - D y| ≤ C * dist x y ^ α := by
  obtain ⟨T, hT, ht⟩ := boundary_neumann_c2_tangential_entries hα hα1 hlam hcap hM hN
  let F := (3 + 9 * M) * N
  let B := (F + 8 * cap * T) / lam
  let K := (F + 9 * M * (T + B) + 8 * cap * T) / lam
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨1 + T + B + K, by positivity, ?_⟩
  intro A H w d
  have hw := boundary_neumann_interior_c2 hα hα1 hlam hM hN d
  let U := boundaryHalfBall (3 / 8 : ℝ)
  have hsub : U ⊆ boundaryHalfBall 1 := boundaryHalfBall_mono (by norm_num)
  have hclosed : U ⊆ closure (boundaryHalfBall 1) := hsub.trans subset_closure
  let a := fun x i j => A x (EuclideanSpace.single j 1) i
  have hell (x) (hx : x ∈ U) : lam ≤ a x (Fin.last 2) (Fin.last 2) := by
    simpa only [EuclideanSpace.inner_single_right, conj_trivial, one_mul] using
      elliptic_diagonal_entry_ge (d.elliptic x (hclosed hx)) (Fin.last 2)
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
  obtain ⟨hf, hfb⟩ := boundary_neumann_c2_source_holder hM hN d
  have hsourceb (x) (hx : x ∈ U) : |boundaryNeumannC2Source A H w x| ≤ F := by
    simpa only [Real.norm_eq_abs] using (hf.nondiv_norm_le (hclosed hx)).trans hfb
  have hsourceh (x) (hx : x ∈ U) (y) (hy : y ∈ U) :
      |boundaryNeumannC2Source A H w x - boundaryNeumannC2Source A H w y| ≤
        F * dist x y ^ α := by
    rw [← Real.norm_eq_abs]
    apply (hf.nondiv_norm_sub_le (hclosed hx) (hclosed hy)).trans
    rw [dist_eq_norm]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) α)
    exact (le_add_of_nonneg_left (holderUniformNorm_nonneg hf.uniform_bounded)).trans hfb
  have heq (x) (hx : x ∈ U) :
      ∑ i, ∑ j, a x i j * boundaryNeumannC2Entry w x i j = boundaryNeumannC2Source A H w x := by
    rw [boundary_neumann_c2_source_expansion]
    have hp := boundary_neumann_c2_pointwise_equation d hw x (hsub hx)
    change (∑ i, ∑ j, a x i j * boundaryNeumannC2Entry w x i j) + _ = _ at hp
    linarith
  obtain ⟨hnb, hnh⟩ := normal_entry_holder_of_contraction hlam hcap hM hT.le hF
    hell hab hah (fun x hx i j hij => (ht A H w d hw i j hij).1 x hx)
    (fun x hx y hy i j hij => (ht A H w d hw i j hij).2 x hx y hy) hsourceb hsourceh heq
  refine ⟨hw.mono hsub, ?_⟩
  intro i j
  have hb : ∀ x ∈ U, |boundaryNeumannC2Entry w x i j| ≤ 1 + T + B + K := by
    intro x hx
    by_cases hij : i = Fin.last 2 ∧ j = Fin.last 2
    · rcases hij with ⟨rfl, rfl⟩
      exact (hnb x hx).trans (by dsimp only [B] at *; linarith)
    · exact ((ht A H w d hw i j hij).1 x hx).trans (by linarith)
  have hh : ∀ x ∈ U, ∀ y ∈ U,
      |boundaryNeumannC2Entry w x i j - boundaryNeumannC2Entry w y i j| ≤
        (1 + T + B + K) * dist x y ^ α := by
    intro x hx y hy
    have hd := Real.rpow_nonneg (dist_nonneg (x := x) (y := y)) α
    by_cases hij : i = Fin.last 2 ∧ j = Fin.last 2
    · rcases hij with ⟨rfl, rfl⟩
      exact (hnh x hx y hy).trans (mul_le_mul_of_nonneg_right (by
        change K ≤ 1 + T + B + K
        linarith) hd)
    · exact ((ht A H w d hw i j hij).2 x hx y hy).trans
        (mul_le_mul_of_nonneg_right (by linarith) hd)
  refine ⟨hb, hh, ?_⟩
  have hbn : ∀ x ∈ U, ‖boundaryNeumannC2Entry w x i j‖ ≤ 1 + T + B + K := by
    simpa only [Real.norm_eq_abs] using hb
  have hhn : ∀ x ∈ U, ∀ y ∈ U,
      ‖boundaryNeumannC2Entry w x i j - boundaryNeumannC2Entry w y i j‖ ≤
        (1 + T + B + K) * dist x y ^ α := by
    simpa only [Real.norm_eq_abs] using hh
  simpa only [Real.norm_eq_abs] using boundary_neumann_c2_holder_extension hα hbn hhn

end LiquidDrop
