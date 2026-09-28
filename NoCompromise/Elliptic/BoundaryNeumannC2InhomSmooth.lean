import NoCompromise.Elliptic.BoundaryNeumannC2InhomReduction

/-!
# Flat boundary C² regularity for smooth inhomogeneous conormal data

This is the smooth-data partial form of the second assertion of blueprint
`thm:boundary-neumann`. The resulting radius is `1/4 * (3/8)`.
-/

noncomputable section
open Set Filter Metric InnerProductSpace MeasureTheory
open scoped Topology Gradient RealInnerProductSpace
namespace LiquidDrop

theorem boundary_neumann_c2_inhom_smooth_fixed
    {α lam : ℝ} (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)} {f z : EuclideanSpace ℝ (Fin 3) → ℝ}
    {F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {h : EuclideanSpace ℝ (Fin 2) → ℝ} {O : Set (EuclideanSpace ℝ (Fin 3))}
    (hO : IsOpen O) (hsub : closedBall 0 1 ⊆ O)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) A O) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f O)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hell : ∀ x ∈ closure (boundaryHalfBall 1), ∀ ξ,
      lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ)
    (hcross : ∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 →
      ∀ i : Fin 3, i ≠ Fin.last 2 →
        A x (EuclideanSpace.single i 1) (Fin.last 2) = 0 ∧
        A x (EuclideanSpace.single (Fin.last 2) 1) i = 0)
    (hpos : ∃ U : Set (EuclideanSpace ℝ (Fin 2)), IsOpen U ∧ closedBall 0 1 ⊆ U ∧
      ∀ x ∈ U, lam ≤ boundaryNeumannNormalCoefficient A x)
    (hz : HasH1GradientOn z F (boundaryHalfBall 1))
    (hweak : ∀ φ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ ball 0 1 →
      (∫ x in boundaryHalfBall 1, inner ℝ (A x (F x)) (gradient φ x)) =
        -(∫ x in boundaryHalfBall 1, f x * φ x) -
          ∫ y in ball (0 : EuclideanSpace ℝ (Fin 2)) 1, h y * φ (graphBaseEmbedding y)) :
    ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
      ContDiffOn ℝ 1 u (ball 0 (1 / 2 : ℝ)) ∧
      ContDiffOn ℝ 2 u (boundaryHalfBall (1 / 4 * (3 / 8))) ∧
      z =ᵐ[volume.restrict (boundaryHalfBall (1 / 4 * (3 / 8)))] u ∧
      F =ᵐ[volume.restrict (boundaryHalfBall (1 / 4 * (3 / 8)))] gradient u ∧
      (∀ i j : Fin 3, ∃ D : EuclideanSpace ℝ (Fin 3) → ℝ,
        ContinuousOn D (closure (boundaryHalfBall (1 / 4 * (3 / 8)))) ∧
        EqOn D (fun x => boundaryNeumannC2Entry u x i j) (boundaryHalfBall (1 / 4 * (3 / 8)))) ∧
      (∀ y : EuclideanSpace ℝ (Fin 2), graphBaseEmbedding y ∈ ball 0 (1 / 2 : ℝ) →
        A (graphBaseEmbedding y) (gradient u (graphBaseEmbedding y)) (Fin.last 2) = h y) := by
  obtain ⟨cap, HA, B, hcap, hHA, hB, d⟩ :=
    boundary_neumann_c2_inhom_smooth_exists_data hα hα1 hO hsub hA hf hh hell hcross hpos
  let E := max (∫ x in boundaryHalfBall 1, ‖F x‖ ^ 2) 0
  obtain ⟨C, hC, hreg⟩ := boundary_neumann_c1_holder_conormal
    hα hα1 hlam hcap hHA hB (le_max_right _ _ : 0 ≤ E)
  obtain ⟨u, hu, hzu, hFu, hbu, hhu, hface⟩ := hreg A F z f h
    d.continuous_coefficient d.bound_coefficient d.elliptic d.holder_coefficient d.cross_face
    d.normal_neighborhood d.bound_datum d.bound_normal d.bound_gradient_datum
    d.bound_gradient_normal d.holder_gradient_datum d.holder_gradient_normal
    d.continuous_forcing d.bound_forcing d.holder_forcing hz (le_max_left _ _) hweak
  let q := boundaryNeumannLift h (boundaryNeumannNormalCoefficient A)
  let H := boundaryNeumannInhomDatum A f h
  let w := fun x => u x - q x
  obtain ⟨hqs, hHs⟩ := boundary_neumann_c2_inhom_smooth_lift_datum
    hlam hO hsub hA hf hh hpos
  let S := closure (boundaryHalfBall (1 / 4 : ℝ))
  have hSc : IsCompact S :=
    (isBounded_ball.subset (inter_subset_left : boundaryHalfBall (1 / 4 : ℝ) ⊆
      ball 0 (1 / 4 : ℝ))).isCompact_closure
  have hSconv : Convex ℝ S := (convex_boundaryHalfBall (1 / 4 : ℝ)).closure
  have hSclosed : S ⊆ closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 4 : ℝ) :=
    closure_minimal (inter_subset_left.trans ball_subset_closedBall) isClosed_closedBall
  have hSsmall : S ⊆ ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2 : ℝ) :=
    hSclosed.trans (closedBall_subset_ball (by norm_num))
  have hSone : S ⊆ ball (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    hSclosed.trans (closedBall_subset_ball (by norm_num))
  have hSunit : S ⊆ closure (boundaryHalfBall 1) :=
    closure_mono (boundaryHalfBall_mono (by norm_num))
  have hAH : HasC1HolderOn α A S := hasC1HolderOn_of_contDiffOn hα.le hα1.le
    hSc hSconv hO (hSone.trans (ball_subset_closedBall.trans hsub)) hA
  have hHH : HasC1HolderOn α H S := hasC1HolderOn_of_contDiffOn hα.le hα1.le
    hSc hSconv isOpen_ball hSone hHs
  have hqH : HasC1HolderOn α q S := hasC1HolderOn_of_contDiffOn hα.le hα1.le
    hSc hSconv isOpen_ball hSone hqs
  have huH : HasC1HolderOn α u S := boundary_neumann_c2_inhom_holder_of_gradient
    hα.le hα1.le hC.le hSc hSconv isOpen_ball hSsmall hu
    (fun x hx => hbu x (hSsmall hx))
    (fun x hx y hy => hhu x (hSsmall hx) y (hSsmall hy))
  have hud (x) (hx : x ∈ S) : DifferentiableAt ℝ u x :=
    (hu.contDiffAt (isOpen_ball.mem_nhds (hSsmall hx))).differentiableAt one_ne_zero
  have hqd (x) (hx : x ∈ S) : DifferentiableAt ℝ q x :=
    (hqs.contDiffAt (isOpen_ball.mem_nhds (hSone hx))).differentiableAt (by simp)
  have hwH : HasC1HolderOn α w S :=
    boundary_neumann_c2_inhom_holder_sub huH hqH hud hqd
  have hgrad (x) (hx : x ∈ S) : gradient w x = gradient u x - gradient q x :=
    boundary_neumann_c2_inhom_gradient_sub (hud x hx) (hqd x hx)
  obtain ⟨V, hV, hVs, hhV, hbV, hposV⟩ := d.normal_neighborhood
  have hproj (x) (hx : x ∈ S) : graphProjectionN 2 x ∈ V :=
    hVs (boundary_neumann_projection_closedBall (ball_subset_closedBall (hSone hx)))
  have hhd (x) (hx : x ∈ S) : DifferentiableAt ℝ h (graphProjectionN 2 x) :=
    (hhV.contDiffAt (hV.mem_nhds (hproj x hx))).differentiableAt one_ne_zero
  have hbd (x) (hx : x ∈ S) :
      DifferentiableAt ℝ (boundaryNeumannNormalCoefficient A) (graphProjectionN 2 x) :=
    (hbV.contDiffAt (hV.mem_nhds (hproj x hx))).differentiableAt one_ne_zero
  have hH0 : ∀ x ∈ S, x (Fin.last 2) = 0 → H x (Fin.last 2) = 0 :=
    fun x hx hx0 => boundaryNeumannInhomDatum_flat_of_elliptic hlam f hx0
      (hell x (hSunit hx)) (hhd x hx) (hbd x hx)
  have hw0 : ∀ x ∈ S, x (Fin.last 2) = 0 → gradient w x (Fin.last 2) = 0 := by
    intro x hx hx0
    have he : graphBaseEmbedding (graphProjectionN 2 x) = x := by
      rw [boundary_neumann_graphBase_eq_append, ← hx0, graphAppendN_projection]
    have hnon : boundaryNeumannNormalCoefficient A (graphProjectionN 2 x) ≠ 0 :=
      (hlam.trans_le (hposV _ (hproj x hx))).ne'
    have hqc := boundaryNeumannLift_conormal (hhd x hx) (hbd x hx) hnon
    rw [he] at hqc
    have huc := hface (graphProjectionN 2 x) (by rw [he]; exact hSsmall hx)
    rw [he] at huc
    apply boundary_neumann_c2_inhom_normal_zero
      (fun i hi => (hcross x (hSunit hx) hx0 i hi).1)
    · have hn := hnon
      rwa [boundaryNeumannNormalCoefficient_eq, he] at hn
    · rw [hgrad x hx, map_sub, PiLp.sub_apply]
      exact sub_eq_zero.mpr (huc.trans hqc.symm)
  have hred : IsBoundaryNeumannEquationOn A (fun x => F x - gradient q x) H 1 :=
    boundary_neumann_inhomogeneous_weak_reduction hα hα1.le hB hB
      d.continuous_coefficient d.bound_coefficient hz.memLp_gradient d.continuous_forcing
      d.bound_forcing d.holder_forcing hh.continuous.continuousOn hweak
  have hFsmall : F =ᵐ[volume.restrict (boundaryHalfBall (1 / 4))] gradient u :=
    ae_restrict_of_ae_restrict_of_subset (boundaryHalfBall_mono (by norm_num)) hFu
  have heq : IsBoundaryNeumannEquationOn A (gradient w) H (1 / 4) :=
    boundary_neumann_c2_inhom_equation_congr
      (boundary_neumann_c2_inhom_equation_mono (by norm_num : (1 / 4 : ℝ) ≤ 1) hred) (by
        filter_upwards [hFsmall,
          ae_restrict_mem (isOpen_boundaryHalfBall (1 / 4 : ℝ)).measurableSet]
          with x hx hxs
        rw [hgrad x (subset_closure hxs), hx])
  obtain ⟨_, -, hreg2⟩ := boundary_neumann_c2_holder_scaled hα hα1 hlam hcap
    hAH.norm_nonneg (add_nonneg hwH.norm_nonneg hHH.norm_nonneg)
  obtain ⟨hw2, hentries⟩ := hreg2 (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num)
    A H w hAH hHH hwH le_rfl le_rfl
    (fun x hx => d.bound_coefficient x (hSunit hx))
    (fun x hx => hell x (hSunit hx))
    (fun x hx => hcross x (hSunit hx)) hH0 hw0 heq
  let r : ℝ := 1 / 4 * (3 / 8)
  have hrsmall : boundaryHalfBall r ⊆ boundaryHalfBall (1 / 2) :=
    boundaryHalfBall_mono (by dsimp [r]; norm_num)
  have hrball : closure (boundaryHalfBall r) ⊆ ball (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    (closure_mono (boundaryHalfBall_mono (by dsimp [r]; norm_num : r ≤ 1 / 4))).trans hSone
  have hq2 : ContDiffOn ℝ 2 q (boundaryHalfBall r) :=
    (hqs.of_le (by simp)).mono (subset_closure.trans hrball)
  have he : (fun x => w x + q x) = u := by funext x; exact sub_add_cancel _ _
  have hu2 : ContDiffOn ℝ 2 u (boundaryHalfBall r) := by
    rw [← he]
    exact hw2.add hq2
  refine ⟨u, hu, hu2,
    ae_restrict_of_ae_restrict_of_subset hrsmall hzu,
    ae_restrict_of_ae_restrict_of_subset hrsmall hFu, ?_, hface⟩
  intro i j
  obtain ⟨D, hDeq, hDc, -, -⟩ := hentries i j
  refine ⟨fun x => D x + boundaryNeumannC2Entry q x i j,
    hDc.add ((boundary_neumann_c2_inhom_entry_continuous isOpen_ball
      (hqs.of_le (by simp)) i j).mono hrball), ?_⟩
  intro x hx
  change D x + boundaryNeumannC2Entry q x i j = boundaryNeumannC2Entry u x i j
  rw [hDeq hx, ← boundary_neumann_c2_inhom_entry_add (isOpen_boundaryHalfBall r) hw2 hq2 hx,
    he]

/-- The requested existential-radius smooth-data form, with the classical
inward-coordinate conormal identity retained on the half-radius flat face. -/
theorem boundary_neumann_c2_inhom_smooth
    {α lam : ℝ} (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)} {f z : EuclideanSpace ℝ (Fin 3) → ℝ}
    {F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {h : EuclideanSpace ℝ (Fin 2) → ℝ} {O : Set (EuclideanSpace ℝ (Fin 3))}
    (hO : IsOpen O) (hsub : closedBall 0 1 ⊆ O)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) A O) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f O)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hell : ∀ x ∈ closure (boundaryHalfBall 1), ∀ ξ,
      lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ)
    (hcross : ∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 →
      ∀ i : Fin 3, i ≠ Fin.last 2 →
        A x (EuclideanSpace.single i 1) (Fin.last 2) = 0 ∧
        A x (EuclideanSpace.single (Fin.last 2) 1) i = 0)
    (hpos : ∃ U : Set (EuclideanSpace ℝ (Fin 2)), IsOpen U ∧ closedBall 0 1 ⊆ U ∧
      ∀ x ∈ U, lam ≤ boundaryNeumannNormalCoefficient A x)
    (hz : HasH1GradientOn z F (boundaryHalfBall 1))
    (hweak : ∀ φ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ ball 0 1 →
      (∫ x in boundaryHalfBall 1, inner ℝ (A x (F x)) (gradient φ x)) =
        -(∫ x in boundaryHalfBall 1, f x * φ x) -
          ∫ y in ball (0 : EuclideanSpace ℝ (Fin 2)) 1, h y * φ (graphBaseEmbedding y)) :
    ∃ r > 0, ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
      ContDiffOn ℝ 1 u (ball 0 (1 / 2 : ℝ)) ∧
      ContDiffOn ℝ 2 u (boundaryHalfBall r) ∧
      z =ᵐ[volume.restrict (boundaryHalfBall r)] u ∧
      F =ᵐ[volume.restrict (boundaryHalfBall r)] gradient u ∧
      (∀ i j : Fin 3, ∃ D : EuclideanSpace ℝ (Fin 3) → ℝ,
        ContinuousOn D (closure (boundaryHalfBall r)) ∧
        EqOn D (fun x => boundaryNeumannC2Entry u x i j) (boundaryHalfBall r)) ∧
      (∀ y : EuclideanSpace ℝ (Fin 2), graphBaseEmbedding y ∈ ball 0 (1 / 2 : ℝ) →
        A (graphBaseEmbedding y) (gradient u (graphBaseEmbedding y)) (Fin.last 2) = h y) := by
  obtain ⟨u, hu⟩ := boundary_neumann_c2_inhom_smooth_fixed hα hα1 hlam hO hsub
    hA hf hh hell hcross hpos hz hweak
  exact ⟨1 / 4 * (3 / 8), by norm_num, u, hu⟩

end LiquidDrop
