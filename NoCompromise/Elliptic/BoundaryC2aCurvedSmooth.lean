module

public import NoCompromise.Elliptic.BoundaryC2aSmoothChain
public import NoCompromise.Elliptic.BoundaryC2aCurvedHolder

@[expose] public section

/-!
# `thm:boundary-C2a`: all higher regularity for a curved boundary

For a smooth diffeomorphism `Θ` flattening the boundary, smooth coefficient `A`, datum `G` and
boundary value `φ`, and a `C^{1,α}` solution `u` of `div(A ∇u) = div G` near
`Θ(closure B⁺₁)` with `u = φ` on the curved face `Θ({y₃ = 0})`, the pulled-back function
`u ∘ Θ` solves the flat problem with the smooth coefficient
`|det DΘ| DΘ⁻¹ (A ∘ Θ) DΘ⁻ᵀ` and datum `|det DΘ| DΘ⁻¹ (G ∘ Θ)`, so
`boundary_c2a_smooth_all_orders` applies; composing back with `Θ⁻¹` gives, for every `k`, a
`Cᵏ` function on the open neighbourhood `Θ(ball 0 ρ)` of `Θ 0` equal to `u` on the part
`Θ(B⁺_ρ)` inside the domain and, by continuity, up to the curved face. The shear chart of a
smooth, globally Lipschitz height is an instance.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- `C^{1,α}` is preserved by pre-composition with a C² Lipschitz map. -/
theorem boundaryC2aCurvedSmooth_comp {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    {Θ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)} (hΘ : ContDiff ℝ 2 Θ)
    {CΘ : ℝ≥0} (hΘlip : LipschitzWith CΘ Θ)
    {W : Set (EuclideanSpace ℝ (Fin 3))} (hW : IsOpen W)
    {K : Set (EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKW : Θ '' K ⊆ W) {u : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hu : HasCkHolderOn 1 α u W (Θ '' K)) :
    HasCkHolderOn 1 α (u ∘ Θ) (Θ ⁻¹' W) K := by
  have hO : IsOpen (Θ ⁻¹' W) := hW.preimage hΘ.continuous
  have hKO : K ⊆ Θ ⁻¹' W := fun y hy => hKW ⟨y, hy, rfl⟩
  obtain ⟨hud, ⟨B, hB⟩, hDu⟩ := (HasCkHolderOn.succ_iff (k := 0) hW).1 hu
  refine (HasCkHolderOn.succ_iff (k := 0) hO).2 ⟨hud.comp
    (hΘ.differentiable (by norm_num)).differentiableOn (fun y hy => hy),
    ⟨B, fun y hy => hB _ ⟨y, hy, rfl⟩⟩, ?_⟩
  have hf : HasCkHolderOn 0 α (fun y => fderiv ℝ u (Θ y)) (Θ ⁻¹' W) K := by
    obtain ⟨hc, ⟨B', hB'⟩, ⟨C, hC⟩⟩ := hasCkHolderOn_zero_iff.1 hDu
    refine hasCkHolderOn_zero_iff.2 ⟨hc.comp hΘ.continuous.continuousOn (fun y hy => hy),
      ⟨B', fun y hy => hB' _ ⟨y, hy, rfl⟩⟩, max C 0 * (CΘ : ℝ) ^ α, fun x hx y hy => ?_⟩
    have h1 := hC _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have hd : dist (Θ x) (Θ y) ≤ CΘ * dist x y := hΘlip.dist_le_mul x y
    have h2 : dist (Θ x) (Θ y) ^ α ≤ (CΘ * dist x y) ^ α :=
      Real.rpow_le_rpow dist_nonneg hd hα
    rw [Real.mul_rpow (NNReal.coe_nonneg _) dist_nonneg] at h2
    calc ‖fderiv ℝ u (Θ x) - fderiv ℝ u (Θ y)‖ ≤ C * dist (Θ x) (Θ y) ^ α := h1
      _ ≤ max C 0 * dist (Θ x) (Θ y) ^ α :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg _)
      _ ≤ max C 0 * ((CΘ : ℝ) ^ α * dist x y ^ α) :=
          mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
      _ = max C 0 * (CΘ : ℝ) ^ α * dist x y ^ α := by ring
  have hg : HasCkHolderOn 0 α (fderiv ℝ Θ) (Θ ⁻¹' W) K :=
    HasCkHolderOn.of_contDiffOn (k := 0) hα1 hO hKO hKc hK
      (hΘ.fderiv_right (m := 1) (by norm_num)).contDiffOn
  have hb := HasCkHolderOn.bilinear hα1 hO hKO hKc hK.isBounded
    (ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)) ℝ) hf hg
  refine hb.congr hO hKO fun y hy => ?_
  have hud' := (hud (Θ y) hy).differentiableAt (hW.mem_nhds hy)
  rw [fderiv_comp y hud' (hΘ.differentiable (by norm_num) y)]
  rfl

/-- **`thm:boundary-C2a`, all higher regularity for a curved boundary.** Let `Θ` be a smooth
diffeomorphism of `ℝ³` with smooth inverse `Θi`, `Θ` globally Lipschitz; let `W` be an open set
containing `Θ(closure B⁺₁)` on which `A` and `G` are smooth, `A` elliptic on
`Θ(closure B⁺₁)`; let `φ` be smooth and `u` be `C^{1,α}` near `Θ(closure B⁺₁)` (relative to `W`),
with `u = φ` on the curved face `Θ(closure B⁺₁ ∩ {y₃ = 0})`, solving `div(A ∇u) = div G` weakly
on `Θ(B⁺₁)`. Then for every `k` there are `ρ > 0` and a function `v`, `Cᵏ` on the open
neighbourhood `Θ(ball 0 ρ)` of `Θ 0`, equal to `u` on `Θ(ball 0 ρ ∩ {y₃ ≥ 0})` (the part of that
neighbourhood in the closed domain, up to the curved face). -/
theorem boundary_c2a_curved_smooth_all_orders {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {Θ Θi : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hΘ : ContDiff ℝ (⊤ : ℕ∞) Θ) (hΘi : ContDiff ℝ (⊤ : ℕ∞) Θi)
    (hl : Function.LeftInverse Θi Θ) (hr : Function.RightInverse Θi Θ)
    {CΘ : ℝ≥0} (hΘlip : LipschitzWith CΘ Θ)
    {W : Set (EuclideanSpace ℝ (Fin 3))} (hW : IsOpen W)
    (hWΘ : Θ '' closure (boundaryHalfBall 1) ⊆ W)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) A W) (hG : ContDiffOn ℝ (⊤ : ℕ∞) G W)
    {lamA : ℝ} (hlamA : 0 < lamA)
    (hAe : ∀ x ∈ Θ '' closure (boundaryHalfBall 1), ∀ ξ,
      lamA * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ)
    {u φ : EuclideanSpace ℝ (Fin 3) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hu : HasCkHolderOn 1 α u W (Θ '' closure (boundaryHalfBall 1)))
    (hface : ∀ y ∈ closure (boundaryHalfBall 1), y (Fin.last 2) = 0 → u (Θ y) = φ (Θ y))
    (hw : IsWeakDivergenceEquationOn A (gradient u) G (Θ '' boundaryHalfBall 1)) :
    ∀ k : ℕ, ∃ ρ > 0, ∃ v : EuclideanSpace ℝ (Fin 3) → ℝ,
      IsOpen (Θ '' ball 0 ρ) ∧ ContDiffOn ℝ k v (Θ '' ball 0 ρ) ∧
      EqOn v u (Θ '' (ball 0 ρ ∩ {y | 0 ≤ y (Fin.last 2)})) := by
  intro k
  set K := closure (boundaryHalfBall (1 : ℝ)) with hK_def
  have hKc : IsCompact K := boundaryC2aCurved_isCompact_closure_halfBall
  have hKv : Convex ℝ K := (convex_boundaryHalfBall 1).closure
  have hΘ2 : ContDiff ℝ 2 Θ := hΘ.of_le (by simp)
  have hΘ1 : ContDiff ℝ 1 Θ := hΘ.of_le (by simp)
  have hΘi1 : ContDiff ℝ 1 Θi := hΘi.of_le (by simp)
  set O := Θ ⁻¹' W with hOdef
  have hO : IsOpen O := hW.preimage hΘ.continuous
  have hKO : K ⊆ O := fun y hy => hWΘ ⟨y, hy, rfl⟩
  -- the pulled-back problem
  set At := dirichletPullbackGeneralCoefficient A Θ
  set Gt := dirichletPullbackGeneralDatum G Θ
  have hAt : ContDiffOn ℝ (⊤ : ℕ∞) At O :=
    contDiffOn_dirichletPullbackGeneralCoefficient (m := ⊤) hΘ (by simp) hΘi1 hl hr hW hA
  have hGt : ContDiffOn ℝ (⊤ : ℕ∞) Gt O :=
    contDiffOn_dirichletPullbackGeneralDatum (m := ⊤) hΘ (by simp) hΘi1 hl hr hW hG
  have hut : HasCkHolderOn 1 α (u ∘ Θ) O K :=
    boundaryC2aCurvedSmooth_comp hα.le hα1.le hΘ2 hΘlip hW hKc hKv hWΘ hu
  have hφt : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ Θ) := hφ.comp hΘ
  have hAc : ContinuousOn A (Θ '' K) := hA.continuousOn.mono hWΘ
  obtain ⟨capA, hcapA⟩ := (hKc.image hΘ.continuous).exists_bound_of_continuousOn hAc
  obtain ⟨lam, cap, hlam, -, hAtb⟩ :=
    dirichletPullbackGeneralCoefficient_bounds hΘ1 hΘi1 hl hr hKc hlamA hcapA hAe
  have hwt0 := isWeakDivergenceEquationOn_dirichletPullbackGeneral_field hΘ1 hΘi1 hl hr
    (mapsTo_image Θ (boundaryHalfBall 1)) hw
  have hwt : IsWeakDivergenceEquationOn At (gradient (u ∘ Θ)) Gt (boundaryHalfBall 1) := by
    intro ψ hψ hcψ hsψ
    rw [← hwt0 ψ hψ hcψ hsψ]
    congr 1
    funext y
    by_cases hy : y ∈ tsupport ψ
    · have hyK : y ∈ O := hKO (subset_closure (hsψ hy))
      have hud := ((HasCkHolderOn.succ_iff (k := 0) hW).1 hu).1
      rw [dirichletPullback_gradient_comp (hΘ1.differentiable one_ne_zero y)
        ((hud (Θ y) hyK).differentiableAt (hW.mem_nhds hyK))]
    · simp [gradient_eq_zero_of_notMem_tsupport hy]
  obtain ⟨ρ₀, hρ₀, v₀, hv₀u, hv₀⟩ := boundary_c2a_smooth_all_orders hα hα1 hlam
    (R := 1) one_pos le_rfl hO hKO hAt hφt hGt hut (fun x hx => (hAtb x hx).1)
    (fun x hx => (hAtb x hx).2) hface hwt k
  -- shrink so that the closed upper part lies in `K`
  set ρ := min ρ₀ 1 with hρdef
  have hρ : 0 < ρ := lt_min hρ₀ one_pos
  have hρρ₀ : ρ ≤ ρ₀ := min_le_left _ _
  have hρ1 : ρ ≤ 1 := min_le_right _ _
  have himg : ∀ S : Set (EuclideanSpace ℝ (Fin 3)), Θ '' S = Θi ⁻¹' S :=
    fun S => by rw [image_eq_preimage_of_inverse hl hr]
  refine ⟨ρ, hρ, v₀ ∘ Θi, ?_, ?_, ?_⟩
  · rw [himg]
    exact isOpen_ball.preimage hΘi.continuous
  · rw [himg]
    exact (hv₀.mono (ball_subset_ball hρρ₀)).comp (hΘi.of_le (by simp)).contDiffOn
      (fun x hx => hx)
  · -- equality on the open part, then up to the face by continuity
    have hupper : ball (0 : EuclideanSpace ℝ (Fin 3)) ρ ∩ {y | 0 ≤ y (Fin.last 2)} ⊆ K :=
      fun y hy => boundary_neumann_reflect_mem_closure
        (ball_subset_ball hρ1 hy.1) hy.2
    have hopen : EqOn v₀ (u ∘ Θ) (boundaryHalfBall ρ) :=
      fun y hy => hv₀u (boundaryHalfBall_mono hρρ₀ hy)
    have hv₀c : ContinuousOn v₀ (ball 0 ρ) :=
      (hv₀.mono (ball_subset_ball hρρ₀)).continuousOn
    have huc : ContinuousOn (u ∘ Θ) O := hut.contDiffOn.continuousOn
    have hcl : EqOn v₀ (u ∘ Θ) (ball 0 ρ ∩ {y | 0 ≤ y (Fin.last 2)}) := by
      refine EqOn.of_subset_closure (s := boundaryHalfBall ρ) ?_
        (hv₀c.mono inter_subset_left) (huc.mono (hupper.trans hKO))
        (fun y hy => ⟨hy.1, show 0 ≤ y (Fin.last 2) from le_of_lt hy.2⟩) ?_
      · exact hopen
      · intro y hy
        exact boundary_neumann_reflect_mem_closure hy.1 hy.2
    rintro x ⟨y, hy, rfl⟩
    simpa [Function.comp_def, hl y] using hcl hy

/-- **`thm:boundary-C2a`, all higher regularity in a shear chart.** For a graph chart with a
smooth, globally Lipschitz height and `ρ ≠ 0`, the conclusion of
`boundary_c2a_curved_smooth_all_orders` holds for the shear flattening
`Θ = boundaryShearMap c a ρ`. -/
theorem boundary_c2a_shear_smooth_all_orders {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (c : C1BoundaryChart) (a : EuclideanSpace ℝ (Fin 2)) {ρ : ℝ} (hρ : ρ ≠ 0)
    (hh : ContDiff ℝ (⊤ : ℕ∞) c.height) {Lh : ℝ≥0} (hhlip : LipschitzWith Lh c.height)
    {W : Set (EuclideanSpace ℝ (Fin 3))} (hW : IsOpen W)
    (hWΘ : boundaryShearMap c a ρ '' closure (boundaryHalfBall 1) ⊆ W)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) A W) (hG : ContDiffOn ℝ (⊤ : ℕ∞) G W)
    {lamA : ℝ} (hlamA : 0 < lamA)
    (hAe : ∀ x ∈ boundaryShearMap c a ρ '' closure (boundaryHalfBall 1), ∀ ξ,
      lamA * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ)
    {u φ : EuclideanSpace ℝ (Fin 3) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hu : HasCkHolderOn 1 α u W (boundaryShearMap c a ρ '' closure (boundaryHalfBall 1)))
    (hface : ∀ y ∈ closure (boundaryHalfBall 1), y (Fin.last 2) = 0 →
      u (boundaryShearMap c a ρ y) = φ (boundaryShearMap c a ρ y))
    (hw : IsWeakDivergenceEquationOn A (gradient u) G
      (boundaryShearMap c a ρ '' boundaryHalfBall 1)) :
    ∀ k : ℕ, ∃ r > 0, ∃ v : EuclideanSpace ℝ (Fin 3) → ℝ,
      IsOpen (boundaryShearMap c a ρ '' ball 0 r) ∧
      ContDiffOn ℝ k v (boundaryShearMap c a ρ '' ball 0 r) ∧
      EqOn v u (boundaryShearMap c a ρ '' (ball 0 r ∩ {y | 0 ≤ y (Fin.last 2)})) := by
  obtain ⟨CΘ, hCΘ⟩ := boundaryShearMap_lipschitz c a ρ hhlip
  have hΘ : ContDiff ℝ (⊤ : ℕ∞) (boundaryShearMap c a ρ) :=
    contDiff_infty.mpr fun n => contDiff_boundaryShearMap c a ρ (contDiff_infty.mp hh n)
  have hΘi : ContDiff ℝ (⊤ : ℕ∞) (boundaryShearInv c a ρ) :=
    contDiff_infty.mpr fun n => contDiff_boundaryShearInv c a ρ (contDiff_infty.mp hh n)
  exact boundary_c2a_curved_smooth_all_orders hα hα1 hΘ hΘi
    (boundaryShearMap_leftInverse c a hρ) (boundaryShearMap_rightInverse c a hρ) hCΘ hW hWΘ
    hA hG hlamA hAe hφ hu hface hw

end LiquidDrop
