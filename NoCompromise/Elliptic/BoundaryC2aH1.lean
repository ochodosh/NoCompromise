module

public import NoCompromise.Elliptic.BoundaryC1Slab
public import NoCompromise.Sobolev.H1Algebra

@[expose] public section

/-!
# Boundary C¹,α from H¹ with a nonzero trace (first step of `thm:boundary-C2a`)

`thm:boundary-C2a` starts from an H¹ weak solution of `div(A∇w) = div G` on the half ball
whose flat trace is the restriction of a given function `φ`. Its proof begins by subtracting
`φ`: `w - φ` has zero flat trace and solves `div(A∇(w - φ)) = div(G - A∇φ)`, whose datum is
α-Hölder when `A` and `∇φ` are. The C¹,α theorem on the fixed slab
(`boundary_c1_holder_slab`) then applies, and adding `φ` back gives a C¹ representative of
`w` with α-Hölder gradient on a fixed neighbourhood of the flat disk, equal to `φ` on the
flat face. The constants depend only on the displayed bounds.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- A C¹ function with bounded gradient on the unit half ball is H¹ there. -/
lemma boundary_c2a_hasH1GradientOn_of_contDiff {φ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hφ : ContDiff ℝ 1 φ) : HasH1GradientOn φ (gradient φ) (boundaryHalfBall 1) := by
  have hU := isOpen_boundaryHalfBall (1 : ℝ)
  have hbU : Bornology.IsBounded (boundaryHalfBall 1) :=
    isBounded_ball.subset inter_subset_left
  let : IsFiniteMeasure (volume.restrict (boundaryHalfBall 1)) :=
    ⟨by simpa using hbU.measure_lt_top⟩
  obtain ⟨C, hC⟩ := hbU.isCompact_closure.exists_bound_of_continuousOn hφ.continuous.continuousOn
  obtain ⟨B, hB⟩ := hbU.isCompact_closure.exists_bound_of_continuousOn
    (continuous_gradient_of_contDiff hφ).continuousOn
  refine ⟨hasWeakGradientOn_of_contDiffOn hU hφ.contDiffOn,
    MemLp.of_bound hφ.continuous.aestronglyMeasurable C ?_,
    MemLp.of_bound (continuous_gradient_of_contDiff hφ).aestronglyMeasurable B ?_⟩
  · filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact hC x (subset_closure hx)
  · filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact hB x (subset_closure hx)

/-- Blueprint `thm:boundary-C2a`, first step (H¹ start with a nonzero trace): for an H¹ weak
solution `u` of `div(A∇u) = div G` on the unit half ball, with continuous α-Hölder `A, G`,
uniform ellipticity, and flat trace equal to that of a C¹ function `φ` whose gradient is
bounded by `P₁` and α-Hölder with constant `P₂` on the closed unit ball, `u` has a C¹
representative `v` on an open `W` containing the closed flat disk of radius `1/2` and the fixed
slab `boundaryC1Slab`, with `∇v = F` a.e., `‖∇v‖ ≤ P`, `∇v` α-Hölder with constant `C`, and
`v = φ` on the flat face. `C` and `P` are chosen before the data. -/
theorem boundary_c1_holder_slab_trace {a lam cap HA HG M P₁ P₂ : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hlam : 0 < lam) (hcap : 0 ≤ cap)
    (hHA : 0 ≤ HA) (hHG : 0 ≤ HG) (hM : 0 ≤ M) (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂) :
    ∃ C P : ℝ, 0 < C ∧ 0 ≤ P ∧
      ∀ (u φ : EuclideanSpace ℝ (Fin 3) → ℝ)
        (F G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
        (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
          EuclideanSpace ℝ (Fin 3)),
        ContinuousOn A (closure (boundaryHalfBall 1)) →
        ContinuousOn G (closure (boundaryHalfBall 1)) →
        (∀ x ∈ closure (boundaryHalfBall 1), ‖A x‖ ≤ cap) →
        (∀ x ∈ closure (boundaryHalfBall 1), ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ) →
        (∀ x ∈ closure (boundaryHalfBall 1), ∀ y ∈ closure (boundaryHalfBall 1),
          ‖A x - A y‖ ≤ HA * dist x y ^ a) →
        (∀ x ∈ closure (boundaryHalfBall 1), ∀ y ∈ closure (boundaryHalfBall 1),
          ‖G x - G y‖ ≤ HG * dist x y ^ a) →
        HasH1GradientOn u F (boundaryHalfBall 1) →
        IsWeakDivergenceEquationOn A F G (boundaryHalfBall 1) →
        ContDiff ℝ 1 φ →
        (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, ‖gradient φ x‖ ≤ P₁) →
        (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1,
          ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1,
          ‖gradient φ x - gradient φ y‖ ≤ P₂ * dist x y ^ a) →
        HasZeroFlatTraceOn (fun x => u x - φ x) (fun x => F x - gradient φ x) (ball 0 1) →
        (∫ x in boundaryHalfBall 1, ‖F x - gradient φ x‖ ^ 2) ≤ M →
        ∃ (W : Set (EuclideanSpace ℝ (Fin 3))) (v : EuclideanSpace ℝ (Fin 3) → ℝ),
          IsOpen W ∧ {x | ‖x‖ ≤ (1 / 2 : ℝ) ∧ x (Fin.last 2) = 0} ⊆ W ∧
          W ⊆ ball 0 (3 / 4 : ℝ) ∧ ContDiffOn ℝ 1 v W ∧
          v =ᵐ[volume.restrict (W ∩ {x | 0 < x (Fin.last 2)})] u ∧
          gradient v =ᵐ[volume.restrict (W ∩ {x | 0 < x (Fin.last 2)})] F ∧
          (∀ x ∈ W, ‖gradient v x‖ ≤ P) ∧
          (∀ x ∈ W, ∀ y ∈ W, ‖gradient v x - gradient v y‖ ≤ C * dist x y ^ a) ∧
          (∀ x ∈ W, x (Fin.last 2) = 0 → v x = φ x) ∧ boundaryC1Slab ⊆ W := by
  have hHG' : 0 ≤ HG + HA * P₁ + cap * P₂ := by positivity
  obtain ⟨C₀, P₀, hC₀, hP₀, hreg⟩ := boundary_c1_holder_slab ha ha1 hlam hcap hHA hHG' hM
  refine ⟨C₀ + P₂, P₀ + P₁, by positivity, by positivity, ?_⟩
  intro u φ F G A hAc hGc hcapb hell hAh hGh hu he hφ hφb hφh htr hen
  have hgradc : Continuous (gradient φ) := continuous_gradient_of_contDiff hφ
  have hsub : closure (boundaryHalfBall 1) ⊆ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    closure_minimal (inter_subset_left.trans ball_subset_closedBall) isClosed_closedBall
  let G' : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) :=
    fun x => G x - A x (gradient φ x)
  have hG'c : ContinuousOn G' (closure (boundaryHalfBall 1)) :=
    hGc.sub (hAc.clm_apply hgradc.continuousOn)
  have hG'h : ∀ x ∈ closure (boundaryHalfBall 1), ∀ y ∈ closure (boundaryHalfBall 1),
      ‖G' x - G' y‖ ≤ (HG + HA * P₁ + cap * P₂) * dist x y ^ a := by
    intro x hx y hy
    have hd : 0 ≤ dist x y ^ a := Real.rpow_nonneg dist_nonneg _
    have he' : G' x - G' y =
        (G x - G y) - ((A x - A y) (gradient φ x) + A y (gradient φ x - gradient φ y)) := by
      simp only [G', sub_apply, map_sub]
      abel
    have h1 : ‖(A x - A y) (gradient φ x)‖ ≤ HA * dist x y ^ a * P₁ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul (hAh x hx y hy) (hφb x (hsub hx)) (norm_nonneg _) (by positivity))
    have h2 : ‖A y (gradient φ x - gradient φ y)‖ ≤ cap * (P₂ * dist x y ^ a) :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul (hcapb y hy) (hφh x (hsub hx) y (hsub hy)) (norm_nonneg _) hcap)
    rw [he']
    calc _ ≤ ‖G x - G y‖ + (‖(A x - A y) (gradient φ x)‖ +
          ‖A y (gradient φ x - gradient φ y)‖) :=
          (norm_sub_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
      _ ≤ HG * dist x y ^ a + (HA * dist x y ^ a * P₁ + cap * (P₂ * dist x y ^ a)) :=
          add_le_add (hGh x hx y hy) (add_le_add h1 h2)
      _ = (HG + HA * P₁ + cap * P₂) * dist x y ^ a := by ring
  have heq : IsWeakDivergenceEquationOn A (fun x => F x - gradient φ x) G'
      (boundaryHalfBall 1) := by
    intro ψ h1 h2 h3
    have h := he ψ h1 h2 h3
    have hfun : (fun x => inner ℝ (A x (F x - gradient φ x) - G' x) (gradient ψ x)) =
        fun x => inner ℝ (A x (F x) - G x) (gradient ψ x) := by
      funext x
      congr 1
      simp only [G', map_sub]
      abel
    rw [hfun]
    exact h
  have d : BoundaryHolderUnitData a lam cap HA (HG + HA * P₁ + cap * P₂) M
      (fun x => u x - φ x) (fun x => F x - gradient φ x) G' A :=
    { coefficient_continuous := hAc
      datum_continuous := hG'c
      coefficient_bound := hcapb
      elliptic := hell
      coefficient_holder := hAh
      datum_holder := hG'h
      h1 := hu.sub (boundary_c2a_hasH1GradientOn_of_contDiff hφ)
      trace_zero := htr
      equation := heq
      energy_bound := hen }
  obtain ⟨W, v₀, hW, hdisk, hWb, hv₀, hae, hgae, hgb, hgh, hflat, hslab⟩ := hreg _ _ _ _ d
  have hWc : W ⊆ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    hWb.trans (ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num)))
  have hgsum : ∀ x ∈ W, gradient (fun y => v₀ y + φ y) x = gradient v₀ x + gradient φ x := by
    intro x hx
    have hd₀ : DifferentiableAt ℝ v₀ x :=
      (hv₀.differentiableOn one_ne_zero x hx).differentiableAt (hW.mem_nhds hx)
    have hd₁ : DifferentiableAt ℝ φ x := hφ.differentiable one_ne_zero x
    unfold gradient
    rw [show (fun y => v₀ y + φ y) = v₀ + φ from rfl, fderiv_add hd₀ hd₁, map_add]
  have hupper : MeasurableSet (W ∩ {x : EuclideanSpace ℝ (Fin 3) | 0 < x (Fin.last 2)}) :=
    hW.measurableSet.inter (isOpen_lt continuous_const
      (EuclideanSpace.proj (Fin.last 2) : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).continuous
      ).measurableSet
  refine ⟨W, fun x => v₀ x + φ x, hW, hdisk, hWb, hv₀.add hφ.contDiffOn, ?_, ?_, ?_, ?_, ?_,
    hslab⟩
  · filter_upwards [hae] with x hx
    rw [hx]
    simp
  · filter_upwards [hgae, ae_restrict_mem hupper] with x hx hxW
    rw [hgsum x hxW.1, hx]
    simp
  · intro x hx
    rw [hgsum x hx]
    exact (norm_add_le _ _).trans (add_le_add (hgb x hx) (hφb x (hWc hx)))
  · intro x hx y hy
    rw [hgsum x hx, hgsum y hy, add_sub_add_comm, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hgh x hx y hy) (hφh x (hWc hx) y (hWc hy)))
  · intro x hx hx0
    simp only [hflat x hx hx0, zero_add]

end LiquidDrop
