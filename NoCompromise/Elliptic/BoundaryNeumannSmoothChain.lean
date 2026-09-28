import NoCompromise.Elliptic.BoundaryNeumannCkLevel
import NoCompromise.Elliptic.BoundaryFaceExtension

/-!
# Chaining the levels of the smooth boundary Neumann iteration (`thm:boundary-neumann`)

Given every level `BoundaryNeumannCkLevel k`, a `C^{1,α}` solution `w` of the homogeneous
flat conormal problem with smooth coefficient `A` and smooth datum `H` on the half ball of
radius `R ≤ 1` agrees, for every `k`, on a smaller half ball with a function which is `C^k`
on the full ball of that radius. The proof is an induction on the invariant: on a closed
half ball of radius `r ≤ R`, `w` agrees with a function `w'` which is `C^{k+1,α}` relative
to an open neighbourhood and has vanishing normal derivative on the flat face. The level
`k` upgrades `w'` to `C^{k+2,α}` on the open half ball of radius `ρ = (3/8) (1/2)ᵏ r`; the
iterated derivatives of order `≤ k + 2` are then uniformly continuous there (Hölder on a
convex bounded set), so the flat-face extension gives a `C^{k+2}` function on `ball 0 ρ`
which keeps the Hölder bound on the closed upper part; its restriction to the closed half
ball of radius `ρ / 2` is the new `w'`, and the face condition passes to it by continuity
of the gradients.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- The closed half ball lies in the closed ball and in the closed upper half space. -/
lemma boundaryNeumannSmoothChain_closure_subset (r : ℝ) :
    closure (boundaryHalfBall r) ⊆
      closedBall (0 : EuclideanSpace ℝ (Fin 3)) r ∩ {x | 0 ≤ x (Fin.last 2)} :=
  closure_minimal (inter_subset_inter ball_subset_closedBall
      fun x (hx : 0 < x (Fin.last 2)) => (le_of_lt hx : 0 ≤ x (Fin.last 2)))
    (isClosed_closedBall.inter
      (isClosed_le continuous_const (EuclideanSpace.proj (Fin.last 2)).continuous))

lemma boundaryNeumannSmoothChain_isCompact_closure (r : ℝ) :
    IsCompact (closure (boundaryHalfBall r)) :=
  (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) r).of_isClosed_subset isClosed_closure
    ((boundaryNeumannSmoothChain_closure_subset r).trans inter_subset_left)

/-- A Hölder bound with positive exponent gives uniform continuity. -/
lemma boundaryNeumannSmoothChain_uniformContinuousOn {E F : Type*} [PseudoMetricSpace E]
    [SeminormedAddCommGroup F] {g : E → F} {S : Set E} {α C : ℝ} (hα : 0 < α)
    (h : ∀ x ∈ S, ∀ y ∈ S, ‖g x - g y‖ ≤ C * dist x y ^ α) : UniformContinuousOn g S := by
  rw [Metric.uniformContinuousOn_iff]
  intro ε hε
  have hC : 0 < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨(ε / max C 1) ^ (1 / α), by positivity, fun x hx y hy hxy => ?_⟩
  rw [dist_eq_norm]
  have hd : 0 ≤ dist x y := dist_nonneg
  calc ‖g x - g y‖ ≤ C * dist x y ^ α := h x hx y hy
    _ ≤ max C 1 * dist x y ^ α :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hd _)
    _ < max C 1 * ((ε / max C 1) ^ (1 / α)) ^ α :=
        mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hd hxy hα) hC
    _ = ε := by
        rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hα.ne', Real.rpow_one]
        field_simp

/-- Functions agreeing on an open set have equal gradients there. -/
lemma boundaryNeumannSmoothChain_gradient_eqOn {f g : EuclideanSpace ℝ (Fin 3) → ℝ}
    {S : Set (EuclideanSpace ℝ (Fin 3))} (hS : IsOpen S) (h : EqOn f g S) :
    EqOn (gradient f) (gradient g) S := fun x hx => by
  have hfg : f =ᶠ[𝓝 x] g := Filter.eventuallyEq_of_mem (hS.mem_nhds hx) h
  simp only [gradient, hfg.fderiv_eq]

/-- The weak conormal equation on the half ball of radius `R₀` restricts to every smaller
radius, also after changing the field on the smaller open half ball. -/
lemma boundaryNeumannSmoothChain_equation_restrict
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    {F G H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)} {r R₀ : ℝ} (hr : r ≤ R₀)
    (he : IsBoundaryNeumannEquationOn A F H R₀) (hFG : EqOn G F (boundaryHalfBall r)) :
    IsBoundaryNeumannEquationOn A G H r := by
  intro φ hφ hφc hφs
  have hz : ∀ x ∉ ball (0 : EuclideanSpace ℝ (Fin 3)) r, gradient φ x = 0 := by
    intro x hx
    have hx' : x ∉ tsupport φ := fun h => hx (hφs h)
    have h0 : fderiv ℝ φ x = 0 := by
      by_contra h
      exact hx' (support_fderiv_subset ℝ h)
    simp [gradient, h0]
  have h1 := he φ hφ hφc (hφs.trans (ball_subset_ball hr))
  calc (∫ x in boundaryHalfBall r, inner ℝ (A x (G x) - H x) (gradient φ x))
      = ∫ x in boundaryHalfBall r, inner ℝ (A x (F x) - H x) (gradient φ x) :=
        setIntegral_congr_fun (isOpen_boundaryHalfBall r).measurableSet
          fun x hx => by simp only [hFG hx]
    _ = ∫ x in {x : EuclideanSpace ℝ (Fin 3) | 0 < x (Fin.last 2)},
          inner ℝ (A x (F x) - H x) (gradient φ x) :=
        (boundary_neumann_integral_upper_eq _ fun x hx => by
          rw [hz x hx, inner_zero_right]).symm
    _ = ∫ x in boundaryHalfBall R₀, inner ℝ (A x (F x) - H x) (gradient φ x) :=
        boundary_neumann_integral_upper_eq _ fun x hx => by
          rw [hz x fun h => hx (ball_subset_ball hr h), inner_zero_right]
    _ = 0 := h1

/-- The invariant of the smooth iteration at order `k`: on a closed half ball of radius
`r ≤ R₀`, `w` agrees on the open half ball with a function which is `C^{k+1,α}` relative to
an open neighbourhood of the closed half ball and has vanishing normal derivative on the
flat face. -/
def boundaryNeumannSmoothChain_Inv (α R₀ : ℝ) (w : EuclideanSpace ℝ (Fin 3) → ℝ) (k : ℕ) :
    Prop :=
  ∃ r : ℝ, 0 < r ∧ r ≤ R₀ ∧ ∃ U' : Set (EuclideanSpace ℝ (Fin 3)), IsOpen U' ∧
    closure (boundaryHalfBall r) ⊆ U' ∧ ∃ w' : EuclideanSpace ℝ (Fin 3) → ℝ,
      EqOn w' w (boundaryHalfBall r) ∧
      HasCkHolderOn (k + 1) α w' U' (closure (boundaryHalfBall r)) ∧
      ∀ x ∈ closure (boundaryHalfBall r), x (Fin.last 2) = 0 →
        gradient w' x (Fin.last 2) = 0

/-- One step of the smooth iteration: the level `k` together with the flat-face extension
upgrades the invariant from order `k` to order `k + 1`. -/
theorem boundaryNeumannSmoothChain_step {k : ℕ} (hlev : BoundaryNeumannCkLevel k)
    {α lam cap R : ℝ} (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hR1 : R ≤ 1)
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U)
    (hUc : closure (boundaryHalfBall R) ⊆ U)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {w : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) A U) (hH : ContDiffOn ℝ (⊤ : ℕ∞) H U)
    (hcap : ∀ x ∈ closure (boundaryHalfBall R), ‖A x‖ ≤ cap)
    (hell : ∀ x ∈ closure (boundaryHalfBall R), ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    (hcross : ∀ x ∈ closure (boundaryHalfBall R), x (Fin.last 2) = 0 →
      ∀ j : Fin 3, j ≠ Fin.last 2 →
        A x (EuclideanSpace.single j 1) (Fin.last 2) = 0 ∧
        A x (EuclideanSpace.single (Fin.last 2) 1) j = 0)
    (hH0 : ∀ x ∈ closure (boundaryHalfBall R), x (Fin.last 2) = 0 → H x (Fin.last 2) = 0)
    (he : IsBoundaryNeumannEquationOn A (gradient w) H R)
    (hinv : boundaryNeumannSmoothChain_Inv α R w k) :
    boundaryNeumannSmoothChain_Inv α R w (k + 1) := by
  obtain ⟨r, hr0, hrR, U', hU', hKU', w', hww, hw', hface⟩ := hinv
  have hr1 : r ≤ 1 := hrR.trans hR1
  have hK1 : closure (boundaryHalfBall r) ⊆ closure (boundaryHalfBall R) :=
    closure_mono (boundaryHalfBall_mono hrR)
  have hKV : closure (boundaryHalfBall r) ⊆ U ∩ U' := subset_inter (hK1.trans hUc) hKU'
  have hV : IsOpen (U ∩ U') := hU.inter hU'
  have hKconv : Convex ℝ (closure (boundaryHalfBall r)) := (convex_boundaryHalfBall r).closure
  have hKc : IsCompact (closure (boundaryHalfBall r)) :=
    boundaryNeumannSmoothChain_isCompact_closure r
  have hHV : HasCkHolderOn (k + 1) α H (U ∩ U') (closure (boundaryHalfBall r)) :=
    HasCkHolderOn.of_contDiffOn_smooth hα1.le hV hKV hKconv hKc (hH.mono inter_subset_left)
      (k + 1)
  have hwV : HasCkHolderOn (k + 1) α w' (U ∩ U') (closure (boundaryHalfBall r)) :=
    ⟨hw'.contDiffOn.mono inter_subset_right, hw'.bounded, hw'.holder⟩
  have he' : IsBoundaryNeumannEquationOn A (gradient w') H r :=
    boundaryNeumannSmoothChain_equation_restrict hrR he
      (boundaryNeumannSmoothChain_gradient_eqOn (isOpen_boundaryHalfBall r) hww)
  have hS := hlev hα hα1 hlam hr0 hr1 hV hKV (hA.mono inter_subset_left) hHV hwV
    (fun x hx => hcap x (hK1 hx)) (fun x hx => hell x (hK1 hx))
    (fun x hx => hcross x (hK1 hx)) (fun x hx => hH0 x (hK1 hx)) hface he'
  set ρ : ℝ := 3 / 8 * (1 / 2) ^ k * r with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρr : ρ ≤ r := by
    have hp : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hp0 : 0 ≤ (1 / 2 : ℝ) ^ k := by positivity
    rw [hρ]
    nlinarith
  have hSo : IsOpen (boundaryHalfBall ρ) := isOpen_boundaryHalfBall ρ
  have hSconv : Convex ℝ (boundaryHalfBall ρ) := convex_boundaryHalfBall ρ
  have hSb : Bornology.IsBounded (boundaryHalfBall ρ) := isBounded_ball.subset inter_subset_left
  have huc : ∀ m ≤ k + 2, UniformContinuousOn (iteratedFDeriv ℝ m w') (boundaryHalfBall ρ) := by
    intro m hm
    obtain ⟨C, hC⟩ := (hS.mono_order hm hα1.le hSo subset_rfl hSconv hSb).holder
    exact boundaryNeumannSmoothChain_uniformContinuousOn hα hC
  obtain ⟨C, hC⟩ := hS.holder
  obtain ⟨w'', hw''w', hw''c, hw''h⟩ := boundary_face_extension_holder hS.contDiffOn huc hC hα
  have hT : closure (boundaryHalfBall (ρ / 2)) ⊆ ball (0 : EuclideanSpace ℝ (Fin 3)) ρ :=
    fun x hx => closedBall_subset_ball (by linarith)
      (boundaryNeumannSmoothChain_closure_subset (ρ / 2) hx).1
  have hTr : closure (boundaryHalfBall (ρ / 2)) ⊆ closure (boundaryHalfBall r) :=
    closure_mono (boundaryHalfBall_mono (by linarith))
  have hTS : boundaryHalfBall (ρ / 2) ⊆ boundaryHalfBall ρ := boundaryHalfBall_mono (by linarith)
  refine ⟨ρ / 2, by positivity, by linarith, ball 0 ρ, isOpen_ball, hT, w'', ?_, ?_, ?_⟩
  · intro x hx
    rw [hw''w' (hTS hx)]
    exact hww (boundaryHalfBall_mono hρr (hTS hx))
  · refine ⟨hw''c, fun m hm => ?_, C, fun x hx y hy => ?_⟩
    · have hm' : m ≤ k + 2 := hm
      have hcont : ContinuousOn (iteratedFDeriv ℝ m w'') (closure (boundaryHalfBall (ρ / 2))) :=
        fun x hx => ((hw''c.contDiffAt (isOpen_ball.mem_nhds (hT hx))).continuousAt_iteratedFDeriv
          (by exact_mod_cast hm')).continuousWithinAt
      exact (boundaryNeumannSmoothChain_isCompact_closure (ρ / 2)).exists_bound_of_continuousOn
        hcont
    · exact hw''h x (hT hx) (boundaryNeumannSmoothChain_closure_subset (ρ / 2) hx).2
        y (hT hy) (boundaryNeumannSmoothChain_closure_subset (ρ / 2) hy).2
  · intro x hx hx0
    have hc1 : ContinuousOn (fderiv ℝ w'') (ball 0 ρ) :=
      hw''c.continuousOn_fderiv_of_isOpen isOpen_ball (by exact_mod_cast (by omega : 1 ≤ k + 2))
    have hc2 : ContinuousOn (fderiv ℝ w') U' :=
      hw'.contDiffOn.continuousOn_fderiv_of_isOpen hU' (by exact_mod_cast (by omega : 1 ≤ k + 1))
    have heq : EqOn (fderiv ℝ w'') (fderiv ℝ w') (boundaryHalfBall (ρ / 2)) := fun y hy =>
      (Filter.eventuallyEq_of_mem (hSo.mem_nhds (hTS hy)) hw''w').fderiv_eq
    have heq' := heq.of_subset_closure (hc1.mono hT) (hc2.mono (hTr.trans hKU')) subset_closure
      subset_rfl
    have hg : gradient w'' x = gradient w' x := by simp only [gradient, heq' hx]
    rw [hg]
    exact hface x (hTr hx) hx0

/-- Smooth iteration of the flat boundary Neumann problem, given all the levels: a
`C^{1,α}` solution with smooth coefficient and datum agrees, for every `k`, on a small
half ball with a function which is `C^k` on the full ball of that radius. -/
theorem boundary_neumann_smooth_of_levels (hlev : ∀ k, BoundaryNeumannCkLevel k)
    {α lam cap R : ℝ} (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hR : 0 < R) (hR1 : R ≤ 1)
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U)
    (hUc : closure (boundaryHalfBall R) ⊆ U)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {w : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) A U) (hH : ContDiffOn ℝ (⊤ : ℕ∞) H U)
    (hw : HasCkHolderOn 1 α w U (closure (boundaryHalfBall R)))
    (hcap : ∀ x ∈ closure (boundaryHalfBall R), ‖A x‖ ≤ cap)
    (hell : ∀ x ∈ closure (boundaryHalfBall R), ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    (hcross : ∀ x ∈ closure (boundaryHalfBall R), x (Fin.last 2) = 0 →
      ∀ j : Fin 3, j ≠ Fin.last 2 →
        A x (EuclideanSpace.single j 1) (Fin.last 2) = 0 ∧
        A x (EuclideanSpace.single (Fin.last 2) 1) j = 0)
    (hH0 : ∀ x ∈ closure (boundaryHalfBall R), x (Fin.last 2) = 0 → H x (Fin.last 2) = 0)
    (hw0 : ∀ x ∈ closure (boundaryHalfBall R), x (Fin.last 2) = 0 →
      gradient w x (Fin.last 2) = 0)
    (he : IsBoundaryNeumannEquationOn A (gradient w) H R) :
    ∀ k : ℕ, ∃ ρ > 0, ∃ v : EuclideanSpace ℝ (Fin 3) → ℝ,
      EqOn v w (boundaryHalfBall ρ) ∧ ContDiffOn ℝ k v (ball 0 ρ) := by
  have hinv : ∀ k, boundaryNeumannSmoothChain_Inv α R w k := by
    intro k
    induction k with
    | zero => exact ⟨R, hR, le_rfl, U, hU, hUc, w, fun _ _ => rfl, hw, hw0⟩
    | succ k ih =>
      exact boundaryNeumannSmoothChain_step (hlev k) hα hα1 hlam hR1 hU hUc hA hH hcap hell
        hcross hH0 he ih
  intro k
  obtain ⟨r, hr0, hrR, U', hU', hKU', w', hww, hw', -⟩ := hinv k
  have h0 : (0 : EuclideanSpace ℝ (Fin 3)) ∈ U' :=
    hKU' (boundary_neumann_reflect_mem_closure (mem_ball_self hr0) (by simp))
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU' 0 h0
  refine ⟨min ε r, lt_min hε hr0, w', fun x hx => hww (boundaryHalfBall_mono (min_le_right _ _) hx),
    ?_⟩
  exact (hw'.contDiffOn.mono ((ball_subset_ball (min_le_left _ _)).trans hεU)).of_le
    (by exact_mod_cast Nat.le_succ k)

end LiquidDrop
