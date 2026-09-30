module

public import NoCompromise.Elliptic.BoundaryC2aCkBase
public import NoCompromise.Elliptic.BoundaryFaceExtension
public import NoCompromise.Elliptic.BoundaryNeumannSmoothChain

@[expose] public section

/-!
# Chaining the levels of the Dirichlet boundary higher-regularity iteration (`thm:boundary-C2a`)

A `C^{1,α}` solution `u` of the flat Dirichlet problem `div(A ∇u) = div G` in the half ball
of radius `R ≤ 1`, with smooth coefficient `A`, smooth datum `G` and smooth boundary datum
`φ` (`u = φ` on the flat face), agrees, for every `k`, on a smaller half ball with a function
which is `C^k` on the full ball of that radius. The proof mirrors the Neumann chain
`boundary_neumann_smooth_of_levels`: the invariant at order `k` is that, on a closed half
ball of radius `r ≤ R`, `u` agrees on the open half ball with a function `u'` which is
`C^{k+1,α}` relative to an open neighbourhood and equals `φ` on the flat face. The level
`boundaryDirichletCkLevel_holds k` upgrades `u'` to `C^{k+2,α}` on the open half ball of
radius `ρ = (3/8) (1/2)ᵏ r`; the flat-face extension gives a `C^{k+2}` function on `ball 0 ρ`
keeping the Hölder bound on the closed upper part; its restriction to the closed half ball
of radius `ρ / 2` is the new `u'`, and the face condition passes to it by continuity.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- The weak Dirichlet-form equation on the half ball of radius `R₀` restricts to every
smaller radius, also after changing the field on the smaller open half ball. -/
lemma boundaryC2aSmoothChain_equation_restrict
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    {F D G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)} {r R₀ : ℝ} (hr : r ≤ R₀)
    (he : IsWeakDivergenceEquationOn A F G (boundaryHalfBall R₀))
    (hFD : EqOn D F (boundaryHalfBall r)) :
    IsWeakDivergenceEquationOn A D G (boundaryHalfBall r) := by
  intro ψ hψ hψc hψs
  have hz : ∀ x ∉ boundaryHalfBall r, gradient ψ x = 0 := by
    intro x hx
    have hx' : x ∉ tsupport ψ := fun h => hx (hψs h)
    have h0 : fderiv ℝ ψ x = 0 := by
      by_contra h
      exact hx' (support_fderiv_subset ℝ h)
    simp [gradient, h0]
  have h1 := he ψ hψ hψc (hψs.trans (boundaryHalfBall_mono hr))
  calc (∫ x, inner ℝ (A x (D x) - G x) (gradient ψ x))
      = ∫ x, inner ℝ (A x (F x) - G x) (gradient ψ x) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        by_cases hx : x ∈ boundaryHalfBall r
        · simp only [hFD hx]
        · simp only [hz x hx, inner_zero_right]
    _ = 0 := h1

/-- The invariant of the Dirichlet smooth iteration at order `k`: on a closed half ball of
radius `r ≤ R₀`, `u` agrees on the open half ball with a function which is `C^{k+1,α}`
relative to an open neighbourhood of the closed half ball and equals `φ` on the flat face. -/
def boundaryC2aSmoothChain_Inv (α R₀ : ℝ) (u φ : EuclideanSpace ℝ (Fin 3) → ℝ) (k : ℕ) :
    Prop :=
  ∃ r : ℝ, 0 < r ∧ r ≤ R₀ ∧ ∃ U' : Set (EuclideanSpace ℝ (Fin 3)), IsOpen U' ∧
    closure (boundaryHalfBall r) ⊆ U' ∧ ∃ u' : EuclideanSpace ℝ (Fin 3) → ℝ,
      EqOn u' u (boundaryHalfBall r) ∧
      HasCkHolderOn (k + 1) α u' U' (closure (boundaryHalfBall r)) ∧
      ∀ x ∈ closure (boundaryHalfBall r), x (Fin.last 2) = 0 → u' x = φ x

/-- One step of the Dirichlet smooth iteration: the level `k` together with the flat-face
extension upgrades the invariant from order `k` to order `k + 1`. -/
theorem boundaryC2aSmoothChain_step (k : ℕ)
    {α lam cap R : ℝ} (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hR1 : R ≤ 1)
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U)
    (hUc : closure (boundaryHalfBall R) ⊆ U)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {u φ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) A U) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G U)
    (hcap : ∀ x ∈ closure (boundaryHalfBall R), ‖A x‖ ≤ cap)
    (hell : ∀ x ∈ closure (boundaryHalfBall R), ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    (he : IsWeakDivergenceEquationOn A (gradient u) G (boundaryHalfBall R))
    (hinv : boundaryC2aSmoothChain_Inv α R u φ k) :
    boundaryC2aSmoothChain_Inv α R u φ (k + 1) := by
  obtain ⟨r, hr0, hrR, U', hU', hKU', w', hww, hw', hface⟩ := hinv
  have hr1 : r ≤ 1 := hrR.trans hR1
  have hK1 : closure (boundaryHalfBall r) ⊆ closure (boundaryHalfBall R) :=
    closure_mono (boundaryHalfBall_mono hrR)
  have hKV : closure (boundaryHalfBall r) ⊆ U ∩ U' := subset_inter (hK1.trans hUc) hKU'
  have hV : IsOpen (U ∩ U') := hU.inter hU'
  have hKconv : Convex ℝ (closure (boundaryHalfBall r)) := (convex_boundaryHalfBall r).closure
  have hKc : IsCompact (closure (boundaryHalfBall r)) :=
    boundaryNeumannSmoothChain_isCompact_closure r
  have hGV : HasCkHolderOn (k + 1) α G (U ∩ U') (closure (boundaryHalfBall r)) :=
    HasCkHolderOn.of_contDiffOn_smooth hα1.le hV hKV hKconv hKc (hG.mono inter_subset_left)
      (k + 1)
  have hwV : HasCkHolderOn (k + 1) α w' (U ∩ U') (closure (boundaryHalfBall r)) :=
    ⟨hw'.contDiffOn.mono inter_subset_right, hw'.bounded, hw'.holder⟩
  have he' : IsWeakDivergenceEquationOn A (gradient w') G (boundaryHalfBall r) :=
    boundaryC2aSmoothChain_equation_restrict hrR he
      (boundaryNeumannSmoothChain_gradient_eqOn (isOpen_boundaryHalfBall r) hww)
  have hS := boundaryDirichletCkLevel_holds k hα hα1 hlam hr0 hr1 hV hKV
    (hA.mono inter_subset_left) hφ hGV hwV
    (fun x hx => hcap x (hK1 hx)) (fun x hx => hell x (hK1 hx)) hface he'
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
    have hc1 : ContinuousOn w'' (ball 0 ρ) := hw''c.continuousOn
    have hc2 : ContinuousOn w' U' := hw'.contDiffOn.continuousOn
    have heq : EqOn w'' w' (boundaryHalfBall (ρ / 2)) := fun y hy => hw''w' (hTS hy)
    have heq' := heq.of_subset_closure (hc1.mono hT) (hc2.mono (hTr.trans hKU')) subset_closure
      subset_rfl
    rw [heq' hx]
    exact hface x (hTr hx) hx0

/-- Blueprint `thm:boundary-C2a` (flat Dirichlet, all higher orders): a `C^{1,α}` solution of
`div(A ∇u) = div G` in the half ball of radius `R ≤ 1`, with smooth coefficient `A`, smooth
datum `G` and smooth boundary datum `φ` (`u = φ` on the flat face), agrees, for every `k`, on
a small half ball with a function which is `C^k` on the full ball of that radius. -/
theorem boundary_c2a_smooth_all_orders
    {α lam cap R : ℝ} (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hR : 0 < R) (hR1 : R ≤ 1)
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U)
    (hUc : closure (boundaryHalfBall R) ⊆ U)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {u φ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) A U) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G U)
    (hu : HasCkHolderOn 1 α u U (closure (boundaryHalfBall R)))
    (hcap : ∀ x ∈ closure (boundaryHalfBall R), ‖A x‖ ≤ cap)
    (hell : ∀ x ∈ closure (boundaryHalfBall R), ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    (hface : ∀ x ∈ closure (boundaryHalfBall R), x (Fin.last 2) = 0 → u x = φ x)
    (he : IsWeakDivergenceEquationOn A (gradient u) G (boundaryHalfBall R)) :
    ∀ k : ℕ, ∃ ρ > 0, ∃ v : EuclideanSpace ℝ (Fin 3) → ℝ,
      EqOn v u (boundaryHalfBall ρ) ∧ ContDiffOn ℝ k v (ball 0 ρ) := by
  have hinv : ∀ k, boundaryC2aSmoothChain_Inv α R u φ k := by
    intro k
    induction k with
    | zero => exact ⟨R, hR, le_rfl, U, hU, hUc, u, fun _ _ => rfl, hu, hface⟩
    | succ k ih =>
      exact boundaryC2aSmoothChain_step k hα hα1 hlam hR1 hU hUc hA hφ hG hcap hell he ih
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
