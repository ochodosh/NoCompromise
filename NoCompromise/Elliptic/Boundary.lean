import NoCompromise.Elliptic.BoundaryHolderSharp
import NoCompromise.Elliptic.BoundaryC1

/-!
# Boundary regularity (blueprint `thm:boundary-C1a` and its successors)

This module collects the boundary regularity endpoints of chapter 10.

* `boundary_holder_mean_oscillation_of_holder` (in `BoundaryHolderSharp`) is the
  displayed Campanato decay `⨍_{B_ρ⁺} |∇w − (∇w)_{B_ρ⁺}|² ≤ C ρ^{2α}` for weak
  `H¹` solutions of `div(A∇w) = div G` on the half ball with Hölder coefficients,
  Hölder datum, uniform positive ellipticity, and zero trace on the flat face.
* `boundary_c1_holder` (in `BoundaryC1`) is the `C^{1,α}` conclusion up to
  `Γ_{1/2}`: an actual `C¹` representative on an open set containing the closed
  flat face of radius `1/2`, with globally Hölder gradient and zero boundary
  values, constants fixed before the solution and data.
* `boundary_C1a` (below) states both halves at once with a single constant.

Both halves take exactly the blueprint's hypotheses, packaged as
`BoundaryHolderUnitData a lam cap HA HG M u F G A`: uniformly elliptic
`A ∈ C^{0,α}(closure B_1^+)`, datum `G ∈ C^{0,α}(closure B_1^+)`, a genuine `H¹`
solution `u` with gradient `F` of the weak equation `div (A ∇u) = div G` on
`B_1^+`, zero flat trace on `Γ_1`, and energy bound `M`. The constants are chosen
before the coefficient fields and the solution, and depend only on `α`, the
ellipticity constants `lam`, `cap`, the Hölder seminorms `HA`, `HG`, and `M`.

`thm:boundary-C2a`, `thm:boundary-nondiv`, and `thm:boundary-neumann` remain to be
added here.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- `thm:boundary-C1a` (boundary `C^{1,α}`, Dirichlet), both halves at once and
with a single constant. Under the blueprint's closed-half-ball hypotheses, the
gradient mean oscillation on every centred half-ball of radius `r ≤ 1` is at most
`C r^{2α}`, and the solution has a `C¹` representative on an open neighbourhood
`W` of the closed flat half-disk `{‖x‖ ≤ 1/2, x₃ = 0}` inside `B_{3/4}` whose
gradient is bounded by `P`, is `α`-Hölder with constant `C`, and which vanishes
on the flat face. -/
theorem boundary_C1a {a lam cap HA HG M : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hlam : 0 < lam) (hcap : 0 ≤ cap)
    (hHA : 0 ≤ HA) (hHG : 0 ≤ HG) (hM : 0 ≤ M) :
    ∃ C P : ℝ, 0 < C ∧ 0 ≤ P ∧
      ∀ (u : EuclideanSpace ℝ (Fin 3) → ℝ)
        (F G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
        (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
          EuclideanSpace ℝ (Fin 3)),
        BoundaryHolderUnitData a lam cap HA HG M u F G A →
        (∀ r ∈ Ioc (0 : ℝ) 1,
            (⨍ x in boundaryHalfBall r, ‖F x - ⨍ y in boundaryHalfBall r, F y‖ ^ 2) ≤
              C * r ^ (2 * a)) ∧
        ∃ (W : Set (EuclideanSpace ℝ (Fin 3))) (v : EuclideanSpace ℝ (Fin 3) → ℝ),
          IsOpen W ∧ {x | ‖x‖ ≤ (1 / 2 : ℝ) ∧ x (Fin.last 2) = 0} ⊆ W ∧
          W ⊆ ball 0 (3 / 4 : ℝ) ∧ ContDiffOn ℝ 1 v W ∧
          v =ᵐ[volume.restrict (W ∩ {x | 0 < x (Fin.last 2)})] u ∧
          gradient v =ᵐ[volume.restrict (W ∩ {x | 0 < x (Fin.last 2)})] F ∧
          (∀ x ∈ W, ‖gradient v x‖ ≤ P) ∧
          (∀ x ∈ W, ∀ y ∈ W, ‖gradient v x - gradient v y‖ ≤ C * dist x y ^ a) ∧
          ∀ x ∈ W, x (Fin.last 2) = 0 → v x = 0 := by
  obtain ⟨C₁, hC₁, hosc⟩ :=
    boundary_holder_mean_oscillation_of_holder ha ha1 hlam hcap hHA hHG hM
  obtain ⟨C₂, P, hC₂, hP, hrep⟩ := boundary_c1_holder ha ha1 hlam hcap hHA hHG hM
  refine ⟨max C₁ C₂, P, lt_of_lt_of_le hC₁ (le_max_left _ _), hP, ?_⟩
  intro u F G A h
  refine ⟨?_, ?_⟩
  · intro r hr
    refine (hosc u F G A h.coefficient_continuous h.datum_continuous h.coefficient_bound
      h.elliptic h.coefficient_holder h.datum_holder h.h1 h.trace_zero h.equation
      h.energy_bound r hr).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hr.1.le _)
  · obtain ⟨W, v, hW, hdisk, hball, hv, huv, hgrad, hbdd, hholder, hflat⟩ :=
      hrep u F G A h
    refine ⟨W, v, hW, hdisk, hball, hv, huv, hgrad, hbdd, ?_, hflat⟩
    intro x hx y hy
    exact (hholder x hx y hy).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg dist_nonneg a))

end LiquidDrop
