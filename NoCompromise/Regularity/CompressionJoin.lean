module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Topology.Piecewise

@[expose] public section

/-! # Joining C¹ scalar profiles at a common first jet -/

noncomputable section
open Set Filter
open scoped Topology
namespace LiquidDrop

lemma hasDerivAt_join_le {f g : ℝ → ℝ} {a d : ℝ}
    (hf : HasDerivAt f d a) (hg : HasDerivAt g d a) (hv : f a = g a) :
    HasDerivAt (fun x => if x ≤ a then f x else g x) d a := by
  have hl : HasDerivWithinAt (fun x => if x ≤ a then f x else g x) d (Iic a) a := by
    apply hf.hasDerivWithinAt.congr
    · intro x hx
      simp only [mem_Iic] at hx
      exact ite_eq_left hx
    · exact ite_eq_left le_rfl
  have hr : HasDerivWithinAt (fun x => if x ≤ a then f x else g x) d (Ici a) a := by
    apply hg.hasDerivWithinAt.congr
    · intro x hx
      by_cases hxa : x ≤ a
      · have he : x = a := le_antisymm hxa hx
        subst x
        simpa using hv
      · exact ite_eq_right hxa
    · simpa using hv
  have hu := hl.hasFDerivWithinAt.union hr.hasFDerivWithinAt
  have hu' := (hasFDerivWithinAt_univ.mp (by simpa only [Iic_union_Ici] using hu)).hasDerivAt
  simpa using hu'

lemma hasDerivAt_join_le_everywhere {f g f' g' : ℝ → ℝ} {a : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hg : ∀ x, HasDerivAt g (g' x) x)
    (hv : f a = g a) (hd : f' a = g' a) (x : ℝ) :
    HasDerivAt (fun y => if y ≤ a then f y else g y)
      (if x ≤ a then f' x else g' x) x := by
  rcases lt_trichotomy x a with hx | rfl | hx
  · rw [ite_eq_left hx.le]
    exact (hf x).congr_of_eventuallyEq
      ((eventually_lt_nhds hx).mono (fun y hy => ite_eq_left hy.le))
  · simp only [le_refl, ite_true]
    exact hasDerivAt_join_le (hf x) (hd ▸ hg x) hv
  · rw [ite_eq_right hx.not_ge]
    exact (hg x).congr_of_eventuallyEq
      ((eventually_gt_nhds hx).mono (fun y hy => ite_eq_right hy.not_ge))

lemma contDiff_join_le {f g : ℝ → ℝ} {a : ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hv : f a = g a) (hd : deriv f a = deriv g a) :
    ContDiff ℝ 1 (fun x => if x ≤ a then f x else g x) := by
  have hder := hasDerivAt_join_le_everywhere
    (fun x => (hf.differentiable (by norm_num) x).hasDerivAt)
    (fun x => (hg.differentiable (by norm_num) x).hasDerivAt) hv hd
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (hder x).differentiableAt, ?_⟩
  have he : deriv (fun x => if x ≤ a then f x else g x) =
      fun x => if x ≤ a then deriv f x else deriv g x := funext (fun x => (hder x).deriv)
  rw [he]
  apply Continuous.if _ (hf.continuous_deriv le_rfl) (hg.continuous_deriv le_rfl)
  intro x hx
  have hx' : x = a := by simpa only [show {x : ℝ | x ≤ a} = Iic a from rfl,
    frontier_Iic, mem_singleton_iff] using hx
  simpa only [hx'] using hd

end LiquidDrop
