import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Analysis.LocallyConvex.Basic
import NoCompromise.Conventions

/-! # Unicoherence of simply connected spaces

A normal, simply connected, locally path-connected space `X` is unicoherent: if `X = A ∪ B` with
`A`, `B` closed and preconnected, then `A ∩ B` is preconnected.  The proof lifts a circle-valued
map through `Circle.exp`.  It is used for `lem:hull-properties` (`∂K` connected). -/

noncomputable section
open Set Real

namespace LiquidDrop

/-- A real function on a preconnected set whose values all lie in the kernel of `Circle.exp`
(the multiples of `2π`) is constant there. -/
theorem unicoherence_eq_of_circleExp_eq_one {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsPreconnected S) {h : X → ℝ} (hh : ContinuousOn h S)
    (h1 : ∀ x ∈ S, Circle.exp (h x) = 1) {x y : X} (hx : x ∈ S) (hy : y ∈ S) : h x = h y := by
  have key : ∀ a ∈ S, ∀ b ∈ S, ¬ h a < h b := by
    intro a ha b hb hab
    have hI : Icc (h a) (h b) ⊆ h '' S := (hS.image h hh).Icc_subset ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    have hd : Circle.exp (h b - h a) = 1 := by rw [Circle.exp_sub, h1 a ha, h1 b hb, div_one]
    obtain ⟨n, hn⟩ := Circle.exp_eq_one.mp hd
    have hn1 : (1 : ℝ) ≤ n := by
      have hpos : (0 : ℝ) < n * (2 * π) := by rw [← hn]; linarith
      have : (0 : ℝ) < n := pos_of_mul_pos_left hpos (by positivity)
      exact_mod_cast (Int.cast_pos.mp this : (0 : ℤ) < n)
    have hmem : h a + π ∈ Icc (h a) (h b) := by
      constructor
      · linarith [pi_pos]
      · nlinarith [pi_pos]
    obtain ⟨z, hz, hzv⟩ := hI hmem
    have : Circle.exp (h z) = Circle.exp π := by
      rw [hzv, Circle.exp_add, h1 a ha, one_mul]
    exact Circle.exp_pi_ne_one (this ▸ h1 z hz)
  rcases lt_trichotomy (h x) (h y) with hlt | heq | hgt
  · exact (key x hx y hy hlt).elim
  · exact heq
  · exact (key y hy x hx hgt).elim

/-- Unicoherence: in a normal, simply connected, locally path-connected space, if `X = A ∪ B` with
`A`, `B` closed and preconnected, then `A ∩ B` is preconnected. -/
theorem isPreconnected_inter_of_isClosed_of_union_eq_univ {X : Type*} [TopologicalSpace X]
    [NormalSpace X] [SimplyConnectedSpace X] [LocallyPathConnectedSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hAc : IsPreconnected A) (hBc : IsPreconnected B)
    (hAB : A ∪ B = univ) : IsPreconnected (A ∩ B) := by
  classical
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro u v hu hv hsub hdisj
  by_contra hne
  have hP : (A ∩ B ∩ u).Nonempty := by
    by_contra h0
    refine hne (Or.inr fun x hx => ?_)
    rcases hsub hx with h | h
    · exact (h0 ⟨x, hx, h⟩).elim
    · exact h
  have hQ : (A ∩ B ∩ v).Nonempty := by
    by_contra h0
    refine hne (Or.inl fun x hx => ?_)
    rcases hsub hx with h | h
    · exact h
    · exact (h0 ⟨x, hx, h⟩).elim
  have hPc : IsClosed (A ∩ B ∩ u) := (hA.inter hB).inter hu
  have hQc : IsClosed (A ∩ B ∩ v) := (hA.inter hB).inter hv
  have hPQ : Disjoint (A ∩ B ∩ u) (A ∩ B ∩ v) := by
    rw [Set.disjoint_left]
    intro x hxu hxv
    have : x ∈ A ∩ B ∩ (u ∩ v) := ⟨hxu.1, hxu.2, hxv.2⟩
    rw [hdisj] at this
    exact this
  obtain ⟨φ, hφ0, hφ1, -⟩ := exists_continuous_zero_one_of_isClosed hPc hQc hPQ
  have hφAB : ∀ x ∈ A ∩ B, φ x = 0 ∨ φ x = 1 := by
    intro x hx
    rcases hsub hx with h | h
    · exact Or.inl (hφ0 ⟨hx, h⟩)
    · exact Or.inr (hφ1 ⟨hx, h⟩)
  have hagree : ∀ x ∈ A ∩ B, Circle.exp (π * φ x) = Circle.exp (-(π * φ x)) := by
    intro x hx
    rcases hφAB x hx with h | h
    · simp [h]
    · rw [h, mul_one, Circle.exp_eq_exp]
      exact ⟨1, by ring⟩
  let f : X → Circle := fun x => if x ∈ A then Circle.exp (π * φ x) else Circle.exp (-(π * φ x))
  have hfc : Continuous f := by
    refine Continuous.if ?_ (Circle.exp.continuous.comp (continuous_const.mul φ.continuous))
      (Circle.exp.continuous.comp (continuous_const.mul φ.continuous).neg)
    intro x hx
    have hxA : x ∈ A := hA.frontier_subset hx
    have hxB : x ∈ B := by
      have : closure {x | x ∈ A}ᶜ ⊆ B :=
        closure_minimal (fun y hy => by
          have : y ∈ A ∪ B := hAB ▸ mem_univ y
          exact this.resolve_left hy) hB
      exact this (frontier_subset_closure (by rwa [frontier_compl]))
    exact hagree x ⟨hxA, hxB⟩
  obtain ⟨p, ⟨hpA, hpB⟩, hpu⟩ := hP
  obtain ⟨q, ⟨hqA, hqB⟩, hqv⟩ := hQ
  obtain ⟨F, ⟨-, hF⟩, -⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
    ⟨f, hfc⟩ p (π * φ p) (by simp [f, hpA])
  have hFx : ∀ x, Circle.exp (F x) = f x := fun x => congrFun hF x
  -- On `A`, `F - πφ` is constant; on `B`, `F + πφ` is constant.
  have hA1 : ∀ x ∈ A, Circle.exp (F x - π * φ x) = 1 := by
    intro x hx
    rw [Circle.exp_sub, hFx x]
    simp [f, hx]
  have hB1 : ∀ x ∈ B, Circle.exp (F x + π * φ x) = 1 := by
    intro x hx
    rw [Circle.exp_add, hFx x]
    by_cases hxA : x ∈ A
    · simp only [f, hxA, ite_true]
      conv_lhs => arg 1; rw [hagree x ⟨hxA, hx⟩]
      rw [Circle.exp_neg, inv_mul_cancel]
    · simp only [f, hxA, ite_false]
      rw [Circle.exp_neg, inv_mul_cancel]
  have hcA := unicoherence_eq_of_circleExp_eq_one (h := fun x => F x - π * φ x) hAc
    (by fun_prop) hA1 hpA hqA
  have hcB := unicoherence_eq_of_circleExp_eq_one (h := fun x => F x + π * φ x) hBc
    (by fun_prop) hB1 hpB hqB
  have hp0 : φ p = 0 := hφ0 ⟨⟨hpA, hpB⟩, hpu⟩
  have hq1 : φ q = 1 := hφ1 ⟨⟨hqA, hqB⟩, hqv⟩
  rw [hp0, hq1] at hcA hcB
  have : π = 0 := by linarith
  exact pi_ne_zero this

/-- `ℝ³` is unicoherent: if `ℝ³ = A ∪ B` with `A`, `B` closed and preconnected, then `A ∩ B` is
preconnected. -/
theorem ambient_isPreconnected_inter_of_isClosed {A B : Set AmbientSpace}
    (hA : IsClosed A) (hB : IsClosed B) (hAc : IsPreconnected A) (hBc : IsPreconnected B)
    (hAB : A ∪ B = univ) : IsPreconnected (A ∩ B) :=
  isPreconnected_inter_of_isClosed_of_union_eq_univ hA hB hAc hBc hAB

end LiquidDrop
