import NoCompromise.Elliptic.HolderInterpolationGeometry
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Explicit uniform and Hölder norms

The real Hölder norm is the uniform norm plus the supremum of the usual difference
quotients. The diagonal quotient is zero. Finiteness is stated explicitly, so no
estimate relies on a conditional supremum of an unbounded set.
-/

noncomputable section
open MeasureTheory Filter Metric Set
open scoped ENNReal Topology

namespace LiquidDrop

/-- The uniform norm on a set, with zero inserted to include the empty-set convention. -/
def holderUniformNorm {E F : Type*} [NormedAddCommGroup F] (f : E → F) (U : Set E) : ℝ :=
  sSup (insert 0 ((fun x => ‖f x‖) '' U))

/-- The standard Hölder seminorm, with diagonal difference quotients interpreted as zero. -/
def holderSeminorm {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (α : ℝ) (f : E → F) (U : Set E) : ℝ :=
  sSup (insert 0 ((fun p : E × E => ‖f p.1 - f p.2‖ / ‖p.1 - p.2‖ ^ α) '' (U ×ˢ U)))

/-- The C^(0,α) norm is the sum of the uniform norm and the Hölder seminorm. -/
def holderNorm {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (α : ℝ) (f : E → F) (U : Set E) : ℝ := holderUniformNorm f U + holderSeminorm α f U

/-- Explicit finiteness of both suprema defining the Hölder norm. -/
structure HasFiniteHolderNormOn {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (α : ℝ) (f : E → F) (U : Set E) : Prop where
  uniform_bounded : BddAbove (insert 0 ((fun x => ‖f x‖) '' U))
  seminorm_bounded :
    BddAbove (insert 0
      ((fun p : E × E => ‖f p.1 - f p.2‖ / ‖p.1 - p.2‖ ^ α) '' (U ×ˢ U)))

lemma holderUniformNorm_nonneg {E F : Type*} [NormedAddCommGroup F]
    {f : E → F} {U : Set E} (hf : BddAbove (insert 0 ((fun x => ‖f x‖) '' U))) :
    0 ≤ holderUniformNorm f U := le_csSup hf (mem_insert _ _)

lemma norm_le_holderUniformNorm {E F : Type*} [NormedAddCommGroup F]
    {f : E → F} {U : Set E} (hf : BddAbove (insert 0 ((fun x => ‖f x‖) '' U)))
    {x : E} (hx : x ∈ U) : ‖f x‖ ≤ holderUniformNorm f U :=
  le_csSup hf (mem_insert_of_mem _ (mem_image_of_mem _ hx))

lemma holderUniformNorm_le {E F : Type*} [NormedAddCommGroup F]
    {f : E → F} {U : Set E} {C : ℝ} (hC : 0 ≤ C) (hf : ∀ x ∈ U, ‖f x‖ ≤ C) :
    holderUniformNorm f U ≤ C := by
  apply csSup_le (insert_nonempty _ _)
  rintro a (rfl | ⟨x, hx, rfl⟩)
  · exact hC
  · exact hf x hx

lemma HasFiniteHolderNormOn.seminorm_nonneg {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {α : ℝ} {f : E → F} {U : Set E} (hf : HasFiniteHolderNormOn α f U) :
    0 ≤ holderSeminorm α f U := le_csSup hf.seminorm_bounded (mem_insert _ _)

lemma HasFiniteHolderNormOn.uniformNorm_le {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {α : ℝ} {f : E → F} {U : Set E} (hf : HasFiniteHolderNormOn α f U) :
    holderUniformNorm f U ≤ holderNorm α f U := le_add_of_nonneg_right hf.seminorm_nonneg

lemma HasFiniteHolderNormOn.norm_nonneg {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {α : ℝ} {f : E → F} {U : Set E} (hf : HasFiniteHolderNormOn α f U) :
    0 ≤ holderNorm α f U := add_nonneg
      (holderUniformNorm_nonneg hf.uniform_bounded) hf.seminorm_nonneg

lemma holderSeminorm_le {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {α : ℝ} {f : E → F} {U : Set E} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ x ∈ U, ∀ y ∈ U, ‖f x - f y‖ / ‖x - y‖ ^ α ≤ C) :
    holderSeminorm α f U ≤ C := by
  apply csSup_le (insert_nonempty _ _)
  rintro a (rfl | ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩)
  · exact hC
  · exact hf x hx y hy

/-- A continuous function on an open Euclidean set obeys its essential uniform bound pointwise. -/
lemma holderInterpolation_norm_le_lpNorm_top {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    {f : EuclideanSpace ℝ (Fin n) → F} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hm : MemLp f ∞ (volume.restrict U)) :
    ∀ x ∈ U, ‖f x‖ ≤ lpNorm f ∞ (volume.restrict U) := by
  let L := lpNorm f ∞ (volume.restrict U)
  have heq : (fun x => max (‖f x‖ - L) 0) =ᵐ[volume.restrict U] fun _ => (0 : ℝ) := by
    filter_upwards [ae_le_lpNorm_exponent_top hm] with x hx
    exact max_eq_right (sub_nonpos.mpr hx)
  have hc : ContinuousOn (fun x => max (‖f x‖ - L) 0) U :=
    (hf.norm.sub continuousOn_const).sup continuousOn_const
  have hp := Measure.eqOn_open_of_ae_eq heq hU hc continuousOn_const
  intro x hx
  have hb := le_max_left (‖f x‖ - L) 0
  have hp' : max (‖f x‖ - L) 0 = 0 := hp hx
  rw [hp'] at hb
  linarith

/-- Explicit uniform and quotient bounds imply finiteness of the Hölder norm. -/
theorem HasFiniteHolderNormOn.of_bounds {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {α A B : ℝ} {f : E → F} {U : Set E} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ x ∈ U, ‖f x‖ ≤ A)
    (hh : ∀ x ∈ U, ∀ y ∈ U, ‖f x - f y‖ / ‖x - y‖ ^ α ≤ B) :
    HasFiniteHolderNormOn α f U := by
  refine ⟨⟨A, ?_⟩, ⟨B, ?_⟩⟩
  · rintro a (rfl | ⟨x, hx, rfl⟩)
    · exact hA
    · exact hf x hx
  · rintro a (rfl | ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩)
    · exact hB
    · exact hh x hx y hy

lemma holderNorm_le {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {α A B : ℝ} {f : E → F} {U : Set E} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ x ∈ U, ‖f x‖ ≤ A)
    (hh : ∀ x ∈ U, ∀ y ∈ U, ‖f x - f y‖ / ‖x - y‖ ^ α ≤ B) :
    holderNorm α f U ≤ A + B :=
  add_le_add (holderUniformNorm_le hA hf) (holderSeminorm_le hB hh)

end LiquidDrop
