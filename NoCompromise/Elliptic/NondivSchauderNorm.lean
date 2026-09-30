module

public import NoCompromise.Elliptic.NewtonianSchauder

@[expose] public section

/-!
# Hölder data for the nondivergence Schauder estimate

C¹,α means actual C¹ regularity and finite Hölder norms of the function and
its actual Fréchet derivative. The norm is their sum. These definitions apply
to scalar functions, vector fields, and operator-valued coefficient fields.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Genuine C¹,α membership, with explicit finiteness of both Hölder norms. -/
structure HasC1HolderOn {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (α : ℝ) (u : E → F) (U : Set E) : Prop where
  contDiff : ContDiffOn ℝ 1 u U
  function_holder : HasFiniteHolderNormOn α u U
  derivative_holder : HasFiniteHolderNormOn α (fderiv ℝ u) U

/-- The C¹,α norm convention is the sum of the two C⁰,α norms. -/
def nondivC1HolderNorm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (α : ℝ) (u : E → F) (U : Set E) : ℝ :=
  holderNorm α u U + holderNorm α (fderiv ℝ u) U

lemma HasC1HolderOn.norm_nonneg {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : ℝ} {u : E → F} {U : Set E} (hu : HasC1HolderOn α u U) :
    0 ≤ nondivC1HolderNorm α u U :=
  add_nonneg hu.function_holder.norm_nonneg hu.derivative_holder.norm_nonneg

lemma HasC1HolderOn.function_norm_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : ℝ} {u : E → F} {U : Set E} (hu : HasC1HolderOn α u U) :
    holderNorm α u U ≤ nondivC1HolderNorm α u U :=
  le_add_of_nonneg_right hu.derivative_holder.norm_nonneg

lemma HasC1HolderOn.derivative_norm_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : ℝ} {u : E → F} {U : Set E} (hu : HasC1HolderOn α u U) :
    holderNorm α (fderiv ℝ u) U ≤ nondivC1HolderNorm α u U :=
  le_add_of_nonneg_left hu.function_holder.norm_nonneg

lemma HasFiniteHolderNormOn.nondiv_norm_le {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {α : ℝ} {f : E → F} {U : Set E} (hf : HasFiniteHolderNormOn α f U)
    {x : E} (hx : x ∈ U) : ‖f x‖ ≤ holderNorm α f U :=
  (norm_le_holderUniformNorm hf.uniform_bounded hx).trans hf.uniformNorm_le

lemma HasFiniteHolderNormOn.nondiv_norm_sub_le {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {α : ℝ} {f : E → F} {U : Set E} (hf : HasFiniteHolderNormOn α f U)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) :
    ‖f x - f y‖ ≤ holderSeminorm α f U * ‖x - y‖ ^ α := by
  by_cases he : x = y
  · subst y
    simp only [sub_self, norm_zero]
    exact mul_nonneg hf.seminorm_nonneg (Real.rpow_nonneg (le_refl 0) α)
  · exact (div_le_iff₀ (Real.rpow_pos_of_pos
      (norm_pos_iff.mpr (sub_ne_zero.mpr he)) α)).mp (schauder_holder_quotient_le hf hx hy)

/-- Bounded linear maps act on the actual Hölder norm with their operator norm. -/
lemma nondiv_holder_comp_clm {E F G : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {α : ℝ} {f : E → F} {U : Set E} (hf : HasFiniteHolderNormOn α f U) (L : F →L[ℝ] G) :
    HasFiniteHolderNormOn α (fun x => L (f x)) U ∧
      holderNorm α (fun x => L (f x)) U ≤ ‖L‖ * holderNorm α f U := by
  have hA := mul_nonneg (norm_nonneg L) (holderUniformNorm_nonneg hf.uniform_bounded)
  have hB := mul_nonneg (norm_nonneg L) hf.seminorm_nonneg
  have hv : ∀ x ∈ U, ‖L (f x)‖ ≤ ‖L‖ * holderUniformNorm f U :=
    fun x hx => (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (norm_le_holderUniformNorm hf.uniform_bounded hx) (norm_nonneg L))
  have hh : ∀ x ∈ U, ∀ y ∈ U, ‖L (f x) - L (f y)‖ / ‖x - y‖ ^ α ≤
      ‖L‖ * holderSeminorm α f U := by
    intro x hx y hy
    rw [← map_sub]
    calc
      _ ≤ (‖L‖ * ‖f x - f y‖) / ‖x - y‖ ^ α :=
        div_le_div_of_nonneg_right (L.le_opNorm _) (by positivity)
      _ = ‖L‖ * (‖f x - f y‖ / ‖x - y‖ ^ α) := mul_div_assoc _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (schauder_holder_quotient_le hf hx hy) (norm_nonneg L)
  refine ⟨HasFiniteHolderNormOn.of_bounds hA hB hv hh,
    (holderNorm_le hA hB hv hh).trans_eq ?_⟩
  simp only [holderNorm, mul_add]

/-- Continuous bilinear maps preserve C⁰,α, with an explicit uniform norm bound. -/
lemma nondiv_holder_bilinear {E F G H : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {α : ℝ} {f : E → F} {g : E → G} {U : Set E}
    (hf : HasFiniteHolderNormOn α f U) (hg : HasFiniteHolderNormOn α g U)
    (B : F →L[ℝ] G →L[ℝ] H) :
    HasFiniteHolderNormOn α (fun x => B (f x) (g x)) U ∧
      holderNorm α (fun x => B (f x) (g x)) U ≤
        3 * ‖B‖ * holderNorm α f U * holderNorm α g U := by
  have hF := hf.norm_nonneg
  have hG := hg.norm_nonneg
  let A := ‖B‖ * holderNorm α f U * holderNorm α g U
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (norm_nonneg B) hf.norm_nonneg) hg.norm_nonneg
  have hb (v : F) (w : G) : ‖B v w‖ ≤ ‖B‖ * ‖v‖ * ‖w‖ :=
    ((B v).le_opNorm w).trans (mul_le_mul_of_nonneg_right (B.le_opNorm v) (norm_nonneg w))
  have hv : ∀ x ∈ U, ‖B (f x) (g x)‖ ≤ A := by
    intro x hx
    exact (hb _ _).trans (mul_le_mul
      (mul_le_mul_of_nonneg_left (hf.nondiv_norm_le hx) (norm_nonneg B))
      (hg.nondiv_norm_le hx) (norm_nonneg _) (by positivity))
  have hh : ∀ x ∈ U, ∀ y ∈ U,
      ‖B (f x) (g x) - B (f y) (g y)‖ / ‖x - y‖ ^ α ≤ 2 * A := by
    intro x hx y hy
    have he : B (f x) (g x) - B (f y) (g y) =
        B (f x - f y) (g x) + B (f y) (g x - g y) := by
      simp only [map_sub, sub_apply]
      abel
    rw [he]
    have hp : 0 ≤ ‖x - y‖ ^ α := by positivity
    have hs (f : E → F) (hf : HasFiniteHolderNormOn α f U) :
        ‖f x - f y‖ / ‖x - y‖ ^ α ≤ holderNorm α f U :=
      (schauder_holder_quotient_le hf hx hy).trans (le_add_of_nonneg_left
        (holderUniformNorm_nonneg hf.uniform_bounded))
    have hs' : ‖g x - g y‖ / ‖x - y‖ ^ α ≤ holderNorm α g U :=
      (schauder_holder_quotient_le hg hx hy).trans (le_add_of_nonneg_left
        (holderUniformNorm_nonneg hg.uniform_bounded))
    calc
      _ ≤ (‖B‖ * ‖f x - f y‖ * ‖g x‖ + ‖B‖ * ‖f y‖ * ‖g x - g y‖) /
          ‖x - y‖ ^ α := div_le_div_of_nonneg_right
        ((norm_add_le _ _).trans (add_le_add (hb _ _) (hb _ _))) hp
      _ = ‖B‖ * (‖f x - f y‖ / ‖x - y‖ ^ α) * ‖g x‖ +
          ‖B‖ * ‖f y‖ * (‖g x - g y‖ / ‖x - y‖ ^ α) := by ring
      _ ≤ A + A := add_le_add
        (mul_le_mul (mul_le_mul_of_nonneg_left (hs f hf) (norm_nonneg B))
          (hg.nondiv_norm_le hx) (norm_nonneg _) (by positivity))
        (mul_le_mul (mul_le_mul_of_nonneg_left (hf.nondiv_norm_le hy) (norm_nonneg B))
          hs' (by positivity) (by positivity))
      _ = 2 * A := by ring
  refine ⟨HasFiniteHolderNormOn.of_bounds hA (by positivity) hv hh,
    (holderNorm_le hA (by positivity) hv hh).trans_eq ?_⟩
  dsimp [A]
  ring


lemma HasC1HolderOn.mono {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : ℝ} {u : E → F} {U V : Set E} (hu : HasC1HolderOn α u U) (hVU : V ⊆ U) :
    HasC1HolderOn α u V ∧ nondivC1HolderNorm α u V ≤ nondivC1HolderNorm α u U := by
  obtain ⟨hf, hfb⟩ := schauder_holder_mono hu.function_holder hVU
  obtain ⟨hd, hdb⟩ := schauder_holder_mono hu.derivative_holder hVU
  exact ⟨⟨hu.contDiff.mono hVU, hf, hd⟩, add_le_add hfb hdb⟩

lemma HasC1HolderOn.memLp_top {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : ℝ} {u : EuclideanSpace ℝ (Fin n) → F} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hu : HasC1HolderOn α u U) (hU : IsOpen U) : MemLp u ∞ (volume.restrict U) := by
  apply memLp_top_of_bound (hu.contDiff.continuousOn.aestronglyMeasurable hU.measurableSet)
    (holderUniformNorm u U)
  filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
  exact norm_le_holderUniformNorm hu.function_holder.uniform_bounded hx

/-- The ordinary Euclidean gradient has the same Hölder bound as the Fréchet derivative. -/
lemma HasC1HolderOn.gradient_holder {n : ℕ} {α : ℝ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hu : HasC1HolderOn α u U) :
    HasFiniteHolderNormOn α (gradient u) U ∧
      holderNorm α (gradient u) U ≤ holderNorm α (fderiv ℝ u) U := by
  let L := (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    change ‖(toDual ℝ (EuclideanSpace ℝ (Fin n))).symm v‖ ≤ 1 * ‖v‖
    rw [LinearIsometryEquiv.norm_map, one_mul]
  obtain ⟨hf, hb⟩ := nondiv_holder_comp_clm hu.derivative_holder L
  exact ⟨hf, hb.trans ((mul_le_mul_of_nonneg_right hL
    hu.derivative_holder.norm_nonneg).trans_eq (one_mul _))⟩

/-- No weak-gradient hypothesis is added: C¹,α data on a bounded open set are H¹
with their actual ordinary gradient. -/
lemma HasC1HolderOn.hasH1GradientOn {n : ℕ} {α : ℝ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hu : HasC1HolderOn α u U) (hU : IsOpen U) (hbU : Bornology.IsBounded U) :
    HasH1GradientOn u (gradient u) U := by
  let : IsFiniteMeasure (volume.restrict U) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hbU.measure_lt_top⟩
  have hg : MemLp (gradient u) ∞ (volume.restrict U) := by
    apply memLp_top_of_bound
      ((continuousOn_gradient_of_contDiffOn hU hu.contDiff).aestronglyMeasurable hU.measurableSet)
      (holderNorm α (gradient u) U)
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact hu.gradient_holder.1.nondiv_norm_le hx
  exact ⟨hasWeakGradientOn_of_contDiffOn hU hu.contDiff,
    (hu.memLp_top hU).mono_exponent le_top, hg.mono_exponent le_top⟩

end LiquidDrop
