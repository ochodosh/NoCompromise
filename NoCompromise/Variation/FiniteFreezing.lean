import NoCompromise.Sobolev.ExtensionPartition
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Finite freezing of a compactly supported field

A finite smooth partition localizes a compact carrier to neighborhoods where the
field differs little from a constant. Each constant is realized by a genuine
smooth compactly supported field, with all supports in one fixed open set.
The partition sum is at most one everywhere, so weighted estimates can be summed
without a factor depending on the number of pieces.
-/

noncomputable section
open Set Metric Filter
open scoped Topology Gradient NNReal
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Concrete finite localization data for freezing a field. The single global
bound controls the original field, all frozen vectors, and all cutoff fields. -/
structure FiniteFieldFreezing (X : AmbientSpace → AmbientSpace)
    (K A : Set AmbientSpace) (η : ℝ) (N : ℕ) where
  weight : Fin N → AmbientSpace → ℝ
  region : Fin N → Set AmbientSpace
  constantVector : Fin N → AmbientSpace
  frozenField : Fin N → AmbientSpace → AmbientSpace
  weightLip : Fin N → ℝ≥0
  fieldLip : Fin N → ℝ≥0
  gradientBound : Fin N → ℝ
  bound : ℝ
  open_ambient : IsOpen A
  bounded_ambient : Bornology.IsBounded A
  weight_contDiff : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (weight j)
  weight_compact : ∀ j, HasCompactSupport (weight j)
  weight_support : ∀ j, tsupport (weight j) ⊆ region j
  weight_nonneg : ∀ j x, 0 ≤ weight j x
  weight_le_one : ∀ j x, weight j x ≤ 1
  weight_lipschitz : ∀ j, LipschitzWith (weightLip j) (weight j)
  gradientBound_nonneg : ∀ j, 0 ≤ gradientBound j
  weight_gradient_bound : ∀ j x, ‖gradient (weight j) x‖ ≤ gradientBound j
  sum_eq_one : ∀ x ∈ K, ∑ j, weight j x = 1
  sum_le_one : ∀ x, ∑ j, weight j x ≤ 1
  open_region : ∀ j, IsOpen (region j)
  compact_closure_region : ∀ j, IsCompact (closure (region j))
  closure_region_subset : ∀ j, closure (region j) ⊆ A
  frozenField_contDiff : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (frozenField j)
  frozenField_compact : ∀ j, HasCompactSupport (frozenField j)
  frozenField_support : ∀ j, tsupport (frozenField j) ⊆ A
  frozenField_eq_constant : ∀ j, EqOn (frozenField j) (fun _ => constantVector j) (region j)
  field_lipschitz : ∀ j, LipschitzWith (fieldLip j) (frozenField j)
  original_lipschitz : ∀ j, LipschitzWith (fieldLip j) X
  oscillation_le : ∀ j x, x ∈ region j → ‖X x - constantVector j‖ ≤ η
  bound_nonneg : 0 ≤ bound
  original_bound : ∀ x, ‖X x‖ ≤ bound
  constant_bound : ∀ j, ‖constantVector j‖ ≤ bound
  frozenField_bound : ∀ j x, ‖frozenField j x‖ ≤ bound

/-- A compact carrier in a fixed bounded open set admits finite smooth freezing
for every strictly positive error tolerance. All auxiliary fields are genuine
smooth compact cutoffs of sampled values of the original field. -/
theorem exists_finiteFieldFreezing {X : AmbientSpace → AmbientSpace}
    {K A : Set AmbientSpace} (hK : IsCompact K) (hA : IsOpen A)
    (hbA : Bornology.IsBounded A) (hKA : K ⊆ A)
    (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X) {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, Nonempty (FiniteFieldFreezing X K A η N) := by
  classical
  have hloc (x : K) : ∃ V : Set AmbientSpace, IsOpen V ∧ (x : AmbientSpace) ∈ V ∧
      IsCompact (closure V) ∧ closure V ⊆ A ∧ ∀ y ∈ V, ‖X y - X x‖ ≤ η := by
    let U := A ∩ {y | ‖X y - X x‖ < η}
    have hU : IsOpen U := hA.inter
      (isOpen_lt (hX.continuous.sub continuous_const).norm continuous_const)
    have hxU : (x : AmbientSpace) ∈ U := ⟨hKA x.property, by simpa using hη⟩
    obtain ⟨V, hV, hxV, hVU, hcV⟩ := exists_open_between_and_isCompact_closure
      (isCompact_singleton (x := (x : AmbientSpace))) hU (singleton_subset_iff.mpr hxU)
    refine ⟨V, hV, hxV (mem_singleton _), hcV, hVU.trans inter_subset_left, ?_⟩
    intro y hy
    exact (hVU (subset_closure hy)).2.le
  choose V hV hxV hcV hVA hosc using hloc
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover V hV (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩)
  let N := Fintype.card ↥s
  let c (j : Fin N) : K := ((Fintype.equivFin ↥s).symm j).val
  let W (j : Fin N) := V (c j)
  have hcover : K ⊆ ⋃ j, W j := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hs hx)
    refine mem_iUnion.mpr ⟨(Fintype.equivFin ↥s) ⟨y, hy⟩, ?_⟩
    simpa only [W, c, Equiv.symm_apply_apply] using hxy
  obtain ⟨ζ, Γ, hζ, hζsum, hζsumle⟩ := exists_finite_smooth_partition_of_bounded_open_cover
    hK W (fun j => hV (c j))
    (fun j => (hcV (c j)).isBounded.subset subset_closure) hcover
  have hcut (j : Fin N) := exists_smooth_cutoff_one_near_compact (hcV (c j)) hA (hVA (c j))
  choose χ hχ hcχ hsχ hχone hχbounds using hcut
  let Y (j : Fin N) (x : AmbientSpace) := χ j x • X (c j)
  have hY (j : Fin N) : ContDiff ℝ (⊤ : ℕ∞) (Y j) := (hχ j).smul contDiff_const
  have hcY (j : Fin N) : HasCompactSupport (Y j) := (hcχ j).smul_right
  have hYs (j : Fin N) : tsupport (Y j) ⊆ A :=
    (tsupport_smul_subset_left (χ j) (fun _ => X (c j))).trans (hsχ j)
  have hYeq (j : Fin N) : EqOn (Y j) (fun _ => X (c j)) (W j) := by
    intro x hx
    have heq := (hχone j).self_of_nhdsSet x (subset_closure hx)
    simp only [Y, heq, one_smul]
  obtain ⟨LX, hLX⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcX hX one_ne_zero
  choose LY hLY using fun j =>
    ContDiff.lipschitzWith_of_hasCompactSupport (hcY j) ((hY j).of_le (by simp) :
      ContDiff ℝ 1 (Y j)) one_ne_zero
  choose Q hQ using fun j =>
    ContDiff.lipschitzWith_of_hasCompactSupport (hζ j).2.1 ((hζ j).1.of_le (by simp) :
      ContDiff ℝ 1 (ζ j)) one_ne_zero
  obtain ⟨B, hB⟩ := hcX.exists_bound_of_continuous hX.continuous
  let B' := max B 0
  have hXB (x : AmbientSpace) : ‖X x‖ ≤ B' := (hB x).trans (le_max_left _ _)
  have hYB (j : Fin N) (x : AmbientSpace) : ‖Y j x‖ ≤ B' := by
    change ‖χ j x • X (c j)‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hχbounds j x).1]
    exact ((mul_le_mul_of_nonneg_right (hχbounds j x).2 (norm_nonneg _)).trans_eq
      (one_mul _)).trans (hXB _)
  refine ⟨N, ⟨{
    weight := ζ
    region := W
    constantVector := fun j => X (c j)
    frozenField := Y
    weightLip := Q
    fieldLip := fun j => max LX (LY j)
    gradientBound := Γ
    bound := B'
    open_ambient := hA
    bounded_ambient := hbA
    weight_contDiff := fun j => (hζ j).1
    weight_compact := fun j => (hζ j).2.1
    weight_support := fun j => (hζ j).2.2.1
    weight_nonneg := fun j x => ((hζ j).2.2.2.1 x).1
    weight_le_one := fun j x => ((hζ j).2.2.2.1 x).2
    weight_lipschitz := hQ
    gradientBound_nonneg := fun j => (hζ j).2.2.2.2.1
    weight_gradient_bound := fun j => (hζ j).2.2.2.2.2
    sum_eq_one := hζsum
    sum_le_one := hζsumle
    open_region := fun j => hV (c j)
    compact_closure_region := fun j => hcV (c j)
    closure_region_subset := fun j => hVA (c j)
    frozenField_contDiff := hY
    frozenField_compact := hcY
    frozenField_support := hYs
    frozenField_eq_constant := hYeq
    field_lipschitz := fun j => (hLY j).weaken (le_max_right _ _)
    original_lipschitz := fun j => hLX.weaken (le_max_left _ _)
    oscillation_le := fun j => hosc (c j)
    bound_nonneg := le_max_right _ _
    original_bound := hXB
    constant_bound := fun j => hXB (c j)
    frozenField_bound := hYB
  }⟩⟩

/-- The approximation is by the actual cutoff field on each weight neighborhood. -/
lemma FiniteFieldFreezing.field_error_le {X : AmbientSpace → AmbientSpace}
    {K A : Set AmbientSpace} {η : ℝ} {N : ℕ} (d : FiniteFieldFreezing X K A η N)
    (j : Fin N) {x : AmbientSpace} (hx : x ∈ d.region j) :
    ‖X x - d.frozenField j x‖ ≤ η := by
  rw [d.frozenField_eq_constant j hx]
  exact d.oscillation_le j x hx

lemma FiniteFieldFreezing.bounded_region {X : AmbientSpace → AmbientSpace}
    {K A : Set AmbientSpace} {η : ℝ} {N : ℕ} (d : FiniteFieldFreezing X K A η N)
    (j : Fin N) : Bornology.IsBounded (d.region j) :=
  (d.compact_closure_region j).isBounded.subset subset_closure

end LiquidDrop
