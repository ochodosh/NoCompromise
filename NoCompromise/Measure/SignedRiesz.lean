import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Tactic

/-!
# Signed Riesz representation from positive functionals

Blueprint `def:locally-bounded`, `def:upper-variation`,
`lem:upper-variation-additive`, `thm:signed-riesz`, and `lem:riesz-exhaustion`.
The underlying space may in particular be an open subset of Euclidean space.
Zero extension identifies the actual open-subtype test spaces with ambient
supported tests. Canonical positive/negative Riesz representation commutes with
restriction, and compatible local functionals glue along increasing open covers.
-/

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped CompactlySupported NNReal Topology

namespace LiquidDrop

variable {X : Type*} [TopologicalSpace X]

/-- Blueprint `def:locally-bounded`: a sup-norm bound on each fixed compact support. -/
def IsLocallyBoundedFunctional (Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ) : Prop :=
  ∀ K : Set X, IsCompact K → ∃ C : ℝ, 0 ≤ C ∧
    ∀ f : C_c(X, ℝ), tsupport f ⊆ K → |Λ f| ≤ C * ‖f.toBoundedContinuousFunction‖

/-- Blueprint `def:upper-variation`, used on nonnegative functions. -/
def upperVariation (Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ) (f : C_c(X, ℝ)) : ℝ :=
  sSup (Λ '' Icc 0 f)

lemma support_subset_of_nonneg_le {f g : C_c(X, ℝ)} (hg : 0 ≤ g) (hgf : g ≤ f) :
    tsupport g ⊆ tsupport f := by
  apply closure_mono
  intro x hx
  change g x ≠ 0 at hx
  change f x ≠ 0
  intro hfx
  have hle : g x ≤ 0 := by simpa [hfx] using hgf x
  exact hx (le_antisymm hle (hg x))

lemma norm_le_of_nonneg_le {f g : C_c(X, ℝ)} (hg : 0 ≤ g) (hgf : g ≤ f) :
    ‖g.toBoundedContinuousFunction‖ ≤ ‖f.toBoundedContinuousFunction‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
  intro x
  change ‖g x‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (hg x)]
  exact (hgf x).trans ((le_abs_self (f x)).trans
    (BoundedContinuousFunction.norm_coe_le_norm f.toBoundedContinuousFunction x))

lemma upperVariation_bddAbove (Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ)
    (hΛ : IsLocallyBoundedFunctional Λ) (f : C_c(X, ℝ)) :
    BddAbove (Λ '' Icc 0 f) := by
  obtain ⟨C, hC, hbound⟩ := hΛ (tsupport f) f.hasCompactSupport
  refine ⟨C * ‖f.toBoundedContinuousFunction‖, ?_⟩
  rintro _ ⟨g, hg, rfl⟩
  exact (le_abs_self _).trans ((hbound g (support_subset_of_nonneg_le hg.1 hg.2)).trans
    (mul_le_mul_of_nonneg_left (norm_le_of_nonneg_le hg.1 hg.2) hC))

lemma upperVariation_nonneg (Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ)
    (hΛ : IsLocallyBoundedFunctional Λ) {f : C_c(X, ℝ)} (hf : 0 ≤ f) :
    0 ≤ upperVariation Λ f := by
  apply le_csSup (upperVariation_bddAbove Λ hΛ f)
  exact ⟨0, ⟨le_rfl, hf⟩, map_zero Λ⟩

lemma le_upperVariation (Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ)
    (hΛ : IsLocallyBoundedFunctional Λ) {f g : C_c(X, ℝ)} (hg : 0 ≤ g) (hgf : g ≤ f) :
    Λ g ≤ upperVariation Λ f :=
  le_csSup (upperVariation_bddAbove Λ hΛ f) ⟨g, ⟨hg, hgf⟩, rfl⟩

lemma upperVariation_le (Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ)
    {f : C_c(X, ℝ)} (hf : 0 ≤ f) {a : ℝ}
    (ha : ∀ g : C_c(X, ℝ), 0 ≤ g → g ≤ f → Λ g ≤ a) :
    upperVariation Λ f ≤ a := by
  change sSup (Λ '' Icc 0 f) ≤ a
  refine csSup_le (s := Λ '' Icc 0 f) ?_ ?_
  · exact ⟨Λ 0, 0, ⟨le_rfl, hf⟩, rfl⟩
  · rintro _ ⟨g, hg, rfl⟩
    exact ha g hg.1 hg.2

/-- Additivity of upper variation on the nonnegative cone. -/
theorem upperVariation_add (Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ)
    (hΛ : IsLocallyBoundedFunctional Λ) {f g : C_c(X, ℝ)} (hf : 0 ≤ f) (hg : 0 ≤ g) :
    upperVariation Λ (f + g) = upperVariation Λ f + upperVariation Λ g := by
  apply le_antisymm
  · apply upperVariation_le Λ (add_nonneg hf hg)
    intro k hk hkfg
    have h₁ : 0 ≤ k ⊓ f := le_inf hk hf
    have h₂ : 0 ≤ k - k ⊓ f := sub_nonneg.mpr inf_le_left
    have h₃ : k - k ⊓ f ≤ g := by
      intro x
      have hx := hkfg x
      change k x - min (k x) (f x) ≤ g x
      change k x ≤ f x + g x at hx
      have hnonneg : 0 ≤ g x := hg x
      rcases le_total (k x) (f x) with h | h
      · simpa [min_eq_left h] using hnonneg
      · rw [min_eq_right h]
        linarith
    calc
      Λ k = Λ (k ⊓ f) + Λ (k - k ⊓ f) := by rw [map_sub]; ring
      _ ≤ _ := add_le_add (le_upperVariation Λ hΛ h₁ inf_le_right)
        (le_upperVariation Λ hΛ h₂ h₃)
  · apply (le_sub_iff_add_le).mp
    apply upperVariation_le Λ hf
    intro k hk hkf
    apply (le_sub_iff_add_le).mpr
    apply (le_sub_iff_add_le').mp
    apply upperVariation_le Λ hg
    intro l hl hlg
    apply (le_sub_iff_add_le').mpr
    rw [← map_add]
    exact le_upperVariation Λ hΛ (add_nonneg hk hl) (add_le_add hkf hlg)

@[simp] theorem upperVariation_zero (Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ) :
    upperVariation Λ 0 = 0 := by
  simp [upperVariation]

/-- Positive homogeneity of upper variation. -/
theorem upperVariation_smul (Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ)
    (hΛ : IsLocallyBoundedFunctional Λ) {f : C_c(X, ℝ)} (hf : 0 ≤ f)
    {r : ℝ} (hr : 0 ≤ r) : upperVariation Λ (r • f) = r * upperVariation Λ f := by
  rcases eq_or_lt_of_le hr with hzero | hpos
  · subst r
    simp
  apply le_antisymm
  · apply upperVariation_le Λ (fun x => mul_nonneg hr (hf x))
    intro g hg hgf
    have hle : r⁻¹ • g ≤ f := by
      intro x
      have := mul_le_mul_of_nonneg_left (hgf x) (inv_nonneg.mpr hr)
      change r⁻¹ * (g x) ≤ f x
      simpa [← mul_assoc, hpos.ne'] using this
    have hb := le_upperVariation Λ hΛ (fun x => mul_nonneg (inv_nonneg.mpr hr) (hg x)) hle
    rw [map_smul, smul_eq_mul] at hb
    have := mul_le_mul_of_nonneg_left hb hr
    simpa [← mul_assoc, hpos.ne'] using this
  · rw [mul_comm]
    apply (le_div_iff₀ hpos).mp
    apply upperVariation_le Λ hf
    intro g hg hgf
    apply (le_div_iff₀ hpos).mpr
    have hb := le_upperVariation Λ hΛ (f := r • f) (g := r • g) (fun x => mul_nonneg hr (hg x))
      (fun x => mul_le_mul_of_nonneg_left (hgf x) hr)
    simpa [map_smul, smul_eq_mul, mul_comm] using hb

open CompactlySupportedContinuousMap

/-- The upper variation as a linear map on the nonnegative cone. -/
def upperVariationNNReal (Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ)
    (hΛ : IsLocallyBoundedFunctional Λ) : C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0 where
  toFun f := ⟨upperVariation Λ f.toReal, upperVariation_nonneg Λ hΛ toReal_nonneg⟩
  map_add' f g := by
    apply NNReal.eq
    change upperVariation Λ (f + g).toReal =
      upperVariation Λ f.toReal + upperVariation Λ g.toReal
    rw [toReal_add, upperVariation_add Λ hΛ toReal_nonneg toReal_nonneg]
  map_smul' r f := by
    apply NNReal.eq
    change upperVariation Λ (r • f).toReal = (r : ℝ) * upperVariation Λ f.toReal
    rw [toReal_smul]
    exact upperVariation_smul Λ hΛ toReal_nonneg r.property

/-- Extend the upper variation from the nonnegative cone to a positive linear functional. -/
def positivePartFunctional (Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ)
    (hΛ : IsLocallyBoundedFunctional Λ) : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  toRealPositiveLinear (upperVariationNNReal Λ hΛ)

theorem positivePartFunctional_apply_of_nonneg (Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ)
    (hΛ : IsLocallyBoundedFunctional Λ) {f : C_c(X, ℝ)} (hf : 0 ≤ f) :
    positivePartFunctional Λ hΛ f = upperVariation Λ f := by
  have hreal : f.nnrealPart.toReal = f := by
    ext x
    simp [Real.toNNReal_of_nonneg (show 0 ≤ f x from hf x)]
  change upperVariation Λ f.nnrealPart.toReal -
    upperVariation Λ (-f).nnrealPart.toReal = upperVariation Λ f
  rw [hreal, nnrealPart_neg_eq_zero_of_nonneg hf]
  have hzero : (0 : C_c(X, ℝ≥0)).toReal = 0 := by ext; simp
  rw [hzero, upperVariation_zero, sub_zero]

/-- The negative part is positive because upper variation majorizes the functional. -/
def negativePartFunctional (Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ)
    (hΛ : IsLocallyBoundedFunctional Λ) : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀ ((positivePartFunctional Λ hΛ).toLinearMap - Λ) (by
    intro f hf
    change 0 ≤ positivePartFunctional Λ hΛ f - Λ f
    rw [positivePartFunctional_apply_of_nonneg Λ hΛ hf]
    exact sub_nonneg.mpr (le_upperVariation Λ hΛ hf le_rfl))

/-- Blueprint `thm:signed-riesz`, constructed using positive Riesz representation only. -/
theorem signed_riesz [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ) (hΛ : IsLocallyBoundedFunctional Λ) :
    ∃ μpos μneg : Measure X, μpos.Regular ∧ μneg.Regular ∧
      IsFiniteMeasureOnCompacts μpos ∧ IsFiniteMeasureOnCompacts μneg ∧
      ∀ f : C_c(X, ℝ), Λ f = (∫ x, f x ∂μpos) - ∫ x, f x ∂μneg := by
  refine ⟨RealRMK.rieszMeasure (positivePartFunctional Λ hΛ),
    RealRMK.rieszMeasure (negativePartFunctional Λ hΛ),
    inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  intro f
  rw [RealRMK.integral_rieszMeasure, RealRMK.integral_rieszMeasure]
  change Λ f = positivePartFunctional Λ hΛ f - (positivePartFunctional Λ hΛ f - Λ f)
  ring

/-- Upper variation depends only on the functional on the support of the test.
This is the locality needed for canonical positive parts on overlapping domains. -/
theorem upperVariation_congr_on_supported
    (Λ Λ' : C_c(X, ℝ) →ₗ[ℝ] ℝ) {U : Set X}
    (h : ∀ g : C_c(X, ℝ), tsupport g ⊆ U → Λ g = Λ' g)
    (f : C_c(X, ℝ)) (hf : tsupport f ⊆ U) :
    upperVariation Λ f = upperVariation Λ' f := by
  unfold upperVariation
  congr 1
  apply Set.image_congr
  intro g hg
  exact h g ((support_subset_of_nonneg_le hg.1 hg.2).trans hf)

theorem tsupport_nnrealPart_toReal_subset (f : C_c(X, ℝ)) :
    tsupport f.nnrealPart.toReal ⊆ tsupport f := by
  apply closure_mono
  intro x hx
  change f.nnrealPart.toReal x ≠ 0 at hx
  change f x ≠ 0
  intro hfx
  apply hx
  simp [hfx]

/-- Canonical positive parts agree on all tests supported in an overlap. -/
theorem positivePartFunctional_congr_on_supported
    (Λ Λ' : C_c(X, ℝ) →ₗ[ℝ] ℝ)
    (hΛ : IsLocallyBoundedFunctional Λ) (hΛ' : IsLocallyBoundedFunctional Λ')
    {U : Set X}
    (h : ∀ g : C_c(X, ℝ), tsupport g ⊆ U → Λ g = Λ' g)
    (f : C_c(X, ℝ)) (hf : tsupport f ⊆ U) :
    positivePartFunctional Λ hΛ f = positivePartFunctional Λ' hΛ' f := by
  change upperVariation Λ f.nnrealPart.toReal - upperVariation Λ (-f).nnrealPart.toReal =
    upperVariation Λ' f.nnrealPart.toReal - upperVariation Λ' (-f).nnrealPart.toReal
  have hn : tsupport (-f) ⊆ U := by simpa using hf
  rw [upperVariation_congr_on_supported Λ Λ' h _
    ((tsupport_nnrealPart_toReal_subset f).trans hf),
    upperVariation_congr_on_supported Λ Λ' h _
    ((tsupport_nnrealPart_toReal_subset (-f)).trans hn)]

/-- Canonical negative parts have the same overlap compatibility. -/
theorem negativePartFunctional_congr_on_supported
    (Λ Λ' : C_c(X, ℝ) →ₗ[ℝ] ℝ)
    (hΛ : IsLocallyBoundedFunctional Λ) (hΛ' : IsLocallyBoundedFunctional Λ')
    {U : Set X}
    (h : ∀ g : C_c(X, ℝ), tsupport g ⊆ U → Λ g = Λ' g)
    (f : C_c(X, ℝ)) (hf : tsupport f ⊆ U) :
    negativePartFunctional Λ hΛ f = negativePartFunctional Λ' hΛ' f := by
  change positivePartFunctional Λ hΛ f - Λ f = positivePartFunctional Λ' hΛ' f - Λ' f
  rw [positivePartFunctional_congr_on_supported Λ Λ' hΛ hΛ' h f hf, h f hf]

/-- Compactly supported continuous tests whose topological support is in `U`.
This ambient realization is useful for gluing functionals without choosing
extensions separately for every test. -/
def supportedTestFunctions (U : Set X) : Submodule ℝ C_c(X, ℝ) where
  carrier := {f | tsupport f ⊆ U}
  zero_mem' := by simp
  add_mem' hf hg := (tsupport_add _ _).trans (union_subset hf hg)
  smul_mem' c f hf := (tsupport_smul_subset_right (fun _ => c) f).trans hf

/-- Pointwise extension by zero from a subset. Continuity is proved below
for compactly supported functions on an open subset of a Hausdorff space. -/
def zeroExtendFunction {U : Set X} (f : U → ℝ) (x : X) : ℝ := by
  classical
  exact if hx : x ∈ U then f ⟨x, hx⟩ else 0

omit [TopologicalSpace X] in
@[simp] theorem zeroExtendFunction_apply_coe {U : Set X} (f : U → ℝ) (x : U) :
    zeroExtendFunction f x = f x := by simp [zeroExtendFunction]

omit [TopologicalSpace X] in
@[simp] theorem zeroExtendFunction_apply_notMem {U : Set X} (f : U → ℝ)
    {x : X} (hx : x ∉ U) : zeroExtendFunction f x = 0 := by simp [zeroExtendFunction, hx]

omit [TopologicalSpace X] in
theorem support_zeroExtendFunction {U : Set X} (f : U → ℝ) :
    Function.support (zeroExtendFunction f) = Subtype.val '' Function.support f := by
  ext x
  by_cases hx : x ∈ U
  · simp [Function.mem_support, zeroExtendFunction, hx]
  · simp [Function.mem_support, zeroExtendFunction, hx]

theorem tsupport_zeroExtendFunction [T2Space X] {U : Set X} (f : C_c(U, ℝ)) :
    tsupport (zeroExtendFunction f) = Subtype.val '' tsupport f := by
  apply le_antisymm
  · apply closure_minimal
    · rw [support_zeroExtendFunction]
      exact image_mono subset_closure
    · exact (f.hasCompactSupport.image continuous_subtype_val).isClosed
  · change Subtype.val '' closure (Function.support f) ⊆
      closure (Function.support (zeroExtendFunction f))
    rw [support_zeroExtendFunction]
    exact image_closure_subset_closure_image continuous_subtype_val

theorem continuous_zeroExtendFunction [T2Space X] {U : Set X} (hU : IsOpen U)
    (f : C_c(U, ℝ)) : Continuous (zeroExtendFunction f) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ U
  · apply (hU.isOpenEmbedding_subtypeVal.continuousAt_iff (x := ⟨x, hx⟩)).mp
    simpa only [Function.comp_def, zeroExtendFunction_apply_coe,
      CompactlySupportedContinuousMap.coe_toContinuousMap] using
      f.continuous.continuousAt (x := ⟨x, hx⟩)
  · have hzero : ContinuousAt (fun _ : X => (0 : ℝ)) x := continuousAt_const
    apply hzero.congr_of_eventuallyEq
    have hnot : x ∉ tsupport (zeroExtendFunction f) := by
      rw [tsupport_zeroExtendFunction]
      rintro ⟨y, _, rfl⟩
      exact hx y.property
    filter_upwards [(isClosed_tsupport (zeroExtendFunction f)).isOpen_compl.mem_nhds hnot] with y hy
    exact image_eq_zero_of_notMem_tsupport hy

/-- Extension by zero as a linear map into ambient compactly supported tests. -/
def zeroExtendCC [T2Space X] {U : Set X} (hU : IsOpen U) :
    C_c(U, ℝ) →ₗ[ℝ] C_c(X, ℝ) where
  toFun f :=
    { toFun := zeroExtendFunction f
      continuous_toFun := continuous_zeroExtendFunction hU f
      hasCompactSupport' := by
        rw [HasCompactSupport, tsupport_zeroExtendFunction]
        exact f.hasCompactSupport.image continuous_subtype_val }
  map_add' f g := by
    ext x
    by_cases hx : x ∈ U <;> simp [zeroExtendFunction, hx]
  map_smul' c f := by
    ext x
    by_cases hx : x ∈ U <;> simp [zeroExtendFunction, hx]

@[simp] theorem zeroExtendCC_apply_coe [T2Space X] {U : Set X} (hU : IsOpen U)
    (f : C_c(U, ℝ)) (x : U) : zeroExtendCC hU f x = f x := by
  exact zeroExtendFunction_apply_coe f x

theorem tsupport_zeroExtendCC [T2Space X] {U : Set X} (hU : IsOpen U)
    (f : C_c(U, ℝ)) : tsupport (zeroExtendCC hU f) = Subtype.val '' tsupport f :=
  tsupport_zeroExtendFunction f

theorem tsupport_zeroExtendCC_subset [T2Space X] {U : Set X} (hU : IsOpen U)
    (f : C_c(U, ℝ)) : tsupport (zeroExtendCC hU f) ⊆ U := by
  rw [tsupport_zeroExtendCC]
  rintro _ ⟨x, _, rfl⟩
  exact x.property

/-- Restriction of an ambient test whose support is contained in a subset. -/
def restrictSupportedCC {U : Set X} (f : supportedTestFunctions U) : C_c(U, ℝ) where
  toFun x := f.val x
  continuous_toFun := f.val.continuous.comp continuous_subtype_val
  hasCompactSupport' := by
    have hc : IsCompact (Subtype.val ⁻¹' tsupport f.val : Set U) :=
      Topology.IsInducing.subtypeVal.isCompact_preimage' f.val.hasCompactSupport
        (by simpa only [Subtype.range_coe] using
          (show tsupport f.val ⊆ U from f.property))
    apply hc.of_isClosed_subset (isClosed_tsupport _)
    exact continuous_subtype_val.closure_preimage_subset (Function.support f.val)

@[simp] theorem restrictSupportedCC_apply {U : Set X} (f : supportedTestFunctions U)
    (x : U) : restrictSupportedCC f x = f.val x := rfl

/-- The open-subtype and ambient supported-test realizations of `C_c(U)` agree. -/
def zeroExtendSupportedEquiv [T2Space X] {U : Set X} (hU : IsOpen U) :
    C_c(U, ℝ) ≃ₗ[ℝ] supportedTestFunctions U where
  toFun f := ⟨zeroExtendCC hU f, tsupport_zeroExtendCC_subset hU f⟩
  invFun := restrictSupportedCC
  left_inv f := by ext x; exact zeroExtendCC_apply_coe hU f x
  right_inv f := by
    apply Subtype.ext
    ext x
    by_cases hx : x ∈ U
    · exact zeroExtendCC_apply_coe hU (restrictSupportedCC f) ⟨x, hx⟩
    · change zeroExtendFunction (restrictSupportedCC f) x = f.val x
      rw [zeroExtendFunction_apply_notMem _ hx]
      exact (image_eq_zero_of_notMem_tsupport (fun h => hx (f.property h))).symm
  map_add' f g := Subtype.ext ((zeroExtendCC hU).map_add f g)
  map_smul' c f := Subtype.ext ((zeroExtendCC hU).map_smul c f)

@[simp] theorem zeroExtendCC_restrictSupportedCC [T2Space X] {U : Set X} (hU : IsOpen U)
    (f : supportedTestFunctions U) : zeroExtendCC hU (restrictSupportedCC f) = f.val :=
  congrArg Subtype.val ((zeroExtendSupportedEquiv hU).apply_symm_apply f)

@[simp] theorem restrictSupportedCC_zeroExtendCC [T2Space X] {U : Set X} (hU : IsOpen U)
    (f : C_c(U, ℝ)) :
    restrictSupportedCC ⟨zeroExtendCC hU f, tsupport_zeroExtendCC_subset hU f⟩ = f :=
  (zeroExtendSupportedEquiv hU).symm_apply_apply f

/-- Zero extension preserves the uniform norm exactly. -/
theorem norm_zeroExtendCC [T2Space X] {U : Set X} (hU : IsOpen U) (f : C_c(U, ℝ)) :
    ‖(zeroExtendCC hU f).toBoundedContinuousFunction‖ = ‖f.toBoundedContinuousFunction‖ := by
  apply le_antisymm
  · apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
    intro x
    change ‖zeroExtendFunction f x‖ ≤ _
    by_cases hx : x ∈ U
    · rw [zeroExtendFunction_apply_coe f ⟨x, hx⟩]
      exact f.toBoundedContinuousFunction.norm_coe_le_norm ⟨x, hx⟩
    · simp [zeroExtendFunction_apply_notMem _ hx]
  · apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
    intro x
    have h := (zeroExtendCC hU f).toBoundedContinuousFunction.norm_coe_le_norm x
    simpa only [CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply,
      zeroExtendCC_apply_coe] using h

theorem norm_restrictSupportedCC [T2Space X] {U : Set X} (hU : IsOpen U)
    (f : supportedTestFunctions U) :
    ‖(restrictSupportedCC f).toBoundedContinuousFunction‖ =
      ‖f.val.toBoundedContinuousFunction‖ := by
  rw [← norm_zeroExtendCC hU, zeroExtendCC_restrictSupportedCC]

theorem tsupport_restrictSupportedCC_subset {U : Set X} (f : supportedTestFunctions U) :
    tsupport (restrictSupportedCC f) ⊆ Subtype.val ⁻¹' tsupport f.val :=
  continuous_subtype_val.closure_preimage_subset (Function.support f.val)

theorem zeroExtendCC_le_iff [T2Space X] {U : Set X} (hU : IsOpen U)
    (f g : C_c(U, ℝ)) : zeroExtendCC hU f ≤ zeroExtendCC hU g ↔ f ≤ g := by
  constructor
  · intro h x
    simpa only [zeroExtendCC_apply_coe] using h x
  · intro h x
    change zeroExtendFunction f x ≤ zeroExtendFunction g x
    by_cases hx : x ∈ U
    · exact (zeroExtendFunction_apply_coe f ⟨x, hx⟩).trans_le
        ((h ⟨x, hx⟩).trans_eq (zeroExtendFunction_apply_coe g ⟨x, hx⟩).symm)
    · simp [zeroExtendFunction_apply_notMem _ hx]

/-- Restrict a functional to an open subset by extending its tests by zero. -/
def restrictFunctionalToOpen [T2Space X] {U : Set X} (hU : IsOpen U)
    (Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ) : C_c(U, ℝ) →ₗ[ℝ] ℝ := Λ.comp (zeroExtendCC hU)

theorem locallyBounded_restrictFunctionalToOpen [T2Space X] {U : Set X} (hU : IsOpen U)
    (Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ) (hΛ : IsLocallyBoundedFunctional Λ) :
    IsLocallyBoundedFunctional (restrictFunctionalToOpen hU Λ) := by
  intro K hK
  obtain ⟨C, hC, hb⟩ := hΛ (Subtype.val '' K) (hK.image continuous_subtype_val)
  refine ⟨C, hC, fun f hf => ?_⟩
  have hs : tsupport (zeroExtendCC hU f) ⊆ Subtype.val '' K := by
    rw [tsupport_zeroExtendCC]
    exact image_mono hf
  change |Λ (zeroExtendCC hU f)| ≤ _
  simpa only [norm_zeroExtendCC] using hb (zeroExtendCC hU f) hs

/-- Pulling back the measure to the open subtype agrees with zero extension
of the integrand. -/
theorem integral_zeroExtendCC [T2Space X] [MeasurableSpace X] [BorelSpace X]
    {U : Set X} (hU : IsOpen U) (μ : Measure X) (f : C_c(U, ℝ)) :
    (∫ x, zeroExtendCC hU f x ∂μ) = ∫ x, f x ∂μ.comap (Subtype.val : U → X) := by
  have heq : (∫ x in U, zeroExtendCC hU f x ∂μ) = ∫ x, zeroExtendCC hU f x ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
      zeroExtendFunction_apply_notMem f hx
  rw [← heq, ← integral_subtype_comap hU.measurableSet]
  simp only [zeroExtendCC_apply_coe]

/-- The upper-variation construction commutes with restriction to open subsets. -/
theorem upperVariation_restrictFunctionalToOpen [T2Space X] {U : Set X} (hU : IsOpen U)
    (Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ) (f : C_c(U, ℝ)) :
    upperVariation (restrictFunctionalToOpen hU Λ) f = upperVariation Λ (zeroExtendCC hU f) := by
  unfold upperVariation
  congr 1
  ext r
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨zeroExtendCC hU g, ⟨?_, (zeroExtendCC_le_iff hU g f).mpr hg.2⟩, rfl⟩
    simpa only [map_zero] using (zeroExtendCC_le_iff hU 0 g).mpr hg.1
  · rintro ⟨g, hg, rfl⟩
    have hs : tsupport g ⊆ U := (support_subset_of_nonneg_le hg.1 hg.2).trans
      (tsupport_zeroExtendCC_subset hU f)
    let g' := restrictSupportedCC ⟨g, hs⟩
    refine ⟨g', ⟨?_, ?_⟩, ?_⟩
    · intro x
      exact hg.1 x
    · intro x
      change g x ≤ f x
      simpa only [zeroExtendCC_apply_coe] using hg.2 x
    · change Λ (zeroExtendCC hU (restrictSupportedCC ⟨g, hs⟩)) = Λ g
      rw [zeroExtendCC_restrictSupportedCC]

theorem zeroExtendCC_nnrealPart_toReal [T2Space X] {U : Set X} (hU : IsOpen U)
    (f : C_c(U, ℝ)) :
    zeroExtendCC hU f.nnrealPart.toReal = (zeroExtendCC hU f).nnrealPart.toReal := by
  ext x
  simp only [toReal_apply, nnrealPart_apply]
  change zeroExtendFunction f.nnrealPart.toReal x = (Real.toNNReal (zeroExtendFunction f x) : ℝ)
  by_cases hx : x ∈ U <;> simp [zeroExtendFunction, hx]

/-- Canonical positive parts commute with restriction to the open-subtype test space. -/
theorem positivePartFunctional_restrictFunctionalToOpen
    [T2Space X] {U : Set X} (hU : IsOpen U)
    (Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ) (hΛ : IsLocallyBoundedFunctional Λ) (f : C_c(U, ℝ)) :
    positivePartFunctional (restrictFunctionalToOpen hU Λ)
      (locallyBounded_restrictFunctionalToOpen hU Λ hΛ) f =
      positivePartFunctional Λ hΛ (zeroExtendCC hU f) := by
  change upperVariation (restrictFunctionalToOpen hU Λ) f.nnrealPart.toReal -
      upperVariation (restrictFunctionalToOpen hU Λ) (-f).nnrealPart.toReal =
    upperVariation Λ (zeroExtendCC hU f).nnrealPart.toReal -
      upperVariation Λ (-(zeroExtendCC hU f)).nnrealPart.toReal
  rw [upperVariation_restrictFunctionalToOpen, upperVariation_restrictFunctionalToOpen,
    zeroExtendCC_nnrealPart_toReal, zeroExtendCC_nnrealPart_toReal, map_neg]

theorem negativePartFunctional_restrictFunctionalToOpen
    [T2Space X] {U : Set X} (hU : IsOpen U)
    (Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ) (hΛ : IsLocallyBoundedFunctional Λ) (f : C_c(U, ℝ)) :
    negativePartFunctional (restrictFunctionalToOpen hU Λ)
      (locallyBounded_restrictFunctionalToOpen hU Λ hΛ) f =
      negativePartFunctional Λ hΛ (zeroExtendCC hU f) := by
  change positivePartFunctional (restrictFunctionalToOpen hU Λ)
      (locallyBounded_restrictFunctionalToOpen hU Λ hΛ) f - Λ (zeroExtendCC hU f) =
    positivePartFunctional Λ hΛ (zeroExtendCC hU f) - Λ (zeroExtendCC hU f)
  rw [positivePartFunctional_restrictFunctionalToOpen]

/-- Positive Riesz representation commutes with restriction to an open subtype. -/
theorem positivePart_rieszMeasure_comap
    [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    {U : Set X} (hU : IsOpen U) [LocallyCompactSpace U]
    (Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ) (hΛ : IsLocallyBoundedFunctional Λ) :
    RealRMK.rieszMeasure (positivePartFunctional (restrictFunctionalToOpen hU Λ)
      (locallyBounded_restrictFunctionalToOpen hU Λ hΛ)) =
      (RealRMK.rieszMeasure (positivePartFunctional Λ hΛ)).comap (Subtype.val : U → X) := by
  let μ := RealRMK.rieszMeasure (positivePartFunctional Λ hΛ)
  let : (μ.comap (Subtype.val : U → X)).Regular :=
    Measure.Regular.comap' μ hU.isOpenEmbedding_subtypeVal
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  rw [RealRMK.integral_rieszMeasure, ← integral_zeroExtendCC hU _ f,
    RealRMK.integral_rieszMeasure]
  exact positivePartFunctional_restrictFunctionalToOpen hU Λ hΛ f

/-- Negative Riesz representation commutes with the same restriction. -/
theorem negativePart_rieszMeasure_comap
    [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    {U : Set X} (hU : IsOpen U) [LocallyCompactSpace U]
    (Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ) (hΛ : IsLocallyBoundedFunctional Λ) :
    RealRMK.rieszMeasure (negativePartFunctional (restrictFunctionalToOpen hU Λ)
      (locallyBounded_restrictFunctionalToOpen hU Λ hΛ)) =
      (RealRMK.rieszMeasure (negativePartFunctional Λ hΛ)).comap (Subtype.val : U → X) := by
  let μ := RealRMK.rieszMeasure (negativePartFunctional Λ hΛ)
  let : (μ.comap (Subtype.val : U → X)).Regular :=
    Measure.Regular.comap' μ hU.isOpenEmbedding_subtypeVal
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  rw [RealRMK.integral_rieszMeasure, ← integral_zeroExtendCC hU _ f,
    RealRMK.integral_rieszMeasure]
  exact negativePartFunctional_restrictFunctionalToOpen hU Λ hΛ f

/-- If a local functional is the restriction of a global one, both canonical
Riesz measures are the corresponding restrictions of the global measures. -/
theorem canonicalRiesz_comap_of_agree
    [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    {U : Set X} (hU : IsOpen U) [LocallyCompactSpace U]
    (Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ) (hΛ : IsLocallyBoundedFunctional Λ)
    (L : C_c(U, ℝ) →ₗ[ℝ] ℝ) (hL : IsLocallyBoundedFunctional L)
    (h : ∀ f, L f = Λ (zeroExtendCC hU f)) :
    RealRMK.rieszMeasure (positivePartFunctional L hL) =
        (RealRMK.rieszMeasure (positivePartFunctional Λ hΛ)).comap (Subtype.val : U → X) ∧
    RealRMK.rieszMeasure (negativePartFunctional L hL) =
        (RealRMK.rieszMeasure (negativePartFunctional Λ hΛ)).comap (Subtype.val : U → X) := by
  have heq : L = restrictFunctionalToOpen hU Λ := LinearMap.ext h
  subst L
  exact ⟨positivePart_rieszMeasure_comap hU Λ hΛ, negativePart_rieszMeasure_comap hU Λ hΛ⟩

/-- Compatible functionals on an exhaustion glue to one locally bounded
functional. Compact containment and all compatibility/boundedness assumptions
are explicit. -/
theorem exists_glued_supportedFunctionals
    (U : ℕ → Set X) (hU : Monotone U)
    (hcover : ∀ K : Set X, IsCompact K → ∃ m, K ⊆ U m)
    (L : ∀ m, supportedTestFunctions (U m) →ₗ[ℝ] ℝ)
    (hcompat : ∀ m n (hmn : m ≤ n) (f : C_c(X, ℝ)) (hf : tsupport f ⊆ U m),
      L m ⟨f, hf⟩ = L n ⟨f, hf.trans (hU hmn)⟩)
    (hbound : ∀ m (K : Set X), IsCompact K → ∀ hKU : K ⊆ U m,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : C_c(X, ℝ)) (hf : tsupport f ⊆ K),
        |L m ⟨f, hf.trans hKU⟩| ≤ C * ‖f.toBoundedContinuousFunction‖) :
    ∃ Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ, IsLocallyBoundedFunctional Λ ∧
      ∀ m (f : C_c(X, ℝ)) (hf : tsupport f ⊆ U m), Λ f = L m ⟨f, hf⟩ := by
  choose stage hstage using fun f : C_c(X, ℝ) => hcover (tsupport f) f.hasCompactSupport
  let a (f : C_c(X, ℝ)) : ℝ := L (stage f) ⟨f, hstage f⟩
  have ha (m : ℕ) (f : C_c(X, ℝ)) (hf : tsupport f ⊆ U m) :
      a f = L m ⟨f, hf⟩ := by
    exact (hcompat (stage f) (max (stage f) m) (le_max_left _ _) f (hstage f)).trans
      (hcompat m (max (stage f) m) (le_max_right _ _) f hf).symm
  let Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ :=
    { toFun := a
      map_add' := by
        intro f g
        let m := max (stage f) (stage g)
        have hf : tsupport f ⊆ U m := (hstage f).trans (hU (le_max_left _ _))
        have hg : tsupport g ⊆ U m := (hstage g).trans (hU (le_max_right _ _))
        have hfg : tsupport (f + g) ⊆ U m := (tsupport_add _ _).trans (union_subset hf hg)
        rw [ha m (f + g) hfg, ha m f hf, ha m g hg]
        exact (L m).map_add ⟨f, hf⟩ ⟨g, hg⟩
      map_smul' := by
        intro c f
        have hf : tsupport (c • f) ⊆ U (stage f) :=
          (tsupport_smul_subset_right (fun _ => c) f).trans (hstage f)
        rw [ha (stage f) (c • f) hf, ha (stage f) f (hstage f)]
        exact (L (stage f)).map_smul c ⟨f, hstage f⟩ }
  refine ⟨Λ, ?_, ha⟩
  intro K hK
  obtain ⟨m, hm⟩ := hcover K hK
  obtain ⟨C, hC, hb⟩ := hbound m K hK hm
  refine ⟨C, hC, fun f hf => ?_⟩
  change |a f| ≤ _
  rw [ha m f (hf.trans hm)]
  exact hb f hf

/-- Glue functionals defined on the actual open-subtype spaces `C_c(U_m)`.
Compatibility is tested by restricting the same ambient supported test. -/
theorem exists_glued_openFunctionals [T2Space X]
    (U : ℕ → Set X) (hU : Monotone U) (hopen : ∀ m, IsOpen (U m))
    (hcover : ∀ K : Set X, IsCompact K → ∃ m, K ⊆ U m)
    (L : ∀ m, C_c(U m, ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀ m, IsLocallyBoundedFunctional (L m))
    (hcompat : ∀ m n (hmn : m ≤ n) (f : C_c(X, ℝ)) (hf : tsupport f ⊆ U m),
      L m (restrictSupportedCC ⟨f, hf⟩) =
        L n (restrictSupportedCC ⟨f, hf.trans (hU hmn)⟩)) :
    ∃ Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ, IsLocallyBoundedFunctional Λ ∧
      ∀ m (f : C_c(U m, ℝ)), Λ (zeroExtendCC (hopen m) f) = L m f := by
  let L' (m : ℕ) := (L m).comp (zeroExtendSupportedEquiv (hopen m)).symm.toLinearMap
  have hbound (m : ℕ) (K : Set X) (hK : IsCompact K) (hKU : K ⊆ U m) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : C_c(X, ℝ)) (hf : tsupport f ⊆ K),
        |L' m ⟨f, hf.trans hKU⟩| ≤ C * ‖f.toBoundedContinuousFunction‖ := by
    have hK' : IsCompact (Subtype.val ⁻¹' K : Set (U m)) :=
      Topology.IsInducing.subtypeVal.isCompact_preimage' hK (by simpa using hKU)
    obtain ⟨C, hC, hb⟩ := hL m _ hK'
    refine ⟨C, hC, fun f hf => ?_⟩
    have hs := (tsupport_restrictSupportedCC_subset ⟨f, hf.trans hKU⟩).trans (preimage_mono hf)
    have h := hb (restrictSupportedCC ⟨f, hf.trans hKU⟩) hs
    rw [norm_restrictSupportedCC (hopen m)] at h
    exact h
  obtain ⟨Λ, hΛ, hglue⟩ := exists_glued_supportedFunctionals U hU hcover L' hcompat hbound
  refine ⟨Λ, hΛ, fun m f => ?_⟩
  have h := hglue m (zeroExtendCC (hopen m) f) (tsupport_zeroExtendCC_subset (hopen m) f)
  change Λ (zeroExtendCC (hopen m) f) =
    L m (restrictSupportedCC ⟨zeroExtendCC (hopen m) f, _⟩) at h
  simpa only [restrictSupportedCC_zeroExtendCC] using h

/-- An increasing open cover contains each compact set in one member. -/
theorem exists_supportedStage_of_isCompact
    (U : ℕ → Set X) (hU : Monotone U) (hopen : ∀ m, IsOpen (U m))
    (hcover : (⋃ m, U m) = univ) {K : Set X} (hK : IsCompact K) :
    ∃ m, K ⊆ U m := by
  apply hK.elim_directed_cover U hopen
  · simp [hcover]
  · intro m n
    exact ⟨max m n, hU (le_max_left _ _), hU (le_max_right _ _)⟩

/-- Blueprint `lem:riesz-exhaustion`: local signed Riesz constructions on an
increasing open cover are restrictions of one global pair. Local functionals
are defined on the open subtypes themselves. -/
theorem signed_riesz_exhaustion
    [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (U : ℕ → Set X) (hU : Monotone U) (hopen : ∀ m, IsOpen (U m))
    (hcover : (⋃ m, U m) = univ)
    (L : ∀ m, C_c(U m, ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀ m, IsLocallyBoundedFunctional (L m))
    (hcompat : ∀ m n (hmn : m ≤ n) (f : C_c(X, ℝ)) (hf : tsupport f ⊆ U m),
      L m (restrictSupportedCC ⟨f, hf⟩) =
        L n (restrictSupportedCC ⟨f, hf.trans (hU hmn)⟩)) :
    ∃ μpos μneg : Measure X, μpos.Regular ∧ μneg.Regular ∧
      IsFiniteMeasureOnCompacts μpos ∧ IsFiniteMeasureOnCompacts μneg ∧
      (∀ m (f : C_c(U m, ℝ)), L m f =
        (∫ x, f x ∂μpos.comap (Subtype.val : U m → X)) -
          ∫ x, f x ∂μneg.comap (Subtype.val : U m → X)) ∧
      ∀ m, letI := (hopen m).locallyCompactSpace
        RealRMK.rieszMeasure (positivePartFunctional (L m) (hL m)) =
            μpos.comap (Subtype.val : U m → X) ∧
        RealRMK.rieszMeasure (negativePartFunctional (L m) (hL m)) =
            μneg.comap (Subtype.val : U m → X) := by
  have hcompact := fun K hK => exists_supportedStage_of_isCompact U hU hopen hcover (K := K) hK
  obtain ⟨Λ, hΛ, hglue⟩ := exists_glued_openFunctionals U hU hopen hcompact L hL hcompat
  let μpos := RealRMK.rieszMeasure (positivePartFunctional Λ hΛ)
  let μneg := RealRMK.rieszMeasure (negativePartFunctional Λ hΛ)
  refine ⟨μpos, μneg, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · intro m f
    rw [← integral_zeroExtendCC (hopen m) μpos f, ← integral_zeroExtendCC (hopen m) μneg f]
    change L m f = (∫ x, zeroExtendCC (hopen m) f x ∂RealRMK.rieszMeasure
      (positivePartFunctional Λ hΛ)) - ∫ x, zeroExtendCC (hopen m) f x ∂RealRMK.rieszMeasure
      (negativePartFunctional Λ hΛ)
    rw [RealRMK.integral_rieszMeasure, RealRMK.integral_rieszMeasure]
    change L m f = positivePartFunctional Λ hΛ (zeroExtendCC (hopen m) f) -
      (positivePartFunctional Λ hΛ (zeroExtendCC (hopen m) f) - Λ (zeroExtendCC (hopen m) f))
    rw [hglue m f]
    ring
  · intro m
    let := (hopen m).locallyCompactSpace
    exact canonicalRiesz_comap_of_agree (hopen m) Λ hΛ (L m) (hL m) (fun f => (hglue m f).symm)

/-- One pair of locally finite regular measures represents all the compatible
functionals on an exhaustion, in the ambient supported-test realization. -/
theorem signed_riesz_of_supported_exhaustion
    [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (U : ℕ → Set X) (hU : Monotone U)
    (hcover : ∀ K : Set X, IsCompact K → ∃ m, K ⊆ U m)
    (L : ∀ m, supportedTestFunctions (U m) →ₗ[ℝ] ℝ)
    (hcompat : ∀ m n (hmn : m ≤ n) (f : C_c(X, ℝ)) (hf : tsupport f ⊆ U m),
      L m ⟨f, hf⟩ = L n ⟨f, hf.trans (hU hmn)⟩)
    (hbound : ∀ m (K : Set X), IsCompact K → ∀ hKU : K ⊆ U m,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : C_c(X, ℝ)) (hf : tsupport f ⊆ K),
        |L m ⟨f, hf.trans hKU⟩| ≤ C * ‖f.toBoundedContinuousFunction‖) :
    ∃ μpos μneg : Measure X, μpos.Regular ∧ μneg.Regular ∧
      IsFiniteMeasureOnCompacts μpos ∧ IsFiniteMeasureOnCompacts μneg ∧
      ∀ m (f : C_c(X, ℝ)) (hf : tsupport f ⊆ U m),
        L m ⟨f, hf⟩ = (∫ x, f x ∂μpos) - ∫ x, f x ∂μneg := by
  obtain ⟨Λ, hΛ, hglue⟩ := exists_glued_supportedFunctionals U hU hcover L hcompat hbound
  obtain ⟨μpos, μneg, hp, hn, hfp, hfn, hrep⟩ := signed_riesz Λ hΛ
  exact ⟨μpos, μneg, hp, hn, hfp, hfn, fun m f hf => (hglue m f hf).symm.trans (hrep f)⟩

/-- Localized uniqueness ingredient for positive Riesz representation. -/
theorem measure_le_of_isCompact_of_integral_on_supported
    [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ ν : Measure X} [ν.OuterRegular]
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    {U : Set X} (hU : IsOpen U)
    (hμν : ∀ f : C_c(X, ℝ), tsupport f ⊆ U → ∫ x, f x ∂μ ≤ ∫ x, f x ∂ν)
    {K : Set X} (hK : IsCompact K) (hKU : K ⊆ U) : μ K ≤ ν K := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hνK : ν K ≠ ⊤ := hK.measure_ne_top
  have hμK : μ K ≠ ⊤ := hK.measure_ne_top
  obtain ⟨V, hKV, hV, hb⟩ := exists_isOpen_le_add K ν
    (ne_of_gt (ENNReal.coe_lt_coe.mpr hε))
  have hKVU : K ⊆ V ∩ U := subset_inter hKV hKU
  have hVU : IsOpen (V ∩ U) := hV.inter hU
  have hbVU : ν (V ∩ U) ≤ ν K + ε := (measure_mono inter_subset_left).trans hb
  have hfin : ν (V ∩ U) < ⊤ := hbVU.trans_lt (by finiteness)
  suffices μ.real K ≤ ν.real K + ε by
    rwa [← ENNReal.toReal_le_toReal, ENNReal.toReal_add, ENNReal.coe_toReal]
    all_goals finiteness
  obtain ⟨f, heq, hc, hs, h01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK hVU hKVU
  let g : C_c(X, ℝ) := ⟨f, hc⟩
  have hgV (x : X) : g x ≤ (V ∩ U).indicator 1 x := by
    by_cases hx : x ∈ tsupport g
    · rw [Set.indicator_of_mem (hs hx)]
      exact (h01 x).2
    · simp [image_eq_zero_of_notMem_tsupport hx, Set.indicator_nonneg]
  have hgK (x : X) : K.indicator 1 x ≤ g x := by
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx]
      change 1 ≤ f x
      rw [heq hx]
      rfl
    · rw [Set.indicator_of_notMem hx]
      exact (h01 x).1
  calc
    μ.real K = ∫ x, K.indicator 1 x ∂μ := (integral_indicator_one hK.measurableSet).symm
    _ ≤ ∫ x, g x ∂μ := integral_mono
      ((continuousOn_const.integrableOn_compact hK).integrable_indicator hK.measurableSet)
      g.integrable hgK
    _ ≤ ∫ x, g x ∂ν := hμν g (hs.trans inter_subset_right)
    _ ≤ ∫ x, (V ∩ U).indicator 1 x ∂ν := integral_mono g.integrable
      (IntegrableOn.integrable_indicator integrableOn_const hVU.measurableSet) hgV
    _ ≤ ν.real K + ↑ε := by
      rw [integral_indicator_one hVU.measurableSet]
      have h := ENNReal.toReal_mono (by finiteness : ν K + ↑ε ≠ ⊤) hbVU
      simpa only [measureReal_def, ENNReal.toReal_add hνK ENNReal.coe_ne_top,
        ENNReal.coe_toReal] using h

/-- Regular measures that agree on all tests supported in an open set have
equal restrictions to that set. -/
theorem measure_restrict_eq_of_integral_on_supported
    [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] {μ ν : Measure X} [μ.Regular] [ν.Regular]
    {U : Set X} (hU : IsOpen U)
    (hμν : ∀ f : C_c(X, ℝ), tsupport f ⊆ U → ∫ x, f x ∂μ = ∫ x, f x ∂ν) :
    μ.restrict U = ν.restrict U := by
  apply Measure.ext
  intro A hA
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA,
    (hA.inter hU.measurableSet).measure_eq_iSup_isCompact μ,
    (hA.inter hU.measurableSet).measure_eq_iSup_isCompact ν]
  apply iSup_congr
  intro K
  apply iSup_congr
  intro hKA
  apply iSup_congr
  intro hK
  exact le_antisymm
    (measure_le_of_isCompact_of_integral_on_supported hU (fun f hf => (hμν f hf).le)
      hK (hKA.trans inter_subset_right))
    (measure_le_of_isCompact_of_integral_on_supported hU (fun f hf => (hμν f hf).ge)
      hK (hKA.trans inter_subset_right))

/-- Canonical positive Riesz measures agree on every open region where their
original signed functionals agree. -/
theorem positivePart_rieszMeasure_restrict_eq
    [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (Λ Λ' : C_c(X, ℝ) →ₗ[ℝ] ℝ)
    (hΛ : IsLocallyBoundedFunctional Λ) (hΛ' : IsLocallyBoundedFunctional Λ')
    {U : Set X} (hU : IsOpen U)
    (h : ∀ f : C_c(X, ℝ), tsupport f ⊆ U → Λ f = Λ' f) :
    (RealRMK.rieszMeasure (positivePartFunctional Λ hΛ)).restrict U =
      (RealRMK.rieszMeasure (positivePartFunctional Λ' hΛ')).restrict U := by
  apply measure_restrict_eq_of_integral_on_supported hU
  intro f hf
  simpa only [RealRMK.integral_rieszMeasure] using
    positivePartFunctional_congr_on_supported Λ Λ' hΛ hΛ' h f hf

/-- The same restriction compatibility for the canonical negative measures. -/
theorem negativePart_rieszMeasure_restrict_eq
    [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (Λ Λ' : C_c(X, ℝ) →ₗ[ℝ] ℝ)
    (hΛ : IsLocallyBoundedFunctional Λ) (hΛ' : IsLocallyBoundedFunctional Λ')
    {U : Set X} (hU : IsOpen U)
    (h : ∀ f : C_c(X, ℝ), tsupport f ⊆ U → Λ f = Λ' f) :
    (RealRMK.rieszMeasure (negativePartFunctional Λ hΛ)).restrict U =
      (RealRMK.rieszMeasure (negativePartFunctional Λ' hΛ')).restrict U := by
  apply measure_restrict_eq_of_integral_on_supported hU
  intro f hf
  simpa only [RealRMK.integral_rieszMeasure] using
    negativePartFunctional_congr_on_supported Λ Λ' hΛ hΛ' h f hf

end LiquidDrop
