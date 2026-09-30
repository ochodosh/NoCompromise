module

public import NoCompromise.Topology.TransversePreimage
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.InnerProductSpace.Calculus

@[expose] public section

/-!
# cor:transv-preimage, disk case (with boundary transversality)

A smooth map of the plane, transverse to a smooth embedded surface on the closed unit disk
and whose restriction to the boundary circle is also transverse, has as preimage of the
surface a topological one-manifold with boundary, whose manifold boundary is exactly its
intersection with the circle. Charts come from the inverse function theorem applied to
`(φ ∘ g, λ)`, where `φ` is a defining function of the surface and `λ` is a linear
coordinate (interior points) or `1 - ‖·‖²` (boundary points).

Without boundary transversality the disk statement is false (the preimage curve may be
tangent to the circle), so the hypothesis `BoundaryTransverseAt` is a proposed correction.
-/

noncomputable section
open Set Filter Function InnerProductSpace Module
open scoped Topology NNReal Gradient RealInnerProductSpace

namespace LiquidDrop

set_option maxSynthPendingDepth 8

/-- Transversality of the boundary restriction at a sphere point `p`: the sphere's tangent
space at `p` is `(ℝ ∙ p)ᗮ`. For `k = 1` this says `f p ∉ S`. -/
def BoundaryTransverseAt (S : Set E₃) {k : ℕ} (f : EuclideanSpace ℝ (Fin k) → E₃)
    (p : EuclideanSpace ℝ (Fin k)) : Prop :=
  f p ∈ S →
    Submodule.map (fderiv ℝ f p : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] E₃) (ℝ ∙ p)ᗮ ⊔
      tangentPlane S (f p) = ⊤

/-- A straightening chart `Λ` in which `C` is `{Λ₁ = 0, Λ₂ + c ≥ 0}` gives a half-line chart
of `C` with value `Λ₂ + c`. -/
theorem exists_halfLine_chart_of_straightening {P : Type*} [TopologicalSpace P] {C : Set P}
    (Λ : OpenPartialHomeomorph P (ℝ × ℝ)) (c : ℝ)
    (hC : ∀ x ∈ Λ.source, x ∈ C ↔ (Λ x).1 = 0 ∧ 0 ≤ (Λ x).2 + c)
    (x : C) (hx : (x : P) ∈ Λ.source) :
    ∃ e : OpenPartialHomeomorph C ℝ≥0, x ∈ e.source ∧ ((e x : ℝ≥0) : ℝ) = (Λ x).2 + c := by
  classical
  let inv : ℝ≥0 → C := fun t =>
    if h : Λ.symm (0, (t : ℝ) - c) ∈ C then ⟨_, h⟩ else x
  have hinvT : ∀ t : ℝ≥0, ((0 : ℝ), (t : ℝ) - c) ∈ Λ.target →
      Λ.symm (0, (t : ℝ) - c) ∈ C := by
    intro t ht
    refine (hC _ (Λ.map_target ht)).mpr ?_
    rw [Λ.right_inv ht]
    simp
  have hinv_val : ∀ t : ℝ≥0, ((0 : ℝ), (t : ℝ) - c) ∈ Λ.target →
      ((inv t : C) : P) = Λ.symm (0, (t : ℝ) - c) := by
    intro t ht
    simp only [inv, dite_eq_left (hinvT t ht)]
  have hnonneg : ∀ y : C, (y : P) ∈ Λ.source → 0 ≤ (Λ y).2 + c := fun y hy =>
    ((hC y hy).mp y.2).2
  have hΛy : ∀ y : C, (y : P) ∈ Λ.source →
      ((0 : ℝ), ((Real.toNNReal ((Λ y).2 + c) : ℝ≥0) : ℝ) - c) = Λ y := by
    intro y hy
    rw [Real.coe_toNNReal _ (hnonneg y hy), add_sub_cancel_right]
    exact Prod.ext ((hC y hy).mp y.2).1.symm rfl
  have hcont : ContinuousOn (fun y : C => Λ (y : P)) (((↑) : C → P) ⁻¹' Λ.source) :=
    Λ.continuousOn.comp continuous_subtype_val.continuousOn (fun y hy => hy)
  have hcontT : Continuous (fun t : ℝ≥0 => ((0 : ℝ), (t : ℝ) - c)) :=
    continuous_const.prodMk (continuous_subtype_val.sub continuous_const)
  let e : OpenPartialHomeomorph C ℝ≥0 :=
    { toFun := fun y => Real.toNNReal ((Λ y).2 + c)
      invFun := inv
      source := ((↑) : C → P) ⁻¹' Λ.source
      target := (fun t : ℝ≥0 => ((0 : ℝ), (t : ℝ) - c)) ⁻¹' Λ.target
      map_source' := by
        intro y hy
        change ((0 : ℝ), ((Real.toNNReal ((Λ y).2 + c) : ℝ≥0) : ℝ) - c) ∈ Λ.target
        rw [hΛy y hy]
        exact Λ.map_source hy
      map_target' := by
        intro t ht
        change ((inv t : C) : P) ∈ Λ.source
        rw [hinv_val t ht]
        exact Λ.map_target ht
      left_inv' := by
        intro y hy
        apply Subtype.ext
        have hT : ((0 : ℝ), ((Real.toNNReal ((Λ y).2 + c) : ℝ≥0) : ℝ) - c) ∈ Λ.target := by
          rw [hΛy y hy]
          exact Λ.map_source hy
        change ((inv (Real.toNNReal ((Λ y).2 + c)) : C) : P) = y
        rw [hinv_val _ hT, hΛy y hy, Λ.left_inv hy]
      right_inv' := by
        intro t ht
        rw [hinv_val t ht, Λ.right_inv ht]
        simp
      open_source := Λ.open_source.preimage continuous_subtype_val
      open_target := Λ.open_target.preimage hcontT
      continuousOn_toFun :=
        continuous_real_toNNReal.comp_continuousOn
          ((continuous_snd.comp_continuousOn hcont).add continuousOn_const)
      continuousOn_invFun := by
        rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
        refine ContinuousOn.congr (f := fun t : ℝ≥0 => Λ.symm (0, (t : ℝ) - c)) ?_ ?_
        · exact Λ.continuousOn_symm.comp hcontT.continuousOn (fun t ht => ht)
        · intro t ht
          exact hinv_val t ht }
  refine ⟨e, hx, ?_⟩
  change ((Real.toNNReal ((Λ x).2 + c) : ℝ≥0) : ℝ) = _
  exact Real.coe_toNNReal _ (hnonneg x hx)

/-- The inverse function theorem for a pair of planar scalar functions with independent
differentials. -/
theorem exists_straightening_chart {h l : EuclideanSpace ℝ (Fin 2) → ℝ}
    {p : EuclideanSpace ℝ (Fin 2)} {α β : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ}
    (hh : HasStrictFDerivAt h α p) (hl : HasStrictFDerivAt l β p)
    (hinj : ∀ u, α u = 0 → β u = 0 → u = 0) :
    ∃ Λ : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) (ℝ × ℝ),
      p ∈ Λ.source ∧ ⇑Λ = fun x => (h x, l x) := by
  let L : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ × ℝ := α.prod β
  have hF : HasStrictFDerivAt (fun x => (h x, l x)) L p := hh.prodMk hl
  have hLinj : Injective (L : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ × ℝ) := by
    refine (injective_iff_map_eq_zero _).mpr fun u hu => ?_
    have hu' : (α u, β u) = ((0 : ℝ), (0 : ℝ)) := hu
    exact hinj u (Prod.mk.inj hu').1 (Prod.mk.inj hu').2
  have hdim : finrank ℝ (EuclideanSpace ℝ (Fin 2)) = finrank ℝ (ℝ × ℝ) := by
    simp [Module.finrank_prod]
  let Le : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] ℝ × ℝ :=
    (LinearMap.linearEquivOfInjective _ hLinj hdim).toContinuousLinearEquiv
  have hLe : (Le : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ × ℝ) = L :=
    ContinuousLinearMap.ext fun u => rfl
  have hF' : HasStrictFDerivAt (fun x => (h x, l x))
      (Le : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ × ℝ) p := by
    rw [hLe]
    exact hF
  exact ⟨hF'.toOpenPartialHomeomorph _, hF'.mem_toOpenPartialHomeomorph_source, rfl⟩

/-- Local straightening of the transverse preimage at a point of the closed disk. -/
theorem exists_local_straightening_transverse_preimage {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) {g : EuclideanSpace ℝ (Fin 2) → E₃}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (htr : ∀ p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, TransverseAt S g p)
    (hbd : ∀ p ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, BoundaryTransverseAt S g p)
    {p : EuclideanSpace ℝ (Fin 2)}
    (hp : p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ∩ g ⁻¹' S) :
    ∃ (Λ : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) (ℝ × ℝ)) (c : ℝ),
      p ∈ Λ.source ∧
      (∀ x ∈ Λ.source, x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ∩ g ⁻¹' S ↔
        (Λ x).1 = 0 ∧ 0 ≤ (Λ x).2 + c) ∧
      ((Λ p).2 + c = 0 ↔ p ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
  obtain ⟨U, φ, hU, hpU, hφ, hzero, hreg⟩ := hS (g p) hp.2
  have hφd : ∀ y, DifferentiableAt ℝ φ y := fun y => hφ.differentiable (by simp) y
  have hgd : ∀ y, DifferentiableAt ℝ g y := fun y => hg.differentiable (by simp) y
  let h : EuclideanSpace ℝ (Fin 2) → ℝ := φ ∘ g
  have hh : ContDiff ℝ (⊤ : ℕ∞) h := hφ.comp hg
  have hhs : HasStrictFDerivAt h (fderiv ℝ h p) p :=
    hh.contDiffAt.hasStrictFDerivAt (by simp)
  have hdh : ∀ u, fderiv ℝ h p u = fderiv ℝ φ (g p) (fderiv ℝ g p u) := by
    intro u
    rw [show h = φ ∘ g from rfl, fderiv_comp p (hφd (g p)) (hgd p)]
    rfl
  have hT : tangentPlane S (g p) = (ℝ ∙ gradient φ (g p))ᗮ :=
    tangentPlane_eq hU hpU (hφ.contDiffAt.of_le (by exact_mod_cast le_top)) hzero hp.2
      (hreg _ ⟨hp.2, hpU⟩)
  have hker : ∀ y, fderiv ℝ φ (g p) y = 0 → y ∈ tangentPlane S (g p) := by
    intro y hy
    rw [hT, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_gradient_left]
    exact hy
  have hTne : tangentPlane S (g p) ≠ ⊤ := by
    intro htop
    have hdim := hS.finrank_tangentPlane hp.2
    rw [htop] at hdim
    norm_num [E₃] at hdim
  have hmemC : ∀ x, g x ∈ U →
      (x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ∩ g ⁻¹' S ↔
        x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧ h x = 0) := by
    intro x hxU
    have hiff : g x ∈ S ↔ φ (g x) = 0 := by
      constructor
      · intro hs
        exact ((Set.ext_iff.mp hzero (g x)).mp ⟨hs, hxU⟩).2
      · intro h0
        exact ((Set.ext_iff.mp hzero (g x)).mpr ⟨hxU, h0⟩).1
    exact and_congr_right fun _ => hiff
  have hUo : IsOpen (g ⁻¹' U) := hU.preimage hg.continuous
  by_cases hps : p ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1
  · -- boundary point: straighten with `-‖x‖²`
    have hbdp := hbd p hps hp.2
    let l : EuclideanSpace ℝ (Fin 2) → ℝ := fun x => -‖x‖ ^ 2
    have hl : HasStrictFDerivAt l (-(2 • innerSL ℝ p)) p :=
      (hasStrictFDerivAt_norm_sq p).neg
    have hp0 : p ≠ 0 := by
      intro h0
      rw [h0, mem_sphere_zero_iff_norm, norm_zero] at hps
      exact zero_ne_one hps
    have hinj : ∀ u, fderiv ℝ h p u = 0 → (-(2 • innerSL ℝ p)) u = 0 → u = 0 := by
      intro u hu1 hu2
      by_contra hu0
      have hpu : inner ℝ p u = 0 := by simpa using hu2
      have huK : u ∈ (ℝ ∙ p)ᗮ := Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hpu
      have : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1 + 1) := ⟨by simp⟩
      have hfin : finrank ℝ (ℝ ∙ p)ᗮ = 1 := Submodule.finrank_orthogonal_span_singleton hp0
      have hspan := (finrank_eq_one_iff_of_nonzero' (⟨u, huK⟩ : (ℝ ∙ p)ᗮ)
        (by simpa using hu0)).mp hfin
      apply hTne
      have hle : Submodule.map (fderiv ℝ g p : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] E₃) (ℝ ∙ p)ᗮ ≤
          tangentPlane S (g p) := by
        rintro _ ⟨w, hw, rfl⟩
        obtain ⟨c, hc⟩ := hspan ⟨w, hw⟩
        have hwc : w = c • u := (congrArg Subtype.val hc).symm
        have huT : fderiv ℝ g p u ∈ tangentPlane S (g p) := hker _ (by rw [← hdh]; exact hu1)
        change fderiv ℝ g p w ∈ tangentPlane S (g p)
        rw [hwc, map_smul]
        exact (tangentPlane S (g p)).smul_mem c huT
      simpa only [sup_eq_right.mpr hle] using hbdp
    obtain ⟨Λ, hΛp, hΛ⟩ := exists_straightening_chart hhs hl hinj
    refine ⟨Λ.restrOpen (g ⁻¹' U) hUo, 1, ⟨hΛp, hpU⟩, ?_, ?_⟩
    · intro x hx
      rw [OpenPartialHomeomorph.coe_restrOpen, hΛ, hmemC x hx.2, mem_closedBall_zero_iff]
      change ‖x‖ ≤ 1 ∧ h x = 0 ↔ h x = 0 ∧ 0 ≤ -‖x‖ ^ 2 + 1
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h2, by nlinarith [norm_nonneg x]⟩
      · rintro ⟨h2, h1⟩
        refine ⟨?_, h2⟩
        by_contra hlt
        have hlt' : 1 < ‖x‖ := lt_of_not_ge hlt
        nlinarith [norm_nonneg x]
    · rw [OpenPartialHomeomorph.coe_restrOpen, hΛ]
      refine iff_of_true ?_ hps
      change -‖p‖ ^ 2 + 1 = 0
      rw [mem_sphere_zero_iff_norm.mp hps]
      norm_num
  · -- interior point: straighten with a linear coordinate along the kernel
    have hpball : ‖p‖ < 1 := by
      have h1 : ‖p‖ ≤ 1 := mem_closedBall_zero_iff.mp hp.1
      have h2 : ‖p‖ ≠ 1 := fun he => hps (mem_sphere_zero_iff_norm.mpr he)
      exact lt_of_le_of_ne h1 h2
    have hα : fderiv ℝ h p ≠ 0 := by
      intro h0
      apply hTne
      have hle : LinearMap.range (fderiv ℝ g p : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] E₃) ≤
          tangentPlane S (g p) := by
        rintro _ ⟨u, rfl⟩
        apply hker
        change fderiv ℝ φ (g p) (fderiv ℝ g p u) = 0
        rw [← hdh, h0]
        rfl
      simpa only [sup_eq_right.mpr hle] using htr p hp.1 hp.2
    let α : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ := (fderiv ℝ h p : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ)
    have hrn := LinearMap.finrank_range_add_finrank_ker α
    have hr1 : finrank ℝ (LinearMap.range α) ≤ 1 :=
      (Submodule.finrank_le _).trans (by simp)
    have hr0 : finrank ℝ (LinearMap.range α) ≠ 0 := by
      rw [Ne, Submodule.finrank_eq_zero, LinearMap.range_eq_bot]
      intro h0
      apply hα
      ext u
      exact congrArg (fun L : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ => L u) h0
    have hk1 : finrank ℝ (LinearMap.ker α) = 1 := by
      simp only [finrank_euclideanSpace_fin] at hrn
      omega
    have hkne : LinearMap.ker α ≠ ⊥ := by
      intro h0
      rw [h0, finrank_bot] at hk1
      exact zero_ne_one hk1
    obtain ⟨v, hvK, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hkne
    let l : EuclideanSpace ℝ (Fin 2) → ℝ := fun x => innerSL ℝ v x
    have hl : HasStrictFDerivAt l (innerSL ℝ v) p := (innerSL ℝ v).hasStrictFDerivAt
    have hinj : ∀ u, fderiv ℝ h p u = 0 → innerSL ℝ v u = 0 → u = 0 := by
      intro u hu1 hu2
      have hspan := (finrank_eq_one_iff_of_nonzero' (⟨v, hvK⟩ : LinearMap.ker α)
        (by simpa using hv0)).mp hk1
      obtain ⟨c, hc⟩ := hspan ⟨u, hu1⟩
      have huc : u = c • v := (congrArg Subtype.val hc).symm
      rw [huc, map_smul, innerSL_apply_apply, real_inner_self_eq_norm_sq, smul_eq_mul] at hu2
      have hvn : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hv0)
      have hc0 : c = 0 := (mul_eq_zero.mp hu2).resolve_right hvn
      rw [huc, hc0, zero_smul]
    obtain ⟨Λ, hΛp, hΛ⟩ := exists_straightening_chart hhs hl hinj
    let O : Set (EuclideanSpace ℝ (Fin 2)) :=
      g ⁻¹' U ∩ Metric.ball 0 1 ∩ {x | |l x - l p| < 1}
    have hO : IsOpen O :=
      (hUo.inter Metric.isOpen_ball).inter (isOpen_lt
        (continuous_abs.comp ((innerSL ℝ v).continuous.sub continuous_const)) continuous_const)
    have hpO : p ∈ O := ⟨⟨hpU, mem_ball_zero_iff.mpr hpball⟩, by simp⟩
    refine ⟨Λ.restrOpen O hO, 1 - l p, ⟨hΛp, hpO⟩, ?_, ?_⟩
    · intro x hx
      obtain ⟨⟨hxU, hxb⟩, hxl⟩ := hx.2
      rw [OpenPartialHomeomorph.coe_restrOpen, hΛ, hmemC x hxU]
      change x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧ h x = 0 ↔
        h x = 0 ∧ 0 ≤ l x + (1 - l p)
      have hxl' : |l x - l p| < 1 := hxl
      have hpos : 0 ≤ l x + (1 - l p) := by
        have := (abs_lt.mp hxl').1
        linarith
      exact ⟨fun hh => ⟨hh.2, hpos⟩, fun hh => ⟨Metric.ball_subset_closedBall hxb, hh.1⟩⟩
    · rw [OpenPartialHomeomorph.coe_restrOpen, hΛ]
      refine iff_of_false ?_ hps
      change l p + (1 - l p) ≠ 0
      norm_num

/-- `cor:transv-preimage`, disk case, with the boundary-transversality hypothesis
(proposed correction): the preimage is a compact topological one-manifold with boundary,
and its manifold boundary is exactly its intersection with the boundary circle. -/
theorem transverse_preimage_disk_of_boundary_transverse {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S)
    {g : EuclideanSpace ℝ (Fin 2) → E₃} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (htr : ∀ p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, TransverseAt S g p)
    (hbd : ∀ p ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, BoundaryTransverseAt S g p) :
    IsCompact (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ∩ g ⁻¹' S) ∧
      IsOneManifoldWithBoundary (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ∩ g ⁻¹' S) ∧
      oneManifoldBoundary (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ∩ g ⁻¹' S) =
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ∩ g ⁻¹' S := by
  set C := Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ∩ g ⁻¹' S with hCdef
  have hchart : ∀ x : C, ∃ e : OpenPartialHomeomorph C ℝ≥0, x ∈ e.source ∧
      ((e x : ℝ≥0) = 0 ↔ (x : EuclideanSpace ℝ (Fin 2)) ∈
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
    intro x
    obtain ⟨Λ, c, hxΛ, hC, hval⟩ :=
      exists_local_straightening_transverse_preimage hS hg htr hbd x.2
    obtain ⟨e, hxe, hex⟩ := exists_halfLine_chart_of_straightening Λ c hC x hxΛ
    refine ⟨e, hxe, ?_⟩
    rw [← hval, ← hex, NNReal.coe_eq_zero]
  refine ⟨isCompact_transverse_preimage hc hg.continuous, fun x => ?_, ?_⟩
  · obtain ⟨e, hxe, -⟩ := hchart x
    exact ⟨e, hxe⟩
  · ext x
    constructor
    · rintro ⟨hxC, e, hxe, hex⟩
      obtain ⟨e', hxe', he'⟩ := hchart ⟨x, hxC⟩
      have h0 := oneManifoldBoundary_chart_eq_zero (x := ⟨x, hxC⟩) ⟨hxC, e, hxe, hex⟩ e' hxe'
      exact ⟨he'.mp h0, hxC.2⟩
    · intro hx
      have hxC : x ∈ C := ⟨Metric.sphere_subset_closedBall hx.1, hx.2⟩
      obtain ⟨e, hxe, he⟩ := hchart ⟨x, hxC⟩
      exact ⟨hxC, e, hxe, he.mpr hx.1⟩

end LiquidDrop
