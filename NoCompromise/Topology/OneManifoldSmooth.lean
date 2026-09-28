import NoCompromise.Topology.OneManifoldFlow
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Smooth complete integral curves on one-manifolds

The given global integral curve supplies completeness. Smoothness always means
`∞ : WithTop ℕ∞`, not the analytic regularity `⊤ : WithTop ℕ∞`.
-/

namespace LiquidDrop

open Set Function Filter Manifold
open scoped Topology ContDiff

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold 𝓘(ℝ, ℝ) ∞ M]
  {v : (x : M) → TangentSpace 𝓘(ℝ, ℝ) x} {γ : ℝ → M}

set_option backward.isDefEq.respectTransparency false in
/-- A global integral curve of a smooth vector field is smooth. -/
theorem oneManifold_integralCurve_contMDiff
    (hv : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent ∞
      (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, ℝ) M)))
    (hγ : IsMIntegralCurve γ v) : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ γ := by
  apply contMDiff_infty.mpr
  intro n
  induction n with
  | zero => exact contMDiff_zero_iff.mpr hγ.continuous
  | succ n ih =>
    intro t₀
    apply contMDiffAt_iff_target.mpr
    refine ⟨hγ.continuous.continuousAt, ?_⟩
    apply ContDiffAt.contMDiffAt
    have hc : ContDiffAt ℝ n
        (fun t => tangentCoordChange 𝓘(ℝ, ℝ) (γ t) (γ t₀) (γ t) (v (γ t))) t₀ := by
      have hs := (hv.of_le (by exact_mod_cast le_top)).contMDiffAt.comp t₀ (ih t₀)
      have he := (contMDiffAt_extChartAt (I := 𝓘(ℝ, ℝ).tangent)
        (x := (⟨γ t₀, v (γ t₀)⟩ : TangentBundle 𝓘(ℝ, ℝ) M)) (n := n)).comp t₀ hs
      exact he.contDiffAt.snd
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by simp]
    apply contDiffAt_succ_iff_hasFDerivAt.mpr
    refine ⟨fun t => (1 : ℝ →L[ℝ] ℝ).smulRight
      (tangentCoordChange 𝓘(ℝ, ℝ) (γ t) (γ t₀) (γ t) (v (γ t))), ?_, ?_⟩
    · exact ((hγ.isMIntegralCurveAt t₀).eventually_hasDerivAt.mono
        fun _ ht => ht.hasFDerivAt).exists_mem
    · exact contDiffAt_const.smulRight hc

set_option backward.isDefEq.respectTransparency false in
/-- A complete integral curve of a nowhere-zero smooth field is a local
diffeomorphism. -/
theorem oneManifold_integralCurve_isLocalDiffeomorph
    (hv : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent ∞
      (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, ℝ) M)))
    (hv0 : ∀ x, v x ≠ 0) (hγ : IsMIntegralCurve γ v) :
    IsLocalDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ γ := by
  have hv1 := hv.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  have hs := oneManifold_integralCurve_contMDiff hv hγ
  have hl : IsLocalHomeomorph γ := by
    apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
    intro t
    obtain ⟨s, hst, hinj⟩ :=
      oneManifold_integralCurveAt_locally_injective hv1 hv0 (hγ.isMIntegralCurveAt t)
    obtain ⟨u, hus, hu, htu⟩ := mem_nhds_iff.mp hst
    refine ⟨u, hu.mem_nhds htu, ?_⟩
    exact Topology.isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr
      ⟨hγ.continuous.comp continuous_subtype_val,
        injOn_iff_injective.mp (hinj.mono hus),
        (oneManifold_integralCurve_isOpenMap hv1 hv0 hγ).comp hu.isOpenMap_subtype_val⟩
  intro t
  obtain ⟨e, ht, he⟩ := hl t
  refine ⟨{ e with
    contMDiffOn_toFun := by
      change ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (e : ℝ → M) e.source
      rw [← he]
      exact hs.contMDiffOn
    contMDiffOn_invFun := ?_ }, ht, fun _ _ => congrFun he _⟩
  intro y hy
  apply ContMDiffAt.contMDiffWithinAt
  rw [contMDiffAt_iff_source, ModelWithCorners.range_eq_univ, contMDiffWithinAt_univ]
  apply ContDiffAt.contMDiffAt
  let c := e.trans (chartAt ℝ y)
  have hγy : γ (e.symm y) = y := by rw [he]; exact e.right_inv hy
  have hcy : chartAt ℝ y y ∈ c.target := by
    exact ⟨(chartAt ℝ y).map_source (mem_chart_source ℝ y), by simpa using hy⟩
  have hci : c.symm (chartAt ℝ y y) = e.symm y := by
    change e.symm ((chartAt ℝ y).symm ((chartAt ℝ y) y)) = e.symm y
    rw [(chartAt ℝ y).left_inv (mem_chart_source ℝ y)]
  have hd : HasDerivAt c (v (γ (e.symm y))) (c.symm (chartAt ℝ y y)) := by
    rw [hci, hγy]
    have hd := (oneManifold_integralCurveAt_hasStrictDerivAt hv1
      (hγ.isMIntegralCurveAt (e.symm y))).hasDerivAt
    rw [hγy] at hd
    simpa only [c, OpenPartialHomeomorph.coe_trans, ← he, extChartAt_coe,
      modelWithCornersSelf_coe, id_comp] using hd
  have hc : ContDiffAt ℝ ∞ c (c.symm (chartAt ℝ y y)) := by
    rw [hci]
    have hc := (contMDiffAt_extChartAt (I := 𝓘(ℝ, ℝ))
      (x := γ (e.symm y)) (n := ∞)).comp
      (e.symm y) (hs (e.symm y))
    rw [hγy] at hc
    simpa only [c, OpenPartialHomeomorph.coe_trans, ← he, extChartAt_coe,
      modelWithCornersSelf_coe, id_comp] using hc.contDiffAt
  exact c.contDiffAt_symm_deriv (hv0 _) hcy hd hc

/-- An injective complete integral curve of a nowhere-zero smooth field on a
connected Hausdorff one-manifold is a diffeomorphism from the real line. -/
theorem oneManifold_integralCurve_diffeomorph_real [T2Space M] [ConnectedSpace M]
    (hv : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent ∞
      (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, ℝ) M)))
    (hv0 : ∀ x, v x ≠ 0) (hγ : IsMIntegralCurve γ v) (hinj : Injective γ) :
    ∃ Φ : ℝ ≃ₘ^∞⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ M, ⇑Φ = γ := by
  exact ⟨(oneManifold_integralCurve_isLocalDiffeomorph hv hv0 hγ).diffeomorphOfBijective
    ⟨hinj, oneManifold_integralCurve_surjective (hv.of_le (by simp)) hv0 hγ⟩, rfl⟩

end LiquidDrop
