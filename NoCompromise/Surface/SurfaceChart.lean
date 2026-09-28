import NoCompromise.Surface.TangentFlow

/-!
# Projection charts on an embedded surface

A `C^k` chart of an embedded surface onto an open subset of the plane whose forward map is
a fixed continuous linear projection. This is the chart in which `lem:morse-coords` is
applied to a height function on the surface (`lem:local-sectors` on `Σ`).
-/

noncomputable section

open Set Filter Function InnerProductSpace
open scoped Topology Gradient

namespace LiquidDrop

local notation "E2" => EuclideanSpace ℝ (Fin 2)

set_option maxSynthPendingDepth 8

/-- A `C^k` chart of an embedded surface near `q`, onto an open subset of the plane, whose
forward map is the restriction of a continuous linear projection `x ↦ P (x - q)` and whose
source is the trace of an ambient open set. -/
theorem IsSmoothEmbeddedSurface.exists_projection_chart {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) {q : E₃} (hq : q ∈ S) (k : ℕ) :
    ∃ (e : OpenPartialHomeomorph S E2) (P : E₃ →L[ℝ] E2) (U : Set E₃),
      IsOpen U ∧ q ∈ U ∧ e.source = Subtype.val ⁻¹' U ∧
      (⟨q, hq⟩ : S) ∈ e.source ∧ e ⟨q, hq⟩ = 0 ∧
      (∀ x : S, e x = P ((x : E₃) - q)) ∧
      ContDiffOn ℝ k (fun y => (e.symm y : E₃)) e.target := by
  classical
  obtain ⟨W, φ, hW, hqW, hφ, hzero, hreg⟩ := hS q hq
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  have hd := hφ1.contDiffAt.hasStrictFDerivAt one_ne_zero (x := q)
  have hsurj : (fderiv ℝ φ q).range = ⊤ := by
    apply Module.Dual.range_eq_top_of_ne_zero
    intro hh
    apply hreg q ⟨hq, hqW⟩
    apply (toDual ℝ E₃).injective
    rw [toDual_gradient, map_zero]
    exact ContinuousLinearMap.ext fun x => congrArg (fun L : E₃ →ₗ[ℝ] ℝ => L x) hh
  let K := (fderiv ℝ φ q).ker
  have hK := (fderiv ℝ φ q).ker_closedComplemented_of_finiteDimensional_range
  let P₀ : E₃ →L[ℝ] K := Classical.choose hK
  let d := hd.implicitFunctionDataOfComplemented φ (fderiv ℝ φ q) hsurj hK
  let E := d.toOpenPartialHomeomorph
  have hE (x : E₃) : E x = (φ x, P₀ (x - q)) := rfl
  have hKr : Module.finrank ℝ K = 2 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (fderiv ℝ φ q : E₃ →ₗ[ℝ] ℝ)
    have hr : Module.finrank ℝ (LinearMap.range (fderiv ℝ φ q : E₃ →ₗ[ℝ] ℝ)) = 1 := by
      have : LinearMap.range (fderiv ℝ φ q : E₃ →ₗ[ℝ] ℝ) = ⊤ := hsurj
      rw [this, finrank_top, Module.finrank_self]
    rw [hr, finrank_euclideanSpace_fin] at h1
    change Module.finrank ℝ (LinearMap.ker (fderiv ℝ φ q : E₃ →ₗ[ℝ] ℝ)) = 2
    omega
  let J : K ≃L[ℝ] E2 :=
    (LinearEquiv.ofFinrankEq K E2
      (by rw [hKr, finrank_euclideanSpace_fin])).toContinuousLinearEquiv
  let P : E₃ →L[ℝ] E2 := (J : K →L[ℝ] E2).comp P₀
  let ψ : E2 → E₃ := fun y => E.symm (0, J.symm y)
  have hqzero : φ q = 0 := (hzero ▸ (show q ∈ S ∩ W from ⟨hq, hqW⟩)).2
  have heq : E q = (0, 0) := by simp [hE, hqzero]
  have hqs : q ∈ E.source := d.pt_mem_toOpenPartialHomeomorph_source
  have hqt : (0, 0) ∈ E.target := heq ▸ E.map_source hqs
  have hinv : E.symm (0, 0) = q := heq ▸ E.left_inv hqs
  have heC : ContDiff ℝ k E :=
    (hφ.of_le (by exact_mod_cast le_top)).prodMk
      (P₀.contDiff.comp (contDiff_id.sub contDiff_const))
  have hiC : ContDiffAt ℝ k E.symm (0, 0) := by
    apply E.contDiffAt_symm hqt
    · rw [hinv]
      exact d.hasStrictFDerivAt.hasFDerivAt
    · exact heC.contDiffAt
  have hψC : ContDiffAt ℝ k ψ 0 := by
    have hlin : ContDiffAt ℝ k (fun y : E2 => ((0 : ℝ), J.symm y)) 0 :=
      contDiffAt_const.prodMk (J.symm : E2 →L[ℝ] K).contDiff.contDiffAt
    have h00 : ((0 : ℝ), J.symm (0 : E2)) = (0, 0) := by simp
    exact (h00 ▸ hiC).comp 0 hlin
  obtain ⟨O, hOo, h0O, hψO⟩ := hψC.contDiffOn' le_rfl (by simp)
  have hψO' : ContDiffOn ℝ k ψ O := by simpa [insert_eq_of_mem h0O] using hψO
  let T : Set E2 := O ∩ ({y | ((0 : ℝ), J.symm y) ∈ E.target} ∩ ψ ⁻¹' W)
  let U : Set E₃ := E.source ∩ W ∩ (fun x => P (x - q)) ⁻¹' O
  have hU : IsOpen U :=
    (E.open_source.inter hW).inter
      (hOo.preimage (P.continuous.comp (continuous_id.sub continuous_const)))
  have hpair : Continuous (fun y : E2 => ((0 : ℝ), J.symm y)) :=
    continuous_const.prodMk J.symm.continuous
  have hT : IsOpen T := by
    refine hOo.inter ?_
    have hψc : ContinuousOn ψ {y | ((0 : ℝ), J.symm y) ∈ E.target} :=
      E.continuousOn_symm.comp hpair.continuousOn fun y hy => hy
    exact hψc.isOpen_inter_preimage (E.open_target.preimage hpair) hW
  -- basic identities
  have hPψ : ∀ y ∈ T, P (ψ y - q) = y := by
    intro y hy
    have h := E.right_inv hy.2.1
    have h2 : P₀ (ψ y - q) = J.symm y := by
      have := congrArg Prod.snd h
      simpa [hE, ψ] using this
    change J (P₀ (ψ y - q)) = y
    rw [h2]; simp
  have hψS : ∀ y ∈ T, ψ y ∈ S := by
    intro y hy
    have h := E.right_inv hy.2.1
    have h1 : φ (ψ y) = 0 := by
      have := congrArg Prod.fst h
      simpa [hE, ψ] using this
    have hmem : ψ y ∈ {x ∈ W | φ x = 0} := ⟨hy.2.2, h1⟩
    rw [← hzero] at hmem
    exact hmem.1
  have hψU : ∀ y ∈ T, ψ y ∈ U := by
    intro y hy
    refine ⟨⟨E.map_target hy.2.1, hy.2.2⟩, ?_⟩
    change P (ψ y - q) ∈ O
    rw [hPψ y hy]; exact hy.1
  have hEx : ∀ x : E₃, x ∈ S → x ∈ W → E x = ((0 : ℝ), J.symm (P (x - q))) := by
    intro x hxS hxW
    have hx0 : φ x = 0 := (hzero ▸ (show x ∈ S ∩ W from ⟨hxS, hxW⟩)).2
    simp [hE, hx0, P]
  have hmapT : ∀ x : E₃, x ∈ S → x ∈ U → P (x - q) ∈ T ∧ ψ (P (x - q)) = x := by
    intro x hxS hxU
    have hEx' := hEx x hxS hxU.1.2
    have hleft : ψ (P (x - q)) = x := by
      change E.symm ((0 : ℝ), J.symm (P (x - q))) = x
      rw [← hEx']
      exact E.left_inv hxU.1.1
    refine ⟨⟨hxU.2, ?_, ?_⟩, hleft⟩
    · change ((0 : ℝ), J.symm (P (x - q))) ∈ E.target
      rw [← hEx']
      exact E.map_source hxU.1.1
    · change ψ (P (x - q)) ∈ W
      rw [hleft]; exact hxU.1.2
  let inv : E2 → S := fun y => if hy : y ∈ T then ⟨ψ y, hψS y hy⟩ else ⟨q, hq⟩
  have hinvT : ∀ y ∈ T, (inv y : E₃) = ψ y := by
    intro y hy
    simp [inv, hy]
  let e : OpenPartialHomeomorph S E2 :=
    { toFun := fun x => P ((x : E₃) - q)
      invFun := inv
      source := Subtype.val ⁻¹' U
      target := T
      map_source' := fun x hx => (hmapT x x.2 hx).1
      map_target' := fun y hy => by
        change (inv y : E₃) ∈ U
        rw [hinvT y hy]; exact hψU y hy
      left_inv' := fun x hx => by
        apply Subtype.ext
        rw [hinvT _ (hmapT x x.2 hx).1]
        exact (hmapT x x.2 hx).2
      right_inv' := fun y hy => by
        rw [hinvT y hy]; exact hPψ y hy
      open_source := hU.preimage continuous_subtype_val
      open_target := hT
      continuousOn_toFun :=
        (P.continuous.comp (continuous_subtype_val.sub continuous_const)).continuousOn
      continuousOn_invFun := by
        rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
        exact (hψO'.continuousOn.mono inter_subset_left).congr fun y hy => hinvT y hy }
  refine ⟨e, P, U, hU, ?_, rfl, ?_, ?_, fun x => rfl, ?_⟩
  · have := hψU 0 ?_
    · simpa [ψ, hinv] using this
    · refine ⟨h0O, ?_, ?_⟩
      · simpa using hqt
      · change E.symm ((0 : ℝ), J.symm 0) ∈ W
        simpa [hinv] using hqW
  · change q ∈ U
    have := hψU 0 ?_
    · simpa [ψ, hinv] using this
    · refine ⟨h0O, ?_, ?_⟩
      · simpa using hqt
      · change E.symm ((0 : ℝ), J.symm 0) ∈ W
        simpa [hinv] using hqW
  · change P (q - q) = 0
    simp
  · exact (hψO'.mono inter_subset_left).congr fun y hy => hinvT y hy

end LiquidDrop
