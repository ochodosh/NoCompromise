import NoCompromise.Topology.OneManifoldCircle
import NoCompromise.Topology.OneManifoldMaximal
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Smooth classification of one-manifolds with a nonvanishing tangent field

The integral curve is only assumed to be defined on its maximal open interval.
Smoothness means `∞ : WithTop ℕ∞` throughout.
-/

namespace LiquidDrop

open Set Function Filter Manifold
open scoped Topology ContDiff

section IntegralCurve

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold 𝓘(ℝ, ℝ) ∞ M]
  {v : (x : M) → TangentSpace 𝓘(ℝ, ℝ) x} {γ : ℝ → M} {J : Set ℝ}

set_option backward.isDefEq.respectTransparency false in
/-- An integral curve of a smooth field is smooth on its open domain. -/
theorem oneManifold_integralCurveOn_contMDiffOn
    (hv : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent ∞
      (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, ℝ) M)))
    (hJ : IsOpen J) (hγ : IsMIntegralCurveOn γ v J) :
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ γ J := by
  apply contMDiffOn_infty.mpr
  intro n
  induction n with
  | zero => exact contMDiffOn_zero_iff.mpr hγ.continuousOn
  | succ n ih =>
    intro t₀ ht₀
    apply ContMDiffAt.contMDiffWithinAt
    apply contMDiffAt_iff_target.mpr
    have hγ₀ := hγ.isMIntegralCurveAt (hJ.mem_nhds ht₀)
    refine ⟨hγ₀.continuousAt, ?_⟩
    apply ContDiffAt.contMDiffAt
    have hc : ContDiffAt ℝ n
        (fun t => tangentCoordChange 𝓘(ℝ, ℝ) (γ t) (γ t₀) (γ t) (v (γ t))) t₀ := by
      have hs := (hv.of_le (by exact_mod_cast le_top)).contMDiffAt.comp t₀
        (ih.contMDiffAt (hJ.mem_nhds ht₀))
      have he := (contMDiffAt_extChartAt (I := 𝓘(ℝ, ℝ).tangent)
        (x := (⟨γ t₀, v (γ t₀)⟩ : TangentBundle 𝓘(ℝ, ℝ) M)) (n := n)).comp t₀ hs
      exact he.contDiffAt.snd
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by simp]
    apply contDiffAt_succ_iff_hasFDerivAt.mpr
    refine ⟨fun t => (1 : ℝ →L[ℝ] ℝ).smulRight
      (tangentCoordChange 𝓘(ℝ, ℝ) (γ t) (γ t₀) (γ t) (v (γ t))), ?_, ?_⟩
    · exact (hγ₀.eventually_hasDerivAt.mono fun _ ht => ht.hasFDerivAt).exists_mem
    · exact contDiffAt_const.smulRight hc

set_option backward.isDefEq.respectTransparency false in
/-- An integral curve of a smooth nowhere-zero field is a local diffeomorphism
at every time in its open domain. -/
theorem oneManifold_integralCurveOn_isLocalDiffeomorphAt
    (hv : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent ∞
      (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, ℝ) M)))
    (hv0 : ∀ x, v x ≠ 0) (hJ : IsOpen J) (hγ : IsMIntegralCurveOn γ v J) :
    ∀ t ∈ J, IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ γ t := by
  intro t ht
  have hv1 := hv.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  have hs := oneManifold_integralCurveOn_contMDiffOn hv hJ hγ
  obtain ⟨s, hst, hinj⟩ := oneManifold_integralCurveAt_locally_injective hv1 hv0
    (hγ.isMIntegralCurveAt (hJ.mem_nhds ht))
  obtain ⟨u, hus, hu, htu⟩ := mem_nhds_iff.mp (inter_mem hst (hJ.mem_nhds ht))
  have huJ : u ⊆ J := fun _ hx => (hus hx).2
  have hinju : InjOn γ u := hinj.mono fun _ hx => (hus hx).1
  have hopen : IsOpenMap (u.domRestrict γ) := by
    intro U hU
    have hU' : IsOpen ((↑) '' U : Set ℝ) := hu.isOpenMap_subtype_val U hU
    rw [show u.domRestrict γ '' U = γ '' ((↑) '' U) by rw [image_image]; rfl,
      isOpen_iff_mem_nhds]
    rintro _ ⟨r, hr, rfl⟩
    have hrJ : r ∈ J := by
      obtain ⟨w, -, rfl⟩ := hr
      exact huJ w.2
    rw [← oneManifold_integralCurveAt_map_nhds hv1 hv0
      (hγ.isMIntegralCurveAt (hJ.mem_nhds hrJ))]
    exact image_mem_map (hU'.mem_nhds hr)
  let e : OpenPartialHomeomorph ℝ M := OpenPartialHomeomorph.ofContinuousOpenRestrict
    hinju.toPartialEquiv (hγ.continuousOn.mono huJ) hopen hu
  have he : (e : ℝ → M) = γ := rfl
  have heJ : e.source ⊆ J := huJ
  refine ⟨{ e with
    contMDiffOn_toFun := by
      change ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (e : ℝ → M) e.source
      rw [he]
      exact hs.mono heJ
    contMDiffOn_invFun := ?_ }, htu, fun _ _ => rfl⟩
  intro y hy
  apply ContMDiffAt.contMDiffWithinAt
  rw [contMDiffAt_iff_source, ModelWithCorners.range_eq_univ, contMDiffWithinAt_univ]
  apply ContDiffAt.contMDiffAt
  let c := e.trans (chartAt ℝ y)
  have hγy : γ (e.symm y) = y := by rw [← he]; exact e.right_inv hy
  have hcy : chartAt ℝ y y ∈ c.target := by
    exact ⟨(chartAt ℝ y).map_source (mem_chart_source ℝ y), by simpa using hy⟩
  have hci : c.symm (chartAt ℝ y y) = e.symm y := by
    change e.symm ((chartAt ℝ y).symm ((chartAt ℝ y) y)) = e.symm y
    rw [(chartAt ℝ y).left_inv (mem_chart_source ℝ y)]
  have hiJ : e.symm y ∈ J := heJ (e.map_target hy)
  have hd : HasDerivAt c (v (γ (e.symm y))) (c.symm (chartAt ℝ y y)) := by
    rw [hci, hγy]
    have hd := (oneManifold_integralCurveAt_hasStrictDerivAt hv1
      (hγ.isMIntegralCurveAt (hJ.mem_nhds hiJ))).hasDerivAt
    rw [hγy] at hd
    simpa only [c, OpenPartialHomeomorph.coe_trans, he, extChartAt_coe,
      modelWithCornersSelf_coe, id_comp] using hd
  have hc : ContDiffAt ℝ ∞ c (c.symm (chartAt ℝ y y)) := by
    rw [hci]
    have hc := (contMDiffAt_extChartAt (I := 𝓘(ℝ, ℝ))
      (x := γ (e.symm y)) (n := ∞)).comp (e.symm y)
      (hs.contMDiffAt (hJ.mem_nhds hiJ))
    rw [hγy] at hc
    simpa only [c, OpenPartialHomeomorph.coe_trans, he, extChartAt_coe,
      modelWithCornersSelf_coe, id_comp] using hc.contDiffAt
  exact c.contDiffAt_symm_deriv (hv0 _) hcy hd hc

end IntegralCurve

/-- A smooth real function whose derivative is everywhere nonzero is a smooth
local diffeomorphism. -/
theorem real_isLocalDiffeomorph_of_contDiff_deriv_ne_zero {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hd : ∀ t, deriv f t ≠ 0) :
    IsLocalDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ f := by
  intro t
  have hft := (hf.hasStrictDerivAt (x := t) (by simp)).hasStrictFDerivAt_equiv (hd t)
  let e := hft.toOpenPartialHomeomorph f
  refine ⟨{ e with
    contMDiffOn_toFun := hf.contMDiff.contMDiffOn
    contMDiffOn_invFun := ?_ }, hft.mem_toOpenPartialHomeomorph_source, fun _ _ => rfl⟩
  intro y hy
  apply ContMDiffAt.contMDiffWithinAt
  apply ContDiffAt.contMDiffAt
  exact e.contDiffAt_symm_deriv (hd (e.symm y)) hy
    (hf.differentiable (by simp) _).hasDerivAt hf.contDiffAt

/-- Every nonempty open order-connected subset of the line admits an increasing
smooth parametrization by the whole line, with positive derivative. -/
theorem exists_contDiff_parametrization_of_isOpen_ordConnected {J : Set ℝ}
    (hJo : IsOpen J) (hJc : J.OrdConnected) (hne : J.Nonempty) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ t, 0 < deriv ψ t) ∧ Injective ψ ∧
      range ψ = J ∧ IsLocalDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ ψ := by
  suffices h : ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ t, 0 < deriv ψ t) ∧ range ψ = J by
    obtain ⟨ψ, hs, hd, hr⟩ := h
    exact ⟨ψ, hs, hd, (strictMono_of_deriv_pos hd).injective, hr,
      real_isLocalDiffeomorph_of_contDiff_deriv_ne_zero hs (fun t => (hd t).ne')⟩
  have key : ∀ t, t ∈ J ↔ (∃ x ∈ J, x < t) ∧ (∃ y ∈ J, t < y) := fun t =>
    ⟨fun ht => by
      obtain ⟨a, b, hab, hta, -⟩ := exists_Ioo_subset_of_isOpen_ordConnected hJo hJc ht ht
      obtain ⟨h1, h2⟩ := hta
      exact ⟨⟨(a + t) / 2, hab ⟨by linarith, by linarith⟩, by linarith⟩,
        ⟨(t + b) / 2, hab ⟨by linarith, by linarith⟩, by linarith⟩⟩,
    fun ⟨⟨_, hx, hxt⟩, ⟨_, hy, hty⟩⟩ => hJc.out hx hy ⟨hxt.le, hty.le⟩⟩
  by_cases hb : BddBelow J <;> by_cases ha : BddAbove J
  · have hJ : J = Ioo (sInf J) (sSup J) := ext fun t => by
      rw [key t, mem_Ioo, csInf_lt_iff hb hne, lt_csSup_iff ha hne]
    have hab : sInf J < sSup J := by
      obtain ⟨t, ht⟩ := hne
      have h := (key t).mp ht
      exact ((csInf_lt_iff hb ⟨t, ht⟩).mpr h.1).trans ((lt_csSup_iff ha ⟨t, ht⟩).mpr h.2)
    rw [hJ]
    set a := sInf J
    set b := sSup J
    have hden (t : ℝ) : 0 < 1 + Real.exp (-t) := by positivity
    have hder (t : ℝ) : HasDerivAt (fun s => a + (b - a) / (1 + Real.exp (-s)))
        ((b - a) * Real.exp (-t) / (1 + Real.exp (-t)) ^ 2) t := by
      convert! ((hasDerivAt_const t (b - a)).div
        (((hasDerivAt_id t).neg.exp).const_add 1) (hden t).ne').const_add a using 1
      dsimp
      ring
    refine ⟨fun s => a + (b - a) / (1 + Real.exp (-s)),
      contDiff_const.add (contDiff_const.div (contDiff_const.add contDiff_id.neg.exp)
        (fun t => (hden t).ne')), ?_, ?_⟩
    · intro t
      rw [(hder t).deriv]
      exact div_pos (mul_pos (sub_pos.mpr hab) (Real.exp_pos _)) (sq_pos_of_pos (hden t))
    · apply Subset.antisymm
      · rintro _ ⟨s, rfl⟩
        have hp : 0 < (b - a) / (1 + Real.exp (-s)) := div_pos (sub_pos.mpr hab) (hden s)
        have hq : (b - a) / (1 + Real.exp (-s)) < b - a := by
          rw [div_lt_iff₀ (hden s)]
          nlinarith [Real.exp_pos (-s)]
        exact ⟨by linarith, by linarith⟩
      · intro t ht
        refine ⟨Real.log (t - a) - Real.log (b - t), ?_⟩
        have hta : 0 < t - a := sub_pos.mpr ht.1
        have hbt : 0 < b - t := sub_pos.mpr ht.2
        dsimp only
        rw [neg_sub, Real.exp_sub, Real.exp_log hbt, Real.exp_log hta]
        field_simp
        ring
  · have hJ : J = Ioi (sInf J) := ext fun t => by
      rw [key t, mem_Ioi, csInf_lt_iff hb hne, and_iff_left (not_bddAbove_iff.mp ha t)]
    rw [hJ]
    refine ⟨fun s => sInf J + Real.exp s, contDiff_const.add Real.contDiff_exp, ?_, ?_⟩
    · intro t
      rw [((Real.hasDerivAt_exp t).const_add (sInf J)).deriv]
      exact Real.exp_pos t
    · apply Subset.antisymm
      · rintro _ ⟨s, rfl⟩
        exact lt_add_of_pos_right _ (Real.exp_pos s)
      · intro t ht
        refine ⟨Real.log (t - sInf J), ?_⟩
        dsimp only
        rw [Real.exp_log (sub_pos.mpr ht)]
        ring
  · have hJ : J = Iio (sSup J) := ext fun t => by
      rw [key t, mem_Iio, lt_csSup_iff ha hne, and_iff_right (not_bddBelow_iff.mp hb t)]
    rw [hJ]
    have hder (t : ℝ) : HasDerivAt (fun s => sSup J - Real.exp (-s)) (Real.exp (-t)) t := by
      convert! (((hasDerivAt_id t).neg.exp).const_sub (sSup J)) using 1
      dsimp
      ring
    refine ⟨fun s => sSup J - Real.exp (-s), contDiff_const.sub contDiff_id.neg.exp, ?_, ?_⟩
    · intro t
      rw [(hder t).deriv]
      exact Real.exp_pos _
    · apply Subset.antisymm
      · rintro _ ⟨s, rfl⟩
        exact sub_lt_self _ (Real.exp_pos _)
      · intro t ht
        refine ⟨-Real.log (sSup J - t), ?_⟩
        dsimp only
        rw [neg_neg, Real.exp_log (sub_pos.mpr ht)]
        ring
  · have hJ : J = univ := eq_univ_of_forall fun t =>
      (key t).mpr ⟨not_bddBelow_iff.mp hb t, not_bddAbove_iff.mp ha t⟩
    exact ⟨id, contDiff_id, fun t => by simp, by simpa using hJ.symm⟩

section Classification

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold 𝓘(ℝ, ℝ) ∞ M] [T2Space M]
  {v : (x : M) → TangentSpace 𝓘(ℝ, ℝ) x}

/-- An injective maximal integral curve of a smooth nowhere-zero field on a
connected Hausdorff one-manifold yields a diffeomorphism from the whole real line. -/
theorem IsMaximalMIntegralCurveOn.exists_diffeomorph_real [ConnectedSpace M]
    (hv : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent ∞
      (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, ℝ) M)))
    (hv0 : ∀ x, v x ≠ 0) {x₀ : M} {γ : ℝ → M} {J : Set ℝ}
    (hmax : IsMaximalMIntegralCurveOn v x₀ γ J) (hinj : InjOn γ J) :
    Nonempty (ℝ ≃ₘ^∞⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ M) := by
  obtain ⟨ψ, -, -, hψinj, hψrange, hψlocal⟩ :=
    exists_contDiff_parametrization_of_isOpen_ordConnected hmax.1 hmax.2.1 ⟨0, hmax.2.2.1⟩
  have hψJ (t : ℝ) : ψ t ∈ J := hψrange ▸ mem_range_self t
  have hlocal : IsLocalDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (γ ∘ ψ) := fun t =>
    (hψlocal t).comp (K := 𝓘(ℝ, ℝ)) (P := M)
      (oneManifold_integralCurveOn_isLocalDiffeomorphAt hv hv0
      hmax.1 hmax.2.2.2.2.1 (ψ t) (hψJ t))
  have hsurj : Surjective (γ ∘ ψ) := by
    intro x
    obtain ⟨t, ht, htx⟩ : x ∈ γ '' J :=
      (hmax.image_eq_univ (hv.of_le (by simp)) hv0).symm ▸ mem_univ x
    rw [← hψrange] at ht
    obtain ⟨s, rfl⟩ := ht
    exact ⟨s, htx⟩
  exact ⟨hlocal.diffeomorphOfBijective
    ⟨fun s t hst => hψinj (hinj (hψJ s) (hψJ t) hst), hsurj⟩⟩

/-- `lem:one-manifold`: a connected Hausdorff smooth one-manifold equipped with
a smooth nowhere-zero tangent field is diffeomorphic to the real line or the
standard circle. No completeness hypothesis is required. -/
theorem oneManifold_diffeomorph_real_or_circle [ConnectedSpace M]
    (hv : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent ∞
      (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, ℝ) M)))
    (hv0 : ∀ x, v x ≠ 0) :
    Nonempty (ℝ ≃ₘ^∞⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ M) ∨
      Nonempty (Circle ≃ₘ^∞⟮𝓡 1, 𝓘(ℝ, ℝ)⟯ M) := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  obtain ⟨γ, J, hmax⟩ :=
    oneManifold_exists_isMaximalMIntegralCurveOn (hv.of_le (by simp)) x₀
  by_cases hinj : InjOn γ J
  · exact Or.inl (hmax.exists_diffeomorph_real hv hv0 hinj)
  · obtain ⟨-, hγ⟩ := hmax.eq_univ_of_not_injOn (hv.of_le (by simp)) hinj
    exact oneManifold_diffeomorph_real_or_circle_of_isMIntegralCurve hv hv0 hγ

end Classification

end LiquidDrop
