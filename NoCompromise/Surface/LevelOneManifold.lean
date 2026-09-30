module

public import NoCompromise.Surface.MergeDisjoint
public import Mathlib.Topology.Instances.AddCircle.Real

@[expose] public section

/-!
# `lem:one-manifold` for regular levels of a smooth function on an embedded surface

`blueprint/chapters/14-flows.tex`, `lem:one-manifold`, in the embedded form in which it is
applied: a connected component `C` of the regular part of a level set of a smooth function `h`
on a compact oriented embedded surface `S ⊆ ℝ³` is the image of a smooth integral curve `γ` of
the nowhere-zero tangent field `levelTangentField n h = n × ∇_Σ h`, and either `γ` is periodic
with least period `τ` and descends to a homeomorphism `ℝ/τℤ ≃ₜ C`, or `γ` is injective and is a
homeomorphism `ℝ ≃ₜ C`. Together with the smoothness of `γ` and `γ' ≠ 0` (a smooth immersion
onto the embedded curve `C`), this is the statement that `C` is diffeomorphic to `S¹` or `ℝ`.
-/

noncomputable section

open Set Filter Topology Function

namespace LiquidDrop

/-- The regular part of the level set `{h = c}` of `h` on `S`. -/
def regularLevel (S : Set E₃) (h : E₃ → ℝ) (c : ℝ) : Set E₃ :=
  {x | x ∈ S ∧ h x = c ∧ ¬ IsSurfaceCriticalPoint S h x}

/-- An integral curve, defined for all time, of a field which is smooth on a set containing the
curve is smooth. -/
theorem contDiff_of_hasDerivAt_of_contDiffOn {U : Set E₃} {X : E₃ → E₃}
    (hX : ContDiffOn ℝ (⊤ : ℕ∞) X U) {γ : ℝ → E₃} (hγU : ∀ t, γ t ∈ U)
    (hγ : ∀ t, HasDerivAt γ (X (γ t)) t) : ContDiff ℝ (⊤ : ℕ∞) γ := by
  have hd : deriv γ = X ∘ γ := funext fun t => (hγ t).deriv
  have hdiff : Differentiable ℝ γ := fun t => (hγ t).differentiableAt
  have key : ∀ k : ℕ, ContDiff ℝ k γ := by
    intro k
    induction k with
    | zero => exact contDiff_zero.mpr hdiff.continuous
    | succ k ih =>
      rw [Nat.cast_succ, contDiff_succ_iff_deriv]
      refine ⟨hdiff, fun h => absurd h (by simp), ?_⟩
      rw [hd]
      exact (hX.of_le (by exact_mod_cast le_top)).comp_contDiff ih hγU
  exact contDiff_infty.mpr key

/-- Two equal values of an integral curve of the rotated gradient on the surface make it
periodic. -/
theorem levelTangentField_curve_periodic {S : Set E₃} {n : E₃ → E₃}
    (hn : IsUnitNormalField S n) {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {γ : ℝ → E₃}
    (hγ : ∀ t, γ t ∈ S ∧ HasDerivAt γ (levelTangentField n h (γ t)) t) {s t : ℝ}
    (hst : γ s = γ t) : Periodic γ (t - s) := by
  intro x
  have := levelTangentField_curve_shift hn hh hγ hγ hst (x - s)
  rw [show s + (x - s) = x by ring, show t + (x - s) = x + (t - s) by ring] at this
  exact this.symm

/-- The integral curve of the rotated gradient through a point of the regular level
`regularLevel S h c` stays in it, its accumulation points in the regular level lie on it, and it
is locally an arc of the regular level. -/
theorem regularLevel_orbit_props {S : Set E₃} {n : E₃ → E₃} (hS : IsSmoothEmbeddedSurface S)
    (hSc : IsCompact S) (hn : IsUnitNormalField S n) {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {c : ℝ} {γ : ℝ → E₃} (hγ : ∀ t, γ t ∈ S ∧ HasDerivAt γ (levelTangentField n h (γ t)) t)
    (hγ0 : γ 0 ∈ regularLevel S h c) :
    (∀ t, γ t ∈ regularLevel S h c) ∧
      (∀ q ∈ regularLevel S h c, q ∈ closure (Set.range γ) → q ∈ Set.range γ) ∧
      (∀ t₀ : ℝ, ∀ ε > 0, ∃ V : Set E₃, IsOpen V ∧ γ t₀ ∈ V ∧
        ∀ y ∈ V ∩ regularLevel S h c, ∃ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε), γ t = y) := by
  have hh1 : ContDiff ℝ 1 h := hh.of_le (by simp)
  have hL : ∀ t, γ t ∈ regularLevel S h c := by
    intro t
    refine ⟨(hγ t).1, ?_, fun hcrit => ?_⟩
    · rw [height_levelTangentField_curve hh1 (fun s => (hγ s).2) t]
      exact hγ0.2.1
    · by_cases h0 : γ 0 = γ t
      · exact hγ0.2.2 (h0 ▸ hcrit)
      · exact levelTangentField_curve_ne hS hn hh hγ hcrit h0 t rfl
  have hshift : ∀ t₀ : ℝ, ∀ u, (fun v => γ (t₀ + v)) u ∈ S ∧
      HasDerivAt (fun v => γ (t₀ + v)) (levelTangentField n h ((fun v => γ (t₀ + v)) u)) u := by
    intro t₀ u
    refine ⟨(hγ (t₀ + u)).1, ?_⟩
    have := (hγ (t₀ + u)).2.scomp u ((hasDerivAt_id' u).const_add t₀)
    simpa [Function.comp_def] using this
  refine ⟨hL, ?_, ?_⟩
  · intro q hq hqc
    obtain ⟨δ, hδ0, hδ⟩ := exists_levelTangentField_curve hS hSc hn hh hq.1
    obtain ⟨V, hV, hqV, hVL⟩ :=
      levelSet_subset_integralCurve hS hn hh hq.1 hq.2.2 hδ0 hδ one_pos
    obtain ⟨_, hyV, ⟨t, rfl⟩⟩ := mem_closure_iff.mp hqc V hV hqV
    obtain ⟨s, -, hs⟩ := hVL (γ t) ⟨hyV, (hγ t).1⟩ ((hL t).2.1.trans hq.2.1.symm)
    exact ⟨t + -s, by rw [levelTangentField_curve_shift hn hh hγ hδ hs.symm (-s), add_neg_cancel,
      hδ0]⟩
  · intro t₀ ε hε
    obtain ⟨V, hV, hqV, hVL⟩ := levelSet_subset_integralCurve hS hn hh (hγ t₀).1
      (hL t₀).2.2 (γ := fun v => γ (t₀ + v)) (by simp) (hshift t₀) hε
    refine ⟨V, hV, hqV, fun y hy => ?_⟩
    obtain ⟨t, ht, hty⟩ := hVL y ⟨hy.1, hy.2.1⟩ (by rw [hy.2.2.1]; exact ((hL t₀).2.1).symm)
    exact ⟨t₀ + t, ⟨by linarith [ht.1], by linarith [ht.2]⟩, hty⟩

/-- `lem:one-manifold` for regular levels on an embedded surface: a connected component `C` of
the regular part of a level set of a smooth function on a compact oriented embedded surface is
the image of a smooth integral curve `γ` of the nowhere-zero field `n × ∇_Σ h`, with `γ' ≠ 0`,
and either `γ` is periodic with least period `τ`, `C` is compact and `γ` descends to a
homeomorphism `ℝ/τℤ ≃ₜ C` (`C ≅ S¹`), or `γ` is injective, `C` is not compact and `γ` is a
homeomorphism `ℝ ≃ₜ C` (`C ≅ ℝ`). -/
theorem levelComponent_diffeo_circle_or_real {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hSc : IsCompact S) (hn : IsUnitNormalField S n)
    {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {c : ℝ} {x₀ : E₃}
    (hx₀ : x₀ ∈ regularLevel S h c) :
    ∃ γ : ℝ → E₃, γ 0 = x₀ ∧ ContDiff ℝ (⊤ : ℕ∞) γ ∧
      (∀ t, HasDerivAt γ (levelTangentField n h (γ t)) t) ∧ (∀ t, deriv γ t ≠ 0) ∧
      Set.range γ = connectedComponentIn (regularLevel S h c) x₀ ∧
      ((∃ τ > 0, Function.Periodic γ τ ∧ Set.InjOn γ (Set.Ico 0 τ) ∧
          IsCompact (connectedComponentIn (regularLevel S h c) x₀) ∧
          ∃ e : AddCircle τ ≃ₜ connectedComponentIn (regularLevel S h c) x₀,
            ∀ t : ℝ, (e (t : AddCircle τ) : E₃) = γ t) ∨
        (Function.Injective γ ∧ ¬ IsCompact (connectedComponentIn (regularLevel S h c) x₀) ∧
          ∃ e : ℝ ≃ₜ connectedComponentIn (regularLevel S h c) x₀,
            ∀ t : ℝ, (e t : E₃) = γ t)) := by
  set L := regularLevel S h c with hLdef
  set C := connectedComponentIn L x₀ with hCdef
  obtain ⟨γ, hγ0, hγ⟩ := exists_levelTangentField_curve hS hSc hn hh hx₀.1
  obtain ⟨hL, hclosed, harc⟩ := regularLevel_orbit_props hS hSc hn hh hγ (hγ0 ▸ hx₀)
  have hγc : Continuous γ := continuous_iff_continuousAt.mpr fun t => (hγ t).2.continuousAt
  obtain ⟨U, -, hSU, hnU⟩ := hn.1
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) γ :=
    contDiff_of_hasDerivAt_of_contDiffOn (contDiffOn_levelTangentField hnU hh)
      (fun t => hSU (hγ t).1) (fun t => (hγ t).2)
  have hX0 : ∀ t, levelTangentField n h (γ t) ≠ 0 := fun t h0 =>
    (hL t).2.2 ((levelTangentField_eq_zero_iff hS hn (hγ t).1).mp h0)
  have hder : ∀ t, deriv γ t ≠ 0 := fun t => by
    rw [(hγ t).2.deriv]
    exact hX0 t
  -- the orbit is the whole component
  have hrange : Set.range γ = C := by
    apply Subset.antisymm
    · exact (isPreconnected_range hγc).subset_connectedComponentIn ⟨0, hγ0⟩
        (range_subset_iff.mpr hL)
    · obtain ⟨p, hp⟩ : ∃ p, p ∉ S := by
        by_contra hcon
        exact noncompact_univ E₃ (by
          rwa [eq_univ_of_forall fun x => not_not.mp fun hx => hcon ⟨x, hx⟩] at hSc)
      exact subset_range_of_local_arc (L := L) (p := p) (fun q hq _ hqc => hclosed q hq hqc)
        harc isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _)
        (fun hpC => hp (connectedComponentIn_subset _ _ hpC).1)
        (hγ0 ▸ mem_connectedComponentIn hx₀)
  refine ⟨γ, hγ0, hsmooth, fun t => (hγ t).2, hder, hrange, ?_⟩
  have hmemC : ∀ t, γ t ∈ C := fun t => hrange ▸ mem_range_self t
  by_cases hinj : Function.Injective γ
  · -- the injective case: `C ≃ₜ ℝ`
    right
    let F : ℝ → C := fun t => ⟨γ t, hmemC t⟩
    have hFc : Continuous F := hγc.subtype_mk _
    have hFinj : Injective F := fun a b hab => hinj (congrArg Subtype.val hab)
    have hFsurj : Surjective F := by
      rintro ⟨y, hy⟩
      rw [← hrange] at hy
      obtain ⟨t, rfl⟩ := hy
      exact ⟨t, rfl⟩
    have hFopen : IsOpenMap F := by
      intro W hW
      rw [isOpen_iff_forall_mem_open]
      rintro _ ⟨t, htW, rfl⟩
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hW t htW
      obtain ⟨V, hV, htV, hVL⟩ := harc t ε hε
      refine ⟨Subtype.val ⁻¹' V, ?_, hV.preimage continuous_subtype_val, htV⟩
      rintro ⟨y, hyC⟩ hyV
      obtain ⟨s, hs, hsy⟩ := hVL y ⟨hyV, connectedComponentIn_subset _ _ hyC⟩
      refine ⟨s, hball ?_, Subtype.ext hsy⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hs.1, hs.2]
    let e : ℝ ≃ₜ C :=
      (Equiv.ofBijective F ⟨hFinj, hFsurj⟩).toHomeomorphOfContinuousOpen hFc hFopen
    refine ⟨hinj, fun hCc => ?_, e, fun t => rfl⟩
    have := isCompact_iff_compactSpace.mp hCc
    have : CompactSpace ℝ := e.symm.compactSpace
    exact noncompact_univ ℝ isCompact_univ
  · -- the periodic case: `C ≃ₜ ℝ/τℤ`
    left
    obtain ⟨a, b, hab, hab'⟩ : ∃ a b, γ a = γ b ∧ a ≠ b := by
      simp only [Injective, not_forall] at hinj
      obtain ⟨a, b, h1, h2⟩ := hinj
      exact ⟨a, b, h1, h2⟩
    have hper : ∀ {s t : ℝ}, γ s = γ t → Periodic γ (t - s) := fun hst =>
      levelTangentField_curve_periodic hn hh hγ hst
    -- no small periods
    obtain ⟨δ, hδ, hδne⟩ := Metric.eventually_nhds_iff.mp
      (eventually_nhdsWithin_iff.mp ((hγ 0).2.eventually_ne (c := γ 0) (hX0 0)))
    have hsmall : ∀ T, 0 < T → Periodic γ T → δ ≤ T := by
      intro T hT hTp
      by_contra hlt
      rw [not_le] at hlt
      have := hδne (show dist T 0 < δ by rw [Real.dist_eq, sub_zero, abs_of_pos hT]; exact hlt)
        (ne_of_gt hT)
      exact this (by simpa using hTp 0)
    set Q := {T : ℝ | δ ≤ T ∧ Periodic γ T} with hQ
    have hQc : IsClosed Q := by
      have : Q = Ici δ ∩ ⋂ x : ℝ, {T | γ (x + T) = γ x} := by
        ext T
        simp [hQ, Periodic]
      rw [this]
      exact isClosed_Ici.inter (isClosed_iInter fun x =>
        isClosed_eq (hγc.comp (continuous_const.add continuous_id)) continuous_const)
    have hQne : Q.Nonempty := by
      rcases lt_or_gt_of_ne hab' with h1 | h1
      · exact ⟨b - a, hsmall _ (sub_pos.mpr h1) (hper hab), hper hab⟩
      · exact ⟨a - b, hsmall _ (sub_pos.mpr h1) (hper hab.symm), hper hab.symm⟩
    have hQb : BddBelow Q := ⟨δ, fun T hT => hT.1⟩
    set τ := sInf Q with hτdef
    have hτQ : τ ∈ Q := hQc.csInf_mem hQne hQb
    have hτ : 0 < τ := lt_of_lt_of_le hδ hτQ.1
    have hτmin : ∀ T, 0 < T → Periodic γ T → τ ≤ T := fun T hT hTp =>
      csInf_le hQb ⟨hsmall T hT hTp, hTp⟩
    have hmult : ∀ T, Periodic γ T → ∃ k : ℤ, T = k • τ := by
      intro T hT
      have hr := toIcoMod_mem_Ico hτ 0 T
      have hrp : Periodic γ (toIcoMod hτ 0 T) := by
        rw [← self_sub_toIcoDiv_zsmul]
        exact hT.sub_period (hτQ.2.zsmul _)
      refine ⟨toIcoDiv hτ 0 T, ?_⟩
      have hr0 : toIcoMod hτ 0 T = 0 := by
        by_contra hne
        have := hτmin _ (lt_of_le_of_ne hr.1 (Ne.symm hne)) hrp
        linarith [hr.2]
      rw [← self_sub_toIcoDiv_zsmul] at hr0
      exact sub_eq_zero.mp hr0
    have hinjIco : InjOn γ (Ico 0 τ) := by
      intro s hs t ht hst
      by_contra hne
      rcases lt_or_gt_of_ne hne with h1 | h1
      · have := hτmin (t - s) (sub_pos.mpr h1) (hper hst)
        linarith [ht.2, hs.1]
      · have := hτmin (s - t) (sub_pos.mpr h1) (hper hst.symm)
        linarith [hs.2, ht.1]
    have hCc : IsCompact C := hrange ▸ hτQ.2.compact_of_continuous hτ.ne' hγc
    have : Fact (0 < τ) := ⟨hτ⟩
    have hmemL : ∀ x : AddCircle τ, hτQ.2.lift x ∈ C := by
      intro x
      induction x using QuotientAddGroup.induction_on with
      | H t => exact hmemC t
    let F : AddCircle τ → C := fun x => ⟨hτQ.2.lift x, hmemL x⟩
    have hlc : Continuous (hτQ.2.lift : AddCircle τ → E₃) :=
      (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.mpr hγc
    have hFc : Continuous F := hlc.subtype_mk _
    have hFinj : Injective F := by
      intro x y hxy
      induction x using QuotientAddGroup.induction_on with | H s => ?_
      induction y using QuotientAddGroup.induction_on with | H t => ?_
      have hst : γ s = γ t := congrArg Subtype.val hxy
      obtain ⟨k, hk⟩ := hmult _ (hper hst.symm)
      exact QuotientAddGroup.eq_iff_sub_mem.mpr (AddSubgroup.mem_zmultiples_iff.mpr ⟨k, hk.symm⟩)
    have hFsurj : Surjective F := by
      rintro ⟨y, hy⟩
      rw [← hrange] at hy
      obtain ⟨t, rfl⟩ := hy
      exact ⟨(t : AddCircle τ), rfl⟩
    exact ⟨τ, hτ, hτQ.2, hinjIco, hCc,
      Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F ⟨hFinj, hFsurj⟩) hFc,
      fun t => rfl⟩

end LiquidDrop
