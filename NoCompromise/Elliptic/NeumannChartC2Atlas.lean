import NoCompromise.Elliptic.NeumannChartC2AmbientHolder
import NoCompromise.Elliptic.BoundaryNeumannRecentre
import NoCompromise.Elliptic.NeumannInteriorSmooth

/-!
# Uniform C²,α bounds on a boundary layer over a finite atlas (`thm:boundary-neumann`)

For a bounded open set with smooth boundary, a weak Neumann solution with smooth data, and
`0 < α < 1`, the local ambient C²,α statements at the boundary points
(`IsWeakNeumannSolution.exists_boundary_c2_holder`) are combined over a finite subcover of the
compact boundary. Continuous representatives agree on overlaps, and a Lebesgue-number argument
gives one representative whose second derivatives are bounded and α-Hölder on the whole
boundary layer `D ∩ V`, `V ⊇ ∂D` open, with one constant.
-/

noncomputable section

open Set Filter Metric InnerProductSpace MeasureTheory
open scoped Topology Gradient NNReal

namespace LiquidDrop

set_option maxSynthPendingDepth 8

/-- Coordinate second derivatives are the entries of the second Fréchet derivative. -/
lemma neumannAtlas_entry_eq {v : AmbientSpace → ℝ} {U : Set AmbientSpace} (hU : IsOpen U)
    (hv : ContDiffOn ℝ 2 v U) {x : AmbientSpace} (hx : x ∈ U) (i j : Fin 3) :
    boundaryNeumannC2Entry v x i j =
      fderiv ℝ (fderiv ℝ v) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  have hc : ContDiffAt ℝ 2 v x := hv.contDiffAt (hU.mem_nhds hx)
  have hPd : DifferentiableAt ℝ (fderiv ℝ v) x :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  unfold boundaryNeumannC2Entry
  rw [fderiv_clm_apply (c := fderiv ℝ v) (u := fun _ => EuclideanSpace.single j 1) hPd
    (differentiableAt_const _)]
  simp

/-- A finite Hölder norm of the Hessian bounds every coordinate entry and its Hölder quotient. -/
lemma neumannAtlas_entry_bounds {α : ℝ} {v : AmbientSpace → ℝ} {U : Set AmbientSpace}
    (hU : IsOpen U) (hv : ContDiffOn ℝ 2 v U)
    {Q : AmbientSpace → AmbientSpace →L[ℝ] AmbientSpace →L[ℝ] ℝ}
    (hQ : EqOn Q (fderiv ℝ (fderiv ℝ v)) U) (hH : HasFiniteHolderNormOn α Q U) (i j : Fin 3) :
    (∀ x ∈ U, |boundaryNeumannC2Entry v x i j| ≤ holderNorm α Q U) ∧
      ∀ x ∈ U, ∀ y ∈ U, |boundaryNeumannC2Entry v x i j - boundaryNeumannC2Entry v y i j| ≤
        holderNorm α Q U * dist x y ^ α := by
  have hn : ∀ (T : AmbientSpace →L[ℝ] AmbientSpace →L[ℝ] ℝ),
      |T (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ ‖T‖ := by
    intro T
    have h1 := (T (EuclideanSpace.single i 1)).le_opNorm (EuclideanSpace.single j 1)
    have h2 := T.le_opNorm (EuclideanSpace.single i 1)
    simp only [PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs] at h1 h2
    exact h1.trans h2
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · rw [neumannAtlas_entry_eq hU hv hx, ← hQ hx]
    exact (hn _).trans (hH.nondiv_norm_le hx)
  · rw [neumannAtlas_entry_eq hU hv hx, neumannAtlas_entry_eq hU hv hy, ← hQ hx, ← hQ hy]
    have := hn (Q x - Q y)
    simp only [sub_apply] at this
    refine this.trans ((hH.nondiv_norm_sub_le hx hy).trans ?_)
    rw [dist_eq_norm]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg _) _)
    exact le_add_of_nonneg_left (holderUniformNorm_nonneg hH.uniform_bounded)

/-- **Uniform C²,α on a boundary layer over a finite atlas.** For a bounded open set with smooth
boundary, a weak Neumann solution with smooth volume and boundary data, and `0 < α < 1`, there
are an open `V ⊇ ∂D` and one representative `v` of `z` on `D ∩ V`, C² there, whose coordinate
second derivatives are bounded and α-Hölder on all of `D ∩ V` with one constant. The constant
comes from finitely many smooth charts covering the compact boundary. -/
theorem IsWeakNeumannSolution.exists_boundary_layer_c2_holder
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {D : Set AmbientSpace} {hD : IsOpen D} {hbD : Bornology.IsBounded D}
    {hL : HasLipschitzBoundary D} {f : Lp ℝ 2 (volume.restrict D)}
    {h : Lp ℝ 2 ((hausdorffMeasure2 3).restrict (frontier D))} {z : H1Space D}
    (hz : IsWeakNeumannSolution hD hbD hL f h z) (hGs : HasSmoothBoundary D)
    {f₀ h₀ : AmbientSpace → ℝ} (hf : ⇑f =ᵐ[volume.restrict D] f₀)
    (hh : ⇑h =ᵐ[(hausdorffMeasure2 3).restrict (frontier D)] h₀)
    (hfs : ContDiff ℝ (⊤ : ℕ∞) f₀) (hhs : ContDiff ℝ (⊤ : ℕ∞) h₀) :
    ∃ (V : Set AmbientSpace) (v : AmbientSpace → ℝ) (C : ℝ),
      IsOpen V ∧ frontier D ⊆ V ∧ ContDiffOn ℝ 2 v (D ∩ V) ∧
      ⇑z =ᵐ[volume.restrict (D ∩ V)] v ∧
      ∀ i j : Fin 3,
        (∀ x ∈ D ∩ V, |boundaryNeumannC2Entry v x i j| ≤ C) ∧
        ∀ x ∈ D ∩ V, ∀ y ∈ D ∩ V,
          |boundaryNeumannC2Entry v x i j - boundaryNeumannC2Entry v y i j| ≤
            C * dist x y ^ α := by
  -- local data at every boundary point, on a ball of radius `2 r`
  have hloc : ∀ p : AmbientSpace, ∃ (r : ℝ) (w : AmbientSpace → ℝ) (B : ℝ),
      p ∈ frontier D → 0 < r ∧ 0 ≤ B ∧ ContDiffOn ℝ 2 w (D ∩ ball p (2 * r)) ∧
        ⇑z =ᵐ[volume.restrict (D ∩ ball p (2 * r))] w ∧
        ∀ i j : Fin 3, (∀ x ∈ D ∩ ball p (2 * r), |boundaryNeumannC2Entry w x i j| ≤ B) ∧
          ∀ x ∈ D ∩ ball p (2 * r), ∀ y ∈ D ∩ ball p (2 * r),
            |boundaryNeumannC2Entry w x i j - boundaryNeumannC2Entry w y i j| ≤
              B * dist x y ^ α := by
    intro p
    by_cases hp : p ∈ frontier D
    · obtain ⟨V, w, hV, hpV, -, hw2, hzw, ⟨Q, -, hQe, hQh⟩, -⟩ :=
        hz.exists_boundary_c2_holder hα hα1 hGs hf hh hfs hhs hp
      obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.mp hV p hpV
      have hsub : D ∩ ball p (2 * (δ / 2)) ⊆ D ∩ V := fun x hx =>
        ⟨hx.1, hδV (by rw [show 2 * (δ / 2) = δ by ring] at hx; exact hx.2)⟩
      have hU : IsOpen (D ∩ ball p (2 * (δ / 2))) := hD.inter isOpen_ball
      have hw2' := hw2.mono hsub
      obtain ⟨hQh', -⟩ := schauder_holder_mono hQh hsub
      refine ⟨δ / 2, w, holderNorm α Q (D ∩ ball p (2 * (δ / 2))), fun _ => ⟨by positivity,
        hQh'.norm_nonneg, hw2', ae_restrict_of_ae_restrict_of_subset hsub hzw, fun i j => ?_⟩⟩
      exact neumannAtlas_entry_bounds hU hw2' (hQe.mono hsub) hQh' i j
    · exact ⟨1, 0, 0, fun h => absurd h hp⟩
  choose r w B hrwB using hloc
  -- a finite subcover of the compact boundary
  have hK : IsCompact (frontier D) :=
    hbD.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover (fun p => ball p (r p))
    (fun p hp => ball_mem_nhds p (hrwB p hp).1)
  obtain ⟨ρ, hρ, hρr⟩ : ∃ ρ > 0, ∀ p ∈ t, ρ ≤ r p := by
    rcases t.eq_empty_or_nonempty with ht | ht
    · exact ⟨1, one_pos, by simp [ht]⟩
    · obtain ⟨q, hq, hmin⟩ := t.exists_min_image r ht
      exact ⟨r q, (hrwB q (htK q hq)).1, hmin⟩
  set Cb : ℝ := ∑ p ∈ t, B p with hCb_def
  have hBC : ∀ p ∈ t, B p ≤ Cb := fun p hp =>
    Finset.single_le_sum (fun q hq => (hrwB q (htK q hq)).2.1) hp
  have hCb : 0 ≤ Cb := Finset.sum_nonneg fun q hq => (hrwB q (htK q hq)).2.1
  set V : Set AmbientSpace := ⋃ p ∈ t, ball p (r p) with hV_def
  have hVo : IsOpen V := isOpen_biUnion fun p _ => isOpen_ball
  set Lr := D ∩ V with hLr_def
  have hLo : IsOpen Lr := hD.inter hVo
  -- a chart centre for every point of the layer
  have hctr : ∀ x ∈ Lr, ∃ p ∈ t, x ∈ ball p (r p) := by
    intro x hx
    have := hx.2
    simp only [hV_def, mem_iUnion] at this
    obtain ⟨p, hp, hxp⟩ := this
    exact ⟨p, hp, hxp⟩
  classical
  set ctr : AmbientSpace → AmbientSpace := fun x =>
    if hx : x ∈ Lr then Classical.choose (hctr x hx) else x with hctr_def
  have hctr_spec : ∀ x ∈ Lr, ctr x ∈ t ∧ x ∈ ball (ctr x) (r (ctr x)) := by
    intro x hx
    have := Classical.choose_spec (hctr x hx)
    have hc : ctr x = Classical.choose (hctr x hx) := by
      simp only [hctr_def, dite_eq_left hx]
    rw [hc]
    exact this
  set P : AmbientSpace → Set AmbientSpace := fun x => D ∩ ball (ctr x) (2 * r (ctr x))
  set u : AmbientSpace → AmbientSpace → ℝ := fun x => w (ctr x)
  have hdata : ∀ x ∈ Lr, 0 < r (ctr x) ∧ 0 ≤ B (ctr x) ∧
      ContDiffOn ℝ 2 (u x) (P x) ∧ ⇑z =ᵐ[volume.restrict (P x)] u x ∧
      ∀ i j : Fin 3, (∀ y ∈ P x, |boundaryNeumannC2Entry (u x) y i j| ≤ B (ctr x)) ∧
        ∀ y ∈ P x, ∀ y' ∈ P x,
          |boundaryNeumannC2Entry (u x) y i j - boundaryNeumannC2Entry (u x) y' i j| ≤
            B (ctr x) * dist y y' ^ α := fun x hx =>
    hrwB (ctr x) (htK _ (hctr_spec x hx).1)
  obtain ⟨v, hv2, hzv, hvent⟩ := boundary_neumann_layer_glue hα hρ hCb hLo P u
    (fun x _ => hD.inter isOpen_ball)
    (fun x hx y hy hxy => by
      refine ⟨hy.1, ?_⟩
      have h1 := (hctr_spec x hx).2
      have h2 := hρr _ (hctr_spec x hx).1
      rw [mem_ball] at h1 ⊢
      have := dist_triangle y x (ctr x)
      rw [dist_comm] at hxy
      linarith)
    (fun x hx => (hdata x hx).2.2.1) (fun x hx => (hdata x hx).2.2.2.1)
    (fun x hx i j y hy => ((hdata x hx).2.2.2.2 i j).1 y hy |>.trans
      (hBC _ (hctr_spec x hx).1))
    (fun x hx i j y hy y' hy' => (((hdata x hx).2.2.2.2 i j).2 y hy y' hy').trans
      (mul_le_mul_of_nonneg_right (hBC _ (hctr_spec x hx).1)
        (Real.rpow_nonneg dist_nonneg α)))
  refine ⟨V, v, 2 * Cb * ρ⁻¹ ^ α + Cb, hVo, hcov, hv2, hzv.symm.symm, fun i j =>
    ⟨fun x hx => ((hvent i j).1 x hx).trans ?_, (hvent i j).2⟩⟩
  have : 0 ≤ 2 * Cb * ρ⁻¹ ^ α := by positivity
  linarith

/-- Coordinate second derivatives of a C³ function are C¹. -/
lemma neumannAtlas_entry_contDiffOn {v : AmbientSpace → ℝ} {U : Set AmbientSpace}
    (hU : IsOpen U) (hv : ContDiffOn ℝ 3 v U) (i j : Fin 3) :
    ContDiffOn ℝ 1 (fun y => boundaryNeumannC2Entry v y i j) U := by
  have h1 : ContDiffOn ℝ 2 (fderiv ℝ v) U := hv.fderiv_of_isOpen hU (by norm_num)
  have h2 : ContDiffOn ℝ 2 (fun y => fderiv ℝ v y (EuclideanSpace.single j 1)) U :=
    h1.clm_apply contDiffOn_const
  have h3 : ContDiffOn ℝ 1 (fderiv ℝ (fun y => fderiv ℝ v y (EuclideanSpace.single j 1))) U :=
    h2.fderiv_of_isOpen hU (by norm_num)
  exact h3.clm_apply contDiffOn_const

/-- **C²,α up to the boundary on the whole domain, constant forcing.** For a bounded open set with
smooth boundary, a weak Neumann solution with constant volume datum and smooth boundary datum,
and `0 < α < 1`, one representative of `z` is C² on `D` with coordinate second derivatives
bounded and α-Hölder on all of `D`, with one constant (the boundary layer over a finite atlas
together with finitely many interior balls). -/
theorem IsWeakNeumannSolution.exists_c2_holder_const_forcing
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {D : Set AmbientSpace} {hD : IsOpen D} {hbD : Bornology.IsBounded D}
    {hL : HasLipschitzBoundary D} {f : Lp ℝ 2 (volume.restrict D)}
    {h : Lp ℝ 2 ((hausdorffMeasure2 3).restrict (frontier D))} {z : H1Space D}
    (hz : IsWeakNeumannSolution hD hbD hL f h z) (hGs : HasSmoothBoundary D)
    {c : ℝ} (hf : ⇑f =ᵐ[volume.restrict D] fun _ => c)
    {h₀ : AmbientSpace → ℝ}
    (hh : ⇑h =ᵐ[(hausdorffMeasure2 3).restrict (frontier D)] h₀)
    (hhs : ContDiff ℝ (⊤ : ℕ∞) h₀) :
    ∃ (v : AmbientSpace → ℝ) (C : ℝ), ContDiffOn ℝ 2 v D ∧ ⇑z =ᵐ[volume.restrict D] v ∧
      ∀ i j : Fin 3, (∀ x ∈ D, |boundaryNeumannC2Entry v x i j| ≤ C) ∧
        ∀ x ∈ D, ∀ y ∈ D,
          |boundaryNeumannC2Entry v x i j - boundaryNeumannC2Entry v y i j| ≤
            C * dist x y ^ α := by
  classical
  obtain ⟨V, vL, CL, hVo, hfV, hvL2, hzvL, hvLent⟩ :=
    hz.exists_boundary_layer_c2_holder hα hα1 hGs hf hh contDiff_const hhs
  obtain ⟨vI, hvI, hzvI, -, -⟩ := hz.exists_smooth_interior_representative hf
  have hvI3 : ContDiffOn ℝ 3 vI D := hvI.of_le (by simp : (3 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞))
  have hKb : IsCompact (frontier D) :=
    hbD.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨δ, hδ, hδV⟩ := hKb.exists_thickening_subset_open hVo hfV
  set ε : ℝ := δ / 2 with hε_def
  have hε : 0 < ε := by positivity
  set K := closure D \ Metric.thickening ε (frontier D) with hK_def
  have hKc : IsCompact K := hbD.isCompact_closure.diff Metric.isOpen_thickening
  have hKD : K ⊆ D := by
    intro x hx
    have hxf : x ∉ frontier D := fun hf' => hx.2 (Metric.self_subset_thickening hε _ hf')
    by_contra hxD
    exact hxf ⟨hx.1, by rwa [hD.interior_eq]⟩
  obtain ⟨η₀, hη₀, hη₀D⟩ := hKc.exists_thickening_subset_open hD hKD
  set η : ℝ := η₀ / 3 with hη_def
  have hη : 0 < η := by positivity
  obtain ⟨t, htK, htcov⟩ := hKc.elim_nhds_subcover (fun p => ball p η)
    (fun p _ => ball_mem_nhds p hη)
  have hballD : ∀ p ∈ K, closedBall p (2 * η) ⊆ D := by
    intro p hp y hy
    refine hη₀D (Metric.mem_thickening_iff.mpr ⟨p, hp, ?_⟩)
    have := mem_closedBall.mp hy
    linarith
  -- Hölder bounds of the interior entries on each closed ball
  have hHI : ∀ p ∈ t, ∀ i j : Fin 3, HasFiniteHolderNormOn α
      (fun y => boundaryNeumannC2Entry vI y i j) (closedBall p (2 * η)) := fun p hp i j =>
    boundary_neumann_c2_inhom_finiteHolder_of_contDiffOn hα.le hα1.le
      (isCompact_closedBall p _) (convex_closedBall p _) hD (hballD p (htK p hp))
      (neumannAtlas_entry_contDiffOn hD hvI3 i j)
  set CI : ℝ := ∑ p ∈ t, ∑ i : Fin 3, ∑ j : Fin 3,
    holderNorm α (fun y => boundaryNeumannC2Entry vI y i j) (closedBall p (2 * η)) with hCI_def
  have hCIle : ∀ p ∈ t, ∀ i j : Fin 3,
      holderNorm α (fun y => boundaryNeumannC2Entry vI y i j) (closedBall p (2 * η)) ≤ CI := by
    intro p hp i j
    have hnn : ∀ q ∈ t, ∀ i j : Fin 3, 0 ≤
        holderNorm α (fun y => boundaryNeumannC2Entry vI y i j) (closedBall q (2 * η)) :=
      fun q hq i j => (hHI q hq i j).norm_nonneg
    calc holderNorm α (fun y => boundaryNeumannC2Entry vI y i j) (closedBall p (2 * η))
        ≤ ∑ j' : Fin 3, holderNorm α (fun y => boundaryNeumannC2Entry vI y i j')
            (closedBall p (2 * η)) :=
          Finset.single_le_sum (f := fun j' => holderNorm α
            (fun y => boundaryNeumannC2Entry vI y i j') (closedBall p (2 * η)))
            (fun j' _ => hnn p hp i j') (Finset.mem_univ j)
      _ ≤ ∑ i' : Fin 3, ∑ j' : Fin 3, holderNorm α (fun y => boundaryNeumannC2Entry vI y i' j')
            (closedBall p (2 * η)) :=
          Finset.single_le_sum (f := fun i' => ∑ j' : Fin 3, holderNorm α
            (fun y => boundaryNeumannC2Entry vI y i' j') (closedBall p (2 * η)))
            (fun i' _ => Finset.sum_nonneg fun j' _ => hnn p hp i' j') (Finset.mem_univ i)
      _ ≤ CI :=
          Finset.single_le_sum (f := fun q => ∑ i' : Fin 3, ∑ j' : Fin 3, holderNorm α
            (fun y => boundaryNeumannC2Entry vI y i' j') (closedBall q (2 * η)))
            (fun q hq => Finset.sum_nonneg fun i' _ => Finset.sum_nonneg fun j' _ =>
              hnn q hq i' j') hp
  have hCI : 0 ≤ CI := Finset.sum_nonneg fun q hq => Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => (hHI q hq i j).norm_nonneg
  set Cb : ℝ := max CL 0 + CI with hCb_def
  have hCb : 0 ≤ Cb := by positivity
  have hCLb : CL ≤ Cb := by have := le_max_left CL 0; linarith
  have hCIb : CI ≤ Cb := by have := le_max_right CL 0; linarith
  -- centres for points away from the boundary
  have hctr : ∀ x ∈ D, x ∉ Metric.thickening ε (frontier D) → ∃ p ∈ t, x ∈ ball p η := by
    intro x hx hxt
    have hxK : x ∈ K := ⟨subset_closure hx, hxt⟩
    have := htcov hxK
    simp only [mem_iUnion] at this
    obtain ⟨p, hp, hxp⟩ := this
    exact ⟨p, hp, hxp⟩
  set ctr : AmbientSpace → AmbientSpace := fun x =>
    if hx : x ∈ D ∧ x ∉ Metric.thickening ε (frontier D) then
      Classical.choose (hctr x hx.1 hx.2) else x with hctr_def
  have hctr_spec : ∀ x ∈ D, x ∉ Metric.thickening ε (frontier D) →
      ctr x ∈ t ∧ x ∈ ball (ctr x) η := by
    intro x hx hxt
    have := Classical.choose_spec (hctr x hx hxt)
    have hc : ctr x = Classical.choose (hctr x hx hxt) := by
      simp only [hctr_def, dite_eq_left (show x ∈ D ∧ x ∉ Metric.thickening ε (frontier D)
        from ⟨hx, hxt⟩)]
    rw [hc]
    exact this
  set P : AmbientSpace → Set AmbientSpace := fun x =>
    if x ∈ Metric.thickening ε (frontier D) then D ∩ V else ball (ctr x) (2 * η) with hP_def
  set u : AmbientSpace → AmbientSpace → ℝ := fun x =>
    if x ∈ Metric.thickening ε (frontier D) then vL else vI with hu_def
  set ρ : ℝ := min ε η with hρ_def
  have hρ : 0 < ρ := lt_min hε hη
  have hspec : ∀ x ∈ D, IsOpen (P x) ∧ (∀ y ∈ D, dist x y < ρ → y ∈ P x) ∧
      ContDiffOn ℝ 2 (u x) (P x) ∧ ⇑z =ᵐ[volume.restrict (P x)] u x ∧
      ∀ i j : Fin 3, (∀ y ∈ P x, |boundaryNeumannC2Entry (u x) y i j| ≤ Cb) ∧
        ∀ y ∈ P x, ∀ y' ∈ P x,
          |boundaryNeumannC2Entry (u x) y i j - boundaryNeumannC2Entry (u x) y' i j| ≤
            Cb * dist y y' ^ α := by
    intro x hx
    by_cases hxt : x ∈ Metric.thickening ε (frontier D)
    · have hPx : P x = D ∩ V := by simp only [hP_def, ite_eq_left hxt]
      have hux : u x = vL := by simp only [hu_def, ite_eq_left hxt]
      rw [hPx, hux]
      refine ⟨hD.inter hVo, fun y hy hxy => ⟨hy, hδV ?_⟩, hvL2, hzvL, fun i j =>
        ⟨fun y hy => ((hvLent i j).1 y hy).trans hCLb, fun y hy y' hy' =>
          ((hvLent i j).2 y hy y' hy').trans (mul_le_mul_of_nonneg_right hCLb
            (Real.rpow_nonneg dist_nonneg α))⟩⟩
      obtain ⟨q, hq, hxq⟩ := Metric.mem_thickening_iff.mp hxt
      refine Metric.mem_thickening_iff.mpr ⟨q, hq, ?_⟩
      have h1 := dist_triangle y x q
      have h2 : ρ ≤ ε := min_le_left _ _
      rw [dist_comm] at hxy
      linarith
    · have hPx : P x = ball (ctr x) (2 * η) := by simp only [hP_def, ite_eq_right hxt]
      have hux : u x = vI := by simp only [hu_def, ite_eq_right hxt]
      obtain ⟨hct, hxc⟩ := hctr_spec x hx hxt
      have hbD' : ball (ctr x) (2 * η) ⊆ D :=
        ball_subset_closedBall.trans (hballD _ (htK _ hct))
      rw [hPx, hux]
      refine ⟨isOpen_ball, fun y hy hxy => ?_, (hvI3.of_le (by norm_num)).mono hbD',
        ae_restrict_of_ae_restrict_of_subset hbD' hzvI, fun i j => ⟨?_, ?_⟩⟩
      · rw [mem_ball] at hxc ⊢
        have h1 := dist_triangle y x (ctr x)
        have h2 : ρ ≤ η := min_le_right _ _
        rw [dist_comm] at hxy
        linarith
      · intro y hy
        have := (hHI _ hct i j).nondiv_norm_le (ball_subset_closedBall hy)
        rw [Real.norm_eq_abs] at this
        exact this.trans ((hCIle _ hct i j).trans hCIb)
      · intro y hy y' hy'
        have h1 := (hHI _ hct i j).nondiv_norm_sub_le (ball_subset_closedBall hy)
          (ball_subset_closedBall hy')
        rw [Real.norm_eq_abs, ← dist_eq_norm] at h1
        have hs : holderSeminorm α (fun y => boundaryNeumannC2Entry vI y i j)
            (closedBall (ctr x) (2 * η)) ≤ Cb :=
          (le_add_of_nonneg_left (holderUniformNorm_nonneg (hHI _ hct i j).uniform_bounded)).trans
            ((hCIle _ hct i j).trans hCIb)
        exact h1.trans (mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg dist_nonneg α))
  obtain ⟨v, hv2, hzv, hvent⟩ := boundary_neumann_layer_glue hα hρ hCb hD P u
    (fun x hx => (hspec x hx).1) (fun x hx => (hspec x hx).2.1)
    (fun x hx => (hspec x hx).2.2.1) (fun x hx => (hspec x hx).2.2.2.1)
    (fun x hx i j => ((hspec x hx).2.2.2.2 i j).1) (fun x hx i j => ((hspec x hx).2.2.2.2 i j).2)
  refine ⟨v, 2 * Cb * ρ⁻¹ ^ α + Cb, hv2, hzv, fun i j =>
    ⟨fun x hx => ((hvent i j).1 x hx).trans ?_, (hvent i j).2⟩⟩
  have : 0 ≤ 2 * Cb * ρ⁻¹ ^ α := by positivity
  linarith

end LiquidDrop
