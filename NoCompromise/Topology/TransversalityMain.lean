import NoCompromise.Topology.TransversePreimageDisk
import NoCompromise.Sard.Equidimensional
import NoCompromise.Sard.FourToThree
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Relative transversality for paths and disks

Regular level surfaces have local C² parametrizations whose derivative ranges are
the intrinsic tangent planes. In each patch, the incidence projection is a map
from three or four dimensions to three dimensions. The corresponding Sard theorem
makes its critical values null. Compactness gives finitely many patches, so good
cutoff parameters occur arbitrarily close to zero. The relative cutoff assembly
then gives the prescribed C¹ approximation and preserves the boundary restriction.
-/

noncomputable section
open Set Filter Function InnerProductSpace MeasureTheory
open scoped Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

-- `BoundaryTransverseAt` is defined in `NoCompromise.Topology.TransversePreimageDisk`.

/-- A parametrization taking values in a surface has tangential derivative. -/
theorem range_fderiv_le_tangentPlane {S : Set E₃} {k : ℕ}
    {ψ : EuclideanSpace ℝ (Fin k) → E₃} {W : Set (EuclideanSpace ℝ (Fin k))}
    (hW : IsOpen W) (hψS : ψ '' W ⊆ S) {w : EuclideanSpace ℝ (Fin k)}
    (hw : w ∈ W) (hψ : DifferentiableAt ℝ ψ w) :
    LinearMap.range (fderiv ℝ ψ w).toLinearMap ≤ tangentPlane S (ψ w) := by
  rintro _ ⟨v, rfl⟩
  rw [mem_tangentPlane_iff]
  intro F hF hzero
  have ht : Tendsto ψ (𝓝 w) (𝓝[S] ψ w) :=
    tendsto_nhdsWithin_iff.mpr ⟨hψ.continuousAt, by
      filter_upwards [hW.mem_nhds hw] with x hx
      exact hψS ⟨x, hx, rfl⟩⟩
  have heq : (F ∘ ψ) =ᶠ[𝓝 w] fun _ => 0 := ht.eventually hzero
  have hd := (hF.hasFDerivAt.comp w hψ.hasFDerivAt).congr_of_eventuallyEq heq.symm
  have hD := hd.fderiv
  have hv := congrArg (fun L => L v) hD
  simpa using hv.symm

/-- An immersive two-dimensional parametrization has exactly the intrinsic tangent range. -/
theorem range_fderiv_eq_tangentPlane {S : Set E₃} (hS : IsSmoothEmbeddedSurface S)
    {ψ : EuclideanSpace ℝ (Fin 2) → E₃} {W : Set (EuclideanSpace ℝ (Fin 2))}
    (hW : IsOpen W) (hψS : ψ '' W ⊆ S) {w : EuclideanSpace ℝ (Fin 2)}
    (hw : w ∈ W) (hψ : DifferentiableAt ℝ ψ w)
    (hinj : Injective (fderiv ℝ ψ w)) :
    LinearMap.range (fderiv ℝ ψ w).toLinearMap = tangentPlane S (ψ w) := by
  apply Submodule.eq_of_le_of_finrank_eq (range_fderiv_le_tangentPlane hW hψS hw hψ)
  rw [LinearMap.finrank_range_of_inj hinj, hS.finrank_tangentPlane (hψS ⟨w, hw, rfl⟩)]
  simp

/-- A regular level surface admits local C² parametrizations with the intrinsic tangent range. -/
theorem IsSmoothEmbeddedSurface.exists_local_parametrization {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) {s₀ : E₃} (hs₀ : s₀ ∈ S) :
    ∃ (Wψ : Set (EuclideanSpace ℝ (Fin 2))) (ψ : EuclideanSpace ℝ (Fin 2) → E₃)
      (O : Set E₃), IsOpen Wψ ∧ ContDiffOn ℝ 2 ψ Wψ ∧ IsOpen O ∧ s₀ ∈ O ∧
      S ∩ O ⊆ ψ '' Wψ ∧ ψ '' Wψ ⊆ S ∧
      ∀ w ∈ Wψ, LinearMap.range (fderiv ℝ ψ w).toLinearMap = tangentPlane S (ψ w) := by
  classical
  obtain ⟨U, φ, hU, hsU, hφ, hzero, hreg⟩ := hS s₀ hs₀
  let A := fderiv ℝ φ s₀
  have hA : A.range = ⊤ := by
    apply Module.Dual.range_eq_top_of_ne_zero
    intro hh
    apply hreg s₀ ⟨hs₀, hsU⟩
    apply (toDual ℝ E₃).injective
    rw [toDual_gradient, map_zero]
    exact ContinuousLinearMap.ext fun x => congrArg (fun L : E₃ →ₗ[ℝ] ℝ => L x) hh
  have hker : A.ker = tangentPlane S s₀ := by
    rw [tangentPlane_eq hU hsU (hφ.of_le (by simp)).contDiffAt hzero hs₀
      (hreg s₀ ⟨hs₀, hsU⟩)]
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_orthogonal_singleton_iff_inner_right,
      inner_gradient_left]
    rfl
  let c : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] A.ker :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [hker, hS.finrank_tangentPlane hs₀]; simp)
  have hd : HasStrictFDerivAt φ A s₀ :=
    (hφ.of_le (show (1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)).contDiffAt.hasStrictFDerivAt
      one_ne_zero
  let D := hd.implicitFunctionDataOfComplemented φ A hA
    A.ker_closedComplemented_of_finiteDimensional_range
  let e := D.toOpenPartialHomeomorph
  have hright : ContDiff ℝ 2 D.rightFun := by
    dsimp [D, HasStrictFDerivAt.implicitFunctionDataOfComplemented]
    exact ContinuousLinearMap.contDiff _ |>.comp (contDiff_id.sub contDiff_const)
  have heinv : ContDiffAt ℝ 2 (e.symm : ℝ × A.ker → E₃) (e s₀) := by
    exact D.contDiffAt_implicitFunction ((hφ.of_le (by simp)).contDiffAt)
      hright.contDiffAt (by norm_num)
  obtain ⟨T, hTsub, hT, hsT⟩ := mem_nhds_iff.mp (heinv.eventually (by norm_num))
  let O := U ∩ (e.source ∩ e ⁻¹' T)
  have hO : IsOpen O := hU.inter (e.isOpen_inter_preimage hT)
  have hOs : O ⊆ e.source := fun _ hx => hx.2.1
  have hsO : s₀ ∈ O := ⟨hsU, D.pt_mem_toOpenPartialHomeomorph_source, hsT⟩
  let ι : EuclideanSpace ℝ (Fin 2) → ℝ × A.ker := fun w => (0, c w)
  have hι : ContDiff ℝ 2 ι := contDiff_const.prodMk c.contDiff
  let Wψ := ι ⁻¹' (e '' O)
  let ψ := e.symm ∘ ι
  have hWψ : IsOpen Wψ := (e.isOpen_image_of_subset_source hO hOs).preimage hι.continuous
  have hinv (w) (hw : w ∈ Wψ) : ψ w ∈ O ∧ e (ψ w) = ι w := by
    obtain ⟨x, hx, hxw⟩ := hw
    have hinv : ψ w = x := by
      dsimp [ψ]
      rw [← hxw, e.left_inv (hOs hx)]
    exact ⟨hinv ▸ hx, by rw [hinv, hxw]⟩
  have hψcd : ContDiffOn ℝ 2 ψ Wψ := by
    intro w hw
    have ht : ι w ∈ T := by
      rw [← (hinv w hw).2]
      exact (hinv w hw).1.2.2
    have hcd : ContDiffAt ℝ 2 (e.symm : ℝ × A.ker → E₃) (ι w) := hTsub ht
    exact (hcd.comp w hι.contDiffAt).contDiffWithinAt
  have hψS : ψ '' Wψ ⊆ S := by
    rintro _ ⟨w, hw, rfl⟩
    have hz : φ (ψ w) = 0 := congrArg Prod.fst (hinv w hw).2
    exact ((congrArg (fun X : Set E₃ => ψ w ∈ X) hzero).mpr
      ⟨(hinv w hw).1.1, hz⟩).1
  refine ⟨Wψ, ψ, O, hWψ, hψcd, hO, hsO, ?_, hψS, ?_⟩
  · intro s hs
    have hz : φ s = 0 := (hzero ▸ (show s ∈ S ∩ U from ⟨hs.1, hs.2.1⟩)).2
    have hi : ι (c.symm (e s).2) = e s := by
      apply Prod.ext
      · exact hz.symm
      · exact c.apply_symm_apply _
    refine ⟨c.symm (e s).2, ?_, ?_⟩
    · change ι (c.symm (e s).2) ∈ e '' O
      rw [hi]
      exact ⟨s, hs.2, rfl⟩
    · change e.symm (ι (c.symm (e s).2)) = s
      rw [hi, e.left_inv (hOs hs.2)]
  · intro w hw
    have hdψ := (hψcd.contDiffAt (hWψ.mem_nhds hw)).differentiableAt (by norm_num)
    apply range_fderiv_eq_tangentPlane hS hWψ hψS hw hdψ
    let ρ := c.symm ∘ D.rightFun
    have hρ : DifferentiableAt ℝ ρ (ψ w) :=
      (c.symm.contDiff.comp hright).differentiable (by norm_num) _
    have heq : (ρ ∘ ψ) =ᶠ[𝓝 w] id := by
      filter_upwards [hWψ.mem_nhds hw] with v hv
      have hv' : D.rightFun (ψ v) = c v := congrArg Prod.snd (hinv v hv).2
      change c.symm (D.rightFun (ψ v)) = v
      rw [hv', c.symm_apply_apply]
    have hder := ((hρ.hasFDerivAt.comp w hdψ.hasFDerivAt).congr_of_eventuallyEq
      heq.symm).fderiv
    intro u v huv
    have heuv := congrArg (fderiv ℝ ρ (ψ w)) huv
    have hdu := congrArg (fun L => L u) hder
    have hdv := congrArg (fun L => L v) hder
    simpa using hdu.trans (heuv.trans hdv.symm)

/-- Boundary transversality is preserved by equality on a neighbourhood. -/
theorem BoundaryTransverseAt.congr_of_eventuallyEq {S : Set E₃} {k : ℕ}
    {f g : EuclideanSpace ℝ (Fin k) → E₃} {p : EuclideanSpace ℝ (Fin k)}
    (hf : BoundaryTransverseAt S f p) (hfg : g =ᶠ[𝓝 p] f) :
    BoundaryTransverseAt S g p := by
  simpa only [BoundaryTransverseAt, hfg.self_of_nhds, hfg.fderiv_eq] using hf

/-- A null set of bad parameters leaves arbitrarily small good parameters. -/
theorem exists_good_parameters_of_volume_bad_eq_zero {k : ℕ} {S : Set E₃}
    {f : EuclideanSpace ℝ (Fin k) → E₃} {χ : EuclideanSpace ℝ (Fin k) → ℝ}
    (hbad : volume {v : E₃ | ∃ p, 0 < χ p ∧
      ¬ TransverseAt S (fun q => f q + χ q • v) p} = 0) :
    ∀ δ > 0, ∃ v : E₃, ‖v‖ < δ ∧
      ∀ p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1,
        0 < χ p → TransverseAt S (fun q => f q + χ q • v) p := by
  classical
  intro δ hδ
  have hex : ∃ v ∈ Metric.ball (0 : E₃) δ,
      v ∉ {v : E₃ | ∃ p, 0 < χ p ∧ ¬ TransverseAt S (fun q => f q + χ q • v) p} := by
    by_contra hn
    push Not at hn
    have hz := measure_mono_null hn hbad
    exact (Metric.measure_ball_pos volume (0 : E₃) hδ).ne' hz
  obtain ⟨v, hv, hgood⟩ := hex
  refine ⟨v, by simpa using hv, ?_⟩
  intro p _ hp
  by_contra hn
  exact hgood ⟨p, hp, hn⟩

/-- Sard in dimensions three and four, after a continuous linear change of source coordinates. -/
theorem critical_values_volume_eq_zero_of_finrank
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 3 ∨ Module.finrank ℝ E = 4)
    {U : Set E} (hU : IsOpen U) {F : E → E₃} (hF : ContDiffOn ℝ 2 F U) :
    volume (F '' {x | x ∈ U ∧ ¬ Surjective (fderiv ℝ F x)}) = 0 := by
  have transport (n : ℕ)
      (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] E)
      (hsard : ∀ {V : Set (EuclideanSpace ℝ (Fin n))}, IsOpen V →
        ∀ {G : EuclideanSpace ℝ (Fin n) → E₃}, ContDiffOn ℝ 2 G V →
        volume (G '' {x | x ∈ V ∧ ¬ Surjective (fderiv ℝ G x)}) = 0) :
      volume (F '' {x | x ∈ U ∧ ¬ Surjective (fderiv ℝ F x)}) = 0 := by
    have hcomp : ContDiffOn ℝ 2 (F ∘ L) (L ⁻¹' U) :=
      hF.comp L.contDiff.contDiffOn (fun _ hx => hx)
    apply measure_mono_null (t := (F ∘ L) ''
      {x | x ∈ L ⁻¹' U ∧ ¬ Surjective (fderiv ℝ (F ∘ L) x)}) _
      (hsard (hU.preimage L.continuous) hcomp)
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨L.symm x, ⟨by simpa using hx.1, ?_⟩, by simp⟩
    intro hsurj
    apply hx.2
    have hdf := (hF.contDiffAt (hU.mem_nhds hx.1)).differentiableAt (by norm_num)
    have hder : fderiv ℝ (F ∘ L) (L.symm x) =
        (fderiv ℝ F x).comp L.toContinuousLinearMap := by
      rw [fderiv_comp _ (by simpa using hdf) L.differentiableAt,
        L.fderiv, L.apply_symm_apply]
    rw [hder] at hsurj
    intro y
    obtain ⟨z, hz⟩ := hsurj y
    exact ⟨L z, hz⟩
  rcases hdim with hdim | hdim
  · apply transport 3 (ContinuousLinearEquiv.ofFinrankEq (by simpa using hdim.symm))
    intro V hV G hG
    have hdet (x : E₃) : (fderiv ℝ G x).det = 0 ↔ ¬ Surjective (fderiv ℝ G x) := by
      rw [ContinuousLinearMap.det, LinearMap.det_eq_zero_iff_ker_ne_bot,
        ne_eq, LinearMap.ker_eq_bot, LinearMap.injective_iff_surjective]
      rfl
    simpa only [hdet] using sard_equidimensional_three hV (hG.of_le (by norm_num))
  · exact transport 4 (ContinuousLinearEquiv.ofFinrankEq (by simpa using hdim.symm))
      (fun hV _ hG => sard_four_to_three_not_surjective hV hG)

/-- The parameter projection in a surface incidence chart. -/
def cutoffIncidenceMap {k : ℕ} (f : EuclideanSpace ℝ (Fin k) → E₃)
    (χ : EuclideanSpace ℝ (Fin k) → ℝ) (ψ : EuclideanSpace ℝ (Fin 2) → E₃)
    (x : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin 2)) : E₃ :=
  (χ x.1)⁻¹ • (ψ x.2 - f x.1)

/-- The incidence projection is C² where the cutoff is positive. -/
theorem contDiffOn_cutoffIncidenceMap {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → E₃} (hf : ContDiff ℝ 2 f)
    {χ : EuclideanSpace ℝ (Fin k) → ℝ} (hχ : ContDiff ℝ 2 χ)
    {ψ : EuclideanSpace ℝ (Fin 2) → E₃} {Wψ : Set (EuclideanSpace ℝ (Fin 2))}
    (hψ : ContDiffOn ℝ 2 ψ Wψ) :
    ContDiffOn ℝ 2 (cutoffIncidenceMap f χ ψ) ({p | 0 < χ p} ×ˢ Wψ) := by
  exact ((hχ.comp contDiff_fst).contDiffOn.inv (fun _ hx => ne_of_gt hx.1)).smul
    ((hψ.comp contDiffOn_snd (fun _ hx => hx.2)).sub (hf.comp contDiff_fst).contDiffOn)

/-- Differentiating the incidence equation gives the cutoff projection formula. -/
theorem fderiv_cutoffIncidenceMap {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → E₃} {χ : EuclideanSpace ℝ (Fin k) → ℝ}
    {ψ : EuclideanSpace ℝ (Fin 2) → E₃}
    {p : EuclideanSpace ℝ (Fin k)} {w : EuclideanSpace ℝ (Fin 2)}
    (hf : DifferentiableAt ℝ f p) (hχ : DifferentiableAt ℝ χ p)
    (hψ : DifferentiableAt ℝ ψ w) (hp : χ p ≠ 0)
    (q : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ (cutoffIncidenceMap f χ ψ) (p, w) q =
      (χ p)⁻¹ • (fderiv ℝ ψ w q.2 -
        fderiv ℝ (fun x => f x + χ x • cutoffIncidenceMap f χ ψ (p, w)) p q.1) := by
  let Φ := cutoffIncidenceMap f χ ψ
  have hcf := hχ.hasFDerivAt.comp (p, w)
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (p, w)))
  have hff := hf.hasFDerivAt.comp (p, w)
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (p, w)))
  have hps := hψ.hasFDerivAt.comp (p, w)
    (hasFDerivAt_snd (𝕜 := ℝ) (p := (p, w)))
  have hΦ : DifferentiableAt ℝ Φ (p, w) :=
    (hcf.differentiableAt.inv hp).smul (hps.differentiableAt.sub hff.differentiableAt)
  have heq : (fun x => χ x.1 • Φ x) =ᶠ[𝓝 (p, w)] (fun x => ψ x.2 - f x.1) := by
    filter_upwards [hcf.continuousAt.eventually_ne hp] with x hx
    change χ x.1 ≠ 0 at hx
    simp [Φ, cutoffIncidenceMap, smul_smul, hx]
  have hd := ((hcf.smul hΦ.hasFDerivAt).congr_of_eventuallyEq heq.symm).unique
    (hps.sub hff)
  have hdq := congrArg (fun L => L q) hd
  have hid : χ p • fderiv ℝ Φ (p, w) q +
      fderiv ℝ χ p q.1 • Φ (p, w) = fderiv ℝ ψ w q.2 - fderiv ℝ f p q.1 := by
    simpa using hdq
  rw [fderiv_cutoff_perturbation hf hχ]
  change fderiv ℝ Φ (p, w) q = (χ p)⁻¹ •
    (fderiv ℝ ψ w q.2 - (fderiv ℝ f p q.1 + fderiv ℝ χ p q.1 • Φ (p, w)))
  have hsolve : fderiv ℝ ψ w q.2 -
      (fderiv ℝ f p q.1 + fderiv ℝ χ p q.1 • Φ (p, w)) =
      χ p • fderiv ℝ Φ (p, w) q := by
    rw [sub_add_eq_sub_sub, ← hid]
    abel
  rw [hsolve, smul_smul, inv_mul_cancel₀ hp, one_smul]

/-- The bad parameters of a cutoff perturbation form a null set for paths and disks. -/
theorem volume_bad_cutoff_parameters_eq_zero {k : ℕ} (hk : k = 1 ∨ k = 2)
    {S : Set E₃} (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S)
    {f : EuclideanSpace ℝ (Fin k) → E₃} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {χ : EuclideanSpace ℝ (Fin k) → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) :
    volume {v : E₃ | ∃ p, 0 < χ p ∧
      ¬ TransverseAt S (fun q => f q + χ q • v) p} = 0 := by
  classical
  choose Wψ ψ O hWψ hψ hO hsO hcover hsub hrange using
    fun s : S => hS.exists_local_parametrization s.property
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover O hO (by
    intro s hs
    exact mem_iUnion.mpr ⟨⟨s, hs⟩, hsO ⟨s, hs⟩⟩)
  let U (s : S) := {p | 0 < χ p} ×ˢ Wψ s
  let Φ (s : S) := cutoffIncidenceMap f χ (ψ s)
  have hU (s : S) : IsOpen (U s) :=
    (isOpen_lt continuous_const hχ.continuous).prod (hWψ s)
  have hΦ (s : S) : ContDiffOn ℝ 2 (Φ s) (U s) :=
    contDiffOn_cutoffIncidenceMap (hf.of_le (by simp)) (hχ.of_le (by simp)) (hψ s)
  have hnull (s : S) : volume (Φ s '' {x | x ∈ U s ∧ ¬ Surjective (fderiv ℝ (Φ s) x)}) = 0 := by
    apply critical_values_volume_eq_zero_of_finrank _ (hU s) (hΦ s)
    simpa only [Module.finrank_prod, finrank_euclideanSpace_fin] using
      hk.imp (fun h => by omega) (fun h => by omega)
  apply measure_mono_null (t := ⋃ s ∈ t,
    Φ s '' {x | x ∈ U s ∧ ¬ Surjective (fderiv ℝ (Φ s) x)}) _
    ((measure_biUnion_null_iff t.countable_toSet).mpr (fun s _ => hnull s))
  rintro v ⟨p, hp, hnot⟩
  have hmem : f p + χ p • v ∈ S := by
    by_contra hn
    exact hnot (fun hs => False.elim (hn hs))
  obtain ⟨s, hs, hpoint⟩ := mem_iUnion₂.mp (ht hmem)
  obtain ⟨w, hw, heqw⟩ := hcover s ⟨hmem, hpoint⟩
  have hv : Φ s (p, w) = v := by
    dsimp [Φ, cutoffIncidenceMap]
    rw [heqw, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ (ne_of_gt hp), one_smul]
  refine mem_iUnion₂.mpr ⟨s, hs, (p, w), ⟨⟨hp, hw⟩, ?_⟩, hv⟩
  intro hsurj
  have hder : (fderiv ℝ (Φ s) (p, w) :
      EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin 2) → E₃) =
      fun q => (χ p)⁻¹ • (fderiv ℝ (ψ s) w q.2 -
        fderiv ℝ (fun x => f x + χ x • v) p q.1) := by
    funext q
    have h := fderiv_cutoffIncidenceMap (hf.differentiable (by simp) p)
      (hχ.differentiable (by simp) p)
      (((hψ s).contDiffAt ((hWψ s).mem_nhds hw)).differentiableAt (by norm_num))
      (ne_of_gt hp) q
    change fderiv ℝ (Φ s) (p, w) q = _ at h
    simpa only [show cutoffIncidenceMap f χ (ψ s) (p, w) = v from hv] using h
  rw [hder] at hsurj
  have htrans := (cutoff_projection_surjective_iff (ne_of_gt hp)
    (fderiv ℝ (fun x => f x + χ x • v) p) (fderiv ℝ (ψ s) w)).mp hsurj
  rw [hrange s w hw, heqw] at htrans
  exact hnot (fun _ => htrans)

/-- Relative C¹-small transversality for paths and disks. -/
theorem exists_transverse_perturbation {k : ℕ} (hk : k = 1 ∨ k = 2)
    {S : Set E₃} (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S)
    {f : EuclideanSpace ℝ (Fin k) → E₃} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {W : Set (EuclideanSpace ℝ (Fin k))} (hW : IsOpen W)
    (hWb : Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1 ⊆ W)
    (hfW : ∀ p ∈ W ∩ Metric.closedBall 0 1, TransverseAt S f p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : EuclideanSpace ℝ (Fin k) → E₃, ContDiff ℝ (⊤ : ℕ∞) g ∧
      (∀ p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1,
        ‖g p - f p‖ < ε ∧ ‖fderiv ℝ g p - fderiv ℝ f p‖ < ε) ∧
      (∃ V : Set (EuclideanSpace ℝ (Fin k)), IsOpen V ∧
        Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1 ⊆ V ∧ ∀ p ∈ V, g p = f p) ∧
      ∀ p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1, TransverseAt S g p := by
  obtain ⟨χ, hχ, _, hχb, hχone, hχzero⟩ := exists_relative_transversality_cutoff hW hWb
  exact exists_relative_perturbation_of_good_parameters hf hfW hχ hχb hχone hχzero
    (exists_good_parameters_of_volume_bad_eq_zero
      (volume_bad_cutoff_parameters_eq_zero hk hS hc hf hχ)) hε

/-- The relative perturbation also preserves transversality of the boundary restriction. -/
theorem exists_transverse_perturbation_of_boundary_transverse {k : ℕ} (hk : k = 1 ∨ k = 2)
    {S : Set E₃} (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S)
    {f : EuclideanSpace ℝ (Fin k) → E₃} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {W : Set (EuclideanSpace ℝ (Fin k))} (hW : IsOpen W)
    (hWb : Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1 ⊆ W)
    (hfW : ∀ p ∈ W ∩ Metric.closedBall 0 1, TransverseAt S f p)
    (hbd : ∀ p ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1, BoundaryTransverseAt S f p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : EuclideanSpace ℝ (Fin k) → E₃, ContDiff ℝ (⊤ : ℕ∞) g ∧
      (∀ p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1,
        ‖g p - f p‖ < ε ∧ ‖fderiv ℝ g p - fderiv ℝ f p‖ < ε) ∧
      (∃ V : Set (EuclideanSpace ℝ (Fin k)), IsOpen V ∧
        Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1 ⊆ V ∧ ∀ p ∈ V, g p = f p) ∧
      (∀ p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1, TransverseAt S g p) ∧
      ∀ p ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1, BoundaryTransverseAt S g p := by
  obtain ⟨g, hg, hsmall, ⟨V, hV, hVb, hgf⟩, htrans⟩ :=
    exists_transverse_perturbation hk hS hc hf hW hWb hfW hε
  refine ⟨g, hg, hsmall, ⟨V, hV, hVb, hgf⟩, htrans, ?_⟩
  intro p hp
  apply (hbd p hp).congr_of_eventuallyEq
  filter_upwards [hV.mem_nhds (hVb hp)] with q hq
  exact hgf q hq

end LiquidDrop
