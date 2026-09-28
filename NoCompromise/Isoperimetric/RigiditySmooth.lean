import NoCompromise.Isoperimetric.SharpNeumann
import NoCompromise.Isoperimetric.RigidityHessian
import NoCompromise.Isoperimetric.RigidityAffine

/-!
# Isoperimetric rigidity for smooth domains

Blueprint `thm:isoperimetric-rigidity`, Steps 3–5, for bounded open sets with smooth boundary.
Equality in the ABP chain of `prop:iso-smooth` forces `|G \ Γ| = 0` and equality in AM–GM
a.e. on the contact set, hence `D²z = (Δz/3) I` on `G` by continuity; then `∇z` is a
homothety and `G` is a ball (`abp_equality_eq_ball`). Equality in `cor:iso-smooth-components`
leaves one component (`iso_smooth_rigidity`). The existence of the Neumann solution
(`lem:abp-neumann`) enters as the named hypothesis `ABPNeumannSolvable`.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal InnerProductSpace

namespace LiquidDrop

/-- Blueprint `thm:isoperimetric-rigidity`, Steps 4–5: equality in the ABP chain. If `z` is as
in the contact-set argument with `Δz = c > 0` on `G` and `|G| (c/3)^3 ≤ |B_1|` (the reverse of
the ABP volume bound), then `D²z = (c/3) I` on `G` and `G` is a ball of radius `3/c`. -/
theorem abp_equality_eq_ball {G : Set AmbientSpace}
    (hGb : Bornology.IsBounded G) (hGo : IsOpen G) (hGc : IsConnected G)
    {z : AmbientSpace → ℝ}
    (hz : ContDiffOn ℝ 2 z G) (hzc : ContinuousOn z (closure G)) (hN : NeumannOne G z)
    {c : ℝ} (hc : 0 < c) (hlap : ∀ x ∈ G, laplacianTrace z x = c)
    (heq : volume G * ENNReal.ofReal ((c / 3) ^ 3) ≤ ENNReal.ofReal (4 * Real.pi / 3)) :
    ∃ p : AmbientSpace, G = ball p (c / 3)⁻¹ := by
  set Γ := abpContactSet G z with hΓ
  have hm : MeasurableSet Γ := measurableSet_abpContactSet hGo hz
  set K : ℝ≥0∞ := ENNReal.ofReal ((c / 3) ^ 3) with hK
  set f : AmbientSpace → ℝ≥0∞ := fun x => ENNReal.ofReal |(abpHessianCLM z x).det| with hf
  have hK0 : K ≠ 0 := by
    rw [hK]; exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hKtop : K ≠ ∞ := ENNReal.ofReal_ne_top
  have hΓG : Γ ⊆ G := fun _ hx => hx.1
  have hGfin : volume G ≠ ∞ := hGb.measure_lt_top.ne
  have hΓfin : volume Γ ≠ ∞ := ne_top_of_le_ne_top hGfin (measure_mono hΓG)
  have hfle : ∀ x ∈ Γ, f x ≤ K := by
    intro x hx
    apply ENNReal.ofReal_le_ofReal
    simpa only [hlap x hx.1] using abs_det_abpHessianCLM_le hGo hz hx
  have h1 : ENNReal.ofReal (4 * Real.pi / 3) ≤ ∫⁻ x in Γ, f x :=
    calc
      ENNReal.ofReal (4 * Real.pi / 3) = volume (ball (0 : AmbientSpace) 1) := by
        rw [volume_ball_eq_ofReal _ zero_le_one]
        norm_num
      _ ≤ volume (gradient z '' Γ) := measure_mono
        (ball_subset_gradient_image_abpContactSet hGb hGo hGc.nonempty hz hzc hN)
      _ ≤ ∫⁻ x in Γ, f x :=
        addHaar_image_le_lintegral_abs_det_fderiv volume hm
          (fun _ hx => (hasFDerivAt_gradient_abpHessianCLM hGo hz hx.1).hasFDerivWithinAt)
  have h2 : ∫⁻ x in Γ, f x ≤ K * volume Γ := by
    calc
      ∫⁻ x in Γ, f x ≤ ∫⁻ _ in Γ, K := setLIntegral_mono' hm hfle
      _ = K * volume Γ := setLIntegral_const _ _
  have h3 : K * volume Γ ≤ volume G * K := by
    rw [mul_comm]; exact mul_le_mul_left (measure_mono hΓG) _
  -- every inequality in the chain is an equality
  have hint : ∫⁻ _ in Γ, K ≤ ∫⁻ x in Γ, f x := by
    rw [setLIntegral_const]
    calc
      K * volume Γ ≤ volume G * K := h3
      _ ≤ _ := heq
      _ ≤ _ := h1
  have hae : f =ᵐ[volume.restrict Γ] fun _ => K := by
    apply ae_eq_of_ae_le_of_lintegral_le
    · exact (ae_restrict_iff' hm).mpr (Eventually.of_forall hfle)
    · exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hKtop hΓfin) h2
    · exact aemeasurable_const
    · exact hint
  have hvolΓ : volume G ≤ volume Γ := by
    have : volume G * K ≤ volume Γ * K := by
      calc
        volume G * K ≤ _ := heq
        _ ≤ _ := h1
        _ ≤ _ := h2
        _ = volume Γ * K := mul_comm _ _
    exact (ENNReal.mul_le_mul_iff_left hK0 hKtop).mp this
  have hnull : volume (G \ Γ) = 0 := by
    rw [measure_sdiff hΓG hm.nullMeasurableSet hΓfin]
    exact tsub_eq_zero_of_le hvolΓ
  -- the Hessian identity holds almost everywhere on `G`
  set A : Set AmbientSpace :=
    G ∩ {x | abpHessianCLM z x ≠ (c / 3) • ContinuousLinearMap.id ℝ AmbientSpace} with hA
  have hAopen : IsOpen A :=
    (continuousOn_abpHessianCLM hGo hz).isOpen_inter_preimage hGo isOpen_ne
  have hAnull : volume A = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    have hG' : ∀ᵐ x ∂volume, x ∉ G \ Γ := measure_eq_zero_iff_ae_notMem.mp hnull
    have hf' := (ae_restrict_iff' hm).mp hae
    filter_upwards [hG', hf'] with x hxG hxf hxA
    have hxΓ : x ∈ Γ := by
      by_contra h
      exact hxG ⟨hxA.1, h⟩
    have hfx : f x = K := hxf hxΓ
    have hdet : |(abpHessianCLM z x).det| = (laplacianTrace z x / 3) ^ 3 := by
      rw [hlap x hxA.1]
      exact (ENNReal.ofReal_eq_ofReal_iff (abs_nonneg _) (by positivity)).mp hfx
    have := abpHessianCLM_eq_smul_id_of_abs_det_eq hGo hz hxΓ hdet
    rw [hlap x hxA.1] at this
    exact hxA.2 this
  have hAempty : A = ∅ := (hAopen.measure_eq_zero_iff volume).mp hAnull
  have hhess : ∀ x ∈ G,
      HasFDerivAt (gradient z) ((c / 3) • ContinuousLinearMap.id ℝ AmbientSpace) x := by
    intro x hx
    have h := hasFDerivAt_gradient_abpHessianCLM hGo hz hx
    have hx' : x ∉ A := by rw [hAempty]; exact notMem_empty x
    have : abpHessianCLM z x = (c / 3) • ContinuousLinearMap.id ℝ AmbientSpace := by
      by_contra hne
      exact hx' ⟨hx, hne⟩
    rwa [this] at h
  have hball : ball (0 : AmbientSpace) 1 ⊆ gradient z '' G :=
    (ball_subset_gradient_image_abpContactSet hGb hGo hGc.nonempty hz hzc hN).trans
      (image_mono hΓG)
  exact eq_ball_of_hasFDerivAt_smul_id hGo hGc.isPreconnected (by positivity) hhess hball heq

/-- Blueprint `thm:isoperimetric-rigidity`, Steps 4–5 for a bounded connected smooth domain,
given `lem:abp-neumann`: equality `Per(G)^3 = 36π|G|^2` (only `≤` is assumed; `≥` is
`prop:iso-smooth`) forces `G` to be a ball. -/
theorem iso_smooth_rigidity_connected (hN : ABPNeumannSolvable) {G : Set AmbientSpace}
    (hGo : IsOpen G) (hGb : Bornology.IsBounded G) (hGc : IsConnected G)
    (hGs : HasSmoothBoundary G)
    (heq : (perimeter G).toReal ^ 3 ≤ 36 * Real.pi * volume.real G ^ 2) :
    ∃ (p : AmbientSpace) (r : ℝ), 0 < r ∧ G = ball p r := by
  obtain ⟨z, hz⟩ := hN G hGo hGb hGc hGs
  have hV : 0 < volume.real G :=
    ENNReal.toReal_pos_iff.mpr ⟨hGo.measure_pos volume hGc.nonempty, hGb.measure_lt_top⟩
  have hiso := iso_smooth hN hGo hGb hGc hGs
  set P := (perimeter G).toReal with hP
  have hP0 : 0 < P := by
    have : 0 < P ^ 3 := lt_of_lt_of_le (by positivity) hiso
    have hP0' : 0 ≤ P := ENNReal.toReal_nonneg
    rcases hP0'.lt_or_eq with h | h
    · exact h
    · rw [← h] at this; norm_num at this
  set c := P / volume.real G with hc
  have hc0 : 0 < c := div_pos hP0 hV
  have hvol : volume G * ENNReal.ofReal ((c / 3) ^ 3) ≤ ENNReal.ofReal (4 * Real.pi / 3) := by
    rw [← ENNReal.ofReal_toReal hGb.measure_lt_top.ne, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
    apply ENNReal.ofReal_le_ofReal
    change volume.real G * (c / 3) ^ 3 ≤ 4 * Real.pi / 3
    have he : volume.real G * (c / 3) ^ 3 = P ^ 3 / (27 * volume.real G ^ 2) := by
      rw [hc]; field_simp; ring
    rw [he, div_le_iff₀ (by positivity)]
    nlinarith [heq]
  obtain ⟨p, hp⟩ := abp_equality_eq_ball hGb hGo hGc hz.contDiffOn_two hz.continuousOn
    hz.neumannOne hc0 hz.2.1 hvol
  exact ⟨p, (c / 3)⁻¹, by positivity, hp⟩

/-- Blueprint `thm:isoperimetric-rigidity`, Steps 3–5 for a bounded open set with smooth
boundary, given `lem:abp-neumann`: if `0 < |S|` and `Per(S) ≤ (36π)^{1/3} |S|^{2/3}` (the
reverse inequality is `cor:iso-smooth-components`), then `S` has one component
(`cor:iso-smooth-components`, strictness via `lem:concavity-23`) and is a ball. -/
theorem iso_smooth_rigidity (hN : ABPNeumannSolvable) {S : Set AmbientSpace}
    (hSo : IsOpen S) (hSb : Bornology.IsBounded S) (hSs : HasSmoothBoundary S)
    (hpos : 0 < volume S)
    (heq : perimeter S ≤
      ENNReal.ofReal ((36 * Real.pi) ^ (1 / (3 : ℝ)) * (volume S).toReal ^ (2 / (3 : ℝ)))) :
    ∃ (p : AmbientSpace) (r : ℝ), 0 < r ∧ S = ball p r := by
  have hfin : volume S ≠ ∞ := hSb.measure_lt_top.ne
  have hcI : 0 < (36 * Real.pi) ^ (1 / (3 : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
  have hrw : ENNReal.ofReal ((36 * Real.pi) ^ (1 / (3 : ℝ)) * (volume S).toReal ^ (2 / (3 : ℝ)))
      = ENNReal.ofReal ((36 * Real.pi) ^ (1 / (3 : ℝ))) * volume S ^ (2 / (3 : ℝ)) := by
    rw [ENNReal.ofReal_mul hcI.le,
      ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
      ENNReal.ofReal_toReal hfin]
  -- Step 3: one component
  obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hpos.ne'
  have hconn : IsConnected S := by
    have hK : connectedComponentIn S x = S := by
      by_contra hne
      obtain ⟨y, hyS, hyK⟩ : ∃ y ∈ S, y ∉ connectedComponentIn S x := by
        by_contra h
        push Not at h
        exact hne (Subset.antisymm (connectedComponentIn_subset S x) h)
      have hGH : connectedComponentIn S x ≠ connectedComponentIn S y := by
        intro h
        exact hyK (h ▸ mem_connectedComponentIn hyS)
      have hlt := volume_rpow_lt_tsum_openComponents hSo hSb ⟨x, hx, rfl⟩ ⟨y, hyS, rfl⟩ hGH
      obtain ⟨h1, -⟩ := iso_smooth_components
        (fun _ hGo hGb hGc hGs => iso_smooth hN hGo hGb hGc hGs) hSo hSb hSs
      have hc0 : ENNReal.ofReal ((36 * Real.pi) ^ (1 / (3 : ℝ))) ≠ 0 :=
        (ENNReal.ofReal_pos.mpr hcI).ne'
      have hlt' := ENNReal.mul_lt_mul_right hc0 ENNReal.ofReal_ne_top hlt
      have := (hlt'.trans_le h1).trans_le heq
      rw [hrw] at this
      exact lt_irrefl _ this
    rw [← hK]
    exact isConnected_connectedComponentIn_iff.mpr hx
  apply iso_smooth_rigidity_connected hN hSo hSb hconn hSs
  -- the cubic form of the equality
  have hPfin : perimeter S ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top heq
  have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top heq
  rw [ENNReal.toReal_ofReal (by positivity)] at hle
  have hc3 : ((36 * Real.pi) ^ (1 / (3 : ℝ))) ^ 3 = 36 * Real.pi := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hv3 : ((volume S).toReal ^ (2 / (3 : ℝ))) ^ 3 = volume.real S ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ENNReal.toReal_nonneg]
    norm_num
    rfl
  calc
    (perimeter S).toReal ^ 3 ≤
        ((36 * Real.pi) ^ (1 / (3 : ℝ)) * (volume S).toReal ^ (2 / (3 : ℝ))) ^ 3 :=
      pow_le_pow_left₀ ENNReal.toReal_nonneg hle 3
    _ = 36 * Real.pi * volume.real S ^ 2 := by rw [mul_pow, hc3, hv3]

end LiquidDrop
