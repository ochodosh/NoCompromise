import NoCompromise.Stationary.CapacitaryEstimate
import NoCompromise.Surface.Geometry
import NoCompromise.Green.SecondIdentity
import NoCompromise.Capacity.HullExistence

/-! # Assembly of `prop:cap-estimate` for stationary domains containing the origin

Blueprint Chapter 33 (`lem:integrate-EL`, `lem:two-bounds-I`, `prop:cap-estimate`), assembled
from the formalised Chapters 29–32 for `K = filledHull Ω` and its capacitary potential `u`.

External inputs, each stated once as a named predicate:

* `HullPotentialBoundaryC2` — the stand-in for `thm:boundary-C2a` used in
  `thm:capacitary-potential` (`u ∈ C^{2,α}_loc(closure (ℝ³ ∖ K))`): the potential of the filled
  hull of a bounded open `Ω ∋ 0` with `C³` boundary has a `C²` extension across `∂K`.
* `TotalCurvatureBound` — `thm:total-curvature-bound` (Chapter 14) for compact connected smooth
  embedded surfaces. It is applied only to the regular levels `{u = t}`, `0 < t < 1`, which are
  `C^∞` since `u` is smooth off `K`; it is never applied to the `C³` surface `∂K`.
* `CapacitaryInequalitiesStatement` — `thm:capacitary-inequalities` for a compact `K` with `C²`
  boundary and the `C²` extension `g` of its potential, with `H` the mean curvature of `∂K` in
  its charts (the form in which `cor:EL-pointwise` gives `H + v_Ω = λ`), given
  `thm:total-curvature-bound`. It is verbatim the statement of
  `CapacitaryK.capacitary_inequalities_of_C2_extension_final` on the Chapter-31 branch (not yet
  on `main`), which depends only on `thm:total-curvature-bound` and the extension; once it is
  merged the predicate is discharged and `prop:cap-estimate` rests on `HullPotentialBoundaryC2`
  and `TotalCurvatureBound` alone.
-/

noncomputable section

open MeasureTheory Set Filter Metric Topology

namespace LiquidDrop

/-- Stand-in for `thm:boundary-C2a` as used in `thm:capacitary-potential`: for the filled hull
`K` of a bounded open `Ω ∋ 0` with `C³` boundary, the capacitary potential `u` (continuous,
harmonic off `K`, `u = 1` on `K`, `u → 0` at infinity) agrees on `closure (ℝ³ ∖ K)` with a
`C²` function on `ℝ³`. -/
def HullPotentialBoundaryC2 : Prop :=
  ∀ (Ω : Set AmbientSpace), IsOpen Ω → Bornology.IsBounded Ω → HasCkBoundary 3 Ω →
    (0 : AmbientSpace) ∈ Ω → ∀ u : AmbientSpace → ℝ, Continuous u →
    HasDistributionalLaplacianOn u (fun _ => 0) (filledHull Ω)ᶜ →
    (∀ x ∈ filledHull Ω, u x = 1) → Tendsto u (cocompact AmbientSpace) (𝓝 0) →
    ∃ g : AmbientSpace → ℝ, ContDiff ℝ 2 g ∧ EqOn u g (closure (filledHull Ω)ᶜ)

/-- Blueprint `thm:total-curvature-bound`: every compact connected smooth embedded surface
with a unit normal field has total Gauss curvature at most `4π`. -/
def TotalCurvatureBound : Prop :=
  ∀ (S : Set AmbientSpace) (n : AmbientSpace → AmbientSpace), IsCompact S → IsConnected S →
    IsSmoothEmbeddedSurface S → IsUnitNormalField S n →
    ∫ x in S, gaussCurvature S n x ∂(Measure.euclideanHausdorffMeasure 2) ≤ 4 * Real.pi

/-- Blueprint `thm:capacitary-inequalities` (`eq:capacitary-inequalities`) for a compact
connected regular `K ∋ 0` with connected complement and `C²` boundary, whose capacitary
potential `u` has a `C²` extension `g` across `∂K`, given `thm:total-curvature-bound`:
`∫_{∂K} |∇u|² ≥ 4π` and `∫_{∂K} H|∇u| ≥ 4 ∫_{∂K} |∇u|² - 8π`, with `∇u = ∇g` on `∂K` and `H`
any function equal on `∂K` to the mean curvature of `∂K` in the `C²` charts of `int K`.
Verbatim the statement of `CapacitaryK.capacitary_inequalities_of_C2_extension_final`
(Chapter-31 branch). -/
def CapacitaryInequalitiesStatement : Prop :=
  ∀ (K : Set AmbientSpace), IsCompact K → IsConnected K → IsPreconnected Kᶜ →
    K = closure (interior K) → HasC2Boundary (interior K) → (0 : AmbientSpace) ∈ interior K →
    ∀ u : AmbientSpace → ℝ, Continuous u → HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ →
    (∀ x ∈ K, u x = 1) → Tendsto u (cocompact AmbientSpace) (𝓝 0) →
    ∀ g : AmbientSpace → ℝ, ContDiff ℝ 2 g → EqOn u g (closure Kᶜ) →
    TotalCurvatureBound →
    ∀ H : AmbientSpace → ℝ, (∀ p ∈ frontier K, ∀ c : C1BoundaryChart,
      c.IsChartFor (interior K) → p ∈ c.region → ContDiff ℝ 2 c.height →
      H p = meanCurvature (frontier K) c.outwardNormal p) →
    4 * Real.pi ≤ ∫ x in frontier K, ‖gradient g x‖ ^ 2 ∂hausdorffMeasure2 3 ∧
      4 * (∫ x in frontier K, ‖gradient g x‖ ^ 2 ∂hausdorffMeasure2 3) - 8 * Real.pi ≤
        ∫ x in frontier K, H x * ‖gradient g x‖ ∂hausdorffMeasure2 3

/-- Cauchy–Schwarz on a set of finite positive measure: `(∫ w)² / |S| ≤ ∫ w²`. -/
theorem capEstimate_sq_integral_div_le {μ : Measure AmbientSpace} {S : Set AmbientSpace}
    {w : AmbientSpace → ℝ} (hS : μ S ≠ ⊤) (hA : 0 < (μ S).toReal)
    (hw : IntegrableOn w S μ) (hw2 : IntegrableOn (fun x => w x ^ 2) S μ) :
    (∫ x in S, w x ∂μ) ^ 2 / (μ S).toReal ≤ ∫ x in S, w x ^ 2 ∂μ := by
  set A := (μ S).toReal
  set m := (∫ x in S, w x ∂μ) / A
  have hc : IntegrableOn (fun _ => m ^ 2) S μ := integrableOn_const hS
  have hexp : (fun x => (w x - m) ^ 2) = fun x => (w x ^ 2 - 2 * m * w x) + m ^ 2 := by
    funext x; ring
  have h0 : 0 ≤ ∫ x in S, (w x - m) ^ 2 ∂μ := setIntegral_nonneg_of_ae_restrict
    (Eventually.of_forall fun _ => sq_nonneg _)
  rw [hexp] at h0
  have hsplit : ∫ x in S, (w x ^ 2 - 2 * m * w x + m ^ 2) ∂μ =
      (∫ x in S, w x ^ 2 ∂μ) - 2 * m * (∫ x in S, w x ∂μ) + μ.real S * m ^ 2 := by
    have h1 : IntegrableOn (fun x => w x ^ 2 - 2 * m * w x) S μ :=
      hw2.sub (hw.const_mul (2 * m))
    rw [integral_add h1 hc, integral_sub hw2 (hw.const_mul (2 * m)), integral_const_mul,
      setIntegral_const, smul_eq_mul]
  rw [hsplit] at h0
  have hmA : m * A = ∫ x in S, w x ∂μ := by
    simp only [m]; field_simp
  have hkey : (∫ x in S, w x ∂μ) ^ 2 / A = m * (∫ x in S, w x ∂μ) := by
    rw [← hmA]; field_simp
  have hA' : μ.real S = A := rfl
  rw [hA'] at h0
  rw [hkey]
  rw [← hmA] at h0 ⊢
  nlinarith [h0]

/-- Blueprint `lem:integrate-EL`, equation `eq:integrate-EL`, for the filled hull `K` of a
stationary domain `Ω ∋ 0` and its capacitary potential `u` with a `C²` extension `g` across `∂K`
(`∇u = ∇g` on `∂K`): `λ Cap(K) - V = (4π)⁻¹ ∫_{∂K} H |∇u|`, for `H` the mean curvature of `∂K`
in the `C²` charts of `int K`. Inputs: `cor:EL-pointwise` through `lem:hull-properties`
(`IsStationaryDomain.filledHull_boundary`), `lem:flux-identity` (`flux_identity_w`) and
`thm:green-identity` (`filledHull_green_identity_of_boundary_C2`). -/
theorem integrate_EL_hull {V lam : ℝ} {Ω : Set AmbientSpace} (hV : 0 < V)
    (h : IsStationaryDomain V lam Ω) (h0 : (0 : AmbientSpace) ∈ Ω)
    {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) (filledHull Ω)ᶜ)
    (hb : ∀ x ∈ filledHull Ω, u x = 1) (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0))
    {g : AmbientSpace → ℝ} (hg : ContDiff ℝ 2 g) (hug : EqOn u g (closure (filledHull Ω)ᶜ))
    {H : AmbientSpace → ℝ} (hH : ∀ p ∈ frontier (filledHull Ω), ∀ c : C1BoundaryChart,
      c.IsChartFor (interior (filledHull Ω)) → p ∈ c.region → ContDiff ℝ 2 c.height →
      H p = meanCurvature (frontier (filledHull Ω)) c.outwardNormal p) :
    lam * capacityOf (filledHull Ω) u - V = (4 * Real.pi)⁻¹ *
      ∫ x in frontier (filledHull Ω), H x * ‖gradient g x‖ ∂hausdorffMeasure2 3 := by
  have ho := h.isOpen
  have hbd := h.isBounded
  have h1 := h.hasC1Boundary
  have h2 := h.hasC2Boundary
  set K := filledHull Ω with hKdef
  have hK : IsCompact K := filledHull_isCompact hbd
  have hreg : K = closure (interior K) := filledHull_eq_closure_interior ho
  have hC1 : HasC1Boundary (interior K) := filledHull_hasC1Boundary_interior ho h1
  have hC2K : HasC2Boundary (interior K) := filledHull_hasC2Boundary_interior ho h2
  have hzero : (0 : AmbientSpace) ∈ interior K := filledHull_subset_interior ho h0
  have hconn : IsPreconnected Kᶜ := (filledHull_isConnected_compl hbd).isPreconnected
  have hfr : frontier (interior K) = frontier K := filledHull_frontier_interior ho
  obtain ⟨R₁, hR₁⟩ := hK.isBounded.subset_closedBall (0 : AmbientSpace)
  have hKR : K ⊆ closedBall 0 (max R₁ 1) :=
    hR₁.trans (closedBall_subset_closedBall (le_max_left _ _))
  have hRpos : (0 : ℝ) < max R₁ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  set σ : Measure AmbientSpace := hausdorffMeasure2 3 with hσ
  have hσfin : σ (frontier K) ≠ ⊤ := by
    have := capacity_boundary_measure_lt_top isOpen_interior
      (hK.isBounded.subset interior_subset) hC1
    rw [hfr] at this
    exact this.ne
  have hfrK : IsCompact (frontier K) := hK.of_isClosed_subset isClosed_frontier
    (hK.isClosed.frontier_subset)
  set w : AmbientSpace → ℝ := fun x => ‖gradient g x‖ with hw
  set v : AmbientSpace → ℝ := coulombPotentialReal Ω with hv
  have hgradc : Continuous (gradient g) := by
    have : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
    exact (InnerProductSpace.toDual ℝ AmbientSpace).symm.continuous.comp this
  have hwc : Continuous w := continuous_norm.comp hgradc
  have hvc : Continuous v := continuous_coulombPotentialReal_of_isBounded ho.measurableSet hbd
  have hint : ∀ f : AmbientSpace → ℝ, Continuous f → IntegrableOn f (frontier K) σ :=
    fun f hf => hf.continuousOn.integrableOn_of_subset_isCompact hfrK
      isClosed_frontier.measurableSet Subset.rfl hσfin
  have hflux : ∫ x in frontier K, w x ∂σ = 4 * Real.pi * capacityOf K u :=
    (flux_identity_w hK hreg hC1 hRpos hKR hzero hu hh hb hinf hg hug hC2K hconn).symm
  have hgreen : (4 * Real.pi)⁻¹ * ∫ x in frontier K, v x * w x ∂σ = V := by
    rw [filledHull_green_identity_of_boundary_C2 ho hbd h1 h0 hu hh hb hinf hg hug,
      h.volume_toReal hV.le]
  have hvreal : ∀ x, (coulombPotential Ω x).toReal = v x := by
    intro x
    rw [hv, coulombPotentialReal_eq_setIntegral Ω ho.measurableSet x,
      coulombPotential_toReal Ω hbd.measure_lt_top x]
    simp only [one_div]
  -- `H + v_Ω = λ` on `∂K` (`cor:EL-pointwise`, `lem:hull-properties`)
  have hHeq : ∫ x in frontier K, H x * w x ∂σ = ∫ x in frontier K, (lam - v x) * w x ∂σ := by
    apply setIntegral_congr_fun isClosed_frontier.measurableSet
    intro x hx
    have hxi : x ∈ frontier (interior K) := by rw [hfr]; exact hx
    obtain ⟨c, hc, hxc, hc3⟩ := h.filledHull_boundary.1 x hxi
    have hc2 : ContDiff ℝ 2 c.height := hc3.of_le (by norm_num)
    have hEL := h.filledHull_boundary.2 x hx c hc hxc hc2
    rw [hvreal] at hEL
    simp only
    rw [hH x hx c hc hxc hc2]
    congr 1
    linarith
  rw [hHeq]
  exact integrate_EL_of_EL_pointwise_of_flux_identity_of_green_identity
    (σ.restrict (frontier K)) (fun x => lam - v x) v w lam (capacityOf K u) V
    (fun x => by ring) hflux hgreen (hint w hwc) (hint _ (hvc.mul hwc))

/-- Blueprint `lem:two-bounds-I` (with `eq:integrate-EL-bound` of `lem:integrate-EL`), equation
`eq:I-bound-combined`, for the filled hull of a stationary domain `Ω ∋ 0`:
`Cap(K) > 0`, `Per(Ω) > 0` and `λ Cap(K) - V ≥ max {2, 16π Cap(K)²/Per(Ω) - 2}`, modulo
`TotalCurvatureBound` and `CapacitaryInequalitiesStatement` (`thm:capacitary-inequalities`);
the `C²` extension `g` is an argument. -/
theorem two_bounds_I_hull (htc : TotalCurvatureBound) (hineq : CapacitaryInequalitiesStatement)
    {V lam : ℝ} {Ω : Set AmbientSpace} (hV : 0 < V)
    (h : IsStationaryDomain V lam Ω) (h0 : (0 : AmbientSpace) ∈ Ω)
    {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) (filledHull Ω)ᶜ)
    (hb : ∀ x ∈ filledHull Ω, u x = 1) (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0))
    {g : AmbientSpace → ℝ} (hg : ContDiff ℝ 2 g) (hug : EqOn u g (closure (filledHull Ω)ᶜ)) :
    0 < capacityOf (filledHull Ω) u ∧ 0 < (perimeter Ω).toReal ∧
      lam * capacityOf (filledHull Ω) u - V ≥
        max 2 (16 * Real.pi * capacityOf (filledHull Ω) u ^ 2 / (perimeter Ω).toReal - 2) := by
  have ho := h.isOpen
  have hbd := h.isBounded
  have h1 := h.hasC1Boundary
  have h2 := h.hasC2Boundary
  set K := filledHull Ω with hKdef
  have hK : IsCompact K := filledHull_isCompact hbd
  have hreg : K = closure (interior K) := filledHull_eq_closure_interior ho
  have hC1 : HasC1Boundary (interior K) := filledHull_hasC1Boundary_interior ho h1
  have hC2K : HasC2Boundary (interior K) := filledHull_hasC2Boundary_interior ho h2
  have hzero : (0 : AmbientSpace) ∈ interior K := filledHull_subset_interior ho h0
  have hconn : IsPreconnected Kᶜ := (filledHull_isConnected_compl hbd).isPreconnected
  have hfr : frontier (interior K) = frontier K := filledHull_frontier_interior ho
  obtain ⟨R₁, hR₁⟩ := hK.isBounded.subset_closedBall (0 : AmbientSpace)
  have hKR : K ⊆ closedBall 0 (max R₁ 1) :=
    hR₁.trans (closedBall_subset_closedBall (le_max_left _ _))
  have hRpos : (0 : ℝ) < max R₁ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  set σ : Measure AmbientSpace := hausdorffMeasure2 3 with hσ
  have hσfin : σ (frontier K) ≠ ⊤ := by
    have := capacity_boundary_measure_lt_top isOpen_interior
      (hK.isBounded.subset interior_subset) hC1
    rw [hfr] at this
    exact this.ne
  have hfrK : IsCompact (frontier K) := hK.of_isClosed_subset isClosed_frontier
    (hK.isClosed.frontier_subset)
  set w : AmbientSpace → ℝ := fun x => ‖gradient g x‖ with hw
  set v : AmbientSpace → ℝ := coulombPotentialReal Ω with hv
  have hgradc : Continuous (gradient g) := by
    have : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
    exact (InnerProductSpace.toDual ℝ AmbientSpace).symm.continuous.comp this
  have hwc : Continuous w := continuous_norm.comp hgradc
  have hint : ∀ f : AmbientSpace → ℝ, Continuous f → IntegrableOn f (frontier K) σ :=
    fun f hf => hf.continuousOn.integrableOn_of_subset_isCompact hfrK
      isClosed_frontier.measurableSet Subset.rfl hσfin
  set C := capacityOf K u with hCdef
  have hflux : ∫ x in frontier K, w x ∂σ = 4 * Real.pi * C :=
    (flux_identity_w hK hreg hC1 hRpos hKR hzero hu hh hb hinf hg hug hC2K hconn).symm
  have hCpos : 0 < C := capacityOf_pos hK hreg hC1 hRpos hKR hzero hu hh hb hinf hg hug
  -- the mean curvature of `∂K`, `H = λ - v_Ω` (`cor:EL-pointwise`, `lem:hull-properties`)
  set H : AmbientSpace → ℝ := fun x => lam - v x with hH
  have hvreal : ∀ x, (coulombPotential Ω x).toReal = v x := by
    intro x
    rw [hv, coulombPotentialReal_eq_setIntegral Ω ho.measurableSet x,
      coulombPotential_toReal Ω hbd.measure_lt_top x]
    simp only [one_div]
  have hHchart : ∀ x ∈ frontier K, ∀ c : C1BoundaryChart, c.IsChartFor (interior K) →
      x ∈ c.region → ContDiff ℝ 2 c.height →
      H x = meanCurvature (frontier K) c.outwardNormal x := by
    intro x hx c hc hxc hc2
    have hEL := h.filledHull_boundary.2 x hx c hc hxc hc2
    rw [hvreal] at hEL
    simp only [hH]
    linarith
  -- `thm:capacitary-inequalities`
  obtain ⟨hI1, hI2⟩ := hineq K hK (filledHull_isConnected h.isConnected hbd) hconn hreg hC2K
    hzero u hu hh hb hinf g hg hug htc H hHchart
  set I := ∫ x in frontier K, w x ^ 2 ∂σ with hIdef
  have hI1 : I ≥ 4 * Real.pi := hI1
  have hcap2 : ∫ x in frontier K, H x * w x ∂σ ≥ 4 * I - 8 * Real.pi := hI2
  -- `lem:integrate-EL`
  have hEL1 := integrate_EL_hull hV h h0 hu hh hb hinf hg hug hHchart
  have hELb := integrate_EL_bound_of_capacitary_inequalities (σ.restrict (frontier K)) H w
    lam C V I hEL1 hcap2
  -- `lem:two-bounds-I`
  set PK := (σ (frontier K)).toReal with hPK
  set P := (perimeter Ω).toReal with hPdef
  have hPKpos : 0 < PK := by
    rcases (ENNReal.toReal_nonneg : (0 : ℝ) ≤ PK).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have hz : σ (frontier K) = 0 := by
        rcases (ENNReal.toReal_eq_zero_iff _).mp heq.symm with h' | h'
        · exact h'
        · exact absurd h' hσfin
      have : ∫ x in frontier K, w x ∂σ = 0 := by
        rw [Measure.restrict_eq_zero.mpr hz, integral_zero_measure]
      rw [hflux] at this
      have : (0 : ℝ) < 4 * Real.pi * C := by positivity
      linarith
  have hPerΩ : perimeter Ω ≠ ⊤ := by
    rw [h1.perimeter_eq_boundaryArea ho]
    exact (capacity_boundary_measure_lt_top ho hbd h1).ne
  have hPKP : PK ≤ P := by
    have hle := filledHull_perimeter_interior_le ho hbd h1
    rw [hC1.perimeter_eq_boundaryArea isOpen_interior, hfr] at hle
    exact ENNReal.toReal_mono hPerΩ hle
  have hPpos : 0 < P := hPKpos.trans_le hPKP
  have hCS : I ≥ (∫ x in frontier K, w x ∂σ) ^ 2 / PK :=
    capEstimate_sq_integral_div_le hσfin hPKpos (hint w hwc) (hint _ (hwc.pow 2))
  have hI2' := I_ge_sq_div (σ.restrict (frontier K)) w hCS hflux hPKP hPKpos
  exact ⟨hCpos, hPpos, lambdaC_sub_V_ge_max (lambdaC_sub_V_ge_two hI1 hELb)
    (lambdaC_sub_V_ge_cap hPpos hI2' hELb)⟩

/-- Blueprint `prop:cap-estimate` (`eq:cap-estimate`) for a stationary domain containing the
origin, from `lem:two-bounds-I` (`two_bounds_I_hull`) and `lem:eliminate-capacity`
(`cap_estimate_of_stationary`) for `K = filledHull Ω` and its capacitary potential
(`exists_filledHull_capacitary_potential`), modulo the named predicates
`HullPotentialBoundaryC2` (`thm:boundary-C2a`), `TotalCurvatureBound`
(`thm:total-curvature-bound`) and `CapacitaryInequalitiesStatement`
(`thm:capacitary-inequalities`, proved on the Chapter-31 branch from
`thm:total-curvature-bound` and the extension). -/
theorem cap_estimate_of_stationary_of_zero_mem (hC2 : HullPotentialBoundaryC2)
    (htc : TotalCurvatureBound) (hineq : CapacitaryInequalitiesStatement) {V lam : ℝ}
    {Ω : Set AmbientSpace} (hV : 0 < V) (h : IsStationaryDomain V lam Ω)
    (h0 : (0 : AmbientSpace) ∈ Ω) :
    (V ≤ 6 → V + 2 ≤ lam * Real.sqrt ((perimeter Ω).toReal / (4 * Real.pi))) ∧
      (6 ≤ V → 4 * Real.sqrt (V - 2) ≤
        lam * Real.sqrt ((perimeter Ω).toReal / (4 * Real.pi))) := by
  obtain ⟨u, hu, hh, -, hb, hinf, -⟩ :=
    exists_filledHull_capacitary_potential h.isOpen h.isBounded h.hasC2Boundary h0
  obtain ⟨g, hg, hug⟩ := hC2 Ω h.isOpen h.isBounded h.boundary_C3 h0 u hu hh hb hinf
  obtain ⟨hCpos, hPpos, hkey⟩ := two_bounds_I_hull htc hineq hV h h0 hu hh hb hinf hg hug
  exact cap_estimate_of_stationary hV hPpos hCpos hkey

end LiquidDrop

#print axioms LiquidDrop.integrate_EL_hull
#print axioms LiquidDrop.two_bounds_I_hull
#print axioms LiquidDrop.cap_estimate_of_stationary_of_zero_mem
