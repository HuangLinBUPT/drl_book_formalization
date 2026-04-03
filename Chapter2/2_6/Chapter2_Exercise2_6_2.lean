import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Chapter2.«2_6».Chapter2_Exercise2_6_1

/-!
# Chapter 2, Exercise 2.6.2: Sphere Projection via First-Order Optimality

## Informal Statement (exercise:sphere-calculus, Part 2)

For nonzero `v ∈ ℝ^d`, the nearest point on the unit sphere S^{d-1} to v is v/‖v‖:
  `proj_{S^{d-1}}(v) := argmin_{‖u‖=1} ‖u - v‖ = v / ‖v‖`

## Proof Strategy (following the book)

The Riemannian gradient of `f(u) = ‖u - v‖²` over the sphere is:
  `grad f(u) = P_u^⊥ ∇f(u) = (I - uu^T)(2(u - v))`

Setting `grad f(u) = 0` means `u - v` is parallel to `u`, i.e., `v = λu` for some scalar λ.
Since `‖u‖ = 1`, we get `u = v / ‖v‖`.

We prove minimality directly using Cauchy-Schwarz:
  `‖u - v‖² = ‖u‖² - 2⟨u,v⟩ + ‖v‖² ≥ 1 - 2‖v‖ + ‖v‖² = (1-‖v‖)² = ‖v/‖v‖ - v‖²`

## References
- Book: deep-representation-learning-book, Chapter 2, exercise:sphere-calculus Part 2
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Key lemmas about the normalized vector -/

/-- The normalized vector ‖v‖⁻¹ • v lies on the unit sphere. -/
lemma sphere_normalize_mem (v : E) (hv : v ≠ 0) : ‖‖v‖⁻¹ • v‖ = 1 :=
  norm_smul_inv_norm hv

/-- The inner product of ‖v‖⁻¹ • v with v equals ‖v‖. -/
lemma inner_normalize_self (v : E) (hv : v ≠ 0) :
    inner ℝ (‖v‖⁻¹ • v) v = ‖v‖ := by
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hv' : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  field_simp

/-- The squared distance from ‖v‖⁻¹ • v to v is (1 - ‖v‖)². -/
lemma norm_normalize_sub_sq (v : E) (hv : v ≠ 0) :
    ‖‖v‖⁻¹ • v - v‖ ^ 2 = (1 - ‖v‖) ^ 2 := by
  rw [norm_sub_sq_real, sphere_normalize_mem v hv, one_pow, inner_normalize_self v hv]
  ring

/-! ### First-order optimality condition -/

/-- The Riemannian gradient of ‖u - v‖² at u = ‖v‖⁻¹ • v is zero.
    Equivalently, `(u - v)` is parallel to `u = ‖v‖⁻¹ • v`. -/
theorem sphere_proj_first_order (v : E) (hv : v ≠ 0) :
    (ℝ ∙ (‖v‖⁻¹ • v))ᗮ.starProjection (‖v‖⁻¹ • v - v) = 0 := by
  have hu : ‖‖v‖⁻¹ • v‖ = 1 := sphere_normalize_mem v hv
  rw [sphere_tangent_projection_explicit (‖v‖⁻¹ • v) hu]
  -- Goal: (‖v‖⁻¹ • v - v) - ⟨‖v‖⁻¹ • v, ‖v‖⁻¹ • v - v⟩ • (‖v‖⁻¹ • v) = 0
  have h_inner : inner ℝ (‖v‖⁻¹ • v) (‖v‖⁻¹ • v - v) = 1 - ‖v‖ := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq, sphere_normalize_mem v hv, one_pow,
        inner_normalize_self v hv]
  rw [h_inner]
  -- Goal: (‖v‖⁻¹ • v - v) - (1 - ‖v‖) • (‖v‖⁻¹ • v) = 0
  -- = ‖v‖⁻¹ • v - v - (‖v‖⁻¹ • v) + ‖v‖ • (‖v‖⁻¹ • v)
  -- = ‖v‖ • (‖v‖⁻¹ • v) - v = (‖v‖ * ‖v‖⁻¹) • v - v = v - v = 0
  have hv' : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  simp only [smul_smul]; ring_nf; rw [mul_inv_cancel₀ hv']; module

/-! ### Main theorem: v/‖v‖ minimizes distance to v on the sphere -/

/-- For any unit vector u, ‖‖v‖⁻¹ • v - v‖ ≤ ‖u - v‖ (Cauchy-Schwarz). -/
theorem sphere_projection_is_argmin (v : E) (hv : v ≠ 0) :
    ∀ u : E, ‖u‖ = 1 → ‖‖v‖⁻¹ • v - v‖ ≤ ‖u - v‖ := by
  intro u hu
  -- Reduce to comparing squared norms (both sides nonneg)
  have h₁ : 0 ≤ ‖‖v‖⁻¹ • v - v‖ := norm_nonneg _
  have h₂ : 0 ≤ ‖u - v‖ := norm_nonneg _
  rw [← Real.sqrt_sq h₁, ← Real.sqrt_sq h₂]
  apply Real.sqrt_le_sqrt
  -- Show ‖‖v‖⁻¹ • v - v‖² ≤ ‖u - v‖²
  have lhs : ‖‖v‖⁻¹ • v - v‖ ^ 2 = (1 - ‖v‖) ^ 2 :=
    norm_normalize_sub_sq v hv
  have rhs : ‖u - v‖ ^ 2 = 1 - 2 * inner ℝ u v + ‖v‖ ^ 2 := by
    rw [norm_sub_sq_real, hu, one_pow]
  -- Cauchy-Schwarz: ⟨u,v⟩ ≤ ‖u‖ * ‖v‖ = ‖v‖
  have cs : inner ℝ u v ≤ ‖v‖ := by
    calc inner ℝ u v ≤ ‖u‖ * ‖v‖ := real_inner_le_norm u v
      _ = ‖v‖ := by rw [hu, one_mul]
  rw [lhs, rhs]
  nlinarith [sq_nonneg (inner ℝ u v), norm_nonneg v, sq_abs ‖v‖]

/-- The minimizer ‖v‖⁻¹ • v is unique: any unit minimizer equals ‖v‖⁻¹ • v. -/
theorem sphere_projection_unique (v : E) (hv : v ≠ 0)
    (u : E) (hu : ‖u‖ = 1) (hmin : ‖u - v‖ ≤ ‖‖v‖⁻¹ • v - v‖) :
    u = ‖v‖⁻¹ • v := by
  -- From hmin and sphere_projection_is_argmin, ‖u - v‖ = ‖‖v‖⁻¹ • v - v‖
  have heq : ‖u - v‖ = ‖‖v‖⁻¹ • v - v‖ :=
    le_antisymm hmin (sphere_projection_is_argmin v hv u hu)
  -- ‖u - v‖² = ‖‖v‖⁻¹ • v - v‖² = (1 - ‖v‖)²
  have lhs_sq : ‖u - v‖ ^ 2 = (1 - ‖v‖) ^ 2 := by
    rw [heq, norm_normalize_sub_sq v hv]
  -- Expanding: 1 - 2⟨u,v⟩ + ‖v‖² = 1 - 2‖v‖ + ‖v‖²
  -- So ⟨u,v⟩ = ‖v‖ = ‖u‖ * ‖v‖, i.e., equality in Cauchy-Schwarz
  have inner_eq : inner ℝ u v = ‖v‖ := by
    have := lhs_sq
    rw [norm_sub_sq_real, hu, one_pow] at this
    nlinarith [sq_nonneg ‖v‖]
  -- Cauchy-Schwarz equality ⟨u,v⟩ = ‖u‖‖v‖ implies u = ‖v‖⁻¹ • v
  have hv' : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  -- inner_eq_norm_mul_iff_real: ⟨u,v⟩ = ‖u‖ * ‖v‖ ↔ ‖v‖ • u = ‖u‖ • v
  have hcol : ‖v‖ • u = ‖u‖ • v :=
    inner_eq_norm_mul_iff_real.mp (by rw [hu, one_mul]; exact inner_eq)
  rw [hu, one_smul] at hcol
  -- hcol : ‖v‖ • u = v, so u = ‖v‖⁻¹ • v
  have : u = ‖v‖⁻¹ • (‖v‖ • u) := by rw [smul_smul, inv_mul_cancel₀ hv', one_smul]
  rw [this, hcol]
