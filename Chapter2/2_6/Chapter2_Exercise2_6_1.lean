import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Chapter 2, Exercise 2.6.1: Sphere Tangent Space and Projection

## Informal Statement (exercise:sphere-calculus, Part 1)

Let `F(u) = ‖u‖² - 1`, so the unit sphere `S^{d-1} = F⁻¹({0})`.

**Part 1a**: The tangent space to the sphere at u is the kernel of `DF_u`,
and since `DF_u[v] = 2⟨u, v⟩`, we have:
  `T_u S^{d-1} = { v ∈ ℝ^d | ⟨v, u⟩ = 0 } = (ℝ · u)ᗮ`

**Part 1b**: The orthogonal projection onto this tangent space is `P_u^⊥ = I - u uᵀ`.
In Lean/Mathlib, this is `(ℝ ∙ u)ᗮ.starProjection`, which satisfies:
  - Idempotent: `P ∘ P = P`
  - Symmetric (self-adjoint): `inner ℝ (P v) w = inner ℝ v (P w)`
  - Range ⊆ tangent space: `inner ℝ (P v) u = 0`
  - Identity on tangent space: `inner ℝ v u = 0 → P v = v`

## References
- Book: deep-representation-learning-book, Chapter 2, exercise:sphere-calculus Part 1
- Mathlib: `Mathlib.Analysis.InnerProductSpace.Projection.Basic`
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Part 1a: Tangent space equals orthogonal complement -/

/-- The tangent space to S^{d-1} at u is the set of vectors orthogonal to u.
    `T_u S^{d-1} = ker(DF_u) = {v | inner ℝ v u = 0} = (ℝ·u)ᗮ`. -/
theorem sphere_tangentSpace_eq_orthogonal (u : E) :
    (ℝ ∙ u)ᗮ = {v : E | inner ℝ v u = (0 : ℝ)} := by
  ext v
  simp [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm]

/-! ### Part 1b: Projection formula P_u^⊥ = id - starProjection(ℝ·u) -/

/-- For a unit vector u, the orthogonal projection onto span {u} satisfies:
    `(ℝ·u).starProjection w = ⟨u, w⟩ • u` -/
lemma starProjection_span_unit (u : E) (hu : ‖u‖ = 1) (w : E) :
    (ℝ ∙ u).starProjection w = (inner ℝ u w : ℝ) • u := by
  rw [Submodule.starProjection_singleton]
  simp [hu]

/-- The projection onto the tangent space (ℝ·u)ᗮ equals `1 - (ℝ·u).starProjection`. -/
theorem sphere_tangent_projection (u : E) :
    (ℝ ∙ u)ᗮ.starProjection = 1 - (ℝ ∙ u).starProjection := by
  exact Submodule.starProjection_orthogonal' (ℝ ∙ u)

/-- The projection onto the tangent space is idempotent. -/
theorem sphere_tangent_projection_idempotent (u : E) :
    IsIdempotentElem (ℝ ∙ u)ᗮ.starProjection :=
  Submodule.isIdempotentElem_starProjection _

/-- For a unit vector u, the explicit formula: P_u^⊥ v = v - ⟨u,v⟩ • u. -/
theorem sphere_tangent_projection_explicit (u : E) (hu : ‖u‖ = 1) (v : E) :
    (ℝ ∙ u)ᗮ.starProjection v = v - (inner ℝ u v : ℝ) • u := by
  rw [Submodule.starProjection_orthogonal_val]
  simp [starProjection_span_unit u hu v]

/-- The projection is symmetric (self-adjoint w.r.t. the inner product). -/
theorem sphere_tangent_projection_symmetric (u : E) (hu : ‖u‖ = 1) (v w : E) :
    inner ℝ ((ℝ ∙ u)ᗮ.starProjection v) w =
    inner ℝ v ((ℝ ∙ u)ᗮ.starProjection w) := by
  simp only [sphere_tangent_projection_explicit u hu]
  simp [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
        real_inner_comm u v, mul_comm]

/-- The projection maps into the tangent space: `inner ℝ (P v) u = 0`. -/
theorem sphere_tangent_projection_range (u : E) (hu : ‖u‖ = 1) (v : E) :
    inner ℝ ((ℝ ∙ u)ᗮ.starProjection v) u = (0 : ℝ) := by
  rw [sphere_tangent_projection_explicit u hu]
  simp only [inner_sub_left, inner_smul_left]
  rw [real_inner_comm u v]
  simp [hu]

/-- If v ⊥ u, then P_u^⊥ acts as the identity: P v = v. -/
theorem sphere_tangent_projection_identity_on_tangent
    (u : E) (hu : ‖u‖ = 1) (v : E) (hv : inner ℝ v u = (0 : ℝ)) :
    (ℝ ∙ u)ᗮ.starProjection v = v := by
  rw [sphere_tangent_projection_explicit u hu]
  have : (inner ℝ u v : ℝ) = 0 := by rw [real_inner_comm]; exact hv
  simp [this]
