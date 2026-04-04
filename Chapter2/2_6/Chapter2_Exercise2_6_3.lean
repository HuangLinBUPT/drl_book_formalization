import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Chapter2.«2_6».Chapter2_Exercise2_6_1

/-!
# Chapter 2, Exercise 2.6.3: Riemannian Hessian for Sphere-Constrained Optimization

## Informal Statement (exercise:sphere-calculus, Part 3)

Let `f : ℝ^d → ℝ` be twice-continuously-differentiable. By differentiating the Riemannian
gradient `grad f(u) = P_u^⊥ ∇f(u)` along a sphere-constrained path and projecting the
result onto the tangent space, we obtain the **Riemannian Hessian**:

  `Hess f(u) = P_u^⊥ (∇²f(u) - ⟨∇f(u), u⟩ · I) P_u^⊥`

where `P_u^⊥ = I - u uᵀ` is the orthogonal projection onto `T_u S^{d-1}`.

## Derivation outline

Let `u(t)` be a smooth curve on `S^{d-1}` with `u(0) = u` and `u'(0) = v ∈ T_u S^{d-1}`.
The Riemannian gradient is `grad f(u(t)) = P_{u(t)}^⊥ ∇f(u(t))`.

Differentiating at `t = 0` and projecting back onto `T_u S^{d-1}`:

  `D_v [grad f(u)] = P_u^⊥ [∇²f(u) v - ⟨∇f(u), u⟩ v - ⟨∇f(u), v⟩ u]`
                  `= P_u^⊥ [∇²f(u) - ⟨∇f(u), u⟩ I] v`   (since `P_u^⊥ u = 0`)

## Formalization

We work algebraically: given `u : E` with `‖u‖ = 1`, a "Hessian map" `H : E →L[ℝ] E`
(representing `∇²f(u)`), and a "gradient vector" `g : E` (representing `∇f(u)`), we define
and prove the key properties of the Riemannian Hessian operator.

## References
- Book: deep-representation-learning-book, Chapter 2, exercise:sphere-calculus Part 3
- See also: Chapter2_Exercise2_6_1.lean (tangent space and projection)
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Definition of the Riemannian Hessian -/

/-- The Riemannian Hessian operator at `u ∈ S^{d-1}`.
    Given the Hessian map `H` and gradient vector `g` of `f` at `u`:
    `Hess_f(u) v = P_u^⊥ ((H - ⟨g, u⟩ · id) (P_u^⊥ v))`
    This is the formula `P_u^⊥ (∇²f - ⟨∇f, u⟩ I) P_u^⊥` applied to `v`. -/
noncomputable def riemHess (u : E) (H : E →L[ℝ] E) (g : E) (v : E) : E :=
  (ℝ ∙ u)ᗮ.starProjection
    (H ((ℝ ∙ u)ᗮ.starProjection v) - (inner ℝ g u : ℝ) • (ℝ ∙ u)ᗮ.starProjection v)

/-! ### Key helper: the projection kills u itself -/

/-- For a unit vector `u`, the projection onto the tangent space satisfies `P_u^⊥ u = 0`. -/
private lemma proj_perp_unit_eq_zero (u : E) (hu : ‖u‖ = 1) :
    (ℝ ∙ u)ᗮ.starProjection u = 0 := by
  rw [sphere_tangent_projection_explicit u hu, real_inner_self_eq_norm_sq, hu,
      one_pow, one_smul, sub_self]

/-! ### Properties of the Riemannian Hessian -/

/-- **Property 1**: The Riemannian Hessian kills the normal direction `u`.
    This reflects that `u ∉ T_u S^{d-1}` and `P_u^⊥ u = 0`. -/
theorem riemHess_kills_u (u : E) (hu : ‖u‖ = 1) (H : E →L[ℝ] E) (g : E) :
    riemHess u H g u = 0 := by
  simp only [riemHess, proj_perp_unit_eq_zero u hu, map_zero, smul_zero, sub_self]

/-- **Property 2**: The Riemannian Hessian maps into the tangent space `T_u S^{d-1}`.
    Equivalently, `⟨Hess_f(u) v, u⟩ = 0` for all `v`. -/
theorem riemHess_in_tangent (u : E) (hu : ‖u‖ = 1) (H : E →L[ℝ] E) (g : E) (v : E) :
    inner ℝ (riemHess u H g v) u = (0 : ℝ) :=
  sphere_tangent_projection_range u hu _

/-- **Property 3**: On the tangent space, `riemHess` simplifies to `P_u^⊥ (H v - ⟨g, u⟩ · v)`.
    For `v ⊥ u`, the inner `P_u^⊥` acts as the identity, giving a cleaner formula. -/
theorem riemHess_on_tangent (u : E) (hu : ‖u‖ = 1) (H : E →L[ℝ] E) (g : E)
    (v : E) (hv : inner ℝ v u = (0 : ℝ)) :
    riemHess u H g v = (ℝ ∙ u)ᗮ.starProjection (H v - (inner ℝ g u : ℝ) • v) := by
  simp only [riemHess, sphere_tangent_projection_identity_on_tangent u hu v hv]

/-- **Property 4**: The Riemannian Hessian is symmetric on the tangent space
    whenever the Euclidean Hessian `H` is self-adjoint.
    `⟨Hess_f(u) v, w⟩ = ⟨v, Hess_f(u) w⟩` for all `v, w ∈ T_u S^{d-1}`. -/
theorem riemHess_symmetric (u : E) (hu : ‖u‖ = 1) (H : E →L[ℝ] E) (g : E)
    (hH : ∀ a b : E, inner ℝ (H a) b = inner ℝ a (H b))
    (v w : E) (hv : inner ℝ v u = (0 : ℝ)) (hw : inner ℝ w u = (0 : ℝ)) :
    inner ℝ (riemHess u H g v) w = inner ℝ v (riemHess u H g w) := by
  rw [riemHess_on_tangent u hu H g v hv, riemHess_on_tangent u hu H g w hw]
  -- Simplify LHS: ⟨P(Hv - c·v), w⟩ = ⟨Hv - c·v, Pw⟩ = ⟨Hv - c·v, w⟩  (P self-adjoint, Pw = w)
  have lhs_eq : inner ℝ ((ℝ ∙ u)ᗮ.starProjection (H v - (inner ℝ g u : ℝ) • v)) w =
                inner ℝ (H v - (inner ℝ g u : ℝ) • v) w := by
    rw [sphere_tangent_projection_symmetric u hu,
        sphere_tangent_projection_identity_on_tangent u hu w hw]
  -- Simplify RHS: ⟨v, P(Hw - c·w)⟩ = ⟨Pv, Hw - c·w⟩ = ⟨v, Hw - c·w⟩  (Pv = v)
  have rhs_eq : inner ℝ v ((ℝ ∙ u)ᗮ.starProjection (H w - (inner ℝ g u : ℝ) • w)) =
                inner ℝ v (H w - (inner ℝ g u : ℝ) • w) := by
    rw [← sphere_tangent_projection_symmetric u hu v,
        sphere_tangent_projection_identity_on_tangent u hu v hv]
  rw [lhs_eq, rhs_eq]
  -- Goal: ⟨Hv - c·v, w⟩ = ⟨v, Hw - c·w⟩
  -- Expand: ⟨Hv, w⟩ - c·⟨v,w⟩ = ⟨v, Hw⟩ - c·⟨v,w⟩, using self-adjointness of H
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
  -- `starRingEnd ℝ` is the identity; use norm_num to handle the ring arithmetic
  rw [show (starRingEnd ℝ) (inner ℝ g u) = inner ℝ g u from rfl]
  linarith [hH v w]
