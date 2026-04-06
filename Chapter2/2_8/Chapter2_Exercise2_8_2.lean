import Mathlib.LinearAlgebra.Matrix.Trace
import Chapter2.«2_8».Chapter2_Exercise2_8_1

/-!
# Chapter 2, Exercise 2.8.2: Riemannian Hessian for Orthogonal Group Optimization

## Informal Statement (exercise:orthogonal-group-calculus, Part 2)

For `f : ℝ^{d×d} → ℝ` twice-continuously-differentiable, the **Riemannian Hessian**
at `Q ∈ O(d)` acting on tangent vectors is:

  `Hess f(Q) = P_{T_Q O(d)} (∇²f(Q) - Symm(Qᵀ ∇f(Q)) ⊗ I) P_{T_Q O(d)}`

where:
- `P_{T_Q O(d)}(Δ) = Q · Skew(Qᵀ Δ)` is the tangent projection (from Exercise 2.8.1)
- `Symm(Δ) = (1/2)(Δ + Δᵀ)` is the symmetric part
- The Kronecker operator `Symm(Qᵀg) ⊗ I` acts on matrix `V` as right multiplication: `V ↦ V · Symm(Qᵀg)`

## Derivation sketch

Let `Q(t)` be a smooth curve on `O(d)` with `Q(0) = Q`, `Q'(0) = V = Q·Ω`
(so `V ∈ T_Q O(d)` and `Ω = QᵀV` is skew-symmetric).

The Riemannian gradient is `grad f(Q(t)) = Q(t) · Skew(Q(t)ᵀ ∇f(Q(t)))`.
Differentiating at `t = 0` and projecting onto `T_Q O(d)`:

  `D_V[grad f(Q)] = P[ Q · Skew(Qᵀ (∇²f · V) - Ω · Symm(Qᵀ g)) ]`

which, after simplification using `V = Q·Ω` and the fact that `P[Q·Ω·Skew(S)] = Q·Skew(Ω·Skew(S))`:

  `= P[ ∇²f · V - V · Symm(Qᵀ g) ]`

## Formalization

We model `∇²f(Q)` as an abstract operator `B : Mat → Mat` (self-adjoint w.r.t. Frobenius)
and `∇f(Q)` as `g : Mat`, and prove the key algebraic properties.

## References
- Book: deep-representation-learning-book/chapters/chapter2/classic-models.tex
  exercise:orthogonal-group-calculus, Part 2
- See also: Chapter2_Exercise2_8_1.lean (tangent space and projection)
            Chapter2_Exercise2_6_3.lean (analogous results for the sphere)
-/

open Matrix

variable (d : ℕ) [DecidableEq (Fin d)]

local notation "Mat" => Matrix (Fin d) (Fin d) ℝ

/-! ### Symmetric part -/

/-- Symmetric part: `Symm(Δ) = (1/2)(Δ + Δᵀ)`. -/
noncomputable def symmPart (Δ : Mat) : Mat := (1 / 2 : ℝ) • (Δ + Δᵀ)

omit [DecidableEq (Fin d)] in
/-- `Symm(Δ)ᵀ = Symm(Δ)` — the symmetric part is symmetric. -/
lemma symmPart_transpose (Δ : Mat) : (symmPart d Δ)ᵀ = symmPart d Δ := by
  simp only [symmPart, transpose_smul, transpose_add, transpose_transpose, add_comm]

omit [DecidableEq (Fin d)] in
/-- `Δ - Skew(Δ) = Symm(Δ)` — skew and symmetric parts decompose the matrix. -/
lemma sub_skewPart_eq_symmPart (Δ : Mat) : Δ - skewPart d Δ = symmPart d Δ := by
  ext i j
  simp [skewPart, symmPart, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.add_apply, Matrix.transpose_apply]
  ring

/-! ### Frobenius inner product bilinearity -/

omit [DecidableEq (Fin d)] in
private lemma matInner_sub_left (X Y Z : Mat) :
    matInner d (X - Y) Z = matInner d X Z - matInner d Y Z := by
  simp [matInner, transpose_sub, sub_mul, trace_sub]

omit [DecidableEq (Fin d)] in
private lemma matInner_sub_right (X Y Z : Mat) :
    matInner d X (Y - Z) = matInner d X Y - matInner d X Z := by
  simp [matInner, mul_sub, trace_sub]

omit [DecidableEq (Fin d)] in
/-- `⟪V·S, W⟫_F = ⟪V, W·S⟫_F` when `S` is symmetric (via trace cyclicity). -/
lemma matInner_mul_right_symm (V W S : Mat) (hS : Sᵀ = S) :
    matInner d (V * S) W = matInner d V (W * S) := by
  unfold matInner
  calc ((V * S)ᵀ * W).trace
      = (S * Vᵀ * W).trace       := by rw [transpose_mul, hS]
    _ = (S * (Vᵀ * W)).trace     := by rw [Matrix.mul_assoc]
    _ = (Vᵀ * W * S).trace       := by rw [trace_mul_comm]
    _ = (Vᵀ * (W * S)).trace     := by rw [Matrix.mul_assoc]

/-! ### Self-adjointness of the tangent projection -/

/-- For `W ∈ T_Q O(d)`: `⟪P(X), W⟫_F = ⟪X, W⟫_F`.
    The projection is self-adjoint w.r.t. Frobenius: residual `X - P(X)` is orthogonal to T. -/
private lemma matInner_proj_left (Q X W : Mat)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin d) ℝ)
    (hW : inTangentSpace d Q W) :
    matInner d (tangentProj d Q X) W = matInner d X W := by
  -- W = Q·(QᵀW) with QᵀW skew, so tangentProj_complement_orthogonal gives ⟪W, X - P(X)⟫ = 0
  have key : matInner d W (X - tangentProj d Q X) = 0 := by
    have h := tangentProj_complement_orthogonal d Q (Qᵀ * W) X hQ hW
    rwa [← tangent_reconstruction d Q W hQ] at h
  have expand : matInner d W (X - tangentProj d Q X) =
      matInner d W X - matInner d W (tangentProj d Q X) :=
    matInner_sub_right d W X (tangentProj d Q X)
  rw [matInner_comm d (tangentProj d Q X) W, matInner_comm d X W]
  linarith

/-- For `V ∈ T_Q O(d)`: `⟪V, P(X)⟫_F = ⟪V, X⟫_F`. -/
private lemma matInner_proj_right (Q X V : Mat)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin d) ℝ)
    (hV : inTangentSpace d Q V) :
    matInner d V (tangentProj d Q X) = matInner d V X := by
  rw [matInner_comm, matInner_proj_left d Q X V hQ hV, matInner_comm]

/-! ### Riemannian Hessian definition -/

/-- The Riemannian Hessian at `Q ∈ O(d)`, applied to tangent vector `V`:

  `riemHessOD B g V = P(B(P(V)) - P(V) · Symm(Qᵀg))`

This is the formula `P (∇²f - Symm(Qᵀ∇f) ⊗ I) P` applied to `V`, where the Kronecker
operator `Symm(Qᵀg) ⊗ I` acts as right matrix multiplication: `V ↦ V · Symm(Qᵀg)`. -/
noncomputable def riemHessOD (Q : Mat) (B : Mat → Mat) (g V : Mat) : Mat :=
  tangentProj d Q (B (tangentProj d Q V) - tangentProj d Q V * symmPart d (Qᵀ * g))

/-! ### Properties -/

/-- **Property 1**: `riemHessOD` maps into the tangent space `T_Q O(d)`. -/
theorem riemHessOD_in_tangent (Q : Mat) (B : Mat → Mat) (g V : Mat)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin d) ℝ) :
    inTangentSpace d Q (riemHessOD d Q B g V) :=
  tangentProj_in_tangentSpace d Q _ hQ

/-- **Property 2**: For tangent vectors `V ∈ T_Q O(d)`, the formula simplifies to
    `P(B(V) - V · Symm(Qᵀg))` (the inner projection `P(V) = V` drops out). -/
theorem riemHessOD_on_tangent (Q : Mat) (B : Mat → Mat) (g V : Mat)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin d) ℝ)
    (hV : inTangentSpace d Q V) :
    riemHessOD d Q B g V = tangentProj d Q (B V - V * symmPart d (Qᵀ * g)) := by
  simp only [riemHessOD, tangentProj_idempotent d Q V hQ hV]

/-- **Property 3**: The Riemannian Hessian is symmetric on `T_Q O(d)` when `B` is
    self-adjoint w.r.t. the Frobenius inner product `⟪X, Y⟫ = tr(XᵀY)`:

    `⟪Hess f(Q)[V], W⟫ = ⟪V, Hess f(Q)[W]⟫`  for all `V, W ∈ T_Q O(d)`. -/
theorem riemHessOD_symmetric (Q : Mat) (B : Mat → Mat) (g V W : Mat)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin d) ℝ)
    (hB : ∀ X Y : Mat, matInner d (B X) Y = matInner d X (B Y))
    (hV : inTangentSpace d Q V)
    (hW : inTangentSpace d Q W) :
    matInner d (riemHessOD d Q B g V) W = matInner d V (riemHessOD d Q B g W) := by
  rw [riemHessOD_on_tangent d Q B g V hQ hV, riemHessOD_on_tangent d Q B g W hQ hW]
  set S := symmPart d (Qᵀ * g)
  have hS : Sᵀ = S := symmPart_transpose d _
  -- Self-adjointness of P: ⟪P(X), W⟫ = ⟪X, W⟫ for W ∈ T_Q,  ⟪V, P(Y)⟫ = ⟪V, Y⟫ for V ∈ T_Q
  rw [matInner_proj_left d Q (B V - V * S) W hQ hW,
      matInner_proj_right d Q (B W - W * S) V hQ hV]
  -- Goal: ⟪BV - VS, W⟫ = ⟪V, BW - WS⟫
  rw [matInner_sub_left d (B V) (V * S) W, matInner_sub_right d V (B W) (W * S)]
  -- Self-adjointness of B: ⟪BV, W⟫ = ⟪V, BW⟫
  have h1 : matInner d (B V) W = matInner d V (B W) := hB V W
  -- Symmetric trace lemma: ⟪VS, W⟫ = ⟪V, WS⟫ since Sᵀ = S
  have h2 : matInner d (V * S) W = matInner d V (W * S) :=
    matInner_mul_right_symm d V W S hS
  linarith

/-! ### Main theorem -/

/-- **Exercise 2.8.2**: Riemannian Hessian Formula for O(d).

For `Q ∈ O(d)`, objective `B` (representing `∇²f(Q)`) self-adjoint w.r.t. Frobenius, and
`g` (representing `∇f(Q)`), the Riemannian Hessian operator

  `Hess f(Q)[V] = P(B(P(V)) - P(V) · Symm(Qᵀg))`

satisfies:
1. **Definition** — matches the book formula with the Kronecker product action
2. **Tangent-space valued** — `Hess f(Q)[V] ∈ T_Q O(d)` for all `V`
3. **Simplified form** — for `V ∈ T_Q O(d)`: `Hess f(Q)[V] = P(B(V) - V · Symm(Qᵀg))`
4. **Symmetry** — `⟪Hess f(Q)[V], W⟫ = ⟪V, Hess f(Q)[W]⟫` for `V, W ∈ T_Q O(d)`

See book Chapter 2, exercise:orthogonal-group-calculus, Part 2. -/
theorem exercise_2_8_2 (Q : Mat) (hQ : Q ∈ Matrix.orthogonalGroup (Fin d) ℝ)
    (B : Mat → Mat) (g : Mat)
    (hB : ∀ X Y : Mat, matInner d (B X) Y = matInner d X (B Y)) :
    -- 1. Definition: matches formula with P(V) and Symm(Qᵀg) ⊗ I = right-mult by Symm(Qᵀg)
    (∀ V : Mat, riemHessOD d Q B g V =
      tangentProj d Q (B (tangentProj d Q V) - tangentProj d Q V * symmPart d (Qᵀ * g))) ∧
    -- 2. Maps into T_Q O(d)
    (∀ V : Mat, inTangentSpace d Q (riemHessOD d Q B g V)) ∧
    -- 3. Simplified on tangent vectors
    (∀ V : Mat, inTangentSpace d Q V →
      riemHessOD d Q B g V = tangentProj d Q (B V - V * symmPart d (Qᵀ * g))) ∧
    -- 4. Symmetry
    (∀ V W : Mat, inTangentSpace d Q V → inTangentSpace d Q W →
      matInner d (riemHessOD d Q B g V) W = matInner d V (riemHessOD d Q B g W)) :=
  ⟨fun _ => rfl,
   fun V => riemHessOD_in_tangent d Q B g V hQ,
   fun V hV => riemHessOD_on_tangent d Q B g V hQ hV,
   fun V W hV hW => riemHessOD_symmetric d Q B g V W hQ hB hV hW⟩
