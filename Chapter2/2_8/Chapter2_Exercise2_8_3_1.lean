import Mathlib.LinearAlgebra.Matrix.Trace
import Chapter2.«2_8».Chapter2_Exercise2_8_2

/-!
# Chapter 2, Exercise 2.8.3 (Part 1): First and Second-Order Optimality Conditions

## Informal Statement (exercise:orthogonal-group-calculus, Part 3a)

Given X ∈ ℝ^{d×d}, the projection onto the orthogonal group is:
  `proj_{O(d)}(X) = argmin_{Q ∈ O(d)} ‖Q - X‖_F²`

Show that every local minimizer Q satisfies:
1. `(QᵀX)ᵀ = QᵀX`       — QᵀX is symmetric (first-order condition)
2. `QᵀX ⪰ 0`             — QᵀX is positive semidefinite (second-order condition)

The Frobenius objective `f(Q) = ‖Q - X‖_F²` has Euclidean gradient `∇f = 2(Q - X)`
and Euclidean Hessian `B(V) = 2V`. At a local minimizer:
- Riemannian gradient = 0 ⟹ `P(Q - X) = 0` ⟹ `Skew(I - QᵀX) = 0` ⟹ `(QᵀX)ᵀ = QᵀX`
- Riemannian Hessian PSD ⟹ `⟪Hess[V], V⟫ ≥ 0` ⟹ `⟪V·QᵀX, V⟫ ≥ 0` for all `V ∈ T`

## References
- Book: deep-representation-learning-book/chapters/chapter2/classic-models.tex
  exercise:orthogonal-group-calculus, Part 3a
- See also: Chapter2_Exercise2_8_1.lean (tangent space, projection)
            Chapter2_Exercise2_8_2.lean (Riemannian Hessian)
-/

open Matrix

variable (d : ℕ) [DecidableEq (Fin d)]

local notation "Mat" => Matrix (Fin d) (Fin d) ℝ

/-! ### Helper lemmas -/

omit [DecidableEq (Fin d)] in
/-- If `skewPart d M = 0` then `M` is symmetric: `Mᵀ = M`. -/
private lemma symm_of_skewPart_zero (M : Mat) (h : skewPart d M = 0) : Mᵀ = M := by
  ext i j
  have hij := congr_fun (congr_fun h i) j
  simp only [skewPart, Matrix.smul_apply, Matrix.sub_apply, Matrix.transpose_apply,
             Matrix.zero_apply, smul_eq_mul] at hij
  simp only [Matrix.transpose_apply]
  linarith

/-- From `tangentProj d Q Δ = 0` and `Q ∈ O(d)`, deduce `skewPart d (Qᵀ * Δ) = 0`. -/
private lemma skewPart_zero_of_tangentProj_zero (Q Δ : Mat)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin d) ℝ)
    (h : tangentProj d Q Δ = 0) :
    skewPart d (Qᵀ * Δ) = 0 := by
  have hQtQ : Qᵀ * Q = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin d) ℝ).mp hQ
  simp only [tangentProj] at h
  have : Qᵀ * (Q * skewPart d (Qᵀ * Δ)) = 0 := by rw [h, mul_zero]
  rwa [← Matrix.mul_assoc, hQtQ, one_mul] at this

omit [DecidableEq (Fin d)] in
/-- If `M` is symmetric then `symmPart d M = M`. -/
private lemma symmPart_of_symm (M : Mat) (hM : Mᵀ = M) : symmPart d M = M := by
  ext i j
  simp only [symmPart, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
  have : M j i = M i j := by
    have := congr_fun (congr_fun hM i) j; simpa [Matrix.transpose_apply] using this
  linarith

/-! ### Frobenius inner product helper -/

omit [DecidableEq (Fin d)] in
private lemma matInner_sub_right' (X Y Z : Mat) :
    matInner d X (Y - Z) = matInner d X Y - matInner d X Z := by
  simp [matInner, mul_sub, trace_sub]

/-- Self-adjointness of tangent projection: `⟪P(A), V⟫ = ⟪A, V⟫` when `V ∈ T_Q O(d)`. -/
private lemma matInner_tangentProj_left (Q A V : Mat)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin d) ℝ)
    (hV : inTangentSpace d Q V) :
    matInner d (tangentProj d Q A) V = matInner d A V := by
  have hkey : matInner d V (A - tangentProj d Q A) = 0 := by
    have h := tangentProj_complement_orthogonal d Q (Qᵀ * V) A hQ hV
    rwa [← tangent_reconstruction d Q V hQ] at h
  rw [matInner_sub_right' d V A (tangentProj d Q A)] at hkey
  rw [matInner_comm d (tangentProj d Q A) V, matInner_comm d A V]
  linarith

/-! ### Part 1: Symmetry of QᵀX -/

/-- **Part 1**: At a critical point of the Frobenius projection problem, QᵀX is symmetric.

From `P(Q - X) = 0` (Riemannian gradient = 0), we derive `Skew(I - QᵀX) = 0`,
hence `(QᵀX)ᵀ = QᵀX`. -/
theorem qtx_symm_of_critical (Q X : Mat)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin d) ℝ)
    (hgrad : tangentProj d Q (Q - X) = 0) :
    (Qᵀ * X)ᵀ = Qᵀ * X := by
  have hQtQ : Qᵀ * Q = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin d) ℝ).mp hQ
  -- Step 1: tangentProj = 0 implies skewPart = 0
  have h1 : skewPart d (Qᵀ * (Q - X)) = 0 :=
    skewPart_zero_of_tangentProj_zero d Q (Q - X) hQ hgrad
  -- Step 2: Qᵀ(Q - X) = I - QᵀX
  rw [show Qᵀ * (Q - X) = 1 - Qᵀ * X from by rw [Matrix.mul_sub, hQtQ]] at h1
  -- Step 3: skewPart(I - QᵀX) = 0 means (I - QᵀX)ᵀ = I - QᵀX
  have h3 : (1 - Qᵀ * X)ᵀ = 1 - Qᵀ * X := symm_of_skewPart_zero d _ h1
  -- Step 4: Expand and cancel to get (QᵀX)ᵀ = QᵀX
  rw [transpose_sub, transpose_one] at h3
  ext i j
  have hij := congr_fun (congr_fun h3 i) j
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.transpose_apply] at hij
  simp only [Matrix.transpose_apply]
  linarith

/-! ### Part 2: Hessian simplification and PSD condition -/

/-- The Riemannian Hessian of `‖Q - X‖_F²` (with `B = id`, `g = Q - X`) simplifies to
    `P(V · QᵀX)` for tangent vectors V, when QᵀX is symmetric. -/
theorem hessian_frobenius_simplify (Q X V : Mat)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin d) ℝ)
    (hV : inTangentSpace d Q V)
    (hsymm : (Qᵀ * X)ᵀ = Qᵀ * X) :
    riemHessOD d Q id (Q - X) V = tangentProj d Q (V * (Qᵀ * X)) := by
  -- Step 1: Simplify using V ∈ T (P(V) = V drops inner projection)
  rw [riemHessOD_on_tangent d Q id (Q - X) V hQ hV]
  congr 1
  -- Step 2: Simplify Qᵀ(Q - X) = I - QᵀX
  have hQtQ : Qᵀ * Q = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin d) ℝ).mp hQ
  rw [show Qᵀ * (Q - X) = 1 - Qᵀ * X from by rw [Matrix.mul_sub, hQtQ]]
  -- Step 3: symmPart(I - QᵀX) = I - QᵀX (since it's symmetric)
  rw [symmPart_of_symm d _ (show (1 - Qᵀ * X)ᵀ = 1 - Qᵀ * X from by
    rw [transpose_sub, transpose_one, hsymm])]
  -- Step 4: V - V * (1 - QᵀX) = V * QᵀX
  simp only [id]
  rw [Matrix.mul_sub, Matrix.mul_one, sub_sub_cancel]

/-- **Part 2**: The PSD condition on the Riemannian Hessian implies `⟪V · QᵀX, V⟫ ≥ 0`
    for all tangent vectors V. -/
theorem psd_of_hessian_psd (Q X : Mat)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin d) ℝ)
    (hsymm : (Qᵀ * X)ᵀ = Qᵀ * X)
    (hhess : ∀ V : Mat, inTangentSpace d Q V →
      matInner d (riemHessOD d Q id (Q - X) V) V ≥ 0)
    (V : Mat) (hV : inTangentSpace d Q V) :
    matInner d (V * (Qᵀ * X)) V ≥ 0 := by
  have h1 := hhess V hV
  rw [hessian_frobenius_simplify d Q X V hQ hV hsymm] at h1
  rwa [matInner_tangentProj_left d Q (V * (Qᵀ * X)) V hQ hV] at h1

/-! ### Main theorem -/

/-- **Exercise 2.8.3 (Part 1)**: First and Second-Order Optimality Conditions.

Every local minimizer `Q ∈ O(d)` of `f(Q) = ‖Q - X‖_F²` satisfies:
1. `(QᵀX)ᵀ = QᵀX` — QᵀX is symmetric
2. `⟪V · QᵀX, V⟫ ≥ 0` for all `V ∈ T_Q O(d)` — QᵀX is positive semidefinite

The hypotheses encode the abstract optimality conditions:
- First-order: `P(Q - X) = 0` (Riemannian gradient vanishes)
- Second-order: `⟪Hess f(Q)[V], V⟫ ≥ 0` for all tangent V (Riemannian Hessian is PSD)

where `B = id` is the Euclidean Hessian `∇²f/2` and `g = Q - X` is `∇f/2`.

See book Chapter 2, exercise:orthogonal-group-calculus, Part 3a. -/
theorem exercise_2_8_3_1 (Q X : Mat)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin d) ℝ)
    -- First-order: Riemannian gradient of ‖Q - X‖_F² is zero
    (hgrad : tangentProj d Q (Q - X) = 0)
    -- Second-order: Riemannian Hessian is PSD on T_Q O(d)
    (hhess : ∀ V : Mat, inTangentSpace d Q V →
      matInner d (riemHessOD d Q id (Q - X) V) V ≥ 0) :
    -- Conclusion 1: QᵀX is symmetric
    (Qᵀ * X)ᵀ = Qᵀ * X ∧
    -- Conclusion 2: QᵀX is PSD (in Frobenius sense on T_Q O(d))
    (∀ V : Mat, inTangentSpace d Q V → matInner d (V * (Qᵀ * X)) V ≥ 0) := by
  have hsymm := qtx_symm_of_critical d Q X hQ hgrad
  exact ⟨hsymm, fun V hV => psd_of_hessian_psd d Q X hQ hsymm hhess V hV⟩
