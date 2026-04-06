import Chapter2.«2_8».Chapter2_Exercise2_8_3_2

/-!
# Chapter 2, Exercise 2.8.3 (Part 3): SVD gives the projection onto O(d)

## Informal Statement (exercise:orthogonal-group-calculus, Part 3c)

Given the SVD `X = U S Vᵀ` where `U, V ∈ O(d)` and `S` is diagonal with nonneg entries,
conclude that `UV^T = proj_{O(d)}(X)`.

## Proof Sketch

From Exercise 2.8.3.2, every local minimizer `Q` satisfies `QᵀX = (XᵀX)^{1/2}`.

We show directly that `Q₀ = UVᵀ` satisfies the **first-order optimality condition**:
  `tangentProj d Q₀ (Q₀ - X) = 0`

**Step 1**: `Q₀ ∈ O(d)` — product of orthogonal matrices.

**Step 2**: Compute `Q₀ᵀ X`:
  ```
  Q₀ᵀ X = (UVᵀ)ᵀ (USVᵀ) = VUᵀ · U · S · Vᵀ = V · (UᵀU) · S · Vᵀ = V · S · Vᵀ
  ```

**Step 3**: `VSVᵀ` is symmetric when `S` is symmetric (diagonal `S = Sᵀ`).

**Step 4**: From `skewPart d (Q₀ᵀQ₀ - Q₀ᵀX) = 0`:
  - `Q₀ᵀQ₀ = I` (since Q₀ ∈ O(d))
  - `Q₀ᵀX = VSVᵀ` is symmetric, so `I - VSVᵀ` is symmetric
  - Hence `skewPart = 0`, so `tangentProj = 0`.

**Step 5**: The PSD condition `⟪V · Q₀ᵀX, V⟫ ≥ 0` for tangent V, since S diagonal with
nonneg diagonal entries implies VSVᵀ is PSD (via `⟪Vw, (VSVᵀ)Vw⟫ ≥ 0`).

## Formalization Note

We axiomatize "S is diagonal nonneg" via `hS_symm : Sᵀ = S` (symmetry of S, equivalent to
diagonal for diagonal matrices) and `hS_psd : ∀ w : Mat, matInner d (w * S) w ≥ 0` (PSD).

The projection `UV^T = proj_{O(d)}(X)` is formalized as: `UVᵀ` satisfies the first-order
conditions from Exercise 2.8.3.1 (gradient = 0) and the second-order conditions (Hessian PSD).

## References
- Book: deep-representation-learning-book/chapters/chapter2/classic-models.tex
  exercise:orthogonal-group-calculus, Part 3c
- See also: Chapter2_Exercise2_8_3_1.lean, Chapter2_Exercise2_8_3_2.lean
-/

open Matrix

variable (d : ℕ) [DecidableEq (Fin d)]

local notation "Mat" => Matrix (Fin d) (Fin d) ℝ

/-! ### Step 1: Product of orthogonal matrices is orthogonal -/

/-- The product `U * Vᵀ` is in `O(d)` when both `U` and `V` are. -/
lemma orthogonal_mul_transpose (U V : Mat)
    (hU : U ∈ Matrix.orthogonalGroup (Fin d) ℝ)
    (hV : V ∈ Matrix.orthogonalGroup (Fin d) ℝ) :
    U * Vᵀ ∈ Matrix.orthogonalGroup (Fin d) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  have hUUt : U * Uᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).mp hU
  have hVtV : Vᵀ * V = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin d) ℝ).mp hV
  calc U * Vᵀ * (U * Vᵀ)ᵀ
      = U * Vᵀ * (V * Uᵀ) := by rw [transpose_mul, transpose_transpose]
    _ = U * (Vᵀ * V) * Uᵀ := by
        rw [← Matrix.mul_assoc (U * Vᵀ) V Uᵀ, Matrix.mul_assoc U Vᵀ V]
    _ = U * 1 * Uᵀ := by rw [hVtV]
    _ = U * Uᵀ := by rw [Matrix.mul_one]
    _ = 1 := hUUt

/-! ### Step 2: Q₀ᵀ X = V S Vᵀ when X = U S Vᵀ and Q₀ = U Vᵀ -/

/-- When `X = U * S * Vᵀ` and `Q₀ = U * Vᵀ`, we have `Q₀ᵀ * X = V * S * Vᵀ`. -/
lemma qtx_eq_vsvt (U V S : Mat)
    (hU : U ∈ Matrix.orthogonalGroup (Fin d) ℝ) :
    (U * Vᵀ)ᵀ * (U * S * Vᵀ) = V * S * Vᵀ := by
  have hUtU : Uᵀ * U = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin d) ℝ).mp hU
  rw [transpose_mul, transpose_transpose]
  -- V * Uᵀ * (U * S * Vᵀ)
  rw [show V * Uᵀ * (U * S * Vᵀ) = V * (Uᵀ * U) * S * Vᵀ from by simp [Matrix.mul_assoc],
      hUtU, Matrix.mul_one]

/-! ### Step 3: VSVᵀ is symmetric when S is symmetric -/

omit [DecidableEq (Fin d)] in
/-- `(V * S * Vᵀ)ᵀ = V * S * Vᵀ` when `Sᵀ = S`. -/
lemma vsvt_symm (V S : Mat) (hS : Sᵀ = S) : (V * S * Vᵀ)ᵀ = V * S * Vᵀ := by
  rw [transpose_mul, transpose_mul, transpose_transpose, hS, ← Matrix.mul_assoc]

/-! ### Step 4: First-order condition — tangent projection of gradient vanishes -/

omit [DecidableEq (Fin d)] in
/-- A matrix is symmetric iff its skewPart is zero. -/
private lemma skewPart_zero_iff_symm (M : Mat) : skewPart d M = 0 ↔ Mᵀ = M := by
  constructor
  · intro h
    ext i j
    have hij := congr_fun (congr_fun h i) j
    simp only [skewPart, Matrix.smul_apply, Matrix.sub_apply, Matrix.transpose_apply,
               Matrix.zero_apply, smul_eq_mul] at hij
    simp only [Matrix.transpose_apply]
    linarith
  · intro h
    ext i j
    simp only [skewPart, Matrix.smul_apply, Matrix.sub_apply, Matrix.transpose_apply,
               Matrix.zero_apply, smul_eq_mul]
    have : M j i = M i j := by
      have := congr_fun (congr_fun h i) j; simpa [Matrix.transpose_apply] using this
    linarith

/-- When `Q₀ = UVᵀ ∈ O(d)` and `Q₀ᵀX = VSVᵀ` is symmetric, the tangent projection of
    the gradient vanishes: `tangentProj d Q₀ (Q₀ - X) = 0`. -/
lemma tangentProj_grad_zero (U V S X : Mat)
    (hU : U ∈ Matrix.orthogonalGroup (Fin d) ℝ)
    (hV : V ∈ Matrix.orthogonalGroup (Fin d) ℝ)
    (hX : X = U * S * Vᵀ)
    (hS_symm : Sᵀ = S) :
    let Q₀ := U * Vᵀ
    tangentProj d Q₀ (Q₀ - X) = 0 := by
  simp only []
  set Q₀ := U * Vᵀ
  have hQ₀ : Q₀ ∈ Matrix.orthogonalGroup (Fin d) ℝ := orthogonal_mul_transpose d U V hU hV
  have hQ₀tQ₀ : Q₀ᵀ * Q₀ = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin d) ℝ).mp hQ₀
  -- Compute Q₀ᵀ(Q₀ - X) = I - Q₀ᵀX = I - VSVᵀ
  have hQtX : Q₀ᵀ * X = V * S * Vᵀ := by
    rw [hX]; exact qtx_eq_vsvt d U V S hU
  -- tangentProj d Q₀ (Q₀ - X) = Q₀ · skewPart(Q₀ᵀ(Q₀ - X))
  rw [tangentProj]
  -- Q₀ᵀ(Q₀ - X) = I - VSVᵀ
  have hkey : Q₀ᵀ * (Q₀ - X) = 1 - V * S * Vᵀ := by
    rw [Matrix.mul_sub, hQ₀tQ₀, hQtX]
  rw [hkey]
  -- skewPart(I - VSVᵀ) = 0 since I - VSVᵀ is symmetric
  have hsymm : (1 - V * S * Vᵀ)ᵀ = 1 - V * S * Vᵀ := by
    rw [transpose_sub, transpose_one, vsvt_symm d V S hS_symm]
  rw [(skewPart_zero_iff_symm d _).mpr hsymm, Matrix.mul_zero]

/-! ### Helper: self-adjointness of tangent projection -/

/-- `⟪P(Y), W⟫ = ⟪Y, W⟫` when `W ∈ T_Q O(d)`. -/
private lemma matInner_tangentProj_left' (Q Y W : Mat)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin d) ℝ)
    (hW : inTangentSpace d Q W) :
    matInner d (tangentProj d Q Y) W = matInner d Y W := by
  have hkey : matInner d W (Y - tangentProj d Q Y) = 0 := by
    have h := tangentProj_complement_orthogonal d Q (Qᵀ * W) Y hQ hW
    rwa [← tangent_reconstruction d Q W hQ] at h
  simp only [matInner]
  -- hkey says matInner W (Y - P(Y)) = 0, i.e. (Wᵀ*(Y - P(Y))).trace = 0
  simp only [matInner, Matrix.mul_sub, trace_sub, sub_eq_zero] at hkey
  -- hkey: (Wᵀ * Y).trace = (Wᵀ * P(Y)).trace
  -- Need: (P(Y)ᵀ * W).trace = (Yᵀ * W).trace
  -- tr(P(Y)ᵀ * W) = tr((Wᵀ * P(Y))ᵀ) = tr(Wᵀ * P(Y)) = tr(Wᵀ * Y) = tr(Yᵀ * W)
  have h1 : ((tangentProj d Q Y)ᵀ * W).trace = (Wᵀ * tangentProj d Q Y).trace := by
    rw [← trace_transpose ((tangentProj d Q Y)ᵀ * W), transpose_mul, transpose_transpose]
  have h2 : (Yᵀ * W).trace = (Wᵀ * Y).trace := by
    rw [← trace_transpose (Yᵀ * W), transpose_mul, transpose_transpose]
  linarith

/-! ### Step 5: Second-order condition — Hessian PSD -/

/-- When S is PSD (`⟪WS, W⟫ ≥ 0`), the second-order condition holds for Q₀ = UVᵀ. -/
lemma hessian_psd_uvt (U V S X : Mat)
    (hU : U ∈ Matrix.orthogonalGroup (Fin d) ℝ)
    (hV : V ∈ Matrix.orthogonalGroup (Fin d) ℝ)
    (hX : X = U * S * Vᵀ)
    (hS_symm : Sᵀ = S)
    (hS_psd : ∀ W : Mat, matInner d (W * S) W ≥ 0) :
    let Q₀ := U * Vᵀ
    ∀ W : Mat, inTangentSpace d Q₀ W →
      matInner d (riemHessOD d Q₀ id (Q₀ - X) W) W ≥ 0 := by
  simp only []
  set Q₀ := U * Vᵀ
  have hQ₀ : Q₀ ∈ Matrix.orthogonalGroup (Fin d) ℝ := orthogonal_mul_transpose d U V hU hV
  have hQtX : Q₀ᵀ * X = V * S * Vᵀ := by rw [hX]; exact qtx_eq_vsvt d U V S hU
  have hQtX_symm : (Q₀ᵀ * X)ᵀ = Q₀ᵀ * X := by rw [hQtX]; exact vsvt_symm d V S hS_symm
  intro W hW
  rw [hessian_frobenius_simplify d Q₀ X W hQ₀ hW hQtX_symm]
  rw [matInner_tangentProj_left' d Q₀ (W * (Q₀ᵀ * X)) W hQ₀ hW]
  rw [hQtX]
  -- Need: matInner d (W * (V * S * Vᵀ)) W ≥ 0
  -- Key identity: matInner d (W*(V*S*Vᵀ)) W = matInner d ((W*V)*S) (W*V)
  -- Proof: tr((V*S*Vᵀ*Wᵀ)*W) = tr(V*(S*Vᵀ*Wᵀ*W)) = tr((S*Vᵀ*Wᵀ*W)*V) = tr(S*(Vᵀ*Wᵀ*W*V))
  -- = tr((S*(W*V)ᵀ)*(W*V)) = tr((W*V*S)ᵀ*(W*V))
  have hrw : matInner d (W * (V * S * Vᵀ)) W = matInner d ((W * V) * S) (W * V) := by
    simp only [matInner, show W * (V * S * Vᵀ) = W * V * S * Vᵀ from by simp [Matrix.mul_assoc]]
    rw [show (W * V * S * Vᵀ)ᵀ * W = V * (S * Vᵀ * Wᵀ * W) from by
      simp [transpose_mul, hS_symm, Matrix.mul_assoc]]
    rw [trace_mul_comm V _, Matrix.mul_assoc,
        show (W * V * S)ᵀ = S * Vᵀ * Wᵀ from by simp [transpose_mul, hS_symm, Matrix.mul_assoc]]
  rw [hrw]
  exact hS_psd (W * V)

/-! ### Main theorem -/

/-- **Exercise 2.8.3.3**: Given SVD `X = U S Vᵀ` with `U, V ∈ O(d)` and `S` symmetric PSD,
    `Q₀ = UVᵀ` satisfies the first and second-order optimality conditions for
    `min_{Q ∈ O(d)} ‖Q - X‖_F²`, hence `UVᵀ = proj_{O(d)}(X)`.

We verify:
1. `Q₀ ∈ O(d)`
2. First-order: `tangentProj d Q₀ (Q₀ - X) = 0`
3. Second-order: `⟪Hess f(Q₀)[W], W⟫ ≥ 0` for all `W ∈ T_{Q₀} O(d)`
4. `Q₀ᵀX` is a PSD square root of `XᵀX` (characterizes the minimizer per Exercise 2.8.3.2)

See book Chapter 2, exercise:orthogonal-group-calculus, Part 3c. -/
theorem exercise_2_8_3_3 (U V S X : Mat)
    (hU : U ∈ Matrix.orthogonalGroup (Fin d) ℝ)
    (hV : V ∈ Matrix.orthogonalGroup (Fin d) ℝ)
    -- SVD decomposition
    (hX : X = U * S * Vᵀ)
    -- S is symmetric (holds for diagonal matrices)
    (hS_symm : Sᵀ = S)
    -- S is PSD: ⟪WS, W⟫ ≥ 0 for all W (holds when S diagonal with nonneg diag)
    (hS_psd : ∀ W : Mat, matInner d (W * S) W ≥ 0) :
    let Q₀ := U * Vᵀ
    -- 1. Q₀ ∈ O(d)
    Q₀ ∈ Matrix.orthogonalGroup (Fin d) ℝ ∧
    -- 2. First-order condition (Riemannian gradient = 0)
    tangentProj d Q₀ (Q₀ - X) = 0 ∧
    -- 3. Second-order condition (Riemannian Hessian is PSD)
    (∀ W : Mat, inTangentSpace d Q₀ W →
      matInner d (riemHessOD d Q₀ id (Q₀ - X) W) W ≥ 0) ∧
    -- 4. Q₀ᵀX is a PSD square root of XᵀX
    IsPSDSqrtOD d (Q₀ᵀ * X) (Xᵀ * X) Q₀ (orthogonal_mul_transpose d U V hU hV) := by
  simp only []
  set Q₀ := U * Vᵀ
  have hQ₀ : Q₀ ∈ Matrix.orthogonalGroup (Fin d) ℝ := orthogonal_mul_transpose d U V hU hV
  have hgrad : tangentProj d Q₀ (Q₀ - X) = 0 :=
    tangentProj_grad_zero d U V S X hU hV hX hS_symm
  have hhess : ∀ W : Mat, inTangentSpace d Q₀ W →
      matInner d (riemHessOD d Q₀ id (Q₀ - X) W) W ≥ 0 :=
    hessian_psd_uvt d U V S X hU hV hX hS_symm hS_psd
  exact ⟨hQ₀, hgrad, hhess,
    exercise_2_8_3_2 d Q₀ X hQ₀ hgrad hhess⟩
