import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic

/-!
# Chapter 2, Exercise 2.8.1: Orthogonal Group Tangent Space and Projection

## Informal Statement (exercise:orthogonal-group-calculus, Part 1)

Let `F(Q) = Qᵀ Q = I`, so the orthogonal group `O(d) = F⁻¹({I})`.

**Part 1a**: The tangent space to O(d) at Q is:
  `T_Q O(d) = { Q·Ω ∈ ℝ^{d×d} | Ωᵀ = -Ω }`
  (i.e., Q times a skew-symmetric matrix).

**Part 1b**: The orthogonal projection onto this tangent space (w.r.t. the inner product
  `⟨X, Y⟩ = tr(Xᵀ Y)`) is:
  `P_{T_Q O(d)}(Δ) = Q · Skew(Qᵀ Δ)`
  where `Skew(Δ) = (1/2)(Δ - Δᵀ)` is the skew-symmetric part of Δ.

## References
- Book: deep-representation-learning-book/chapters/chapter2/classic-models.tex
  exercise:orthogonal-group-calculus, Part 1
- See also: Chapter2_Exercise2_6_1.lean (analogous result for the sphere)
-/

open Matrix

variable (d : ℕ) [DecidableEq (Fin d)]

local notation "Mat" => Matrix (Fin d) (Fin d) ℝ

/-! ### Frobenius inner product -/

/-- Frobenius inner product: `⟪X, Y⟫ = tr(Xᵀ Y)`. -/
noncomputable def matInner (X Y : Mat) : ℝ := (Xᵀ * Y).trace

omit [DecidableEq (Fin d)] in
lemma matInner_comm (X Y : Mat) : matInner d X Y = matInner d Y X := by
  simp only [matInner]
  rw [← trace_transpose (Xᵀ * Y), transpose_mul, transpose_transpose]

/-! ### Skew-symmetric part -/

/-- Skew-symmetric part: `Skew(Δ) = (1/2)(Δ - Δᵀ)`. -/
noncomputable def skewPart (Δ : Mat) : Mat := (1 / 2 : ℝ) • (Δ - Δᵀ)

omit [DecidableEq (Fin d)] in
/-- `Skew(Δ)ᵀ = -Skew(Δ)`. -/
lemma skewPart_transpose (Δ : Mat) : (skewPart d Δ)ᵀ = -(skewPart d Δ) := by
  simp only [skewPart, transpose_smul]
  rw [transpose_sub, transpose_transpose]
  ext i j; simp [Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply]; ring

omit [DecidableEq (Fin d)] in
/-- `Skew(Δ) = Δ` when `Δᵀ = -Δ`. -/
lemma skewPart_of_skew (Δ : Mat) (hΔ : Δᵀ = -Δ) : skewPart d Δ = Δ := by
  ext i j
  simp only [skewPart, smul_eq_mul, Matrix.smul_apply, Matrix.sub_apply, Matrix.transpose_apply]
  have h1 : Δ j i = -Δ i j := congr_fun (congr_fun hΔ i) j
  linarith

omit [DecidableEq (Fin d)] in
/-- The symmetric part: `Δ - Skew(Δ) = (1/2)(Δ + Δᵀ)`. -/
lemma symmPart_eq (Δ : Mat) : Δ - skewPart d Δ = (1 / 2 : ℝ) • (Δ + Δᵀ) := by
  ext i j
  simp [skewPart, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply]
  ring

/-! ### Tangent space -/

/-- `V ∈ T_Q O(d)` iff `QᵀV` is skew-symmetric. -/
def inTangentSpace (Q V : Mat) : Prop := (Qᵀ * V)ᵀ = -(Qᵀ * V)

/-- If Q ∈ O(d) and V ∈ T_Q O(d), then V = Q * (QᵀV). -/
lemma tangent_reconstruction (Q V : Mat)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin d) ℝ) :
    V = Q * (Qᵀ * V) := by
  have hQ' : Q * Qᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).mp hQ
  calc V = (Q * Qᵀ) * V := by rw [hQ', Matrix.one_mul]
    _ = Q * (Qᵀ * V) := Matrix.mul_assoc Q Qᵀ V

/-! ### Projection -/

/-- The projection: `P(Δ) = Q · Skew(Qᵀ Δ)`. -/
noncomputable def tangentProj (Q Δ : Mat) : Mat := Q * skewPart d (Qᵀ * Δ)

/-- `P(Δ) ∈ T_Q O(d)` for any Q ∈ O(d). -/
theorem tangentProj_in_tangentSpace (Q Δ : Mat)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin d) ℝ) :
    inTangentSpace d Q (tangentProj d Q Δ) := by
  simp only [inTangentSpace, tangentProj, transpose_mul, transpose_transpose]
  have hQtQ : Qᵀ * Q = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin d) ℝ).mp hQ
  rw [show (skewPart d (Qᵀ * Δ))ᵀ * Qᵀ * Q = (skewPart d (Qᵀ * Δ))ᵀ * (Qᵀ * Q) from
    Matrix.mul_assoc _ _ _, hQtQ, Matrix.mul_one,
    show -(Qᵀ * (Q * skewPart d (Qᵀ * Δ))) = -(Qᵀ * Q) * skewPart d (Qᵀ * Δ) from by
      simp [Matrix.mul_assoc]]
  rw [hQtQ]
  simp [skewPart_transpose d (Qᵀ * Δ)]

/-- `P` is idempotent on tangent vectors: if V ∈ T, then P(V) = V. -/
theorem tangentProj_idempotent (Q V : Mat)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin d) ℝ)
    (hV : inTangentSpace d Q V) :
    tangentProj d Q V = V := by
  rw [tangentProj, skewPart_of_skew d _ hV]
  exact (tangent_reconstruction d Q V hQ).symm

/-! ### Orthogonality of skew × symmetric -/

omit [DecidableEq (Fin d)] in
/-- If Ωᵀ = -Ω and Sᵀ = S, then `tr(Ω * S) = 0`. -/
lemma trace_skew_mul_symm (Ω S : Mat) (hΩ : Ωᵀ = -Ω) (hS : Sᵀ = S) :
    (Ω * S).trace = 0 := by
  have h : (Ω * S).trace = -((Ω * S).trace) := by
    nth_rw 1 [← trace_transpose (Ω * S), transpose_mul, hS, hΩ]
    rw [show S * -Ω = -(S * Ω) from by rw [Matrix.mul_neg]]
    rw [trace_neg, ← trace_mul_comm]
  linarith

/-! ### Main orthogonality theorem -/

/-- The residual `Δ - P(Δ)` is Frobenius-orthogonal to every tangent vector Q·Ω. -/
theorem tangentProj_complement_orthogonal (Q Ω Δ : Mat)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin d) ℝ)
    (hΩ : Ωᵀ = -Ω) :
    matInner d (Q * Ω) (Δ - tangentProj d Q Δ) = 0 := by
  simp only [matInner, tangentProj]
  have hQtQ : Qᵀ * Q = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin d) ℝ).mp hQ
  set M := Qᵀ * Δ
  -- Step 1: expand tr((QΩ)ᵀ (Δ - Q·Skew(M))) = tr(ΩᵀM) - tr(ΩᵀSkew(M))
  have expand : ((Q * Ω)ᵀ * (Δ - Q * skewPart d M)).trace =
      (Ωᵀ * M).trace - (Ωᵀ * skewPart d M).trace := by
    simp only [transpose_mul, Matrix.mul_sub, trace_sub, Matrix.mul_assoc]
    congr 1
    rw [show Ωᵀ * (Qᵀ * (Q * skewPart d M)) = Ωᵀ * (Qᵀ * Q) * skewPart d M from by
      rw [Matrix.mul_assoc, Matrix.mul_assoc]]
    rw [hQtQ, Matrix.mul_one]
  rw [expand]
  -- Step 2: combine as tr(Ωᵀ (M - Skew(M)))
  rw [← trace_sub, ← Matrix.mul_sub]
  -- Step 3: M - Skew(M) = (1/2)(M + Mᵀ) is the symmetric part
  rw [symmPart_eq d M, Matrix.mul_smul, trace_smul]
  -- Step 4: tr(Ωᵀ (M + Mᵀ)) = 0  (Ωᵀ skew, M + Mᵀ symm)
  suffices h : (Ωᵀ * (M + Mᵀ)).trace = 0 by simp [h]
  apply trace_skew_mul_symm d
  · rw [transpose_transpose, hΩ, neg_neg]
  · rw [transpose_add, transpose_transpose, add_comm]

/-! ### Main theorem -/

/-- **Exercise 2.8.1**: Orthogonal Projection Formula for O(d).

For Q ∈ O(d) and any matrix Δ, the orthogonal projection of Δ onto the tangent space
`T_Q O(d) = { Q·Ω | Ωᵀ = -Ω }` with respect to the Frobenius inner product `tr(Xᵀ Y)` is:

  `P(Δ) = Q · Skew(Qᵀ · Δ)`,  where `Skew(M) = (1/2)(M - Mᵀ)`.

Properties:
1. `P(Δ) ∈ T_Q O(d)` — lies in the tangent space
2. `P(P(Δ)) = P(Δ)` — idempotent
3. `⟪Q·Ω, Δ - P(Δ)⟫ = 0` for all skew Ω — residual is orthogonal to tangent space

See book Chapter 2, exercise:orthogonal-group-calculus, Part 1. -/
theorem exercise_2_8_1 (Q : Mat) (hQ : Q ∈ Matrix.orthogonalGroup (Fin d) ℝ) (Δ : Mat) :
    tangentProj d Q Δ = Q * skewPart d (Qᵀ * Δ) ∧
    inTangentSpace d Q (tangentProj d Q Δ) ∧
    tangentProj d Q (tangentProj d Q Δ) = tangentProj d Q Δ ∧
    ∀ Ω : Mat, Ωᵀ = -Ω → matInner d (Q * Ω) (Δ - tangentProj d Q Δ) = 0 :=
  ⟨rfl,
   tangentProj_in_tangentSpace d Q Δ hQ,
   tangentProj_idempotent d Q _ hQ (tangentProj_in_tangentSpace d Q Δ hQ),
   fun Ω hΩ => tangentProj_complement_orthogonal d Q Ω Δ hQ hΩ⟩
