import Mathlib

/-!
# Chapter 2, Exercise 2.4.2: Whitening gives identity empirical covariance

## Informal statement

In Exercise 2.4.1, we obtained a factorization `X = V * Y` with `Vᵀ * V = I`.
The second part of the whitening exercise states that, when the whitening
operator `(Y * Yᵀ)^{-1/2}` exists, the whitened matrix
`(Y * Yᵀ)^{-1/2} * Y` has identity empirical covariance.

This file formalizes two layers of that claim.

1. A general linear-algebraic core: if a matrix `M` satisfies
   `M * (Y * Yᵀ) * Mᵀ = I`, then `W = M * Y` satisfies `W * Wᵀ = I`.
2. A more book-faithful version: when `Y * Yᵀ` is nonsingular, we can take
   the whitening operator to be `((CFC.sqrt (Y * Yᵀ))⁻¹)`, i.e. the inverse
   of the positive square root, and the resulting whitened matrix still has
   identity empirical covariance.

Thus the file now explicitly represents the matrix `(Y * Yᵀ)^{-1/2} * Y`
from the book, while still keeping the theorem purely linear-algebraic and
fully checkable in Lean.

## Alignment with the book sentence

Book sentence:

> the *whitened matrix* `(Y Yᵀ)^{-1/2} Y` exists in expectation whenever
> `Cov(z)` is nonsingular, and that it has identity empirical covariance.

Current formalization status:

* `exercise_2_4_2_inv_sqrt_form` proves the **identity empirical covariance**
  part for the explicit inverse-square-root whitening formula.
* `exercise_2_4_2_exists_whitening` proves an **existence statement in pure
  linear algebra**: if `Y * Yᵀ` is nonsingular, then such a whitening matrix
  exists.
* `rows_linearIndependent_implies_gram_isUnit` and
  `exercise_2_4_2_from_row_full_rank` provide a **bridge hypothesis**
  (full row rank of `Y`) implying that `Y * Yᵀ` is nonsingular.
* The probabilistic phrase **"exists in expectation whenever `Cov(z)` is
  nonsingular" is not yet formalized here**. That would require additional
  probabilistic machinery connecting `Cov(z)` to the sample matrix `Y`.

See book Chapter 2, Exercise 2.4 (exercise:whitening), part 2.
-/

open Matrix
open scoped MatrixOrder

noncomputable section

namespace Chapter2Exercise24_2

private theorem gram_posSemidef
    (d N : ℕ) (Y : Matrix (Fin d) (Fin N) ℝ) :
    (Y * Yᵀ : Matrix (Fin d) (Fin d) ℝ).PosSemidef := by
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.posSemidef_self_mul_conjTranspose Y)

/--
Lean's chosen positive square root of the Gram matrix `Y * Yᵀ`.
Mathematically, this plays the role of `(Y * Yᵀ)^{1/2}`.
-/
noncomputable def gramPosSqrt
    (d N : ℕ) (Y : Matrix (Fin d) (Fin N) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  CFC.sqrt (Y * Yᵀ)

private theorem gramPosSqrt_mul_self
    (d N : ℕ) (Y : Matrix (Fin d) (Fin N) ℝ) :
    gramPosSqrt d N Y * gramPosSqrt d N Y = Y * Yᵀ := by
  have hA_nonneg : (0 : Matrix (Fin d) (Fin d) ℝ) ≤ Y * Yᵀ := (gram_posSemidef d N Y).nonneg
  unfold gramPosSqrt
  simpa using CFC.sqrt_mul_sqrt_self (Y * Yᵀ : Matrix (Fin d) (Fin d) ℝ) hA_nonneg

private theorem gramPosSqrt_isUnit_iff
    (d N : ℕ) (Y : Matrix (Fin d) (Fin N) ℝ) :
    IsUnit (gramPosSqrt d N Y) ↔ IsUnit (Y * Yᵀ : Matrix (Fin d) (Fin d) ℝ) := by
  have hA_nonneg : (0 : Matrix (Fin d) (Fin d) ℝ) ≤ Y * Yᵀ := (gram_posSemidef d N Y).nonneg
  unfold gramPosSqrt
  simpa using CFC.isUnit_sqrt_iff (Y * Yᵀ : Matrix (Fin d) (Fin d) ℝ) hA_nonneg

private theorem gramPosSqrt_transpose
    (d N : ℕ) (Y : Matrix (Fin d) (Fin N) ℝ) :
    (gramPosSqrt d N Y)ᵀ = gramPosSqrt d N Y := by
  have hsa : star (CFC.sqrt (Y * Yᵀ : Matrix (Fin d) (Fin d) ℝ)) =
      CFC.sqrt (Y * Yᵀ : Matrix (Fin d) (Fin d) ℝ) :=
    IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (Y * Yᵀ : Matrix (Fin d) (Fin d) ℝ))
  unfold gramPosSqrt
  simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using hsa

/--
Linear-algebraic whitening core: if `M` whitens `Y * Yᵀ`, then the transformed
matrix `M * Y` has identity empirical covariance.
-/
theorem whitening_has_identity_empirical_covariance
    (d N : ℕ)
    (Y : Matrix (Fin d) (Fin N) ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : M * (Y * Yᵀ) * Mᵀ = 1) :
    let W : Matrix (Fin d) (Fin N) ℝ := M * Y
    W * Wᵀ = 1 := by
  simp only []
  calc
    (M * Y) * (M * Y)ᵀ = M * (Y * Yᵀ) * Mᵀ := by
      rw [Matrix.transpose_mul]
      rw [← Matrix.mul_assoc, Matrix.mul_assoc M Y Yᵀ]
    _ = 1 := hM

/--
Exercise 2.4.2 (formalized core): if `M_invSqrt` is a whitening matrix for
`Y * Yᵀ`, then the whitened matrix `M_invSqrt * Y` has identity empirical
covariance.
-/
theorem exercise_2_4_2
    (d N : ℕ)
    (Y : Matrix (Fin d) (Fin N) ℝ)
    (M_invSqrt : Matrix (Fin d) (Fin d) ℝ)
    (hwhite : M_invSqrt * (Y * Yᵀ) * M_invSqrtᵀ = 1) :
    let whitened : Matrix (Fin d) (Fin N) ℝ := M_invSqrt * Y
    whitened * whitenedᵀ = 1 := by
  simpa using whitening_has_identity_empirical_covariance d N Y M_invSqrt hwhite

/--
A more book-faithful whitening statement: if `Y * Yᵀ` is nonsingular, then we
can use the inverse of its positive square root as the whitening operator.
Here `gramPosSqrt d N Y` is Lean's version of `(Y * Yᵀ)^{1/2}`.
-/
theorem exercise_2_4_2_inv_sqrt_form
    (d N : ℕ)
    (Y : Matrix (Fin d) (Fin N) ℝ)
    (hYYt_unit : IsUnit (Y * Yᵀ : Matrix (Fin d) (Fin d) ℝ)) :
    let S : Matrix (Fin d) (Fin d) ℝ := gramPosSqrt d N Y
    let whitened : Matrix (Fin d) (Fin N) ℝ := S⁻¹ * Y
    whitened * whitenedᵀ = 1 := by
  simp only []
  have hS_unit : IsUnit (gramPosSqrt d N Y) :=
    (gramPosSqrt_isUnit_iff d N Y).2 hYYt_unit
  have hwhite : (gramPosSqrt d N Y)⁻¹ * (Y * Yᵀ) * ((gramPosSqrt d N Y)⁻¹)ᵀ = 1 := by
    calc
      (gramPosSqrt d N Y)⁻¹ * (Y * Yᵀ) * ((gramPosSqrt d N Y)⁻¹)ᵀ
          = (gramPosSqrt d N Y)⁻¹ * (gramPosSqrt d N Y * gramPosSqrt d N Y) *
              ((gramPosSqrt d N Y)⁻¹)ᵀ := by rw [gramPosSqrt_mul_self d N Y]
      _ = (gramPosSqrt d N Y)⁻¹ * (gramPosSqrt d N Y * gramPosSqrt d N Y) *
            (gramPosSqrt d N Y)⁻¹ := by
            rw [Matrix.transpose_nonsing_inv, gramPosSqrt_transpose d N Y]
      _ = ((gramPosSqrt d N Y)⁻¹ * gramPosSqrt d N Y) *
            (gramPosSqrt d N Y * (gramPosSqrt d N Y)⁻¹) := by
            rw [← Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = 1 := by
            rw [Matrix.nonsing_inv_mul _ (hS_unit.map Matrix.detMonoidHom),
              Matrix.mul_nonsing_inv _ (hS_unit.map Matrix.detMonoidHom), one_mul]
  simpa using whitening_has_identity_empirical_covariance d N Y (gramPosSqrt d N Y)⁻¹ hwhite

/--
Existence-style restatement: if `Y * Yᵀ` is nonsingular, then there exists a
whitening matrix obtained from the inverse square root of `Y * Yᵀ`.
-/
theorem exercise_2_4_2_exists_whitening
    (d N : ℕ)
    (Y : Matrix (Fin d) (Fin N) ℝ)
    (hYYt_unit : IsUnit (Y * Yᵀ : Matrix (Fin d) (Fin d) ℝ)) :
    ∃ M_invSqrt : Matrix (Fin d) (Fin d) ℝ,
      M_invSqrt = (gramPosSqrt d N Y)⁻¹ ∧
      let whitened : Matrix (Fin d) (Fin N) ℝ := M_invSqrt * Y
      whitened * whitenedᵀ = 1 := by
  refine ⟨(gramPosSqrt d N Y)⁻¹, rfl, ?_⟩
  simpa using exercise_2_4_2_inv_sqrt_form d N Y hYYt_unit

/--
Bridge lemma toward the book statement: if the rows of `Y` are linearly
independent (a full-row-rank condition), then the Gram matrix `Y * Yᵀ` is
nonsingular.
-/
theorem rows_linearIndependent_implies_gram_isUnit
    (d N : ℕ)
    (Y : Matrix (Fin d) (Fin N) ℝ)
    (hYrow : LinearIndependent ℝ Y.row) :
    IsUnit (Y * Yᵀ : Matrix (Fin d) (Fin d) ℝ) := by
  have hYt_inj : Function.Injective (Yᵀ.mulVec) := by
    rw [Matrix.mulVec_injective_iff]
    simpa [Matrix.col_transpose] using hYrow
  have hGram_inj : Function.Injective ((Y * Yᵀ : Matrix (Fin d) (Fin d) ℝ).mulVec) := by
    intro v w hvw
    apply hYt_inj
    have hsub : (Y * Yᵀ : Matrix (Fin d) (Fin d) ℝ) *ᵥ (v - w) = 0 := by
      calc
        (Y * Yᵀ : Matrix (Fin d) (Fin d) ℝ) *ᵥ (v - w)
            = (Y * Yᵀ : Matrix (Fin d) (Fin d) ℝ) *ᵥ v - (Y * Yᵀ : Matrix (Fin d) (Fin d) ℝ) *ᵥ w := by
                simp [Matrix.mulVec_sub]
        _ = 0 := by rw [hvw, sub_self]
    have hzero : Yᵀ *ᵥ (v - w) = 0 :=
      (Matrix.self_mul_conjTranspose_mulVec_eq_zero Y (v - w)).1 <| by
        simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hsub
    simpa [Matrix.mulVec_sub, sub_eq_zero] using hzero
  exact (Matrix.mulVec_injective_iff_isUnit).1 hGram_inj

/--
Book-style bridge theorem: under a full-row-rank hypothesis on `Y`, the Gram
matrix `Y * Yᵀ` is invertible, so the inverse-square-root whitening formula is
well-defined and has identity empirical covariance.
-/
theorem exercise_2_4_2_from_row_full_rank
    (d N : ℕ)
    (Y : Matrix (Fin d) (Fin N) ℝ)
    (hYrow : LinearIndependent ℝ Y.row) :
    let whitened : Matrix (Fin d) (Fin N) ℝ := (gramPosSqrt d N Y)⁻¹ * Y
    whitened * whitenedᵀ = 1 := by
  exact exercise_2_4_2_inv_sqrt_form d N Y (rows_linearIndependent_implies_gram_isUnit d N Y hYrow)

end Chapter2Exercise24_2
