# Exercise 2.3.1 Formalization Report: GL(d) Symmetry

## Problem Statement

**Source**: Deep Representation Learning Book, Chapter 2, Exercise 2.3 Part 1

**Informal Statement**: Consider the model X = UZ for matrices X, U, Z of compatible sizes. Show that if A is any square invertible matrix of compatible size, then the pair (UA, A⁻¹Z) also equals X under the model. We call this a **GL(d) symmetry**.

## Mathematical Context

### The Linear Model
- **Data matrix**: X ∈ ℝ^(D×N) (D-dimensional data, N samples)
- **Dictionary/Basis**: U ∈ ℝ^(D×d) (D dimensions, d basis vectors)
- **Coefficients**: Z ∈ ℝ^(d×N) (d coefficients per sample)
- **Model**: X = UZ

### GL(d) Symmetry
The general linear group GL(d) consists of all d×d invertible matrices. The exercise shows that the factorization X = UZ is **not unique**: any invertible transformation A ∈ GL(d) gives another valid factorization.

## Formalization Approach

### Type Setup
```lean
variable {D d N : Type*} [Fintype D] [Fintype d] [Fintype N]
```
We use type variables for dimensions to maximize generality. All matrices are over ℝ.

### Key Theorem: `gl_d_symmetry`

**Statement**:
```lean
theorem gl_d_symmetry
    (U : Matrix D d ℝ)
    (Z : Matrix d N ℝ)
    (A : Matrix d d ℝ)
    (hA : IsUnit A.det) :
    (U * A) * (A⁻¹ * Z) = U * Z
```

**Proof Strategy**:
The proof is a straightforward algebraic manipulation:

1. **(UA)(A⁻¹Z)** — Given expression
2. **= U(A(A⁻¹Z))** — Matrix multiplication associativity
3. **= U((AA⁻¹)Z)** — Matrix multiplication associativity
4. **= U(IZ)** — Inverse property: AA⁻¹ = I (requires A invertible)
5. **= UZ** — Identity property: IZ = Z

**Key Lemmas Used**:
- `Matrix.mul_assoc`: Matrix multiplication is associative
- `Matrix.nonsing_inv_mul`: For invertible A, we have AA⁻¹ = I
- `Matrix.one_mul`: Identity matrix is the multiplicative identity
- `IsUnit A.det`: Condition for invertibility (det(A) ≠ 0)

### Additional Theorems

#### `model_invariance_under_GLd`
Shows that if X = UZ, then X = (UA)(A⁻¹Z) for any invertible A.

This is a direct corollary that explicitly states the model equation is preserved.

#### `factorization_non_uniqueness`
Demonstrates the existence of infinitely many factorizations: given one factorization X = UZ, we can construct another (U', Z') = (UA, A⁻¹Z) for any invertible A.

This theorem captures the **non-identifiability** of the model: without additional constraints, we cannot uniquely determine U and Z from observations of X alone.

## Mathematical Significance

### Why This Matters

1. **Non-identifiability**: The model X = UZ admits infinite solutions. Any (U, Z) can be transformed to (UA, A⁻¹Z) for any A ∈ GL(d).

2. **Need for Constraints**: To uniquely recover U (or Z), we need additional assumptions:
   - **Orthogonality**: U has orthonormal columns (U^T U = I) → Reduces GL(d) to orthogonal group O(d)
   - **Statistical Independence**: Components of Z are independent → ICA methods
   - **Sparsity**: Z has sparse structure → Dictionary learning

3. **Connection to Part 2**: Exercise 2.3.2 shows that with independence assumptions on Z, the symmetry group reduces from GL(d) to just scaling and rotations (D₁QD₂ form).

4. **Geometric Interpretation**: GL(d) symmetry means the representation space can be arbitrarily transformed (stretched, rotated, sheared) without changing the observations X.

## Verification

The formalization was verified to typecheck successfully:
```bash
cd lean_formalization
lake env lean Chapter2/2_3/Chapter2_Exercise2_3_1.lean
```

All theorems compile without `sorry` — the proofs are complete.

## Lean 4 Technical Notes

### Invertibility Condition
We use `IsUnit A.det` to express that A is invertible. This is equivalent to det(A) ≠ 0 and is the standard way in Mathlib to work with invertible matrices.

### Matrix Inverse Notation
- `A⁻¹` is Lean notation for the matrix inverse
- The lemma `Matrix.nonsing_inv_mul` requires proof of `IsUnit A.det` to conclude `A * A⁻¹ = 1`

### Noncomputability
The `noncomputable section` declaration is necessary because matrix inverses and determinants are not computably decidable in general.

## References

- **Book**: Deep Representation Learning, Chapter 2, Exercise 2.3
- **Related Theory**: Independent Component Analysis (ICA), Dictionary Learning
- **Mathlib Modules**:
  - `Mathlib.Data.Matrix.Basic`
  - `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`
  - `Mathlib.LinearAlgebra.Matrix.Determinant`

## Next Steps

To complete Exercise 2.3:
- **Part 2**: Formalize the characterization of A when Az has uncorrelated components
- Show that A must have the form D₁QD₂ (diagonal × orthogonal × diagonal)
- This will require formalization of:
  - Random variables and covariance
  - Uncorrelated components condition
  - Polar decomposition theorem
