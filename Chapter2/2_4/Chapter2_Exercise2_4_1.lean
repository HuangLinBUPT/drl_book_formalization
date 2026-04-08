import Mathlib

/-!
# Chapter 2, Exercise 2.4.1: Rank bound and orthonormal factorization

## Informal statement

Consider the model `x = U z`, where `U ∈ ℝ^{D×d}` has rank `d`, and let
`x₁, ..., x_N` be samples. Writing

`X = [x₁, ..., x_N] = U Z`,

show that `rank(X) ≤ d`, and therefore there exist a matrix `V ∈ ℝ^{D×d}`
with orthonormal columns and a matrix `Y ∈ ℝ^{d×N}` such that `X = V Y`.

This formalization proves the linear-algebraic core of the statement.
See book Chapter 2, Exercise 2.4 (exercise:whitening), part 1.
-/

open Matrix
open scoped BigOperators

noncomputable section

namespace Chapter2Exercise24_1

private lemma euclidean_inner_eq_sum (D : ℕ) (x y : EuclideanSpace ℝ (Fin D)) :
    @inner ℝ _ _ x y = ∑ i, x.ofLp i * y.ofLp i := by
  have key := @PiLp.inner_apply ℝ _ (Fin D) _ (fun _ => ℝ) _ _ x y
  simp only [RCLike.inner_apply] at key
  rw [key]
  congr 1
  ext i
  simp [mul_comm]

/--
Exercise 2.4.1: if `X = U * Z` with `U : ℝ^{D×d}` then `rank X ≤ d`.
Moreover, if `U` has full column rank `d`, then `X` admits a factorization
`X = V * Y` where `Vᵀ * V = I`.
-/
theorem exercise_2_4_1
    (D d N : ℕ)
    (U : Matrix (Fin D) (Fin d) ℝ)
    (Z : Matrix (Fin d) (Fin N) ℝ)
    (hU : U.rank = d) :
    let X : Matrix (Fin D) (Fin N) ℝ := U * Z
    X.rank ≤ d ∧
    ∃ (V : Matrix (Fin D) (Fin d) ℝ) (Y : Matrix (Fin d) (Fin N) ℝ),
      Vᵀ * V = 1 ∧ X = V * Y := by
  simp only []
  let X : Matrix (Fin D) (Fin N) ℝ := U * Z
  have h_rank : X.rank ≤ d := by
    calc
      X.rank = (U * Z).rank := rfl
      _ ≤ U.rank := Matrix.rank_mul_le_left U Z
      _ = d := hU

  let W : Submodule ℝ (EuclideanSpace ℝ (Fin D)) := (Matrix.toEuclideanLin U).range
  have hWfin : Module.finrank ℝ W = d := by
    calc
      Module.finrank ℝ W = U.rank := by
        symm
        simpa [W, Matrix.toEuclideanLin_eq_toLin_orthonormal] using
          (Matrix.rank_eq_finrank_range_toLin U
            (EuclideanSpace.basisFun (Fin D) ℝ).toBasis
            (EuclideanSpace.basisFun (Fin d) ℝ).toBasis)
      _ = d := hU

  let bW0 : OrthonormalBasis (Fin (Module.finrank ℝ W)) ℝ W := stdOrthonormalBasis ℝ W
  let bW : OrthonormalBasis (Fin d) ℝ W := bW0.reindex (finCongr hWfin)

  let V : Matrix (Fin D) (Fin d) ℝ :=
    Matrix.of fun i j => ((W.subtypeₗᵢ (bW j)).ofLp i)

  have hV_orth : Vᵀ * V = 1 := by
    ext j k
    simp only [V, Matrix.transpose_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    rw [← euclidean_inner_eq_sum D (W.subtypeₗᵢ (bW j)) (W.subtypeₗᵢ (bW k))]
    have hinner :
        @inner ℝ _ _ (W.subtypeₗᵢ (bW j)) (W.subtypeₗᵢ (bW k)) = if j = k then 1 else 0 := by
      simpa using (orthonormal_iff_ite.mp bW.orthonormal) j k
    simpa using hinner

  let xW : Fin N → W := fun j =>
    ⟨(Matrix.toEuclideanLin U) ((EuclideanSpace.equiv (Fin d) ℝ).symm (Z.col j)), by
      exact ⟨((EuclideanSpace.equiv (Fin d) ℝ).symm (Z.col j)), rfl⟩⟩

  let Y : Matrix (Fin d) (Fin N) ℝ := fun i j => (bW.repr (xW j)).ofLp i

  have hxW_coord (i : Fin D) (j : Fin N) : ((W.subtypeₗᵢ (xW j)).ofLp i) = X i j := by
    dsimp [xW, X]
    change (U.mulVec (Z.col j)) i = (U * Z) i j
    simp only [Matrix.mulVec, dotProduct, Matrix.col, Matrix.transpose_apply, Matrix.mul_apply]

  have hsum (j : Fin N) : ∑ k, ((bW.repr (xW j)).ofLp k) • bW k = xW j := by
    simpa using (bW.sum_repr (xW j))

  have hcoord (i : Fin D) (j : Fin N) :
      ∑ k, (bW.repr (xW j)).ofLp k * (W.subtypeₗᵢ (bW k)).ofLp i = X i j := by
    have htmp := congrArg (fun w : W => ((W.subtypeₗᵢ w).ofLp i)) (hsum j)
    calc
      ∑ k, (bW.repr (xW j)).ofLp k * (W.subtypeₗᵢ (bW k)).ofLp i
          = (W.subtypeₗᵢ (xW j)).ofLp i := by
              simpa [smul_eq_mul] using htmp
      _ = X i j := hxW_coord i j

  refine ⟨h_rank, V, Y, hV_orth, ?_⟩
  ext i j
  calc
    X i j = ∑ k, (bW.repr (xW j)).ofLp k * (W.subtypeₗᵢ (bW k)).ofLp i := by
      symm
      exact hcoord i j
    _ = ∑ k, V i k * Y k j := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [V, Y, Matrix.of_apply]
      rw [mul_comm]
    _ = (V * Y) i j := by
      rw [Matrix.mul_apply]

end Chapter2Exercise24_1
