import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# Chapter 2, Exercise 2.7.1: First-Order Stationarity for Sphere-Constrained Kurtosis Maximization

## Informal Statement (exercise:kurtosis-sphere-landscape, Part 1)

Consider the sphere-constrained population kurtosis maximization problem:

  max_{‖w‖₂² = 1}  ∑_i kurt(z_i) w_i⁴

where κ_i = kurt(z_i) are the (elementwise) kurtosis values of the independent components.

Using the Riemannian gradient formula from Exercise 2.6.1, show that the first-order optimality
condition is:

  (∑_i κ_i w_i⁴) · w  =  κ ⊙ w⊙³

where ⊙ denotes elementwise multiplication and w⊙³ denotes elementwise cubing.

## Derivation Outline

Let f(w) = ∑_i κ_i w_i⁴.  The Euclidean gradient is ∇f(w) = (4 κ_i w_i³)_i.

The Riemannian gradient (Exercise 2.6.1) is:
  grad f(w) = P_w^⊥ ∇f(w)  =  ∇f(w) − ⟨∇f(w), w⟩ · w.

Setting grad f(w) = 0 gives:
  ∇f(w) = ⟨∇f(w), w⟩ · w
  4(κ_i w_i³)_i = 4(∑_i κ_i w_i⁴) · w
  (κ_i w_i³)_i = f(w) · w.

The stationarity condition is therefore:  f(w) · w = κ ⊙ w⊙³.

## Formalization Notes

We work in `EuclideanSpace ℝ (Fin d)`, with coordinates accessed via `(·.ofLp i)`.
The main theorem (`exercise_2_7_1`) gives the iff between:
- Riemannian gradient being zero: `(ℝ ∙ w)ᗮ.starProjection (kurtGrad κ w) = 0`
- Stationarity equation: `kurtObj κ w • w = elemCube κ w`

We also prove `hasFDerivAt_kurtObj`, confirming that `kurtGrad κ w` is indeed the
Euclidean gradient of `kurtObj κ` at `w` (via `HasFDerivAt`).

## References
- Book: deep-representation-learning-book/chapters/chapter2/classic-models.tex
  exercise:kurtosis-sphere-landscape, Part 1
- See also: Chapter2_Exercise2_6_1.lean (tangent space and projection for sphere)
-/

variable {d : ℕ}

-- ℝ inner product: ⟨a, b⟩_ℝ = a * b
private lemma inner_ℝ (a b : ℝ) : @inner ℝ ℝ _ a b = a * b := by simp [mul_comm]

/-! ### Auxiliary: coordinate linear map -/

/-- The continuous linear map `EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ` that evaluates the `i`-th
    coordinate: `coordLinear i v = v.ofLp i`. -/
noncomputable def coordLinear (i : Fin d) : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj i ∘L (EuclideanSpace.equiv (Fin d) ℝ).toContinuousLinearMap

@[simp] lemma coordLinear_apply (v : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    coordLinear i v = v.ofLp i := rfl

/-! ### Definitions: objective, gradient, stationarity vector -/

/-- 目标函数: f(w) = ∑_i κ_i w_i⁴ — 球面约束问题的种群峰度。
    The sphere-constrained kurtosis objective:
      kurtObj κ w = ∑ i, κ.ofLp i * w.ofLp i ^ 4. -/
noncomputable def kurtObj (κ w : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i : Fin d, κ.ofLp i * w.ofLp i ^ 4

/-- 元素级三次方向量: (κ_i w_i³)_i — 驻点方程右侧。
    The elementwise product κ ⊙ w⊙³, i.e., the vector with i-th entry κ_i w_i³. -/
noncomputable def elemCube (κ w : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => κ.ofLp i * w.ofLp i ^ 3)

@[simp] lemma elemCube_coord (κ w : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    (elemCube κ w).ofLp i = κ.ofLp i * w.ofLp i ^ 3 := rfl

/-- 欧氏梯度: ∇f(w) = 4 · (κ_i w_i³)_i.
    The Euclidean gradient of `kurtObj κ` at `w`, equal to `4 • elemCube κ w`. -/
noncomputable def kurtGrad (κ w : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  (4 : ℝ) • elemCube κ w

/-! ### Key computations -/

/-- ⟨kurtGrad κ w, w⟩ = 4 · f(w).
    The inner product of the gradient with w equals four times the objective value.
    This uses the identity ∑_i (κ_i w_i³) * w_i = ∑_i κ_i w_i⁴. -/
lemma inner_kurtGrad_self (κ w : EuclideanSpace ℝ (Fin d)) :
    inner (𝕜 := ℝ) (kurtGrad κ w) w = 4 * kurtObj κ w := by
  simp only [kurtGrad, elemCube]
  rw [inner_smul_left, show (starRingEnd ℝ) (4 : ℝ) = 4 from rfl, PiLp.inner_apply]
  simp only [show ∀ j : Fin d,
    ((EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => κ.ofLp i * w.ofLp i ^ 3)).ofLp j =
    κ.ofLp j * w.ofLp j ^ 3 from fun j => rfl, inner_ℝ, kurtObj, Finset.mul_sum]
  congr 1; ext i; ring

/-- **Gradient formula**: The Fréchet derivative of `kurtObj κ` at `w` equals `innerSL ℝ (kurtGrad κ w)`.
    That is, `D(kurtObj κ)(w)[v] = ⟨kurtGrad κ w, v⟩` for all `v`. -/
lemma hasFDerivAt_kurtObj (κ w : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (kurtObj κ) (innerSL ℝ (kurtGrad κ w)) w := by
  -- Each coordinate term κ_i * (w_i)^4 differentiates to κ_i * 4 * w_i^3 * (-)
  have key : ∀ i : Fin d,
      HasFDerivAt (fun w : EuclideanSpace ℝ (Fin d) => κ.ofLp i * w.ofLp i ^ 4)
        (κ.ofLp i • (4 * w.ofLp i ^ 3) • coordLinear i) w := fun i => by
    have := (((coordLinear i).hasFDerivAt (x := w)).pow (n := 4)).const_mul (κ.ofLp i)
    simp only [nsmul_eq_mul] at this
    convert this using 2
  -- Sum over all coordinates
  have hsum := HasFDerivAt.sum (u := Finset.univ) (fun i _ => key i)
  rw [show kurtObj κ = (fun w => ∑ i : Fin d, κ.ofLp i * w.ofLp i ^ 4) from rfl]
  convert hsum using 1
  · ext; simp
  -- Show the two CLM representations agree pointwise
  · ext v
    simp only [innerSL_apply_apply, PiLp.inner_apply, kurtGrad, elemCube,
      show ∀ j : Fin d, (((4 : ℝ) • (EuclideanSpace.equiv (Fin d) ℝ).symm
        (fun i => κ.ofLp i * w.ofLp i ^ 3)).ofLp j) =
        4 * (κ.ofLp j * w.ofLp j ^ 3) from fun j => by simp [PiLp.smul_apply], inner_ℝ]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
               coordLinear, ContinuousLinearMap.coe_comp', Function.comp,
               EuclideanSpace.equiv, ContinuousLinearMap.proj_apply]
    congr 1; ext i
    change _ = κ.ofLp i • (4 * w.ofLp i ^ 3) • v.ofLp i
    simp only [smul_eq_mul]; ring

/-! ### Projection formula (from Exercise 2.6.1) -/

/-- Explicit formula for the projection onto the tangent space to the sphere at a unit vector `w`.
    `P_w^⊥ v = v - ⟨w, v⟩ · w`.
    (Re-stated here from Chapter2_Exercise2_6_1 for `EuclideanSpace`.) -/
private lemma proj_perp_explicit (w v : EuclideanSpace ℝ (Fin d)) (hw : ‖w‖ = 1) :
    (ℝ ∙ w)ᗮ.starProjection v = v - (inner (𝕜 := ℝ) w v) • w := by
  rw [Submodule.starProjection_orthogonal_val, Submodule.starProjection_singleton, hw]
  norm_num

/-! ### Main theorem -/

/-- **Exercise 2.7.1**: First-Order Optimality Condition for Sphere-Constrained Kurtosis Maximization.

The Riemannian gradient of the kurtosis objective `kurtObj κ` at a unit vector `w` vanishes if
and only if the following stationarity equation holds:

  f(w) · w  =  κ ⊙ w⊙³

where `f(w) = ∑_i κ_i w_i⁴` (the objective value) and `κ ⊙ w⊙³ = (κ_i w_i³)_i` (elementwise).

## Proof
Using `proj_perp_explicit`:
  `P_w^⊥ ∇f(w) = ∇f(w) - ⟨∇f(w), w⟩ · w = 4·elemCube - 4·f(w)·w`

This equals zero iff `4·(elemCube - f(w)·w) = 0`, iff `elemCube = f(w)·w`.

See book Chapter 2, exercise:kurtosis-sphere-landscape Part 1. -/
theorem exercise_2_7_1 (κ w : EuclideanSpace ℝ (Fin d)) (hw : ‖w‖ = 1) :
    -- First-order optimality: Riemannian gradient of kurtObj vanishes at w
    (ℝ ∙ w)ᗮ.starProjection (kurtGrad κ w) = 0
    ↔
    -- Stationarity equation: (∑_i κ_i w_i⁴) · w = (κ_i w_i³)_i
    kurtObj κ w • w = elemCube κ w := by
  -- Expand Riemannian gradient using P_w^⊥ formula from 2.6.1
  rw [proj_perp_explicit w (kurtGrad κ w) hw, real_inner_comm, inner_kurtGrad_self]
  -- Now: 4 • elemCube κ w - (4 * kurtObj κ w) • w = 0 ↔ kurtObj κ w • w = elemCube κ w
  simp only [kurtGrad]
  -- Factor out 4: 4 • (elemCube κ w - kurtObj κ w • w) = 0
  rw [show (4 * kurtObj κ w) • w = (4 : ℝ) • (kurtObj κ w • w) from by rw [mul_smul]]
  rw [← smul_sub, smul_eq_zero]
  -- 4 ≠ 0, so: elemCube κ w - kurtObj κ w • w = 0 ↔ kurtObj κ w • w = elemCube κ w
  simp only [show (4 : ℝ) ≠ 0 from by norm_num, false_or]
  constructor
  · intro h; exact (sub_eq_zero.mp h).symm
  · intro h; exact sub_eq_zero.mpr h.symm
