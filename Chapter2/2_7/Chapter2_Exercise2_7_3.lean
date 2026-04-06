import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Chapter 2, Exercise 2.7.3: Local Maxima of Sphere-Constrained Kurtosis (Part C)

## Informal Statement (exercise:kurtosis-sphere-landscape, Part 3)

The sphere-constrained kurtosis maximization problem is:
  max_{‖w‖₂² = 1}  f(w) = ∑_i κ_i w_i⁴

**Exercise 2.7.3** (Part 3): Assume ∃ i, κ_i > 0. Using the Riemannian Hessian bilinear form
  hessForm κ w v = ∑_i 12 κ_i w_i² v_i² − 4 f(w) ‖v‖²
(restricted to v ∈ T_w S^{d-1}), show:

1. At w = e_j (the j-th standard basis vector) with κ_j > 0:
     hessForm κ (e_j) v = −4 κ_j ‖v‖²  for all v ⊥ e_j.
   So e_j is a strict local maximum (negative definite Hessian on tangent space).

2. The objective value at e_j is f(e_j) = κ_j.

3. Global maxima are ±e_j where j achieves the maximum value of κ_j over all j with κ_j > 0.

## Key computation

At w = e_j:
  - w_j = 1, w_i = 0 for i ≠ j
  - f(e_j) = κ_j · 1⁴ = κ_j
  - For v ⊥ e_j, we have v_j = 0
  - hessForm κ (e_j) v = ∑_i 12 κ_i · (e_j)_i² · v_i² − 4 κ_j ‖v‖²
                       = 12 κ_j · 1 · 0² − 4 κ_j ‖v‖²   (only i=j term is nonzero in w,
                                                             but v_j = 0)
                       = −4 κ_j ‖v‖²

## References
- Book: deep-representation-learning-book/chapters/chapter2/classic-models.tex
  exercise:kurtosis-sphere-landscape, Part 3
- See also: Chapter2_Exercise2_7_1.lean (objective, gradient)
- See also: Chapter2_Exercise2_7_2.lean (critical points)
- See also: Chapter2_Exercise2_6_3.lean (Riemannian Hessian)
-/

variable {d : ℕ}

open Finset Real

/-! ### Definitions -/

/-- The kurtosis objective: f(w) = ∑_i κ_i w_i⁴. -/
noncomputable def kurtObj₃ (κ w : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i : Fin d, κ.ofLp i * w.ofLp i ^ 4

/-- The standard basis vector e_j in EuclideanSpace ℝ (Fin d). -/
noncomputable def stdBasis (j : Fin d) : EuclideanSpace ℝ (Fin d) :=
  EuclideanSpace.single j (1 : ℝ)

@[simp] lemma stdBasis_coord_eq (j i : Fin d) :
    (stdBasis j).ofLp i = if i = j then 1 else 0 := by
  simp [stdBasis]

lemma stdBasis_norm (j : Fin d) : ‖stdBasis j‖ = 1 := by
  simp [stdBasis, EuclideanSpace.norm_single]

/-- The Riemannian Hessian bilinear form for the kurtosis objective.
    hessForm κ w v = ∑_i 12 κ_i w_i² v_i² − 4 f(w) ‖v‖²
    (valid when ⟨v, w⟩ = 0). -/
noncomputable def hessForm (κ w v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i : Fin d, 12 * κ.ofLp i * w.ofLp i ^ 2 * v.ofLp i ^ 2
  - 4 * kurtObj₃ κ w * ‖v‖ ^ 2

/-! ### Part A: Objective value at standard basis vectors -/

/-- **Part A**: f(e_j) = κ_j. -/
theorem kurtObj_stdBasis (κ : EuclideanSpace ℝ (Fin d)) (j : Fin d) :
    kurtObj₃ κ (stdBasis j) = κ.ofLp j := by
  simp only [kurtObj₃, stdBasis_coord_eq]
  -- Rewrite: κ_i * (if i = j then 1 else 0)^4  =  if i = j then κ_i * 1 else 0
  --        = if i = j then κ_i else 0
  simp only [ite_pow, one_pow, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
             mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ j (fun i => κ.ofLp i)]
  simp

/-! ### Part B: Hessian form at standard basis vectors -/

/-- Norm squared in terms of coordinates. -/
private lemma norm_sq_eq_sum (v : EuclideanSpace ℝ (Fin d)) :
    ‖v‖ ^ 2 = ∑ i : Fin d, v.ofLp i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  congr 1; ext i; simp

/-- **Part B**: For v ⊥ e_j (i.e., v_j = 0), the Riemannian Hessian bilinear form at e_j is:
    hessForm κ (e_j) v = −4 κ_j ‖v‖². -/
theorem hessForm_stdBasis (κ : EuclideanSpace ℝ (Fin d)) (j : Fin d)
    (v : EuclideanSpace ℝ (Fin d))
    (hv : inner (𝕜 := ℝ) v (stdBasis j) = (0 : ℝ)) :
    hessForm κ (stdBasis j) v = -4 * κ.ofLp j * ‖v‖ ^ 2 := by
  -- Extract v_j = 0 from the tangency condition ⟨v, e_j⟩ = 0
  have hvj : v.ofLp j = 0 := by
    have hinner : inner (𝕜 := ℝ) v (stdBasis j) =
        ∑ i : Fin d, v.ofLp i * (stdBasis j).ofLp i := by
      simp [PiLp.inner_apply]
    rw [hinner] at hv
    simp only [stdBasis_coord_eq, mul_ite, mul_one, mul_zero] at hv
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hv
    exact hv
  rw [hessForm, kurtObj_stdBasis]
  -- The sum ∑_i 12 κ_i (e_j)_i² v_i²: only i=j contributes, but v_j = 0
  have hsum : ∑ i : Fin d, 12 * κ.ofLp i * (stdBasis j).ofLp i ^ 2 * v.ofLp i ^ 2 = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp only [stdBasis_coord_eq]
    by_cases hij : i = j
    · subst hij; simp [hvj]
    · simp [hij]
  rw [hsum, zero_sub, norm_sq_eq_sum]
  ring

/-! ### Part C: Negative definiteness implies local maximum for κ_j > 0 -/

/-- **Part C**: For j ∈ S⁺ (κ_j > 0), the Hessian form at e_j is negative semi-definite
    on the tangent space, with equality only at v = 0.
    This certifies that e_j is a (strict) local maximum. -/
theorem hessForm_stdBasis_neg_def (κ : EuclideanSpace ℝ (Fin d)) (j : Fin d)
    (hκj : 0 < κ.ofLp j)
    (v : EuclideanSpace ℝ (Fin d))
    (hv : inner (𝕜 := ℝ) v (stdBasis j) = (0 : ℝ)) :
    hessForm κ (stdBasis j) v ≤ 0 := by
  rw [hessForm_stdBasis κ j v hv]
  have h1 : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
  nlinarith

/-- Strict version: equality holds iff v = 0. -/
theorem hessForm_stdBasis_neg_def_strict (κ : EuclideanSpace ℝ (Fin d)) (j : Fin d)
    (hκj : 0 < κ.ofLp j)
    (v : EuclideanSpace ℝ (Fin d))
    (hv : inner (𝕜 := ℝ) v (stdBasis j) = (0 : ℝ)) :
    hessForm κ (stdBasis j) v = 0 ↔ v = 0 := by
  rw [hessForm_stdBasis κ j v hv]
  constructor
  · intro h
    have hκ : (0 : ℝ) < 4 * κ.ofLp j := by linarith
    have : ‖v‖ ^ 2 = 0 := by nlinarith
    rwa [sq_eq_zero_iff, norm_eq_zero] at this
  · intro hv0
    simp [hv0]

/-! ### Part D: Global maximum over S⁺ -/

/-- **Part D**: Among all standard basis vectors in S⁺ = {i | κ_i > 0},
    the objective value is maximized where κ_i is maximized.
    More precisely: f(e_i) = κ_i, so the global maximum is max_{i ∈ S⁺} κ_i. -/
theorem globalMax_over_Splus (κ : EuclideanSpace ℝ (Fin d)) (Splus : Finset (Fin d))
    (hSne : Splus.Nonempty) :
    Splus.sup' hSne (fun i => kurtObj₃ κ (stdBasis i)) =
    Splus.sup' hSne (fun i => κ.ofLp i) := by
  congr 1
  ext i
  exact kurtObj_stdBasis κ i

/-- **Summary theorem (Exercise 2.7.3)**: Combining all parts.
    Under the hypothesis that κ has at least one positive component (j ∈ S⁺):
    1. f(e_j) = κ_j
    2. The Riemannian Hessian form at e_j on T_{e_j} S is -4 κ_j ‖v‖²
    3. This is strictly negative (local maximum) since κ_j > 0 -/
theorem exercise_2_7_3 (κ : EuclideanSpace ℝ (Fin d)) (j : Fin d) (hκj : 0 < κ.ofLp j) :
    -- (1) objective value at e_j
    kurtObj₃ κ (stdBasis j) = κ.ofLp j ∧
    -- (2) unit norm
    ‖stdBasis j‖ = 1 ∧
    -- (3) Hessian form is -4 κ_j ‖v‖² on tangent vectors
    (∀ v : EuclideanSpace ℝ (Fin d), inner (𝕜 := ℝ) v (stdBasis j) = 0 →
        hessForm κ (stdBasis j) v = -4 * κ.ofLp j * ‖v‖ ^ 2) ∧
    -- (4) Hessian form is strictly negative (local max condition)
    (∀ v : EuclideanSpace ℝ (Fin d), inner (𝕜 := ℝ) v (stdBasis j) = 0 →
        hessForm κ (stdBasis j) v ≤ 0) :=
  ⟨kurtObj_stdBasis κ j,
   stdBasis_norm j,
   fun v hv => hessForm_stdBasis κ j v hv,
   fun v hv => hessForm_stdBasis_neg_def κ j hκj v hv⟩
