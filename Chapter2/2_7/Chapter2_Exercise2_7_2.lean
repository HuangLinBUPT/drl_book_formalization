import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Chapter 2, Exercise 2.7.2: Critical-Point Structure for Sphere-Constrained Kurtosis (Part B)

## Informal Statement

For the positive-sign critical points of the sphere-constrained kurtosis maximization:
  max_{‖w‖₂² = 1}  ∑_i κ_i w_i⁴

Given a nonempty subset S ⊆ {1,...,d} with κ_i > 0 for all i ∈ S, define:
  σ = 1 / (∑_{j ∈ S} 1/κ_j)
  w_S(i) = √(σ/κ_i)  if i ∈ S,  0  otherwise.

Then:
1. ‖w_S‖ = 1
2. f(w_S) · w_S = κ ⊙ w_S^{⊙3}  (stationarity equation from Exercise 2.7.1)

## References
- Book: deep-representation-learning-book/chapters/chapter2/classic-models.tex
  exercise:kurtosis-sphere-landscape, Part B (verification of critical points)
- See also: Chapter2_Exercise2_7_1.lean (definitions and Part 1)
-/

open Finset Real in

variable {d : ℕ}

/-! ### Definitions reused from Exercise 2.7.1 -/

/-- The kurtosis objective: f(w) = ∑_i κ_i w_i⁴. -/
noncomputable def kurtObj' (κ w : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i : Fin d, κ.ofLp i * w.ofLp i ^ 4

/-- The elementwise cube vector: (κ_i w_i³)_i. -/
noncomputable def elemCube' (κ w : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => κ.ofLp i * w.ofLp i ^ 3)

@[simp] lemma elemCube'_coord (κ w : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    (elemCube' κ w).ofLp i = κ.ofLp i * w.ofLp i ^ 3 := rfl

/-! ### Definitions for the critical point -/

/-- σ_S = 1 / (∑_{j ∈ S} 1/κ_j): the objective value at the critical point w_S. -/
noncomputable def sigma_S (κ : EuclideanSpace ℝ (Fin d)) (S : Finset (Fin d)) : ℝ :=
  1 / ∑ j ∈ S, 1 / κ.ofLp j

/-- The critical point w_S with coordinates:
    w_S(i) = √(σ/κ_i) if i ∈ S, 0 otherwise. -/
noncomputable def critPoint (κ : EuclideanSpace ℝ (Fin d)) (S : Finset (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm
    (fun i => if i ∈ S then Real.sqrt (sigma_S κ S / κ.ofLp i) else 0)

@[simp] lemma critPoint_coord_mem (κ : EuclideanSpace ℝ (Fin d)) (S : Finset (Fin d))
    (i : Fin d) (hi : i ∈ S) :
    (critPoint κ S).ofLp i = Real.sqrt (sigma_S κ S / κ.ofLp i) := by
  simp [critPoint, hi]

@[simp] lemma critPoint_coord_nmem (κ : EuclideanSpace ℝ (Fin d)) (S : Finset (Fin d))
    (i : Fin d) (hi : i ∉ S) :
    (critPoint κ S).ofLp i = 0 := by
  simp [critPoint, hi]

/-! ### Helper lemmas -/

private lemma sum_inv_pos (κ : EuclideanSpace ℝ (Fin d)) (S : Finset (Fin d))
    (hκ : ∀ i ∈ S, 0 < κ.ofLp i) (hSne : S.Nonempty) :
    0 < ∑ j ∈ S, 1 / κ.ofLp j :=
  Finset.sum_pos (fun j hj => div_pos one_pos (hκ j hj)) hSne

private lemma sigma_pos (κ : EuclideanSpace ℝ (Fin d)) (S : Finset (Fin d))
    (hκ : ∀ i ∈ S, 0 < κ.ofLp i) (hSne : S.Nonempty) :
    0 < sigma_S κ S :=
  div_pos one_pos (sum_inv_pos κ S hκ hSne)

private lemma sigma_div_pos (κ : EuclideanSpace ℝ (Fin d)) (S : Finset (Fin d))
    (hκ : ∀ i ∈ S, 0 < κ.ofLp i) (hSne : S.Nonempty) (i : Fin d) (hi : i ∈ S) :
    0 < sigma_S κ S / κ.ofLp i :=
  div_pos (sigma_pos κ S hκ hSne) (hκ i hi)

/-- Key identity: σ · (∑_{j ∈ S} 1/κ_j) = 1 -/
private lemma sigma_mul_sum (κ : EuclideanSpace ℝ (Fin d)) (S : Finset (Fin d))
    (hκ : ∀ i ∈ S, 0 < κ.ofLp i) (hSne : S.Nonempty) :
    sigma_S κ S * ∑ j ∈ S, 1 / κ.ofLp j = 1 := by
  rw [sigma_S, one_div, inv_mul_cancel₀]
  exact ne_of_gt (sum_inv_pos κ S hκ hSne)

/-- ∑_{i ∈ S} σ/κ_i = 1 -/
private lemma sum_sigma_div_eq_one (κ : EuclideanSpace ℝ (Fin d)) (S : Finset (Fin d))
    (hκ : ∀ i ∈ S, 0 < κ.ofLp i) (hSne : S.Nonempty) :
    ∑ i ∈ S, sigma_S κ S / κ.ofLp i = 1 := by
  have : ∀ i ∈ S, sigma_S κ S / κ.ofLp i = sigma_S κ S * (1 / κ.ofLp i) :=
    fun _ _ => by ring
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
  exact sigma_mul_sum κ S hκ hSne

/-! ### Part 1: ‖w_S‖ = 1 -/

theorem critPoint_norm (κ : EuclideanSpace ℝ (Fin d)) (S : Finset (Fin d))
    (hκ : ∀ i ∈ S, 0 < κ.ofLp i) (hSne : S.Nonempty) :
    ‖critPoint κ S‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  rw [show (∑ i, ‖(critPoint κ S).ofLp i‖ ^ 2) = (1 : ℝ) from ?_]
  · simp
  -- Show ∑ i, ‖w_S(i)‖² = 1
  -- Split: for i ∉ S the term is 0; for i ∈ S, ‖sqrt(σ/κ_i)‖² = σ/κ_i.
  rw [← Finset.sum_add_sum_compl S (fun i => ‖(critPoint κ S).ofLp i‖ ^ 2)]
  -- Terms outside S are 0
  have hout : ∑ i ∈ Sᶜ, ‖(critPoint κ S).ofLp i‖ ^ 2 = 0 := by
    apply Finset.sum_eq_zero; intro i hi
    simp [Finset.mem_compl.mp hi]
  rw [hout, add_zero]
  -- Terms inside S: ‖sqrt(σ/κ_i)‖² = σ/κ_i
  have hin : ∀ i ∈ S, ‖(critPoint κ S).ofLp i‖ ^ 2 = sigma_S κ S / κ.ofLp i := by
    intro i hi
    simp only [critPoint_coord_mem κ S i hi]
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (le_of_lt (sigma_div_pos κ S hκ hSne i hi))]
  rw [Finset.sum_congr rfl hin]
  exact sum_sigma_div_eq_one κ S hκ hSne

/-! ### Part 2: Stationarity f(w_S) · w_S = κ ⊙ w_S^{⊙3} -/

/-- The objective value at w_S equals σ. -/
theorem kurtObj_critPoint (κ : EuclideanSpace ℝ (Fin d)) (S : Finset (Fin d))
    (hκ : ∀ i ∈ S, 0 < κ.ofLp i) (hSne : S.Nonempty) :
    kurtObj' κ (critPoint κ S) = sigma_S κ S := by
  simp only [kurtObj']
  -- Split sum over S and Sᶜ
  rw [← Finset.sum_add_sum_compl S (fun i => κ.ofLp i * (critPoint κ S).ofLp i ^ 4)]
  -- Outside S: terms are 0
  have hout : ∑ i ∈ Sᶜ, κ.ofLp i * (critPoint κ S).ofLp i ^ 4 = 0 := by
    apply Finset.sum_eq_zero; intro i hi
    simp [Finset.mem_compl.mp hi]
  rw [hout, add_zero]
  -- Inside S: κ_i * sqrt(σ/κ_i)^4 = κ_i * (σ/κ_i)^2 = σ²/κ_i
  have hin : ∀ i ∈ S, κ.ofLp i * (critPoint κ S).ofLp i ^ 4 =
      sigma_S κ S ^ 2 / κ.ofLp i := by
    intro i hi
    simp only [critPoint_coord_mem κ S i hi]
    rw [show Real.sqrt (sigma_S κ S / κ.ofLp i) ^ 4 =
        (Real.sqrt (sigma_S κ S / κ.ofLp i) ^ 2) ^ 2 from by ring]
    rw [Real.sq_sqrt (le_of_lt (sigma_div_pos κ S hκ hSne i hi))]
    field_simp [ne_of_gt (hκ i hi)]
  rw [Finset.sum_congr rfl hin]
  -- ∑_{i ∈ S} σ²/κ_i = σ² · ∑_{i ∈ S} 1/κ_i = σ
  have h : ∑ x ∈ S, sigma_S κ S ^ 2 / κ.ofLp x =
      sigma_S κ S ^ 2 * ∑ x ∈ S, (1 / κ.ofLp x) := by
    rw [Finset.mul_sum]; congr 1; ext i; ring
  rw [h, sq, mul_assoc, sigma_mul_sum κ S hκ hSne, mul_one]

/-- **Exercise 2.7.2 (Part B)**: The critical point w_S satisfies the stationarity equation
    f(w_S) · w_S = κ ⊙ w_S^{⊙3}. -/
theorem exercise_2_7_2_stationarity (κ : EuclideanSpace ℝ (Fin d)) (S : Finset (Fin d))
    (hκ : ∀ i ∈ S, 0 < κ.ofLp i) (hSne : S.Nonempty) :
    kurtObj' κ (critPoint κ S) • critPoint κ S = elemCube' κ (critPoint κ S) := by
  rw [kurtObj_critPoint κ S hκ hSne]
  ext i
  simp only [PiLp.smul_apply, smul_eq_mul, elemCube'_coord]
  by_cases hi : i ∈ S
  · -- Case i ∈ S: σ · sqrt(σ/κ_i) = κ_i · sqrt(σ/κ_i)³
    simp only [critPoint_coord_mem κ S i hi]
    -- RHS: κ_i * sqrt(σ/κ_i)^3 = κ_i * sqrt(σ/κ_i) * (σ/κ_i)
    -- LHS: σ * sqrt(σ/κ_i)
    -- They are equal since κ_i * (σ/κ_i) = σ
    set r := sigma_S κ S / κ.ofLp i with hr_def
    have hr : 0 ≤ r := le_of_lt (sigma_div_pos κ S hκ hSne i hi)
    -- sqrt(r)^3 = sqrt(r) * r (with mul_comm)
    have cube : Real.sqrt r ^ 3 = Real.sqrt r * r := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, mul_comm, Real.sq_sqrt hr]
    rw [cube]
    -- Now goal: σ * √r = κ_i * (√r * r)
    -- κ_i * r = σ, so κ_i * (√r * r) = √r * (κ_i * r) = √r * σ
    have hκr : κ.ofLp i * r = sigma_S κ S := by
      rw [hr_def]; field_simp [ne_of_gt (hκ i hi)]
    nlinarith [Real.sqrt_nonneg r]
  · -- Case i ∉ S: both sides are 0
    simp [critPoint_coord_nmem κ S i hi]

/-- **Exercise 2.7.2**: Complete verification that w_S is a unit-norm critical point of the
    sphere-constrained kurtosis objective. -/
theorem exercise_2_7_2 (κ : EuclideanSpace ℝ (Fin d)) (S : Finset (Fin d))
    (hκ : ∀ i ∈ S, 0 < κ.ofLp i) (hSne : S.Nonempty) :
    ‖critPoint κ S‖ = 1 ∧
    kurtObj' κ (critPoint κ S) • critPoint κ S = elemCube' κ (critPoint κ S) :=
  ⟨critPoint_norm κ S hκ hSne, exercise_2_7_2_stationarity κ S hκ hSne⟩
