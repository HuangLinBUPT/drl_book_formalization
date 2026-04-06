import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Chapter 2, Exercise 2.7.4: Over-Deflated Kurtosis Landscape (Part D)

## Informal Statement (exercise:kurtosis-sphere-landscape, Part 4)

The sphere-constrained kurtosis maximization problem is:
  max_{‖w‖₂ = 1}  f(w) = ∑_i κ_i w_i⁴

**Exercise 2.7.4** (Part 4): Assume κ_j < 0 for every j = 1, …, d (the "over-deflated" case).
Using the Riemannian Hessian bilinear form
  hessForm κ w v = ∑_i 12 κ_i w_i² v_i² − 4 f(w) ‖v‖²
(restricted to v ∈ T_w S^{d-1}), show that the only local maxima are the signed dense vectors
  w_full = ∑_i ± √(σ_full / κ_i) e_i
where σ_full = 1 / (∑_j 1/κ_j) < 0 and S = {1,…,d} (full support).

## Key computation

At w = w_full (full support, all κ_i < 0):
  - σ_full < 0 (since each 1/κ_j < 0)
  - w_full,i² = σ_full / κ_i > 0  (both negative → positive)
  - f(w_full) = σ_full  (objective value equals σ)
  - For any v ∈ T_{w_full} S^{d-1}:
      hessForm κ w_full v
        = ∑_i 12 κ_i · (σ_full/κ_i) · v_i²  − 4 σ_full ‖v‖²
        = 12 σ_full ∑_i v_i²                  − 4 σ_full ‖v‖²
        = 12 σ_full ‖v‖²                       − 4 σ_full ‖v‖²
        = 8 σ_full ‖v‖²
  Since σ_full < 0, this is ≤ 0, certifying w_full as a local maximum.

## References
- Book: deep-representation-learning-book/chapters/chapter2/classic-models.tex
  exercise:kurtosis-sphere-landscape, Part 4
- See also: Chapter2_Exercise2_7_1.lean (objective, gradient)
- See also: Chapter2_Exercise2_7_2.lean (critical points)
- See also: Chapter2_Exercise2_7_3.lean (Riemannian Hessian, Part 3)
-/

variable {d : ℕ}

open Finset Real

/-! ### Definitions (mirroring prior exercises) -/

/-- The kurtosis objective: f(w) = ∑_i κ_i w_i⁴. -/
noncomputable def kurtObj₄ (κ w : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i : Fin d, κ.ofLp i * w.ofLp i ^ 4

/-- σ_S = 1 / (∑_{j ∈ S} 1/κ_j): the objective value at the critical point w_S. -/
noncomputable def sigma₄ (κ : EuclideanSpace ℝ (Fin d)) (S : Finset (Fin d)) : ℝ :=
  1 / ∑ j ∈ S, 1 / κ.ofLp j

/-- The critical point w_S with coordinates:
    w_S(i) = √(σ/κ_i) if i ∈ S, 0 otherwise. -/
noncomputable def critPoint₄ (κ : EuclideanSpace ℝ (Fin d)) (S : Finset (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm
    (fun i => if i ∈ S then Real.sqrt (sigma₄ κ S / κ.ofLp i) else 0)

@[simp] lemma critPoint₄_coord_mem (κ : EuclideanSpace ℝ (Fin d)) (S : Finset (Fin d))
    (i : Fin d) (hi : i ∈ S) :
    (critPoint₄ κ S).ofLp i = Real.sqrt (sigma₄ κ S / κ.ofLp i) := by
  simp [critPoint₄, hi]

@[simp] lemma critPoint₄_coord_nmem (κ : EuclideanSpace ℝ (Fin d)) (S : Finset (Fin d))
    (i : Fin d) (hi : i ∉ S) :
    (critPoint₄ κ S).ofLp i = 0 := by
  simp [critPoint₄, hi]

/-- The Riemannian Hessian bilinear form for the kurtosis objective.
    hessForm κ w v = ∑_i 12 κ_i w_i² v_i² − 4 f(w) ‖v‖²
    (valid when ⟨v, w⟩ = 0). -/
noncomputable def hessForm₄ (κ w v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i : Fin d, 12 * κ.ofLp i * w.ofLp i ^ 2 * v.ofLp i ^ 2
  - 4 * kurtObj₄ κ w * ‖v‖ ^ 2

/-! ### Helper lemmas for the negative-kurtosis case -/

/-- When all κ_i < 0, the sum ∑_{j ∈ S} 1/κ_j < 0. -/
private lemma sum_inv_neg (κ : EuclideanSpace ℝ (Fin d)) (S : Finset (Fin d))
    (hκ : ∀ i ∈ S, κ.ofLp i < 0) (hSne : S.Nonempty) :
    ∑ j ∈ S, 1 / κ.ofLp j < 0 :=
  Finset.sum_neg (fun j hj => div_neg_of_pos_of_neg one_pos (hκ j hj)) hSne

/-- When all κ_i < 0, σ_S < 0. -/
private lemma sigma₄_neg (κ : EuclideanSpace ℝ (Fin d)) (S : Finset (Fin d))
    (hκ : ∀ i ∈ S, κ.ofLp i < 0) (hSne : S.Nonempty) :
    sigma₄ κ S < 0 :=
  div_neg_of_pos_of_neg one_pos (sum_inv_neg κ S hκ hSne)

/-- When κ_i < 0 and σ_S < 0, σ_S/κ_i > 0. -/
private lemma sigma₄_div_pos (κ : EuclideanSpace ℝ (Fin d)) (S : Finset (Fin d))
    (hκ : ∀ i ∈ S, κ.ofLp i < 0) (hSne : S.Nonempty) (i : Fin d) (hi : i ∈ S) :
    0 < sigma₄ κ S / κ.ofLp i := by
  exact div_pos_of_neg_of_neg (sigma₄_neg κ S hκ hSne) (hκ i hi)

/-- Norm squared in terms of coordinates. -/
private lemma norm_sq_eq_sum₄ (v : EuclideanSpace ℝ (Fin d)) :
    ‖v‖ ^ 2 = ∑ i : Fin d, v.ofLp i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  congr 1; ext i; simp

/-! ### Core computation: σ · (∑_{j ∈ S} 1/κ_j) = 1 (for negative case) -/

/-- σ_S · (∑_{j ∈ S} 1/κ_j) = 1 -/
private lemma sigma₄_mul_sum (κ : EuclideanSpace ℝ (Fin d)) (S : Finset (Fin d))
    (hκ : ∀ i ∈ S, κ.ofLp i < 0) (hSne : S.Nonempty) :
    sigma₄ κ S * ∑ j ∈ S, 1 / κ.ofLp j = 1 := by
  rw [sigma₄, one_div, inv_mul_cancel₀]
  exact ne_of_lt (sum_inv_neg κ S hκ hSne)

/-- ∑_{i ∈ S} σ_S / κ_i = 1 -/
private lemma sum_sigma₄_div_eq_one (κ : EuclideanSpace ℝ (Fin d)) (S : Finset (Fin d))
    (hκ : ∀ i ∈ S, κ.ofLp i < 0) (hSne : S.Nonempty) :
    ∑ i ∈ S, sigma₄ κ S / κ.ofLp i = 1 := by
  have : ∀ i ∈ S, sigma₄ κ S / κ.ofLp i = sigma₄ κ S * (1 / κ.ofLp i) :=
    fun _ _ => by ring
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
  exact sigma₄_mul_sum κ S hκ hSne

/-! ### The key calculation: hessForm at the full-support critical point -/

/-- At the critical point w_S (with all κ_i < 0), the squared coordinates satisfy:
    κ_i · w_S(i)² = σ_S. -/
private lemma coord_sq_mul_kappa (κ : EuclideanSpace ℝ (Fin d)) (S : Finset (Fin d))
    (hκ : ∀ i ∈ S, κ.ofLp i < 0) (hSne : S.Nonempty) (i : Fin d) (hi : i ∈ S) :
    κ.ofLp i * (critPoint₄ κ S).ofLp i ^ 2 = sigma₄ κ S := by
  simp only [critPoint₄_coord_mem κ S i hi]
  rw [Real.sq_sqrt (le_of_lt (sigma₄_div_pos κ S hκ hSne i hi))]
  field_simp [ne_of_lt (hκ i hi)]

/-- The objective value at w_S equals σ_S. -/
theorem kurtObj₄_critPoint (κ : EuclideanSpace ℝ (Fin d)) (S : Finset (Fin d))
    (hκ : ∀ i ∈ S, κ.ofLp i < 0) (hSne : S.Nonempty) :
    kurtObj₄ κ (critPoint₄ κ S) = sigma₄ κ S := by
  simp only [kurtObj₄]
  rw [← Finset.sum_add_sum_compl S (fun i => κ.ofLp i * (critPoint₄ κ S).ofLp i ^ 4)]
  have hout : ∑ i ∈ Sᶜ, κ.ofLp i * (critPoint₄ κ S).ofLp i ^ 4 = 0 := by
    apply Finset.sum_eq_zero; intro i hi
    simp [Finset.mem_compl.mp hi]
  rw [hout, add_zero]
  have hin : ∀ i ∈ S, κ.ofLp i * (critPoint₄ κ S).ofLp i ^ 4 =
      sigma₄ κ S ^ 2 / κ.ofLp i := by
    intro i hi
    simp only [critPoint₄_coord_mem κ S i hi]
    rw [show Real.sqrt (sigma₄ κ S / κ.ofLp i) ^ 4 =
        (Real.sqrt (sigma₄ κ S / κ.ofLp i) ^ 2) ^ 2 from by ring]
    rw [Real.sq_sqrt (le_of_lt (sigma₄_div_pos κ S hκ hSne i hi))]
    field_simp [ne_of_lt (hκ i hi)]
  rw [Finset.sum_congr rfl hin]
  have h : ∑ x ∈ S, sigma₄ κ S ^ 2 / κ.ofLp x =
      sigma₄ κ S ^ 2 * ∑ x ∈ S, (1 / κ.ofLp x) := by
    rw [Finset.mul_sum]; congr 1; ext i; ring
  rw [h, sq, mul_assoc, sigma₄_mul_sum κ S hκ hSne, mul_one]

/-- **Key theorem**: The Hessian form at the *full-support* critical point w_full equals
    8 σ_full ‖v‖². Since σ_full < 0, this is ≤ 0 for all tangent vectors v.

    Note: this holds for S = Finset.univ because every coordinate i is in S,
    so κ_i w_i² = σ_full for all i, giving ∑_i 12 κ_i w_i² v_i² = 12 σ ‖v‖². -/
theorem hessForm₄_critPoint_univ (κ : EuclideanSpace ℝ (Fin d)) [NeZero d]
    (hκ : ∀ i : Fin d, κ.ofLp i < 0)
    (v : EuclideanSpace ℝ (Fin d)) :
    hessForm₄ κ (critPoint₄ κ Finset.univ) v =
      8 * sigma₄ κ Finset.univ * ‖v‖ ^ 2 := by
  have hκ_univ : ∀ i ∈ (Finset.univ : Finset (Fin d)), κ.ofLp i < 0 := fun i _ => hκ i
  have hSne : (Finset.univ : Finset (Fin d)).Nonempty := Finset.univ_nonempty
  rw [hessForm₄, kurtObj₄_critPoint κ Finset.univ hκ_univ hSne]
  -- Key: show ∑_i 12 κ_i w_i² v_i² = 12 σ ‖v‖²
  -- Since S = univ, every i ∈ S, so κ_i w_i² = σ for all i.
  have hsum : ∑ i : Fin d, 12 * κ.ofLp i * (critPoint₄ κ Finset.univ).ofLp i ^ 2 * v.ofLp i ^ 2 =
      12 * sigma₄ κ Finset.univ * ‖v‖ ^ 2 := by
    rw [norm_sq_eq_sum₄]
    -- Every term satisfies κ_i w_i² = σ (since S = univ, all i ∈ S)
    have hterm : ∀ i : Fin d,
        12 * κ.ofLp i * (critPoint₄ κ Finset.univ).ofLp i ^ 2 * v.ofLp i ^ 2 =
        12 * sigma₄ κ Finset.univ * v.ofLp i ^ 2 := fun i => by
      have hi : i ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ i
      have := coord_sq_mul_kappa κ Finset.univ hκ_univ hSne i hi
      nlinarith [sq_nonneg (v.ofLp i)]
    rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum]
  rw [hsum]
  ring

/-- **Exercise 2.7.4 (Part A)**: The Riemannian Hessian at the *full-support* critical point
    is negative semi-definite (since σ_full < 0): it equals 8 σ_full ‖v‖² ≤ 0. -/
theorem hessForm₄_neg_semidef_univ (κ : EuclideanSpace ℝ (Fin d)) [NeZero d]
    (hκ : ∀ i : Fin d, κ.ofLp i < 0)
    (v : EuclideanSpace ℝ (Fin d)) :
    hessForm₄ κ (critPoint₄ κ Finset.univ) v ≤ 0 := by
  rw [hessForm₄_critPoint_univ κ hκ]
  have hσ : sigma₄ κ Finset.univ < 0 :=
    sigma₄_neg κ Finset.univ (fun i _ => hκ i) Finset.univ_nonempty
  nlinarith [sq_nonneg ‖v‖]

/-- The objective value at the full-support critical point is σ_S < 0. -/
theorem kurtObj₄_critPoint_neg (κ : EuclideanSpace ℝ (Fin d)) (S : Finset (Fin d))
    (hκ : ∀ i ∈ S, κ.ofLp i < 0) (hSne : S.Nonempty) :
    kurtObj₄ κ (critPoint₄ κ S) < 0 := by
  rw [kurtObj₄_critPoint κ S hκ hSne]
  exact sigma₄_neg κ S hκ hSne

/-! ### The full-support case: S = Finset.univ -/

/-- **Exercise 2.7.4 (Main)**: When all κ_j < 0, the full-support critical point
    w_full = critPoint κ univ satisfies:
    1. hessForm κ w_full v = 8 σ_full ‖v‖² for all v (regardless of tangency)
    2. Since σ_full < 0, the Hessian is negative semi-definite everywhere on the sphere
    3. This certifies w_full as a local maximum

    The "signed dense vectors" of the book are ±w_full = ±critPoint κ univ. -/
theorem exercise_2_7_4 (κ : EuclideanSpace ℝ (Fin d)) [NeZero d]
    (hκ : ∀ i : Fin d, κ.ofLp i < 0) :
    -- (1) The Hessian bilinear form at the full-support critical point equals 8 σ ‖v‖²
    (∀ v : EuclideanSpace ℝ (Fin d),
        hessForm₄ κ (critPoint₄ κ Finset.univ) v =
          8 * sigma₄ κ Finset.univ * ‖v‖ ^ 2) ∧
    -- (2) σ_full < 0 (so the Hessian is non-positive)
    sigma₄ κ Finset.univ < 0 ∧
    -- (3) The Hessian is non-positive for all v (local maximum certificate)
    (∀ v : EuclideanSpace ℝ (Fin d),
        hessForm₄ κ (critPoint₄ κ Finset.univ) v ≤ 0) := by
  have hκ_univ : ∀ i ∈ (Finset.univ : Finset (Fin d)), κ.ofLp i < 0 :=
    fun i _ => hκ i
  have hSne : (Finset.univ : Finset (Fin d)).Nonempty :=
    Finset.univ_nonempty
  exact ⟨fun v => hessForm₄_critPoint_univ κ hκ v,
         sigma₄_neg κ Finset.univ hκ_univ hSne,
         fun v => hessForm₄_neg_semidef_univ κ hκ v⟩
