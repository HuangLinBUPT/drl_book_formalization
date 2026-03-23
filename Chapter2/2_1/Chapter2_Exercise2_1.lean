/-
  深度表征学习 第2章 练习2.1

  证明：对于任何对称矩阵 A，问题 max_{U ∈ O(D,d)} tr(U^T A U) 的解是矩阵 U*，
  其列是 A 的前 d 个单位特征向量。

  这是主成分分析(PCA)的核心数学基础。

  基于 Ky Fan 最大值原理（Ky Fan's Maximum Principle）的形式化。
-/

import Mathlib

/-!
# 主成分分析定理 (Ky Fan 最大值原理)

我们形式化并证明：对于任意实对称矩阵 A（尺寸为 D×D），
优化问题

  `max { tr(Uᵀ A U) | U ∈ ℝ^{D×d}, Uᵀ U = I_d }`

的解是矩阵 U⋆，其列是 A 的 d 个最大特征值对应的特征向量。
等价地，最大值等于前 d 个特征值之和。

这也被称为 **Ky Fan 最大值原理** 或 **Ky Fan trace 不等式**。
-/

open Matrix Finset BigOperators

noncomputable section

namespace Chapter2Exercise21

variable {D d : ℕ}

/-- The sum of the `d` largest values of a function `Fin D → ℝ`.
Defined as the supremum over all `d`-element subsets of `Fin D` of the sum of `f`
over the subset. -/
def sumLargest (f : Fin D → ℝ) (d : ℕ) (hd : d ≤ D) : ℝ :=
  ((Finset.univ : Finset (Fin D)).powersetCard d).sup'
    (by rw [Finset.powersetCard_nonempty]; simp [Finset.card_univ]; exact hd)
    (fun s => ∑ i ∈ s, f i)

set_option maxHeartbeats 800000 in
/-- **Ky Fan's Maximum Principle (upper bound)**:
For any real symmetric `D × D` matrix `A` and any `D × d` matrix `U` with orthonormal
columns (`Uᴴ U = I`), we have `tr(Uᴴ A U) ≤ Σ (top d eigenvalues of A)`. -/
theorem principal_components_bound (hd : d ≤ D)
    (A : Matrix (Fin D) (Fin D) ℝ) (hA : A.IsHermitian)
    (U : Matrix (Fin D) (Fin d) ℝ) (hU : U.conjTranspose * U = 1) :
    (U.conjTranspose * A * U).trace ≤ sumLargest hA.eigenvalues d hd := by
  -- Let $V = P^* U$ (matrix product). Since $P$ is unitary and $U$ has orthonormal columns ($U^* U = I$), $V$ also has orthonormal columns: $V^* V = U^* P P^* U = U^* U = I$.
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin D) (Fin D) ℝ, P.conjTranspose * P = 1 ∧ A = P * Matrix.diagonal (hA.eigenvalues) * P.conjTranspose := by
    have := hA.spectral_theorem;
    refine' ⟨ _, _, _ ⟩;
    exact ( hA.eigenvectorUnitary : Matrix ( Fin D ) ( Fin D ) ℝ );
    · simp +decide [ ← Matrix.ext_iff ];
      intro i j; have := hA.eigenvectorBasis.orthonormal; simp +decide [ orthonormal_iff_ite ] at this;
      convert this i j using 1 ; simp +decide [ Matrix.mul_apply, inner ] ; ring!;
      ac_rfl;
    · convert this using 1;
  -- Let $V = P^* U$ (matrix product). Since $P$ is unitary and $U$ has orthonormal columns ($U^* U = I$), $V$ also has orthonormal columns: $V^* V = U^* P P^* U = U^* U = I$ and $\text{tr}(V^* \text{diag}(\lambda) V) = \sum_{j=1}^D \lambda_j w_j$ where $w_j = \sum_{i=1}^d |V_{ji}|^2$.
  set V : Matrix (Fin D) (Fin d) ℝ := P.conjTranspose * U
  have hV : V.conjTranspose * V = 1 := by
    simp +zetaDelta at *;
    simp_all +decide [ Matrix.mul_assoc ];
    simp_all +decide [ ← Matrix.mul_assoc, mul_eq_one_comm.mp hP.1 ]
  have h_trace : (U.conjTranspose * A * U).trace = ∑ j, hA.eigenvalues j * ∑ i, V j i ^ 2 := by
    -- Expanding the trace using the definition of $V$, we get:
    have h_trace_expanded : (U.conjTranspose * A * U).trace = (V.conjTranspose * Matrix.diagonal (hA.eigenvalues) * V).trace := by
      simp +zetaDelta at *; (
      simp +decide [ hP.2, Matrix.mul_assoc ])
    generalize_proofs at *; (
    convert h_trace_expanded using 1 ; simp +decide [ Matrix.trace, Matrix.mul_apply, sq ] ; ring!;
    simp +decide [ Matrix.mul_apply, sq, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ; ring!;
    simp +decide [ Matrix.diagonal ] ; ring!;
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm ) |> Eq.trans <| Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring;)
  generalize_proofs at *; (
  -- Since $V$ has orthonormal columns, we have $0 \leq w_j \leq 1$ for all $j$ and $\sum_{j=1}^D w_j = d$.
  have h_w_bounds : ∀ j, 0 ≤ ∑ i, V j i ^ 2 ∧ ∑ i, V j i ^ 2 ≤ 1 := by
    intro j
    have h_w_j : ∑ i, V j i ^ 2 ≤ 1 := by
      have h_norm_sq_le_one : ∀ j, ∑ i, (V j i)^2 ≤ 1 := by
        intro j
        have h_norm_sq_le_one : ∑ i, (V j i)^2 = (V * V.conjTranspose) j j := by
          simp +decide [ sq, Matrix.mul_apply ]
        have h_norm_sq_le_one : (V * V.conjTranspose) * (V * V.conjTranspose) = V * V.conjTranspose := by
          simp_all +decide [ ← Matrix.mul_assoc ];
          simp_all +decide [ Matrix.mul_assoc ]
        generalize_proofs at *; (
        have h_norm_sq_le_one : (V * V.conjTranspose) j j = ∑ i, (V * V.conjTranspose) j i ^ 2 := by
          replace h_norm_sq_le_one := congr_fun ( congr_fun h_norm_sq_le_one j ) j; simp_all +decide [ Matrix.mul_apply, sq ] ;
          simp_all +decide [ mul_comm ]
        generalize_proofs at *; (
        contrapose! h_norm_sq_le_one;
        rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ j ) ] at *;
        exact ne_of_lt ( lt_add_of_lt_of_nonneg ( by nlinarith only [ h_norm_sq_le_one, ‹∑ i, V j i ^ 2 = ( V * Vᴴ ) j j› ] ) ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) )))
      generalize_proofs at *; (
      exact h_norm_sq_le_one j)
    exact ⟨Finset.sum_nonneg fun _ _ => sq_nonneg _, h_w_j⟩
  have h_w_sum : ∑ j, ∑ i, V j i ^ 2 = d := by
    have h_w_sum : ∑ j, ∑ i, V j i ^ 2 = Matrix.trace (V * V.conjTranspose) := by
      simp +decide [ Matrix.trace, Matrix.mul_apply, sq ]
    generalize_proofs at *; (
    rw [ h_w_sum, Matrix.trace_mul_comm ] ; aesop;)
  generalize_proofs at *; (
  -- Let $S$ be the set of indices corresponding to the $d$ largest eigenvalues of $A$.
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin D), S.card = d ∧ ∀ j ∈ S, ∀ k ∉ S, hA.eigenvalues j ≥ hA.eigenvalues k := by
    -- By definition of `sumLargest`, there exists a subset `S` of size `d` such that the sum of the eigenvalues over `S` is at least as large as the sum over any other subset of size `d`.
    have h_exists_S : ∃ S : Finset (Fin D), S.card = d ∧ ∀ T : Finset (Fin D), T.card = d → ∑ j ∈ S, hA.eigenvalues j ≥ ∑ j ∈ T, hA.eigenvalues j := by
      have h_max_sum : ∃ S ∈ Finset.powersetCard d (Finset.univ : Finset (Fin D)), ∀ T ∈ Finset.powersetCard d (Finset.univ : Finset (Fin D)), ∑ j ∈ S, hA.eigenvalues j ≥ ∑ j ∈ T, hA.eigenvalues j := by
        apply_rules [ Finset.exists_max_image ] ; norm_num [ Finset.mem_powersetCard, hd ] ;
      generalize_proofs at *; (
      exact ⟨ h_max_sum.choose, Finset.mem_powersetCard.mp h_max_sum.choose_spec.1 |>.2, fun T hT => h_max_sum.choose_spec.2 T <| Finset.mem_powersetCard.mpr ⟨ Finset.subset_univ _, hT ⟩ ⟩)
    generalize_proofs at *; (
    obtain ⟨ S, hS₁, hS₂ ⟩ := h_exists_S; use S; refine' ⟨ hS₁, fun j hj k hk => _ ⟩ ; specialize hS₂ ( Insert.insert k ( S.erase j ) ) ; simp_all +decide [ Finset.card_insert_of_notMem, Finset.card_erase_of_mem ] ;
    grind)
  generalize_proofs at *; (
  -- Let $m = \min_{j \in S} \lambda_j$.
  obtain ⟨m, hm⟩ : ∃ m : ℝ, (∀ j ∈ S, hA.eigenvalues j ≥ m) ∧ (∀ k ∉ S, hA.eigenvalues k ≤ m) := by
    by_cases hS_empty : S = ∅ <;> simp +decide [ hS_empty ] at hS ⊢
    generalize_proofs at *; (
    exact ⟨ ∑ j, |hA.eigenvalues j|, fun k => le_trans ( le_abs_self _ ) ( Finset.single_le_sum ( fun j _ => abs_nonneg ( hA.eigenvalues j ) ) ( Finset.mem_univ k ) ) ⟩);
    exact ⟨ Finset.min' ( S.image hA.eigenvalues ) ⟨ _, Finset.mem_image_of_mem _ ( Classical.choose_spec ( Finset.nonempty_of_ne_empty hS_empty ) ) ⟩, fun j hj => Finset.min'_le _ _ ( Finset.mem_image_of_mem _ hj ), fun k hk => Finset.min'_mem ( S.image hA.eigenvalues ) ⟨ _, Finset.mem_image_of_mem _ ( Classical.choose_spec ( Finset.nonempty_of_ne_empty hS_empty ) ) ⟩ |> fun x => by obtain ⟨ j, hj, hj' ⟩ := Finset.mem_image.mp x; linarith [ hS.2 j hj k hk ] ⟩
  generalize_proofs at *; (
  -- Then $\sum_{j \in S} \lambda_j - \sum_{j} \lambda_j w_j \geq m \sum_{j \in S} (1 - w_j) - m \sum_{j \notin S} w_j = m(d - \sum_{j} w_j) = 0$.
  have h_sum_ineq : ∑ j ∈ S, hA.eigenvalues j - ∑ j, hA.eigenvalues j * ∑ i, V j i ^ 2 ≥ m * (d - ∑ j, ∑ i, V j i ^ 2) := by
    have h_sum_ineq : ∑ j ∈ S, hA.eigenvalues j - ∑ j, hA.eigenvalues j * ∑ i, V j i ^ 2 ≥ ∑ j ∈ S, m * (1 - ∑ i, V j i ^ 2) - ∑ j∉S, m * ∑ i, V j i ^ 2 := by
      have h_sum_ineq : ∑ j ∈ S, hA.eigenvalues j - ∑ j, hA.eigenvalues j * ∑ i, V j i ^ 2 ≥ ∑ j ∈ S, (hA.eigenvalues j * (1 - ∑ i, V j i ^ 2)) - ∑ j∉S, (hA.eigenvalues j * ∑ i, V j i ^ 2) := by
        simp +decide [ mul_sub, Finset.sum_sub_distrib, Finset.compl_eq_univ_sdiff ]
      generalize_proofs at *; (
      refine le_trans ?_ h_sum_ineq;
      exact sub_le_sub ( Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right ( hm.1 j hj ) ( sub_nonneg.2 ( h_w_bounds j |>.2 ) ) ) ( Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right ( hm.2 j ( Finset.mem_compl.1 hj ) ) ( h_w_bounds j |>.1 ) ))
    generalize_proofs at *; (
    convert h_sum_ineq using 1 ; norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, h_w_sum ] ; ring;
    rw [ Finset.compl_eq_univ_sdiff ] ; norm_num [ h_w_sum, hS.1 ] ; ring;)
  generalize_proofs at *; (
  -- Since $\sum_{j} w_j = d$, we have $m(d - \sum_{j} w_j) = 0$.
  have h_zero : m * (d - ∑ j, ∑ i, V j i ^ 2) = 0 := by
    rw [ h_w_sum, sub_self, MulZeroClass.mul_zero ]
  generalize_proofs at *; (
  exact h_trace.symm ▸ le_trans ( by linarith ) ( Finset.le_sup' ( fun s => ∑ i ∈ s, hA.eigenvalues i ) ( Finset.mem_powersetCard.mpr ⟨ Finset.subset_univ S, by aesop ⟩ ) )))))))

/-- **Ky Fan's Maximum Principle (attainment)**:
The upper bound is tight — there exists a `D × d` matrix with orthonormal columns
(formed from eigenvectors of `A` for the `d` largest eigenvalues) that achieves
`tr(Uᴴ A U) = Σ (top d eigenvalues of A)`. -/
theorem principal_components_attained (hd : d ≤ D)
    (A : Matrix (Fin D) (Fin D) ℝ) (hA : A.IsHermitian) :
    ∃ U : Matrix (Fin D) (Fin d) ℝ,
      U.conjTranspose * U = 1 ∧
      (U.conjTranspose * A * U).trace = sumLargest hA.eigenvalues d hd := by
  -- Let's choose any subset S of size d with the maximum sum of eigenvalues.
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin D), S.card = d ∧ (∑ i ∈ S, hA.eigenvalues i) = sumLargest hA.eigenvalues d hd := by
    have h_max_exists : ∃ S ∈ Finset.univ.powersetCard d, ∀ T ∈ Finset.univ.powersetCard d, ∑ i ∈ T, hA.eigenvalues i ≤ ∑ i ∈ S, hA.eigenvalues i := by
      apply_rules [ Finset.exists_max_image ] ; aesop;
    obtain ⟨ S, hS₁, hS₂ ⟩ := h_max_exists; use S; simp_all +decide [ sumLargest ] ;
    exact le_antisymm ( Finset.le_sup' ( fun s => ∑ i ∈ s, hA.eigenvalues i ) ( Finset.mem_powersetCard.mpr ⟨ Finset.subset_univ _, hS₁ ⟩ ) ) ( Finset.sup'_le _ _ fun s hs => hS₂ s <| Finset.mem_powersetCard.mp hs |>.2 );
  obtain ⟨e, he⟩ : ∃ e : Fin d ↪ Fin D, Finset.image e Finset.univ = S := by
    obtain ⟨e, he⟩ : ∃ e : Fin d ≃ S, True := by
      exact ⟨ Fintype.equivOfCardEq <| by aesop, trivial ⟩;
    refine' ⟨ ⟨ fun i => e i, _ ⟩, _ ⟩ <;> simp_all +decide [ Function.Injective, Finset.ext_iff ];
    exact fun a => ⟨ fun ⟨ i, hi ⟩ => hi ▸ Subtype.mem _, fun ha => ⟨ e.symm ⟨ a, ha ⟩, by simp +decide ⟩ ⟩;
  -- Let $U$ be the matrix whose columns are the eigenvectors corresponding to the eigenvalues in $S$.
  obtain ⟨U, hU⟩ : ∃ U : Matrix (Fin D) (Fin d) ℝ, U.conjTranspose * U = 1 ∧ A * U = U * Matrix.diagonal (fun i => hA.eigenvalues (e i)) := by
    use Matrix.of (fun i j => hA.eigenvectorBasis (e j) i);
    constructor;
    · ext i j; simp +decide [ Matrix.mul_apply, hA.eigenvectorBasis.orthonormal.1 ] ;
      have := hA.eigenvectorBasis.orthonormal; simp_all +decide [ orthonormal_iff_ite ] ;
      convert this ( e i ) ( e j ) using 1 ; simp +decide [ inner, mul_comm ];
      simp +decide [ Matrix.one_apply, e.injective.eq_iff ];
    · ext i j; have := hA.mulVec_eigenvectorBasis ( e j ) ; simp_all +decide [ Matrix.mulVec, dotProduct ] ;
      simpa [ mul_comm ] using congr_fun this i;
  refine' ⟨ U, hU.1, _ ⟩;
  rw [ ← hS.2, ← he, Finset.sum_image ];
  · simp +decide [ Matrix.mul_assoc, hU.2 ];
    rw [ ← Matrix.mul_assoc, Matrix.trace ];
    simp_all +decide [ Matrix.mul_apply, Matrix.diagonal ];
  · exact e.injective.injOn

/-- **主成分分析定理**：结合上界和可达性，
对于列正交的 D×d 矩阵 U，max tr(Uᵀ A U) 等于 A 的前 d 个最大特征值之和。 -/
theorem principal_components (hd : d ≤ D)
    (A : Matrix (Fin D) (Fin D) ℝ) (hA : A.IsHermitian) :
    IsGreatest
      {x | ∃ U : Matrix (Fin D) (Fin d) ℝ,
        U.conjTranspose * U = 1 ∧ x = (U.conjTranspose * A * U).trace}
      (sumLargest hA.eigenvalues d hd) := by
  constructor
  · -- The value is achieved
    obtain ⟨U, hU, htr⟩ := principal_components_attained hd A hA
    exact ⟨U, hU, htr.symm⟩
  · -- It's an upper bound
    rintro x ⟨U, hU, rfl⟩
    exact principal_components_bound hd A hA U hU

end Chapter2Exercise21