/-
  深度表征学习 第2章 练习2.1

  证明：对于任何对称矩阵 A，问题 max_{U ∈ O(D,d)} tr(U^T A U) 的解是矩阵 U*，
  其列是 A 的前 d 个单位特征向量。

  这是主成分分析(PCA)的核心数学基础。
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.Spectrum

namespace Chapter2Exercise21

open Matrix
open BigOperators

variable {D d : ℕ} [NeZero D] [NeZero d]
variable (hd : d ≤ D) -- 子空间维度不超过环境维度

/-!
## 问题陈述

给定：
- A ∈ ℝ^{D×D} 是对称矩阵
- U ∈ O(D,d) 是列正交矩阵（即 U^T U = I_d）

求解优化问题：
  max_{U ∈ O(D,d)} tr(U^T A U)

定理：最优解 U* 的列是 A 的前 d 个特征向量（按特征值降序排列）
-/

/-- 列正交矩阵的定义：U^T·U = I -/
def IsColumnOrthogonal (U : Matrix (Fin D) (Fin d) ℝ) : Prop :=
  Uᵀ * U = 1

/-- 对称矩阵的定义：A^T = A -/
def IsSymmetric (A : Matrix (Fin D) (Fin D) ℝ) : Prop :=
  Aᵀ = A

/-!
## 引理1：迹的性质

迹的循环性：tr(ABC) = tr(CAB) = tr(BCA)
这对于理解目标函数至关重要
-/

/-- 迹在矩阵乘法下的循环性 -/
lemma trace_cyclic {n m k : ℕ}
    (A : Matrix (Fin n) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin n) ℝ) :
    trace (A * B * C) = trace (C * A * B) := by
  -- 使用Mathlib中的迹循环性质
  rw [mul_assoc]
  rw [Matrix.trace_mul_comm]
  rw [mul_assoc]

/-!
## 引理2：目标函数的重新表述

tr(U^T A U) 可以理解为：
- 将 A 变换到 U 张成的子空间
- 计算限制在该子空间上的迹

关键观察：对于列正交的 U，
  tr(U^T A U) = Σᵢ uᵢ^T A uᵢ
其中 uᵢ 是 U 的第 i 列
-/

/-- 目标函数展开为列向量的二次型之和 -/
lemma objective_as_quadratic_forms
    (A : Matrix (Fin D) (Fin D) ℝ)
    (U : Matrix (Fin D) (Fin d) ℝ)
    (hU : IsColumnOrthogonal U) :
    trace (Uᵀ * A * U) = ∑ i : Fin d, dotProduct (U.transpose i) (A.mulVec (Uᵀ i)) := by
  sorry -- 完整证明需要展开迹和矩阵乘法的定义

/-!
## 引理3：瑞利商（Rayleigh Quotient）

对于单位向量 v，二次型 v^T A v 被称为瑞利商。
对于对称矩阵 A：
  λ_min ≤ v^T A v ≤ λ_max
当 v 是对应的特征向量时取得等号。
-/

/-- 瑞利商的定义 -/
def RayleighQuotient (A : Matrix (Fin D) (Fin D) ℝ) (v : Fin D → ℝ) : ℝ :=
  dotProduct v (A.mulVec v)

/-- 单位向量的瑞利商被最大特征值界定 -/
lemma rayleigh_quotient_bounded_by_max_eigenvalue
    (A : Matrix (Fin D) (Fin D) ℝ)
    (hA : IsSymmetric A)
    (v : Fin D → ℝ)
    (hv : ‖v‖ = 1) :
    RayleighQuotient A v ≤ ⨆ (λ : ℝ) (_ : Module.End.HasEigenvalue (toLin' A) λ), λ := by
  sorry -- 需要谱定理和特征值的性质

/-!
## 引理4：正交向量的瑞利商之和

关键洞察：如果 u₁, ..., u_d 是正交的单位向量，则
  Σᵢ uᵢ^T A uᵢ ≤ λ₁ + λ₂ + ... + λ_d
当且仅当 uᵢ 是前 d 个特征向量时取得等号。
-/

/-- 正交向量组的瑞利商之和被前d个特征值之和界定 -/
lemma sum_rayleigh_quotients_bounded
    (A : Matrix (Fin D) (Fin D) ℝ)
    (hA : IsSymmetric A)
    (U : Matrix (Fin D) (Fin d) ℝ)
    (hU : IsColumnOrthogonal U)
    (λ : Fin D → ℝ)
    (hλ_ordered : ∀ i j : Fin D, i < j → λ j ≤ λ i) -- 特征值降序排列
    (hλ_eigenvalues : ∀ i, Module.End.HasEigenvalue (toLin' A) (λ i)) :
    ∑ i : Fin d, RayleighQuotient A (Uᵀ i) ≤ ∑ i : Fin d, λ i := by
  sorry -- 完整证明需要Courant-Fischer极小极大定理

/-!
## 主定理：PCA的最优性

证明策略：
1. 将目标函数表示为瑞利商之和
2. 使用引理4得到上界
3. 证明当U的列是前d个特征向量时达到上界
4. 因此这是全局最优解
-/

/-- 主定理：前d个特征向量最大化迹 -/
theorem pca_optimality
    (A : Matrix (Fin D) (Fin D) ℝ)
    (hA : IsSymmetric A)
    (λ : Fin D → ℝ)
    (hλ_ordered : ∀ i j : Fin D, i < j → λ j ≤ λ i)
    (v : Fin D → Fin D → ℝ) -- 特征向量
    (hλ_eigen : ∀ i, Module.End.HasEigenvalue (toLin' A) (λ i))
    (hv_eigen : ∀ i, Module.End.HasEigenvector (toLin' A) (λ i) (v i))
    (hv_ortho : ∀ i j, i ≠ j → dotProduct (v i) (v j) = 0)
    (hv_unit : ∀ i, ‖v i‖ = 1) :
    let U_star : Matrix (Fin D) (Fin d) ℝ := fun i j => v j i -- 前d个特征向量作为列
    ∀ (U : Matrix (Fin D) (Fin d) ℝ),
      IsColumnOrthogonal U →
      trace (Uᵀ * A * U) ≤ trace (U_starᵀ * A * U_star) := by
  intro U_star U hU
  -- 证明思路：
  -- 1. 使用 objective_as_quadratic_forms 展开两边
  -- 2. 应用 sum_rayleigh_quotients_bounded 得到 LHS ≤ Σλᵢ
  -- 3. 直接计算显示 RHS = Σλᵢ (因为特征向量的性质)
  -- 4. 因此 LHS ≤ RHS
  sorry

/-!
## 推论：唯一性（模正交变换）

最优解在正交变换下是唯一的：
如果 λ₁ > λ₂ > ... > λ_d（特征值严格递减），
则 U* 的列空间唯一确定（但列可以进行正交旋转）。
-/

/-- 在特征值不重复的情况下，最优子空间唯一 -/
theorem pca_uniqueness_up_to_rotation
    (A : Matrix (Fin D) (Fin D) ℝ)
    (hA : IsSymmetric A)
    (λ : Fin D → ℝ)
    (hλ_strict : ∀ i j : Fin D, i < j → λ j < λ i) -- 严格递减
    (U₁ U₂ : Matrix (Fin D) (Fin d) ℝ)
    (hU₁ : IsColumnOrthogonal U₁)
    (hU₂ : IsColumnOrthogonal U₂)
    (hU₁_opt : ∀ U, IsColumnOrthogonal U → trace (Uᵀ * A * U) ≤ trace (U₁ᵀ * A * U₁))
    (hU₂_opt : ∀ U, IsColumnOrthogonal U → trace (Uᵀ * A * U) ≤ trace (U₂ᵀ * A * U₂)) :
    ∃ (Q : Matrix (Fin d) (Fin d) ℝ), IsColumnOrthogonal Q ∧ U₂ = U₁ * Q := by
  sorry -- 证明需要特征子空间的理论

/-!
## 几何解释

定理的几何意义：
1. A 的特征向量定义了 ℝᴰ 的主方向
2. 沿着这些方向，数据的方差（由A编码）最大
3. 前 d 个特征向量张成了捕获最多方差的 d 维子空间
4. 这正是PCA寻找的低维表示

在第2章的上下文中：
- A 通常是数据的协方差矩阵
- U* 的列形成了最优的低维基
- 投影 U* U*ᵀ x 给出最佳的低秩近似
-/

/-!
## 计算方面的说明

虽然这个定理给出了理论上的最优解，但在实践中：
1. 计算所有D个特征值/向量代价高昂（O(D³)）
2. 幂迭代法可以高效计算前几个主成分（见第2章第297-346行）
3. 随机化方法可以进一步加速（见后续章节）

这个理论结果为实际算法提供了正确性保证。
-/

end Chapter2Exercise21

/-!
## 练习扩展

读者可以尝试：

1. 完成所有 sorry 的证明
2. 推广到加权迹：tr(W (U^T A U))，其中 W 是对角权重矩阵
3. 证明贪婪算法的正确性：逐一找最大特征向量
4. 连接到奇异值分解(SVD)：U* 对应于 A 的前 d 个左奇异向量
5. 分析扰动理论：当 A 被小扰动时，U* 如何变化？

这些扩展将深化对PCA数学基础的理解。
-/
