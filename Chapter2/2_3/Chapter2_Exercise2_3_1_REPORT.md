# 第2章 练习2.3.1 形式化报告：GL(d) 对称性

## 习题陈述

**来源**：深度表征学习书籍，第2章，练习2.3 第1部分

**非形式化陈述**：考虑模型 X = UZ，其中 X、U、Z 为大小相容的矩阵。证明：若 A 是任意大小相容的方阵可逆矩阵，则 (UA, A⁻¹Z) 在该模型下同样等于 X。我们称之为 **GL(d) 对称性**。

## 数学背景

### 线性模型
- **数据矩阵**：X ∈ ℝ^(D×N)（D 维数据，N 个样本）
- **字典/基**：U ∈ ℝ^(D×d)（D 维空间中的 d 个基向量）
- **系数**：Z ∈ ℝ^(d×N)（每个样本的 d 个系数）
- **模型**：X = UZ

### GL(d) 对称性
一般线性群 GL(d) 由所有 d×d 可逆矩阵组成。该练习说明分解 X = UZ **不唯一**：任意可逆变换 A ∈ GL(d) 都给出另一个有效分解。

## 形式化方案

### 类型设置
```lean
variable {D d N : Type*} [Fintype D] [Fintype d] [Fintype N]
```
使用类型变量表示维度，以最大化通用性。所有矩阵定义在 ℝ 上。

### 主定理：`gl_d_symmetry`

**陈述**：
```lean
theorem gl_d_symmetry
    (U : Matrix D d ℝ)
    (Z : Matrix d N ℝ)
    (A : Matrix d d ℝ)
    (hA : IsUnit A.det) :
    (U * A) * (A⁻¹ * Z) = U * Z
```

**证明策略**：
证明是直接的代数推导：

1. **(UA)(A⁻¹Z)** — 给定表达式
2. **= U(A(A⁻¹Z))** — 矩阵乘法结合律
3. **= U((AA⁻¹)Z)** — 矩阵乘法结合律
4. **= U(IZ)** — 逆元性质：AA⁻¹ = I（需要 A 可逆）
5. **= UZ** — 单位元性质：IZ = Z

**使用的关键引理**：
- `Matrix.mul_assoc`：矩阵乘法满足结合律
- `Matrix.nonsing_inv_mul`：当 A 可逆时，AA⁻¹ = I
- `Matrix.one_mul`：单位矩阵是乘法单位元
- `IsUnit A.det`：可逆性条件（det(A) ≠ 0）

### 附加定理

#### `model_invariance_under_GLd`
证明若 X = UZ，则对任意可逆 A，X = (UA)(A⁻¹Z)。

这是一个直接推论，明确指出模型方程在该变换下保持不变。

#### `factorization_non_uniqueness`
证明存在无穷多个分解：给定一个分解 X = UZ，可以构造另一个分解 (U', Z') = (UA, A⁻¹Z)，对任意可逆 A 均成立。

该定理描述了模型的**不可识别性**：若没有额外约束，仅凭对 X 的观测无法唯一确定 U 和 Z。

## 数学意义

### 为什么重要

1. **不可识别性**：模型 X = UZ 有无穷多个解。任意 (U, Z) 都可以变换为 (UA, A⁻¹Z)，其中 A ∈ GL(d)。

2. **需要约束条件**：为了唯一恢复 U（或 Z），需要额外假设：
   - **正交性**：U 的列正交归一（U^T U = I）→ 将 GL(d) 约简为正交群 O(d)
   - **统计独立性**：Z 的分量相互独立 → ICA 方法
   - **稀疏性**：Z 具有稀疏结构 → 字典学习

3. **与第2部分的联系**：练习2.3.2 证明了在对 Z 加独立性假设后，对称性群从 GL(d) 约简为仅含缩放和旋转（D₁QD₂ 形式）。

4. **几何解释**：GL(d) 对称性意味着表示空间可以任意变换（拉伸、旋转、剪切），而不改变观测值 X。

## 验证

形式化已验证类型检查通过：
```bash
cd lean_formalization
lake env lean Chapter2/2_3/Chapter2_Exercise2_3_1.lean
```

所有定理均无 `sorry` 编译通过——证明完整。

## Lean 4 技术说明

### 可逆性条件
使用 `IsUnit A.det` 表达 A 可逆。这等价于 det(A) ≠ 0，是 Mathlib 中处理可逆矩阵的标准方式。

### 矩阵逆的记号
- `A⁻¹` 是 Lean 中矩阵逆的记号
- 引理 `Matrix.nonsing_inv_mul` 需要 `IsUnit A.det` 的证明，才能得出 `A * A⁻¹ = 1`

### 不可计算性
`noncomputable section` 声明是必要的，因为矩阵逆和行列式在一般情况下不可计算。

## 参考文献

- **书籍**：深度表征学习，第2章，练习2.3
- **相关理论**：独立成分分析（ICA）、字典学习
- **Mathlib 模块**：
  - `Mathlib.Data.Matrix.Basic`
  - `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`
  - `Mathlib.LinearAlgebra.Matrix.Determinant`

## 后续工作

完成练习2.3的计划：
- **第2部分**：形式化 Az 具有不相关分量时 A 的特征刻画
- 证明 A 必须具有 D₁QD₂ 的形式（对角矩阵 × 正交矩阵 × 对角矩阵）
- 这将需要形式化：
  - 随机变量和协方差
  - 不相关分量条件
  - 极分解定理
