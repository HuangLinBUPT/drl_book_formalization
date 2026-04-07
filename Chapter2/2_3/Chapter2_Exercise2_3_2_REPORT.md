# 第2章 练习2.3.2 形式化报告：ICA 对称性分解

## 习题陈述

**来源**：深度表征学习书籍，第2章，练习2.3（`exercise:symmetry-identifiability`），第2部分

**非形式化陈述**：设 z 是零均值的随机向量，具有相互独立且正方差的分量 z_i（即 Cov(z) = Σ = diag(σ₁,...,σd)，σᵢ > 0）。对任意可逆方阵 A，若 Az 的各分量不相关（即 Cov(Az) 是对角矩阵），则 A 可以写成 A = D₁QD₂，其中 Q 是正交矩阵，D₁, D₂ 是对角矩阵。

**书中原文**：
> *"This links the 'independence' assumption in ICA to a 'symmetry breaking' effect, which only allows scale and rotational symmetries."*

## 数学背景

### ICA 模型的不可识别性
在独立成分分析（ICA）中，数据矩阵满足 X = UZ，其中 U 是未知字典，Z 是具有独立分量的系数矩阵。由练习2.3.1可知，模型具有 GL(d) 对称性：对任意可逆 A，(UA, A⁻¹Z) 产生同样的 X。本习题在 Z 满足独立分量假设的条件下，进一步限制了这种对称性。

### 不相关条件的代数含义
设 Cov(z) = Σ = diagonal(σ)，σᵢ > 0。则：
- Cov(Az) = A Cov(z) Aᵀ = A Σ Aᵀ
- Az 各分量不相关 ⟺ A Σ Aᵀ 是对角矩阵

### 核心结论的数学意义
A = D₁QD₂ 意味着：
- **D₂**：对 z 各分量做独立缩放
- **Q**：施加正交变换（旋转/反射）
- **D₁**：对变换后的分量再做独立缩放

因此，保持不相关性的变换恰好是"坐标缩放 + 正交旋转 + 坐标缩放"——对称性群从完整的 GL(d) 约简为 Diag × O(d) × Diag。

## 形式化方案

### 类型设置
```lean
variable {d : Type*} [Fintype d] [DecidableEq d]
```
使用有限类型 `d` 表示维度，支持任意有限索引类型（不仅限于 `Fin n`），保持最大通用性。所有矩阵定义在 `ℝ` 上。

### 条件的精确形式化

| 数学条件 | Lean 形式化 | 说明 |
|---------|------------|------|
| A 可逆 | `IsUnit A` | Mathlib 中可逆矩阵的标准表达 |
| Cov(z) = diag(σ)，σᵢ > 0 | `∀ i, 0 < σ i`（隐含 `diagonal σ` 作为协方差） | 独立性蕴含协方差对角；正方差即对角元为正 |
| Cov(Az) 对角 | `(A * diagonal σ * Aᵀ).IsDiag` | Cov(Az) = A Cov(z) Aᵀ = A Σ Aᵀ |
| Q ∈ O(d) | `Q ∈ Matrix.orthogonalGroup d ℝ` | 即 Q * Qᵀ = 1 |
| D₁, D₂ 对角 | `D₁.IsDiag`, `D₂.IsDiag` | `Matrix.IsDiag` 谓词 |

**注**：形式化定理比书中更强——只需协方差对角（不相关），无需完整的统计独立性假设。

---

## 证明结构

### 辅助引理层级

```
isUnit_diagonal_of_pos          正对角矩阵可逆
diag_sqrt_mul_transpose         D * Dᵀ = Σ（D = diag(√σ)）
posDef_mul_transpose_of_isUnit  可逆矩阵 B 满足 B * Bᵀ 正定
ortho_row_decomp                可逆矩阵且 BBᵀ 对角 ⟹ B = D₁Q（正交行分解）
        ↓
ica_symmetry_decomposition      主定理：A = D₁QD₂
        ↓
ica_symmetry_group_restriction  推论：存在对角向量 d₁, d₂ 使 A = diag(d₁)·Q·diag(d₂)
```

### 主证明策略

**核心思路**：通过引入对角矩阵 D = diag(√σ)，将问题化归为"正交行分解"问题。

**步骤 1**：令 D = diagonal(fun i => √(σ i))，B = A * D
- D 可逆（正对角元）⟹ B = A * D 可逆（可逆矩阵之积）

**步骤 2**：计算 B * Bᵀ = A * Σ * Aᵀ
```
B * Bᵀ = (A*D) * (A*D)ᵀ
       = (A*D) * (Dᵀ * Aᵀ)        -- 转置是反序的
       = A * (D * Dᵀ) * Aᵀ        -- 结合律
       = A * diagonal σ * Aᵀ       -- D * Dᵀ = Σ（因 D 对角且对称，D² = Σ）
```

**步骤 3**：由假设 (A * Σ * Aᵀ).IsDiag 得 (B * Bᵀ).IsDiag，即 B 的各行正交。

**步骤 4**：由 `ortho_row_decomp` 分解 B = D₁ * Q（Q 正交，D₁ 对角正定）。

**步骤 5**：令 D₂ = D⁻¹（对角矩阵的逆仍为对角），则：
```
A = (A * D) * D⁻¹ = B * D₂ = (D₁ * Q) * D₂ = D₁ * Q * D₂
```

### 关键引理 `ortho_row_decomp` 的证明

**命题**：若 B 可逆且 B * Bᵀ 对角，则 B = D₁ * Q（D₁ 对角，Q 正交）。

**证明**：
1. 由 `posDef_mul_transpose_of_isUnit`：B 可逆 ⟹ B * Bᵀ 正定
2. 由 `Matrix.PosDef.diag_pos`：正定矩阵的对角元均为正，故 (B * Bᵀ)ᵢᵢ > 0
3. 令 `rowSq i := (B * Bᵀ) i i`（第 i 行的平方范数）
4. 令 D₁ = diagonal(fun i => √(rowSq i))，由步骤2知 D₁ 可逆
5. 令 Q = D₁⁻¹ * B，则：
   - B = D₁ * (D₁⁻¹ * B) = D₁ * Q（由 D₁ * D₁⁻¹ = I）
   - Q * Qᵀ = D₁⁻¹ * B * Bᵀ * (D₁⁻¹)ᵀ = D₁⁻¹ * diagonal(rowSq) * D₁⁻¹ = I
     （B * Bᵀ = diagonal(rowSq) 因 B * Bᵀ 对角；D₁ = diag(√rowSq) 故 D₁² = diagonal(rowSq)）

---

## 关键 Mathlib 引理

| 引理 | 用途 |
|------|------|
| `Matrix.isUnit_iff_isUnit_det` | IsUnit A ↔ IsUnit A.det |
| `Matrix.det_diagonal` | det(diag(f)) = ∏ f i |
| `Finset.prod_pos` | 正数之积为正 |
| `Matrix.diagonal_transpose` | 对角矩阵转置等于自身 |
| `Matrix.diagonal_mul_diagonal` | diag(f) * diag(g) = diag(fun i => f i * g i) |
| `Real.mul_self_sqrt` | √x * √x = x（x ≥ 0 时） |
| `Real.sq_sqrt` | √x ^ 2 = x（x ≥ 0 时） |
| `Matrix.vecMul_injective_of_isUnit` | 可逆矩阵 ⟹ 左乘单射 |
| `Matrix.PosDef.mul_conjTranspose_self` | 行单射矩阵 A ⟹ A * Aᴴ 正定 |
| `Matrix.conjTranspose_eq_transpose_of_trivial` | 实矩阵共轭转置 = 普通转置 |
| `Matrix.PosDef.diag_pos` | 正定矩阵对角元为正 |
| `Matrix.inv_eq_right_inv` | 若 A * B = I 则 A⁻¹ = B |
| `Matrix.inv_diagonal` | (diag(v))⁻¹ = diag(Ring.inverse v) |
| `Matrix.transpose_nonsing_inv` | (A⁻¹)ᵀ = (Aᵀ)⁻¹ |
| `Matrix.mul_nonsing_inv` | A * A⁻¹ = 1（A 可逆时） |
| `Matrix.mem_orthogonalGroup_iff` | Q ∈ O(d) ↔ Q * Qᵀ = 1 |
| `Matrix.IsDiag.isDiag_diagonal` | diagonal(f) 满足 IsDiag |
| `Matrix.isDiag_iff_diagonal_diag` | A.IsDiag ↔ diagonal A.diag = A |
| `Matrix.detMonoidHom` | det : (n×n 矩阵, ×) →* (ℝ, ×) |

---

## 验证结果

```
#check @Chapter2Exercise23_2.ica_symmetry_decomposition
-- ∀ {d : Type u_1} [inst : Fintype d] [inst_1 : DecidableEq d]
--   (A : Matrix d d ℝ) (σ : d → ℝ),
--   IsUnit A → (∀ i, 0 < σ i) → (A * diagonal σ * Aᵀ).IsDiag →
--   ∃ D₁ D₂ Q, D₁.IsDiag ∧ D₂.IsDiag ∧ Q ∈ orthogonalGroup d ℝ ∧ A = D₁ * Q * D₂
```

**公理检查**：
```
#print axioms Chapter2Exercise23_2.ica_symmetry_decomposition
-- 'Chapter2Exercise23_2.ica_symmetry_decomposition' depends on axioms:
-- [propext, Classical.choice, Quot.sound]
```

✅ 仅依赖 Lean 4 标准公理，无自定义公理，无 `sorry`。

---

## 与书中的对照说明

### 条件对应

**书中**："z 的分量相互独立且正方差"
**Lean 中**：`σ : d → ℝ`，`∀ i, 0 < σ i`，协方差矩阵取为 `diagonal σ`

独立性蕴含不相关性（协方差对角），但反之不成立。形式化只需要不相关性（协方差对角）即可推导出 D₁QD₂ 分解，因此 **Lean 版本是书中定理的加强版**：在更弱的假设（仅需不相关，无需独立）下得到相同的结论。

### 结论对应

**书中**：A = D₁QD₂，Q 正交，D₁, D₂ 对角矩阵

**Lean 主定理** (`ica_symmetry_decomposition`)：给出矩阵形式，`D₁.IsDiag ∧ D₂.IsDiag ∧ Q ∈ orthogonalGroup d ℝ ∧ A = D₁ * Q * D₂`

**Lean 推论** (`ica_symmetry_group_restriction`)：进一步给出向量形式，存在对角向量 d₁, d₂ 使得 `A = diagonal d₁ * Q * diagonal d₂`，直接对应书中的记号。

---

## 数学意义

### 对称性的约简

| 模型 | 对称性群 | 保持的变换 |
|------|---------|-----------|
| X = UZ（无约束） | GL(d)：全部可逆矩阵 | 任意线性变换（练习2.3.1） |
| X = UZ（z 不相关分量） | Diag × O(d) × Diag | 坐标缩放 + 旋转/反射 + 坐标缩放 |
| X = UZ（z 独立分量，非高斯） | Diag × S_d（置换群） | 坐标缩放 + 置换（ICA 可识别性） |

本习题处于第2行，形式化了从完整 GL(d) 到 D₁QD₂ 结构的对称性约简。

### 与 ICA 算法的联系

D₁QD₂ 分解表明：在不相关条件下，矩阵 A 的自由度被限制在"缩放 + 正交变换"的范围内。这正是 FastICA、白化（whitening）等 ICA 预处理步骤的理论依据：白化后的数据只剩 O(d) 的不确定性，而非全 GL(d)，从而大幅简化了 ICA 问题。

---

## Lean 4 技术说明

### `IsUnit A` vs `IsUnit A.det`

本文件统一使用 `IsUnit A`（而非练习2.3.1 中的 `IsUnit A.det`）表达矩阵可逆性。`IsUnit A` 是更强的表达，直接提供了 `hA.mul`（可逆矩阵之积可逆）等丰富 API，而 `IsUnit A.det` 需要借助 `Matrix.isUnit_iff_isUnit_det` 才能做到同样的事。

### `noncomputable section`

矩阵的逆、行列式、平方根等均不可计算，故整个 section 声明为 `noncomputable`。

### `Ring.inverse` vs `(·)⁻¹`

`Matrix.inv_diagonal` 给出 `(diagonal v)⁻¹ = diagonal (Ring.inverse v)`，其中 `Ring.inverse` 作用于函数类型 `d → ℝ` 时具有 Pi 环结构（非逐点取倒数）。证明中通过 `Matrix.inv_eq_right_inv` 绕开了这一问题，直接用 `mul_inv_cancel₀` 验证 D₁ * diagonal(1/√rowSq) = I，从而给出 D₁⁻¹ 的显式表达式 `diagonal (fun i => (√(rowSq i))⁻¹)`。

---

## 参考文献

- **书籍**：深度表征学习，第2章，练习2.3（`exercise:symmetry-identifiability`），第2部分
- **相关定理**：正交群、协方差矩阵、独立成分分析
- **Mathlib 模块**：
  - `Mathlib.LinearAlgebra.Matrix.PosDef`
  - `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`
  - `Mathlib.LinearAlgebra.UnitaryGroup`
  - `Mathlib.LinearAlgebra.Matrix.IsDiag`
  - `Mathlib.LinearAlgebra.Matrix.Orthogonal`
  - `Mathlib.Data.Real.Sqrt`
