# 第2章 练习2.6 第2部分：形式化报告

## 习题信息

**来源**：深度表征学习书籍，第2章，练习2.6（`exercise:sphere-calculus`），第2部分
**文件位置**：`deep-representation-learning-book/chapters/chapter2/classic-models.tex:2362`
**Lean 文件**：`lean_formalization/Chapter2/2_6/Chapter2_Exercise2_6_2.lean`
**日期**：2026-04-03

## 非形式化陈述

设 $\mathbf{v} \in \mathbb{R}^d$ 为非零向量。利用球面上的一阶最优性条件，证明距 $\mathbf{v}$ 最近的单位向量是 $\frac{\mathbf{v}}{\|\mathbf{v}\|}$：

$$\operatorname{proj}_{S^{d-1}}(\mathbf{v}) := \arg\min_{\|\mathbf{u}\|_2^2 = 1} \|\mathbf{u} - \mathbf{v}\|_2 = \frac{\mathbf{v}}{\|\mathbf{v}\|_2}$$

此外，该最近点是唯一的。

## 非形式化证明思路

### 书中给出的策略（一阶最优性条件）

对目标函数 $f(\mathbf{u}) = \|\mathbf{u} - \mathbf{v}\|^2$ 在球面 $\|\mathbf{u}\|^2 = 1$ 上求极值。

欧式梯度为 $\nabla f(\mathbf{u}) = 2(\mathbf{u} - \mathbf{v})$，黎曼梯度为：
$$\operatorname{grad} f(\mathbf{u}) = P_{\mathbf{u}}^\perp \nabla f(\mathbf{u}) = (I - \mathbf{u}\mathbf{u}^\top) \cdot 2(\mathbf{u} - \mathbf{v})$$

令黎曼梯度为零：
$$(I - \mathbf{u}\mathbf{u}^\top)(\mathbf{u} - \mathbf{v}) = \mathbf{0}$$

即 $\mathbf{u} - \mathbf{v}$ 平行于 $\mathbf{u}$，故 $\mathbf{v} = \lambda \mathbf{u}$ 对某个标量 $\lambda$ 成立。
结合 $\|\mathbf{u}\| = 1$，得 $\mathbf{u} = \frac{\mathbf{v}}{\|\mathbf{v}\|}$。

### 形式化采用的策略（Cauchy-Schwarz 直接比较）

对于任意单位向量 $\mathbf{u}$（$\|\mathbf{u}\|=1$）：
$$\|\mathbf{u} - \mathbf{v}\|^2 = \|\mathbf{u}\|^2 - 2\langle \mathbf{u}, \mathbf{v}\rangle + \|\mathbf{v}\|^2 = 1 - 2\langle \mathbf{u}, \mathbf{v}\rangle + \|\mathbf{v}\|^2$$

由 Cauchy-Schwarz 不等式 $\langle \mathbf{u}, \mathbf{v}\rangle \leq \|\mathbf{u}\|\|\mathbf{v}\| = \|\mathbf{v}\|$，得：
$$\|\mathbf{u} - \mathbf{v}\|^2 \geq 1 - 2\|\mathbf{v}\| + \|\mathbf{v}\|^2 = (1 - \|\mathbf{v}\|)^2$$

而 $\|\|\mathbf{v}\|^{-1}\mathbf{v} - \mathbf{v}\|^2 = (1 - \|\mathbf{v}\|)^2$，故 $\|\mathbf{v}\|^{-1}\mathbf{v}$ 确实是最近点。

**唯一性**：等号成立当且仅当 $\langle \mathbf{u}, \mathbf{v}\rangle = \|\mathbf{v}\|$，即 Cauchy-Schwarz 等号条件，意味着 $\mathbf{u}$ 与 $\mathbf{v}$ 共线且方向相同，故 $\mathbf{u} = \|\mathbf{v}\|^{-1}\mathbf{v}$。

## 形式化策略

### 两个视角的统一

| 视角 | 内容 | 对应定理 |
|------|------|----------|
| 一阶条件（书中方法） | 黎曼梯度在 $\|\mathbf{v}\|^{-1}\mathbf{v}$ 处为零 | `sphere_proj_first_order` |
| 最优性（直接证明） | 对所有单位向量 $\mathbf{u}$，$\|\|\mathbf{v}\|^{-1}\mathbf{v} - \mathbf{v}\| \leq \|\mathbf{u} - \mathbf{v}\|$ | `sphere_projection_is_argmin` |
| 唯一性 | 若 $\|\mathbf{u} - \mathbf{v}\| = \|\|\mathbf{v}\|^{-1}\mathbf{v} - \mathbf{v}\|$ 则 $\mathbf{u} = \|\mathbf{v}\|^{-1}\mathbf{v}$ | `sphere_projection_unique` |

### Lean 中使用的关键 Mathlib 工具

| 工具 | 用途 |
|------|------|
| `norm_smul_inv_norm` | `‖‖v‖⁻¹ • v‖ = 1`（归一化向量在球面上） |
| `real_inner_smul_left` | `⟨a • x, y⟩_ℝ = a * ⟨x, y⟩_ℝ` |
| `real_inner_self_eq_norm_sq` | `⟨x, x⟩_ℝ = ‖x‖²` |
| `norm_sub_sq_real` | `‖x - y‖² = ‖x‖² - 2⟨x,y⟩ + ‖y‖²` |
| `real_inner_le_norm` | Cauchy-Schwarz：`⟨x,y⟩_ℝ ≤ ‖x‖ * ‖y‖` |
| `inner_eq_norm_mul_iff_real` | Cauchy-Schwarz 等号条件：`⟨x,y⟩ = ‖x‖‖y‖ ↔ ‖y‖ • x = ‖x‖ • y` |
| `Real.sqrt_le_sqrt` | 从平方不等式推出范数不等式 |
| `sphere_tangent_projection_explicit` | 来自习题 2.6.1 的切空间投影显式公式 |

### 关键技术：黎曼梯度为零的证明

黎曼梯度 $P_u^\perp(\mathbf{u} - \mathbf{v})$ 在 $\mathbf{u} = \|\mathbf{v}\|^{-1}\mathbf{v}$ 处化为：

$$(\|\mathbf{v}\|^{-1}\mathbf{v} - \mathbf{v}) - \langle \|\mathbf{v}\|^{-1}\mathbf{v},\, \|\mathbf{v}\|^{-1}\mathbf{v} - \mathbf{v}\rangle \cdot (\|\mathbf{v}\|^{-1}\mathbf{v}) = 0$$

计算内积：
$$\langle \|\mathbf{v}\|^{-1}\mathbf{v},\, \|\mathbf{v}\|^{-1}\mathbf{v} - \mathbf{v}\rangle = \|\|\mathbf{v}\|^{-1}\mathbf{v}\|^2 - \langle \|\mathbf{v}\|^{-1}\mathbf{v}, \mathbf{v}\rangle = 1 - \|\mathbf{v}\|$$

代入后目标变为：
$$(\|\mathbf{v}\|^{-1}\mathbf{v} - \mathbf{v}) - (1 - \|\mathbf{v}\|) \cdot (\|\mathbf{v}\|^{-1}\mathbf{v}) = 0$$

化简：$\|\mathbf{v}\| \cdot (\|\mathbf{v}\|^{-1}\mathbf{v}) - \mathbf{v} = \mathbf{v} - \mathbf{v} = 0$，由 `module` 策略（模结构计算）完成。

### 文件结构

```
Chapter2_Exercise2_6_2.lean
├── import Chapter2.«2_6».Chapter2_Exercise2_6_1  -- 复用切空间投影公式
├── sphere_normalize_mem       -- ‖‖v‖⁻¹ • v‖ = 1
├── inner_normalize_self       -- ⟨‖v‖⁻¹ • v, v⟩ = ‖v‖
├── norm_normalize_sub_sq      -- ‖‖v‖⁻¹ • v - v‖² = (1-‖v‖)²
├── sphere_proj_first_order    -- 黎曼梯度 = 0（一阶最优性）
├── sphere_projection_is_argmin  -- 最近点定理（主定理）
└── sphere_projection_unique   -- 唯一性
```

### 假设

所有定理在如下变量上成立：

| 变量 | 类型 | 含义 |
|------|------|------|
| `E` | `Type*` | 抽象实内积空间（无需有限维或完备） |
| `[NormedAddCommGroup E]` | 实例 | 赋范加法交换群 |
| `[InnerProductSpace ℝ E]` | 实例 | 实内积空间 |
| `v : E` | 向量 | 非零向量（需要 `hv : v ≠ 0`） |

注：**无需 `FiniteDimensional`，无需 `CompleteSpace`**，结论在任意（可能无穷维）实内积空间中成立。

## 形式化状态

### ✅ 完全完成（零 sorry）

**定理一览**：

| 定理名 | 内容 | 状态 |
|--------|------|------|
| `sphere_normalize_mem` | `‖‖v‖⁻¹ • v‖ = 1` | ✅ |
| `inner_normalize_self` | `⟨‖v‖⁻¹ • v, v⟩ = ‖v‖` | ✅ |
| `norm_normalize_sub_sq` | `‖‖v‖⁻¹ • v - v‖² = (1-‖v‖)²` | ✅ |
| `sphere_proj_first_order` | 黎曼梯度 $P_u^\perp(u-v) = 0$ 在 $u = \|\mathbf{v}\|^{-1}\mathbf{v}$ 处 | ✅ |
| `sphere_projection_is_argmin` | $\forall u,\, \|u\|=1 \Rightarrow \|\|v\|^{-1}v-v\| \leq \|u-v\|$ | ✅ |
| `sphere_projection_unique` | 若 $\|u-v\| \leq \|\|v\|^{-1}v-v\|$ 则 $u = \|v\|^{-1}v$ | ✅ |

## 验证

### 编译状态

```
lean_diagnostic_messages → success: true, items: []
```

✅ 零错误，零 sorry，零警告。

### 公理检查

仅使用标准 Lean 4 / Mathlib 公理：
```
propext, Classical.choice, Quot.sound
```
✅ 无自定义公理。

### 关键技术细节

1. **`module` 策略处理向量等式**：

   证明 `‖v‖⁻¹ • v - v - (1 - ‖v‖) • ‖v‖⁻¹ • v = 0` 时，
   先用 `simp only [smul_smul]; ring_nf` 将标量系数收集，
   再用 `rw [mul_inv_cancel₀ hv']` 代入 `‖v‖ * ‖v‖⁻¹ = 1`，
   最后 `module` 完成模结构计算（消去 `1 • v = v` 等）。

2. **平方范数比较**：

   由于 `Real.sqrt_le_sqrt` 要求输入为实数（不是范数），
   先用 `rw [← Real.sqrt_sq (norm_nonneg _)]` 将范数转化为 `sqrt(‖·‖²)`，
   再应用 `Real.sqrt_le_sqrt` 归约为平方范数的比较，
   最后 `nlinarith` 处理代数不等式。

3. **Cauchy-Schwarz 等号条件**：

   Mathlib 中 `inner_eq_norm_mul_iff_real` 给出：
   ```lean
   ⟪x, y⟫_ℝ = ‖x‖ * ‖y‖ ↔ ‖y‖ • x = ‖x‖ • y
   ```
   用 `‖u‖ = 1` 化简后得 `‖v‖ • u = v`，从而 `u = ‖v‖⁻¹ • v`，
   最终由 `smul_smul` + `inv_mul_cancel₀` 完成。

4. **避免 `v / ‖v‖` 的除法**：

   全程使用 `‖v‖⁻¹ • v`（标量乘法）而非 `v / ‖v‖`（除法），
   避免了向量除以标量的类型类解析歧义，所有 Mathlib 引理（如 `real_inner_smul_left`）可直接适用。

5. **`starRingEnd ℝ` 在 `field_simp` 中的处理**：

   `inner_normalize_self` 中，`real_inner_smul_left` 展开后得
   `‖v‖⁻¹ * ‖v‖² = ‖v‖`，这是一个纯实数等式，`field_simp [hv']` 直接完成。

## Mathlib 依赖

| 模块 | 用途 |
|------|------|
| `Mathlib.Analysis.InnerProductSpace.Projection.Basic` | `starProjection`，`sphere_tangent_projection_explicit`（通过习题 2.6.1） |
| `Mathlib.Analysis.InnerProductSpace.Basic` | `real_inner_le_norm`，`inner_eq_norm_mul_iff_real`，`norm_sub_sq_real` |
| `Mathlib.Analysis.InnerProductSpace.PiL2` | `norm_smul_inv_norm` |

## 与书中的对应关系

| 书中陈述 | Lean 形式化 | 状态 |
|---------|------------|------|
| $\operatorname{proj}_{S^{d-1}}(v) = v / \|v\|$（最近点） | `sphere_projection_is_argmin` | ✅ |
| 一阶最优性条件在 $v/\|v\|$ 处成立 | `sphere_proj_first_order` | ✅ |
| 最近点唯一 | `sphere_projection_unique` | ✅ |

## 与习题 2.6.1 的依赖关系

习题 2.6.2 直接导入习题 2.6.1，使用了以下内容：

| 来自 2.6.1 | 用途 |
|-----------|------|
| `sphere_tangent_projection_explicit` | 展开切空间投影 $P_u^\perp v = v - \langle u,v\rangle u$ |

## 习题 2.6 各部分对比

| 维度 | 习题 2.6.1（切空间） | 习题 2.6.2（球面投影） |
|------|---------------------|----------------------|
| 核心数学内容 | 切空间与正交投影 | 球面最近点优化 |
| 主要工具 | `starProjection` API | Cauchy-Schwarz 不等式 |
| 关键 Mathlib 引理 | `starProjection_orthogonal_val` | `real_inner_le_norm`、`inner_eq_norm_mul_iff_real` |
| sorry 数 | 0 | 0 |
| 定理数 | 8 | 6 |
| 逻辑结构 | API 调用为主 | 代数计算为主 |

## 总结

**完成度**：100%（零 sorry）

习题 2.6.2 完全形式化完成。本习题在习题 2.6.1 的基础上，将切空间投影用于优化问题，证明了球面上的最近点公式。

形式化工作完整覆盖了书中的三个核心要点：
1. 一阶最优性条件（黎曼梯度为零）
2. 最优性（最近点不等式，通过 Cauchy-Schwarz 直接证明）
3. 唯一性（Cauchy-Schwarz 等号条件）

技术上，全程使用 `‖v‖⁻¹ • v` 代替 `v / ‖v‖` 是关键设计决策，简化了类型推断并使所有内积引理可直接调用。
