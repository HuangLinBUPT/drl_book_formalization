# 第2章 练习2.6 第1部分：形式化报告

## 习题信息

**来源**：深度表征学习书籍，第2章，练习2.6（`exercise:sphere-calculus`），第1部分
**文件位置**：`deep-representation-learning-book/chapters/chapter2/classic-models.tex:2317`
**Lean 文件**：`lean_formalization/Chapter2/2_6/Chapter2_Exercise2_6_1.lean`
**日期**：2026-04-03

## 非形式化陈述

设 $F(\mathbf{u}) = \|\mathbf{u}\|_2^2 - 1$，则单位球面 $S^{d-1} = F^{-1}(\{0\})$。

**第1a部分**：证明球面在 $\mathbf{u}$ 处的切空间等于 $\mathbf{u}$ 的正交补：
$$T_{\mathbf{u}} S^{d-1} = \ker(DF_{\mathbf{u}}) = \{ \mathbf{v} \in \mathbb{R}^d \mid \langle \mathbf{v}, \mathbf{u} \rangle = 0 \}$$

**第1b部分**：证明到该切空间的正交投影算子为：
$$P_{\mathbf{u}}^\perp = I - \mathbf{u}\mathbf{u}^\top$$

具体地：
- **幂等性**：$(P_{\mathbf{u}}^\perp)^2 = P_{\mathbf{u}}^\perp$
- **对称性**：$\langle P_{\mathbf{u}}^\perp \mathbf{v},\, \mathbf{w} \rangle = \langle \mathbf{v},\, P_{\mathbf{u}}^\perp \mathbf{w} \rangle$
- **值域⊆切空间**：$\langle P_{\mathbf{u}}^\perp \mathbf{v},\, \mathbf{u} \rangle = 0$
- **切空间上恒等**：$\langle \mathbf{v}, \mathbf{u} \rangle = 0 \Rightarrow P_{\mathbf{u}}^\perp \mathbf{v} = \mathbf{v}$

## 非形式化证明思路

**第1a部分**：

$F(\mathbf{u}) = \|\mathbf{u}\|_2^2 - 1$ 的微分为 $DF_{\mathbf{u}}[\mathbf{v}] = 2\langle \mathbf{u}, \mathbf{v} \rangle$，
故 $\ker(DF_{\mathbf{u}}) = \{\mathbf{v} \mid \langle \mathbf{u}, \mathbf{v} \rangle = 0\}$。

**第1b部分**：

取 $P = I - \mathbf{u}\mathbf{u}^\top$，则对任意 $\mathbf{v}$：
$$P\mathbf{v} = \mathbf{v} - \langle \mathbf{u}, \mathbf{v} \rangle \mathbf{u}$$

- **幂等**：$P(P\mathbf{v}) = P\mathbf{v} - \langle \mathbf{u}, P\mathbf{v} \rangle \mathbf{u}$，
  而 $\langle \mathbf{u}, P\mathbf{v} \rangle = \langle \mathbf{u}, \mathbf{v} \rangle - \langle \mathbf{u}, \mathbf{v} \rangle \|\mathbf{u}\|^2 = 0$（用 $\|\mathbf{u}\|=1$），故 $P^2\mathbf{v} = P\mathbf{v}$。
- **对称**：$\langle P\mathbf{v}, \mathbf{w} \rangle = \langle \mathbf{v}, \mathbf{w} \rangle - \langle \mathbf{u},\mathbf{v}\rangle\langle \mathbf{u}, \mathbf{w}\rangle = \langle \mathbf{v}, P\mathbf{w}\rangle$（对称性显然）。
- **值域⊆切空间**：$\langle P\mathbf{v}, \mathbf{u} \rangle = \langle \mathbf{v}, \mathbf{u}\rangle - \langle \mathbf{u},\mathbf{v}\rangle\|\mathbf{u}\|^2 = 0$。
- **切空间上恒等**：$\langle \mathbf{v},\mathbf{u}\rangle = 0 \Rightarrow P\mathbf{v} = \mathbf{v} - 0 = \mathbf{v}$。

## 形式化策略

### Lean 中使用的关键 Mathlib 工具

| 工具 | 用途 |
|------|------|
| `Submodule.mem_orthogonal_singleton_iff_inner_right` | $(ℝ\cdot u)^\perp$ 的成员刻画 |
| `Submodule.starProjection_singleton` | $\text{proj}_{ℝ\cdot u}\, w = \frac{\langle u,w\rangle}{\|u\|^2} \cdot u$ |
| `Submodule.starProjection_orthogonal'` | $(U^\perp).\text{proj} = 1 - U.\text{proj}$ |
| `Submodule.starProjection_orthogonal_val` | $(U^\perp).\text{proj}\, v = v - U.\text{proj}\, v$ |
| `Submodule.isIdempotentElem_starProjection` | 正交投影的幂等性 |
| `inner_sub_left`, `inner_smul_left` | 内积关于减法和数乘的线性性 |
| `real_inner_comm` | 实内积的对称性：$\langle u,v\rangle = \langle v,u\rangle$ |

### Mathlib 中的正交投影体系

在 Mathlib 中，子空间 $K$ 的正交投影有两个层次：

| 类型 | 说明 |
|------|------|
| `K.orthogonalProjection : E →L[𝕜] K` | 值域为 $K$（子空间类型） |
| `K.starProjection : E →L[𝕜] E` | 值域为 $E$（即 `subtypeL ∘ orthogonalProjection`） |

本文件使用 `starProjection`，因为它直接作用在 $E$ 上，与书中 $P_u^\perp : \mathbb{R}^d \to \mathbb{R}^d$ 的描述一致。

### 文件结构

```
Chapter2_Exercise2_6_1.lean
├── sphere_tangentSpace_eq_orthogonal     -- Part 1a：切空间 = (ℝ·u)ᗮ
├── starProjection_span_unit (辅助引理)   -- span {u} 上的投影显式公式
├── sphere_tangent_projection             -- (ℝ·u)ᗮ 的投影 = 1 - (ℝ·u) 的投影
├── sphere_tangent_projection_idempotent  -- 幂等性
├── sphere_tangent_projection_explicit    -- 显式公式：P v = v - ⟨u,v⟩·u
├── sphere_tangent_projection_symmetric   -- 对称性
├── sphere_tangent_projection_range       -- 值域 ⊆ 切空间
└── sphere_tangent_projection_identity_on_tangent  -- 切空间上恒等
```

### 假设与类型参数

所有定理在如下变量上成立：

| 变量 | 类型 | 含义 |
|------|------|------|
| `E` | `Type*` | 抽象实内积空间（无需有限维） |
| `[NormedAddCommGroup E]` | 实例 | 赋范加法交换群 |
| `[InnerProductSpace ℝ E]` | 实例 | 实内积空间 |
| `u : E` | 向量 | 单位向量（部分定理需要 `‖u‖ = 1`） |

注：**无需 `CompleteSpace E`**（希尔伯特空间完备性），因为 `starProjection` 对一般内积空间即有意义。

## 形式化状态

### ✅ 完全完成（零 sorry）

**定理一览**：

| 定理名 | 内容 | 状态 |
|--------|------|------|
| `sphere_tangentSpace_eq_orthogonal` | $(ℝ\cdot u)^\perp = \{v \mid \langle v,u\rangle = 0\}$ | ✅ |
| `starProjection_span_unit` | $\text{proj}_{ℝ\cdot u}\, w = \langle u,w\rangle \cdot u$（$\|u\|=1$） | ✅ |
| `sphere_tangent_projection` | $(ℝ\cdot u)^\perp.\text{proj} = 1 - (ℝ\cdot u).\text{proj}$ | ✅ |
| `sphere_tangent_projection_idempotent` | $P^2 = P$ | ✅ |
| `sphere_tangent_projection_explicit` | $Pv = v - \langle u,v\rangle u$ | ✅ |
| `sphere_tangent_projection_symmetric` | $\langle Pv, w\rangle = \langle v, Pw\rangle$ | ✅ |
| `sphere_tangent_projection_range` | $\langle Pv, u\rangle = 0$ | ✅ |
| `sphere_tangent_projection_identity_on_tangent` | $\langle v,u\rangle=0 \Rightarrow Pv = v$ | ✅ |

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

1. **`starRingEnd ℝ` 化简**：

   在证明 `sphere_tangent_projection_range` 时，`inner_smul_left` 引入了
   `(starRingEnd ℝ) (inner ℝ u v)` 项。对实数域，`starRingEnd ℝ = id`，
   但 Lean 不会自动化简。最终发现 `simp [hu]` 可以同时处理
   `starRingEnd ℝ x = x` 和 `‖u‖^2 = 1` 两个化简，一步完成。

2. **`inner ℝ u u = 1` 的处理**：

   `real_inner_self_eq_norm_sq` 将 `inner ℝ u u` 改写为 `‖u‖^2`，
   但在部分目标中 `simp [hu]` 可以直接处理 `‖u‖` 出现的所有形式，
   无需显式使用该引理。

3. **对称性证明的 simp 策略**：

   展开为显式公式 `v - ⟨u,v⟩·u` 后，
   `simp [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
          real_inner_comm u v, mul_comm]`
   可以自动完成所有内积代数化简。
   其中 `real_inner_comm u v` 将 $\langle u,v\rangle$ 统一为 $\langle v,u\rangle$
   方向，再由 `mul_comm` 处理乘法顺序。

4. **无需完备性假设**：

   `Submodule.starProjection_orthogonal'` 和相关引理仅需要
   `[InnerProductSpace 𝕜 E]`（通过 `HasOrthogonalProjection` 实例），
   不要求完备性，因此定理对所有实内积空间成立。

## Mathlib 依赖

| 模块 | 用途 |
|------|------|
| `Mathlib.Analysis.InnerProductSpace.Projection.Basic` | `starProjection`，正交投影的所有核心引理 |
| `Mathlib.Analysis.InnerProductSpace.PiL2` | `EuclideanSpace` 的内积空间实例（备用） |

## 与书中的对应关系

| 书中陈述 | Lean 形式化 | 状态 |
|---------|------------|------|
| $T_u S^{d-1} = \{v \mid \langle v,u\rangle=0\}$ | `sphere_tangentSpace_eq_orthogonal` | ✅ |
| $P_u^\perp = I - uu^\top$（幂等） | `sphere_tangent_projection_idempotent` | ✅ |
| $P_u^\perp = I - uu^\top$（对称） | `sphere_tangent_projection_symmetric` | ✅ |
| $P_u^\perp = I - uu^\top$（值域） | `sphere_tangent_projection_range` | ✅ |
| $P_u^\perp = I - uu^\top$（恒等） | `sphere_tangent_projection_identity_on_tangent` | ✅ |

## 总结

**完成度**：100%（零 sorry）

练习 2.6.1（球面切空间与正交投影）完全形式化完成。

本习题是 FastICA 算法在球面上梯度上升的数学基础，证明了：
1. 球面的切空间是法向量的正交补（几何直觉的严格化）
2. 投影矩阵 $I - uu^\top$ 满足正交投影的所有特征性质

技术上，Mathlib 的 `Submodule.starProjection` 体系已内置了大部分所需结论，
主要工作在于正确调用相关 API 并处理实数域上的 `starRingEnd` 化简细节。
