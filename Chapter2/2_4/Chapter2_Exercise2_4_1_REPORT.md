# 第2章 练习2.4 第1部分：形式化报告

## 习题信息

**来源**：深度表征学习书籍，第2章，练习2.4（`exercise:whitening`），第1部分
**文件位置**：`deep-representation-learning-book/chapters/chapter2/classic-models.tex:2285`
**Lean 文件**：`lean_formalization/Chapter2/2_4/Chapter2_Exercise2_4_1.lean`
**日期**：2026-04-08

## 非形式化陈述

考虑线性生成模型

$$
\mathbf{x} = U\mathbf{z}, \qquad U \in \mathbb{R}^{D \times d}, \quad \operatorname{rank}(U)=d,
$$

并设 $\mathbf{x}_1, \dots, \mathbf{x}_N$ 为该模型生成的样本。将样本按列拼成矩阵：

$$
X = [\mathbf{x}_1, \dots, \mathbf{x}_N] = U Z,
$$

其中 $X \in \mathbb{R}^{D \times N}$，$Z \in \mathbb{R}^{d \times N}$。

**习题要求**：证明：

1. $\operatorname{rank}(X) \le d$
2. 因而存在矩阵 $V \in \mathbb{R}^{D \times d}$ 和 $Y \in \mathbb{R}^{d \times N}$，使得
   $$
   V^\top V = I_d, \qquad X = VY.
   $$

这正是书中“用 PCA 得到一个列正交基，然后把数据投影到该基下”的线性代数核心。

## 非形式化证明思路

### 第一步：秩界

由于 $X = UZ$，矩阵乘法的秩满足

$$
\operatorname{rank}(X) = \operatorname{rank}(UZ) \le \operatorname{rank}(U) = d.
$$

因此 $X$ 的所有列都落在一个维数不超过 $d$ 的子空间中。

### 第二步：构造列空间的正交基

考虑 $U$ 作为线性映射

$$
U : \mathbb{R}^d \to \mathbb{R}^D.
$$

其像空间 $W = \operatorname{im}(U)$ 的维数正好为 $d$，因为 $\operatorname{rank}(U)=d$。

因此可以在 $W$ 中选取一个标准正交基

$$
b_1, \dots, b_d.
$$

将这些基向量写成 ambient 空间 $\mathbb{R}^D$ 中的列向量，拼成矩阵

$$
V = [b_1, \dots, b_d] \in \mathbb{R}^{D \times d}.
$$

由于 $b_i$ 两两正交且范数为 1，立刻得到

$$
V^\top V = I_d.
$$

### 第三步：构造坐标矩阵 $Y$

因为 $X$ 的每一列都在 $W$ 中，对每个样本列 $X_{:,j}$，都可以写成正交基 $b_1,\dots,b_d$ 下的坐标展开：

$$
X_{:,j} = \sum_{i=1}^d Y_{ij} b_i.
$$

把所有列的坐标拼起来，就得到矩阵 $Y \in \mathbb{R}^{d \times N}$，从而

$$
X = VY.
$$

## 形式化策略

### 主要建模对象

| Lean 对象 | 数学含义 | 类型 |
|----------|----------|------|
| `X := U * Z` | 数据矩阵 $X = UZ$ | `Matrix (Fin D) (Fin N) ℝ` |
| `W := (Matrix.toEuclideanLin U).range` | $U$ 作为线性映射的像空间 $\operatorname{im}(U)$ | `Submodule ℝ (EuclideanSpace ℝ (Fin D))` |
| `bW` | $W$ 上的标准正交基 | `OrthonormalBasis (Fin d) ℝ W` |
| `V` | 将基向量嵌入 $\mathbb{R}^D$ 后得到的矩阵 | `Matrix (Fin D) (Fin d) ℝ` |
| `xW j` | 第 $j$ 列样本视为 $W$ 中元素 | `W` |
| `Y` | 各列在基 `bW` 下的坐标矩阵 | `Matrix (Fin d) (Fin N) ℝ` |

### Lean 中使用的关键 Mathlib 工具

| 工具 | 用途 |
|------|------|
| `Matrix.rank_mul_le_left` | 证明 $\operatorname{rank}(UZ) \le \operatorname{rank}(U)$ |
| `Matrix.rank_eq_finrank_range_toLin` | 将矩阵秩转化为线性映射像空间的 `finrank` |
| `Matrix.toEuclideanLin_eq_toLin_orthonormal` | 把 `toEuclideanLin` 与标准正交基下的 `toLin` 对齐 |
| `stdOrthonormalBasis` | 为有限维内积空间构造标准正交基 |
| `OrthonormalBasis.reindex` | 将基重编号为 `Fin d` |
| `orthonormal_iff_ite` | 将正交归一性写成 `if j = k then 1 else 0` |
| `OrthonormalBasis.sum_repr` | 坐标展开公式 $\sum_i \langle x,b_i\rangle b_i = x$ |
| `Matrix.mul_apply` | 按坐标展开矩阵乘法 |
| `Matrix.mulVec` / `Matrix.col` | 将列向量看成函数并与矩阵作用对应 |

### EuclideanSpace 坐标技巧

本文件工作在 `EuclideanSpace ℝ (Fin D)` 中，关键技巧包括：

1. **坐标访问**：`v.ofLp i` 表示向量第 `i` 个坐标
2. **把矩阵列转成向量**：`(EuclideanSpace.equiv (Fin d) ℝ).symm (Z.col j)`
3. **把像空间元素嵌回 ambient 空间**：`W.subtypeₗᵢ`
4. **内积按坐标展开**：私有引理 `euclidean_inner_eq_sum`

其中 `euclidean_inner_eq_sum` 是证明 `Vᵀ * V = 1` 的关键桥梁：

```lean
private lemma euclidean_inner_eq_sum (D : ℕ) (x y : EuclideanSpace ℝ (Fin D)) :
    @inner ℝ _ _ x y = ∑ i, x.ofLp i * y.ofLp i
```

它把矩阵乘法中的坐标求和识别为欧氏内积。

### 主定理的证明结构

`exercise_2_4_1` 的证明分成四步：

```
exercise_2_4_1
├── h_rank      ① 由 X = UZ 得 rank X ≤ rank U = d
├── hWfin       ② 由 rank(U)=d 推出 finrank(W)=d
├── hV_orth     ③ 用 W 的正交基构造 V，并证 VᵀV = I
├── hxW_coord   ④ 证明 xW j 的 ambient 坐标就是 X 的第 j 列
├── hsum        ⑤ 用 bW.sum_repr 展开 xW j
├── hcoord      ⑥ 得到第 j 列的坐标展开公式
└── X = V * Y   ⑦ 按列逐坐标收束为矩阵等式
```

## 关键证明步骤

### 1. 用 `rank_eq_finrank_range_toLin` 建立像空间维数

定义

```lean
let W : Submodule ℝ (EuclideanSpace ℝ (Fin D)) := (Matrix.toEuclideanLin U).range
```

然后通过：

```lean
Matrix.rank_eq_finrank_range_toLin U
  (EuclideanSpace.basisFun (Fin D) ℝ).toBasis
  (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
```

把 `U.rank` 识别为 `Module.finrank ℝ W`。再结合假设 `hU : U.rank = d` 得到

```lean
have hWfin : Module.finrank ℝ W = d
```

这一步是“书中 rank(U)=d，因此像空间恰好 d 维”的正式版本。

### 2. 从子空间正交基构造矩阵 `V`

先取标准正交基：

```lean
let bW0 : OrthonormalBasis (Fin (Module.finrank ℝ W)) ℝ W := stdOrthonormalBasis ℝ W
let bW : OrthonormalBasis (Fin d) ℝ W := bW0.reindex (finCongr hWfin)
```

再定义矩阵 `V` 的第 `j` 列为基向量 `bW j` 嵌入 ambient 空间后的坐标：

```lean
let V : Matrix (Fin D) (Fin d) ℝ :=
  Matrix.of fun i j => ((W.subtypeₗᵢ (bW j)).ofLp i)
```

这正对应于数学上的 $V = [b_1,\dots,b_d]$。

### 3. 证明 `Vᵀ * V = 1`

证明方式是逐项展开矩阵乘法，把它识别为内积：

```lean
rw [← euclidean_inner_eq_sum D (W.subtypeₗᵢ (bW j)) (W.subtypeₗᵢ (bW k))]
```

随后利用 `bW.orthonormal`：

```lean
have hinner :
    @inner ℝ _ _ (W.subtypeₗᵢ (bW j)) (W.subtypeₗᵢ (bW k)) = if j = k then 1 else 0 := by
  simpa using (orthonormal_iff_ite.mp bW.orthonormal) j k
```

因此 `(Vᵀ * V) j k` 恰为 Kronecker delta，故 `Vᵀ * V = 1`。

### 4. 构造 `xW`：把 `X` 的每一列看成像空间元素

对每个 `j : Fin N`，定义：

```lean
let xW : Fin N → W := fun j =>
  ⟨(Matrix.toEuclideanLin U) ((EuclideanSpace.equiv (Fin d) ℝ).symm (Z.col j)), ...⟩
```

即把 `Z` 的第 `j` 列作为 $\mathbb{R}^d$ 中向量，经 `U` 作用后得到 `X` 的第 `j` 列，这当然属于 `W = range(U)`。

关键坐标引理是：

```lean
have hxW_coord (i : Fin D) (j : Fin N) : ((W.subtypeₗᵢ (xW j)).ofLp i) = X i j
```

证明中使用：

```lean
change (U.mulVec (Z.col j)) i = (U * Z) i j
simp only [Matrix.mulVec, dotProduct, Matrix.col, Matrix.transpose_apply, Matrix.mul_apply]
```

这是把“线性映射作用在列向量上”和“矩阵乘法得到对应列”对齐的关键一步。

### 5. 用 `sum_repr` 构造坐标矩阵 `Y`

定义：

```lean
let Y : Matrix (Fin d) (Fin N) ℝ := fun i j => (bW.repr (xW j)).ofLp i
```

即第 `j` 列的第 `i` 个坐标，是 `xW j` 在基 `bW` 下的表示向量的第 `i` 个分量。

然后使用正交基展开公式：

```lean
have hsum (j : Fin N) : ∑ k, ((bW.repr (xW j)).ofLp k) • bW k = xW j := by
  simpa using (bW.sum_repr (xW j))
```

把它嵌入 ambient 空间并逐坐标取值，得到：

```lean
have hcoord (i : Fin D) (j : Fin N) :
    ∑ k, (bW.repr (xW j)).ofLp k * (W.subtypeₗᵢ (bW k)).ofLp i = X i j
```

这正是第 `j` 列在基 `bW` 下的坐标展开。

### 6. 最终证明 `X = V * Y`

最后逐坐标证明矩阵相等：

```lean
ext i j
calc
  X i j = ∑ k, (bW.repr (xW j)).ofLp k * (W.subtypeₗᵢ (bW k)).ofLp i := by
    symm
    exact hcoord i j
  _ = ∑ k, V i k * Y k j := by
    apply Finset.sum_congr rfl
    intro k hk
    simp only [V, Y, Matrix.of_apply]
    rw [mul_comm]
  _ = (V * Y) i j := by
    rw [Matrix.mul_apply]
```

其中第二步只是把“基展开公式”改写回 `V` 与 `Y` 的定义。

## 形式化状态

### ✅ 完全完成（零 sorry）

| 定理/引理名 | 数学内容 | 状态 |
|------------|----------|------|
| `euclidean_inner_eq_sum` | 欧氏内积按坐标展开 | ✅ |
| `exercise_2_4_1` | $\operatorname{rank}(X) \le d$ 且 $\exists V,Y,\;V^\top V=I,\;X=VY$ | ✅ |

## 验证

### 编译状态

```
lean_diagnostic_messages → success: true, items: []
```

✅ 零错误，零 sorry，零警告。

### 公理检查

```
propext, Classical.choice, Quot.sound
```

✅ 无自定义公理。

## 与书中的对应关系

| 书中陈述 | Lean 形式化 | 状态 |
|---------|------------|------|
| $X = UZ$ | `let X := U * Z` | ✅ |
| $\operatorname{rank}(X) \le d$ | `h_rank` / `exercise_2_4_1` 第一部分 | ✅ |
| $\operatorname{im}(U)$ 维数为 $d$ | `hWfin : Module.finrank ℝ W = d` | ✅ |
| 存在列正交矩阵 $V$ | `V` 与 `hV_orth : Vᵀ * V = 1` | ✅ |
| 存在坐标矩阵 $Y$ 使 $X = VY$ | `Y` 与主定理中的 `X = V * Y` | ✅ |

## Mathlib 依赖

| 模块/工具 | 用途 |
|-----------|------|
| `Mathlib` | 总入口，覆盖矩阵、内积空间、有限维线性代数 API |
| `Matrix.rank_mul_le_left` | 秩不等式 |
| `Matrix.rank_eq_finrank_range_toLin` | 秩与像空间维数的桥梁 |
| `Matrix.toEuclideanLin` | 把矩阵视为 Euclidean 空间之间的线性映射 |
| `stdOrthonormalBasis` | 构造有限维内积空间正交基 |
| `OrthonormalBasis.sum_repr` | 坐标展开 |

## 与 2.4 系列后续部分的关系

| 部分 | 内容 | 本文件提供的基础 |
|------|------|------------------|
| 2.4.1（本文件） | 秩界与正交分解 $X = VY$ | 提供白化前的正交坐标分解 |
| 2.4.2 | 白化矩阵存在与经验协方差为单位阵 | 依赖 `Y` 的构造与 $V^\top V = I$ |
| 2.4.3 | SVD 视角下的白化表示 | 与本文件的正交分解互补 |

从数学上说，2.4.1 先把样本矩阵压缩到一个 $d$ 维正交坐标系中，后续 2.4.2/2.4.3 再在这个低维表示上进行白化与 SVD 分析。

## 总结

**完成度**：100%（零 sorry）

练习 2.4.1 已完成书本强结论的形式化：不仅证明了 $X = UZ$ 满足 $\operatorname{rank}(X) \le d$，还进一步构造出书中所需的

$$
X = VY, \qquad V^\top V = I_d,
$$

其中 `V : ℝ^{D×d}` 的列由像空间 `range(U)` 的标准正交基给出，`Y : ℝ^{d×N}` 则是各样本列在该正交基下的坐标矩阵。

这份形式化的核心价值在于：

1. **把“PCA 直觉”转化为严格线性代数构造**：不依赖谱分解或 QR/SVD 存在性，而是直接从 `range(U)` 的有限维正交基出发。
2. **严格对齐书中结论的尺寸**：在 `rank(U)=d` 的前提下，构造出的 `V` 宽度正好是 `d`，而不是某个抽象的 `r ≤ d`。
3. **为后续白化部分奠定基础**：`X = VY` 是 2.4.2 与 2.4.3 中白化与 SVD 论证的自然起点。

从 Lean 技术上看，本文件最关键的桥梁是：
- `rank_eq_finrank_range_toLin`：把矩阵秩连接到像空间维数；
- `stdOrthonormalBasis`：在像空间中选择标准正交基；
- `sum_repr`：把每一列样本还原为基向量的线性组合。

因此，本文件已经完整捕捉了书中“rank bound ⇒ orthonormal factorization”这一步的数学本质。