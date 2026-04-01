# 第2章 练习2.1：PCA 最优性（Ky Fan 最大值原理）

## 书籍原文

> **Exercise 2.1** (p.2237)
> Prove that, for any symmetric matrix $\vA$, the solution to the problem
> $\max_{\vU \in \O(D, d)}\tr\left(\vU^{\top}\vA\vU\right)$
> is the matrix $\vU^{\star}$ whose columns are the top $d$ unit eigenvectors of $\vA$.

## 形式化文件

- `Chapter2_Exercise2_1.lean` - 完整证明（已验证通过）

## 形式化的定理

### sumLargest
定义前 d 个最大特征值之和（形式化为有限集合上的上确界）：
```lean
def sumLargest (f : Fin D → ℝ) (d : ℕ) (hd : d ≤ D) : ℝ :=
  ((Finset.univ : Finset (Fin D)).powersetCard d).sup'
    (by rw [Finset.powersetCard_nonempty]; simp [Finset.card_univ]; exact hd)
    (fun s => ∑ i ∈ s, f i)
```

### principal_components_bound (上界定理)
对于任意对称矩阵 A ∈ ℝ^{D×D} 和任意列正交矩阵 U ∈ ℝ^{D×d}：
$$ \operatorname{tr}(U^\top A U) \leq \sum_{i=1}^{d} \lambda_i $$

其中 $\lambda_1 \geq \lambda_2 \geq \cdots \geq \lambda_D$ 是 A 的特征值（降序排列）。

### principal_components_attained (可达性定理)
存在由前 d 个特征向量构成的矩阵 $U^*$ 达到上界：
$$ \operatorname{tr}((U^*)^\top A U^*) = \sum_{i=1}^{d} \lambda_i $$

### principal_components (主定理)
$$ \max_{U \in \O(D,d)} \operatorname{tr}(U^\top A U) = \sum_{i=1}^{d} \lambda_i $$

---

## 形式化证明详解

### 核心定义

```lean
-- 列正交矩阵：U^T U = I
U.conjTranspose * U = 1

-- 对称矩阵：A^T = A
A.IsHermitian
```

### 证明步骤

#### 第一步：谱定理分解

利用谱定理，将对称矩阵 A 分解为：
```
A = P Λ P^T
```
其中：
- P ∈ ℝ^{D×D} 是酉矩阵（特征向量组成的正交基）
- Λ = diag(λ₁, λ₂, ..., λ_D) 是特征值对角矩阵

在 Lean 中：
```lean
obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin D) (Fin D) ℝ,
  P.conjTranspose * P = 1 ∧
  A = P * Matrix.diagonal (hA.eigenvalues) * P.conjTranspose
```

#### 第二步：酉变换保持正交性

令 V = P^T U，则 V 仍然满足 V^T V = I：
```lean
set V : Matrix (Fin D) (Fin d) ℝ := P.conjTranspose * U
have hV : V.conjTranspose * V = 1
```

此时迹可以展开为：
```lean
have h_trace :
  (U.conjTranspose * A * U).trace = ∑ j, hA.eigenvalues j * ∑ i, V j i ^ 2
```

即：
$$\operatorname{tr}(U^\top A U) = \sum_{j=1}^{D} \lambda_j \cdot w_j$$

其中 $w_j = \sum_{i=1}^{d} V_{ji}^2$ 表示第 j 个特征向量上的权重。

#### 第三步：权重约束

由于 V 的列正交，可以证明：
```lean
have h_w_bounds : ∀ j, 0 ≤ ∑ i, V j i ^ 2 ∧ ∑ i, V j i ^ 2 ≤ 1

have h_w_sum : ∑ j, ∑ i, V j i ^ 2 = d
```

即：
- $0 \leq w_j \leq 1$（每个权重在 [0,1] 之间）
- $\sum_{j=1}^{D} w_j = d$（权重之和等于 d）

#### 第四步：上界证明

设 S 是前 d 个最大特征值对应的索引集合，$m = \min_{j \in S} \lambda_j$。

通过不等式放缩证明：
$$\sum_{j \in S} \lambda_j - \sum_j \lambda_j w_j \geq m(d - \sum_j w_j) = 0$$

因此：
$$\operatorname{tr}(U^\top A U) \leq \sum_{j \in S} \lambda_j$$

即前 d 个特征值之和。

#### 第五步：构造性证明（可达性）

取 U 的列为对应前 d 个最大特征值的特征向量：
```lean
use Matrix.of (fun i j => hA.eigenvectorBasis (e j) i)
```

此时可以验证：
- U^T U = I（正交性）
- tr(U^T A U) = Σ_{j∈S} λ_j（等号成立）

---

## 编译状态

- ✅ 无错误
- ✅ 无 `sorry`
- ⚠️ 少量 linter 警告（未使用的 simp 参数，可忽略）

## 验证命令

```bash
cd lean_formalization
lake env lean Chapter2/2_1/Chapter2_Exercise2_1.lean
```
