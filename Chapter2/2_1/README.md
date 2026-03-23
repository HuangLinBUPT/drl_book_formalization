# Chapter 2, Exercise 2.1: PCA Optimality (Ky Fan Maximum Principle)

## 书籍原文

> **Exercise 2.1** (p.2237)
> Prove that, for any symmetric matrix $\vA$, the solution to the problem
> $\max_{\vU \in \O(D, d)}\tr\left(\vU^{\top}\vA\vU\right)$
> is the matrix $\vU^{\star}$ whose columns are the top $d$ unit eigenvectors of $\vA$.

## 形式化文件

- `Chapter2_Exercise2_1.lean` - 完整证明

## 形式化的定理

### sumLargest
定义前 d 个最大特征值之和：
```lean
def sumLargest (f : Fin D → ℝ) (d : ℕ) (hd : d ≤ D) : ℝ
```

### principal_components_bound (上界)
对于任意对称矩阵 A 和列正交矩阵 U：
$$ \operatorname{tr}(U^\top A U) \leq \sum_{i=1}^{d} \lambda_i $$

其中 $\lambda_1 \geq \lambda_2 \geq \cdots \geq \lambda_D$ 是 A 的特征值（降序）。

### principal_components_attained (可达性)
存在由前 d 个特征向量构成的矩阵 $U^*$ 达到上界：
$$ \operatorname{tr}((U^*)^\top A U^*) = \sum_{i=1}^{d} \lambda_i $$

### principal_components (主定理)
$$ \max_{U \in \O(D,d)} \operatorname{tr}(U^\top A U) = \sum_{i=1}^{d} \lambda_i $$

## 证明策略

1. **谱定理**：将对称矩阵分解为 $A = P \operatorname{diag}(\lambda) P^\top$
2. **正交变换**：令 $V = P^\top U$，则 $V$ 仍有正交列
3. **迹展开**：$\operatorname{tr}(U^\top A U) = \sum_j \lambda_j \cdot w_j$，其中 $w_j = \sum_i |V_{ji}|^2$
4. **权重性质**：$0 \leq w_j \leq 1$ 且 $\sum_j w_j = d$
5. **不等式证明**：使用重排不等式的思想证明上界
6. **构造性证明**：取前 d 个特征向量构造 $U^*$ 达到上界

## 编译状态

- ✅ 无错误
- ✅ 无 `sorry`
- ⚠️ 少量警告（未使用的 simp 参数，可忽略）
