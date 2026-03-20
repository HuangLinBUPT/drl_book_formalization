# 深度表征学习（Deep Representation Learning）形式化项目

[![Lean 4](https://img.shields.io/badge/Lean-4.28.0-blue.svg)](https://leanprover.github.io/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-blue.svg)](https://github.com/leanprover-community/mathlib4)

这是《深度表征学习》（*Deep Representation Learning*）一书的 Lean 4 形式化证明项目。我们的目标是用形式化数学语言验证书中的所有主要定理、引理和算法的正确性。

## 项目愿景

深度学习的数学基础需要严格的形式化验证。本项目致力于：

1. **严格性**：用机器可验证的证明替代传统的数学论证
2. **完整性**：覆盖从线性方法到深度神经网络的完整理论体系
3. **教育性**：为学习者提供可交互的、逐步验证的数学证明
4. **可扩展性**：建立可复用的形式化框架，便于扩展到新研究

## 项目结构

```
lean_formalization/
├── Chapter2/              # 第2章：学习线性和独立结构
│   ├── 2_1/              # 练习 2.1: PCA 最优性定理
│   ├── 2_2/              # 练习 2.2: 高斯分布的旋转不变性（待开始）
│   ├── 2_3/              # 练习 2.3: 对称性与可识别性（待开始）
│   └── 2_4/              # 练习 2.4: 白化变换（待开始）
├── Chapter3/              # 第3章：流形学习（计划中）
├── Chapter4/              # 第4章：概率流形（计划中）
├── Chapter5/              # 第5章：神经网络架构（计划中）
├── ...                    # 更多章节
├── lakefile.toml         # Lake 构建配置
├── lean-toolchain        # Lean 版本 (v4.28.0)
├── Main.lean            # 主入口
├── INSTALL.md           # 安装指南
└── README.md            # 本文件
```

## 当前进度

### 第2章：学习线性和独立结构 🚧

| 练习/定理 | 状态 | 完成度 | 说明 |
|---------|------|--------|------|
| **2.1 PCA 最优性** | ⚠️ 进行中 | 🟨 60% | 框架完成，主证明待填充 |
| 2.2 高斯旋转不变性 | 📋 未开始 | ⬜ 0% | - |
| 2.3 对称性与可识别性 | 📋 未开始 | ⬜ 0% | - |
| 2.4 白化变换 | 📋 未开始 | ⬜ 0% | - |
| 幂迭代算法收敛性 | 📋 未开始 | ⬜ 0% | - |
| 概率 PCA | 📋 未开始 | ⬜ 0% | - |
| FastICA 算法 | 📋 未开始 | ⬜ 0% | - |

### 其他章节 📅

| 章节 | 状态 | 计划开始时间 |
|------|------|-------------|
| 第3章：流形学习 | 📋 计划中 | 2026 Q2 |
| 第4章：概率流形 | 📋 计划中 | 2026 Q3 |
| 第5章：神经网络架构 | 📋 计划中 | 2026 Q4 |
| 第6-11章 | 📋 长期规划 | 2027+ |

**整体进度**: 🟩 约 3% (1/30+ 主要定理已完成框架)

## 快速开始

### 环境要求

- **Lean 4**: v4.28.0
- **操作系统**: Linux / macOS / Windows (WSL)
- **内存**: 建议 8GB+ RAM
- **磁盘**: 约 10GB（包含 Mathlib 缓存）

### 安装步骤

#### 1. 安装 Lean 4

```bash
# 使用 elan 安装（推荐）
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source ~/.profile

# 验证安装
lean --version  # 应显示 Lean (version 4.28.0, ...)
```

详细安装说明请参考 [INSTALL.md](INSTALL.md)。

#### 2. 克隆并构建项目

```bash
# 克隆项目
cd lean_formalization

# 获取预编译的 Mathlib 缓存（强烈推荐！）
lake exe cache get

# 构建项目（可选）
lake build
```

#### 3. 验证示例代码

```bash
# 验证 Chapter 2.1 的工作版本
lake env lean Chapter2/2_1/Chapter2_Exercise2_1_Working.lean

# 查看数学证明草图
cat Chapter2/2_1/Chapter2_Exercise2_1_Sketch.lean
```

### 使用 VS Code（推荐）

1. 安装 [VS Code](https://code.visualstudio.com/)
2. 安装 Lean 4 扩展：`lean4.lean4`
3. 打开项目目录
4. 享受交互式证明体验！

## 项目亮点

### ✅ 已实现：练习 2.1 - PCA 最优性定理

**定理**：对于对称矩阵 A ∈ ℝ^{D×D}，优化问题

```
max_{U ∈ O(D,d)} tr(U^T A U)
```

的解是 U*，其列是 A 的前 d 个特征向量（按特征值降序）。

**验证状态**（2026-03-20）：
- ✅ 核心定义：列正交矩阵、对称矩阵、瑞利商
- ✅ 基本引理：迹的循环性、对称矩阵性质
- ✅ 主定理类型签名正确
- ⚠️ 主证明使用 `sorry` 占位（依赖 Courant-Fischer 定理）

**文件位置**: `Chapter2/2_1/`

**数学意义**：这是主成分分析（PCA）的理论基础，证明了特征向量确实能最大化投影方差。

### 📁 多版本形式化策略

为了平衡完整性和可用性，我们为重要定理提供多个版本：

1. **完整版** (`_Full.lean`): 包含所有引理和完整证明链
2. **工作版** (`_Working.lean`): 可立即运行，避免重度依赖
3. **最小版** (`_Minimal.lean`): 展示核心结构，适合学习
4. **草图版** (`_Sketch.lean`): 纯数学推导，易于理解

## 形式化方法论

### 证明策略

我们采用分层形式化方法：

1. **第一层：类型定义** - 定义问题的数学结构
2. **第二层：陈述定理** - 用 Lean 类型系统表达定理
3. **第三层：引理分解** - 将大定理分解为小引理
4. **第四层：填充证明** - 逐步证明每个引理
5. **第五层：组装完整证明** - 连接所有引理

### 依赖管理

- **Mathlib**: 依赖强大的数学库 Mathlib 4
- **自定义定义**: 书中特定概念的形式化定义
- **可复用组件**: 构建跨章节的通用理论库

### 质量保证

- ✅ 所有定义必须通过 Lean 类型检查
- ✅ 避免不安全的 `axiom`（除非绝对必要）
- ⚠️ `sorry` 仅用于标记待完成的证明
- 📝 详细注释解释数学直觉

## 技术细节

### 核心依赖

```toml
# lakefile.toml
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4"
rev = "v4.28.0"
```

### 主要使用的 Mathlib 模块

- `Mathlib.LinearAlgebra.Matrix.*` - 矩阵理论
- `Mathlib.Analysis.InnerProductSpace.*` - 内积空间
- `Mathlib.LinearAlgebra.Eigenspace.*` - 特征值理论
- `Mathlib.Data.Real.*` - 实数分析
- `Mathlib.Topology.MetricSpace.*` - 度量空间

### 代码风格指南

- 使用 4 空格缩进
- 中文注释用于高层解释，英文用于代码
- 定理命名采用 `snake_case`
- 模块命名采用 `PascalCase`

## 常见问题

### Q: 为什么有些证明用 `sorry`？

**A**: `sorry` 是 Lean 的占位符，表示"这里需要证明，但我们先跳过"。这让我们可以：
1. 先搭建整体框架
2. 验证定理陈述的正确性
3. 逐步填充证明细节

最终目标是消除所有 `sorry`。

### Q: 编译很慢怎么办？

**A**: 使用预编译的 Mathlib 缓存：
```bash
lake exe cache get
```
这会下载预编译的 `.olean` 文件，避免从源码构建 Mathlib（需要数小时）。

### Q: 遇到 "unknown module" 错误？

**A**: 确保在项目根目录运行命令，并使用 `lake env`:
```bash
lake env lean Chapter2/2_1/Chapter2_Exercise2_1_Working.lean
```

### Q: 如何贡献代码？

**A**: 欢迎贡献！请参考下面的"参与贡献"部分。

## 开发路线图

### 近期目标（2026 Q1-Q2）

- [x] 完成项目架构设计
- [x] 完成 2.1 练习框架（60%）
- [ ] 填充 2.1 的完整证明（移除所有 `sorry`）
- [ ] 实现 Courant-Fischer 定理
- [ ] 开始 2.2-2.4 练习
- [ ] 完成第2章所有练习的框架

### 中期目标（2026 Q3-Q4）

- [ ] 完成第2章所有定理的完整证明
- [ ] 形式化幂迭代、FastICA 等算法
- [ ] 开始第3章（流形学习）的形式化
- [ ] 建立跨章节的理论库
- [ ] 添加计算示例和可视化

### 长期目标（2027+）

- [ ] 完成前5章的形式化（线性方法到神经网络）
- [ ] 形式化深度学习的主要定理
- [ ] 连接到实际代码实现
- [ ] 发布学术论文和教学材料
- [ ] 建立社区贡献者生态

## 参与贡献

我们欢迎各种形式的贡献！

### 如何贡献

1. **填充证明**：选择一个带 `sorry` 的定理，尝试完成证明
2. **添加新定理**：形式化书中尚未覆盖的定理
3. **改进文档**：改善注释、添加示例、写教程
4. **报告问题**：发现错误或不清晰的地方
5. **优化代码**：重构代码以提高可读性或性能

### 贡献流程

1. Fork 本项目
2. 创建特性分支 (`git checkout -b feature/amazing-proof`)
3. 提交更改 (`git commit -m 'Add proof for theorem X'`)
4. 推送到分支 (`git push origin feature/amazing-proof`)
5. 创建 Pull Request

### 贡献指南

- 确保所有代码通过 `lake build` 检查
- 添加详细的注释解释证明思路
- 更新相关文档（README、注释等）
- 遵循现有的代码风格

### 适合新手的任务

标记为 `good-first-issue` 的任务适合初学者：
- 完成简单引理的证明
- 改进现有代码的注释
- 添加测试用例
- 修正文档错误

## 学习资源

### Lean 4 学习

- 📖 [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/) - 官方教程
- 📖 [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/) - 数学证明入门
- 📖 [Functional Programming in Lean](https://leanprover.github.io/functional_programming_in_lean/) - 函数式编程
- 🎥 [Lean 4 Tutorials (YouTube)](https://www.youtube.com/c/leanprovercommunity)

### Mathlib 文档

- 📚 [Mathlib4 Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- 📚 [Mathlib4 API Search](https://loogle.lean-lang.org/)
- 📚 [Lean Zulip Chat](https://leanprover.zulipchat.com/) - 社区讨论

### 深度学习数学

- 📖 《深度表征学习》原书
- 📖 *Mathematics for Machine Learning* (Deisenroth et al.)
- 📖 *Deep Learning* (Goodfellow et al.)

## 相关项目

- [Lean 4 Official Repository](https://github.com/leanprover/lean4)
- [Mathlib4](https://github.com/leanprover-community/mathlib4) - Lean 4 数学库
- [Lean Game Server](https://adam.math.hhu.de/) - 交互式 Lean 游戏
- [Formalized Mathematics](https://github.com/leanprover-community/formalizations) - 其他形式化项目

## 致谢

感谢所有为本项目做出贡献的开发者、数学家和机器学习研究者。

特别感谢：
- Lean 社区提供了强大的证明助手工具
- Mathlib 团队维护了丰富的数学库
- 《深度表征学习》作者提供了严谨的数学理论

## 许可证

本项目遵循原书的许可协议。

## 联系方式

- **Issues**: [GitHub Issues](https://github.com/your-repo/issues)
- **Discussions**: [GitHub Discussions](https://github.com/your-repo/discussions)
- **Email**: your-email@example.com

---

**最后更新**: 2026-03-20
**项目状态**: 🚧 早期开发阶段 - 欢迎贡献！

---

> "形式化证明不仅仅是验证正确性，更是深入理解数学本质的过程。"
> — Lean Community

**让我们一起用形式化方法重新理解深度学习！** 🚀
