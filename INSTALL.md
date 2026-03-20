# Lean 4 安装说明

## 在Linux/WSL上安装Lean 4

### 方法1：使用官方安装脚本（推荐）

```bash
# 1. 安装Elan（Lean版本管理器）
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# 2. 将elan添加到PATH（或重启终端）
source ~/.profile
# 或者
source ~/.bashrc

# 3. 验证安装
lean --version
lake --version
```

### 方法2：手动安装

如果上述脚本不工作，可以手动下载：

```bash
# 下载并安装elan
wget https://github.com/leanprover/elan/releases/latest/download/elan-x86_64-unknown-linux-gnu.tar.gz
tar xzf elan-x86_64-unknown-linux-gnu.tar.gz
./elan-init

# 添加到PATH
echo 'export PATH="$HOME/.elan/bin:$PATH"' >> ~/.bashrc
source ~/.bashrc
```

## 创建Lean项目

```bash
# 进入工作目录
cd ~/code/deep-representation-learning-book/lean_formalization

# 创建新项目
lake init pca-formalization

# 进入项目
cd pca-formalization

# 添加Mathlib依赖
lake update
```

## 配置lakefile.lean

编辑项目中的 `lakefile.lean` 文件，添加Mathlib依赖：

```lean
import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

package «pca-formalization» where
  -- add package configuration options here

lean_lib «PcaFormalization» where
  -- add library configuration options here

@[default_target]
lean_exe «pca-formalization» where
  root := `Main
```

## 构建项目

```bash
# 获取并构建Mathlib（第一次会很慢，可能需要30分钟-2小时）
lake exe cache get
lake build
```

## VS Code配置（可选但推荐）

```bash
# 安装VS Code
# 然后安装Lean 4扩展
code --install-extension leanprover.lean4
```

## 测试安装

创建一个简单的测试文件：

```bash
cat > Test.lean << 'EOF'
import Mathlib

#check Nat
#eval 2 + 2

theorem test : 2 + 2 = 4 := by rfl

#check test
EOF

# 检查文件
lean Test.lean
```

如果看到输出没有错误，说明安装成功！

## 常见问题

### 问题1：curl不可用
```bash
sudo apt-get update
sudo apt-get install curl
```

### 问题2：网络连接问题
如果在国内，可能需要设置代理或使用镜像：
```bash
# 使用代理
export https_proxy=http://your-proxy:port
```

### 问题3：Mathlib下载太慢
```bash
# 使用缓存服务器
lake exe cache get
```

## 运行本项目的代码

安装完成后：

```bash
cd ~/code/deep-representation-learning-book/lean_formalization
cp PCA_Denoising.lean pca-formalization/PcaFormalization/
cd pca-formalization
lake build PcaFormalization.PCA_Denoising
```

## 资源链接

- Lean 4 官方文档: https://lean-lang.org/
- Mathlib 文档: https://leanprover-community.github.io/mathlib4_docs/
- Lean 4 教程: https://leanprover.github.io/theorem_proving_in_lean4/
- Lean Zulip 聊天: https://leanprover.zulipchat.com/
