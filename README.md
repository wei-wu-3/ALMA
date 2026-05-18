# ALMA — Arche of Being: Logically Necessary Metatheoretical Architecture

ALMA 是论文 *Arche of Being: Logically Necessary Metatheoretical Architecture* 的配套形式化框架，
基于依赖类型论（Agda v2.8.0）构建，将论文中的核心本体论原理编码为形式化定理并提供证明。

## 论文链接
[PhilPeople 预印本](https://philpeople.org/profiles/wei-wu-3)

## 模块结构

| 模块 | 哲学对应 | 核心内容 |
|------|---------|---------|
| `Prelude` | 逻辑基础 | 同一律、矛盾律、虚无排除 |
| `Indestructibility` | 不可消减原理 | 永恒流、两种构造模式、唯一性定理 |
| `Core` | 动态存在者 | 过程、张量积、对称幺半范畴结构 |
| `Beings` | 相干模式与演化 | 相干阶段、不可逆定理 |
| `Cosmos` | 宇宙结构 | 投影、嵌入、不可重构定理 |
| `Inhomogeneity` | 非均匀性 | 内在差异必然性 |
| `Interact` | 动态关联性 | 交互、耦合、对偶观察 |
| `StandardModel*` | 标准模型实例 | 意识涌现、相变演示 |

## 依赖与编译

- Agda v2.8.0
- Agda 标准库 (standard-library) v2.3

```bash
# 克隆仓库
git clone https://github.com/wei-wu-3/ALMA.git
cd ALMA

# 编译所有模块
agda src/ALMA/StandardModelAll.agda
