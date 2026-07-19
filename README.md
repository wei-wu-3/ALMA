# ALMA — Arche of Being: Logically Necessary Metatheoretical Architecture
# ALMA — 存在之本原：逻辑必然的元理论架构

## Introduction / 简介

ALMA is a formal framework grounded in type theory, category theory, containers,
and coalgebras. Its modular, parameterized architecture separates categorical
infrastructure (categories with object equivalence, container functors) from
unfolding systems (polynomial coalgebras), enabling composable universe constructions.
At its core lies Cosmos — an infinite, unbounded, self-referential dynamic universe — providing a mathematical model for philosophical ontology.

ALMA 是基于类型论、范畴论、容器、余代数的形式化框架。其架构采用模块化参数化设计：
将范畴基础设施（对象等价范畴、容器函子）与展开系统（多项式余代数）解耦，
实现宇宙构造的可组合性。项目核心 Cosmos —— 无限无界动态自指涉宇宙，
为哲学本体论研究提供数学模型。

The project adopts a three-tier modular architecture that captures the evolutionary development of the formalization:

项目采用三层模块化架构，清晰反映了形式化过程中的演进脉络：

src/ALMA/Prototype/ contains the original, self-contained, and fully hand-unfolded formalization of the philosophical ideas from the paper. It serves as the first Agda prototype, specifically designed to trace the formation process of the formalized philosophy. 

src/ALMA/Prototype/ 是论文哲学思想在 Agda 中首次形式化的完全自包含、手工展开初始原型，旨在完整追溯该哲学思想形式化的生成脉络。

src/ALMA/InitialPass/ represents the first community-assisted refactoring iteration. It was developed after the proof of comp-cong-≃⇒ℱ became entangled in subst complexities during the prototype phase. Following feedback from the Agda community, this version was rebuilt upon a generalized categorical library.

src/ALMA/InitialPass/ 该版本为首次基于社区反馈的重构迭代。其起因是原型阶段 comp-cong-≃⇒ℱ 的证明深陷 subst 复杂性泥潭；后经 Agda 社区指导，基于通用范畴库重新构建而成。

src/ALMA/Cosmos/ (along with the root Cosmos.agda) is the ongoing, latest evolution of the codebase. It is currently under active development, with its core closure mechanisms and internal consistency not yet fully finalized.

src/ALMA/Cosmos/（及根目录 Cosmos.agda）则为当前演进中的最新代码。该项目目前仍在积极开发中，其核心闭合机制及内部一致性尚待最终确立。

## Preprint / 预印本

<https://philpeople.org/profiles/wei-wu-3>

## Dependencies & Build / 依赖与构建

- Agda v2.8.0  
- Agda Standard Library v2.4  

## Architecture / 架构

src/ALMA/
├── Cosmos.agda
├── Cosmos/
│   ├── ContCategory.agda
│   ├── ContCategoryLemmas.agda
│   ├── ContCatEquiv.agda
│   ├── ContCatEquivLemmas.agda
│   ├── ContCatEquivFunctor.agda
│   ├── ContFunctor.agda
│   ├── MorphismMorphism.agda
│   ├── MorphismObject.agda
│   └── Unfolding.agda
├── InitialPass/
│   ├── ContCategory.agda
│   ├── ContCategoryLemmas.agda
│   ├── ContCatEquiv.agda
│   ├── ContCatEquivLemmas.agda
│   ├── ContCatEquivFunctor.agda
│   ├── Cosmos.agda
│   ├── MorphismMorphism.agda
│   ├── MorphismObject.agda
│   ├── ObjEquivCat.agda
│   ├── ObjEquivFunctor.agda
│   └── Unfolding.agda
└── Prototype/
    ├── Beings.agda
    ├── Cosmos.agda
    ├── Indestructibility.agda
    ├── Prelude.agda
    ├── Properties.agda
    ├── StandardModel.agda
    └── Universe.agda

## Contributing / 贡献指南

Discussions, proof ideas, literature references and code contributions 
are all welcome
欢迎参与讨论、提供证明思路与文献指引，或贡献代码
