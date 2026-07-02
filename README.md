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

## Preprint / 预印本

<https://philpeople.org/profiles/wei-wu-3>

## Dependencies & Build / 依赖与构建

- Agda v2.8.0  
- Agda Standard Library v2.4  

## Architecture / 架构

src/ALMA/
├── Cosmos/
│   ├── Iso.agda                  -- Object isomorphisms
│   ├── ContCategory.agda         -- Container category
│   ├── ObjEquivCat.agda          -- Categories with object equivalence
│   ├── ObjEquivFunctor.agda      -- Functors preserving object equivalence
│   ├── ContCatEquiv.agda         -- Base category + container functor
│   ├── ContCatEquivFunctor.agda  -- Morphisms between ContCatEquivs
│   ├── UnfoldingObject.agda      -- Object-level unfolding structure
│   ├── UnfoldingMorphism.agda    -- Morphism-level unfolding structure
│   ├── MorphismObject.agda       -- Object-level components of coalgebra homomorphisms
│   └── MorphismMorphism.agda     -- Action compatibility for coalgebra homomorphisms
└── Cosmos.agda                   -- Terminal coalgebra: Cosmos, _⇒ℱ_, id⇒ℱ, _∘⇒ℱ_, UnitCosmos

### Dependency order (bottom-up)

Iso → ContCategory → ObjEquivCat → ObjEquivFunctor
                                    ↓
ContCatEquiv → ContCatEquivFunctor ──────────────┐
       ↓                                         ↓
UnfoldingObject → UnfoldingMorphism              │
       ↓                  ↓                      │
MorphismObject ──→ MorphismMorphism              │
       ↓                  ↓                      ↓
       └──────────────────┴──────────────────────┘
                          ↓
     Cosmos (terminal coalgebra) + UnitCosmos (instance)

## Contributing / 贡献指南

Discussions, proof ideas, literature references and code contributions 
are all welcome.
欢迎讨论交流、证明思路、文献指引与代码贡献。
