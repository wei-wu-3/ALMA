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

This modular design separates concerns across layers, allowing each layer's
proofs and combinators to be reused independently. Compared to a flat Cosmos
definition, the layered architecture reduces proof burden for composition
and coherence laws by distributing them into single-layer components.

分层设计将关注点按层次分离，各层的证明和组合子可独立复用。
相较扁平 Cosmos 定义，分层架构将复合与相干律的证明负担分散到各单层组件中，
显著降低了高层构造的证明复杂度。

## Preprint / 预印本

<https://philpeople.org/profiles/wei-wu-3>

## Dependencies & Build / 依赖与构建

- Agda v2.8.0  
- Agda Standard Library v2.4  

## Architecture / 架构

src/ALMA/
├── Cosmos/
│   ├── Iso.agda                    -- Object isomorphisms
│   ├── ContCategory.agda           -- Container category
│   ├── ContCategoryLemmas.agda     -- Algebraic lemmas for container morphism equivalence
│   ├── ObjEquivCat.agda            -- Categories with object equivalence
│   ├── ObjEquivFunctor.agda        -- Functors preserving object equivalence
│   ├── ContCatEquiv.agda           -- Base category + container functor
│   ├── ContCatEquivLemmas.agda     -- Lemmas: onPos-subst-comm, comp-nat-shape-eq
│   ├── ContCatEquivFunctor.agda    -- Morphisms between ContCatEquivs
│   ├── UnfoldingObject.agda        -- Object-level unfolding structure
│   ├── UnfoldingMorphism.agda      -- Morphism-level unfolding structure
│   ├── MorphismObject.agda         -- Object-level homomorphisms
│   └── MorphismMorphism.agda       -- Action compatibility (onActP)
└── Cosmos.agda                     -- Terminal coalgebra: Cosmos, _⇒ℱ_, id⇒ℱ, _∘⇒ℱ_, UnitCosmos

## Contributing / 贡献指南

Discussions, proof ideas, literature references and code contributions 
are all welcome
欢迎讨论交流、证明思路、文献指引与代码贡献