# ALMA — Arche of Being: Logically Necessary Metatheoretical Architecture
# ALMA —— 存在之本原：逻辑必然的元理论架构

## Introduction / 简介

ALMA is a formal framework grounded in type theory, category theory, containers, and coalgebras. Its modular, parameterized architecture decouples categorical infrastructures (object-equivalence categories and container functors) from unfolding systems (polynomial coalgebras), thereby supporting composable universe constructions. At its core is Cosmos—an infinite, unbounded, self-referential dynamic universe—which serves as a mathematical model for philosophical ontology.

ALMA 是基于类型论、范畴论、容器及余代数的形式化框架。其模块化参数化架构将对象等价范畴与容器函子等范畴基础设施，同多项式余代数等展开系统相解耦，从而支撑起宇宙构造的可组合性。项目核心 Cosmos——一个无限、无界、动态且自我指涉的宇宙——为哲学本体论研究提供了数学模型。

The project is structured into three modular layers, each corresponding to a distinct stage in the formalization's evolutionary process:

项目结构划分为三个模块化层级，每一层分别对应形式化在演进过程中的特定阶段：

src/ALMA/Prototype/ — The original, self-contained, hand-unfolded prototype. It serves as the first Agda formalization of the paper's philosophical ideas, designed to trace their conceptual genesis.

src/ALMA/Prototype/ —— 完全自包含、手工展开的初始原型。它是论文哲学思想在 Agda 中的首次形式化呈现，旨在追溯其思想概念的生成脉络。

src/ALMA/InitialPass/ — The first community-assisted refactoring, developed to resolve the subst complexity in the comp-cong-≃⇒ℱ proof. Based on community feedback, this iteration was rebuilt upon a generalized categorical library.

src/ALMA/InitialPass/ —— 基于社区反馈，为解决原型阶段 comp-cong-≃⇒ℱ 证明中的 subst 复杂性问题，依托通用范畴库进行了首次重构。

src/ALMA/Cosmos/ — The ongoing, latest evolution of the codebase. Currently under active development, its core closure mechanisms and internal consistency are still being finalized.

src/ALMA/Cosmos/ —— 当前演进中的最新代码。该项目仍在积极开发中，其核心闭合机制与内部一致性尚待最终确立。

## Motivation / 动机

The inherent ambiguity and non-computability of natural language render it an unreliable tool for rigorously examining the logical necessity of philosophical thought; mathematics is therefore introduced as a more precise alternative.

自然语言固有的歧义性与不可计算性，使其无法成为严格审查哲学思想逻辑必然性的可靠工具；因此，数学被引入，作为一种更精确的替代。

## Preprint / 预印本

<https://philpeople.org/profiles/wei-wu-3>

## Dependencies & Build / 依赖与构建

- Agda v2.8.0  
- Agda Standard Library v2.4  
- agda-categories v0.3.0

## Architecture / 架构

```text
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

## References / 参考文献

Abbott, M., Altenkirch, T., & Ghani, N. (2003). Categories of containers. In A. D. Gordon (Ed.), Foundations of software science and computation structures (LNCS 2620, pp. 23–38). Springer. https://doi.org/10.1007/3-540-36576-1_2

Abbott, M., Altenkirch, T., & Ghani, N. (2005). Containers: Constructing strictly positive types. Theoretical Computer Science, 342(1), 3–27. https://doi.org/10.1016/j.tcs.2005.06.002

Baars, B. J. (1989). A cognitive theory of consciousness. Cambridge University Press.

Bohr, N. (1935). Can quantum-mechanical description of physical reality be considered complete? Physical Review, 48(8), 696–702. https://doi.org/10.1103/PhysRev.48.696

Chalmers, D. J. (1995). Facing up to the problem of consciousness. Journal of Consciousness Studies, 2(3), 200–209.

Dehaene, S., & Changeux, J.-P. (2011). Experimental and theoretical approaches to conscious processing. Neuron, 70(2), 200–227. https://doi.org/10.1016/j.neuron.2011.03.018

Einstein, A. (1905). Zur Elektrodynamik bewegter Körper. Annalen der Physik, 322(10), 891–921. https://doi.org/10.1002/andp.19053221004

Hawking, S. W. (1988). A brief history of time: From the big bang to black holes. Bantam Books.

Heidegger, M. (1962). Being and time (J. Macquarrie & E. Robinson, Trans.). Harper & Row. (Original work published 1927)

Jacobs, B. (1999). Categorical logic and type theory (Studies in Logic and the Foundations of Mathematics, Vol. 141). Elsevier Science.

Kant, I. (1781/1787). Kritik der reinen Vernunft. Hartknoch.

Leibniz, G. W. (1989). Philosophical essays (R. Ariew & D. Garber, Trans.). Hackett Publishing.

Parmenides. (1983). Fragments of on nature. In G. S. Kirk, J. E. Raven, & M. Schofield (Eds.), The presocratic philosophers (2nd ed., pp. 239–268). Cambridge University Press.

Penrose, R. (2016). Fashion, faith, and fantasy in the new physics of the universe. Princeton University Press.

Prigogine, I. (1980). From being to becoming: Time and complexity in the physical sciences. W. H. Freeman.

Wittgenstein, L. (1922/1981). Tractatus logico-philosophicus (C. K. Ogden, Trans.). Routledge & Kegan Paul.
