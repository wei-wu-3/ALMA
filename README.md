# ALMA — Arche of Being: Logically Necessary Metatheoretical Architecture

[![build](https://img.shields.io/github/actions/workflow/status/wei-wu-3/ALMA/build.yml?branch=main&label=build&logo=github&logoColor=white)](https://github.com/wei-wu-3/ALMA/actions/workflows/build.yml)
[![Docs Status](https://github.com/wei-wu-3/ALMA/actions/workflows/docs.yml/badge.svg)](https://github.com/wei-wu-3/ALMA/actions/workflows/docs.yml)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21511879.svg)](https://doi.org/10.5281/zenodo.21511879)

## Introduction / 简介

ALMA is a formal framework grounded in type theory, category theory, containers, and coalgebras. Its modular, parameterized architecture decouples categorical infrastructures (object-equivalence categories and container functors) from unfolding systems (polynomial coalgebras), thereby supporting composable universe constructions. At its core is Cosmos—an infinite, unbounded, self-referential dynamic universe—which serves as a mathematical model for philosophical ontology.

ALMA 是基于类型论、范畴论、容器及余代数的形式化框架。其模块化参数化架构将对象等价范畴与容器函子等范畴基础设施，与多项式余代数等展开系统解耦，从而支撑起宇宙构造的可组合性。项目核心 Cosmos——一个无限、无界、动态且自我指涉的宇宙——为哲学本体论研究提供了数学模型。

The project is structured into three layers, each corresponding to a distinct stage in the formalization's evolutionary process:

项目结构划分为三个层级，每一层分别对应形式化在演进过程中的特定阶段：

src/ALMA/Prototype/ — The initial, fully self-contained and hand-unfolded prototype. It traces the trajectory from a one-to-one mapping of philosophical concepts to their convergence into a single coinductive record, where the resulting "subst hell" motivated all subsequent refactoring. Frozen for archival purposes as the first Agda formalization of the paper's philosophical ideas, it preserves the genesis of the conceptual framework.

src/ALMA/Prototype/ —— 完全自包含、手工展开的初始原型。它记录了从哲学概念的一对一映射到收敛为单一余归纳记录的演进轨迹；正是由此引发的“subst hell”问题推动了后续全部重构。作为论文哲学思想在 Agda 中的首次形式化呈现，已冻结存档，保留了概念框架的生成脉络。

src/ALMA/InitialPass/ — An intermediate refactoring that decomposes the monolithic prototype into separate modules. It represents the first structural reorganization following community feedback.

src/ALMA/InitialPass/ —— 介于原型与最新架构之间的中间重构层，旨在将单体原型拆分为独立模块。它是吸纳社区反馈后的首次结构性重组。

src/ALMA/Cosmos/ — The active main line of development. Building on the structural decomposition of InitialPass, it achieves full modularization and categorical reconstruction atop the standard library's containers and agda-categories, with unified bilingual Chinese–English comments throughout.

src/ALMA/Cosmos/ —— 当前活跃开发的主线架构。它在 InitialPass 结构性拆分的基础上，依托标准库容器与 agda-categories 实现模块化及范畴论重建，并统一采用中英文双语注释。

## Motivation / 动机

The inherent ambiguity and non-computability of natural language render it an unreliable tool for rigorously examining the logical necessity of philosophical thought; mathematics is therefore introduced as a more precise alternative.

自然语言固有的歧义性与不可计算性，使其无法成为严格审查哲学思想逻辑必然性的可靠工具；因此，数学被引入，作为一种更为精确的研究载体。

### Tool Migration and Ontological Commitment / 工具迁移与本体论承诺

The formalization has undergone three tool migrations, each driven by a fundamental conflict in ontological commitment. In the QS5+BF phase, the Barcan Formula forces all possible worlds to share a single domain of quantification. The subsequent turn to Lean 4 revealed, beyond expressivity bottlenecks, that its mathematical library's deep entrenchment in the law of excluded middle and classical set theory constitutes a direct conflict at the level of ontological commitment. Agda was ultimately selected: its constructive foundation presupposes no classical axioms whatsoever, and its dependent types and coinductive records align precisely with the ontological commitments of this work. This migratory trajectory itself reveals that formalization languages are not neutral notational vehicles; their logical foundations, type structures, and axiomatic environments collectively constitute an implicit set of ontological commitments. To choose a tool is to choose an ontology.

形式化历经三次工具迁移，其背后是本体论承诺的根本性冲突。QS5+BF 阶段，Barcan 公式强制所有可能世界共享同一论域。转向 Lean 4 后，除表达力瓶颈外，更发现与其数学库对排中律与经典集合论的深度嵌入，直接构成本体论承诺层面的冲突。最终选定 Agda：其构造性基底不预设任何经典公理，依赖类型与余归纳记录恰与该项工作的本体论承诺完全相合。这一迁移历程本身揭示：形式化语言并非中性的记号载体；其逻辑基底、类型结构与公理环境，共同构成一套隐性的本体论承诺。工具选择，即本体论选择。

## Key Contribution / 核心贡献

### A Novel Mathematical Structure / 一种新的数学结构

The central construction of the formalization is the coinductive record Cosmos: it consolidates container structure, an intrinsic category, the action of morphisms on shapes, coalgebraic unfolding, and dynamic self-reference into a single type, thereby granting philosophical thought a machine-checkable, rigorous expression. Its ontological commitment is as follows: what Cosmos characterizes is the structure of the Cosmos insofar as it can be determined by logical necessity, rather than a hypothetical model in the empirical-scientific sense subject to physical falsification—though this does not preclude the structure's trivialization under specific conditions, whereby it degenerates into precisely such a model.

形式化的核心构造是余归纳记录 Cosmos：它将容器结构、内禀范畴、态射对形状的变换、余代数展开及动态自我指涉收束于单一类型，使哲学思想获得机器可检验的严格表达。其本体论承诺在于：Cosmos 所刻画的，是宇宙就其可被逻辑必然性所规定而言的结构，而非经验科学意义上可被物理检验的假设模型——这并不排斥该结构在特定条件下平凡化，从而退化为这样的模型。

## Dependencies & Build / 依赖与构建

### Prerequisites / 依赖

| Dependency | Version |
|---|---|
| [Agda](https://github.com/agda/agda) | 2.8.0 |
| [Agda Standard Library](https://github.com/agda/agda-stdlib) | 2.4 |
| [agda-categories](https://github.com/agda/agda-categories) | 0.3.0 |

### Build / 构建

```bash
git clone https://github.com/wei-wu-3/ALMA.git
cd ALMA
agda -i src src/Everything.agda
```

## Architecture / 架构

```text
src/
├── ALMA/
│   ├── Cosmos.agda
│   ├── Cosmos/
│   │   ├── ContCategory.agda
│   │   ├── ContCategoryLemmas.agda
│   │   ├── ContFunctor.agda
│   │   ├── ContCatEquiv.agda
│   │   ├── ContCatEquivFunctor.agda
│   │   ├── Unfolding.agda
│   │   ├── MorphismObject.agda
│   │   ├── ContCatEquivLemmas.agda
│   │   ├── MorphismMorphism.agda
│   │   ├── Terminal.agda
│   │   ├── CoalgCat.agda
│   │   ├── Lambek.agda
│   │   ├── MorphismCorrespondence.agda
│   │   ├── ListCosmos.agda
│   │   └── Closure.agda
│   ├── InitialPass/
│   │   ├── ObjEquivCat.agda
│   │   ├── ObjEquivFunctor.agda
│   │   ├── ContCategory.agda
│   │   ├── ContCategoryLemmas.agda
│   │   ├── ContCatEquiv.agda
│   │   ├── ContCatEquivFunctor.agda
│   │   ├── Unfolding.agda
│   │   ├── MorphismObject.agda
│   │   ├── ContCatEquivLemmas.agda
│   │   ├── MorphismMorphism.agda
│   │   └── Cosmos.agda
│   └── Prototype/
│       ├── Prelude.agda
│       ├── Cosmos.agda
│       ├── Properties.agda
│       ├── Indestructibility.agda
│       ├── Beings.agda
│       ├── Universe.agda
│       └── StandardModel.agda
└── Everything.agda
```

## Contributing / 贡献指南

Discussions, proof ideas, literature references and code contributions are all welcome.

欢迎参与讨论、提供证明思路与文献指引，或贡献代码。

## Preprint / 预印本

### English Version / 英文版

*Arche of Being: Logically Necessary Metatheoretical Architecture*

- [English Record](https://philpapers.org/rec/WUTVFF)
- [English PDF](https://philpapers.org/archive/WUTVFF.pdf)

### Chinese Version / 中文版

*存在之本原：逻辑必然的元理论架构*

- [Chinese Record](https://philpapers.org/rec/WEIJML-2)
- [Chinese PDF](https://philpapers.org/archive/WEIJML-2.pdf)

## Works Cited / 参考文献

Abbott, Michael, Thorsten Altenkirch, and Neil Ghani. 2003. "Categories of Containers." In *Foundations of Software Science and Computation Structures*, edited by Andrew D. Gordon, 23–38. Lecture Notes in Computer Science 2620. Berlin: Springer. https://doi.org/10.1007/3-540-36576-1_2.

Abbott, Michael, Thorsten Altenkirch, and Neil Ghani. 2005. "Containers: Constructing Strictly Positive Types." *Theoretical Computer Science* 342, no. 1: 3–27. https://doi.org/10.1016/j.tcs.2005.06.002.

Baars, Bernard J. 1989. *A Cognitive Theory of Consciousness*. Cambridge: Cambridge University Press.

Bohr, Niels. 1935. "Can Quantum-Mechanical Description of Physical Reality Be Considered Complete?" *Physical Review* 48, no. 8: 696–702. https://doi.org/10.1103/PhysRev.48.696.

Chalmers, David John. 1995. "Facing Up to the Problem of Consciousness." *Journal of Consciousness Studies* 2, no. 3: 200–209.

Dehaene, Stanislas, and Jean-Pierre Changeux. 2011. "Experimental and Theoretical Approaches to Conscious Processing." *Neuron* 70, no. 2: 200–227. https://doi.org/10.1016/j.neuron.2011.03.018.

Derrida, Jacques. 1967. *De la grammatologie*. Paris: Les Éditions de Minuit.

Einstein, Albert. 1905. "Zur Elektrodynamik bewegter Körper." *Annalen der Physik* 322, no. 10: 891–921. https://doi.org/10.1002/andp.19053221004.

Gödel, Kurt. 1931. "Über formal unentscheidbare Sätze der *Principia Mathematica* und verwandter Systeme I" [On Formally Undecidable Propositions of *Principia Mathematica* and Related Systems I]. *Monatshefte für Mathematik und Physik* 38: 173–198. https://doi.org/10.1007/BF01700692.

Hawking, Stephen William. 1988. *A Brief History of Time: From the Big Bang to Black Holes*. New York: Bantam Books.

Hegel, Georg Wilhelm Friedrich. 1969. *Science of Logic*. Translated by Arthur V. Miller. London: George Allen & Unwin. Originally published 1812.

Heidegger, Martin. 1962. *Being and Time*. Translated by John Macquarrie and Edward Robinson. New York: Harper & Row. Originally published 1927.

Hu, Jason Z. S., and Jacques Carette. 2021. "Formalizing Category Theory in Agda." In *Proceedings of the 10th ACM SIGPLAN International Conference on Certified Programs and Proofs*, 327–342. New York, NY, USA: Association for Computing Machinery. https://doi.org/10.1145/3437992.3439922.

Jacobs, Bart. 1999. *Categorical Logic and Type Theory*. Studies in Logic and the Foundations of Mathematics 141. Amsterdam: Elsevier Science.

Kant, Immanuel. 1781/1787. *Kritik der reinen Vernunft*. Riga: Hartknoch.

Landauer, Rolf. 1961. "Irreversibility and Heat Generation in the Computing Process." *IBM Journal of Research and Development* 5, no. 3: 183–191. https://doi.org/10.1147/rd.53.0183.

Leibniz, Gottfried Wilhelm. 1989. *Philosophical Essays*. Translated by Roger Ariew and Daniel Garber. Indianapolis: Hackett Publishing.

Norell, Ulf. 2007. "Towards a Practical Programming Language Based on Dependent Type Theory." PhD diss., Department of Computer Science and Engineering, Chalmers University of Technology, Gothenburg.

Parmenides. 1983. "Fragments of *On Nature*." In *The Presocratic Philosophers*, 2nd ed., edited by Geoffrey S. Kirk, John E. Raven, and Malcolm Schofield, 239–268. Cambridge: Cambridge University Press.

Penrose, Roger. 2016. *Fashion, Faith, and Fantasy in the New Physics of the Universe*. Princeton: Princeton University Press.

Prigogine, Ilya. 1980. *From Being to Becoming: Time and Complexity in the Physical Sciences*. San Francisco: W. H. Freeman.

Rutten, Jan J. M. M. 2000. "Universal Coalgebra: A Theory of Systems." *Theoretical Computer Science* 249, no. 1: 3–80. https://doi.org/10.1016/S0304-3975(00)00056-6.

Wittgenstein, Ludwig. 1922/1981. *Tractatus Logico-Philosophicus*. Translated by Charles Kay Ogden. London: Routledge & Kegan Paul.

## Declarations / 声明

Funding: This research received no specific grant from any funding agency in the public, commercial, or not-for-profit sectors.

基金支持：本研究未获得任何公共、商业或非营利部门的专项资助。

Conflict of Interest: The author declares no financial or non-financial conflicts of interest relevant to this study.

利益冲突：作者声明不存在任何与本研究相关的财务或非财务利益冲突。

Ethics Approval: This study is a purely philosophical and theoretical inquiry involving no human or animal experimentation; ethical approval is not applicable.

伦理审批：本研究为纯哲学理论探讨，不涉及人类或动物实验，无需伦理审批。

Informed Consent (Participation): No human participants were involved; informed consent is not applicable.

知情同意（参与）：本研究不涉及人类参与者，无知情同意适用对象。

Informed Consent (Publication): This manuscript contains no individually identifiable information; consent for publication is not applicable.

知情同意（发表）：本研究不包含任何可识别个人身份的信息，无需发表同意。

Data Availability: This study is a theoretical analysis and did not generate empirical data; a data availability statement is not applicable.

数据可用性：本研究为理论分析，未生成实证数据，数据可用性声明不适用。

Author Contributions: The author independently completed the research conception, logical analysis, and manuscript writing.

作者贡献：作者独立完成研究构思、逻辑分析与论文撰写。

Use of AI Tools: Generative AI tools were employed solely in auxiliary capacities during the preparation of this manuscript. AI-generated content was used exclusively as a reference for constructing counterarguments and for preliminary code drafting. All translated passages were verified through back-translation and finalized following sentence-by-sentence review by the author. The author assumes full academic responsibility for the entirety of this manuscript, including text, code, data, citations, and conclusions.

AI工具使用：本研究在辅助性环节使用了生成式人工智能工具。AI生成内容仅用于构建反驳论证的参考及代码草稿；相关翻译文稿均通过回译校验，经作者逐句审核定稿。作者对论文的全部内容（包括文字、代码、数据、引用及结论）承担完整的学术责任。

## Acknowledgments / 致谢

The author wishes to express sincere gratitude to Mr. Liang Wenfeng for his pivotal contributions to the open-source advancement of large language models, from which a broad public community—including the present study—has directly benefited.

谨向梁文峰先生致以诚挚感谢。其在推动AI语言模型开源领域的关键性贡献，令包括本研究在内的广泛公众群体直接受益。
