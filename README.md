# Project Lemma

Project Lemma is an independent research project led by Troy Valiyaparampil. It investigates open mathematical questions using AI to develop arguments and formal proofs. Each investigation records the problem, the proof or certificate, what the literature already establishes, and the roles of the human researcher and AI systems.

## Research index

### Problem 001: The First Mills Number on Fourteen Vertices

How little data can the busiest of fourteen machines store if each pair of data items must share a machine? The optimal fraction is **7/23**. In extremal combinatorics this gives $L(14)=M_1(14)=7/23$. Equivalently, the maximum fractional matching number of an intersecting hypergraph on fourteen vertices is **23/7**.

The theorem establishes the $q=3$ case of Füredi’s 1990 conjecture. Barker supplied an attaining construction in 2008. Our literature review located no earlier proof of the matching universal bound. Historical priority remains open to correction.

The theorem gives $C(70,21,2)=C(33,10,2)=C(43,13,2)=15$. For every positive integer $n$, it gives $C(70n,21n,2)=15$ with the published construction. The companion equality $C(69n,21n,2)=14$ follows from Barker’s construction and an incidence count. The supplementary data distinguish prior bounds from consequences of the sharp inequality.

**Public research preprint · Version 1.0.0 · 25 November 2026.** Formally verified in Lean 4. Independent peer review remains pending.

[Read the paper](problems/001-mills-number-14/paper/paper.pdf) · [Inspect the Lean proof](problems/001-mills-number-14/formal/VERIFICATION.md) · [Construction certificates](problems/001-mills-number-14/certificates/README.md) · [Reproduce the checks](problems/001-mills-number-14/README.md) · [Supplementary results](problems/001-mills-number-14/results/README.md)

## Research practice

We look for questions whose status can be checked against primary sources. A proof establishes a mathematical statement. A literature search addresses priority. Formal verification and explicit construction certificates give readers ways to check the reasoning independently. Each problem reports which checks ran and whether the work has received peer review.

Independent scrutiny, corrections and references to earlier work are welcome through [GitHub Issues](https://github.com/troytsv/project-lemma/issues). Identify the problem number and the statement or source involved. [Research directory](problems/README.md) · [AI contributions](AI_DISCLOSURE.md) · [Licensing](LICENSING.md) · [How to contribute](CONTRIBUTING.md)

The [Project Lemma publication skill](tools/skills/project-lemma-publication/SKILL.md) contains the maintainer workflow for preparing, publishing, auditing and disseminating an investigation.
