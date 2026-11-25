# Understanding the fourteen-vertex proof

You can demonstrate the question with fourteen cards labeled as machines. Give each data item a list of the cards that store it. Two items can be compared locally if their lists share a card. Items with the same list can be combined into one list with their total weight. The load on a card is the sum of the weights of lists containing it. The question is how small the busiest card's share can be.

## What was known, and what had to be proved?

Colin Barker recorded a covering with 69 items and fourteen cards in 2008. Each card holds 21 items and all 2,346 pairs share a card. This proves that a largest load of 21/69, or 7/23, **can occur**. No amount of checking those 2,346 pairs can show every other distribution has a load at least that large. That second assertion, including distributions with unequal or irrational weights, is the substance of the proof.

## Why change the units?

Measure weight so that every card has capacity 21. If you could store unit total mass with largest load below 7/23, you could scale up until the busiest card has load 21. The total would then exceed 69. We assume that situation and derive a contradiction. The word **exceed** matters. Barker's covering occupies exactly the boundary.

On any proposed set of lists, maximize the total mass subject to the fourteen capacity inequalities. At an extreme point there can be at most fourteen positive weights. Otherwise the fourteen-row incidence matrix has dependent columns. One can vary the positive weights a little in opposite directions along that dependence, keeping every card load fixed. Their midpoint could not have been an extreme point. This reduction chooses a convenient hypothetical counterexample and allows its mass to increase.

## What does one four-card list tell you?

Call a list an edge. Add up the loads on the cards of an edge. That sum counts every edge's weight at least once, since all lists intersect. An edge on four cards counts its own weight four times. If its weight is $w$, then $84\ge W+3w$, where $W>69$ is the total. Hence $w<5$. A list of three or fewer cards cannot even count all $W$. A five-card list weighs less than 9 by the same argument.

Every unit of weight uses at least four slots. There are $14\cdot21=294$ slots. The excess $E$ counts slots used beyond four per unit. Then $E\le294-4W<18$. Every unit on a larger list consumes at least one excess slot, so the total weight $H$ on the larger lists is below 18. More than 51 units must be on four-card lists. There are at least eleven such lists.

## Why count deficits?

For each four-card list write its weight as five minus a deficit. If there are $t$ such lists, their total deficit is $D=5t-W+H$. Deficits measure how much freedom the four-card lists have to overlap. On a given four-card list $A$, the extra intersections with *other* lists cost less than three times its own deficit. Each extra intersection with $B$ costs all of $B$'s weight.

The proof shows $D\ge4$. Try the opposite. Five four-card lists through one card would weigh more than $25-4=21$, so every card has four-card degree at most four. Every card occurs in at least one four-card list: even all the large lists together cannot supply its minimum load. On any four-card list the sum of its four degrees is at least $t+3$, counting itself four times and the rest at least once. Counting all the unused degree capacity $4-d$ along incident lists in two ways gives incompatible lower and upper bounds. For $t=11$ they are 24 and 22. For $t=12,13,14$ the contradictions are even stronger.

## Which configurations survive?

Since $5t=W-H+D>55$, there are at least twelve four-card lists and at most two larger ones. Cards outside every large list need at least five incident four-card lists. To see why, sum the loads on the other three cards of each incident list. If the card has degree $k$, then $63k\ge kW+(3-k)\ell$, where $\ell\le21$ is its load. Degrees one through four all contradict $W>69$. Each such outside card therefore receives at least four units of deficit. Each four-card list spends its deficit on at most three outside cards, since it meets a large list. If there are $o$ outside cards, $4o\le3D$.

This inequality rules out a single large list. The excess budget and the same inequality rule out any large list of size six or more. The only possibility is twelve four-card lists and two five-card lists. If the five-card lists have two cards in common, too many four-card lists must meet those already heavily loaded cards. More than two common cards would require more outside deficit than is available.

## The last pigeonhole

The two five-card lists have one common card $v$. Four cards belong only to the first list, four only to the second, and five to neither. The deficit and unused-capacity equations force exactly two four-card lists to contain $v$. The other ten share **less than two units of deficit altogether**.

If two of those ten met twice, the extra intersections in both directions would require a combined deficit greater than $5/2$. Thus they meet only once. Each must also meet each five-card list only once, since an extra intersection with one of those heavy lists would exceed the entire allowance for that four-card list. Each of the ten therefore contains one first-only card, one second-only card and a pair of outside cards.

Sort the ten lists by their first-only card. There are four groups. In a single group the lists already share that first card, so their outside pairs must be disjoint. Five outside cards accommodate at most two disjoint pairs. Four groups therefore accommodate at most eight lists. The required ten cannot exist.

## Questions worth answering in your own words

- **Does the argument rely on enumerating every arrangement?** It eliminates all arrangements by inequalities. The numerical search recovered a known example. Removing the search leaves the proof intact.
- **Why doesn't the proof exclude Barker's covering?** There $W=69$. The nine retained plane lines have weight exactly five and the three large lists weigh eighteen in total. Both are strict inequalities in the contradiction argument. The construction actually has eleven four-card lists.
- **How does this settle the 70-point problem?** Fourteen blocks of size 21 could have load only $21/70$, smaller than $7/23$. So at least fifteen blocks are necessary. A separately published certificate attains fifteen.
- **What did Lean certify?** The universal statement about real weights and an explicit equality example. The verification report identifies the separate formal results about ordinary block systems. Scholarly priority, human authorship and the adequacy of a journal submission are questions for people.
- **What remains open here?** This paper settles one value of $q$. The proof does not classify every optimal fourteen-vertex arrangement or settle the conjecture in general.

To prepare for an expert discussion, derive $w<5$, $D\ge4$ for $t=11$, and the final eight-list limit on paper. Then follow the two common-vertex cases in the manuscript, especially the use of total slack to rule out zero or one four-card list through $v$. [Manuscript](../paper.pdf) · [Axiom and build audit](../formal/VERIFICATION.md)
