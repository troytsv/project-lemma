# Covering certificates

[`known15.txt`](known15.txt) is the unchanged 15-block certificate published on 22 October 2026 by Arhan Canli (Quantavane). It is reproduced under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). Its SHA-256 is `c04ae2eb837507c43560e500ae598368a249418444a7c4846e91aaa39dd02274`. [Source file](https://github.com/arhancanli/quantavane-covering-records/blob/main/coverings/C_70_21_2_15.txt)

Each row lists one block of 21 points, numbered 1 through 70. The project verifiers check that these blocks contain all 2,415 pairs.

## Replay the comparison with prior records

The regression tests include explicit permutations that map the Quantavane construction to the two records below. Download the original data into this directory under the indicated filenames. Each comparison runs when its source file is present.

| Source | Local filename | SHA-256 |
| --- | --- | --- |
| [Meliwat's C70_21_2_b15.txt](https://github.com/Meliwat/covering-hunt/blob/master/records/C70_21_2_b15.txt) | `meliwat15.txt` | `3f89ef622d633a3f93b8ebdaf4f0377cf002ae795afdfae18cb8e64eb499a538` |
| C(70,21,2) entry in [IRSI's September certificate ZIP](https://irsi.ai/records/irsi-certificates-2026-09-25.zip) | `irsi-original.txt` | `0db44e17f4ccc0c7c6c6bd4f984597f4f086b7d460e8ae3199e828c9c1b3a024` |

IRSI lists the ZIP SHA-256 as `baba879c2874f0572ef7eae95f06ba9959c99a289706da0333d69563d781ca25`. [IRSI table and archive information](https://irsi.ai/tables.html)

With both files available, run from the problem directory.

```text
python verification/verify_pairs.py certificates/known15.txt certificates/meliwat15.txt certificates/irsi-original.txt
python verification/search/verify_dual.py certificates/known15.txt certificates/meliwat15.txt certificates/irsi-original.txt
python -B -m unittest discover -s verification/search -v
```
