# Pair-covering corollaries

For integers $2\le k\le v$, write $C(v,k,2)$ for the least number of $k$-subsets of a $v$-set whose union of pairs is all pairs. If there is a covering with at most fourteen blocks, index its blocks by distinct coordinates of a fourteen-set. For each point take the set of indices of its blocks and give it weight $1/v$. Every point lies in a block because $v\ge2$. The index sets intersect pairwise, and the load at each used coordinate is $k/v$. Unused coordinates have load zero. The theorem gives $k/v\ge7/23$, hence $C(v,k,2)\ge15$ whenever $7v>23k$.

More generally, fourteen machines storing data for all-to-all comparison must have a machine holding at least $7/23$ of total data weight. With $v$ equal-sized items, some machine must hold at least $\lceil 7v/23\rceil$ items. The Barker design attains the fraction for 69 items. With per-vertex capacity one the corresponding maximum total fractional matching mass is $23/7$.

[Supplementary table of the ten exact covering consequences](ten-exact.csv) · [Full 39-row comparison](pair-coverings.csv)

## Two infinite families

Given a $(v,k,2)$-covering, replace every point by a set of $n$ copies. Replace every block by the union of the copies of its points. Pairs of copies of different points inherit a covering block from their originals. Copies of the same point share any block containing that point. This gives $C(nv,nk,2)\le C(v,k,2)$ for positive integers $n$.

- **$C(70n,21n,2)=15$.** Use the fifteen-block construction for $(70,21,2)$ and the strict bound above, since $7\cdot70>23\cdot21$. IRSI posted a fifteen-block covering in September 2026. Meliwat and Arhan Canli (Quantavane) posted fifteen-block coverings in October. The repository has point and block relabelings for comparison of these certificates. [IRSI](https://irsi.ai/tables.html), [Meliwat](https://github.com/Meliwat/covering-hunt), [Quantavane](https://quantavane.com/results/coverings/c-70-21-2/), [certificate replay](../certificates/README.md)
- **$C(69n,21n,2)=14$.** Use Barker's fourteen-block covering, scaled as above. A cover with at most thirteen blocks would have $k/v\ge L(13)=4/13$, whereas $21/69=7/23<4/13$. This family follows from the archived construction and the earlier $L(13)$ result. [La Jolla v1.2.1](https://doi.org/10.5281/zenodo.24119701), [Hall, Horsley and Stinson, Theorem 1.3](https://doi.org/10.1007/s10623-024-01418-6)

## Comparison with dated records

[The CSV](pair-coverings.csv) lists the 39 La Jolla v1.2.1 pair-covering cells for which the archive lower bound is below 15 and $7v>23k$. All 39 listed lower bounds equal 14, as does the Schönheim bound in these rows. The archived upper bounds give 19 exact values of 15. Including the independently published $(70,21,2)$ certificate yields 20 exact values and 19 rows with a lower bound of 15 and a compared upper bound of 16 or 17.

- The 2024 Hall–Horsley–Stinson bound $L(14)>(123+\sqrt{1297})/532$ already forces at least 15 blocks in 24 rows, including six exact rows. [Theorem 1.5](https://doi.org/10.1007/s10623-024-01418-6)
- For five more rows, $k/v=3/10$ and the project's earlier proof already gives the same lower bound. Four of those rows have a compared upper bound of 15. The other is $15\le C(40,12,2)\le16$ using the archive construction. This interval describes the dated comparison, with the current successor-table status unverified. [Research history](../research/history.md)
- For the remaining ten rows, $3/10<k/v<7/23$ and the archive reports an upper bound of 15. They give exact values relative to these comparisons. The pairs $(v,k)$ are $(33,10)$, $(43,13)$, $(53,16)$, $(56,17)$, $(63,19)$, $(66,20)$, $(73,22)$, $(76,23)$, $(79,24)$, and $(83,25)$. For example, Michael Dambmann's 2008 constructions give the upper bounds for $(33,10)$ and $(43,13)$. The $(66,20)$ upper bound follows by doubling the $(33,10)$ construction. Archive records also identify deletion constructions for some cells. [Successor listing for $(33,10)$](https://www.coveringrepository.com/systems.aspx?k=10), [La Jolla blocks for $(43,13)$](https://ljcr.dmgordon.org/cover/show_cover.php?k=13&t=2&v=43)

These counts compare a fixed archive and the cited 2026 records. They measure the difference between specified bounds. Earlier literature may already imply individual values. The targeted contemporary search checked the IRSI, Meliwat, and Quantavane records and found a relevant update at $(70,21)$. The comparison does not include a complete current export of the successor database. See the [priority assessment](../l14/prior-work.md).

## Verify the ten fifteen-block certificates

Each of the ten exact values beyond the earlier project's ratio bound has an explicit block list in [covering-certificates.json](covering-certificates.json). The verifier checks the block count, distinctness, sizes, point labels and every point pair. It verifies 528 pairs for $(33,10)$ and 903 pairs for $(43,13)$.

```sh
python -B results/verify_covering_certificates.py
```

The certificate JSON contains ten entries from `covers.json` in Daniel M. Gordon's La Jolla Coverings Repository v1.2.1 under CC BY 4.0. The block labels and order are unchanged. Project Lemma extracted the entries and changed the indentation. The archive credits Michael Dambmann for $(33,10)$, $(43,13)$, and $(56,17)$, Jan de Heer and Steve Muir for $(53,16)$, $(73,22)$, and $(83,25)$, and LJCR for the derived constructions at $(63,19)$, $(66,20)$, $(76,23)$, and $(79,24)$. [Dataset DOI](https://doi.org/10.5281/zenodo.24119701) · [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)

To check the provenance, request bytes `0-4999999` of the [versioned covers.json](https://zenodo.org/api/records/24119701/files/covers.json/content). The prefix has SHA-256 `baa5b3c9f226248f5f4afb7172f165e5f6916c029b9053eb62d9cbffee8d70cf`. The ten entries begin at zero-based offsets `2183433`, `2555075`, `2850555`, `2937776`, `3098650`, `3172611`, `3313920`, `3380059`, `3443192`, and `3505784`, in the order used in the certificate file.

Pass the prefix to the verifier to check the actual archive constructions for all 39 rows and to match the ten bundled lists to the archive. The byte limit keeps the download under 5 MB if the server ignores the requested range.

```sh
curl -fL --range 0-4999999 --max-filesize 5000000 \
  --output covers-prefix.json https://zenodo.org/api/records/24119701/files/covers.json/content
python -B results/verify_covering_certificates.py --archive-prefix covers-prefix.json
```

## Reproduce the CSV

Download [coverdata.json](https://zenodo.org/api/records/24119701/files/coverdata.json/content) from Daniel M. Gordon's [La Jolla Coverings Repository v1.2.1](https://doi.org/10.5281/zenodo.24119701), published 10 November 2026 under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). The script verifies the archive hash. The CSV attributes archive-derived fields to Gordon and retains the original upper bound beside the contemporary value.

```sh
python -B results/compare_coverings.py coverdata.json > results/pair-coverings.csv
```

`outcome=exact` means the theorem's lower bound and the compared upper bound coincide. Each `*_excludes_14` field records whether the named older theorem suffices by itself. The reduced parameter pair and common factor flag rows where scaling is possible. Dated upper bounds are read from the archive index. The script checks their consistency with the lower bounds. The two family seeds have separate [Barker](../l14/classify/verify_barker.py) and [Quantavane](../certificates/README.md) certificate checkers.
