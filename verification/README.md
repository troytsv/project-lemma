# Rebuild the release files

The publication candidate contains one primary manuscript at the repository root, with its generated `paper.bbl` and source `references.bib`. The release ZIP also contains the formal sources, tests, research notes, machine-readable outcomes, disclosures and license notices. The arXiv source archive and journal ZIP contain only their respective manuscript files. Contact lists, draft correspondence and personal declarations are maintained separately for the author's review.

## Source and artifact replay

1. Follow the [formal verification report](../formal/VERIFICATION.md) for the pinned toolchain, statement and axiom checks. Run the ordinary certificate commands in the root [README](../README.md) and `python results/verify_covering_certificates.py` for the ten additional examples.
2. Set `SOURCE_DATE_EPOCH=1795564800` in the environment. In a clean directory, copy `paper.tex` and `references.bib` and run `tectonic --keep-intermediates paper.tex`. This regenerates both the PDF and the formatted bibliography; the first run needs access to the standard TeX bundle. With that bundle cached you can use `--only-cached`. Compare the rebuilt files to the candidate. Tectonic version used for the release is 0.17.0+20260731.
3. From a Git checkout run `python verification/package_release.py ../release-output --rev HEAD`. This packages the specified committed tree, independent of other working-tree files. The ZIP comment identifies the commit. The command writes three versioned archives and `SHA256SUMS.txt`. The script uses the Python standard library and Git.
4. Extract and build the arXiv source package locally to check it before any upload. It contains `paper.tex`, `references.bib`, `paper.bbl` and a `00README.json` selecting XeLaTeX. arXiv's final PDF must also be reviewed on the platform after submission preparation is authorized. [arXiv processing specification](https://info.arxiv.org/help/00README.html)
5. For journal submission the candidate ZIP contains editable sources, the formatted bibliography and the matching PDF. Supply author-confirmed contact details and declarations in the final journal copy and portal. An external editor makes the publication decision.

The [dataset replay](../results/README.md) explains how to regenerate the comparative CSV from Gordon's versioned public index. The third-party certificates carry separate attribution and license terms. [Licensing and sources](../REFERENCES.md)
