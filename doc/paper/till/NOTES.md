# NOTES.md — Internal Submission Notes
## "A Delay-Graded Lax Monad: Timed Multiset Rewriting with Proven-Exact Acceleration"

This file is NOT for inclusion in the PDF. It collects:
1. Reviewer-facing weak points (moved verbatim from scale paper Appendix A)
2. Notation conflicts resolved during the merge
3. Bib deduplication log
4. TODO-verify citations from both source refs.bib files
5. Disposition table: every numbered theorem/definition/law from both sources

---

## 1. Reviewer-Facing Weak Points (Honest Self-Review)

*Moved verbatim from till-scale/main.tex Appendix A (label: app:weak-points).
This content MUST NOT appear in the PDF.*

1. **No mechanized proofs.** Every theorem in §§ calculus–cohort-firing is
   on-paper only. A POPL submission without at least the central cut-admissibility
   result in a proof assistant will draw pushback; mechanizing THY_0023's graded
   fragment is the highest-leverage pre-submission investment.

2. **The bridge is extra-logical and trusted.** The `settle` → derivability
   direction rests on the `@fire` oracle rule being excluded from the
   cut-elimination claim and flagged `unverified: 'modeSwitch'` at runtime — the
   "execution = proof search" slogan needs a clearer formal scope statement (which
   steps are kernel-checked, which are trusted).

3. **No formal IMTL / timed-MSR comparison.** The graded-relative vs.
   labeled-absolute design axis (§ fenced grades) is asserted, not proven — a
   reviewer will ask for an embedding or separation theorem between till and IMTL.

---

## 2. Notation Conflicts Resolved During Merge

The monad paper's names win in every conflict. Scale-paper usages were rewritten.

| Concept | Monad name | Scale name | Resolution |
|---|---|---|---|
| Graded lax monad | `\lax{S}{d}` (`{S}@d`) | `\laxm{A}{d}` | Use `\lax` |
| Bare lax monad | `\lax{S}{0}` | `\laxb{A}` (`{A}`) | New `\laxb` macro kept for readability |
| Counted bang | `\gbang{k}` | inline `$!_k A$` | Use `\gbang` |
| Timed action | `\act` (`\rhd`, ⊳) | `\action` (`\triangleright`) | Use `\act` |
| Additive conjunction | `\addconj` (`\&`) | `\with` (`\&`) | Use `\addconj` |
| Truth judgment suffix | `A\tr` | `\jtrue{A}` | Use `\tr` suffix form |
| Lax judgment marker | `S\laxjdg{d}` | `\jlax{S}{d}` | Use `\laxjdg` suffix form |
| Tropical dioid | `\TT` (`\mathbb{T}`) | `\Ttrop` | Use `\TT` |
| Rationals | `\QQ` | `\Q` | Use `\QQ` |
| Non-neg rationals | `\QQ_{\geq 0}` (inline) | `\Qnn` | Use `\QQ_{\geq 0}` inline |
| Naturals | `\NN` | `\N` | Use `\NN` |
| Partial residual | `\res` (`\ominus`) | `\res` (`\ominus`) | **Same — no conflict** |
| Stamp notation | `\stmp{a}{t}` | `A@t` (inline) | Use `\stmp` |
| Theory premise | `\thprem{...}` | inline | Use `\thprem` |

New macros added (scale-only concepts not in monad paper):
- `\laxb{S}` — bare `{S}` lax monad (= `\lax{S}{0}`)
- `\adddisj` — additive disjunction ⊕
- `\enc{A}` — labelled-state encoding bracket ⌈A⌉
- `\wop{q}` — weighted additive disjunction `+[q]`

---

## 3. Bibliography Deduplication Log

**26 unique entries from monad paper + 18 new from scale paper = 44 total entries.**
(JensenKristensenWells2007 kept separately from Jensen2007CPN — different publications.)

Deduplicated pairs (scale key → canonical monad key):

| Scale key | Monad canonical key | Notes |
|---|---|---|
| WatkinsCervesatoPfenningWalker02 | Watkins2002CLF | Same paper, same data |
| FairtloughMendler97 | FairtloughMendler1997 | |
| PfenningDavies01 | PfenningDavies2001 | |
| GirardScedrovScott92 | GirardScedrovScott1992 | |
| Atkey18 | Atkey2018 | |
| OrchardLiepeltEades19 | OrchardLiepeltEades2019 | Scale had page numbers; merged in |
| VollmerMarshallEadesOrchard25 | VollmerMarshallEadesOrchard2025 | Title differs; TODO-verify |
| HanukaevEades25 | HanukaevEades2025 | Author name and title differ; TODO-verify |
| Katsumata14 | Katsumata2014 | |
| FujiiKatsumataMellies16 | FujiiKatsumataMillies2016 | Spelling: Mellies vs Millies; kept monad spelling |
| Iemhoff24 | Iemhoff2024 | Format differs (book vs misc/arXiv); kept misc, added TODO-verify |
| KanovichKiriginNigamScedrovTalcott16 | KanovichFORMATS2016 | |
| deSaToninhoPfenning23 | deSaToninhoPfenning2023 | Scale had page note; merged in |
| GaboardiKatsumataOrchardBreuvartUustalu16 | GaboardiICFP2016 | |
| Nakano00 | Nakano2000 | |
| BaccelliCohenOlsderQuadrat92 | Baccelli1992 | |
| NegriVonPlato98 | NegriVonPlato1998 | |

**17 duplicate pairs collapsed. 18 new scale-only entries added.**

Scale-only entries renamed to monad style (AuthorYear):

| Old scale key | New canonical key |
|---|---|
| AlurDill94 | AlurDill1994 |
| BanatreLeMet90 | BanatreLeMetayer1990 |
| BengtssonYi04 | BengtssonYi2004 |
| BestDevillers87 | BestDevillers1987 |
| DanosEhrhard11 | DanosEhrhard2011 |
| Gabbay96 | Gabbay1996 |
| GreenKarvounarakisTannen07 | GreenKarvounarakisTannen2007 |
| Huet80 | Huet1980 |
| JensenKristensenWells07 | JensenKristensenWells2007 |
| Martens15 | Martens2015 |
| MurrayMcsherry13 | MurrayMcSherry2013 |
| Negri05 | Negri2005 |
| Newman42 | Newman1942 |
| NigamOlartePimentel17 | NigamOlartePimentel2017 |
| OlartePimentelDePaiva19 | OlartePimentelDePaiva2019 |
| Paun00 | Paun2000 |
| Peled93 | Peled1993 |
| BoigelotFAST | BoigelotFAST (kept — journal entry) |

---

## 4. TODO-verify Citations

Consolidated from both source refs.bib files (all % TODO-verify markers):

From monad paper:
- **MoonEadesOrchard2021**: page numbers
- **VollmerMarshallEadesOrchard2025**: exact title and page numbers (scale paper has different title "A Mixed Linear and Graded Logic" and different author order)
- **HanukaevEades2025**: exact title and authors (scale paper has "Combining Dependency, Grades and Adjoint Logic" and "Avi Hanukaev"; monad has "Arnon Hanukaev")
- **GRASS2026**: full title, authors, and venue
- **KanovichFORMATS2016**: exact author list and page numbers
- **KanovichResilient2024**: exact title, venue, and page numbers
- **Jensen2007CPN**: year (2007 or 2009) and exact title; publisher
- **deSaToninhoPfenning2023**: page numbers and exact ACM DOI
- **LassezMcAloon1990**: exact title and page numbers; which Lassez–McAloon paper covers CLP-style constraint discharge
- **Ohlebusch2002**: exact chapter reference for deterministic 3-CTRSs
- **Amer1984**: exact title and journal
- **Iemhoff2024**: book or arXiv? Exact publisher/venue

From scale paper (additional):
- **deSaToninhoPfenning2023**: page numbers and exact ACM DOI (duplicate of above)
- **FujiiKatsumataMellies16 (= FujiiKatsumataMillies2016)**: FoSSaCS 2016 volume and page range
- **OrchardLiepeltEades2019**: exact article number and pages
- **VollmerMarshallEadesOrchard2025**: title and authors (see above)
- **HanukaevEades2025**: title and authors (see above)
- **NigamOlartePimentel2017**: CONCUR 2017 LIPIcs volume number and pages
- **Peled1993**: exact title (source says "Ample Sets in Partial-Order Reduction")
- **MurrayMcSherry2013**: Naiad SOSP 2013 (Murray et al.) vs Differential Dataflow CIDR 2013 (McSherry et al.) — verify which is intended
- **BoigelotFAST**: Boigelot is associated with LASH, not FAST (by Bardin/Finkel/Leroux/Petrucci) — verify intended citations and whether LASH should be added separately
- **Iemhoff2024**: book ("Proof Theory for Lax Logic", Springer 2024) per scale paper vs arXiv:2209.08976 per monad paper — need to verify

---

## 5. Disposition Table

Every numbered theorem/definition/law from both source papers.
Status: **MERGED** = appears exactly once in merged paper | **DUPLICATE** = collapsed with MERGED item | **DROPPED** = excluded per task instructions

### From till-monad/main.tex

| Source item | Merged location | Status |
|---|---|---|
| Thm 2.1 Grade Preservation | §2, Thm 2.1 | MERGED |
| Thm 3.1 Presentation Equivalence | §3, Thm 3.1 | MERGED |
| Thm 4.1 Cut Admissibility | §4, Thm 4.1 | MERGED |
| Thm 4.2 Identity Expansion | §4, Thm 4.2 | MERGED |
| Thm 4.3 Counted-Bang Completeness | §4, Thm 4.3 | MERGED |
| Cor 4.4 (misc: consistency, subformula, admissible compositions) | §4, Cor 4.4 | MERGED |
| Prop 5.1 Lexicographic-first is unsound | §5, Prop 5.1 | MERGED |
| Thm 5.2 Determinism and composability | §5, Thm 5.3 | MERGED (renumbered; Prop 5.2 B&B inserted before it) |
| Thm 5.3 Termination/Zeno guard | §5, Thm 5.4 | MERGED (renumbered) |
| Thm 6.1 Exactness | §6, Thm 6.1 | MERGED |
| Thm 6.2 Timed confluence | §6, Thm 6.2 | MERGED |
| Thm 6.3 Work adequacy | §6, Thm 6.3 | MERGED |
| Thm 6.4 Work/makespan separation | §6, Thm 6.4 | MERGED |
| Thm 6.5 Oracle soundness | §6, Thm 6.5 | MERGED |
| Thm 7.1 Fusion = Atomicity | §7, Thm 7.1 | MERGED |
| Remark 7.2 Engineering corollary | §7, Rem 7.2 | MERGED |

### From till-scale/main.tex

| Source item | Merged location | Status |
|---|---|---|
| Thm 3.2 Grade Preservation | §2, Thm 2.1 | DUPLICATE of monad Thm 2.1 |
| Thm 3.3 Cut Admissibility | §4, Thm 4.1 | DUPLICATE of monad Thm 4.1 |
| Thm (Identity Expansion) | §4, Thm 4.2 | DUPLICATE of monad Thm 4.2 |
| Thm (Counted-Bang Completeness) | §4, Thm 4.3 | DUPLICATE of monad Thm 4.3 |
| Thm (Work Adequacy) | §6, Thm 6.3 | DUPLICATE of monad Thm 6.3 |
| Thm (Work/Makespan Separation) | §6, Thm 6.4 | DUPLICATE of monad Thm 6.4 |
| Prop (Lex-first unsound) | §5, Prop 5.1 | DUPLICATE of monad Prop 5.1 |
| Prop (B&B sound and complete) | §5, Prop 5.2 | MERGED (new in merged paper) |
| Thm E5 (Composability / Frame-Rate Independence) | §5, Thm 5.3 | DUPLICATE of monad Thm 5.2 (scale proof kept as it's clearer) |
| Thm (Determinism) | §5, Thm 5.3 | DUPLICATE (subsumed into monad Thm 5.2) |
| Thm (Termination) | §5, Thm 5.4 | DUPLICATE of monad Thm 5.3 |
| Lem (Representation Adequacy, THY_0024) | §8, Lem 8.1 | MERGED (new in merged paper) |
| Thm (Forced-Prefix Batching, THY_0025) | §8, Thm 8.2 | MERGED (new in merged paper) |
| Mass Conservation (woplus) | §3, Remark | MERGED (brief) |
| Derivation Forest ≅ Markov Chain (woplus) | §3, Remark | MERGED (brief) |
| Phase-Independence Lemma | §8.2 (prose) | MERGED |
| Appendix A (Reviewer weak points) | NOTES.md §1 | MOVED TO NOTES.md |

### Disposition counts

- From monad paper: 16 items → 16 MERGED (none dropped)
- From scale paper: 17 distinct numbered items → 4 MERGED + 12 DUPLICATE + 1 MOVED-TO-NOTES
- Refinement sorts section (scale §3.5): EXCLUDED per task instructions (no THY_0020 content)
- Scale paper Appendix A (reviewer weak points): moved verbatim to this file

---

*Last updated: 2026-08-23*
