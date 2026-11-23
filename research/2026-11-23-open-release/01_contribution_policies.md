# Contribution policies for AI-assisted Lean 4 formalization (research report)

Date of research: 2026-11-23. Tags: [READ] = read on the page itself, [SNIPPET] = seen only in a search result, [INFERRED] = my conclusion. Note: WebFetch returns a small-model summary of each page, so "READ" means the page was opened, not that I saw raw text. Two files (docs/100.yaml, docs/1000.yaml) were fetched with curl and searched with grep, so those are full-text checks.

## 1 Summary

1. Mathlib does NOT ban AI-assisted PRs. It requires disclosure in the PR description (tools and how used), a comment "LLM-generated" to get the label for substantial LLM code, and that the author fully understands and can defend every line without AI help. [READ] https://leanprover-community.github.io/contribute/index.html
2. Low-quality LLM PRs may be closed without comment, and repeat offenders can be banned from PRs and Zulip. Using an LLM to write GitHub or Zulip comments is forbidden. [READ] same page.
3. The GitHub label "LLM-generated" is in heavy use: 1430 PRs carry it, 579 of those have a "[Merged by Bors]" title, 426 are open. So AI-written PRs are routinely merged. [READ via GitHub API, counts of 2026-11-23] (details in section 2)
4. Mathlib license is Apache-2.0; each file needs a header "Copyright (c) YEAR Name. All rights reserved. / Released under Apache 2.0 license ... / Authors: ..." Newcomers work from a fork; no write-access procedure is documented. [READ]
5. Reservoir needs: public non-fork GitHub repo, lake-manifest.json at root, OSI/SPDX license detected by GitHub, and at least 2 stars. [READ] https://reservoir.lean-lang.org/inclusion-criteria
6. 1000+ list already has rows for Baker's theorem, Bang's theorem and Zsigmondy's theorem, all with NO formalization linked. No BBP or Machin row found. Entries are added by PR to mathlib (docs/1000.yaml) and external-repo links are allowed. [READ]
7. formal-conjectures (Google DeepMind) accepts Erdos problem statements and links to formal proofs of solved ones (many such PRs merged 2026-11-23); it follows Mathlib's AI conventions; needs the Google CLA. [READ]
8. PrimeNumberTheoremAnd: task-claim workflow, own PR style file with an AI section (disclose tool, understand every line, at most about 3 open AI PRs, size under about 500 lines preferred). [READ]
9. Archiving: Zenodo GitHub integration gives a DOI per release; Zenodo allows AI tools but not as listed authors and wants substantive AI use disclosed. Software Heritage: Save Code Now, no account. [READ / SNIPPET]
10. A GPL or CC0 source repo does not by itself block Mathlib contribution if you hold the copyright and relicense your own files as Apache-2.0; GPL-derived third-party text would. [INFERRED]

## 2 Mathlib and AI

Written policy (community site contribution guide, text says "mid 2026" for context) [READ] https://leanprover-community.github.io/contribute/index.html and mirror https://mathlib.org/contribute/index.html:
- Using AI in any form must be stated in the PR description, with which tools and how.
- Substantial LLM-generated code: add the label by posting a comment with the single word "LLM-generated".
- Contributors must understand all AI-written content and justify design decisions to reviewers without AI help.
- No LLM-written comments on GitHub or Zulip.
- Low-quality LLM-produced PRs may be closed without comment, especially when the idea was not discussed with the community first; repeat offences can mean suspension or permanent ban from PRs and Zulip.
- AI-written code without a Lean expert's supervision is said to fall well short of Mathlib standards.
- PR size: no numeric limit. Small fixes and single lemmas are almost always welcome; longer PRs extending existing theories are welcome; new theories get more scrutiny (taught at university level? fits maintainers' interests?). The page notes more than 2600 open PRs mid 2026, and suggests alternatives to contributing directly. Asking on the #mathlib Zulip channel whether a topic fits is recommended.
- The PR template contains no AI section. [READ] https://raw.githubusercontent.com/leanprover-community/mathlib4/master/.github/PULL_REQUEST_TEMPLATE.md
- The README asks newcomers to introduce plans on Zulip. [READ] https://raw.githubusercontent.com/leanprover-community/mathlib4/master/README.md
- CONTRIBUTING.md on master: HTTP 404 (file does not exist at that path). [READ]

Label: "LLM-generated", description (the one quote of this report) "PRs with substantial input from LLMs - review accordingly". [READ] https://api.github.com/repos/leanprover-community/mathlib4/labels/LLM-generated

How the policy came about: Zulip thread of Sep 2025 proposing disclosure; draft policy PR to the community site opened 2025-12-21 (website#767), revised Jan 2026. [READ] https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/policy.20proposal.3A.20mention.20AI.20use.20in.20PR.20description.3F.html Other Zulip views seen only in a search summary: a maintainer's personal Feb 2026 opinion against mass-adopting untested AI code; a "sloplib" thread about an AI-maintained fork. [SNIPPET] https://leanprover-community.github.io/archive/stream/113488-general/topic/sloplib.html

Public cases (GitHub search API, 2026-11-23, https://api.github.com/search/issues?q=repo:leanprover-community/mathlib4+is:pr+label:LLM-generated):
- Total PRs with label: 1430. Open: 426. Title starting "[Merged by Bors]": 579 (merged PRs are closed by bors so merged_at is null in the API; I counted by title). Remainder, about 425, closed without merge [INFERRED: 1430 - 579 - 426].
- Accepted example: #44917 trace identity for positive powers of matrix products, merged 2026-10-28; #42475 Poisson-Jensen formula, merged 2026-11-19; #43702 Varignon's theorem, merged 2026-11-19 (all labelled LLM-generated). [READ]
- Rejected example: #46127 "critical-line IVT zero detection and 3-4-1 zeta product positivity", by a new contributor, labels new-contributor and LLM-generated, closed 2026-11-18. The triage bot said it did not meet community standards for AI use, that reviewer time is limited and goes first to contributors who can learn and contribute back and to high-quality content. Sibling PRs #46128 and #46129 closed the same minute. https://github.com/leanprover-community/mathlib4/pull/46127 [READ via API]
- Zsigmondy in Mathlib: PR #28895 "prove Zsigmondy's theorem" (draft, by a contributor, opened 2025-08-25) was closed 2026-09-18; the thread shows only bot comments (merge conflicts), no stated reason. https://github.com/leanprover-community/mathlib4/pull/28895 [READ via API]. Search of Mathlib issues/PRs for BBP, Machin, Bailey-Borwein-Plouffe: 0 hits. [READ]
- PrimeNumberTheorem+ Zulip (Jan 2026): disclosure ideas such as Co-authored-by trailers for AI tools, logs of agent sessions; no adopted rule recorded in that thread. [READ] https://leanprover-community.github.io/archive/stream/423402-PrimeNumberTheorem+/topic/Disclosure.20of.20AI.20tools.20in.20PRs.html

CONTRADICTION of the assumption: Mathlib does take AI-written PRs, hundreds have been merged, provided they are disclosed, labelled, reviewed and of high quality. What is rejected is unsupervised, low-quality or unexplained bulk AI output, especially from first-time contributors with a big unannounced PR. [INFERRED from the above]

Practical guidance [INFERRED]: do not drop a large block of the library into one PR. Announce on Zulip (#mathlib4 or #mathlib), propose small pieces that extend existing files (for example Bernoulli or Nat.log lemmas, a primitive-prime-divisor file), disclose tools in each PR, add the LLM-generated comment, and be ready to answer review questions yourself.

## 3 Mathlib mechanics

- License: repository is Apache-2.0 (SPDX). [READ] https://api.github.com/repos/leanprover-community/mathlib4/license
- Header [READ] https://mathlib.org/contribute/style.html : block comment at the top with copyright line (year, name, "All rights reserved"), the Apache 2.0 release line pointing to the LICENSE file, and an Authors line. Label is always "Authors" (even for one), no final period, comma-separated, no "and". The guide sets no strict criteria for who is listed; the idea is people who could be asked about the file's design. Then the `module` keyword and imports.
- Who may be author: [INFERRED] a human (or humans) who takes responsibility. Nothing found that lets an AI be listed. The PR template says co-authors come from commit authors or Co-authored-by trailers at the bottom of the commit message [READ]; the PNT+ thread notes that Mathlib and CSLib have used such trailers for the Aristotle tool [READ, see section 2 link]. Whether an AI trailer is encouraged or merely tolerated for Mathlib: not found.
- Write access: a newcomer works from a fork (origin = fork, upstream = official repo), makes a branch per piece, pushes to the fork, opens PR via "compare across forks". The guide documents giving collaborators write access to YOUR fork only; no procedure for write access to the main repo was found. [READ] https://mathlib.org/contribute/git.html . The old community-site pages leanprover-community.github.io/contribute/git.html and style.html now only redirect to mathlib.org. [READ]
- Review: contributors are encouraged to find reviewers; reviewers need not be maintainers; a review queue dashboard exists; reviewers look mostly at PRs with green CI (per PR template). Merging is done by bors (titles "[Merged by Bors] - ..."). Typical PRs open for weeks to months (sample open PRs updated 2026-11 were created 2026-07 to 2026-10). [READ]
- Build steps: `lake exe cache get`, `lake build`, `lake exe mk_all` after adding a file, lint with `lake test`. [READ] README.

## 4 Reservoir

Criteria [READ] https://reservoir.lean-lang.org/inclusion-criteria :
1. Public GitHub repo, not a fork; a repo created from a template counts as a fork.
2. lake-manifest.json in the root (a root lakefile.lean was required before April 2024).
3. GitHub must detect an OSI-approved license listed in SPDX.
4. At least 2 GitHub stars.
Reservoir then indexes, builds and tests packages and shows, per commit, the toolchain and whether it builds (latest stable shown: Lean v4.36.0). [READ] https://reservoir.lean-lang.org/ . No separate submission form was found. Note for the project: the star requirement means someone other than the owner must star it; whether one's own star counts: not stated. [INFERRED]

## 5 Lists linking to external formalizations

- Both lists are edited by a PR to mathlib4 (docs/1000.yaml, docs/100.yaml), doable in the GitHub web editor. [READ] https://leanprover-community.github.io/1000.html and /100.html
- External repos: yes. 100.yaml has 17+ entries that link to separate projects; 1000.yaml entries carry a `url:` to external files (for example PrimeNumberTheoremAnd, Sard's theorem repos, Foundation). [READ] https://raw.githubusercontent.com/leanprover-community/mathlib4/master/docs/1000.yaml
- Upstream 1000+ project (https://github.com/1000-plus/1000-plus.github.io): only theorems on Wikipedia's list of theorems are accepted; each entry is keyed by Wikidata ID with status (formalized or statement), library code (code "X" = external dedicated repository) and url. [READ]
- Specific entries, from full-text grep of 1000.yaml [READ]:
  - Baker's theorem (Q3527009): row exists, no decl, no url, i.e. not formalized.
  - Bang's theorem (Q7686760): row exists, no decl.
  - Zsigmondy's theorem (Q8074796): row exists, comment "TODO: Find the code", author Mantas Baksys, date 2022; no decl. [INFERRED: an external formalization from 2022 exists but is not linked.]
  - BBP / Bailey-Borwein-Plouffe, Machin: no row in 1000.yaml or 100.yaml (only "Bailey" as an author name). They may not be on Wikipedia's theorem list; not checked. Adding a new row would require the Wikipedia/Wikidata route above. [INFERRED]
- Consequence [INFERRED]: if the project proves Zsigmondy/Bang (primitive prime divisors) or Baker's theorem, it could fill those rows by adding `url:` and status to the yaml through a small PR to Mathlib; this is likely the lowest-friction contribution. Whether a project built on Baker "from Karatarakis's proof" counts: the row says Baker's theorem, so a full proof would qualify.
- 100 list: entries 1-64 inspected (page truncated after that); no Zsigmondy/Baker/BBP/Machin. Entries 65-100 not read. [READ]

## 6 Other projects

formal-conjectures (https://github.com/google-deepmind/formal-conjectures) [READ CONTRIBUTING and README]:
- Accepts statements (proofs not needed) of open conjectures, bug fixes of statements, marking solved problems. Erdos problems from erdosproblems.com are welcome in an ErdosProblems folder.
- Solved: retag from "research open" to "research solved" and add a formal_proof attribute pointing to the proof; formal proofs may live elsewhere (long proofs, about 25-50+ lines, should be hosted elsewhere and linked); formal proofs of research problems should link a Palomar registry entry. Partly solved: not described.
- Needs Google CLA; Apache-2.0 headers; contributors keep copyright and may add themselves to AUTHORS; non-code material CC BY 4.0.
- AI: follows Mathlib's AI conventions; humans review; plans to use AlphaProof to spot misformalizations.
- Activity: 2496 PRs matched an AI-related search; seven of eight latest hits were merged on 2026-11-23 (for example "link a formal proof" PRs for Erdos 766, 494, 626, 1111). 93 PRs mention Zsigmondy/primitive/prime divisor/BBP, including open #7903 (Erdos 1100), #7425 (primitive-root variants with recorded Lean proofs). [READ via API] https://api.github.com/search/issues?q=repo:google-deepmind/formal-conjectures+is:pr
- [INFERRED] A statement or a linked external proof for an Erdos conjecture is a fit; check #7903 and neighbouring Erdos PRs for duplicate work before starting.

Erdos problems site (erdosproblems.com): pages returned HTTP 403, so its own rules could NOT be read. Related repo https://github.com/teorth/erdosproblems (Apache-2.0, 887 stars) holds data/problems.yaml, edited by PR; entries link formalized statements to formal-conjectures files; its CONTRIBUTING says AI-generated issues must disclose AI use and may be closed if low value, AI may help compute OEIS terms but results must be verified, AI-written OEIS submissions are banned; a wiki of AI assistance was frozen 2026-06-30. [READ] https://raw.githubusercontent.com/teorth/erdosproblems/main/CONTRIBUTING.md . Discussion of solutions belongs on the problem's page on the site. Other repos: Shashi456/erdos-formalizations (Lean 4, Apache-2.0, 1 star); neelsomani/gpt-erdos (LLM proof search). [SNIPPET via API search] https://api.github.com/search/repositories?q=erdosproblems

PrimeNumberTheoremAnd (https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) [READ CONTRIBUTING.md and PULL_REQUEST_STYLE.md]:
- Work from a fork; each PR maps to a task issue; comment `claim`, then `propose <PR#>`, then `awaiting-review`. New contributions on a newer "IEANTN" topic go to teorth/IEANTN instead.
- AI section (Section 13): disclose the tool with one line in the PR body (CI adds labels); consolidate related changes; tick test items only after running them; reuse the paper's own lemmas; understand every line; keep at most about three open AI-assisted PRs. Size: under about 500 lines easy, 500-2000 workable. Ask on Zulip before big or unusual work.
- Fit for number-theory results: it targets the prime number theorem blueprint; BBP or primitive prime divisors do not obviously fit [INFERRED]; the repo has an Apache LICENSE file and CITATION.cff. [READ]

Others [INFERRED / SNIPPET, not opened]: Lean FRO's CSLib (https://github.com/leanprover/cslib, Apache-2.0) is for computer science, not number theory; the search summary says CSLib and Mathlib mark Aristotle co-authorship in commits [SNIPPET, see PNT+ thread]. Lean Zulip and mathlib "Archive" folder (for formalizations of famous results not meant as library code; Mathlib's 100.yaml lists several Archive entries) are possible homes for a self-contained result such as the BBP formula. [READ for Archive in 100.yaml; fit INFERRED]

## 7 Archiving and citation

- Zenodo GitHub integration: repo must be public and licensed; log in to Zenodo with GitHub, enable the repo, then each published GitHub release is archived and given a DOI (organization repos may need owner approval of the Zenodo app). [READ] https://docs.github.com/en/repositories/archiving-a-github-repository/referencing-and-citing-content . CITATION.cff handling: not in that page. Zenodo metadata is CC0; records are kept at least as long as CERN operates (planned 20+ years); withdrawn records leave a tombstone and keep the DOI. [READ] https://about.zenodo.org/policies/
- Zenodo AI policy [READ] https://support.zenodo.org/help/en-gb/13/227 : generative AI is allowed as a tool; the research must be real human-conducted work; depositor and listed creators are fully responsible for all AI-introduced errors in text and code; AI tools cannot be listed as creators or contributors; substantive AI use should be disclosed (tool, purpose, parts affected); undisclosed use alone does not cause removal; acceptable: code generation the depositor reviews; unacceptable: raw AI output as research artifact, fabricated results, bulk AI submissions. Page "What content is not suitable" classes content mostly generated by AI with no verifiable human research link as misuse. [SNIPPET] https://support.zenodo.org/help/en-gb/2/141 [INFERRED: kernel-checked proofs under human direction, with disclosure, fit the allowed side.]
- Software Heritage: the docs site returned an access-denied bot page, so I read nothing from it. From a search summary: Save Code Now takes git, svn, hg URLs, needs no account; a GitHub Action can request archival on each release; the directory-level SWHID is recommended for academic citation; BibTeX can be generated from codemeta.json or citation.cff; do not write the SWHID into the source files themselves. [SNIPPET] https://www.softwareheritage.org/howto-archive-and-reference-your-code/ and https://docs.softwareheritage.org/devel/architecture/citation.html . No AI-content policy found for Software Heritage.

## 8 Licenses

- Mathlib: Apache-2.0 [READ]. Batteries, CSLib, PrimeNumberTheoremAnd and Lean 4 itself: Apache-2.0 [READ via GitHub license API]. formal-conjectures: Apache-2.0 code, CC BY 4.0 other material [READ]. Erdos database repo: Apache-2.0 [READ].
- The Mathlib header states files are released under Apache 2.0, so contributions must be offered under it. [READ header, INFERRED requirement]
- Does a different license in the source repo block contribution? No rule found in the pages read (nothing addresses it). [INFERRED]: (a) CC0 or any permissive license: compatible, owner can relicense own files as Apache-2.0. (b) GPL: the copyright holder can still release their own files under Apache-2.0 in a separate copy (dual licensing), but copying text from GPL third-party sources into Mathlib would not be allowed. (c) Content derived from other people's papers or the Compendium: formalizing facts is not copying text, but doc-strings should paraphrase and cite. (d) Whether AI-generated material carries copyright (and so can be licensed) is legally unsettled; I did not research it. Suggest the owner pick Apache-2.0 for the public repo, which makes Reservoir listing and later Mathlib/formal-conjectures transfer simple. [INFERRED]
- Page text addressed to me: none found in any page.

## 9 Sources

- https://leanprover-community.github.io/contribute/index.html
- https://mathlib.org/contribute/index.html
- https://mathlib.org/contribute/style.html
- https://mathlib.org/contribute/git.html
- https://raw.githubusercontent.com/leanprover-community/mathlib4/master/.github/PULL_REQUEST_TEMPLATE.md
- https://raw.githubusercontent.com/leanprover-community/mathlib4/master/README.md
- https://raw.githubusercontent.com/leanprover-community/mathlib4/master/docs/1000.yaml
- https://raw.githubusercontent.com/leanprover-community/mathlib4/master/docs/100.yaml
- https://leanprover-community.github.io/1000.html
- https://leanprover-community.github.io/100.html
- https://github.com/1000-plus/1000-plus.github.io
- https://api.github.com/repos/leanprover-community/mathlib4/labels/LLM-generated
- https://api.github.com/repos/leanprover-community/mathlib4/issues/46127 (and /comments)
- https://api.github.com/repos/leanprover-community/mathlib4/issues/28895 (and /comments)
- https://api.github.com/search/issues?q=repo:leanprover-community/mathlib4+is:pr+label:LLM-generated (several variants)
- https://api.github.com/repos/{leanprover-community/mathlib4, leanprover-community/batteries, leanprover/cslib, AlexKontorovich/PrimeNumberTheoremAnd, leanprover/lean4}/license
- https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/policy.20proposal.3A.20mention.20AI.20use.20in.20PR.20description.3F.html
- https://leanprover-community.github.io/archive/stream/423402-PrimeNumberTheorem+/topic/Disclosure.20of.20AI.20tools.20in.20PRs.html
- https://leanprover-community.github.io/archive/stream/113488-general/topic/sloplib.html (snippet only)
- https://reservoir.lean-lang.org/ and https://reservoir.lean-lang.org/inclusion-criteria
- https://github.com/google-deepmind/formal-conjectures/blob/main/CONTRIBUTING.md and raw README.md; https://api.github.com/search/issues?q=repo:google-deepmind/formal-conjectures+...
- https://raw.githubusercontent.com/AlexKontorovich/PrimeNumberTheoremAnd/main/CONTRIBUTING.md and PULL_REQUEST_STYLE.md
- https://raw.githubusercontent.com/teorth/erdosproblems/main/README.md and CONTRIBUTING.md; https://api.github.com/search/repositories?q=erdosproblems
- https://docs.github.com/en/repositories/archiving-a-github-repository/referencing-and-citing-content
- https://about.zenodo.org/policies/ ; https://support.zenodo.org/help/en-gb/13/227 ; https://support.zenodo.org/help/en-gb/2/141 (snippet); https://help.zenodo.org/docs/profile/linking-accounts/
- https://www.softwareheritage.org/howto-archive-and-reference-your-code/ (snippet); https://docs.softwareheritage.org/devel/architecture/citation.html (snippet)

## 10 Search log

- WebSearch calls: 3 of 6 (Mathlib AI policy; Zenodo AI notice; Software Heritage Save Code Now).
- WebFetch calls: about 48 (Lean community and mathlib.org pages, GitHub API and raw files, Reservoir, Zenodo, GitHub docs, SWH docs, Erdos site), plus 2 curl downloads of docs/100.yaml and docs/1000.yaml to the temp folder for text search.
- Failed or blocked: mathlib4 CONTRIBUTING.md (404); lean-lang.org/doc/reservoir (404); contribute/howto.html (404); docs.softwareheritage.org pages (bot-protection block); erdosproblems.com and /faq (403); old community-site git.html and style.html (redirect notices only).
- Not done: Mathlib Zulip threads read beyond the two archive pages; the Erdos site's own AI policy; the 100 list entries 65-100; the Wikipedia theorem list (to see if BBP is there); legal status of copyright in AI-generated code.
- No personal details were used in any query.
