# Palomar registry: what a submission requires (research report, 2026-11-24)

Tags: [READ] = read on the page/file itself; [SNIPPET] = seen only in a search result; [INFERRED] = my deduction.
Pages carry no visible dates. All fetches were done on 2026-11-24. ASCII only.

## 1 Summary

1. Palomar is a free, automated registry of Lean 4 results. An entry = one public GitHub repo at one 40-char commit SHA + one comparator.json. [READ] https://palomar-registry.org/about
2. Submission is through a web form (GitHub sign-in proving push access) or an agent protocol (tag + secret gist via `gh`). No account, no e-mail; the status-page link is the only way back. [READ] https://palomar-registry.org/how-to-submit
3. Checks: mechanical (Lean `lake comparator`, kernel + nanoda replay, axioms limited to propext/Quot.sound/Classical.choice), then a language-model review (statement fairness, disclosure, "research interest" floor). No human reads the mathematics. Review target: one hour. [READ] about page, policy CONTRIBUTING.md
4. Required files: lean-toolchain (>= v4.35.0-rc2), lakefile.toml or .lean, lake-manifest.json, Challenge.lean, Solution.lean, comparator.json, formalization.yaml (v0.4), one root LICENSE whose SPDX id equals project.license. [READ]
5. Challenge: <= 1,000 lines and 100 KiB (300 lines / 32 KiB preferred); transitive imports only Lean core / Mathlib (or Tau Ceti / CSLib). The project's own library may NOT be in its import closure. [READ]
6. Solution may use the repo's own library (contained path dependencies) or pinned public GitHub dependencies. [READ]
7. BIGGEST OBSTACLE (new rule): every committed .lean file in the submitted repo (including unused files and contained path dependencies) must start with `module` and have <= 10,000 lines. A 3,000-module library written without the module system would have to be ported. Only external pinned Git dependencies are exempt from the line cap. [READ] policy sec 2.1; llms.txt
8. AI-written proofs are accepted; automation (models, framework, tool setup) must be disclosed in formalization.yaml. project.authors and responsible_maintainers must be humans only. [READ]
9. Registering is permanent (append-only; only a moderator tombstone). Withdrawal is possible only before registering. New versions of the same ID are allowed. [READ]
10. Registry data is CC0 (the record only); the repo keeps its own licence. The formal-conjectures repo asks that formal proofs of research problems link to a Palomar entry. [READ]

## 2 The registry

- Purpose: Palomar, "a registry of Lean-verified mathematics"; public, searchable; each entry points to an immutable repository version and records the checked statement, dependencies, proof-check result and the review's comments. [READ] https://palomar-registry.org/ , /about , /statement
- Who runs it: the pages do not name people or an institution. GitHub org PalomarRegistry hosts PalomarPolicy, PalomarTemplate, PalomarSubmission (comparator CI), PalomarServer (Cloudflare Worker over GitHub state), PalomarWeb, PalomarReviewer, PalomarDatabaseTools, PalomarDatabase. [READ] GitHub API org repo list. The statement page says it builds on tools from the Lean FRO (comparator, Verso) and the Mathlib Initiative (formalization.yaml). [READ] /statement. "Technical Maintainers" and "Moderators" exist but are not named. [READ] policy sec 9.1
- Launch status: the policy says Palomar "has not launched in the sense of inviting submissions", while the append-only guarantee has been in force since 2026-08-10. [READ] https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md sec 8. The template and the Anthropic repo nonetheless describe live submissions. Treat as "open but described as pre-launch". [INFERRED]
- Submission route: public GitHub repo + full commit SHA + Comparator config path (+ optional project path, formalization.yaml path, existing Palomar ID for a new version) at https://submit.palomar-registry.org/ . Proof of push access: GitHub sign-in (browser), or for agents a tag `palomar-verify-<challenge>` at the commit plus a secret gist carrying the challenge, via `gh`. The submitter must declare being a responsible author/maintainer of the substantive formalization, or having approval from one (recorded permanently and public). Up to 10 verification attempts per intake; an intake is discarded after 15 minutes. [READ] https://submit.palomar-registry.org/llms.txt ; /how-to-submit
- Recommended pre-flight: call the reusable workflow PalomarRegistry/PalomarSubmission/.github/workflows/submission.yml at a pinned commit with `mode: full`, `execution_profile: palomar-standard-v1` and options JSON containing comparator_config_path and authorization_relationship. A local lake build or standalone comparator run is declared "not equivalent". [READ] submit llms.txt
- Automated checks: (a) mechanical: scan of all sources, headers confirmed with Lean, Challenge compiled against core + Mathlib only, comparator run offline in a sandbox, kernel plus nanoda replay, con-ron advisory; (b) language-model review with fixed prompts (prompts, rubric.json, schemas are public in PalomarPolicy); (c) disclosure check. Outcomes: neutral (no blocking problem), revision_required, rejected, review-failed (operational). [READ] CONTRIBUTING.md sec 5, 7
- Human review: none ("no human editorial step"). No appeal on an individual result; a rejected submission can be revised and resubmitted after a waiting period that lengthens with repeats. [READ] /about. The specification calls a cooldown policy an open question, yet submit llms.txt says cooldowns "still apply". [READ] spec.md; submit llms.txt
- Turnaround: mechanical run first (public GitHub Actions); review aimed within one hour after mechanical pass (target, not guarantee); an entry appears only after the database pull request is merged. [READ] /how-to-submit
- Updates/withdrawal: withdraw from any non-terminal state (no public trace of the review); after registering you cannot withdraw. New versions keep the same ID (same repo, project path, comparator path; new commit); old versions stay resolvable; a new result gets a new ID. Technical-maintainer metadata corrections exist; a moderator can retract a version (tombstone). [READ] /how-to-submit; CONTRIBUTING.md sec 9
- Public: repo, commit, submission id, declared authorization relationship and any approval note (public from verification on); after registering: the record, redacted review (comments, no scores), reviewer model ids, policy commit, preservation forks in github.com/PalomarArchive (submitted repo and every pinned Git dependency), immutable tags, Verso-rendered Challenge. The submitter's GitHub account is not published. Rejected/withdrawn reviews are not public; operators retain reviews indefinitely. [READ] /how-to-submit; CONTRIBUTING.md sec 8
- Data: https://data.palomar-registry.org/api/v1/results (CC0), RSS, schema-v3.json. [READ] /llms.txt

## 3 Layout and files

Ordinary layout (repo root = Lean project) [READ CONTRIBUTING.md sec 2; template https://github.com/PalomarRegistry/PalomarTemplate]:

    lean-toolchain  lakefile.toml|lakefile.lean  lake-manifest.json
    formalization.yaml  Challenge.lean  Solution.lean  comparator.json  LICENSE
    (template also: README.md, docbuild/, scripts/, test/, a project library folder)

Template scripts: check-lean-sources.py, validate-formalization.rb, verify-comparator.sh. Template pins lean v4.35.0-rc2 and Mathlib rev v4.35.0-rc2. [READ]

Toolchain / versions:
- lean-toolchain must read `leanprover/lean4:<version>`, not older than `minimum` in toolchains.json, currently v4.35.0-rc2. [READ] https://raw.githubusercontent.com/PalomarRegistry/PalomarSubmission/main/toolchains.json
- With Mathlib, the project toolchain must equal Mathlib's own lean-toolchain at the resolved revision exactly (patch and rc suffix). [READ] CONTRIBUTING.md 2.1
- No upper bound stated. v4.36.0 is above the minimum. [INFERRED]

Lake/manifest: exactly one of lakefile.toml/.lean (<= 1 MiB). Manifest mandatory for lakefile.lean, strongly recommended for toml. Git dependencies: credential-free https://github.com/owner/repo URLs pinned to full 40-hex SHA. No submodules, no Git LFS pointers, no committed compiled output (.olean etc.). Checkout <= 500 MiB. [READ] CONTRIBUTING.md 2.1, 2.4, 2

Source rules [READ]: every regular .lean file uses `module`, <= 10,000 physical lines (lakefile.lean exempt from the header only); module docs go after `module`; .lean symlinks refused; porting needs `public import`, public declarations, exposed definition bodies; external pinned Git deps exempt from the line cap.

Challenge rules [READ]: distinct dotted module names; files inside the project; <= 1,000 lines and 100 KiB hard (warning above 300 lines / 32 KiB); transitive imports only Lean core, Mathlib at canonical revision, Tau Ceti, CSLib (last two flagged as "qualified dependencies"); no other project source; a previously registered Palomar project is not importable. Prefer theorems to new definitions; document every definition; state every headline claim; no hidden hypotheses. Deliberate `sorry` allowed. Inline Verso display only if exactly one compared declaration and <= 100 lines / 32 KiB; otherwise a separate rendered page.

Solution rules [READ]: same names and types as the compared Challenge declarations; may depend on any pinned public Git dependency or contained path dependency; no sorryAx, Lean.ofReduceBool (so no native_decide), custom axioms; plain `decide` is fine.

comparator.json [READ policy 2.3; template]: one JSON object, <= 1 MiB.

| key | status | meaning |
|---|---|---|
| challenge_module | required | dotted module name, e.g. "Challenge" |
| solution_module | required | dotted module name |
| theorem_names | required, nonempty | fully qualified names to compare |
| permitted_axioms | required | subset of propext, Quot.sound, Classical.choice |
| definition_names | optional (default []) | defs left abstract in Challenge, valued in Solution (editorial scrutiny) |
| enable_nanoda | optional | ignored; Palomar always enables nanoda; `external_kernels` is rejected (template script comment) |

One submission = one comparator config = one entry.

formalization.yaml (mathlib-initiative v0.4 base; Palomar accepts unknown fields; UTF-8, <= 256 KiB, one mapping, no duplicate keys or merge keys; `version: v0.4` expected) [READ CONTRIBUTING.md sec 3; template formalization.yaml]:

| field | required by Palomar? | meaning / constraint |
|---|---|---|
| version | expected | "v0.4" |
| project.name | yes | <= 300 chars; entry title |
| project.description | yes | <= 10,000 chars; the public abstract |
| project.authors | yes | nonempty list of human names; no AI/agent/tool |
| project.license | yes | SPDX id exactly equal to the one detected in root LICENSE |
| project.responsible_maintainers | yes | nonempty list of humans |
| repository.substantive_formalization.{id,revision} | only for a thin wrapper | owner/repo and 40-hex SHA; omit otherwise |
| classification.arxiv | yes | 1-8 codes from Palomar's taxonomy snapshot (template comment says 1-2) |
| classification.msc2020 | optional, <= 8 | 5-character codes from the snapshot |
| sources[] | yes, nonempty | title and relationship (formalizes / adapts / independently-proves / background / other) required; optional type (paper, book, web discussion, folklore, original-proof, other), authors, contributors[{name, role}], id, location, note, license, author_endorsement |
| origin rule | yes | original: an entry of type original-proof with relationship other, all others background/other; otherwise source-based: some entry formalizes/adapts/independently-proves |
| related_formalizations[] | optional | id, relationship (builds-on, adapts, independent, supersedes, other), note |
| status.scope, sorry_count, sorry_in_definitions, axioms, main_results | in template/upstream; not stated as mechanical | what is and is not formalized; counts exclude Challenge sorries |
| automation.methods[] | yes, nonempty | method (manual/copilot/agent/autonomous/other), models, framework, tool_setup, cost{wall_time, spend_usd, hardware}, prompting_notes |
| automation.spend_usd, notes | optional | |
| fidelity.divergences | optional | known divergences from the source |
| review.status | yes | e.g. unchecked, agent-reviewed, self-assessed, peer-reviewed, author-verified; the review done before submission |
| review.reviewers, review.notes | optional | |
| alignment.namespace, alignment.statements[] | optional | source / lean / module / status / note |
| acknowledgements | optional | |

ORCID ids are optional (structured `orcid` field; existence is checked). Legacy singular aliases are accepted.

Narrative account (location free: yaml, Challenge docs/docstrings, README) must cover: plain-language account of every compared theorem; mismatches, extra assumptions, limits; sources; what is original/adapted/proved/missing; relation to earlier formalizations; authorship and production process including AI and human review; the licence. [READ CONTRIBUTING.md 3.4]

## 4 Authorship, AI and licensing rules

- AI allowed: a formalization may be written by a person, by AI, or a mixture. Models, framework and tooling must be recorded (or `manual`). [READ] /about
- Authors and maintainers are human only; credit AI in the automation fields and narrative (the policy cites the Leiden Declaration principle). Enforced editorially. [READ] CONTRIBUTING.md 3. Note the Anthropic example lists "Claude" as an author in its yaml, which seems to contradict this rule; it may predate the rule. [INFERRED]
- Submitter must be a responsible author/maintainer or have approval from one; write access, fork, org membership do not count; a false answer is a material misrepresentation. [READ] sec 4
- Paper / informal write-up: no separate paper is mandatory, but an informal account is needed in substance, in any eligible location. An optional informal proof must describe the Lean proof actually present. [READ] sec 3.4
- Novelty/priority: Palomar certifies neither. Do not claim novelty without a credible literature search; say "unknown" otherwise. Mandatory research-interest floor: could warrant a paper or serious note, and an identifiable research area and kind of mathematician; failing it means rejection. Not indexed: trivial results, tailor-made definitions, purported solutions of famous open problems without a careful comparison, literature account and honest gap statement, lightly repackaged work. [READ] sec 1, 3.4, 7; /about
- Licence: exactly one root file named LICENSE/LICENCE/COPYING/UNLICENSE/OFL (optionally .md/.markdown/.txt), non-empty UTF-8, <= 1 MiB, detected as exactly one standard SPDX id equal to project.license. Apache-2.0 is fine (the template uses it). Registry data is CC0 (the record only); ownership of the licence is not verified. On registering, Palomar makes public forks of the repo and all pinned Git dependencies and may quote the metadata. [READ] sec 2.5, 8; /llms.txt
- The review is a filter and "does not accept, approve, or endorse"; the registry is not a certificate of novelty. [READ] /about

## 5 The worked example: anthropics/formal-math

Repo root: .github, .gitignore, 3sum-apsp, eth, vp-vnp, zeta23, LICENSE (Apache-2.0), README.md. [READ] https://api.github.com/repos/anthropics/formal-math/contents/
The README says each folder is a Lake project laid out like the Palomar template, submitted with the folder as "selected project"; Palomar reads the repo-root LICENSE. CI runs comparator with nanoda and landrun and expects the text "Your solution is okay!". [READ] https://raw.githubusercontent.com/anthropics/formal-math/main/README.md

zeta23/ files: Challenge.lean (13 KB, 231 lines), Challenge/ (dir), ChallengeDeps.lean (6 KB) + ChallengeDeps/, Solution.lean (7 KB) + Solution/, Zeta23.lean + Zeta23/ (the proof library, in the same folder), comparator.json, comparator-xiprime.json (second config, not submitted), formalization.yaml (14 KB), lake-manifest.json, lakefile.toml, lean-toolchain (v4.33.0-rc2), LICENSE, NOTICE, README.md (27 KB), AUDIT.md (25 KB), Gemfile(.lock), docbuild/, scripts/, test/, .gitignore. [READ] .../contents/zeta23
- lakefile.toml: one [[require]] mathlib (git url, rev = full SHA); [[lean_lib]] entries Zeta23 (proof), ChallengeDeps, Challenge, Solution; defaultTargets lists them. [READ]
- Challenge.lean: Apache header, long doc comment, `import Mathlib` (no `module` line, so it predates the module rule), 17 theorems with `sorry`; definitions inlined in the file (also kept in ChallengeDeps). Solution.lean proves the same 17 statements by delegating to the Zeta23 library. [READ] raw Challenge.lean / Solution.lean
- comparator.json keys: challenge_module, solution_module, theorem_names (17 names), definition_names (empty), permitted_axioms (the three), enable_nanoda true. [READ]
- formalization.yaml top-level keys (read in full to the automation section): version; project{name, description, authors, license, responsible_maintainers}; classification{arxiv [one code], msc2020 [three codes]}; sources[{title, authors, id "arXiv:...", type paper, location, relationship formalizes, note, author_endorsement participated}]; related_formalizations[{id URL, relationship adapts, note}]; status{scope, sorry_count 0, sorry_in_definitions 0, axioms [three], main_results[{declaration, file, sorry_count, axioms, comparator_config, literature_dependencies}]}; automation{methods[{method autonomous, models [Claude], framework n/a, tool_setup, cost{wall_time, spend_usd, hardware}, prompting_notes}], spend_usd, notes}; then fidelity, review, alignment, acknowledgements as in the template. Authors list "Claude"; maintainer a human. A `# yaml-language-server: $schema=...` first line. [READ] https://raw.githubusercontent.com/anthropics/formal-math/main/zeta23/formalization.yaml
- eth/ (smaller): Challenge.lean (1.9 KB) imports only `MainResults` (11.5 KB, imports Mathlib alone, holds all definitions and the two propositions); two `sorry` theorems; Solution.lean imports the proof sub-libraries under proof/ (many [[lean_lib]] with srcDir, Mathlib pinned by rev SHA); also paper.pdf, NOTICE, README, scripts. comparator.json lists 2 theorems. No formalization.yaml in the eth listing. [READ] .../contents/eth; raw eth files. Under the current policy this Challenge import structure would break the rule that the Challenge closure contain no project source; the template's Challenge is one self-contained file. Inline definitions. [INFERRED from policy plus examples]
- Module system: the Zeta23 and eth Challenge/Solution files read have no `module` header, so those examples do not satisfy the current rule for new ordinary submissions as written. I did not check every file. [READ + INFERRED]

## 6 Checklist for the described project

Already has (per the description) [INFERRED match to rules]:
- Apache-2.0 licence (accepted SPDX); confirm the repo is public.
- Mathlib-only challenge file; comparator.json accepted by `lake comparator`, also paranoid mode; Lean v4.36.0 is above the minimum v4.35.0-rc2; Mathlib tag equals the toolchain (verify against Mathlib's own lean-toolchain).
- Standard axioms only (confirm no native_decide / ofReduceBool).
- AI-written under human direction: allowed, to be disclosed in automation.methods.

Missing / to do:
- formalization.yaml v0.4 with all fields above: classification (an arXiv math.NT code plus MSC 11xxx codes), sources (original-proof entry if there is no prior paper; the Erdos problem as background/other), human authors and responsible maintainers, status counts, honest review.status (unchecked / agent-reviewed / self-assessed).
- Informal account: plain-language theorem, scope (periodic f, which case), extra assumptions, what is original, human review. Novelty: say "unknown" unless a literature search is documented.
- Challenge self-contained: definitions inlined, imports Mathlib only, <= 1,000 lines / 100 KiB (aim <= 300 lines). Add the `module` header and `public import` as in the template and re-run comparator.
- Run Palomar's full-mode reusable workflow from the repo (not only local comparator).
- Commit and push; commit lake-manifest.json; no .olean, no LFS, no submodules, size <= 500 MiB.

Possible problems:
1. Library of about 3,000 modules: all must start with `module`, be <= 10,000 lines and compile under the module system (public declarations/imports, exposed definition bodies). Even unused or generated files count. If the library were an external pinned public Git dependency, the line cap would not apply, but [INFERRED] it would still have to work with the module system, and it would be forked into PalomarArchive on registering. The thin-wrapper route (repository.substantive_formalization) does not escape this: the substantive repo gets the same module/line checks. [READ rules; INFERRED consequence]
2. Mathlib-only statement: any project-specific notion (periodic f, the sum of f(n)/n) must be written in Mathlib terms or inlined in Challenge.
3. Research-interest floor and famous-open-problem screening: the Erdos case must be compared carefully with the standard conjecture, with an honest scope/gap statement, or the review may reject; resubmission then waits.
4. Authorship: do not list Claude or any agent in authors/maintainers (unlike the Anthropic example). The human submitter must truthfully declare being a responsible author or maintainer.
5. Permanence: registration cannot be withdrawn; metadata and any approval note are public.
6. Resources: Palomar's default runner profile is named 16x32 and has OOM/timeout failure modes; a 3,000-module build in their sandbox must fit. [READ name; INFERRED relevance]
7. Pre-launch wording in the policy; rules are changing (the module rule is recent), so re-read the policy before submitting.

## 7 Related lists

- formal-conjectures (google-deepmind): short proofs (about 25-50 lines at most) may be included; longer proofs go in your own repo and are linked with the `formal_proof` attribute; for formal proofs of research problems that attribute "should always link to" a Palomar entry. Mark a problem solved by changing its category tag and adding `@[formal_proof using <kind> at "<url>"]`; Google CLA and an issue first. [READ] https://raw.githubusercontent.com/google-deepmind/formal-conjectures/main/CONTRIBUTING.md
- Lean Pool: the about page suggests it for AI-driven updating of a project as Lean/Mathlib move. [READ] /about (link not opened)
- Reservoir lists the template package (search result only). [SNIPPET] https://reservoir.lean-lang.org/@PalomarRegistry/PalomarTemplate

## 8 Sources and search log

Sources (all fetched 2026-11-24; no page dates shown):
- https://palomar-registry.org/ , /about , /statement , /how-to-submit , /llms.txt
- https://github.com/PalomarRegistry/PalomarPolicy (CONTRIBUTING.md, docs/specification.md, grepped for withdrawal/cooldown)
- https://github.com/PalomarRegistry/PalomarTemplate (API listing; raw comparator.json, Challenge.lean, lean-toolchain, lakefile.toml, formalization.yaml, scripts/verify-comparator.sh)
- https://raw.githubusercontent.com/PalomarRegistry/PalomarSubmission/main/toolchains.json
- https://submit.palomar-registry.org/llms.txt
- https://github.com/anthropics/formal-math (README; zeta23 and eth listings and files)
- https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/main/README.md
- https://raw.githubusercontent.com/google-deepmind/formal-conjectures/main/CONTRIBUTING.md

Not opened or not found: privacy page text, the formalization.yaml JSON schema, PalomarSubmission README (workflow input labels), PalomarPolicy rubric.json and prompts, any registered entry, Zulip discussions, the Lean Pool page.
Text addressed to agents: both llms.txt files tell agents not to drive the browser form/OAuth and to confirm with the user before submitting. I did not act on it; no login, post, or submission was made.

Search log: WebSearch x1 ("Palomar registry of formal proofs Lean comparator formalization.yaml submission"); WebFetch x2 (palomar-registry.org home; GitHub API root listing of formal-math); about 30 curl fetches of the pages and files above.
