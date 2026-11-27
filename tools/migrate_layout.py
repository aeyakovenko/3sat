#!/usr/bin/env python3
"""Move the journal from its flat layout into notes/, lean/ and audits/.

Run from the repository root.

    python3 tools/migrate_layout.py             do whatever is still to do
    python3 tools/migrate_layout.py --dry-run   report what would change, change nothing
    python3 tools/migrate_layout.py --no-split  leave README.md in one piece

The script is idempotent: on a tree that is already in the layout it changes nothing.
Run it again whenever flat-layout material arrives, for example after merging or
cherry-picking commits made before the move, or after a file was added at the root.
All steps are computed first; the working tree is touched only at the end.

When such a merge conflicts in README.md, take the flat side
(`git checkout --theirs README.md && git add README.md`) and run the script: it
splits that README.md again, regenerates RESULTS.md and JOURNAL.md from it, and keeps
the front page of HEAD.

1. Move.  Every tracked file at the root goes to the directory that check.py assigns
   to its suffix (`git mv`): *.md to notes/, *.lean to lean/, and *.py, *.cpp, *.hpp,
   *.sh, *.gz, *.patch to audits/.  README.md, RESULTS.md, JOURNAL.md,
   research-steering.md and files with any other suffix stay.  Untracked files are
   left alone unless --include-untracked is given.
2. Links.  A relative inline link in a Markdown file is left alone if it resolves from
   where the file is now.  Otherwise it is read as a flat-layout link and rewritten to
   the relative path of the same target in the layout.  `#fragments` are kept.
   External URLs, pure `#fragment` links and targets that resolve under neither
   reading are not touched.
3. Shell scripts.  A bare file name in a shell script that names a file of another
   layout directory gets the relative path to that file.  Python and C++ sources are
   never edited.
4. README.  If README.md still has the sections of the flat layout it is split:
   RESULTS.md gets everything from the first `## ` heading up to
   `## Earlier research and conditional tests`; JOURNAL.md gets that section and the
   ones up to `## Reproducing the checks`; the command list of the latter is dropped
   because tools/check.py runs every file; prose that follows the list and is not
   about checking is appended to RESULTS.md.  README.md becomes the front page: the
   file given with --front-page, else the README.md of HEAD if that one is already a
   front page, else the built-in page.  Links to `README.md#heading` are pointed at
   the file that now has the heading.
5. Unlinked notes.  The last section of JOURNAL.md, `## Notes not linked from the
   indexes`, is regenerated: the notes that no other Markdown file links to.

Review the result with `git status` and `git diff`, run `python3 tools/check.py`, and
commit with `git add -A`.
"""
import argparse
import json
import os
import posixpath
import re
import subprocess
import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import check
from check import ROOT

INDEX_FILES = ('README.md', 'RESULTS.md', 'JOURNAL.md')
JOURNAL_START = '## Earlier research and conditional tests'
JOURNAL_SECTIONS = [JOURNAL_START, '## Research journal', '## Literature checks']
REPRODUCING = '## Reproducing the checks'
UNLINKED_HEADING = '## Notes not linked from the indexes'
UNLINKED_INTRO = ('No other file in the repository links to the notes below. '
                  '`tools/migrate_layout.py` regenerates this list.')
UNLINKED_NONE = 'Every note is linked from at least one other file.'

# Prose of the old `## Reproducing the checks` section that the built-in front page
# carries over.  The last sentence of the introduction, "Run from the repository
# root.", is replaced there by the convention for commands quoted in notes.
REPRODUCING_INTRO = (
    'Use Lean 4.19.0 with its bundled Std library and Python 3.11 or later. The finite '
    'permanent-grid and matching experiments use SymPy. The independent singleton '
    'optimization check uses NumPy and SciPy.')
REPRODUCING_INTRO_END = ' Run from the repository root.'
KERNEL_SCOPE = (
    'The Lean files state the parts checked by the kernel. The asymptotic constructions, '
    'reductions, and complexity estimates are manuscript arguments.')

FRONT_PAGE = '''{title}

<!-- STATUS-SUMMARY -->

## Layout

Start with [RESULTS.md](RESULTS.md), the index of results. [JOURNAL.md](JOURNAL.md) has the earlier research and conditional tests, the research journal, the literature checks and a list of the notes that no other file links to. [research-steering.md](research-steering.md) is the steering log of the project.

| Path | Files | Contents |
| --- | ---: | --- |
| [notes/](notes) | {notes} | One Markdown note per result or attempt. Notes link to each other and to the files that check them. |
| [lean/](lean) | {lean} | Lean 4 files, each run on its own as `lean File.lean`. |
| [audits/](audits) | {audits} | {audit_kinds}. They share one directory because they import, include and open one another by bare file name. |
| [upstream-checks/](upstream-checks) | {upstream} | Lean files that import Mathlib, which the pinned toolchain alone does not provide. |
| [tools/](tools) | {tools} | [check.py](tools/check.py), its baseline [known-failures.json](tools/known-failures.json), and [migrate_layout.py](tools/migrate_layout.py), which produced this layout from the earlier flat one. |

`lean-toolchain` and `.gitignore` stay at the root. The file counts are those of the commit that introduced this layout.

`python3 tools/migrate_layout.py` is idempotent. Run it again when a file lands at the root or when a branch made before the move is merged: it moves the new files, rewrites flat-layout links, and regenerates the list of unlinked notes in `JOURNAL.md`.

## Checking

Run the checker from the repository root:

```sh
python3 tools/check.py
```

It checks three things and prints a short summary.

1. Layout. No tracked file at the root belongs in `notes/`, `lean/` or `audits/`.
2. Links. Every relative link in every tracked Markdown file resolves to a tracked file or directory, and every `#anchor` on a Markdown target is a heading of that file.
3. Run. Every tracked Lean file is run as `lean File.lean` and every Python file in `audits/` as `python3 -B file.py`, each from its own directory, in parallel and under a time limit.

The results are compared with [tools/known-failures.json](tools/known-failures.json). The exit status is 0 when nothing regressed. It is 1 when a file that is not listed there fails, when a listed file fails without the output recorded for its category, when a link that is not listed there is broken, or when the layout check fails. Listed failures that now pass are reported and do not change the exit status.

| Option | Effect |
| --- | --- |
| `--skip-run` | Check the layout and the links only. This takes about a second. |
| `--only-links` | Check the links only. |
| `--jobs N` | Run `N` files at once. The default is 20, or the number of processors if that is smaller. |
| `--lean PATH` | Use this Lean binary. The default is `$LEAN`, then the elan toolchain named in `lean-toolchain`, then `lean` on `PATH`. |
| `--lean-timeout S`, `--py-timeout S` | Time limit for one file in seconds. The default is 300. |
| `FILE ...` | Run only the named Lean or Python files, for example `python3 tools/check.py lean/Adaptive.lean`. |

### Tool versions

{reproducing_intro}

The baseline in `tools/known-failures.json` was recorded on {recorded_date} with Lean {recorded_lean}, Python {recorded_python}, NumPy {recorded_numpy}, SciPy {recorded_scipy}, SymPy {recorded_sympy} and {recorded_cxx} installed as `c++`, which five audits use to compile C++20 sources.

{kernel_scope}

### Known failures

Of the {run_total} files that are run, {run_passing} pass and {run_failing} fail for a recorded reason.

| Category | Files | Reason |
| --- | ---: | --- |
{categories}

To record another known failure, add a line `"path": "category"` to the `failures` object of that file.

A file of the category `lean-sibling-import` checks once its import is compiled, for example from `lean/`:

```sh
lean -o /tmp/NestedClauseCycle.olean NestedClauseCycle.lean
LEAN_PATH=/tmp lean EightTerminalCycle.lean
```

The same baseline lists {known_links} relative link targets that do not resolve.

| Reason | Links |
| --- | ---: |
{link_rows}

### Commands quoted in notes

Notes quote commands with bare file names, such as `python3 some_audit.py` or `lean SomeFile.lean`. Run Python, C++ and shell commands from `audits/` and Lean commands from `lean/`.
'''


def fail(message):
    sys.exit(f'migrate_layout.py: {message}')


def git(*arguments):
    return subprocess.run(['git', '-C', str(ROOT), *arguments],
                          capture_output=True, text=True, check=True).stdout


def plural(count, singular, plural_form=None):
    return f'{count} {singular if count == 1 else plural_form or singular + "s"}'


class Plan:
    """The tree as it will be: layout path -> where the file is now, plus new contents."""

    def __init__(self, include_untracked):
        unmerged = sorted({line.split('\t', 1)[1] for line in git('ls-files', '-u', '-z').split('\0') if line})
        if unmerged:
            fail('resolve the merge conflicts first: ' + ', '.join(unmerged[:10])
                 + (f' and {len(unmerged) - 10} more' if len(unmerged) > 10 else ''))
        tracked = check.tracked_files()
        loose = [name for name in git('ls-files', '-z', '--others', '--exclude-standard').split('\0')
                 if name and check.destination(name) != name]
        self.untracked = set(loose) if include_untracked else set()
        self.left_alone = [] if include_untracked else loose
        self.source = {}        # layout path -> path on disk now (None: created by this run)
        self.text = {}          # layout path -> content to write
        self.warnings = []
        for name in tracked + sorted(self.untracked):
            if not os.path.lexists(ROOT / name):
                self.warnings.append(f'{name} is tracked but missing from the working tree; skipped')
                continue
            new = check.destination(name)
            if new in self.source:
                fail(f'{name} and {self.source[new]} would both be {new}; resolve this by hand')
            self.source[new] = name
        for new, old in self.source.items():
            if new != old and os.path.lexists(ROOT / new):
                fail(f'cannot move {old}: {new} exists and is not tracked')
        self.layout_path = {old: new for new, old in self.source.items()}
        self.directories = check.directories_of(self.source)

    def moves(self):
        return sorted((old, new) for new, old in self.source.items() if old and old != new)

    def exists(self, path):
        return path in self.source or path in self.directories

    def read(self, path):
        if path in self.text:
            return self.text[path]
        return check.read_text(self.source[path])

    def write(self, path, text):
        if path not in self.source:
            self.source[path] = None
        if self.source[path] is None or text != check.read_text(self.source[path]):
            self.text[path] = text
        else:
            self.text.pop(path, None)

    def markdown(self):
        return sorted(path for path in self.source if path.endswith('.md'))

    def tracked(self, prefix='', suffix=''):
        return [path for path, old in self.source.items()
                if old not in self.untracked and path.startswith(prefix) and path.endswith(suffix)]


# ---------------------------------------------------------------- step 2: links

def flat_directory(plan, path):
    """The directory that flat-layout links of the file at `path` are relative to."""
    old = plan.source[path]
    if old is not None and old != path:
        return posixpath.dirname(old)
    name = path.partition('/')[2]
    if name and check.destination(name) == path:
        return ''
    return posixpath.dirname(path)


def flat_reading(plan, base, name):
    """Layout path of what `name`, relative to `base` in the flat layout, refers to, or None."""
    flat = posixpath.normpath(posixpath.join(base, name))
    if flat == '..' or flat.startswith('../'):
        return None
    if flat == '.':
        return ''
    there = plan.layout_path.get(flat) or check.destination(flat)
    return there if plan.exists(there) else None


def new_target(plan, path, target):
    """The target to write instead of `target` in the file at `path`; None to keep it."""
    relative, _ = check.split_target(target)
    if not relative or relative.startswith('/'):
        return None
    here = posixpath.dirname(path)
    moved = plan.source[path] != path
    if not moved and plan.exists(posixpath.normpath(posixpath.join(here, relative))):
        return None
    there = flat_reading(plan, flat_directory(plan, path), relative)
    if there is None:
        return None
    new = posixpath.relpath(there or '.', here or '.')
    if relative.endswith('/') and not new.endswith('/'):
        new += '/'
    new += target[len(relative):]
    return None if new == target else new


def rewrite_links(plan):
    files = links = 0
    for path in plan.markdown():
        try:
            text = plan.read(path)
        except UnicodeDecodeError:
            plan.warnings.append(f'{path} is not UTF-8; its links were not examined')
            continue
        count = 0

        def replace(match):
            nonlocal count
            new = new_target(plan, path, match.group(1))
            if new is None:
                return match.group(0)
            count += 1
            return f']({new})'

        new_text = check.LINK.sub(replace, text)
        if count:
            plan.write(path, new_text)
            files += 1
            links += count
    return files, links


# ---------------------------------------------------------------- step 3: shell scripts

BARE_NAME = re.compile(r'(?<![\w./$-])[A-Za-z0-9_][A-Za-z0-9_-]*(?:\.[A-Za-z0-9_-]+)+(?![\w/-])')


def fix_shell_scripts(plan):
    fixed = []
    for path in sorted(name for name in plan.source if name.endswith('.sh')):
        here = posixpath.dirname(path)
        base = flat_directory(plan, path)
        moved = plan.source[path] != path

        def replace(match):
            name = match.group(0)
            if not moved and plan.exists(posixpath.normpath(posixpath.join(here, name))):
                return name
            there = flat_reading(plan, base, name)
            if not there or there not in plan.source:
                return name
            new = posixpath.relpath(there, here or '.')
            if new != name:
                fixed.append((path, name, new))
            return new

        try:
            text = plan.read(path)
        except UnicodeDecodeError:
            plan.warnings.append(f'{path} is not UTF-8; it was not examined')
            continue
        new_text = BARE_NAME.sub(replace, text)
        if new_text != text:
            plan.write(path, new_text)
    return fixed


# ---------------------------------------------------------------- step 4: README

def heading_index(lines, heading):
    hits = [index for index, line in enumerate(lines) if line.rstrip() == heading]
    if len(hits) > 1:
        fail(f'the heading {heading!r} occurs {len(hits)} times in one file')
    return hits[0] if hits else None


def block(lines):
    return '\n'.join(lines).strip('\n')


def is_front_page(text):
    lines = text.split('\n')
    return heading_index(lines, JOURNAL_START) is None and heading_index(lines, REPRODUCING) is None


def built_in_front_page(plan, title):
    try:
        described = json.loads(check.KNOWN_FAILURES.read_text())
        known, recorded = described['failures'], described['recorded']
    except (OSError, ValueError, KeyError) as error:
        fail(f'the built-in front page needs tools/known-failures.json ({error!r})')
    count = lambda prefix, suffix='': len(plan.tracked(prefix, suffix))
    kinds = [plural(count('audits/', '.py'), 'Python audit or experiment', 'Python audits and experiments'),
             plural(count('audits/', '.cpp'), 'C++ program') + ' with '
             + plural(count('audits/', '.hpp'), 'header'),
             plural(count('audits/', '.sh'), 'shell replay script'),
             plural(count('audits/', '.gz'), 'gzip-compressed JSON data file'),
             plural(count('audits/', '.patch'), 'patch file')]
    targets = check.run_targets(plan.tracked())
    listed = [name for name in targets if name in known]
    rows = []
    for name, entry in described['categories'].items():
        rows.append(f"| `{name}` | {sum(1 for target in listed if known[target] == name)} "
                    f"| {entry['reason']} |")
    reasons = {}
    for entry in described['broken_links']:
        reasons[entry['reason']] = reasons.get(entry['reason'], 0) + 1
    link_rows = [f'| {reason} | {number} |' for reason, number in reasons.items()]
    return FRONT_PAGE.format(
        title=title, notes=count('notes/', '.md'), lean=count('lean/', '.lean'),
        audits=count('audits/'), audit_kinds=', '.join(kinds[:-1]) + ' and ' + kinds[-1],
        upstream=count('upstream-checks/'), tools=count('tools/'),
        reproducing_intro=REPRODUCING_INTRO, kernel_scope=KERNEL_SCOPE,
        run_total=len(targets), run_passing=len(targets) - len(listed), run_failing=len(listed),
        categories='\n'.join(rows), known_links=len(described['broken_links']),
        link_rows='\n'.join(link_rows), **{'recorded_' + key.replace('+', 'x'): value
                                           for key, value in recorded.items()})


def split_readme(plan, front_page_file):
    """Split a flat-layout README.md; return a description, or None if it is already split."""
    if 'README.md' not in plan.source:
        return None
    lines = plan.read('README.md').split('\n')
    journal, reproducing = heading_index(lines, JOURNAL_START), heading_index(lines, REPRODUCING)
    if journal is None and reproducing is None:
        return None
    if journal is None or reproducing is None or reproducing < journal:
        fail(f'README.md should have {JOURNAL_START!r} and after it {REPRODUCING!r}, or neither')
    title = next((index for index, line in enumerate(lines) if line.startswith('# ')), None)
    first = next((index for index, line in enumerate(lines) if line.startswith('## ')), None)
    if title is None or first is None or not title < first <= journal:
        fail('README.md should start with a `# ` title followed by `## ` sections')
    sections = [line.rstrip() for line in lines[journal:reproducing] if line.startswith('## ')]
    if sections != JOURNAL_SECTIONS:
        plan.warnings.append('JOURNAL.md got the sections ' + ', '.join(sections)
                             + '; this script expected ' + ', '.join(JOURNAL_SECTIONS))

    # The section that is dropped: introduction, one fenced command list, closing prose.
    fences = [index for index in range(reproducing + 1, len(lines)) if lines[index].startswith('```')]
    if len(fences) != 2:
        fail(f'{REPRODUCING!r} should contain exactly one fenced command list')
    introduction = block(lines[reproducing + 1:fences[0]])
    if introduction != REPRODUCING_INTRO + REPRODUCING_INTRO_END:
        plan.warnings.append(f'the introduction of {REPRODUCING!r} changed; compare it with the '
                             'Checking section of README.md:\n    ' + introduction)
    commands = [line for line in lines[fences[0] + 1:fences[1]] if line.strip()]
    run = set(check.run_targets(plan.source))
    uncovered = [line for line in commands
                 if not (match := re.fullmatch(r'(lean|python3) ([\w.-]+)', line.strip()))
                 or check.destination(match.group(2)) not in run]
    if uncovered:
        plan.warnings.append(f'{len(uncovered)} dropped commands are not run by tools/check.py:\n    '
                             + '\n    '.join(uncovered))
    closing = [part for part in re.split(r'\n{2,}', block(lines[fences[1] + 1:])) if part.strip()]
    if KERNEL_SCOPE not in closing:
        plan.warnings.append(f'{REPRODUCING!r} no longer ends with the sentence on what Lean checks; '
                             'compare it with the Checking section of README.md')
    unfiled = [part for part in closing if part != KERNEL_SCOPE]
    preamble = block(lines[title + 1:first])
    if preamble:
        plan.warnings.append('text between the title and the first section of README.md was put at '
                             'the top of RESULTS.md')

    results = [part for part in (preamble, block(lines[first:journal]), *unfiled) if part]
    if front_page_file:
        front, origin = Path(front_page_file).read_text(), front_page_file
    else:
        try:
            front, origin = git('show', 'HEAD:README.md'), 'README.md of HEAD'
        except subprocess.CalledProcessError:
            front = ''
        if not front or not is_front_page(front):
            front, origin = built_in_front_page(plan, lines[title].rstrip()), 'built-in page'
    plan.write('RESULTS.md', '# Results index\n\n' + '\n\n'.join(results) + '\n')
    plan.write('JOURNAL.md', '# Research journal\n\n' + block(lines[journal:reproducing]) + '\n')
    plan.write('README.md', front)
    return (f'README.md split: RESULTS.md gets lines {first + 1}-{journal} and '
            f'{plural(len(unfiled), "closing paragraph")}, JOURNAL.md lines {journal + 1}-{reproducing}; '
            f'{plural(len(commands), "listed command")} dropped; front page from the {origin}')


def retarget_index_anchors(plan):
    """Point `#fragment` links at whichever index file now has the heading."""
    present = [name for name in INDEX_FILES if name in plan.source]
    anchors = {name: check.heading_anchors(plan.read(name)) for name in present}
    retargeted = []
    for path in plan.markdown():
        here = posixpath.dirname(path)
        try:
            text = plan.read(path)
        except UnicodeDecodeError:
            continue

        def replace(match):
            target = match.group(1)
            relative, fragment = check.split_target(target)
            if relative is None or not fragment:
                return match.group(0)
            if relative == '':
                if not target.startswith('#'):
                    return match.group(0)
                resolved = path
            else:
                resolved = posixpath.normpath(posixpath.join(here, relative))
            if resolved not in anchors or fragment in anchors[resolved]:
                return match.group(0)
            for other in present:
                if other != resolved and fragment in anchors[other]:
                    new = f'{posixpath.relpath(other, here or ".")}#{fragment}'
                    retargeted.append((path, target, new))
                    return f']({new})'
            return match.group(0)

        new_text = check.LINK.sub(replace, text)
        if new_text != text:
            plan.write(path, new_text)
    return retargeted


# ---------------------------------------------------------------- step 5: unlinked notes

def list_unlinked_notes(plan):
    lines = plan.read('JOURNAL.md').rstrip('\n').split('\n')
    start = heading_index(lines, UNLINKED_HEADING)
    if start is None:
        before, after = lines, []
    else:
        end = next((index for index in range(start + 1, len(lines)) if lines[index].startswith('## ')),
                   len(lines))
        before, after = lines[:start], lines[end:]
    rest = block(before) + ('\n\n' + block(after) if after else '')
    report = check.scan_links(plan.tracked(), lambda path: rest if path == 'JOURNAL.md' else plan.read(path))
    notes = check.unlinked_notes(plan.tracked(), report['edges'])
    entries = []
    for note in notes:
        title = re.search(r'^# +(.+?)[ \t]*$', plan.read(note), re.M)
        label = title.group(1) if title else posixpath.basename(note)
        label = re.sub(r'[][]', lambda bracket: '\\' + bracket.group(0), label)
        entries.append(f'- [{label}]({note})')
    section = [UNLINKED_HEADING, '', UNLINKED_INTRO, '', *entries] if entries else \
              [UNLINKED_HEADING, '', UNLINKED_NONE]
    plan.write('JOURNAL.md', block(before) + '\n\n' + '\n'.join(section) + '\n'
               + ('\n' + block(after) + '\n' if after else ''))
    return notes


# ---------------------------------------------------------------- applying the plan

def apply(plan):
    moves = plan.moves()
    for directory in sorted({posixpath.dirname(new) for _, new in moves}):
        os.makedirs(ROOT / directory, exist_ok=True)
        tracked = [old for old, new in moves
                   if posixpath.dirname(new) == directory and old not in plan.untracked]
        for start in range(0, len(tracked), 200):
            git('mv', '--', *tracked[start:start + 200], directory + '/')
    for old, new in moves:
        if old in plan.untracked:
            os.rename(ROOT / old, ROOT / new)
    created = []
    for path, text in sorted(plan.text.items()):
        if plan.source[path] is None:
            created.append(path)
        (ROOT / path).write_bytes(text.encode('utf-8'))
    if created:
        git('add', '--intent-to-add', '--', *created)


def main():
    parser = argparse.ArgumentParser(
        description='Move flat-layout files into notes/, lean/ and audits/, rewrite the relative '
                    'links, and split README.md. Idempotent; run from the repository root.')
    parser.add_argument('--dry-run', action='store_true', help='report what would change; change nothing')
    parser.add_argument('--no-split', action='store_true',
                        help='do not split README.md and do not touch RESULTS.md or JOURNAL.md')
    parser.add_argument('--include-untracked', action='store_true',
                        help='also move untracked, unignored files at the root and rewrite their links')
    parser.add_argument('--front-page', metavar='FILE',
                        help='when README.md is split, use this file as the new README.md')
    args = parser.parse_args()
    if Path.cwd().resolve() != ROOT:
        parser.error(f'run this from the repository root: cd {ROOT} && python3 tools/migrate_layout.py')

    plan = Plan(args.include_untracked)
    moves = plan.moves()
    files, links = rewrite_links(plan)
    scripts = fix_shell_scripts(plan)
    split = None if args.no_split else split_readme(plan, args.front_page)
    retargeted = [] if args.no_split else retarget_index_anchors(plan)
    unlinked = None
    if not args.no_split and 'JOURNAL.md' in plan.source:
        unlinked = list_unlinked_notes(plan)
    report = check.scan_links(plan.tracked(), plan.read)

    per_directory = {}
    for _, new in moves:
        per_directory[posixpath.dirname(new)] = per_directory.get(posixpath.dirname(new), 0) + 1
    print(f'move:    {plural(len(moves), "file")}'
          + ''.join(f', {count} to {directory}/' for directory, count in sorted(per_directory.items())))
    print(f'links:   {plural(links, "link")} rewritten in {plural(files, "Markdown file")}')
    print(f'scripts: {plural(len(scripts), "file name")} given a relative path')
    for path, old, new in scripts:
        print(f'    {path}: {old} -> {new}')
    if split:
        print(f'readme:  {split}')
    for path, old, new in retargeted:
        print(f'anchor:  {path}: {old} -> {new}')
    if unlinked is not None:
        print(f'journal: {plural(len(unlinked), "note")} listed under {UNLINKED_HEADING!r}')
    print(f"result:  {report['markdown']} Markdown files, {report['occurrences']} relative links to "
          f"files ({len(report['edges'])} distinct source-target pairs), "
          f"{plural(len(report['broken']), 'target')} unresolved")
    for source, target, kind in report['broken']:
        print(f'    unresolved: {source} -> {target}')
    if plan.left_alone:
        print(f'note:    {plural(len(plan.left_alone), "untracked file")} at the root left where '
              f'{"it is" if len(plan.left_alone) == 1 else "they are"} (--include-untracked moves them)')
    for warning in plan.warnings:
        print(f'warning: {warning}')
    changed = sorted(plan.text)
    if args.dry_run:
        print(f'dry run: nothing changed; {plural(len(moves), "move")} and '
              f'{plural(len(changed), "file")} to write')
        return 0
    if not moves and not changed:
        print('nothing to do')
        return 0
    apply(plan)
    print(f'done:    {plural(len(moves), "file")} moved, {plural(len(changed), "file")} written; '
          'review with git status and git diff')
    return 0


if __name__ == '__main__':
    sys.exit(main())
