#!/usr/bin/env python3
"""Check the journal: layout, relative Markdown links, every Lean file and Python audit.

Run from the repository root.

    python3 tools/check.py               layout and link checks, then run every file
    python3 tools/check.py --skip-run    layout and link checks only (about a second)
    python3 tools/check.py --only-links  link check only
    python3 tools/check.py lean/A.lean audits/b_audit.py    run only the named files

Layout.  A tracked file at the repository root that belongs in notes/, lean/ or
audits/ is reported; tools/migrate_layout.py moves such files and fixes their links.

Links.  Every relative inline link `[text](target)` of every tracked Markdown file
must resolve to a tracked file or directory.  A `#fragment` on a Markdown target must
be the anchor of one of its headings.

Run.  Every tracked Lean file is run as `lean File.lean` and every tracked Python
file outside tools/ as `python3 -B file.py`, each with its own directory as working
directory, in parallel and under a time limit.

The results are compared with tools/known-failures.json.  The exit status is
  0  when nothing regressed,
  1  when a file that is not listed there fails, a listed file fails without showing
     the output recorded for its category, a link that is not listed there is broken,
     or the layout check fails,
  2  on a usage or setup error.
Listed failures that now pass, listed links that are not broken any more and listed
files that no longer exist are reported and do not change the exit status.  To record a new known
failure, add `"path": "category"` to the `failures` object of that file.
"""
import argparse
import collections
import concurrent.futures
import json
import os
import posixpath
import re
import shutil
import signal
import subprocess
import sys
import threading
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
KNOWN_FAILURES = ROOT / 'tools' / 'known-failures.json'

# ---------------------------------------------------------------- layout

# Markdown files that stay at the repository root.
ROOT_FILES = frozenset({'README.md', 'RESULTS.md', 'JOURNAL.md', 'research-steering.md'})
# Every other file that would sit at the root goes to a directory chosen by its suffix.
# The audits stay together: they import, include and open each other by bare file name.
DIRECTORY_BY_SUFFIX = {
    '.md': 'notes',
    '.lean': 'lean',
    '.py': 'audits', '.cpp': 'audits', '.hpp': 'audits', '.sh': 'audits',
    '.gz': 'audits', '.patch': 'audits',
}


def destination(path):
    """Where the layout puts the file that the flat layout had at `path`."""
    if '/' in path or path in ROOT_FILES:
        return path
    directory = DIRECTORY_BY_SUFFIX.get(posixpath.splitext(path)[1])
    return f'{directory}/{path}' if directory else path


def tracked_files():
    try:
        out = subprocess.run(['git', '-C', str(ROOT), 'ls-files', '-z'],
                             capture_output=True, text=True, check=True).stdout
    except (OSError, subprocess.CalledProcessError) as error:
        sys.exit(f'check.py: cannot list the tracked files with git: {error}')
    return sorted({name for name in out.split('\0') if name})


def read_text(path):
    return (ROOT / path).read_bytes().decode('utf-8')


# ---------------------------------------------------------------- links

# An inline link or image target.  The journal uses no other link syntax; OTHER_SYNTAX
# finds reference definitions, titled or bracketed targets and HTML links if any appear.
LINK = re.compile(r'\]\(([^)\s]+)\)')
EXTERNAL = re.compile(r'[A-Za-z][A-Za-z0-9+.-]*:|//')
OTHER_SYNTAX = re.compile(
    r'^ {0,3}\[[^\]\n]+\]:[ \t]*\S+'            # [label]: target
    r'|\]\([ \t]*<[^>\n]*>'                      # [text](<target>)
    r'|\]\([^)\s]+[ \t]+["\'][^\n]*?\)'          # [text](target "title")
    r'|<(?:a|img)\b[^>\n]*\b(?:href|src)[ \t]*=[^>\n]*>',   # <a href=...>, <img src=...>
    re.M | re.I)
HEADING = re.compile(r'^ {0,3}#{1,6}[ \t]+(.*?)(?:[ \t]+#+)?[ \t]*$')
FENCE = re.compile(r'^ {0,3}(?:```|~~~)')


def heading_anchors(text):
    """The anchors GitHub gives to the headings of a Markdown text."""
    anchors, seen, fenced = set(), collections.Counter(), False
    for line in text.split('\n'):
        if FENCE.match(line):
            fenced = not fenced
            continue
        match = None if fenced else HEADING.match(line)
        if not match:
            continue
        title = re.sub(r'\[([^\]]*)\]\([^)]*\)', r'\1', match.group(1))
        slug = ''.join(c for c in title.lower() if c.isalnum() or c in ' -_').replace(' ', '-')
        anchors.add(f'{slug}-{seen[slug]}' if seen[slug] else slug)
        seen[slug] += 1
    return anchors


def split_target(target):
    """Split a link target into (path, fragment); path is None for an external link."""
    if EXTERNAL.match(target):
        return None, ''
    path, _, fragment = target.partition('#')
    return path.split('?')[0], fragment


def directories_of(files):
    directories = {''}
    for name in files:
        while '/' in name:
            name = name.rsplit('/', 1)[0]
            directories.add(name)
    return directories


def scan_links(files, read=read_text):
    """Resolve every relative link of the Markdown files among `files`.

    Returns a dict with
      markdown     number of Markdown files read
      occurrences  number of relative links that resolve to a file
      edges        set of (source, target file) pairs among them
      directories  number of relative links that resolve to a directory
      anchors      number of `#fragment`s checked against the headings of their target
      broken       list of (source, target as written, 'missing' or 'anchor')
      other        list of (source, line number, text) in a link syntax that is not checked
    """
    files = set(files)
    directories = directories_of(files)
    anchor_cache = {}
    report = {'markdown': 0, 'occurrences': 0, 'edges': set(), 'directories': 0,
              'anchors': 0, 'broken': [], 'other': []}
    for source in sorted(name for name in files if name.endswith('.md')):
        text = read(source)
        report['markdown'] += 1
        anchor_cache[source] = heading_anchors(text)
        base = posixpath.dirname(source)
        for match in LINK.finditer(text):
            target = match.group(1)
            path, fragment = split_target(target)
            if path is None:
                continue
            if path == '':
                if not target.startswith('#'):
                    continue
                resolved = source
            else:
                if path.startswith('/'):
                    resolved = posixpath.normpath(path.lstrip('/') or '.')
                else:
                    resolved = posixpath.normpath(posixpath.join(base, path))
                if resolved == '.':
                    resolved = ''
                if resolved in files:
                    report['occurrences'] += 1
                    report['edges'].add((source, resolved))
                elif resolved in directories:
                    report['directories'] += 1
                    continue
                else:
                    report['broken'].append((source, target, 'missing'))
                    continue
            if fragment and resolved.endswith('.md'):
                if resolved not in anchor_cache:
                    anchor_cache[resolved] = heading_anchors(read(resolved))
                report['anchors'] += 1
                if fragment not in anchor_cache[resolved]:
                    report['broken'].append((source, target, 'anchor'))
        for match in OTHER_SYNTAX.finditer(text):
            line = text.count('\n', 0, match.start()) + 1
            report['other'].append((source, line, match.group(0)[:80]))
    return report


def unlinked_notes(files, edges):
    """Notes under notes/ that no other Markdown file links to."""
    linked = {target for source, target in edges if source != target}
    return sorted(name for name in files
                  if name.startswith('notes/') and name.endswith('.md') and name not in linked)


# ---------------------------------------------------------------- running files

def run_targets(files):
    return [name for name in files
            if name.endswith(('.lean', '.py')) and not name.startswith('tools/')]


def find_lean(explicit):
    """The Lean binary: --lean, $LEAN, the elan toolchain named by lean-toolchain, then PATH."""
    if explicit:
        return explicit
    if os.environ.get('LEAN'):
        return os.environ['LEAN']
    toolchain = (ROOT / 'lean-toolchain').read_text().strip()
    pinned = (Path.home() / '.elan' / 'toolchains'
              / toolchain.replace('/', '--').replace(':', '---') / 'bin' / 'lean')
    if pinned.exists():
        return str(pinned)
    return shutil.which('lean')


class Runner:
    """Runs files in their own process groups and can stop all of them at once."""

    def __init__(self, lean, limits):
        self.lean, self.limits = lean, limits
        self.env = dict(os.environ, OPENBLAS_NUM_THREADS='1', OMP_NUM_THREADS='1',
                        MKL_NUM_THREADS='1', PYTHONDONTWRITEBYTECODE='1')
        self.nice = ['nice', '-n', '19'] if shutil.which('nice') else []
        self.lock, self.running, self.stopped = threading.Lock(), set(), False

    @staticmethod
    def kill(process):
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass

    def stop(self):
        with self.lock:
            self.stopped = True
            for process in self.running:
                self.kill(process)

    def run(self, name):
        """Run one Lean or Python file from its own directory; return (status, seconds, output).

        The status is the exit status, or 'timeout', 'not started' or 'cancelled'."""
        path = ROOT / name
        if name.endswith('.lean'):
            command, limit = [self.lean, path.name], self.limits['lean']
        else:
            command, limit = [sys.executable, '-B', path.name], self.limits['py']
        start = time.time()
        with self.lock:
            if self.stopped:
                return 'cancelled', 0.0, ''
            try:
                process = subprocess.Popen(self.nice + command, cwd=path.parent, env=self.env,
                                           stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                                           stderr=subprocess.STDOUT, start_new_session=True)
            except OSError as error:
                return 'not started', 0.0, str(error)
            self.running.add(process)
        try:
            output, _ = process.communicate(timeout=limit)
            status = process.returncode
        except subprocess.TimeoutExpired:
            self.kill(process)
            output, _ = process.communicate()
            status = 'timeout'
        finally:
            with self.lock:
                self.running.discard(process)
        return status, time.time() - start, output.decode(errors='replace')


def run_all(targets, lean, jobs, limits, progress):
    runner, results = Runner(lean, limits), {}
    pool = concurrent.futures.ThreadPoolExecutor(jobs)
    try:
        futures = {pool.submit(runner.run, name): name for name in targets}
        for done, future in enumerate(concurrent.futures.as_completed(futures), 1):
            results[futures[future]] = future.result()
            if progress and (done % 50 == 0 or done == len(targets)):
                print(f'\r  {done}/{len(targets)} files', end='', file=sys.stderr, flush=True)
    except KeyboardInterrupt:
        runner.stop()
        pool.shutdown(wait=True, cancel_futures=True)
        sys.exit('\ncheck.py: interrupted; the running files were stopped')
    pool.shutdown()
    if progress:
        print(file=sys.stderr)
    return results


def tail(output, lines=12):
    kept = output.rstrip('\n').split('\n')[-lines:]
    return '\n'.join('      ' + line[:300] for line in kept)


# ---------------------------------------------------------------- main

def load_known():
    try:
        known = json.loads(KNOWN_FAILURES.read_text())
        categories = {name: re.compile(entry['pattern'])
                      for name, entry in known['categories'].items()}
        failures = dict(known['failures'])
        links = {(entry['source'], entry['target']) for entry in known['broken_links']}
    except (OSError, ValueError, KeyError, TypeError, re.error) as error:
        sys.exit(f'check.py: cannot use {KNOWN_FAILURES.relative_to(ROOT)}: {error!r}')
    for name, category in failures.items():
        if category not in categories:
            sys.exit(f'check.py: {name} has the undefined category {category!r} '
                     f'in {KNOWN_FAILURES.relative_to(ROOT)}')
    return categories, failures, links


def check_layout(files):
    """Tracked root files that the layout puts in a directory."""
    return [name for name in files if destination(name) != name]


def main():
    parser = argparse.ArgumentParser(
        description='Check layout and links, run every Lean file and Python audit, and '
                    'compare the results with tools/known-failures.json.',
        epilog='Run from the repository root. Exit status: 0 nothing regressed, '
               '1 regression, 2 usage or setup error.')
    parser.add_argument('files', nargs='*', metavar='FILE',
                        help='run only these Lean or Python files (default: all of them)')
    parser.add_argument('--only-links', action='store_true',
                        help='check the Markdown links and nothing else')
    parser.add_argument('--skip-run', action='store_true',
                        help='check the layout and the links; do not run any file')
    parser.add_argument('--jobs', type=int, default=min(20, os.cpu_count() or 1), metavar='N',
                        help='number of files run at once (default: %(default)s)')
    parser.add_argument('--lean', metavar='PATH',
                        help='Lean binary (default: $LEAN, then the elan toolchain named '
                             'in lean-toolchain, then `lean` on PATH)')
    parser.add_argument('--lean-timeout', type=int, default=300, metavar='SECONDS',
                        help='time limit for one Lean file (default: %(default)s)')
    parser.add_argument('--py-timeout', type=int, default=300, metavar='SECONDS',
                        help='time limit for one Python file (default: %(default)s)')
    args = parser.parse_args()
    if Path.cwd().resolve() != ROOT:
        parser.error(f'run this from the repository root: cd {ROOT} && python3 tools/check.py')
    if args.jobs < 1:
        parser.error('--jobs must be at least 1')
    if args.files and (args.only_links or args.skip_run):
        parser.error('FILE arguments select files to run; they cannot be combined with '
                     '--only-links or --skip-run')

    files = tracked_files()
    categories, known, known_links = load_known()
    problems = 0

    # Layout.
    if not args.only_links:
        misplaced = check_layout(files)
        if misplaced:
            problems += len(misplaced)
            print(f'layout: {len(misplaced)} tracked files at the root belong in a directory; '
                  'run python3 tools/migrate_layout.py')
            for name in misplaced[:20]:
                print(f'    {name} -> {destination(name)}')
            if len(misplaced) > 20:
                print(f'    ... and {len(misplaced) - 20} more')
        else:
            print(f'layout: {len(files)} tracked files, none misplaced')
        for name in sorted(set(known) - set(run_targets(files))):
            print(f'    listed in tools/known-failures.json but not a tracked Lean or Python file: {name}')

    # Links.
    report = scan_links(files)
    found = {(source, target) for source, target, _ in report['broken']}
    new_broken = [entry for entry in report['broken'] if entry[:2] not in known_links]
    resolved_again = sorted(known_links - found)
    problems += len(new_broken)
    print(f"links:  {report['markdown']} Markdown files, {report['occurrences']} relative links "
          f"to files ({len(report['edges'])} distinct source-target pairs), "
          f"{report['directories']} to directories, {report['anchors']} anchors checked")
    print(f"        {len(new_broken)} broken, {len(found & known_links)} known broken")
    for source, target, kind in new_broken:
        reason = 'no such heading' if kind == 'anchor' else 'no such tracked file'
        print(f'    BROKEN  {source} -> {target}  ({reason})')
    for source, target in resolved_again:
        print(f'    listed in tools/known-failures.json but not broken any more: '
              f'{source} -> {target}')
    if report['other']:
        print(f"        {len(report['other'])} links in a syntax that is not checked:")
        for source, line, text in report['other'][:20]:
            print(f'    {source}:{line}: {text}')
    if not args.only_links:
        unlinked = unlinked_notes(files, report['edges'])
        if unlinked:
            print(f'        {len(unlinked)} notes are not linked from any other file:')
            for name in unlinked[:20]:
                print(f'    {name}')
            if len(unlinked) > 20:
                print(f'    ... and {len(unlinked) - 20} more')

    # Run.
    if not (args.only_links or args.skip_run):
        targets = run_targets(files)
        if args.files:
            wanted = list(dict.fromkeys(posixpath.normpath(name) for name in args.files))
            unknown = [name for name in wanted if name not in targets]
            if unknown:
                parser.error('not a tracked Lean or Python file outside tools/: ' + ', '.join(unknown))
            targets = wanted
        lean = find_lean(args.lean)
        needs_lean = any(name.endswith('.lean') for name in targets)
        version = ''
        if needs_lean:
            if not lean:
                parser.error('no Lean binary found; pass --lean PATH or use --skip-run')
            try:
                version = subprocess.run([lean, '--version'], capture_output=True, text=True,
                                         cwd=ROOT, timeout=120).stdout.strip().split('\n')[0]
            except (OSError, subprocess.SubprocessError) as error:
                parser.error(f'cannot run {lean}: {error}')
            pinned = (ROOT / 'lean-toolchain').read_text().strip().rsplit(':v', 1)[-1]
            if pinned not in version:
                print(f'run:    warning: lean-toolchain names {pinned} but {lean} reports '
                      f'{version!r}')
        python = 'Python ' + sys.version.split()[0]
        print(f"run:    {len(targets)} files with {args.jobs} jobs "
              f"({', '.join(part for part in (version, python) if part)})")
        start = time.time()
        results = run_all(targets, lean, args.jobs, {'lean': args.lean_timeout, 'py': args.py_timeout},
                          progress=sys.stderr.isatty())
        passed, expected, regressions, fixed = [], collections.Counter(), [], []
        for name in targets:
            status, seconds, output = results[name]
            if status == 0:
                (fixed if name in known else passed).append(name)
            elif name not in known:
                regressions.append((name, status, 'fails and is not listed in tools/known-failures.json', output))
            elif not categories[known[name]].search(output):
                regressions.append((name, status, f'listed as {known[name]} but its output does not '
                                    f'match {categories[known[name]].pattern!r}', output))
            else:
                expected[known[name]] += 1
        problems += len(regressions)
        summary = ', '.join(f'{category} {count}' for category, count in sorted(expected.items()))
        print(f'        {len(passed) + len(fixed)} passed, {sum(expected.values())} known failures'
              f"{' (' + summary + ')' if summary else ''}, {len(regressions)} regressions, "
              f'{time.time() - start:.0f} s')
        for name, status, why, output in regressions:
            outcome = f'exit status {status}' if isinstance(status, int) else status
            print(f'    REGRESSION  {name}: {outcome}; {why}')
            print(tail(output))
        for name in fixed:
            print(f'    listed in tools/known-failures.json as {known[name]} but passes now: {name}')

    print('FAILED' if problems else 'OK')
    return 1 if problems else 0


if __name__ == '__main__':
    sys.exit(main())
