#!/usr/bin/env python3
"""Check that every row of every Markdown table has as many cells as its header.

usage: check_md_tables.py FILE.md... [--fix]

In GitHub-flavored Markdown, every unescaped `|` in a table row ends a cell, even inside a code
span. So `` `|S| ≥ 2` `` in a table cell breaks the row into extra cells. The script reports such
rows. With --fix, it escapes the pipes inside code spans of table rows (`\\|`, which renders as
`|`) and checks again. Exits with status 1 if a broken row remains.
"""
import argparse
import re
import sys
from pathlib import Path

RULE = re.compile(r'^\|\s*:?-{3}')
PIPE = re.compile(r'(?<!\\)\|')


def escape_code_spans(line):
    return re.sub(r'`[^`\n]*`', lambda m: m.group(0).replace('\\|', '|').replace('|', '\\|'), line)


def broken_rows(lines):
    out, i = [], 0
    while i < len(lines):
        if lines[i].startswith('|') and i + 1 < len(lines) and RULE.match(lines[i + 1]):
            cells = len(PIPE.findall(lines[i]))
            j = i + 2
            while j < len(lines) and lines[j].startswith('|'):
                if len(PIPE.findall(lines[j])) != cells:
                    out.append(j)
                j += 1
            i = j
        else:
            i += 1
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument('files', nargs='+')
    ap.add_argument('--fix', action='store_true')
    args = ap.parse_args()
    bad = 0
    for f in args.files:
        lines = Path(f).read_text(encoding='utf-8').split('\n')
        if args.fix:
            fixed = [escape_code_spans(l) if l.startswith('|') else l for l in lines]
            if fixed != lines:
                Path(f).write_text('\n'.join(fixed), encoding='utf-8')
                print(f'{f}: escaped pipes in code spans')
                lines = fixed
        for j in broken_rows(lines):
            bad += 1
            print(f'{f}:{j + 1}: cell count differs from the header: {lines[j][:100]}')
    print(f'{bad} broken table rows')
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
