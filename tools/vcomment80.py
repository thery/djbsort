#!/usr/bin/env python3
"""Keep framed / multi-line Rocq (.v) comments aligned so the closing *) is at
column 80 -- without disturbing intentionally-narrow blocks or standalone
one-line comments.

Convention (thery/djbsort): a framed comment block has a straight right border
with the closing `*)` on column 80 (line length 80, padded with spaces). A
ragged border (79/81/82) is the "wave" we fix.

What the tool aligns to column 80:
  * every horizontal RULE line  (* ****...**** *) / (* ----...---- *) ;
  * every comment line ENCLOSED between two rule lines (a framed block);
  * every multi-line run of ordinary comment lines whose border is already
    ragged, or uniform at width > 80.
What it deliberately leaves alone:
  * a multi-line block already uniform at width < 80 (an intentional narrow
    note, e.g. nsort.v's width-67 block);
  * a standalone one-line comment that is not enclosed by rules.
A line whose text alone passes column 78 cannot fit `*)` at 80; it is left
untouched and reported so a human can reword it.

Usage:
    tools/vcomment80.py --check FILE.v ...   # report, exit 1 if anything off
    tools/vcomment80.py --fix   FILE.v ...   # rewrite in place

Typical:  tools/vcomment80.py --fix code/*/proof/*.v
          tools/vcomment80.py --check code/*/proof/*.v      # pre-commit / CI
"""
import sys

WIDTH = 80


def is_comment_line(line):
    s = line.strip()
    return s.startswith("(*") and s.endswith("*)")


def is_rule(line):
    s = line.strip()
    if not (s.startswith("(*") and s.endswith("*)")):
        return False
    interior = s[2:-2].strip()
    return len(interior) >= 4 and set(interior) <= set("*-=")


def normalize(line):
    """(new_line, ok); ok=False if the text overflows column 80."""
    inner = line.rstrip()[:-2].rstrip()          # drop trailing '*)' and spaces
    pad = WIDTH - len(inner) - 2
    if pad < 0:
        return line, False
    return inner + " " * pad + "*)", True


def targets(lines):
    """Set of line indices that should be aligned to column 80."""
    n = len(lines)
    idx = set(i for i, l in enumerate(lines) if is_rule(l))   # rules are always 80
    i = 0
    while i < n:
        if is_comment_line(lines[i]) and not is_rule(lines[i]):
            a = i
            while i < n and is_comment_line(lines[i]) and not is_rule(lines[i]):
                i += 1
            b = i - 1                                          # run [a..b]
            enclosed = (a - 1 >= 0 and is_rule(lines[a - 1])
                        and b + 1 < n and is_rule(lines[b + 1]))
            if enclosed:
                idx.update(range(a, b + 1))
            elif b > a:                                        # multi-line run
                widths = {len(lines[k]) for k in range(a, b + 1)}
                if not (len(widths) == 1 and next(iter(widths)) < WIDTH):
                    idx.update(range(a, b + 1))
            # single, non-enclosed comment: leave it
        else:
            i += 1
    return idx


def process(lines):
    out = lines[:]
    fixed, overflow = [], []
    for k in sorted(targets(lines)):
        new, ok = normalize(lines[k])
        if not ok:
            overflow.append(k + 1)
        elif new != lines[k]:
            out[k] = new
            fixed.append(k + 1)
    return out, fixed, overflow


def main():
    args = sys.argv[1:]
    if len(args) < 2 or args[0] not in ("--check", "--fix"):
        sys.stderr.write(__doc__)
        sys.exit(2)
    mode, files = args[0], args[1:]
    problems = 0
    for fn in files:
        with open(fn) as f:
            lines = f.read().split("\n")
        out, fixed, overflow = process(lines)
        for ln in overflow:
            print(f"{fn}:{ln}: comment text overflows column 80 -- reword")
            problems += 1
        if mode == "--fix":
            if fixed:
                with open(fn, "w") as f:
                    f.write("\n".join(out))
                print(f"{fn}: aligned {len(fixed)} line(s) to column 80")
        else:
            for ln in fixed:
                print(f"{fn}:{ln}: closing *) not at column 80")
                problems += 1
    sys.exit(1 if problems else 0)


if __name__ == "__main__":
    main()
