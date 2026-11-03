"""Attach zed-testgen's generated rows to the functions they test.

Reads the report on stdin and the source file named by argv[1]; writes the source with each
function's `;` replaced by its `test { ... }` block (a test block takes no `;` after it).
Each function must end with `;` at the end of a line, as in examples.zed.
"""

import re
import sys

source = open(sys.argv[1]).read()
name = None
for line in sys.stdin:
    head = re.match(r"^(\w+)  \(", line)
    if head:
        name = head.group(1)
    gen = re.match(r"^  generated:  (test \{.*\})$", line.rstrip("\n"))
    if gen and name:
        start = re.search(rf"^{name}\(", source, re.M)
        if not start:
            sys.exit(f"no declaration of {name}")
        end = source.index(";\n", start.start())
        source = source[:end] + "\n  " + gen.group(1) + source[end + 1 :]
sys.stdout.write(source)
