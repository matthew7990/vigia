# Security

vigia fetches untrusted pages and executes their JavaScript by design.
The sandbox boundary is the process: scripts run in our own interpreter
with hard caps on heap, steps, call depth, and external fetches. There
is no shell escape hatch by intention.

If you find a way for page content to escape that boundary (host file
access, process execution, cap bypasses, memory unsafety), please do not
open a public issue. Report it privately to the maintainer via GitHub's
"Report a vulnerability" flow on the Security tab.

For everything else (wrong render, hangs, crashes), a normal issue is fine.
